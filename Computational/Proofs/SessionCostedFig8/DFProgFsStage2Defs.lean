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
import Computational.Proofs.SessionCostedFig8.BundlesAuxSize
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase
import Computational.Proofs.ReductionDsl.PureAuxMacroLift
import Computational.Proofs.ReductionDsl.Notation
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Stage-2 Multi-Session FS-AEAD Atomic Program Definitions & Coin-Branch Combinator

Defines `coinBranchRed`, `ckaCoinBranchDFRed`, and the Stage-2 multi-session `SM.specDF`
atomic FS-AEAD reductions (`redFSAuthDF*AtomicProg`) so downstream potential/evaluation
modules do not wait on the `GRedBounded` cost proofs in `DFProgFsStage2Bounds`.
-/

namespace Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.SM.Construction (Header redFSAuthDFMultiProg
  redFSAuthDFMultiBucketProg redFSAuthDFPaperMultiProg redFSAuthDFPaperMultiBucketModeProg
  fsaeadMultiHeaderAdIface)
open _root_.ReductionDsl (Sig Ops Ty Var Env Expr Comp Iface GameCodec CostedReduction
  fsaeadHeaderIface fig8SmCodecDF)
open scoped Computational.Proofs.ReductionDsl.Notation
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
local notation "Bytes" => List (BitVec 8)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun CKASamp)
open _root_.CryptoGames.PRFPRNG (prngSMCodecDF)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFs (compileFsMultiDFAtomic)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase (compListMNodes compQueryCount
  comp_renameM_queries)
open Computational.Proofs.SessionCostedFig8.DFProgBucketBounds (dummyFsStage2AtomicProg)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMultiProg redFSAuthDFShiftedDir2PaperMultiProg)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW compCostW compCostW_rename)

section CoinBranchCombinator

@[reducible] private def renWk1 {S : Sig} {a b : Ty S} : ∀ ⦃u⦄, Var [a] u → Var [b, a] u
  | _, .zero => .succ .zero

@[reducible] private def renSkip1 {S : Sig} {a mid b : Ty S} : ∀ ⦃u⦄, Var [a, b] u → Var [a, mid, b] u
  | _, .zero => .zero
  | _, .succ .zero => .succ (.succ .zero)

/-- Generic 1-bit coin-branching combinator on `CostedReduction`s with disjoint branch state `.sum R₁.σ R₂.σ`. -/
def coinBranchRed {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (cCoin : Comp O I [rIn] .bool)
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out) :
    CostedReduction O I G C rIn aIn aOut out where
  σ := .sum R₁.σ R₂.σ
  init :=
    .bind cCoin
      (.ite (.var .zero)
        (.bind (R₁.init.renameM renWk1)
          (.ret (.pair (.fst (.var .zero)) (.inl (.snd (.var .zero))))))
        (.bind (R₂.init.renameM renWk1)
          (.ret (.pair (.fst (.var .zero)) (.inr (.snd (.var .zero)))))))
  handle :=
    .caseSum (.var .zero)
      (.bind (R₁.handle.renameM renSkip1)
        (.ret (.pair (.fst (.var .zero)) (.inl (.snd (.var .zero))))))
      (.bind (R₂.handle.renameM renSkip1)
        (.ret (.pair (.fst (.var .zero)) (.inr (.snd (.var .zero))))))
  finish :=
    .caseSum (.var .zero)
      (R₁.finish.renameM renSkip1)
      (R₂.finish.renameM renSkip1)

private theorem run_simulateQ_query_bind_gen {ι : Type} {spec : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] {σ α : Type}
    (impl : QueryImpl spec (StateT σ m)) (q : spec.Domain)
    (k : spec.Range q → OracleComp spec α) (s : σ) :
    (simulateQ impl (liftM (OracleSpec.query q) >>= k)).run s =
      ((impl q).run s >>= fun p => (simulateQ impl (k p.1)).run p.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run_bind]

private theorem simulateQ_coinBranchRed_inl {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (cCoin : Comp O I [rIn] .bool)
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out)
    {α : Type} (oa : OracleComp (unifSpec + G) α) (s₁ : R₁.σ.denote) :
    (simulateQ (coinBranchRed cCoin R₁ R₂).impl oa).run
        (Sum.inl s₁ : (coinBranchRed cCoin R₁ R₂).σ.denote) =
      Prod.map id Sum.inl <$> (simulateQ R₁.impl oa).run s₁ := by
  induction oa using OracleComp.inductionOn generalizing s₁ with
  | pure b => rfl
  | query_bind q k ih =>
    have hL : (simulateQ (coinBranchRed cCoin R₁ R₂).impl (liftM (OracleSpec.query q) >>= k)).run
        (Sum.inl s₁ : (coinBranchRed cCoin R₁ R₂).σ.denote) =
        (((coinBranchRed cCoin R₁ R₂).impl q).run (Sum.inl s₁ : (coinBranchRed cCoin R₁ R₂).σ.denote) >>=
          fun p => (simulateQ (coinBranchRed cCoin R₁ R₂).impl (k p.1)).run p.2) := by
      dsimp only [coinBranchRed, Ty.denote]
      exact run_simulateQ_query_bind_gen _ _ _ _
    rw [hL, run_simulateQ_query_bind_gen, map_bind]
    cases q with
    | inl n =>
      dsimp only [CostedReduction.impl, coinBranchRed, ReductionDsl.handlerImpl]
      simp only [StateT.run_lift, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u s₁
    | inr t =>
      have hren : (R₁.handle.renameM renSkip1).eval
          (Env.cons s₁ (Env.cons (t := .sum R₁.σ R₂.σ) (Sum.inl s₁) (Env.cons (C.qenc t) Env.nil))) =
          R₁.handle.eval (Env.cons s₁ (Env.cons (C.qenc t) Env.nil)) :=
        R₁.handle.renameM_eval (fun _ v => match v with | .zero => rfl | .succ .zero => rfl)
      dsimp only [CostedReduction.impl, coinBranchRed, ReductionDsl.handlerImpl]
      simp only [StateT.run_mk, Comp.eval, Expr.eval, Env.get, hren, bind_assoc, pure_bind]
      exact bind_congr fun ⟨rOut, s₁'⟩ => ih (C.rdec t rOut) s₁'

private theorem simulateQ_coinBranchRed_inr {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (cCoin : Comp O I [rIn] .bool)
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out)
    {α : Type} (oa : OracleComp (unifSpec + G) α) (s₂ : R₂.σ.denote) :
    (simulateQ (coinBranchRed cCoin R₁ R₂).impl oa).run
        (Sum.inr s₂ : (coinBranchRed cCoin R₁ R₂).σ.denote) =
      Prod.map id Sum.inr <$> (simulateQ R₂.impl oa).run s₂ := by
  induction oa using OracleComp.inductionOn generalizing s₂ with
  | pure b => rfl
  | query_bind q k ih =>
    have hL : (simulateQ (coinBranchRed cCoin R₁ R₂).impl (liftM (OracleSpec.query q) >>= k)).run
        (Sum.inr s₂ : (coinBranchRed cCoin R₁ R₂).σ.denote) =
        (((coinBranchRed cCoin R₁ R₂).impl q).run (Sum.inr s₂ : (coinBranchRed cCoin R₁ R₂).σ.denote) >>=
          fun p => (simulateQ (coinBranchRed cCoin R₁ R₂).impl (k p.1)).run p.2) := by
      dsimp only [coinBranchRed, Ty.denote]
      exact run_simulateQ_query_bind_gen _ _ _ _
    rw [hL, run_simulateQ_query_bind_gen, map_bind]
    cases q with
    | inl n =>
      dsimp only [CostedReduction.impl, coinBranchRed, ReductionDsl.handlerImpl]
      simp only [StateT.run_lift, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u s₂
    | inr t =>
      have hren : (R₂.handle.renameM renSkip1).eval
          (Env.cons s₂ (Env.cons (t := .sum R₁.σ R₂.σ) (Sum.inr s₂) (Env.cons (C.qenc t) Env.nil))) =
          R₂.handle.eval (Env.cons s₂ (Env.cons (C.qenc t) Env.nil)) :=
        R₂.handle.renameM_eval (fun _ v => match v with | .zero => rfl | .succ .zero => rfl)
      dsimp only [CostedReduction.impl, coinBranchRed, ReductionDsl.handlerImpl]
      simp only [StateT.run_mk, Comp.eval, Expr.eval, Env.get, hren, bind_assoc, pure_bind]
      exact bind_congr fun ⟨rOut, s₂'⟩ => ih (C.rdec t rOut) s₂'

theorem coinBranchRed_eval {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (cCoin : Comp O I [rIn] .bool)
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) :
    (coinBranchRed cCoin R₁ R₂).eval A x = (do
      let b ← cCoin.eval (.cons x .nil)
      if b then R₁.eval A x else R₂.eval A x) := by
  have h1 := simulateQ_coinBranchRed_inl (α := aOut.denote) cCoin R₁ R₂
  have h2 := simulateQ_coinBranchRed_inr (α := aOut.denote) cCoin R₁ R₂
  rw [CostedReduction.eval]
  dsimp only [coinBranchRed] at h1 h2 ⊢
  simp only [Comp.eval, bind_assoc]
  refine bind_congr fun b => ?_
  cases b
  · have hi : (R₂.init.renameM renWk1).eval (Env.cons (t := .bool) false (Env.cons x Env.nil)) =
        R₂.init.eval (Env.cons x Env.nil) :=
      R₂.init.renameM_eval (fun _ v => match v with | .zero => rfl)
    simp only [Expr.eval, Env.get, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind, hi]
    refine bind_congr fun ⟨a, s₂⟩ => ?_
    dsimp only
    rw [h2 (A a) s₂, bind_map_left]
    refine bind_congr fun ⟨bOut, s₂'⟩ => ?_
    simp only [Prod.map_apply, id_eq]
    exact R₂.finish.renameM_eval (fun _ v => match v with | .zero => rfl | .succ .zero => rfl)
  · have hi : (R₁.init.renameM renWk1).eval (Env.cons (t := .bool) true (Env.cons x Env.nil)) =
        R₁.init.eval (Env.cons x Env.nil) :=
      R₁.init.renameM_eval (fun _ v => match v with | .zero => rfl)
    simp only [Expr.eval, Env.get, ↓reduceIte, bind_assoc, pure_bind, hi]
    refine bind_congr fun ⟨a, s₁⟩ => ?_
    dsimp only
    rw [h1 (A a) s₁, bind_map_left]
    refine bind_congr fun ⟨bOut, s₁'⟩ => ?_
    simp only [Prod.map_apply, id_eq]
    exact R₁.finish.renameM_eval (fun _ v => match v with | .zero => rfl | .succ .zero => rfl)

theorem coinBranchRed_compCostW {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    (cCoin : Comp O I [rIn] .bool)
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out) :
    compCostW opC sC qC (coinBranchRed cCoin R₁ R₂).init ≤
      compCostW opC sC qC cCoin +
        max (compCostW opC sC qC R₁.init) (compCostW opC sC qC R₂.init) + 12 ∧
    compCostW opC sC qC (coinBranchRed cCoin R₁ R₂).handle ≤
      max (compCostW opC sC qC R₁.handle) (compCostW opC sC qC R₂.handle) + 10 ∧
    compCostW opC sC qC (coinBranchRed cCoin R₁ R₂).finish ≤
      max (compCostW opC sC qC R₁.finish) (compCostW opC sC qC R₂.finish) + 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [coinBranchRed, compCostW, exprCostW, compCostW_rename] <;>
    omega

theorem coinBranchRed_totalQueries_le {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (cCoin : Comp O I [rIn] .bool)
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out) (q qOut : ℕ)
    (hCoin : cCoin.queries w ws = 0)
    (hi₁ : R₁.init.queries w ws = 0) (hi₂ : R₂.init.queries w ws = 0)
    (hf₁ : R₁.finish.queries w ws = 0) (hf₂ : R₂.finish.queries w ws = 0)
    (h₁ : R₁.totalQueries w ws q ≤ qOut)
    (h₂ : R₂.totalQueries w ws q ≤ qOut) :
    (coinBranchRed cCoin R₁ R₂).totalQueries w ws q ≤ qOut := by
  simp only [CostedReduction.totalQueries, hi₁, hi₂, hf₁, hf₂, Nat.zero_add, Nat.add_zero] at h₁ h₂
  simp only [CostedReduction.totalQueries, coinBranchRed, Comp.queries, comp_renameM_queries,
    hCoin, hi₁, hi₂, hf₁, hf₂, Nat.add_zero, Nat.zero_add, max_self]
  cases le_total (R₁.handle.queries w ws) (R₂.handle.queries w ws) with
  | inl hle => simpa [_root_.max_eq_right hle] using h₂
  | inr hle => simpa [_root_.max_eq_left hle] using h₁

theorem coinBranchRed_compSizeW {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ)
    (cCoin : Comp O I [rIn] .bool)
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out) :
    Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS sS qS
        (coinBranchRed cCoin R₁ R₂).init =
      Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS sS qS cCoin +
        Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS sS qS R₁.init +
        Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS sS qS R₂.init + 19 ∧
    Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS sS qS
        (coinBranchRed cCoin R₁ R₂).handle =
      Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS sS qS R₁.handle +
        Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS sS qS R₂.handle + 18 ∧
    Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS sS qS
        (coinBranchRed cCoin R₁ R₂).finish =
      Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS sS qS R₁.finish +
        Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW opS sS qS R₂.finish + 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [coinBranchRed,
      Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW,
      Computational.Proofs.SessionCostedFig8.BundlesAuxSize.exprSizeW,
      Computational.Proofs.SessionCostedFig8.BundlesAuxSize.compSizeW_renameM] <;>
    omega

@[local simp] private theorem compListMNodes_renameM {S : Sig} {O : Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u)
    {t : Ty S} (c : Comp O I Γ t) :
    compListMNodes (c.renameM ξ) = compListMNodes c := by
  induction c generalizing Δ <;> simp [Comp.renameM, compListMNodes, *]

@[local simp] private theorem compQueryCount_renameM {S : Sig} {O : Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u)
    {t : Ty S} (c : Comp O I Γ t) :
    compQueryCount (c.renameM ξ) = compQueryCount c := by
  induction c generalizing Δ <;> simp [Comp.renameM, compQueryCount, *]

theorem coinBranchRed_compListMNodes {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (cCoin : Comp O I [rIn] .bool)
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out) :
    compListMNodes (coinBranchRed cCoin R₁ R₂).init =
      compListMNodes cCoin + compListMNodes R₁.init + compListMNodes R₂.init ∧
    compListMNodes (coinBranchRed cCoin R₁ R₂).handle =
      compListMNodes R₁.handle + compListMNodes R₂.handle ∧
    compListMNodes (coinBranchRed cCoin R₁ R₂).finish =
      compListMNodes R₁.finish + compListMNodes R₂.finish := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp [coinBranchRed, compListMNodes]; try omega)

theorem coinBranchRed_compQueryCount {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (cCoin : Comp O I [rIn] .bool)
    (R₁ R₂ : CostedReduction O I G C rIn aIn aOut out) :
    compQueryCount (coinBranchRed cCoin R₁ R₂).init =
      compQueryCount cCoin + compQueryCount R₁.init + compQueryCount R₂.init ∧
    compQueryCount (coinBranchRed cCoin R₁ R₂).handle =
      compQueryCount R₁.handle + compQueryCount R₂.handle ∧
    compQueryCount (coinBranchRed cCoin R₁ R₂).finish =
      compQueryCount R₁.finish + compQueryCount R₂.finish := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp [coinBranchRed, compQueryCount]; try omega)

/-- 1-bit CKA coin-branching (`gMain ← CKASamp.bit .unit`) on shallow multi-session `SM.specDF` reductions. -/
@[expose] def ckaCoinBranchDFRed
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (B0 : ℕ)
    (Rtrue Rfalse : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
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
    CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
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
      .unit .unit .bool .bool :=
  coinBranchRed
    (Comp.sample
      (O := fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (I := fsaeadMultiHeaderAdIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      CKASamp.bit .unit)
    Rtrue Rfalse

theorem ckaCoinBranchDFRed_eval
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (B0 : ℕ)
    (Rtrue Rfalse : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
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
    (A : Unit → OracleComp (unifSpec +
      CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      Bool)
    (x : Unit) :
    (ckaCoinBranchDFRed ℓ Pt C Dh encPt encT idOf lam B0 Rtrue Rfalse).eval A x = (do
      let gMain ←
        (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ($ᵗ Bool)
      if gMain then Rtrue.eval A x else Rfalse.eval A x) := by
  simpa [ckaCoinBranchDFRed, Comp.eval, Expr.eval] using
    coinBranchRed_eval
      (Comp.sample
        (O := fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (I := fsaeadMultiHeaderAdIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        CKASamp.bit .unit)
      Rtrue Rfalse A x

theorem ckaCoinBranchDFRed_eval_sampleT
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (B0 : ℕ)
    (Rtrue Rfalse : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
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
    (A : Unit → OracleComp (unifSpec +
      CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      Bool)
    (x : Unit) :
    (ckaCoinBranchDFRed ℓ Pt C Dh encPt encT idOf lam B0 Rtrue Rfalse).eval A x =
      (_root_.CryptoGames.SM.Construction.sampleT Bool >>= fun gMain =>
        if gMain then Rtrue.eval A x else Rfalse.eval A x) := by
  exact ckaCoinBranchDFRed_eval ℓ Pt C Dh encPt encT idOf lam B0 Rtrue Rfalse A x

theorem ckaCoinBranchDFRed_isQueryBoundP
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (B0 : ℕ)
    (Rtrue Rfalse : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
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
    (A : Unit → OracleComp (unifSpec +
      CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      Bool)
    (x : Unit)
    (p : (unifSpec + OracleSpec.sigma (fun _ : ℕ =>
      CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (ℕ × LibsignalCiphertextWithSalt32))).Domain → Prop)
    [DecidablePred p] (k : ℕ)
    (hpU : ∀ n, ¬ p (.inl n))
    (htrue : (Rtrue.eval A x).IsQueryBoundP p k)
    (hfalse : (Rfalse.eval A x).IsQueryBoundP p k) :
    ((ckaCoinBranchDFRed ℓ Pt C Dh encPt encT idOf lam B0 Rtrue Rfalse).eval A x).IsQueryBoundP p k := by
  rw [ckaCoinBranchDFRed_eval]
  have h0 : ((fsaeadMultiHeaderAdIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
      ($ᵗ Bool)).IsQueryBoundP p 0 :=
    (ReductionDsl.liftP_queryBound p (fun n => by
      dsimp only [fsaeadMultiHeaderAdIface]
      simp [hpU n]) ($ᵗ Bool))
  rw [← Nat.zero_add k]
  refine OracleComp.isQueryBoundP_bind
    (ob := fun gMain => if gMain then Rtrue.eval A x else Rfalse.eval A x) h0 (fun b _ => ?_)
  cases b
  · simpa using hfalse
  · simpa using htrue

end CoinBranchCombinator

section Stage2FsMultiAtomicProgs

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey)
  (idOf : Party → IdentityKey) (lam : Pt)

local instance : Nonempty Pt := ⟨0⟩
local notation "atomicFig8Ops" => _root_.ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam

/-- Stage-2 atomic `redFSAuthDFMulti` program (`[B7]`, single target epoch `t`). -/
@[expose] def redFSAuthDFMultiAtomicProg
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction atomicFig8Ops (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let L := q + 1
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let qepC := qep
  if t ≤ qepC + 3 ∧ (∀ x, tL = some x → x ≤ qepC + 3) ∧ qR ≤ 2 * q + 2 then
    compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qepC qR B0
      (redFSAuthDFMultiProg L B0 1 qepC maxForwardJumps la tL t)
  else
    dummyFsStage2AtomicProg Dh encPt C ℓ encT idOf lam

/-- Stage-2 atomic `(tL, par)`-bucket `redFSAuthDFMultiBucket` program (`[B7]` × `[B8]`, `B_fs_u`). -/
@[expose] def redFSAuthDFMultiBucketAtomicProg
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (par : Bool) :
    CostedReduction atomicFig8Ops (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let L := q + 1
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let qepC := qep
  if (∀ x, tL = some x → x ≤ qepC + 3) ∧ qR ≤ 2 * q + 2 then
    compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qepC qR B0
      (redFSAuthDFMultiBucketProg L B0 1 4 qepC maxForwardJumps la tL par)
  else
    dummyFsStage2AtomicProg Dh encPt C ℓ encT idOf lam

/-- Stage-2 atomic `redFSAuthDFPaperMulti` program (`[B7]`, paper unshifted single epoch `t`). -/
@[expose] def redFSAuthDFPaperMultiAtomicProg
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction atomicFig8Ops (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let L := q + 1
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let qepC := qep
  if t ≤ qepC + 3 ∧ (∀ x, tL = some x → x ≤ qepC + 3) ∧ qR ≤ 2 * q + 2 then
    compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qepC qR B0
      (redFSAuthDFPaperMultiProg L B0 1 qepC maxForwardJumps la tL t)
  else
    dummyFsStage2AtomicProg Dh encPt C ℓ encT idOf lam

/-- Stage-2 atomic `redFSAuthDFShiftedPaperMulti` program (`[B7]`, paper `B2` at `tL = some (t - 3)`). -/
@[expose] def redFSAuthDFShiftedPaperMultiAtomicProg
    (stage la : Bool) (j qR q qep t : ℕ) :
    CostedReduction atomicFig8Ops (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let L := q + 1
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let qepC := qep
  if t ≤ qepC + 3 ∧ qR ≤ 2 * q + 2 then
    compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qepC qR B0
      (redFSAuthDFShiftedPaperMultiProg L B0 1 qepC maxForwardJumps (t - 2) t la)
  else
    dummyFsStage2AtomicProg Dh encPt C ℓ encT idOf lam

/-- Stage-2 atomic `redFSAuthDFShiftedDir2PaperMulti` program (`[B7]`, paper `B1` at `tL = some (t - 2)`). -/
@[expose] def redFSAuthDFShiftedDir2PaperMultiAtomicProg
    (stage la : Bool) (j qR q qep t : ℕ) :
    CostedReduction atomicFig8Ops (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let L := q + 1
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let qepC := qep
  if t ≤ qepC + 3 ∧ qR ≤ 2 * q + 2 then
    compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qepC qR B0
      (redFSAuthDFShiftedDir2PaperMultiProg L B0 qepC maxForwardJumps (t - 1) t la)
  else
    dummyFsStage2AtomicProg Dh encPt C ℓ encT idOf lam

/-- Unified case-splitting Stage-2 atomic `redFSAuthDFCasePaperMulti` program (`[B7]`):
routes `B1` (`2 ≤ t ∧ tL = some (t - 2)`), `B2` (`3 ≤ t ∧ tL = some (t - 3)`), and unshifted epochs. -/
@[expose] def redFSAuthDFCasePaperMultiAtomicProg
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction atomicFig8Ops (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    redFSAuthDFShiftedDir2PaperMultiAtomicProg ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep t
  else if 3 ≤ t ∧ tL = some (t - 3) then
    redFSAuthDFShiftedPaperMultiAtomicProg ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep t
  else
    redFSAuthDFPaperMultiAtomicProg ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep tL t

/-- Stage-2 coin-averaged (`gMain ← CKASamp.bit .unit`) atomic `(tL, par)`-bucket
`redFSAuthDFPaperMultiBucket` program (`[B7]` × `[B8]`, paper `B_fs_u`). -/
@[expose] def redFSAuthDFPaperMultiBucketAtomicProg
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (par : Bool) :
    CostedReduction atomicFig8Ops (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let L := q + 1
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let qepC := min qep (q + 11)
  if (∀ x, tL = some x → x ≤ qepC + 3) ∧ qR ≤ 2 * q + 2 then
    compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j qepC qR B0
      (ckaCoinBranchDFRed ℓ Pt C Dh encPt encT idOf lam B0
        (redFSAuthDFPaperMultiBucketModeProg L B0 1 4 qepC maxForwardJumps true la tL par)
        (redFSAuthDFPaperMultiBucketModeProg L B0 1 4 qepC maxForwardJumps false la tL par))
  else
    dummyFsStage2AtomicProg Dh encPt C ℓ encT idOf lam

theorem redFSAuthDFPaperMultiBucketAtomicProg_eq_compile
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (htL : ∀ x, tL = some x → x ≤ min qep (q + 11) + 3)
    (hqR : qR ≤ 2 * q + 2) :
    redFSAuthDFPaperMultiBucketAtomicProg ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep tL par =
      compileFsMultiDFAtomic ℓ Pt C Dh encPt encT idOf lam stage la j (min qep (q + 11)) qR
        ((q + 1) * (maxForwardJumps + 1))
        (ckaCoinBranchDFRed ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1))
          (redFSAuthDFPaperMultiBucketModeProg (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 4
            (min qep (q + 11)) maxForwardJumps true la tL par)
          (redFSAuthDFPaperMultiBucketModeProg (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 4
            (min qep (q + 11)) maxForwardJumps false la tL par)) := by
  dsimp only [redFSAuthDFPaperMultiBucketAtomicProg]
  split_ifs with h
  · rfl
  · exact absurd ⟨htL, hqR⟩ h

end Stage2FsMultiAtomicProgs

end

end Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs

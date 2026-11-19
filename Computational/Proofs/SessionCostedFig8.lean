/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatements -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedCKA
public import Computational.Proofs.ReductionDsl.SM.RedFS -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedPRNG
import Computational.Proofs.ReductionDsl.SM.Theorem1
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8SourceCosts -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.QuerySubsumes -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.ProgBounds
import Computational.Proofs.SessionCostedFig8.TopAssembly
import Computational.Proofs.SessionCostedFig8.BucketPRNGProgBounds
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsQueries
import Computational.Proofs.SessionCostedFig8.BucketFSAuthPotOK
import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap
import Computational.Proofs.SessionCostedFig8.BundlesEval
public import Computational.Proofs.SessionCostedFs -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SignedPrims -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem1 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries
import Computational.Proofs.SessionCostedBase
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.SignalWireShortProto
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.GameHop.ReductionDsl.CostUB
import Computational.Proofs.E2E.SignedCoin
import Computational.Proofs.SessionCostedFig8.RedFSUniSafePost
import Computational.Proofs.SessionCostedFig8.BucketCKAEval
import Computational.Proofs.SessionCostedFig8.BucketCKASwap
import Computational.Proofs.SessionCostedFig8.BucketPRNGSwap
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridge
import Computational.Proofs.SessionCostedFig8.RedCKAPrivUBridge
import Computational.Proofs.SessionCostedFig8.RedCKAPrivUDhSwap
import Computational.Proofs.SessionCostedFig8.RedFSUniEval
import Computational.Proofs.SessionCostedFig8.Stage2Swap
import Computational.Proofs.CryptoGames.SM.Theorem6Libsignal
import Computational.Proofs.CryptoGames.SM.Theorem8
import Computational.Proofs.CryptoGames.SM.Theorem8.Stage2Defs
import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth
import Computational.Proofs.CryptoGames.SM.Theorem12
import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs
import Computational.Proofs.CryptoGames.CKA.DHProof
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.FSAEADRed -- proof-setup: allow-public-import
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.CryptoGames.SM.Theorem8.Stage2Bucket

/-!
# Costed Figure 8 Reduction Bundle and Advantage Bridges

Instantiates the atomic `Fig8CostedReds` bundle `fig8RedsInst` with `fig8CostedBounds` and bridges
its single-instance and mixture (`advAvg`) advantages to `fig8ShortBoundWith`.-/

namespace CryptoVerification.LibsignalSession
public section

set_option autoImplicit false


open OracleComp OracleSpec _root_.CryptoGames _root_.CryptoGames.LibsignalSM
  _root_.CryptoGames.Ratchet _root_.CryptoGames.Ratchet.LibsignalInst
  _root_.CryptoGames.LibsignalSession _root_.CryptoVerification.LibsignalProtoCodec
  _root_.CryptoGames.HMAC _root_.CryptoGames.HKDF _root_.CryptoGames.CBC
  _root_.CryptoGames.LibsignalAead _root_.CryptoGames.SM _root_.CryptoGames.SM.Construction
  _root_.CryptoGames.SM.Engine _root_.CryptoGames.CKA _root_.CryptoGames.AEADScheme
  _root_.CryptoGames.MACScheme _root_.CryptoGames.WireAEAD _root_.CryptoGames.FSAEAD
  _root_.ReductionDsl ENNReal MeasureTheory
open Computational.Proofs.GameHop.ReductionDsl.CostUB
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (CoinSimEquiv
  ckaAdvantage_congr prngAdvantage_congr fsaeadGame_evalDistEq_of_coinSimEquiv)
open Computational.Proofs.ReductionDsl.MacroLift (toVal guardRed dummyRed)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb atomicShortPubB
  atomicShortPubB_imp_shortB fsAtomicB fsAtomicB_send_eq)
open _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge (ckaBranch_dhSchemeFb_eq)
open _root_.CryptoVerification.E2E.Signed (advAvg ckaBranch_avg prngBranch_avg boolBias_mix_coin)
open Computational.Proofs.SessionCostedFig8
open Computational.Proofs.SessionCostedFig8.QuerySubsumes

export Computational.Proofs.ReductionDsl.Fig8SourceCosts (v0_cost v1_cost v2_cost v3_cost
  v4_cost v5_cost v6_cost v7_cost bits_succ_le bits_le_bits_qep_add HooksCostBounded
  fig8_poly_le_ratchetCostBudget add_mul_le_ratchetCostBudget)

abbrev fig8StepBound (q qep : ℕ) : ℕ :=
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  2000 * (L * L) + 2700 * L + L * (3 * ReductionDsl.bits qep + 60) + 3 * B +
    200 * ReductionDsl.bits qep + 350000

private theorem liftP_congr_local {ι : Type} {T : OracleSpec.{0, 0} ι} {S₁' S₂' : Sig}
    (I₂ : Iface S₂' T) (I₁ : Iface S₁' T) (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    {α : Type} (p : ProbComp α) : I₂.liftP p = I₁.liftP p := by
  unfold Iface.liftP
  rw [funext hFwdU]

private theorem pureRetRed_isQueryBoundP_local
    {S : Sig} {O : Ops S} {ι κ : Type} {T₀ : OracleSpec.{0, 0} ι}
    {I : Iface S (unifSpec + T₀)}
    {G : OracleSpec.{0, 0} κ} {C : _root_.ReductionDsl.GameCodec S G}
    {rIn aIn aOut out σ : Ty S}
    (initE : Expr O [rIn] (.prod aIn σ))
    (handleE : Expr O [σ, C.Q] (.prod C.R σ))
    (finishE : Expr O [σ, aOut] out)
    {P : (unifSpec + T₀).Domain → Prop} [DecidablePred P]
    (hFwdU : ∀ n, I.fwdU n = liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)))
    (hP : ∀ n, ¬ P (.inl n))
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) (k : ℕ) :
    (({ σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE } :
        CostedReduction O I G C rIn aIn aOut out).eval A x).IsQueryBoundP P k := by
  let R : CostedReduction O I G C rIn aIn aOut out :=
    { σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE }
  suffices hSim : ∀ (oa : OracleComp (unifSpec + G) aOut.denote) (s : σ.denote),
      (((simulateQ R.impl oa).run s) >>= fun bs =>
        pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))).IsQueryBoundP P k by
    change (R.eval A x).IsQueryBoundP P k
    unfold CostedReduction.eval
    simp only [R, Comp.eval, pure_bind]
    exact hSim (A (initE.eval (.cons x .nil)).1) (initE.eval (.cons x .nil)).2
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure b =>
    intro s
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    intro s
    rcases q with n | t
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)) >>= fun u =>
            (((simulateQ R.impl (mx u)).run s) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, _root_.ReductionDsl.handlerImpl,
          StateT.run_bind, StateT.run_lift, hFwdU, map_eq_bind_pure_comp, bind_assoc]
      rw [hStep, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (hP n), fun u => by simpa [hP n] using ih u s⟩
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          (((simulateQ R.impl
              (mx (C.rdec t (handleE.eval (.cons s (.cons (C.qenc t) .nil))).1))).run
            (handleE.eval (.cons s (.cons (C.qenc t) .nil))).2) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, _root_.ReductionDsl.handlerImpl, Comp.eval,
          StateT.run_bind, StateT.run_mk, pure_bind]
      rw [hStep]
      exact ih _ _

section Fig8Costed

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance : Inhabited Pt := ⟨0⟩

omit [Zero Pt] [SampleableType Pt] in
/-- Well-formedness hypotheses on an FS-AEAD reduction `R` required by `lFS_full_bound_short_proto`. -/
@[expose] def FsOk (ℓ : ℕ) (qR qd : ℕ)
    (R : FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      LibsignalCiphertextWithSalt32) : Prop :=
  FSAEAD.MakesAtMostQueries R qR ∧ FSAEAD.MakesAtMostDecQueries R qd ∧
    FSAEAD.EqualPubChallenges R ∧
    FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) R ∧
    FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) R ∧
    GuardedFSInjectShort R

private theorem pureRetRed_isQueryBoundP
    {S : Sig} {O : Ops S} {ι κ : Type} {T₀ : OracleSpec.{0, 0} ι}
    {I : Iface S (unifSpec + T₀)}
    {G : OracleSpec.{0, 0} κ} {C : _root_.ReductionDsl.GameCodec S G}
    {rIn aIn aOut out σ : Ty S}
    (initE : Expr O [rIn] (.prod aIn σ))
    (handleE : Expr O [σ, C.Q] (.prod C.R σ))
    (finishE : Expr O [σ, aOut] out)
    {P : (unifSpec + T₀).Domain → Prop} [DecidablePred P]
    (hFwdU : ∀ n, I.fwdU n = liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)))
    (hP : ∀ n, ¬ P (.inl n))
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) (k : ℕ) :
    (({ σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE } :
        CostedReduction O I G C rIn aIn aOut out).eval A x).IsQueryBoundP P k := by
  let R : CostedReduction O I G C rIn aIn aOut out :=
    { σ := σ, init := .ret initE, handle := .ret handleE, finish := .ret finishE }
  suffices hSim : ∀ (oa : OracleComp (unifSpec + G) aOut.denote) (s : σ.denote),
      (((simulateQ R.impl oa).run s) >>= fun bs =>
        pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))).IsQueryBoundP P k by
    change (R.eval A x).IsQueryBoundP P k
    unfold CostedReduction.eval
    simp only [R, Comp.eval, pure_bind]
    exact hSim (A (initE.eval (.cons x .nil)).1) (initE.eval (.cons x .nil)).2
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure b =>
    intro s
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    intro s
    rcases q with n | t
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          liftM (OracleSpec.query (spec := unifSpec + T₀) (.inl n)) >>= fun u =>
            (((simulateQ R.impl (mx u)).run s) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, _root_.ReductionDsl.handlerImpl,
          StateT.run_bind, StateT.run_lift, hFwdU, map_eq_bind_pure_comp, bind_assoc]
      rw [hStep, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (hP n), fun u => by simpa [hP n] using ih u s⟩
    · have hStep : ((simulateQ R.impl
          (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx)).run s) >>=
            (fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) =
          (((simulateQ R.impl
              (mx (C.rdec t (handleE.eval (.cons s (.cons (C.qenc t) .nil))).1))).run
            (handleE.eval (.cons s (.cons (C.qenc t) .nil))).2) >>=
              fun bs => pure (finishE.eval (.cons bs.2 (.cons bs.1 .nil)))) := by
        simp [R, CostedReduction.impl, _root_.ReductionDsl.handlerImpl, Comp.eval,
          StateT.run_bind, StateT.run_mk, pure_bind]
      rw [hStep]
      exact ih _ _

end Fig8Costed

/-! ## Concrete atomic bundle and bridges -/

section ConcreteAtomicFig8

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance : Inhabited Pt := ⟨0⟩

abbrev fig8RedsInst := @Bundles.fig8RedsInst

abbrev challSimDFAtomicProg := @Bundles.challSimDFAtomicProg
abbrev redCKAAuthDFAtomicProg := @Bundles.redCKAAuthDFAtomicProg
abbrev redPRNGAuthDFAtomicProg := @Bundles.redPRNGAuthDFAtomicProg
abbrev redFSAuthDFAtomicProg := @Bundles.redFSAuthDFAtomicProg

private theorem prngPureAuxBundle_samp_querySubsumes_local
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : LibsignalSession.Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (B0 : ℕ) (s : CKA.CKASamp)
    (z : ((PRFPRNG.prngIface (BitVec 256) (CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    QuerySubsumes
      (((Bundles.prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (Bundles.fSortCKA ℓ Pt) (Bundles.toDenCKA ℓ Pt) _ z)
          (.cons (idOf .A, idOf .B) .nil)))
      (toVal (Bundles.fSortCKA ℓ Pt) (Bundles.toDenCKA ℓ Pt)
        ((PRFPRNG.prngIface (BitVec 256) (CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (FSAEAD.RatchetSenderState (BitVec 256))
          (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ)
          (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (PRFPRNG.prngIface (BitVec 256) (CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (FSAEAD.RatchetSenderState (BitVec 256))
          (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ)
          (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((PRFPRNG.prngIface (BitVec 256) (CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (FSAEAD.RatchetSenderState (BitVec 256))
            (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ)
            (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply QuerySubsumes.of_eq
    exact (liftP_congr_local (prngTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    exact
      Bundles.querySubsumes_liftP_of_support_subset (prngTargetIface ℓ Pt)
        (PRFPRNG.prngIface (BitVec 256) (CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (FSAEAD.RatchetSenderState (BitVec 256))
          (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ)
          (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => by simp)

private theorem compilePrngAtomic_makesAtMostQueries_local
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : LibsignalSession.Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (B0 qOut : ℕ)
    (R : CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (PRFPRNG.prngIface (BitVec 256) (CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (FSAEAD.RatchetSenderState (BitVec 256))
        (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ)
        (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (SM.spec (LibsignalSim.Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (LibsignalSim.Fig8C Pt))
      (PRFPRNG.prngSMCodec (BitVec 256) (CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (FSAEAD.RatchetSenderState (BitVec 256))
        (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ)
        (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : Fig8Adv Pt ℓ)
    (hR : (R.eval (fun _ => A) ()).IsQueryBoundP (· matches .inr _) qOut) :
    PRFPRNG.MakesAtMostQueries
      ((Bundles.compilePrngAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ()) qOut := by
  unfold Bundles.compilePrngAtomic guardRed
  split_ifs with hℓ
  · have hsub := QuerySubsumes.compilePureAuxRed_querySubsumes
      (Bundles.prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (Bundles.ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
      R (Bundles.toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
      (Bundles.fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
      (Bundles.ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
      (prngPureAuxBundle_samp_querySubsumes_local Dh encPt C ℓ encT idOf lam B0)
      (fun g z => .of_eq (Bundles.prngPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
      (fun _ => rfl) (fun _ => rfl)
      (Bundles.fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
      (Bundles.fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
      (fun _ => A) (fun _ => A) id
      (fun _ => .of_eq (id_map (f := OracleComp _) A).symm)
      (fun _ => rfl)
      (outEq := id) (fun _ => rfl)
    rw [id_map] at hsub
    exact hsub.isQueryBoundP (fun _ => nofun)
      (LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
        (by rintro (_ | _) <;> rfl) hR)
  · unfold dummyRed
    apply pureRetRed_isQueryBoundP_local
    · intro; rfl
    · intro _ h; nomatch h

private theorem fig8RedsInst_redPRNGAuth_queries_local (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (t : ℕ) (A : Fig8Adv Pt ℓ) (hA : SM.MakesAtMostQueries A q) :
    PRFPRNG.MakesAtMostQueries
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGAuth tL t).eval
        (fun _ => A) ())
      (min (2 + 2 * q) (q + 3)) := by
  dsimp only [fig8RedsInst, Bundles.fig8RedsInst]
  refine compilePrngAtomic_makesAtMostQueries_local Dh encPt C ℓ encT idOf lam _ _ _ A ?_
  exact LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
    (by rintro (_ | _) <;> rfl)
    (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.redPRNGAuthBucketHybridProg_makesAtMostQueries
      (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL t q A hA)

private theorem fig8RedsInst_redFSAuth_queries_local (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (stage la : Bool) (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : Fig8Adv Pt ℓ) (hA : SM.MakesAtMostQueries A q) :
    FSAEAD.MakesAtMostQueries
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSAuth stage la j tL t).eval
        (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [fig8RedsInst, Bundles.fig8RedsInst]
  exact Computational.Proofs.SessionCostedFig8.BundlesMultiFsQueries.compileFsMultiAtomic_makesAtMostQueries
    ℓ Pt C Dh encPt encT idOf lam stage la
    ((q + 1) * (t - SM.Construction.healEpoch tL) + j) qep (min (2 * q) (q + 2))
    ((q + 1) * (maxForwardJumps + 1)) (min (2 * q) (q + 2)) _ A
    (Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase.redFSAuthMultiBucketProg_sess_isQueryBoundP
      ℓ Pt C Dh encPt encT idOf lam q ((q + 1) * (maxForwardJumps + 1)) qep
      (decide (j = 0)) la tL (decide (Party.senderOf t == .A)) A hA
      ((q + 1) * (t - SM.Construction.healEpoch tL) + j))

/-- All ten `GRedBounded` conjuncts and eight semantic query bounds of `fig8CostedBounds q qep`
for `fig8RedsInst`. -/
theorem fig8RedsInst_bounds (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    fig8CostedBounds q qep (fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q) := by
  refine ⟨ProgBounds.fig8RedsInst_challSim_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q hqep,
    fun i hi =>
      ProgBounds.fig8RedsInst_privRedB_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q i hi hqep,
    fun tL htL =>
      ProgBounds.fig8RedsInst_redCKAAuth_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q tL htL hqep,
    fun tL htL t ht => ?_,
    fun tL htL t _ j _ stage la => ?_,
    fun i hi tL htL =>
      ProgBounds.fig8RedsInst_redCKAPriv_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q i hi tL htL hqep,
    fun i hi tL htL =>
      ProgBounds.fig8RedsInst_redCKAPrivU_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q i hi tL htL hqep,
    fun i hi tL htL =>
      ProgBounds.fig8RedsInst_redPRNGPriv_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q i hi tL htL hqep,
    fun i hi =>
      ProgBounds.fig8RedsInst_redFSPriv_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q i hi hqep,
    fun i hi =>
      ProgBounds.fig8RedsInst_redFSPrivCoin_gRedBounded Dh encPt C codec ℓ encT idOf lam qep q i hi hqep,
    fun tL _ A hA =>
      ProgBounds.fig8RedsInst_redCKAAuth_queries_stage2 Dh encPt C codec ℓ encT idOf lam qep q tL A hA,
    fun i _ tL _ A hA =>
      ProgBounds.fig8RedsInst_redCKAPriv_queries_stage2 Dh encPt C codec ℓ encT idOf lam qep q tL i A hA,
    fun i _ tL _ A hA =>
      ProgBounds.fig8RedsInst_redCKAPrivU_queries_stage2 Dh encPt C codec ℓ encT idOf lam qep q tL i A hA,
    fun tL _ t _ A hA =>
      fig8RedsInst_redPRNGAuth_queries_local Dh encPt C codec ℓ encT idOf lam qep q tL t A hA,
    fun i _ tL _ A hA =>
      ProgBounds.fig8RedsInst_redPRNGPriv_queries_stage2 Dh encPt C codec ℓ encT idOf lam qep q tL i A hA,
    fun tL _ t _ j _ stage la A hA =>
      fig8RedsInst_redFSAuth_queries_local Dh encPt C codec ℓ encT idOf lam qep q stage la j tL t A hA,
    fun i _ A hA =>
      ProgBounds.fig8RedsInst_redFSPriv_queries_stage2 Dh encPt C codec ℓ encT idOf lam qep q i A hA,
    fun i _ A hA =>
      ProgBounds.fig8RedsInst_redFSPrivCoin_queries_stage2 Dh encPt C codec ℓ encT idOf lam qep q i A hA⟩
  · have ht_lt : t < qep + 2 := (Finset.mem_Ico.mp ht).2
    dsimp only [fig8RedsInst, Bundles.fig8RedsInst]
    exact ProgBounds.compilePrngAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
      (Computational.Proofs.SessionCostedFig8.BucketPRNGProgBounds.redPRNGAuthBucketHybridProg_parts_le_qep q qep t tL ht_lt htL)
      (Computational.Proofs.SessionCostedFig8.BucketPRNGProgBounds.redPRNGAuthBucketHybridProg_size_le_qep q qep t tL ht_lt htL hqep)
      (by rw [Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.redPRNGAuthBucketHybridProg_totalQueries]; omega)
  · have htL_all : ∀ x, tL = some x → x ≤ qep + 3 := by
      intro x hx
      subst hx
      simp only [SM.admissibleLastLeakGuesses, Finset.mem_insert,
        Finset.mem_image, Finset.mem_range, reduceCtorEq, Option.some.injEq, false_or] at htL
      rcases htL with ⟨y, hy, rfl⟩
      omega
    dsimp only [fig8RedsInst, Bundles.fig8RedsInst]
    exact Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase.redFSAuthMultiBucketAtomic_gRedBounded
      ℓ Pt C Dh encPt encT idOf lam stage la
      ((q + 1) * (t - SM.Construction.healEpoch tL) + j)
      q qep (min (2 * q) (q + 2)) ((q + 1) * (maxForwardJumps + 1))
      (decide (j = 0)) tL (decide (Party.senderOf t == .A))
      rfl (by omega) htL_all

theorem fig8RedsInst_challSim_eval (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q) :
    ((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).challSim.eval (fun _ => A) ()) =
      SM.Thm1.challSim (2 + 1) qep A :=
  BundlesEval.fig8RedsInst_challSim_eval Dh encPt C codec ℓ hℓ encT idOf lam qep q A hqA

theorem fig8RedsInst_privRedB_eval (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q i : ℕ)
    (A : Fig8Adv Pt ℓ) (hqA : SM.MakesAtMostQueries A q) :
    (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).privRedB i).eval (fun _ => A) ()) =
      SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) A :=
  BundlesEval.fig8RedsInst_privRedB_eval Dh encPt C codec ℓ hℓ encT idOf lam qep q i A hqA

omit [DecidableEq Pt] in
theorem ckaAdvantage_dhSchemeFb_eq (Dh : DHFun (BitVec 256) Pt) (Δ tStar : ℕ)
    (A : CKA.Adversary (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) :
    CKA.advantage (dhSchemeFb Dh) Δ tStar A = CKA.advantage (dhScheme Dh) Δ tStar A := by
  rw [CKA.advantage_eq_boolDist, CKA.advantage_eq_boolDist,
    ckaBranch_dhSchemeFb_eq Dh Δ tStar true A, ckaBranch_dhSchemeFb_eq Dh Δ tStar false A]

/-! ## Mixture advantage bridges -/

theorem fig8RedsInst_redCKAPriv_advAvg_advantage {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (lam : Pt) (qep q tStar : ℕ) (tL : Option ℕ) (i : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    CKA.advantage (dhScheme Dh) 1 tStar
      (advAvg oa fun o =>
        ((fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redCKAPriv tL i).eval
          (fun _ => A o) ()) =
    CKA.advantage (dhScheme Dh) 1 tStar
      (advAvg oa fun o =>
        SM.Construction.redCKAPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o)) := by
  subst hc
  rw [QuerySubsumes.ckaAdvantage_advAvg_congr (dhScheme Dh) 1 tStar oa fun o =>
      BundlesEval.fig8RedsInst_redCKAPriv_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT (idOf o) lam qep q tL i (A o) (hqA o)]
  rw [CKA.advantage_eq_boolDist, CKA.advantage_eq_boolDist,
    ckaBranch_avg, ckaBranch_avg, ckaBranch_avg, ckaBranch_avg]
  have hBr : ∀ b,
      (oa >>= fun o => CKA.branch (dhScheme Dh) 1 tStar b
        (SM.Construction.redCKAPriv (dhSchemeFb Dh) (rootPRNG C.F encPt)
          (fsAtomicB C ℓ encT (idOf o) ((q + 1) * (maxForwardJumps + 1)))
          lam 1 qep tL i (A o))) =
      (oa >>= fun o => CKA.branch (dhScheme Dh) 1 tStar b
        (SM.Construction.redCKAPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o))) :=
    fun b => bind_congr fun o => by
      rw [← ckaBranch_dhSchemeFb_eq]
      exact FsAtomicBSwap.ckaBranch_redCKAPriv_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT (idOf o)
        lam ((q + 1) * (maxForwardJumps + 1)) q 1 tStar qep tL i b (Nat.le_refl _)
        (A o) q (hqA o) (Nat.le_refl q) (hshA o)
  rw [hBr true, hBr false]

theorem fig8RedsInst_redPRNGPriv_advAvg_advantage {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : LibsignalSession.Crypto) (codec : SignalMessageProtoCodec)
    (hc : codec = protoSignalCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (i : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (advAvg oa fun o =>
        ((fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redPRNGPriv tL i).eval
          (fun _ => A o) ()) =
    PRFPRNG.advantage (rootPRNG C.F encPt)
      (advAvg oa fun o =>
        SM.Construction.redPRNGPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o)) := by
  subst hc
  rw [QuerySubsumes.prngAdvantage_advAvg_congr (rootPRNG C.F encPt) oa fun o =>
      BundlesEval.fig8RedsInst_redPRNGPriv_prog_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT (idOf o) lam qep q tL i (A o)]
  rw [PRFPRNG.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist,
    prngBranch_avg, prngBranch_avg, prngBranch_avg, prngBranch_avg]
  have hBr : ∀ b,
      (oa >>= fun o => PRFPRNG.branch (rootPRNG C.F encPt) b
        ((SM.Construction.redPRNGPrivProg (q + 1) ((q + 1) * (maxForwardJumps + 1))
          1 qep maxForwardJumps tL i :
          CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT (idOf o) lam
            ((q + 1) * (maxForwardJumps + 1)))
            (PRFPRNG.prngIface (BitVec 256) (CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
              (BitVec 256) (BitVec 256) (BitVec 256)
              (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
              ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
            _ _ .unit .unit .bool .bool).eval (fun _ => A o) ())) =
      (oa >>= fun o => PRFPRNG.branch (rootPRNG C.F encPt) b
        (SM.Construction.redPRNGPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o))) :=
    fun b => bind_congr fun o => by
      rw [BundlesEval.redPRNGPrivProg_branch_eval_atomic Dh encPt C ℓ encT (idOf o)
        lam qep q tL i (A o) (hqA o) b,
        FsAtomicBSwap.redPRNGPriv_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT (idOf o) lam
          ((q + 1) * (maxForwardJumps + 1)) q 1 qep tL i (Nat.le_refl _) (A o) q (hqA o)
          (Nat.le_refl q) (hshA o)]
  rw [hBr true, hBr false]


private theorem isQueryBoundP_zero_mono {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {oa : OracleComp spec α} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (hqp : ∀ x, q x → p x) (h : IsQueryBoundP oa p 0) : IsQueryBoundP oa q 0 := by
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    have hnp : ¬ p t := h.1.resolve_right (Nat.not_lt_zero 0)
    have hnq : ¬ q t := mt (hqp t) hnp
    exact ⟨Or.inl hnq, fun u => by
      have hu := h.2 u
      simp only [hnp, ite_false] at hu
      simpa [hnq] using ih u hu⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem encMsgsOk_shortB_of_atomicShortPubB {SS RS AD C : Type} {ℓ : ℕ}
    {R : FSAEAD.Adversary SS RS AD (LibsignalMsgPublicPart × Plain ℓ) C}
    (h : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) R) :
    FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) R := by
  refine isQueryBoundP_zero_mono (fun t ht => ?_) h
  rcases t with _ | (((((⟨_, m⟩ | ⟨_, m₀, m₁⟩) | _) | _) | _) | _)
  · cases ht
  · simp only [FSAEAD.encBadMsg, Bool.not_eq_true'] at ht ⊢
    cases hat : atomicShortPubB m.1
    · rfl
    · rw [atomicShortPubB_imp_shortB hat] at ht; cases ht
  · simp only [FSAEAD.encBadMsg, Bool.or_eq_true, Bool.not_eq_true'] at ht ⊢
    rcases ht with ht₀ | ht₁
    · left
      cases hat : atomicShortPubB m₀.1
      · rfl
      · rw [atomicShortPubB_imp_shortB hat] at ht₀; cases ht₀
    · right
      cases hat : atomicShortPubB m₁.1
      · rfl
      · rw [atomicShortPubB_imp_shortB hat] at ht₁; cases ht₁
  all_goals cases ht

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem fsClamp_fsAtomicB_fsSendShort (C : LibsignalSession.Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (B B0 : ℕ) :
    LibsignalSM.Proofs.SessionShort.FSAEADRed.FsSendShort
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) := by
  intro ss hdr m hm
  change ((fsAtomicB C ℓ encT idOf B0).send ss hdr m).2.2.1.1.length + 8 < 2 ^ 32
  rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  exact LibsignalSM.Proofs.SessionShort.FSAEADRed.lFS_fsSendShort C protoSignalCodec
    signalEncodeFits32_proto ℓ (by omega) encT idOf maxForwardJumps ss hdr m
    (atomicShortPubB_imp_shortB hm)

end ConcreteAtomicFig8

end

end CryptoVerification.LibsignalSession

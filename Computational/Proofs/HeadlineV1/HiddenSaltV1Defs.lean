/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.CouplingV1 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.SteerCoupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.CorrSend
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Eager
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Eager
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Inject
import ProofLib.SepLogic.WP.StepsCore
import LibsignalBinary.Proofs.SpqrV1.KemFailFindFacts -- shake: keep
import Computational.Proofs.HeadlineV1.SignedRefineC -- shake: keep
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.StateInv -- shake: keep
import Computational.Proofs.SpqrV1Sync.TopLog
import LibsignalBinary.Proofs.SpqrV1Sync.CoinBridge
import LibsignalBinary.Proofs.SpqrV1.MlKemCorrectFacts
import VCVio.ProgramLogic.Unary.HoareTriple
import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip
import Computational.Proofs.CryptoGames.SM.LibsignalCorrNoInj
import Computational.Specifications.Session.ACD19.Ratchet.LibsignalSim
import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
import Computational.Proofs.SpqrV1Sync.SendTotal -- shake: keep
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePRNG
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10Aux
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.Fig8ExcessCosts
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds
import ToMathlib.Control.StateT
import VCVio.CryptoFoundations.SecExp
import VCVio.EvalDist.EvalDistEq
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Hidden-salt glue for the V1 headline

**Checked by Lean.** Proves the `DeliverForge` coupling, `KemFailFind` tracking reduction, and
evicted-wire spurious-key invariants behind `HiddenSaltBoundHolds` (`hiddenSaltTerm ≤
hiddenSaltBound`).
-/
public section

set_option autoImplicit true
set_option linter.unusedSimpArgs false

open OracleComp OracleSpec ENNReal MeasureTheory
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal
  (Encaps1Total spqrV1Send_msg_len_lt spqrV1SessionB_sendCorrectQ)
open CryptoVerification.E2E (partyIdentityKey paramsIdsWithSpqr)
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqrV1
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Correctness
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

namespace CryptoGames.LibsignalSM.Proofs.Refinement


variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

/-! ## `DeliverForge` triviality -/

/-- An uncompromised in-transit record is never trivial under any healing delay `Δ`. -/
theorem trivial_false_of_inTransit_uncomp {St Msg C : Type} [DecidableEq C]
    {s : CryptoGames.SM.GameState St Msg C} {Q : Party} {c : C} {r : CryptoGames.SM.Record Msg C} (Δ : ℕ)
    (htr : s.inTransit Q c = some r) (hcomp : s.comp.contains r.pos = false) :
    s.trivial Δ r.pos = false := by
  have hmem : r ∈ s.trans := List.mem_of_find?_eq_some htr
  have hany : s.trans.any (fun r' => r'.pos == r.pos) = true :=
    List.any_eq_true.mpr ⟨r, hmem, beq_self_eq_true _⟩
  have hmem_f : r.pos ∉ s.comp := by
    simpa using hcomp
  simp [CryptoGames.SM.GameState.trivial, hmem_f, hany]

end CryptoGames.LibsignalSM.Proofs.Refinement

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoGames.LibsignalSM.Proofs.Refinement

variable {Pt PQ : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]

/-! ## `fig8ToDFImpl` and `deliverForgeHook` coupling -/

section DeliverForgeStepLemmas


omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_inl_run (ℓ : ℕ) (n : unifSpec.Domain) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inl n)).run sent =
      (liftM (OracleSpec.query (spec := unifSpec +
        CryptoGames.SM.Construction.DeliverForge.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n)) >>=
        fun u => pure (u, sent)) := by
  simp [fig8ToDFImpl, StateT.run_lift, map_eq_bind_pure_comp]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_transmit_run (ℓ : ℕ) (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ)
    (r : Option (BitVec 256)) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inl (Q, m, r))))))).run sent =
      (CryptoGames.SM.Construction.DeliverForge.transmitQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q m r >>=
        fun res => pure (res, match res with | some c => c :: sent | none => sent)) := by
  simp only [fig8ToDFImpl, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  congr 1; funext res
  cases res <;> simp [StateT.run_modify]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_chall_run (ℓ : ℕ) (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ)
    (r : Option (BitVec 256)) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))))).run sent =
      (CryptoGames.SM.Construction.DeliverForge.challQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
        Q m₀ m₁ r >>=
        fun res => pure (res, match res with | some c => c :: sent | none => sent)) := by
  simp only [fig8ToDFImpl, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  congr 1; funext res
  cases res <;> simp [StateT.run_modify]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_deliver_run (ℓ : ℕ) (Q : Party) (c : Fig8C Pt) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inr (Q, c)))))).run sent =
      (CryptoGames.SM.Construction.DeliverForge.deliverQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c >>=
        fun res => pure (res, sent)) := by
  simp [fig8ToDFImpl, StateT.run_lift, map_eq_bind_pure_comp]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_inject_run (ℓ : ℕ) (Q : Party) (c : Fig8C Pt) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inr (.inl (.inr (Q, c))))).run sent =
      (CryptoGames.SM.Construction.DeliverForge.injectQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c >>=
        fun res => pure (res, sent)) := by
  simp [fig8ToDFImpl, StateT.run_lift, map_eq_bind_pure_comp]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_corr_run (ℓ : ℕ) (Q : Party) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inr (.inr Q))).run sent =
      (CryptoGames.SM.Construction.DeliverForge.corrQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q >>=
        fun res => pure (res, sent)) := by
  simp [fig8ToDFImpl, StateT.run_lift, map_eq_bind_pure_comp]

omit [Zero Pt] [SampleableType Pt] in
theorem deliverForgeHook_probe_run (ℓ : ℕ) (Q : Party) (c' : Fig8C Pt)
    (sent : List (Fig8C Pt)) :
    ((deliverForgeHook Pt ℓ).probe Q c').run sent =
      match sent.find? (fun c => sameWireFig8 c c') with
      | some c =>
          CryptoGames.SM.Construction.DeliverForge.deliverForgeQuery
            (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
            Q c c' >>= fun _ => pure ((), sent)
      | none => pure ((), sent) := by
  simp only [deliverForgeHook, StateT.run_bind, StateT.run_get, pure_bind]
  cases sent.find? (fun c => sameWireFig8 c c') with
  | none => simp [StateT.run_pure]
  | some c => simp [StateT.run_lift, map_eq_bind_pure_comp]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fullImplDF_inr_inl_of_forgeWin_false
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (sameHdr : C → C → Bool) (cfg : CryptoGames.SM.Config Msg)
    (q : (CryptoGames.SM.spec St Msg Coins C).Domain)
    (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF St Msg C) (hfw : s.forgeWin = false) :
    (CryptoGames.SM.Construction.DeliverForge.fullImplDF sm Δ qep sameHdr cfg (.inr (.inl q))).run s =
      ((CryptoGames.SM.oracleImpl sm Δ qep cfg q).run s.base >>=
        fun z => pure (z.1, { s with base := z.2 })) := by
  change (CryptoGames.SM.Construction.DeliverForge.liftBaseImpl (CryptoGames.SM.oracleImpl sm Δ qep cfg) CryptoGames.SM.Construction.DeliverForge.noneOutBase q).run s =
    _
  unfold CryptoGames.SM.Construction.DeliverForge.liftBaseImpl
  simp [hfw, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set]

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_inl
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (n : unifSpec.Domain)
    (sent : List (Fig8C Pt))
    (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inl n)).run sent)).run s =
      ((fig8ImplH1 fig qepF (.inl n)).run s.base >>=
        fun z => pure ((z.1, sent), { s with base := z.2 })) := by
  rw [fig8ToDFImpl_inl_run]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  change ((liftM (OracleSpec.query (spec := unifSpec) n) :
      StateT (CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp _).run
        s >>=
    fun z => pure ((z.1, sent), z.2)) =
    ((liftM (OracleSpec.query (spec := unifSpec) n) :
      StateT (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp _).run s.base >>=
    fun z => pure ((z.1, sent), { s with base := z.2 }))
  simp [StateT.run_monadLift]

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_transmit
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (sent : List (Fig8C Pt))
    (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inl (Q, m, r))))))).run sent)).run s =
      ((CryptoGames.SM.transmitImpl fig (2 + 1) qepF (Q, m, r)).run s.base >>=
        fun z => pure ((z.1, match z.1 with | some c => c :: sent | none => sent),
          { s with base := z.2 })) := by
  rw [fig8ToDFImpl_transmit_run]
  unfold CryptoGames.SM.Construction.DeliverForge.transmitQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [fullImplDF_inr_inl_of_forgeWin_false fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1
    (.inl (.inl (.inl (.inl (Q, m, r))))) s hfw]
  simp only [bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun z => ?_)
  rcases z with ⟨res, b'⟩
  cases res <;> rfl

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_chall
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (sent : List (Fig8C Pt))
    (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))))).run sent)).run s =
      ((CryptoGames.SM.challImpl fig (2 + 1) qepF CryptoGames.SM.Config.h1 (Q, m₀, m₁, r)).run s.base >>=
        fun z => pure ((z.1, match z.1 with | some c => c :: sent | none => sent),
          { s with base := z.2 })) := by
  rw [fig8ToDFImpl_chall_run]
  unfold CryptoGames.SM.Construction.DeliverForge.challQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [fullImplDF_inr_inl_of_forgeWin_false fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1
    (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) s hfw]
  simp only [bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun z => ?_)
  rcases z with ⟨res, b'⟩
  cases res <;> rfl

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_deliver
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (c : Fig8C Pt) (sent : List (Fig8C Pt))
    (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inr (Q, c)))))).run sent)).run s =
      ((CryptoGames.SM.deliverImpl fig CryptoGames.SM.Config.h1 (Q, c)).run s.base >>=
        fun z => pure ((z.1, sent), { s with base := z.2 })) := by
  rw [fig8ToDFImpl_deliver_run]
  unfold CryptoGames.SM.Construction.DeliverForge.deliverQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [fullImplDF_inr_inl_of_forgeWin_false fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1
    (.inl (.inl (.inr (Q, c)))) s hfw]
  simp
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_inject
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (c : Fig8C Pt) (sent : List (Fig8C Pt))
    (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inr (Q, c))))).run sent)).run s =
      ((CryptoGames.SM.injectImpl fig (2 + 1) qepF CryptoGames.SM.Config.h1 (Q, c)).run s.base >>=
        fun z => pure ((z.1, sent), { s with base := z.2 })) := by
  rw [fig8ToDFImpl_inject_run]
  unfold CryptoGames.SM.Construction.DeliverForge.injectQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [fullImplDF_inr_inl_of_forgeWin_false fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1
    (.inl (.inr (Q, c))) s hfw]
  simp
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_corr
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (sent : List (Fig8C Pt))
    (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inr (.inr Q))).run sent)).run s =
      ((CryptoGames.SM.corrImpl Q).run s.base >>=
        fun z => pure ((z.1, sent), { s with base := z.2 })) := by
  rw [fig8ToDFImpl_corr_run]
  unfold CryptoGames.SM.Construction.DeliverForge.corrQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [fullImplDF_inr_inl_of_forgeWin_false fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1
    (.inr Q) s hfw]
  simp
  rfl

/-- Updates the recorded `sent` ciphertext list after a single Fig. 8 query. -/
@[expose] def updSentFig8 (Pt : Type) (ℓ : ℕ)
    (q : (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (res : (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Range q)
    (sent : List (Fig8C Pt)) : List (Fig8C Pt) :=
  match q, res with
  | .inr (.inl (.inl (.inl (.inl _)))), some c => c :: sent
  | .inr (.inl (.inl (.inl (.inr _)))), some c => c :: sent
  | _, _ => sent

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem mem_updSentFig8_of_mem {ℓ : ℕ}
    (q : (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (res : (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Range q)
    {sent : List (Fig8C Pt)} {c₀ : Fig8C Pt} (hmem : c₀ ∈ sent) :
    c₀ ∈ updSentFig8 Pt ℓ q res sent := by
  rcases q with n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
  · exact hmem
  · cases res <;> simp [updSentFig8, hmem]
  · cases res <;> simp [updSentFig8, hmem]
  · exact hmem
  · exact hmem
  · exact hmem

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_of_forgeWin_false
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (q : (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (sent : List (Fig8C Pt))
    (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ q).run sent)).run s =
      ((fig8ImplH1 fig qepF q).run s.base >>=
        fun z => pure ((z.1, updSentFig8 Pt ℓ q z.1 sent), { s with base := z.2 })) := by
  rcases q with n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
  · exact simulateQ_fullImplDF_fig8ToDFImpl_inl fig qepF sameHdr n sent s
  · rw [simulateQ_fullImplDF_fig8ToDFImpl_transmit fig qepF sameHdr Q m r sent s hfw]
    refine congrArg (_ >>= ·) (funext fun z => ?_)
    rcases z with ⟨res, b'⟩
    cases res <;> rfl
  · rw [simulateQ_fullImplDF_fig8ToDFImpl_chall fig qepF sameHdr Q m₀ m₁ r sent s hfw]
    refine congrArg (_ >>= ·) (funext fun z => ?_)
    rcases z with ⟨res, b'⟩
    cases res <;> rfl
  · exact simulateQ_fullImplDF_fig8ToDFImpl_deliver fig qepF sameHdr Q c sent s hfw
  · exact simulateQ_fullImplDF_fig8ToDFImpl_inject fig qepF sameHdr Q c sent s hfw
  · exact simulateQ_fullImplDF_fig8ToDFImpl_corr fig qepF sameHdr Q sent s hfw

omit [Zero Pt] [SampleableType Pt] in
/-- While `s.forgeWin = false`, `deliverForgeHook.lift` couples with `fig8ImplH1` on `s.base`. -/
theorem deliverForgeHook_lift_bind_base_eq_of_forgeWin_false
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    {α : Type} (x : Fig8Comp Pt ℓ α) :
    ∀ (sent : List (Fig8C Pt))
      (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      s.forgeWin = false →
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
          (((deliverForgeHook Pt ℓ).lift x).run sent)).run s >>=
        fun z => pure (z.1.1, z.2.base)) =
        (simulateQ (fig8ImplH1 fig qepF) x).run s.base := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro sent s _
    simp [deliverForgeHook]
  | query_bind q r ih =>
    intro sent s hfw
    change ((simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
        (((fig8ToDFImpl Pt ℓ q).run sent) >>=
          fun p => ((deliverForgeHook Pt ℓ).lift (r p.1)).run p.2)).run s >>=
        fun z => pure (z.1.1, z.2.base)) = _
    rw [simulateQ_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]
    rw [simulateQ_fullImplDF_fig8ToDFImpl_of_forgeWin_false fig qepF sameHdr q sent s hfw]
    simp only [bind_assoc, pure_bind]
    refine congrArg (_ >>= ·) (funext fun z => ?_)
    exact ih z.1 (updSentFig8 Pt ℓ q z.1 sent) { s with base := z.2 } hfw

omit [Zero Pt] [SampleableType Pt] in
theorem inTransit_ct_mem_updSentFig8
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ)
    (q : (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (sent : List (Fig8C Pt))
    (s : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hsent : ∀ r ∈ s.trans, r.ct ∈ sent)
    (z : (unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Range q ×
      CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hz : z ∈ support ((fig8ImplH1 fig qepF q).run s)) :
    ∀ r ∈ z.2.trans, r.ct ∈ updSentFig8 Pt ℓ q z.1 sent := by
  have hep_trans : ∀ Q bad s₁,
      s.epMgmt (2 + 1) qepF Q bad = some s₁ → s₁.trans = s.trans := by
    intro Q bad s₁ hep
    unfold CryptoGames.SM.GameState.epMgmt CryptoGames.SM.GameState.leak at hep
    by_cases hs : Q.sendsIn (s.epoch Q + 1) = true
    · by_cases hq : qepF < s.epoch Q + 1
      · simp [hs, hq] at hep
      · cases bad <;> cases hsc : s.safeCh (2 + 1) Q <;>
          simp [hs, hq, hsc] at hep <;>
          (subst hep; rfl)
    · by_cases hq : qepF < s.epoch Q <;> simp [hs, hq] at hep
      subst hep; rfl
  rcases q with n | ((((⟨Q, m, ro⟩ | ⟨Q, m₀, m₁, ro⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
  · change z ∈ support ((liftM (OracleSpec.query (spec := unifSpec) n) :
        StateT (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp _).run s) at hz
    simp only [StateT.run_monadLift, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact hsent
  · change z ∈ support ((CryptoGames.SM.transmitImpl fig (2 + 1) qepF (Q, m, ro)).run s) at hz
    unfold CryptoGames.SM.transmitImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hsent
    · simp only [StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hep : s.epMgmt (2 + 1) qepF Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hsent
      | some s₁ =>
        simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz
        intro r hr
        simp only [CryptoGames.SM.GameState.record, List.mem_cons] at hr
        rcases hr with rfl | hr
        · simp [updSentFig8]
        · rw [hep_trans Q cb.2 s₁ hep] at hr
          exact List.mem_cons_of_mem _ (hsent r hr)
  · change z ∈ support ((CryptoGames.SM.challImpl fig (2 + 1) qepF CryptoGames.SM.Config.h1 (Q, m₀, m₁, ro)).run s) at hz
    unfold CryptoGames.SM.challImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hsent
    · simp only [StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hep : s.epMgmt (2 + 1) qepF Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hsent
      | some s₁ =>
        simp only [hep] at hz
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hsent
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz
          intro r hr
          simp only [CryptoGames.SM.GameState.record, List.mem_cons] at hr
          rcases hr with rfl | hr
          · simp [updSentFig8]
          · rw [hep_trans Q cb.2 s₁ hep] at hr
            exact List.mem_cons_of_mem _ (hsent r hr)
  · change z ∈ support ((CryptoGames.SM.deliverImpl fig CryptoGames.SM.Config.h1 (Q, c)).run s) at hz
    unfold CryptoGames.SM.deliverImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hsent
    · cases hin : s.inTransit Q.other c with
      | none =>
        simp only [hin, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hsent
      | some r₀ =>
        simp only [hin] at hz
        cases hrec : fig.receive (s.st Q) c with
        | none =>
          simp only [hrec] at hz
          split at hz <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz <;>
            (subst hz; exact hsent)
        | some res' =>
          rcases res' with ⟨st', t', i', m'⟩
          simp only [hrec] at hz
          split at hz <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz <;>
            (subst hz; intro r hr; exact hsent r (List.mem_of_mem_filter hr))
  · change z ∈ support ((CryptoGames.SM.injectImpl fig (2 + 1) qepF CryptoGames.SM.Config.h1 (Q, c)).run s) at hz
    unfold CryptoGames.SM.injectImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hsent
    · cases hrec : fig.receive (s.st Q) c with
      | none =>
        simp only [hrec, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hsent
      | some res' =>
        rcases res' with ⟨st', t', i', m'⟩
        simp only [hrec] at hz
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hsent
        · split at hz
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz
            subst hz; intro r hr; exact hsent r (List.mem_of_mem_filter hr)
          · split at hz <;>
              simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hz <;>
              (subst hz; exact hsent)
  · change z ∈ support ((CryptoGames.SM.corrImpl Q).run s) at hz
    unfold CryptoGames.SM.corrImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz <;>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz <;>
      (subst hz; exact hsent)

omit [Zero Pt] [SampleableType Pt] in
theorem deliverForgeHook_lift_support_invariants
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    {α : Type} (x : Fig8Comp Pt ℓ α) :
    ∀ (sent : List (Fig8C Pt))
      (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (z : (α × List (Fig8C Pt)) ×
        CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      s.forgeWin = false →
      z ∈ support
        ((simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
          (((deliverForgeHook Pt ℓ).lift x).run sent)).run s) →
      z.2.forgeWin = false ∧
      (z.1.1, z.2.base) ∈ support ((simulateQ (fig8ImplH1 fig qepF) x).run s.base) ∧
      (∀ c ∈ sent, c ∈ z.1.2) ∧
      ((∀ r ∈ s.base.trans, r.ct ∈ sent) → ∀ r ∈ z.2.base.trans, r.ct ∈ z.1.2) := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro sent s z hfw hz
    simp only [deliverForgeHook, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz ⊢
    subst hz
    exact ⟨hfw, rfl, fun _ hc => hc, fun htr => htr⟩
  | query_bind q r ih =>
    intro sent s z hfw hz
    change z ∈ support
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
        (((fig8ToDFImpl Pt ℓ q).run sent) >>=
          fun p => ((deliverForgeHook Pt ℓ).lift (r p.1)).run p.2)).run s) at hz
    rw [simulateQ_bind, StateT.run_bind,
      simulateQ_fullImplDF_fig8ToDFImpl_of_forgeWin_false fig qepF sameHdr q sent s hfw] at hz
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨z₀, hz₀, hz_cont⟩
    rcases ih z₀.1 (updSentFig8 Pt ℓ q z₀.1 sent) { s with base := z₀.2 } z hfw hz_cont with
      ⟨hfw', hsup', hsent', htr'⟩
    refine ⟨hfw', ?_, fun c hc => hsent' c (mem_updSentFig8_of_mem q z₀.1 hc),
      fun htr => htr' (inTransit_ct_mem_updSentFig8 fig qepF q sent s.base htr z₀ hz₀)⟩
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind]
    exact ⟨z₀, hz₀, hsup'⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem bind_eq_of_support_imp {α β γ : Type} (m : ProbComp α) (P : α → Prop)
    (proj : α → β) (f : α → ProbComp γ) (g : β → ProbComp γ)
    (hP : ∀ a ∈ support m, P a)
    (hfg : ∀ a, P a → f a = g (proj a)) :
    (m >>= f) = ((m >>= fun a => pure (proj a)) >>= g) := by
  induction m using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact hfg a (hP a (by simp))
  | query_bind t r ih =>
    simp only [bind_assoc]
    refine congrArg (_ >>= ·) (funext fun u => ?_)
    rw [ih u (fun a ha => hP a (by
      rw [MonadAttach.mem_support_bind]
      exact ⟨u, by simp, ha⟩))]
    simp only [bind_assoc]

/-- Coupling relation between `probeHook` and `deliverForgeHook` when no probe fires. -/
@[expose] def df_noProbe_rel {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α)
    (mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α) :
    Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
    s.forgeWin = false →
    ((simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
        ((mDF.run sC).run sent)).run s >>=
      fun z => pure (z.1.1, (z.2.base, false))) =
      ((mPr.run sC).run (s.base, false)) ∧
    ∀ z ∈ support
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
        ((mDF.run sC).run sent)).run s),
      z.2.forgeWin = false ∧
      (∀ c ∈ sent, c ∈ z.1.2) ∧
      ((∀ r ∈ s.base.trans, r.ct ∈ sent) → ∀ r ∈ z.2.base.trans, r.ct ∈ z.1.2)

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_pure {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (a : α) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr (pure a) (pure a) := by
  intro sC sent s hfw
  refine ⟨by simp, fun z hz => ?_⟩
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hfw, fun _ hc => hc, fun htr => htr⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_bind {PQ α β : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ} {sameHdr : Fig8C Pt → Fig8C Pt → Bool}
    {mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α}
    {kPr : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    {kDF : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) β}
    (hm : df_noProbe_rel fig qepF sameHdr mPr mDF)
    (hk : ∀ a, df_noProbe_rel fig qepF sameHdr (kPr a) (kDF a)) :
    df_noProbe_rel fig qepF sameHdr (mPr >>= kPr) (mDF >>= kDF) := by
  intro sC sent s hfw
  refine ⟨?_, ?_⟩
  · simp only [StateT.run_bind, simulateQ_bind, bind_assoc]
    rw [← (hm sC sent s hfw).1]
    exact bind_eq_of_support_imp
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
        ((mDF.run sC).run sent)).run s)
      (fun z => z.2.forgeWin = false)
      (fun z => (z.1.1, (z.2.base, false)))
      (fun z => (simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
        (((kDF z.1.1.1).run z.1.1.2).run z.1.2)).run z.2 >>=
          fun z' => pure (z'.1.1, (z'.2.base, false)))
      (fun r => ((kPr r.1.1).run r.1.2).run r.2)
      (fun z hz => ((hm sC sent s hfw).2 z hz).1)
      (fun z hfw' => (hk z.1.1.1 z.1.1.2 z.1.2 z.2 hfw').1)
  · intro z hz
    simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨z₀, hz₀, hz₁⟩
    rcases (hm sC sent s hfw).2 z₀ hz₀ with ⟨hfw₀, hsent₀, htr₀⟩
    rcases (hk z₀.1.1.1 z₀.1.1.2 z₀.1.2 z₀.2 hfw₀).2 z hz₁ with ⟨hfw₁, hsent₁, htr₁⟩
    exact ⟨hfw₁, fun c hc => hsent₁ c (hsent₀ c hc), fun htr => htr₁ (htr₀ htr)⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_get (PQ : Type)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr
      (get : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (LibsignalToModularSchemeSimState PQ Pt ℓ))
      (get : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) (LibsignalToModularSchemeSimState PQ Pt ℓ)) := by
  intro sC sent s hfw
  refine ⟨by simp, fun z hz => ?_⟩
  simp only [StateT.run_get, StateT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hfw, fun _ hc => hc, fun htr => htr⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_set {PQ : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr
      (set sC' : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) PUnit)
      (set sC' : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) PUnit) := by
  intro sC sent s hfw
  refine ⟨by simp, fun z hz => ?_⟩
  simp only [StateT.run_set, StateT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hfw, fun _ hc => hc, fun htr => htr⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_modify {PQ : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr
      (modify f : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) PUnit)
      (modify f : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) PUnit) := by
  intro sC sent s hfw
  refine ⟨by simp, fun z hz => ?_⟩
  simp only [StateT.run_modify, StateT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hfw, fun _ hc => hc, fun htr => htr⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_ite {PQ α : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ} {sameHdr : Fig8C Pt → Fig8C Pt → Bool} {P_cond : Prop} [Decidable P_cond]
    {tPr ePr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {tDF eDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α}
    (ht : df_noProbe_rel fig qepF sameHdr tPr tDF)
    (he : df_noProbe_rel fig qepF sameHdr ePr eDF) :
    df_noProbe_rel fig qepF sameHdr
      (if P_cond then tPr else ePr) (if P_cond then tDF else eDF) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift x).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) x).run gh.1 >>= fun p => pure (p.1, (p.2, gh.2))) :=
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem zoomB_probeHook_run {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((runOnBaseState (probeHook fig qepF) x).run sC).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) (x.run sC.base)).run gh.1 >>= fun r =>
        pure ((r.1.1, { sC with base := r.1.2 }), (r.2, gh.2))) := by
  change (((probeHook fig qepF).lift (x.run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh = _
  rw [StateT.run_bind, probeHook_lift_run]
  simp only [bind_assoc, pure_bind, StateT.run_pure]

omit [Zero Pt] [SampleableType Pt] in
theorem zoomB_deliverForgeHook_run {PQ α : Type}
    (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt)) :
    ((runOnBaseState (deliverForgeHook Pt ℓ) x).run sC).run sent =
      (((deliverForgeHook Pt ℓ).lift (x.run sC.base)).run sent >>= fun p =>
        pure ((p.1.1, { sC with base := p.1.2 }), p.2)) :=
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_zoomB {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr
      (runOnBaseState (probeHook fig qepF) x)
      (runOnBaseState (deliverForgeHook Pt ℓ) x) := by
  intro sC sent s hfw
  refine ⟨?_, ?_⟩
  · rw [zoomB_deliverForgeHook_run, zoomB_probeHook_run, simulateQ_bind, StateT.run_bind]
    simp only [simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    rw [← deliverForgeHook_lift_bind_base_eq_of_forgeWin_false fig qepF sameHdr (x.run sC.base)
      sent s hfw]
    simp only [bind_assoc, pure_bind]
  · intro z hz
    rw [zoomB_deliverForgeHook_run, simulateQ_bind, StateT.run_bind] at hz
    simp only [simulateQ_pure, StateT.run_pure, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨z₀, hz₀, rfl⟩
    rcases deliverForgeHook_lift_support_invariants fig qepF sameHdr (x.run sC.base) sent s z₀
      hfw hz₀ with ⟨hfw', _, hsent', htr'⟩
    exact ⟨hfw', hsent', htr'⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_liftC {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (x : Fig8Comp Pt ℓ α) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr
      (CryptoGames.Ratchet.LibsignalSimC.liftC (probeHook fig qepF) x)
      (CryptoGames.Ratchet.LibsignalSimC.liftC (deliverForgeHook Pt ℓ) x) := by
  intro sC sent s hfw
  unfold CryptoGames.Ratchet.LibsignalSimC.liftC
  refine ⟨?_, ?_⟩
  · simp only [StateT.run_lift, probeHook_lift_run, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    rw [← deliverForgeHook_lift_bind_base_eq_of_forgeWin_false fig qepF sameHdr x sent s hfw]
    simp only [bind_assoc, pure_bind]
  · intro z hz
    simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨z₀, hz₀, rfl⟩
    rcases deliverForgeHook_lift_support_invariants fig qepF sameHdr x sent s z₀ hfw hz₀ with
      ⟨hfw', _, hsent', htr'⟩
    exact ⟨hfw', hsent', htr'⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_guardC {PQ α : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ} {sameHdr : Fig8C Pt → Fig8C Pt → Bool}
    {mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    {mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) (Option α)}
    (hm : df_noProbe_rel fig qepF sameHdr mPr mDF) :
    df_noProbe_rel fig qepF sameHdr (CryptoGames.Ratchet.LibsignalSimC.guardC mPr) (CryptoGames.Ratchet.LibsignalSimC.guardC mDF) := by
  unfold CryptoGames.Ratchet.LibsignalSimC.guardC
  refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC => ?_
  exact df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr none) hm

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_simSendC {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    df_noProbe_rel fig qepF sameHdr
      (CryptoGames.Ratchet.LibsignalSimC.simSendC P qep fig (probeHook fig qepF) Q m₀ chal r)
      (CryptoGames.Ratchet.LibsignalSimC.simSendC P qep fig (deliverForgeHook Pt ℓ) Q m₀ chal r) := by
  unfold CryptoGames.Ratchet.LibsignalSimC.simSendC
  refine df_noProbe_rel_bind (df_noProbe_rel_zoomB (PQ := PQ) fig qepF sameHdr _) fun res => ?_
  cases res with
  | none => exact df_noProbe_rel_pure fig qepF sameHdr none
  | some w =>
    refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC => ?_
    exact df_noProbe_rel_bind (df_noProbe_rel_set fig qepF sameHdr _) fun _ =>
      df_noProbe_rel_pure fig qepF sameHdr (some w)

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_fwdAnswerC {PQ : Type} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    df_noProbe_rel fig qepF sameHdr
      (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c')
      (fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine df_noProbe_rel_bind (df_noProbe_rel_zoomB (PQ := PQ) fig qepF sameHdr _) fun res => ?_
  cases res with
  | none => exact df_noProbe_rel_zoomB (PQ := PQ) fig qepF sameHdr _
  | some r =>
    cases r with
    | accepted _ _ _ =>
      exact df_noProbe_rel_bind (df_noProbe_rel_modify fig qepF sameHdr _) fun _ =>
        df_noProbe_rel_zoomB (PQ := PQ) fig qepF sameHdr _
    | _ => exact df_noProbe_rel_zoomB (PQ := PQ) fig qepF sameHdr _

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_simCorrC {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    df_noProbe_rel fig qepF sameHdr
      (CryptoGames.Ratchet.LibsignalSimC.simCorrC P encT (probeHook fig qepF) Dh Q)
      (CryptoGames.Ratchet.LibsignalSimC.simCorrC P encT (deliverForgeHook Pt ℓ) Dh Q) := by
  unfold CryptoGames.Ratchet.LibsignalSimC.simCorrC
  refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC => ?_
  refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
  refine df_noProbe_rel_bind (df_noProbe_rel_liftC fig qepF sameHdr _) fun res => ?_
  cases res with
  | none => exact df_noProbe_rel_pure fig qepF sameHdr _
  | some st =>
    exact df_noProbe_rel_bind (df_noProbe_rel_set fig qepF sameHdr _) fun _ =>
      df_noProbe_rel_pure fig qepF sameHdr _

omit [SampleableType Pt] in
theorem df_noProbe_rel_simRecvC_inject {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (w : List (BitVec 8)) :
    df_noProbe_rel fig qepF sameHdr
      (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w false)
      (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs (deliverForgeHook Pt ℓ) Q w false) := by
  unfold CryptoGames.Ratchet.LibsignalSimC.simRecvC
  generalize (2 ^ 32 : ℕ) = maxI
  generalize (25000 : ℕ) = maxSkip
  refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC => ?_
  dsimp only
  refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
  refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
  refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
  refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact df_noProbe_rel_pure fig qepF sameHdr _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
    refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
    cases P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact df_noProbe_rel_pure fig qepF sameHdr _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
        unfold CryptoGames.Ratchet.LibsignalSimC.fwdC
        refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC' => ?_
        cases (List.find? (fun wc => (wc.1 == w) && (CryptoGames.Party.senderOf wc.2.1.1 == Q.other))
            sC.base.honest).map Prod.snd with
        | none =>
          exact df_noProbe_rel_fwdAnswerC qep fig fs qepF sameHdr Q w false (some ci)
            h.senderRatchetKey pq' _
        | some c =>
          simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact df_noProbe_rel_fwdAnswerC qep fig fs qepF sameHdr Q w false (some ci)
            h.senderRatchetKey pq' _
      | none =>
        dsimp only
        refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
        refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
        refine df_noProbe_rel_ite
          (df_noProbe_rel_bind (df_noProbe_rel_modify fig qepF sameHdr _) fun _ => ?_) ?_ <;>
        · refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
          cases decT h.senderRatchetKey with
          | none => exact df_noProbe_rel_pure fig qepF sameHdr _
          | some T =>
            refine df_noProbe_rel_ite ?_ ?_
            · unfold fwdEvictC
              refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC' => ?_
              simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              exact df_noProbe_rel_fwdAnswerC qep fig fs qepF sameHdr Q w false none
                h.senderRatchetKey pq' _
            · unfold CryptoGames.Ratchet.LibsignalSimC.fwdC
              refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC' => ?_
              cases (List.find? (fun wc => (wc.1 == w) && (CryptoGames.Party.senderOf wc.2.1.1 == Q.other))
                  sC.base.honest).map Prod.snd with
              | none =>
                exact df_noProbe_rel_fwdAnswerC qep fig fs qepF sameHdr Q w false none
                  h.senderRatchetKey pq' _
              | some c =>
                simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                exact df_noProbe_rel_fwdAnswerC qep fig fs qepF sameHdr Q w false none
                  h.senderRatchetKey pq' _

@[expose] def df_noProbe_rel_at {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α)
    (mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α) :
    Prop :=
  ∀ (sent : List (Fig8C Pt))
    (s : CryptoGames.SM.Construction.DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
    s.forgeWin = false →
    ((simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
        ((mDF.run sC).run sent)).run s >>=
      fun z => pure (z.1.1, (z.2.base, false))) =
      ((mPr.run sC).run (s.base, false)) ∧
    ∀ z ∈ support
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr CryptoGames.SM.Config.h1)
        ((mDF.run sC).run sent)).run s),
      z.2.forgeWin = false ∧
      (∀ c ∈ sent, c ∈ z.1.2) ∧
      ((∀ r ∈ s.base.trans, r.ct ∈ sent) → ∀ r ∈ z.2.base.trans, r.ct ∈ z.1.2)

end DeliverForgeStepLemmas

section KemFailSimCoupling


omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fig8ImplH1_liftM_probComp {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (m : ProbComp α)
    (s : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fig8ImplH1 fig qepF) (liftM m : Fig8Comp Pt ℓ α)).run s =
      (m >>= fun a => pure (a, s)) := by
  induction m using OracleComp.inductionOn with
  | pure a =>
    simp
  | query_bind n r ih =>
    change (simulateQ (fig8ImplH1 fig qepF)
      ((liftM (OracleSpec.query (spec := unifSpec) n) : Fig8Comp Pt ℓ _) >>=
        fun u => (liftM (r u) : Fig8Comp Pt ℓ α))).run s = _
    rw [simulateQ_bind, StateT.run_bind]
    change (((liftM (OracleSpec.query (spec := unifSpec) n) :
        StateT (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp _).run s) >>=
      fun z => (simulateQ (fig8ImplH1 fig qepF) (liftM (r z.1) : Fig8Comp Pt ℓ α)).run z.2) = _
    simp only [StateT.run_monadLift, bind_assoc, pure_bind]
    refine congrArg (_ >>= ·) (funext fun u => ?_)
    exact ih u

omit [DecidableEq Pt] [SampleableType Pt] in
theorem runProbeStep_run {PQ PQC α : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (step : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) :
    (runProbeStep P ℓ Dh encPt encT decT idOf lam qep step).run (sC, gh, tr) =
      (((step.run sC).run gh) >>= fun z => pure (z.1.1, (z.1.2, z.2, tr))) :=
  rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem stateT_run_get_bind_prod3 {α β γ δ : Type}
    (f : α × β × γ → StateT (α × β × γ) ProbComp δ) (a : α) (b : β) (c : γ) :
    ((get >>= f).run (a, b, c)) = (f (a, b, c)).run (a, b, c) :=
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_pure_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (a : α)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift (pure a)).run gh = pure (a, gh) := by
  cases gh; rfl

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_bind_run {α β : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) (y : α → Fig8Comp Pt ℓ β)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift (x >>= y)).run gh =
      (((probeHook fig qepF).lift x).run gh >>=
        fun z => ((probeHook fig qepF).lift (y z.1)).run z.2) := by
  change ((simulateQ (fig8ImplH1 fig qepF) (x >>= y)).run gh.1 >>=
    fun z => pure (z.1, (z.2, gh.2))) =
    (((simulateQ (fig8ImplH1 fig qepF) x).run gh.1 >>= fun z => pure (z.1, (z.2, gh.2))) >>=
      fun z => (simulateQ (fig8ImplH1 fig qepF) (y z.1)).run z.2.1 >>=
        fun w => pure (w.1, (w.2, z.2.2)))
  rw [simulateQ_bind, StateT.run_bind, bind_assoc, bind_assoc]
  refine congrArg (_ >>= ·) (funext fun z => ?_)
  simp

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_liftM_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (m : ProbComp α)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift (liftM m : Fig8Comp Pt ℓ α)).run gh =
      (m >>= fun a => pure (a, gh)) := by
  change ((simulateQ (fig8ImplH1 fig qepF) (liftM m : Fig8Comp Pt ℓ α)).run gh.1 >>=
    fun z => pure (z.1, (z.2, gh.2))) = _
  rw [simulateQ_fig8ImplH1_liftM_probComp, bind_assoc]
  refine congrArg (m >>= ·) (funext fun a => ?_)
  cases gh; rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem zoomB_bind_run {PQ α β : Type}
    (H : Hook Pt ℓ (ProbeM Pt ℓ))
    (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    (((CryptoGames.Ratchet.LibsignalSimC.runOnBaseState H x >>= f).run sC).run gh) =
      (((H.lift (x.run sC.base)).run gh) >>=
        fun z => ((f z.1.1).run { sC with base := z.1.2 }).run z.2) := by
  rw [StateT.run_bind]
  change ((H.lift (x.run sC.base) >>= fun z => pure (z.1, { sC with base := z.2 })).run gh >>=
    fun p => ((f p.1.1).run p.1.2).run p.2) = _
  rw [StateT.run_bind, bind_assoc]
  refine congrArg (_ >>= ·) (funext fun z => ?_)
  simp

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem probComp_bind_congr {α β : Type} (m : ProbComp α) {f g : α → ProbComp β}
    (h : ∀ a, f a = g a) : (m >>= f) = (m >>= g) :=
  congrArg (m >>= ·) (funext h)

omit [SampleableType Pt] in
theorem kemFailSendStep_proj_eq_simSendC {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) :
    ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run (sC, gh, tr) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) =
    (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simSendC P qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
        Q m₀ chal r)).run sC).run gh) := by
  unfold kemFailSendStep
  rw [stateT_run_get_bind_prod3]
  split
  rcases Prod.mk.injEq _ _ _ _ |>.mp ‹(sC, gh, tr) = _› with ⟨rfl, hgh_tr⟩
  rcases Prod.mk.injEq _ _ _ _ |>.mp hgh_tr with ⟨rfl, rfl⟩
  unfold CryptoGames.Ratchet.LibsignalSimC.guardC CryptoGames.Ratchet.LibsignalSimC.simSendC
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  cases hstop : sC.base.stopped
  · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rw [zoomB_bind_run]
    unfold CryptoGames.Ratchet.LibsignalSim.simSend
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    cases hwin : (sC.base.mir.win || !noBobSendInEpoch0 sC.base.mir Q)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
      | none =>
        simp only [StateT.run_pure, probeHook_lift_pure_run, pure_bind]
      | some s₁ =>
        cases hchal : (chal.isSome && !s₁.safeCh 3 Q)
        · simp only [hchal, Bool.false_eq_true, ↓reduceIte]
          cases r with
          | none =>
            rw [StateT.run_bind, StateT.run_monadLift,
              StateT.run_bind, probeHook_lift_bind_run]
            unfold CryptoGames.Ratchet.LibsignalSim.coin CryptoGames.Ratchet.LibsignalSim.liftQ
            rw [StateT.run_lift, probeHook_lift_bind_run, probeHook_lift_liftM_run]
            simp only [MonadLiftT.monadLift, probeHook_lift_pure_run, bind_assoc, pure_bind]
            generalize ($ᵗ BitVec 512 : ProbComp (BitVec 512)) = m512
            apply probComp_bind_congr
            intro rq
            generalize mkPub P sC.base Q rq _ = mkRes
            rcases mkRes with _ | ⟨pq', pub⟩
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
                probeHook_lift_pure_run, pure_bind]
            · cases chal <;>
              · rw [StateT.run_bind, StateT.run_monadLift,
                  StateT.run_bind, StateT.run_lift,
                  probeHook_lift_bind_run, probeHook_lift_bind_run]
                simp only [MonadLiftT.monadLift,
                  probeHook_lift_pure_run, bind_assoc, pure_bind]
                apply probComp_bind_congr
                intro ⟨res, gh'⟩
                cases res
                · simp [probeHook_lift_pure_run, StateT.run_set]
                · simp only [probeHook_lift_pure_run, CryptoGames.Ratchet.LibsignalSim.putS, StateT.run_bind,
                    StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
                  cases (sC.kept Q).full <;> rfl
          | some rq =>
            rw [StateT.run_bind, StateT.run_pure, pure_bind,
              StateT.run_bind, StateT.run_map, StateT.run_monadLift,
              StateT.run_bind, StateT.run_pure, pure_bind,
              StateT.run_bind, StateT.run_map]
            unfold CryptoGames.Ratchet.LibsignalSim.coin CryptoGames.Ratchet.LibsignalSim.liftQ
            rw [StateT.run_lift, probeHook_lift_bind_run]
            simp only [MonadLiftT.monadLift, map_eq_bind_pure_comp,
              Function.comp_apply, bind_assoc, pure_bind]
            rw [probeHook_lift_bind_run, probeHook_lift_liftM_run, bind_assoc]
            simp only [probeHook_lift_pure_run, bind_assoc, pure_bind]
            generalize ($ᵗ BitVec 256 : ProbComp (BitVec 256)) = m256
            apply probComp_bind_congr
            intro rc
            generalize mkPub P sC.base Q rq _ = mkRes
            rcases mkRes with _ | ⟨pq', pub⟩
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
                probeHook_lift_pure_run, pure_bind]
            · cases chal <;>
              · rw [StateT.run_bind, StateT.run_monadLift,
                  StateT.run_bind, StateT.run_lift,
                  probeHook_lift_bind_run, probeHook_lift_bind_run]
                simp only [MonadLiftT.monadLift,
                  probeHook_lift_pure_run, bind_assoc, pure_bind]
                apply probComp_bind_congr
                intro ⟨res, gh'⟩
                cases res
                · simp [probeHook_lift_pure_run, StateT.run_set]
                · simp only [probeHook_lift_pure_run, CryptoGames.Ratchet.LibsignalSim.putS, StateT.run_bind,
                    StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
                  cases (sC.kept Q).full <;> rfl
        · simp only [hchal, ↓reduceIte, StateT.run_pure, probeHook_lift_pure_run, pure_bind]
    · simp only [↓reduceIte, StateT.run_pure, probeHook_lift_pure_run, pure_bind]
  · simp only [Bool.true_or, ↓reduceIte, StateT.run_pure, pure_bind]

omit [SampleableType Pt] in
theorem kemFailSimImpl_proj_eq_simImplC {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) :
    ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run (sC, gh, tr) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) =
    (((CryptoGames.Ratchet.LibsignalSimC.simImplC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
        Dh q_sm).run sC).run gh) := by
  rcases q_sm with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · change (((StateT.lift (OracleSpec.query (spec := unifSpec) n : ProbComp _) :
        KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr)) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) =
      (((StateT.lift ((probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)).lift
        (liftM (OracleSpec.query (spec := unifSpec) n : ProbComp _))) :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) _).run sC).run gh)
    rw [StateT.run_lift, bind_assoc, StateT.run_lift, StateT.run_bind,
      probeHook_lift_liftM_run, bind_assoc]
    simp only [pure_bind, StateT.run_pure]
  · exact kemFailSendStep_proj_eq_simSendC P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r
      sC gh tr
  · exact kemFailSendStep_proj_eq_simSendC P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
      sC gh tr
  · change (((do
        let ⟨sC, _, _⟩ ← get
        let revHonest := sC.base.honest.reverse
        let j? := revHonest.findIdx? (fun wc => wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other)
        let res ← runProbeStep P ℓ Dh encPt encT decT idOf lam qep
          (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (lFS P.C P.codec ℓ encT idOf 25000)
            (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w true))
        match res, j? with
        | some (.accepted _ _ _), some j =>
          modify fun ⟨sC', gh', tr⟩ => (sC', gh', stepKemFailDeliver P.C.F K tr Q j)
        | _, _ => pure ()
        return res : KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr)) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) = _
    rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, runProbeStep_run,
      bind_assoc, bind_assoc]
    refine (probComp_bind_congr _ fun ⟨⟨res, sC'⟩, gh'⟩ => ?_).trans (bind_pure _)
    rw [pure_bind]
    rcases res with _ | r_acc
    · simp
    · cases r_acc with
      | rejected => simp
      | accepted t i pm =>
        cases List.findIdx? (fun wc => wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other)
            sC.base.honest.reverse <;>
          simp [StateT.run_modify]
  · change ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep _).run (sC, gh, tr) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) = _
    rw [runProbeStep_run, bind_assoc]
    simp only [pure_bind, Prod.mk.eta, bind_pure]
    rfl
  · change ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep _).run (sC, gh, tr) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) = _
    rw [runProbeStep_run, bind_assoc]
    simp only [pure_bind, Prod.mk.eta, bind_pure]
    rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evalDist_bind_le_add_bool_of_support {α : Type} (p : ProbComp α)
    (f g h : α → ProbComp Bool)
    (hle : ∀ a ∈ support p, 𝒟[f a] {true} ≤ 𝒟[g a] {true} + 𝒟[h a] {true}) :
    𝒟[p >>= f] {true} ≤ 𝒟[p >>= g] {true} + 𝒟[p >>= h] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact hle a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable,
        ← MeasureTheory.lintegral_add_left Measurable.of_discrete]
    refine MeasureTheory.lintegral_mono fun u => ih u fun a ha => hle a ?_
    rw [MonadAttach.mem_support_bind]
    exact ⟨u, by simp, ha⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_at_flag_eq_false {PQ α : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ} {sameHdr : Fig8C Pt → Fig8C Pt → Bool}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α}
    (h : df_noProbe_rel_at fig qepF sameHdr sC mPr mDF)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (w : (α × LibsignalToModularSchemeSimState PQ Pt ℓ) ×
      (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool))
    (hw : w ∈ support ((mPr.run sC).run (g, false))) :
    w.2.2 = false := by
  have heq := (h [] { base := g } rfl).1
  rw [← heq, MonadAttach.mem_support_bind] at hw
  rcases hw with ⟨z, _, hw⟩
  simp only [support_pure, Set.mem_singleton_iff] at hw
  subst hw
  rfl

omit [SampleableType Pt] in
theorem mem_support_simImplC_of_mem_support_kemFailSimImpl {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run
      (sC, gh, tr))) :
    ((z.1, z.2.1), z.2.2.1) ∈ support
      (((CryptoGames.Ratchet.LibsignalSimC.simImplC P encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000)
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
          Dh q_sm).run sC).run gh) := by
  rw [← kemFailSimImpl_proj_eq_simImplC P K ℓ Dh encPt encT decT idOf lam qep q_sm sC gh tr,
      MonadAttach.mem_support_bind]
  exact ⟨z, hz, by simp⟩

omit [SampleableType Pt] in
theorem kemFailSimImpl_inl_state_eq {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (n : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inl n) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep (.inl n)).run
      (sC, gh, tr))) :
    z.2 = (sC, gh, tr) := by
  change z ∈ support ((StateT.lift (OracleSpec.query (spec := unifSpec) n) :
      KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr)) at hz
  simp only [StateT.run_lift, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hz
  rcases hz with ⟨_, _, rfl⟩
  rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem simulateQ_fig8ToDFImpl_liftM_probComp {α : Type}
    (ℓ : ℕ) (m : ProbComp α) (sent : List (Fig8C Pt)) :
    (simulateQ (fig8ToDFImpl Pt ℓ) (liftM m : Fig8Comp Pt ℓ α)).run sent =
      ((liftM m : CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
          (Fig8C Pt) α) >>= fun a => pure (a, sent)) := by
  induction m using OracleComp.inductionOn with
  | pure a =>
    simp
  | query_bind n r ih =>
    change (simulateQ (fig8ToDFImpl Pt ℓ)
      ((liftM (OracleSpec.query (spec := unifSpec) n) : Fig8Comp Pt ℓ _) >>=
        fun u => (liftM (r u) : Fig8Comp Pt ℓ α))).run sent =
      (((liftM (OracleSpec.query (spec := unifSpec) n) :
          CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) _) >>=
        fun u => (liftM (r u) :
          CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
            (Fig8C Pt) α)) >>=
        fun a => pure (a, sent))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    change ((fig8ToDFImpl Pt ℓ (.inl n)).run sent >>=
      fun z => (simulateQ (fig8ToDFImpl Pt ℓ) (liftM (r z.1) : Fig8Comp Pt ℓ α)).run z.2) = _
    rw [fig8ToDFImpl_inl_run, bind_assoc]
    refine congrArg (_ >>= ·) (funext fun u => ?_)
    rw [pure_bind]
    exact ih u

omit [Zero Pt] [SampleableType Pt] in
theorem deliverForgeHook_lift_liftM_run {α : Type}
    (ℓ : ℕ) (m : ProbComp α) (sent : List (Fig8C Pt)) :
    ((deliverForgeHook Pt ℓ).lift (liftM m : Fig8Comp Pt ℓ α)).run sent =
      ((liftM m : CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
          (Fig8C Pt) α) >>= fun a => pure (a, sent)) :=
  simulateQ_fig8ToDFImpl_liftM_probComp ℓ m sent

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evalDist_bind_true_le_add_of_badCoin {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] {d₁ d₂ : ℝ≥0∞} (oa : ProbComp α) (bad : α → Bool)
    (hbad : 𝒟[oa] {a | bad a = true} ≤ d₁) (f : α → ProbComp Bool)
    (h : ∀ a, bad a = false → 𝒟[f a] {true} ≤ d₂) :
    𝒟[oa >>= f] {true} ≤ d₁ + d₂ := by
  have hc := (closeByRefines_bind_of_bad (d₂ := d₂) 0 oa bad hbad
    (fR := f) (fS := fun _ => pure false) (fWin := fun _ _ => pure false)
    (fEps0 := fun _ => pure false) fun a ha => by
      unfold CloseByRefines
      simp [h a ha]).1
  simpa [OracleComp.evalDist_bind_const] using hc

/-- Remaining union-bound slack across `w_rem` epoch-coin draws and at most `q` candidates per draw. -/
@[expose] noncomputable def spurSlack {PQ PQC : Type} (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (q w_rem : ℕ) : ℝ≥0∞ :=
  ((q * w_rem : ℕ) : ℝ≥0∞) * spurUnit P.C.F encPt Dh

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spurSlack_step_le {PQ PQC : Type} (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (q : ℕ) {L_len w_rem : ℕ} (hL : L_len ≤ q) :
    (L_len : ℝ≥0∞) * spurUnit P.C.F encPt Dh + spurSlack P encPt Dh q w_rem ≤
      spurSlack P encPt Dh q (w_rem + 1) := by
  have h1 : (L_len : ℝ≥0∞) * spurUnit P.C.F encPt Dh ≤
      (q : ℝ≥0∞) * spurUnit P.C.F encPt Dh := by gcongr
  calc (L_len : ℝ≥0∞) * spurUnit P.C.F encPt Dh + spurSlack P encPt Dh q w_rem
      ≤ (q : ℝ≥0∞) * spurUnit P.C.F encPt Dh + spurSlack P encPt Dh q w_rem := by gcongr
    _ = spurSlack P encPt Dh q (w_rem + 1) := by
      unfold spurSlack
      push_cast
      ring

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spurSlack_le_spuriousStepTerm {PQ PQC : Type} (P : Params PQ PQC)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q qep : ℕ)
    {w_rem : ℕ} (hw : w_rem ≤ qep) :
    spurSlack P encPt Dh q w_rem ≤ spuriousStepTerm P.C.F encPt Dh q qep := by
  unfold spurSlack CryptoGames.Ratchet.LibsignalSim.spuriousStepTerm CryptoGames.Ratchet.LibsignalSim.rootKdfSpuriousStepUnit spurUnit
  gcongr

/-- Number of sending epochs of `Q` in `[1, t]`. -/
@[expose] def sentEpochsUpTo : Party → ℕ → ℕ
  | .A, t => (t + 1) / 2
  | .B, t => t / 2

/-- Remaining sending-epoch budget for the evicted-wire union bound. -/
@[expose] def remSendEpochs {St Msg C : Type} (qep : ℕ) (mir : CryptoGames.SM.GameState St Msg C) : ℕ :=
  qep - (sentEpochsUpTo .A (mir.epoch .A) + sentEpochsUpTo .B (mir.epoch .B))

theorem sentEpochsUpTo_mono (Q : Party) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) :
    sentEpochsUpTo Q t₁ ≤ sentEpochsUpTo Q t₂ := by
  cases Q <;> simp only [sentEpochsUpTo] <;> omega

theorem remSendEpochs_anti_epoch (qep : ℕ) {St Msg C : Type}
    (mir mir' : CryptoGames.SM.GameState St Msg C)
    (hep : ∀ R, mir.epoch R ≤ mir'.epoch R) :
    remSendEpochs qep mir' ≤ remSendEpochs qep mir := by
  have hA := sentEpochsUpTo_mono .A (hep .A)
  have hB := sentEpochsUpTo_mono .B (hep .B)
  unfold remSendEpochs
  omega

theorem sentEpochsUpTo_succ_of_sendsIn (Q : Party) (t : ℕ)
    (hs : Q.sendsIn (t + 1) = true) :
    sentEpochsUpTo Q (t + 1) = sentEpochsUpTo Q t + 1 := by
  cases Q <;> simp only [CryptoGames.Party.sendsIn, beq_iff_eq, sentEpochsUpTo] at hs ⊢ <;> omega

theorem sentEpochsUpTo_add_le {qep tA tB : ℕ} (hA : tA ≤ qep) (hB : tB ≤ qep) :
    sentEpochsUpTo .A tA + sentEpochsUpTo .B tB ≤ qep := by
  simp only [sentEpochsUpTo]
  omega

theorem remSendEpochs_new_send_epoch (qep : ℕ) {St Msg C : Type}
    (mir mir' : CryptoGames.SM.GameState St Msg C) (Q : Party)
    (hs : Q.sendsIn (mir.epoch Q + 1) = true)
    (hQ_le : mir.epoch Q + 1 ≤ qep)
    (hother_le : mir.epoch Q.other ≤ qep)
    (hep' : mir'.epoch = Function.update mir.epoch Q (mir.epoch Q + 1)) :
    0 < remSendEpochs qep mir ∧
      remSendEpochs qep mir' = remSendEpochs qep mir - 1 := by
  have hsucc := sentEpochsUpTo_succ_of_sendsIn Q (mir.epoch Q) hs
  unfold remSendEpochs
  rw [hep']
  cases Q with
  | A =>
    rw [Function.update_self, Function.update_of_ne (by decide : CryptoGames.Party.B ≠ CryptoGames.Party.A), hsucc]
    have hsum : sentEpochsUpTo .A (mir.epoch .A) + 1 + sentEpochsUpTo .B (mir.epoch .B) ≤ qep := by
      rw [← hsucc]
      exact sentEpochsUpTo_add_le hQ_le hother_le
    omega
  | B =>
    rw [Function.update_self, Function.update_of_ne (by decide : CryptoGames.Party.A ≠ CryptoGames.Party.B), hsucc]
    have hsum :
        sentEpochsUpTo .A (mir.epoch .A) + (sentEpochsUpTo .B (mir.epoch .B) + 1) ≤ qep := by
      rw [← hsucc]
      exact sentEpochsUpTo_add_le hother_le hQ_le
    omega

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurInit_spurBadList_eq_false
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8))
    (sa sb : List (BitVec 8)) (epExp : ℕ → BitVec 256)
    (Q : Party) (w_acc : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F)
    (rk_base : CryptoGames.Ratchet.RootKey) (T_base : Pt) :
    spurBadList P encPt Dh Q rk_base T_base
      (CryptoGames.LibsignalSM.Proofs.Refinement.evictedSpurCandList P epExp w_acc
        (CryptoGames.LibsignalSM.Proofs.Refinement.honestBeforeEpoch (initSimC (Pt := Pt) (ℓ := ℓ) sa sb).base.honest
          (CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch (initSimC (Pt := Pt) (ℓ := ℓ) sa sb).base.mir Q)))
      (epExp ((initSimC (Pt := Pt) (ℓ := ℓ) sa sb).base.mir.epoch Q)) = false := by
  simp [initSimC, initSim, CryptoGames.LibsignalSM.Proofs.Refinement.honestBeforeEpoch,
    CryptoGames.LibsignalSM.Proofs.Refinement.evictedSpurCandList, spurBadList]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurInit_remSendEpochs
    (qep : ℕ) (sa sb : List (BitVec 8)) :
    remSendEpochs qep (initSimC (Pt := Pt) (ℓ := ℓ) sa sb).base.mir = qep := by
  simp [remSendEpochs, sentEpochsUpTo, initSimC, initSim]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAcceptPure_inject_not_accepted_invariants
    (qep : ℕ) (P_party : Party) (w : List (BitVec 8))
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (s : SimState (List (BitVec 8)) Pt ℓ)
    (hnot : ∀ t' i' pm',
      (onAcceptPure qep P_party w false t i m ci? T pq' s).1 ≠ some (.accepted t' i' pm')) :
    let s' := (onAcceptPure qep P_party w false t i m ci? T pq' s).2
    s'.honest = s.honest ∧ s'.pq = s.pq ∧ s'.chains = s.chains ∧ s'.mir.epoch = s.mir.epoch := by
  unfold onAcceptPure at hnot ⊢
  dsimp only at hnot ⊢
  simp only [Bool.false_eq_true, ↓reduceIte] at hnot ⊢
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · rename_i hle
    simp only [hle, ↓reduceIte] at hnot
    split
    · rename_i htriv
      simp only [htriv, ↓reduceIte] at hnot
      exact False.elim (hnot t i (some m) rfl)
    · exact ⟨rfl, rfl, rfl, rfl⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAnswerPure_inject_not_accepted_invariants
    (qep : ℕ) (P_party : Party) (w : List (BitVec 8))
    (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (res : Option (CryptoGames.SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState (List (BitVec 8)) Pt ℓ)
    (hnot : ∀ t' i' pm',
      (onAnswerPure qep P_party w false ci? T pq' res s).1 ≠ some (.accepted t' i' pm')) :
    let s' := (onAnswerPure qep P_party w false ci? T pq' res s).2
    s'.honest = s.honest ∧ s'.pq = s.pq ∧ s'.chains = s.chains ∧ s'.mir.epoch = s.mir.epoch := by
  unfold onAnswerPure at hnot ⊢
  cases res with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some r =>
    cases r with
    | rejected => exact ⟨rfl, rfl, rfl, rfl⟩
    | accepted t i pm =>
      exact onAcceptPure_inject_not_accepted_invariants qep P_party w t i
        ((pm.map (·.2)).getD default) ci? T pq' s hnot

omit [SampleableType Pt] in
theorem fwdCPure_inject_not_accepted_invariants
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (P_party : Party) (w : List (BitVec 8)) (ci? : Option ℕ)
    (T : PublicKey) (pq' : List (BitVec 8)) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hnot : ∀ t' i' pm',
      (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a P_party w false ci? T pq' honestC c' x).1 ≠
        some (.accepted t' i' pm')) :
    let s' := (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a P_party w false ci? T pq'
      honestC c' x).2.1.base
    s'.honest = x.1.base.honest ∧ s'.pq = x.1.base.pq ∧
      s'.chains = x.1.base.chains ∧ s'.mir.epoch = x.1.base.mir.epoch := by
  have hc3a : fwdCPure P ℓ Dh encPt encT idOf lam qep c3a P_party w false ci? T pq' honestC c' x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false P_party w false ci? T pq' none c' x := by
    unfold fwdCPure
    cases honestC <;> simp [Bool.false_and, Bool.and_false]
  rw [hc3a] at hnot ⊢
  unfold fwdCPure at hnot ⊢
  dsimp only at hnot ⊢
  exact onAnswerPure_inject_not_accepted_invariants qep P_party w ci? T pq' _ x.1.base hnot

theorem kemFailSimImpl_deliver_run
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) :
    let r := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)
    let j? := sC.base.honest.reverse.findIdx?
      (fun wc => wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other)
    let tr' := match r.1, j? with
      | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
      | _, _ => tr
    (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inl (.inr (Q, w)))))).run
      (sC, gh, tr) = pure (r.1, (r.2.1, r.2.2, tr')) := by
  dsimp only
  change (do
    let ⟨sC, _, _⟩ ← get
    let revHonest := sC.base.honest.reverse
    let j? := revHonest.findIdx? (fun wc => wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other)
    let res ← runProbeStep P ℓ Dh encPt encT decT idOf lam qep
      (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w true))
    match res, j? with
    | some (.accepted _ _ _), some j =>
      modify fun ⟨sC', gh', tr⟩ => (sC', gh', stepKemFailDeliver P.C.F K tr Q j)
    | _, _ => pure ()
    return res : KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr) = _
  rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, runProbeStep_run,
    simRecvC_probe_run P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)]
  simp only [pure_bind]
  rcases (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)).1 with _ | r_acc
  · rfl
  · cases r_acc with
    | rejected => rfl
    | accepted t i pm =>
      cases sC.base.honest.reverse.findIdx?
          (fun wc => wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other) <;>
        simp [StateT.run_modify]


/-- Refinement invariant combining `SimInvCX` with `spurBadList = false` outside receive-only epochs. -/
@[expose] def EvictedSpurSimInv
    (P : Params (List (BitVec 8)) (BitVec 512))
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  ∃ x₀ s_R ec winBefore epExp,
    CryptoGames.LibsignalSM.Proofs.Refinement.SimInvCX P InvPQ ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { g with win := false } ec winBefore epExp ∧
    ∀ Q w_acc rk_base T_base,
      inReceiveOnlyEpoch sC.base.mir Q = false →
      spurBadList P encPt Dh Q rk_base T_base
        (CryptoGames.LibsignalSM.Proofs.Refinement.evictedSpurCandList P epExp w_acc
          (CryptoGames.LibsignalSM.Proofs.Refinement.honestBeforeEpoch sC.base.honest
            (CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch sC.base.mir Q)))
        (epExp (sC.base.mir.epoch Q)) = false

omit [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurSimInv_init_of_simInvCX
    (P : Params (List (BitVec 8)) (BitVec 512))
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (sa sb : List (BitVec 8))
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {x₀ : BitVec 256}
    {s_R : CryptoGames.SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8))}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hsim : CryptoGames.LibsignalSM.Proofs.Refinement.SimInvCX P InvPQ ℓ Dh encPt encT idOf lam qep q r
      x₀ s_R (initSimC sa sb) { g with win := false } ec winBefore epExp) :
    EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q r (initSimC sa sb) g :=
  ⟨x₀, s_R, ec, winBefore, epExp, hsim,
    fun Q w_acc rk_base T_base _ =>
      evictedSpurInit_spurBadList_eq_false P Dh encPt sa sb epExp Q w_acc rk_base T_base⟩

theorem evictedSpurSimInv_init
    (P : Params (List (BitVec 8)) (BitVec 512))
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hS : CryptoGames.LibsignalSM.Proofs.Refinement.SpqrCLocal P.spqr q InvPQ)
    (b : Bool) (k : BitVec 256 × BitVec 256) (pqrKey : BitVec 256)
    (hcoll0 : ∃ eA₀ : BitVec 256, Dh.dh eA₀ Dh.base ≠ Dh.dh k.2 Dh.base) :
    EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q q
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (CryptoGames.SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b) := by
  rcases k with ⟨k_root, x₀⟩
  rcases hcoll0 with ⟨eA₀, hne⟩
  exact evictedSpurSimInv_init_of_simInvCX P InvPQ ℓ Dh encPt encT idOf lam qep q q
    (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    (CryptoGames.SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (k_root, x₀) b)
    (CryptoGames.LibsignalSM.Proofs.Refinement.simInvCX_init P InvPQ ℓ Dh encPt encT idOf lam qep q hX b k_root x₀ eA₀
      pqrKey hne hS)

theorem fwdPure_accepted_epoch_eq
    {PQ PQC : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (s : SimState PQ Pt ℓ) (Q : Party) (c' : Fig8C Pt)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {t' i' : ℕ} {pm : Option (LibsignalMsgPublicPart × Plain ℓ)}
    (hacc : (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
      CryptoGames.SM.Config.h1 s Q c' g).1 = some (.accepted t' i' pm)) :
    t' = c'.1.1 := by
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  unfold fwdPure at hacc
  split at hacc
  · unfold CryptoGames.LibsignalSM.Proofs.Refinement.deliverPure at hacc
    split at hacc
    · cases hacc
    · cases htr : g.inTransit Q.other c' with
      | none => rw [htr] at hacc; cases hacc
      | some r =>
        rw [htr] at hacc
        dsimp only at hacc
        cases hrcv : sm.receive (g.st Q) c' with
        | none => rw [hrcv] at hacc; cases hacc
        | some v =>
          rcases v with ⟨st', t₁, i₁, m'⟩
          rw [hrcv] at hacc
          cases hacc
          exact (lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
            (g.st Q) c' hrcv).1
  · unfold CryptoGames.LibsignalSM.Proofs.Refinement.injectPure at hacc
    split at hacc
    · cases hacc
    · cases hrcv : sm.receive (g.st Q) c' with
      | none => rw [hrcv] at hacc; cases hacc
      | some v =>
        rcases v with ⟨st', t₁, i₁, m'⟩
        rw [hrcv] at hacc
        dsimp only at hacc
        split at hacc
        · cases hacc
        · split at hacc
          · cases hacc
            exact (lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
              (g.st Q) c' hrcv).1
          · cases hacc

theorem fwdCPure_inject_not_accepted_of_epoch_le
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ)
    (T : PublicKey) (pq' : List (BitVec 8)) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hsafe : x.1.base.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, CryptoGames.SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hep_le : x.1.base.mir.epoch Q ≤ c'.1.1) :
    ∀ t' i' pm',
      (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w false ci? T pq' honestC c' x).1 ≠
        some (.accepted t' i' pm') := by
  intro t' i' pm' hacc
  have hc3a : fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w false ci? T pq' honestC c' x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' none c' x := by
    unfold fwdCPure
    cases honestC <;> simp [Bool.false_and, Bool.and_false]
  rw [hc3a] at hacc
  unfold fwdCPure onAnswerPure at hacc
  dsimp only at hacc
  cases hz : (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
      CryptoGames.SM.Config.h1 x.1.base Q c' x.2.1).1 with
  | none => rw [hz] at hacc; cases hacc
  | some r_res =>
    rw [hz] at hacc
    cases r_res with
    | rejected => cases hacc
    | accepted t₁ i₁ pm₁ =>
      have ht₁ : t₁ = c'.1.1 :=
        fwdPure_accepted_epoch_eq P ℓ Dh encPt encT idOf lam qep x.1.base Q c' x.2.1 hz
      have htriv_f : x.1.base.mir.trivial 3 ⟨Q.other, t₁, i₁⟩ = false :=
        CryptoGames.LibsignalSM.Proofs.Refinement.trivial_false_of_newChain_inject hsafe hcomp Q ⟨Q.other, t₁, i₁⟩
          (by dsimp only; omega)
      unfold onAcceptPure at hacc
      dsimp only at hacc
      simp only [Bool.false_eq_true, ↓reduceIte, htriv_f] at hacc
      split at hacc <;> cases hacc

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAcceptPure_inject_some_invariants
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (t i : ℕ) (m : Plain ℓ) (ci : ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (s : SimState (List (BitVec 8)) Pt ℓ)
    (hsafe : s.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ s.mir.comp, CryptoGames.SM.healedBy s.mir.tL 3 p.epoch = false)
    (hhist : CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K s)
    (hreach : CryptoGames.LibsignalSM.Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (s.pq Q) pq') :
    let s' := (onAcceptPure qep Q w false t i m (some ci) T pq' s).2
    s'.honest = s.honest ∧ s'.mir.epoch = s.mir.epoch ∧
      CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K s' := by
  refine ⟨?_, ?_,
    CryptoGames.LibsignalSM.Proofs.Refinement.spqrHistoryInv_onAcceptPure_some P K qep Q w false t i m ci T pq' s
      hhist hreach⟩
  · unfold onAcceptPure
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · split <;> rfl
  · unfold onAcceptPure
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · split
      · rename_i htriv
        have ht_le : (⟨Q.other, t, i⟩ : CryptoGames.SM.Pos).epoch ≤ s.mir.epoch Q := by
          by_contra hnot_le
          have hge : s.mir.epoch Q ≤ (⟨Q.other, t, i⟩ : CryptoGames.SM.Pos).epoch := by
            dsimp only at hnot_le ⊢; omega
          have hf := CryptoGames.LibsignalSM.Proofs.Refinement.trivial_false_of_newChain_inject hsafe hcomp Q
            ⟨Q.other, t, i⟩ hge
          rw [htriv] at hf
          cases hf
        exact CryptoGames.LibsignalSM.Proofs.Refinement.WP2A.I3.accept_epoch_eq_of_le s.mir Q () ⟨Q.other, t, i⟩ ht_le
      · rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAnswerPure_inject_some_invariants
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (ci : ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (res : Option (CryptoGames.SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState (List (BitVec 8)) Pt ℓ)
    (hsafe : s.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ s.mir.comp, CryptoGames.SM.healedBy s.mir.tL 3 p.epoch = false)
    (hhist : CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K s)
    (hreach : CryptoGames.LibsignalSM.Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (s.pq Q) pq') :
    let s' := (onAnswerPure qep Q w false (some ci) T pq' res s).2
    s'.honest = s.honest ∧ s'.mir.epoch = s.mir.epoch ∧
      CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K s' := by
  unfold onAnswerPure
  cases res with
  | none => exact ⟨rfl, rfl, hhist⟩
  | some r =>
    cases r with
    | rejected => exact ⟨rfl, rfl, hhist⟩
    | accepted t i pm =>
      exact onAcceptPure_inject_some_invariants P K qep Q w t i
        ((pm.map (·.2)).getD default) ci T pq' s hsafe hcomp hhist hreach

omit [SampleableType Pt] in
theorem fwdCPure_inject_some_invariants
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8)) (ci : ℕ)
    (T : PublicKey) (pq' : List (BitVec 8)) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hsafe : x.1.base.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, CryptoGames.SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hhist : CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K x.1.base)
    (hreach : CryptoGames.LibsignalSM.Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (x.1.base.pq Q) pq') :
    let s' := (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w false (some ci) T pq'
      honestC c' x).2.1.base
    s'.honest = x.1.base.honest ∧ s'.mir.epoch = x.1.base.mir.epoch ∧
      CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K s' := by
  have hc3a : fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w false (some ci) T pq' honestC c' x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false (some ci) T pq' none c' x := by
    unfold fwdCPure
    cases honestC <;> simp [Bool.false_and, Bool.and_false]
  rw [hc3a]
  unfold fwdCPure
  dsimp only
  exact onAnswerPure_inject_some_invariants P K qep Q w ci T pq' _ x.1.base hsafe hcomp hhist
    hreach

theorem fwdCPure_inject_none_invariants
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8))
    (T : PublicKey) (pq' : List (BitVec 8)) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hsafe : x.1.base.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, CryptoGames.SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hep_le : x.1.base.mir.epoch Q ≤ c'.1.1)
    (hhist : CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K x.1.base) :
    let s' := (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w false none T pq'
      honestC c' x).2.1.base
    s'.honest = x.1.base.honest ∧ s'.mir.epoch = x.1.base.mir.epoch ∧
      CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K s' := by
  have hnot_acc := fwdCPure_inject_not_accepted_of_epoch_le P ℓ Dh encPt encT idOf lam qep c3a
    Q w none T pq' honestC c' x hsafe hcomp hep_le
  obtain ⟨h1, h2, h3, h4⟩ := fwdCPure_inject_not_accepted_invariants P ℓ Dh encPt encT idOf lam
    qep c3a Q w none T pq' honestC c' x hnot_acc
  exact ⟨h1, h4, CryptoGames.LibsignalSM.Proofs.Refinement.spqrHistoryInv_preserve_of_sub hhist h1
    (fun R => by rw [h2]; exact .refl _)
    (fun R t ht => by rwa [h3] at ht)⟩

theorem simRecvStepC_inject_preserves_spqrHistoryInv_and_epoch_of_simInvC
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC (List (BitVec 8)) Pt ℓ)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, CryptoGames.SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hhist : CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K x.1.base) :
    let s' := (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w false x).2.1.base
    s'.honest = x.1.base.honest ∧ s'.mir.epoch = x.1.base.mir.epoch ∧
      CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K s' := by
  rcases x with ⟨⟨s, kept, sent, snaps⟩, g, fl⟩
  unfold simRecvStepC simRecvStepCGen
  by_cases hst : s.stopped = true
  · simp [hst, hhist]
  simp only [hst, Bool.false_eq_true, ↓reduceIte]
  by_cases hwin : s.mir.win = true
  · simp [hwin, hhist]
  simp only [hwin, Bool.false_eq_true, ↓reduceIte]
  by_cases hdel : (false && (s.mir.inTransit Q.other w).isNone) = true
  · simp at hdel
  simp only [hdel, Bool.false_eq_true, ↓reduceIte]
  by_cases hinj : (!false && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w))) = true
  · simp at hinj; simp [hinj, hhist]
  have hsafe : s.mir.safeInj 3 = true := by
    revert hinj
    cases (s.mir.inTransit Q.other w).isSome <;> cases s.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  simp only [hinj, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : w.length < 9
  · simp [hlen, hhist]
  simp only [hlen, ↓reduceIte]
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact ⟨rfl, rfl, hhist⟩
  | some hb =>
    rcases hb with ⟨h, body⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · simp [haddr, hhist]
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    by_cases hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet = true
    · simp [hpan, hhist]
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    cases hspqr : P.spqr.recv (s.pq Q) h.pqRatchet with
    | error _ => exact ⟨rfl, rfl, hhist⟩
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      have hreach : CryptoGames.LibsignalSM.Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (s.pq Q) pq' :=
        .recv (.refl _) (hspqr_eq ▸ hspqr)
      cases hci : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        split
        · exact ⟨rfl, rfl, hhist⟩
        · exact fwdCPure_inject_some_invariants P K ℓ Dh encPt encT idOf lam qep true Q w ci
            h.senderRatchetKey pq' _ _ (⟨s, kept, sent, snaps⟩, g, fl) hsafe hcomp hhist hreach
      | none =>
        dsimp only
        let x₁ : JointC (List (BitVec 8)) Pt ℓ :=
          if inReceiveOnlyEpoch s.mir Q || (Q == CryptoGames.Party.A && (s.chains Q).any (·.key.isNone)) then
            ({ base := { s with amb := s.amb + 1, stopped := false },
                kept := kept, sent := sent, snaps := snaps }, g, fl)
          else (⟨s, kept, sent, snaps⟩, g, fl)
        have hx1 : x₁.1.base.honest = s.honest ∧ x₁.1.base.pq = s.pq ∧
            x₁.1.base.chains = s.chains ∧ x₁.1.base.mir = s.mir := by
          dsimp only [x₁]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
        have hhist1 : CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K x₁.1.base :=
          CryptoGames.LibsignalSM.Proofs.Refinement.spqrHistoryInv_preserve_of_sub hhist hx1.1
            (fun R => by rw [hx1.2.1]; exact .refl _)
            (fun R t ht => by rwa [hx1.2.2.1] at ht)
        split
        · exact ⟨rfl, rfl, hhist⟩
        · split
          · exact ⟨rfl, rfl, hhist⟩
          · split
            · exact ⟨hx1.1, congrArg (·.epoch) hx1.2.2.2, hhist1⟩
            · cases hT : decT h.senderRatchetKey with
              | none => exact ⟨hx1.1, congrArg (·.epoch) hx1.2.2.2, hhist1⟩
              | some T =>
                dsimp only
                let hc_opt : Option (Fig8C Pt) :=
                  (s.honest.find? fun (wc : List (BitVec 8) × Fig8C Pt) =>
                    wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2)
                let c_fb : Fig8C Pt :=
                  ((s.mir.epoch Q + 1, some T),
                    (h.counter.toNat + 1,
                      ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
                        effectiveHkdfSalt32 salt)))
                split
                · unfold fwdEvictCPure
                  simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                  obtain ⟨h1, h4, hhist2⟩ := fwdCPure_inject_none_invariants P K ℓ Dh encPt encT
                    idOf lam qep false Q w h.senderRatchetKey pq' none c_fb x₁
                    (hx1.2.2.2.symm ▸ hsafe) (hx1.2.2.2.symm ▸ hcomp)
                    (by rw [hx1.2.2.2]; dsimp only [c_fb]; omega) hhist1
                  exact ⟨h1.trans hx1.1, h4.trans (congrArg (·.epoch) hx1.2.2.2), hhist2⟩
                · rename_i hev_false
                  have hmk_ep : x₁.1.base.mir.epoch Q ≤
                      (match hc_opt with
                      | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else c_fb
                      | none => c_fb).1.1 := by
                    rw [hx1.2.2.2]
                    cases hfind : hc_opt with
                    | none => dsimp only [c_fb]; omega
                    | some c =>
                      change ¬(Option.map (fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) hc_opt ==
                          some true) = true at hev_false
                      rw [hfind] at hev_false
                      simp only [Option.map_some, beq_iff_eq, Option.some.injEq,
                        decide_eq_true_eq, not_ne_iff] at hev_false
                      dsimp only [c_fb]
                      split <;> [omega; (dsimp only; omega)]
                  obtain ⟨h1, h4, hhist2⟩ := fwdCPure_inject_none_invariants P K ℓ Dh encPt encT
                    idOf lam qep true Q w h.senderRatchetKey pq' _ _ x₁
                    (hx1.2.2.2.symm ▸ hsafe) (hx1.2.2.2.symm ▸ hcomp) hmk_ep hhist1
                  exact ⟨h1.trans hx1.1, h4.trans (congrArg (·.epoch) hx1.2.2.2), hhist2⟩

/-- Game-level SPQR history and remaining-epoch invariant for `kemFailSimImpl`. -/
structure EvictedSpurHistGameInv
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (qep w_rem : ℕ) (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) : Prop where
  hhist : CryptoGames.LibsignalSM.Proofs.Refinement.SpqrHistoryInv P K sC.base
  hw_rem : remSendEpochs qep sC.base.mir ≤ w_rem

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_init
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (pqrKey : BitVec 256) (qep : ℕ) :
    EvictedSpurHistGameInv (Pt := Pt) (ℓ := ℓ) P K qep qep
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) :=
  ⟨(CryptoGames.LibsignalSM.Proofs.Refinement.spqrHistoryInv_init P K
    (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)).2,
   (evictedSpurInit_remSendEpochs (Pt := Pt) (ℓ := ℓ) qep
    (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)).le⟩

omit [SampleableType Pt] in
theorem kemFailSimImpl_corr_flag_eq_false {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (z : Option (GhostState PQ) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q))).run (sC, (g, false), tr))) :
    z.2.2.1.2 = false :=
  df_noProbe_rel_at_flag_eq_false
    (df_noProbe_rel_guardC (df_noProbe_rel_simCorrC P encT
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)
      CryptoGames.SM.Construction.DeliverForge.sameHdrScheme Dh Q) sC)
    g ((z.1, z.2.1), z.2.2.1)
    (mem_support_simImplC_of_mem_support_kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q)) sC (g, false) tr z hz)

omit [SampleableType Pt] in
theorem kemFailSimImpl_inject_flag_eq_false {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (z : Option (CryptoGames.SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inr (Q, w))))).run (sC, (g, false), tr))) :
    z.2.2.1.2 = false :=
  df_noProbe_rel_at_flag_eq_false
    (df_noProbe_rel_guardC (df_noProbe_rel_simRecvC_inject P encT decT qep
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000) (qep + 1)
      CryptoGames.SM.Construction.DeliverForge.sameHdrScheme Q w) sC)
    g ((z.1, z.2.1), z.2.2.1)
    (mem_support_simImplC_of_mem_support_kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inr (Q, w)))) sC (g, false) tr z hz)

omit [SampleableType Pt] in
theorem kemFailSimImpl_send_flag_eq_false {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_send : Party × Plain ℓ × Option (BitVec 512) ⊕
      Party × Plain ℓ × Plain ℓ × Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inl (.inl q_send)))) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inl (.inl q_send))))).run (sC, (g, false), tr))) :
    z.2.2.1.2 = false := by
  rcases q_send with ⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩
  · exact df_noProbe_rel_at_flag_eq_false
      (df_noProbe_rel_guardC (df_noProbe_rel_simSendC P qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme Q m₀ none r) sC)
      g ((z.1, z.2.1), z.2.2.1)
      (mem_support_simImplC_of_mem_support_kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) sC (g, false) tr z hz)
  · exact df_noProbe_rel_at_flag_eq_false
      (df_noProbe_rel_guardC (df_noProbe_rel_simSendC P qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)
        CryptoGames.SM.Construction.DeliverForge.sameHdrScheme Q m₀ (some m₁) r) sC)
      g ((z.1, z.2.1), z.2.2.1)
      (mem_support_simImplC_of_mem_support_kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) sC (g, false) tr z hz)

omit [SampleableType Pt] in
theorem kemFailSimImpl_corr_preserves_evictedSpurHistGameInv
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep w_rem : ℕ)
    (Q : Party)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (z : Option (GhostState (List (BitVec 8))) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q))).run (sC, gh, tr))) :
    EvictedSpurHistGameInv P K qep w_rem z.2.1 := by
  change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simCorrC P encT
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q))).run
    (sC, gh, tr)) at hz
  rw [runProbeStep_run, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hw_step : (w.1.1, (w.1.2, w.2)) ∈ support
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) (sC, gh)) := by
    change (w.1.1, (w.1.2, w.2)) ∈ support
      ((((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simCorrC P encT
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q)).run
        sC).run gh) >>= fun r => pure (r.1.1, (r.1.2, r.2)))
    rw [MonadAttach.mem_support_bind]
    exact ⟨w, hw, by simp⟩
  obtain ⟨hhon_eq, hpq_eq, hep_eq, _, _⟩ :=
    stepSimCNone_corr_invariants P ℓ Dh encPt encT decT idOf lam qep Q (sC, gh)
      (w.1.1, (w.1.2, w.2)) hw_step
  have hchains_ep : ∀ R,
      (w.1.2.base.chains R).map (·.epoch) = (sC.base.chains R).map (·.epoch) := by
    intro R
    rw [stepSimCNone_corr_eq_steer] at hw_step
    simp only [support_pure, Set.mem_singleton_iff] at hw_step
    have hbase : w.1.2.base = (simCorrPureCSteer P Dh encT Q (sC, gh)).2.1.base :=
      congrArg (·.2.1.base) hw_step
    rw [hbase]
    unfold simCorrPureCSteer
    dsimp only
    split
    · rfl
    · split
      · rfl
      · cases (corrPure Q gh.1).1 with
        | none => rfl
        | some figSt =>
          dsimp only
          split
          · cases figSt.γ with
            | pub _ => rfl
            | exp x =>
              dsimp only
              cases R with
              | A =>
                rw [Function.update_self]
                exact c8_map_epoch_resolve_list (sC.base.chains .A) (encT (Dh.dh x Dh.base))
              | B =>
                rw [Function.update_of_ne (by decide : CryptoGames.Party.B ≠ CryptoGames.Party.A)]
          · rfl
  refine ⟨CryptoGames.LibsignalSM.Proofs.Refinement.spqrHistoryInv_preserve_of_sub hInv.hhist hhon_eq
    (fun R => by rw [hpq_eq]; exact .refl _)
    (fun R t ht => by rwa [hchains_ep R] at ht), ?_⟩
  have hrem : remSendEpochs qep w.1.2.base.mir = remSendEpochs qep sC.base.mir := by
    unfold remSendEpochs
    rw [hep_eq]
  exact hrem ▸ hInv.hw_rem

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_preserve_of_unchanged_pq_honest
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem} {qep w_rem : ℕ}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hhon : sC'.base.honest = sC.base.honest)
    (hpq : sC'.base.pq = sC.base.pq)
    (hchains : ∀ R t, t ∈ (sC'.base.chains R).map (·.epoch) →
      t ∈ (sC.base.chains R).map (·.epoch))
    (hep_le : ∀ R, sC.base.mir.epoch R ≤ sC'.base.mir.epoch R) :
    EvictedSpurHistGameInv P K qep w_rem sC' :=
  ⟨CryptoGames.LibsignalSM.Proofs.Refinement.spqrHistoryInv_preserve_of_sub hInv.hhist hhon
    (fun R => by rw [hpq]; exact .refl _) hchains,
   (remSendEpochs_anti_epoch qep sC.base.mir sC'.base.mir hep_le).trans hInv.hw_rem⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_send_same_epoch
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    {qep w_rem : ℕ}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {Q : Party} {pq' : List (BitVec 8)} {rq : BitVec 512} {salt : Salt}
    {seed : BitVec 256} {i t : ℕ} {T : Pt} {pub : LibsignalMsgPublicPart} {m : Plain ℓ}
    {w_top : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F}
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hsender : CryptoGames.Party.senderOf t = Q)
    (hspqr_send : P.spqr.send (sC.base.pq Q) rq = some (pq', salt, pub.pqmsg))
    (hpq' : sC'.base.pq = Function.update sC.base.pq Q pq')
    (hhon' : sC'.base.honest =
      (CryptoGames.Ratchet.LibsignalSim.toWire
        ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
          seed (i, (t, some T)) (pub, m))),
       ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
          seed (i, (t, some T)) (pub, m)))) :: sC.base.honest)
    (hchains : ∀ R t', t' ∈ (sC'.base.chains R).map (·.epoch) →
      t' ∈ (sC.base.chains R).map (·.epoch))
    (hw_top : CryptoVerification.SpqrV1Sync.SendTotal.TopStateW P.C.F K (sC.base.pq Q) w_top)
    (hpqmsg : ∀ h body,
      (signalWireCodec P.codec).parse
        ((CryptoGames.Ratchet.LibsignalSim.toWire
          ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
            seed (i, (t, some T)) (pub, m)))).take
          ((CryptoGames.Ratchet.LibsignalSim.toWire
            ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
              seed (i, (t, some T)) (pub, m)))).length - 8)) = some (h, body) →
      h.pqRatchet = pub.pqmsg)
    (hord_old : ∀ w₀ c₀, (w₀, c₀) ∈ sC.base.honest → CryptoGames.Party.senderOf c₀.1.1 = Q → c₀.1.1 ≤ t)
    (hep_le : ∀ R, sC.base.mir.epoch R ≤ sC'.base.mir.epoch R) :
    EvictedSpurHistGameInv P K qep w_rem sC' :=
  ⟨CryptoGames.LibsignalSM.Proofs.Refinement.spqrHistoryInv_preserve_send hInv.hhist hhon' hpq' hchains
    hsender hw_top (hspqr_eq ▸ hspqr_send) hpqmsg hord_old,
   (remSendEpochs_anti_epoch qep sC.base.mir sC'.base.mir hep_le).trans hInv.hw_rem⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_send_new_epoch
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    {qep w_rem : ℕ}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {Q : Party} {pq' : List (BitVec 8)} {rq : BitVec 512} {salt : Salt}
    {seed : BitVec 256} {i t : ℕ} {T : Pt} {pub : LibsignalMsgPublicPart} {m : Plain ℓ}
    {w_top : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F}
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hsender : CryptoGames.Party.senderOf t = Q)
    (hspqr_send : P.spqr.send (sC.base.pq Q) rq = some (pq', salt, pub.pqmsg))
    (hpq' : sC'.base.pq = Function.update sC.base.pq Q pq')
    (hhon' : sC'.base.honest =
      (CryptoGames.Ratchet.LibsignalSim.toWire
        ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
          seed (i, (t, some T)) (pub, m))),
       ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
          seed (i, (t, some T)) (pub, m)))) :: sC.base.honest)
    (hchains : ∀ R t', t' ∈ (sC'.base.chains R).map (·.epoch) →
      t' ∈ (sC.base.chains R).map (·.epoch))
    (hw_top : CryptoVerification.SpqrV1Sync.SendTotal.TopStateW P.C.F K (sC.base.pq Q) w_top)
    (hpqmsg : ∀ h body,
      (signalWireCodec P.codec).parse
        ((CryptoGames.Ratchet.LibsignalSim.toWire
          ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
            seed (i, (t, some T)) (pub, m)))).take
          ((CryptoGames.Ratchet.LibsignalSim.toWire
            ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
              seed (i, (t, some T)) (pub, m)))).length - 8)) = some (h, body) →
      h.pqRatchet = pub.pqmsg)
    (hord_old : ∀ w₀ c₀, (w₀, c₀) ∈ sC.base.honest → CryptoGames.Party.senderOf c₀.1.1 = Q → c₀.1.1 ≤ t)
    (hs : Q.sendsIn (sC.base.mir.epoch Q + 1) = true)
    (hQ_le : sC.base.mir.epoch Q + 1 ≤ qep)
    (hother_le : sC.base.mir.epoch Q.other ≤ qep)
    (hep' : sC'.base.mir.epoch = Function.update sC.base.mir.epoch Q (sC.base.mir.epoch Q + 1)) :
    0 < w_rem ∧ EvictedSpurHistGameInv P K qep (w_rem - 1) sC' := by
  obtain ⟨hpos, hrem_eq⟩ := remSendEpochs_new_send_epoch qep sC.base.mir sC'.base.mir Q
    hs hQ_le hother_le hep'
  have hw_pos : 0 < w_rem := lt_of_lt_of_le hpos hInv.hw_rem
  have hw_rem' : remSendEpochs qep sC'.base.mir ≤ w_rem - 1 := by
    have := hInv.hw_rem
    omega
  have hhist' := CryptoGames.LibsignalSM.Proofs.Refinement.spqrHistoryInv_preserve_send hInv.hhist hhon' hpq' hchains
    hsender hw_top (hspqr_eq ▸ hspqr_send) hpqmsg hord_old
  exact ⟨hw_pos, hhist', hw_rem'⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_deliver_existing_chain
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem} {ℓ : ℕ}
    {qep w_rem : ℕ}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {Q : Party} {w_wire : List (BitVec 8)} {t i : ℕ} {m : Plain ℓ}
    {ci : ℕ} {k_ratchet : PublicKey} {pq' : List (BitVec 8)}
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hreach : CryptoGames.LibsignalSM.Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (sC.base.pq Q) pq')
    (hbase : sC'.base = (onAcceptPure qep Q w_wire true t i m (some ci) k_ratchet pq' sC.base).2)
    (hep_le : ∀ R, sC.base.mir.epoch R ≤ sC'.base.mir.epoch R) :
    EvictedSpurHistGameInv P K qep w_rem sC' :=
  ⟨hbase ▸ CryptoGames.LibsignalSM.Proofs.Refinement.spqrHistoryInv_onAcceptPure_some P K qep Q w_wire true t i m ci
    k_ratchet pq' sC.base hInv.hhist hreach,
   (remSendEpochs_anti_epoch qep sC.base.mir sC'.base.mir hep_le).trans hInv.hw_rem⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_deliver_new_chain
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem} {ℓ : ℕ}
    {qep w_rem : ℕ}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {Q : Party} {w_wire w : List (BitVec 8)} {t i : ℕ} {m : Plain ℓ}
    {k_ratchet : PublicKey} {pq' : List (BitVec 8)}
    {c : Fig8C Pt} {h : SignalHeader} {body : List (BitVec 8)} {salt : Salt}
    {w_acc : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F}
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hc_mem : (w, c) ∈ sC.base.honest)
    (ht_eq : t = c.1.1)
    (hc_sender : CryptoGames.Party.senderOf c.1.1 = Q.other)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hw_acc : CryptoVerification.SpqrV1Sync.SendTotal.TopStateW P.C.F K (sC.base.pq Q) w_acc)
    (hrecv : (spqrV1SessionUniformCoins P.C.F K).recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hbase : sC'.base = (onAcceptPure qep Q w_wire true t i m none k_ratchet pq' sC.base).2)
    (hep_le : ∀ R, sC.base.mir.epoch R ≤ sC'.base.mir.epoch R) :
    EvictedSpurHistGameInv P K qep w_rem sC' :=
  ⟨hbase ▸ CryptoGames.LibsignalSM.Proofs.Refinement.spqrHistoryInv_onAcceptPure_none P K qep Q w_wire true t i m
    k_ratchet pq' sC.base w c h body salt w_acc hInv.hhist hc_mem ht_eq hc_sender hparse hw_acc
    hrecv,
   (remSendEpochs_anti_epoch qep sC.base.mir sC'.base.mir hep_le).trans hInv.hw_rem⟩

section CorrSimInvCX


omit [SampleableType Pt] in
@[expose] def clearWin {ℓ : ℕ}
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
  { g with win := false }

omit [SampleableType Pt] in
theorem fwdPure_of_win_true
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (s : SimState (List (BitVec 8)) Pt ℓ) (Q : Party) (c' : Fig8C Pt)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : g.win = true) :
    fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) CryptoGames.SM.Config.h1 s Q c' g =
      (none, g) := by
  unfold fwdPure deliverPure injectPure
  split <;> simp [hwin]

omit [SampleableType Pt] in
theorem fwdCPure_inject_of_fwdPure_not_accepted
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hno_acc : ∀ t i m,
      (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) CryptoGames.SM.Config.h1
        x.1.base Q c' x.2.1).1 ≠ some (.accepted t i m))
    (hg_eq :
      { (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) CryptoGames.SM.Config.h1
          x.1.base Q c' x.2.1).2 with win := false } =
        { x.2.1 with win := false }) :
    (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' honestC c' x).2.1 = x.1 ∧
    { (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' honestC c' x).2.2.1 with
      win := false } = { x.2.1 with win := false } := by
  have hplain :
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' honestC c' x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' none c' x := by
    unfold fwdCPure
    cases honestC <;> simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hplain]
  unfold fwdCPure
  dsimp only
  rcases hfwd :
      fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) CryptoGames.SM.Config.h1
        x.1.base Q c' x.2.1 with ⟨res8, g'⟩
  rw [hfwd] at hno_acc hg_eq
  cases res8 with
  | none =>
    unfold onAnswerPure
    exact ⟨rfl, hg_eq⟩
  | some r8 =>
    cases r8 with
    | accepted t i m => exact False.elim (hno_acc t i m rfl)
    | rejected =>
      unfold onAnswerPure
      exact ⟨rfl, hg_eq⟩

theorem fwdCPure_inject_of_epoch_lt
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hsafe : x.1.base.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, CryptoGames.SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hhon : ∀ wc ∈ x.1.base.honest, wc.1 = CryptoGames.Ratchet.LibsignalSim.toWire wc.2)
    (hw : CryptoGames.Ratchet.LibsignalSim.toWire c' = w)
    (htr : (x.1.base.mir.inTransit Q.other w).isSome = false)
    (htriv_eq : ∀ pos, x.2.1.trivial 3 pos = x.1.base.mir.trivial 3 pos)
    (hep_lt : x.1.base.mir.epoch Q < c'.1.1) :
    (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' honestC c' x).2.1 = x.1 ∧
    clearWin (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq'
      honestC c' x).2.2.1 = clearWin x.2.1 := by
  unfold clearWin
  have hfwd :=
    fwdPure_of_inTransit_false (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
      CryptoGames.SM.Config.h1 x.1.base Q w c' x.2.1 hhon hw htr
  refine fwdCPure_inject_of_fwdPure_not_accepted P ℓ Dh encPt encT idOf lam qep Q w ci? T pq'
    honestC c' x ?_ ?_
  · intro t i m
    rw [hfwd]
    unfold injectPure
    split
    · simp
    · cases hrec : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (x.2.1.st Q) c' with
      | none => simp
      | some val =>
        rcases val with ⟨st', t', i', pm⟩
        rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
          (x.2.1.st Q) c' hrec with ⟨ht', _⟩
        dsimp only
        split
        · simp
        · have htriv_f : x.1.base.mir.trivial 3 ⟨Q.other, t', i'⟩ = false :=
            trivial_false_of_newChain_inject hsafe hcomp Q ⟨Q.other, t', i'⟩
              (by dsimp only; omega)
          rw [htriv_eq, htriv_f]
          simp
  · rw [hfwd]
    unfold injectPure
    split
    · rfl
    · cases hrec : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (x.2.1.st Q) c' with
      | none => rfl
      | some val =>
        rcases val with ⟨st', t', i', pm⟩
        rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
          (x.2.1.st Q) c' hrec with ⟨ht', _⟩
        dsimp only
        split
        · rfl
        · have htriv_f : x.1.base.mir.trivial 3 ⟨Q.other, t', i'⟩ = false :=
            trivial_false_of_newChain_inject hsafe hcomp Q ⟨Q.other, t', i'⟩
              (by dsimp only; omega)
          rw [htriv_eq, htriv_f]
          simp only [Bool.false_eq_true, ↓reduceIte]
          split <;> rfl

/-- Combined game-level and refinement invariant for `kemFailSimImpl`. -/
@[expose] def EvictedSpurHistSimInv
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r w_rem : ℕ)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  EvictedSpurHistGameInv P K qep w_rem sC ∧
  EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q r sC g

theorem evictedSpurHistSimInv_init
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hS : CryptoGames.LibsignalSM.Proofs.Refinement.SpqrCLocal P.spqr q InvPQ)
    (b : Bool) (k : BitVec 256 × BitVec 256) (pqrKey : BitVec 256)
    (hcoll0 : ∃ eA₀ : BitVec 256, Dh.dh eA₀ Dh.base ≠ Dh.dh k.2 Dh.base) :
    EvictedSpurHistSimInv P K InvPQ ℓ Dh encPt encT idOf lam qep q q qep
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (CryptoGames.SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b) :=
  ⟨evictedSpurHistGameInv_init P K pqrKey qep,
   evictedSpurSimInv_init P InvPQ ℓ Dh encPt encT idOf lam qep q hX hS b k pqrKey hcoll0⟩

theorem kemFailSimImpl_deliver_eq_simRecvStepC
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (Q : Party) (w : List (BitVec 8))
    {z : Option (CryptoGames.SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F)}
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, gh, tr))) :
    (z.1, (z.2.1, z.2.2.1)) =
      CryptoGames.LibsignalSM.Proofs.Refinement.simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh) := by
  rw [kemFailSimImpl_deliver_run, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictAccEpoch_le_of_inWin_false
    {s : SimState (List (BitVec 8)) Pt ℓ} {Q : Party}
    (hinwQ : inReceiveOnlyEpoch s.mir Q = false)
    (hep_adj : ∀ P,
      (inReceiveOnlyEpoch s.mir P = true → s.mir.epoch P ≤ s.mir.epoch P.other) ∧
      (inReceiveOnlyEpoch s.mir P = false → s.mir.epoch P ≤ s.mir.epoch P.other + 1))
    (R : Party) :
    CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir R ≤ s.mir.epoch Q := by
  have hOO : Q.other.other = Q := by cases Q <;> rfl
  by_cases hRQ : R = Q
  · subst hRQ
    unfold CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch
    rw [hinwQ]
    simp
  · have hRO : R = Q.other := by cases R <;> cases Q <;> first | contradiction | rfl
    subst hRO
    unfold CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch
    split
    · rename_i hinwO
      have hle := (hep_adj Q.other).1 hinwO
      rwa [hOO] at hle
    · rename_i hinwO
      have hle := (hep_adj Q.other).2 (Bool.eq_false_iff.mpr hinwO)
      rw [hOO] at hle
      omega

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictAccEpoch_and_honestBeforeEpoch_new_epoch_send
    {s s' : SimState (List (BitVec 8)) Pt ℓ}
    {Q : Party} {w_new : List (BitVec 8)} {c_new : Fig8C Pt}
    (hinwQ : inReceiveOnlyEpoch s.mir Q = true)
    (hinwQ' : inReceiveOnlyEpoch s'.mir Q = false)
    (hep : s'.mir.epoch = Function.update s.mir.epoch Q (s.mir.epoch Q + 1))
    (hhon : s'.honest = (w_new, c_new) :: s.honest)
    (hc_ep : c_new.1.1 = s.mir.epoch Q + 1)
    (hother_le : s.mir.epoch Q.other ≤ s.mir.epoch Q + 1) :
    ∀ R,
      CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s'.mir R = CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir R ∧
      CryptoGames.LibsignalSM.Proofs.Refinement.honestBeforeEpoch s'.honest (CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s'.mir R) =
        CryptoGames.LibsignalSM.Proofs.Refinement.honestBeforeEpoch s.honest (CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir R) := by
  intro R
  have hev_eq : CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s'.mir R =
      CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir R := by
    by_cases hRQ : R = Q
    · subst hRQ
      unfold CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch
      rw [hinwQ', hinwQ, hep, Function.update_self]
      simp
    · unfold CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch inReceiveOnlyEpoch
      rw [hep, Function.update_of_ne hRQ]
  refine ⟨hev_eq, ?_⟩
  have hev_le : CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir R ≤ c_new.1.1 := by
    rw [hc_ep]
    by_cases hRQ : R = Q
    · subst hRQ; unfold CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch; split <;> omega
    · have hRO : R = Q.other := by cases R <;> cases Q <;> first | contradiction | rfl
      subst hRO; unfold CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch; split <;> omega
  rw [hhon, hev_eq]
  exact CryptoGames.LibsignalSM.Proofs.Refinement.honestBeforeEpoch_cons_of_le s.honest w_new c_new
    (CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir R) hev_le

omit [SampleableType Pt] in
theorem kemFailSendStep_run_of_guard_fail {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (hfail :
      (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true ∨
      sC.base.mir.epMgmt 3 qep Q r.isSome = none ∨
      ∃ s₁, sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁ ∧
        (chal.isSome && !s₁.safeCh 3 Q) = true) :
    (kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run (sC, gh, tr) =
      pure (none, (sC, gh, tr)) := by
  unfold kemFailSendStep
  rw [stateT_run_get_bind_prod3]
  rcases hfail with hg1 | hg2 | ⟨s₁, hep, hg3⟩
  · simp [hg1]
  · by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true
    · simp [hg1]
    · simp [hg1, hg2]
  · by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true
    · simp [hg1]
    · simp [hg1, hep, hg3]

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_transmitQuery_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ((probeHook fig (qep + 1)).lift (CryptoGames.SM.transmitQuery Q m rc)).run (g, false) =
      if g.win then pure (none, (g, false))
      else CryptoGames.SM.samIfNec rc >>= fun cb =>
        let z := transmitPure fig 3 (qep + 1) Q m cb.1 cb.2 g
        pure (z.1, (z.2, false)) := by
  rw [probeHook_lift_run, ← bind_pure (CryptoGames.SM.transmitQuery Q m rc)]
  unfold fig8ImplH1
  rw [simulateQ_transmitQuery_run fig 3 (qep + 1) CryptoGames.SM.Config.h1 Q m rc pure g]
  split <;> simp [simulateQ_pure, StateT.run_pure]

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_challQuery_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ((probeHook fig (qep + 1)).lift (CryptoGames.SM.challQuery Q m₀ m₁ rc)).run (g, false) =
      if g.win then pure (none, (g, false))
      else CryptoGames.SM.samIfNec rc >>= fun cb =>
        let z := challPure fig 3 (qep + 1) CryptoGames.SM.Config.h1 Q m₀ m₁ cb.1 cb.2 g
        pure (z.1, (z.2, false)) := by
  rw [probeHook_lift_run, ← bind_pure (CryptoGames.SM.challQuery Q m₀ m₁ rc)]
  unfold fig8ImplH1
  rw [simulateQ_challQuery_run fig 3 (qep + 1) CryptoGames.SM.Config.h1 Q m₀ m₁ rc pure g]
  split <;> simp [simulateQ_pure, StateT.run_pure]

theorem kemFailSendStep_rc_isSome {r : Option (BitVec 512)} {rc : Option (BitVec 256)}
    (hrc : (r = none ∧ rc = none) ∨ (∃ rq c_cka, r = some rq ∧ rc = some c_cka)) :
    rc.isSome = r.isSome := by
  rcases hrc with ⟨rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ <;> rfl

theorem stateT_run_kemFailSend_coins_support {σ α : Type}
    (r : Option (BitVec 512)) (st : σ)
    (k : BitVec 512 → Option (BitVec 256) → StateT σ ProbComp α)
    (z : α × σ)
    (hz : z ∈ support ((do
      let rq ← match r with
        | some rq => pure rq
        | none => liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512))
      let rc : Option (BitVec 256) ← match r with
        | some _ => some <$> liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        | none => pure none
      k rq rc).run st)) :
    ∃ rq rc,
      ((r = none ∧ rc = none) ∨ (∃ rq' c_cka, r = some rq' ∧ rq = rq' ∧ rc = some c_cka)) ∧
      z ∈ support ((k rq rc).run st) := by
  cases r with
  | none =>
    simp only [StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      pure_bind, bind_assoc] at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨rq, _, hz⟩
    exact ⟨rq, none, Or.inl ⟨rfl, rfl⟩, hz⟩
  | some rq =>
    simp only [StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      map_eq_bind_pure_comp, Function.comp_apply, pure_bind, bind_assoc] at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨c_cka, _, hz⟩
    exact ⟨rq, some c_cka, Or.inr ⟨rq, c_cka, rfl, rfl, rfl⟩, hz⟩

omit [SampleableType Pt] in
theorem kemFailSendStep_of_fig8_win {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hg_win : g.win = true)
    (z : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run
      (sC, (g, false), tr))) :
    z.1 = none ∧ z.2.1 = sC ∧ z.2.2.1 = (g, false) := by
  by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r
      sC (g, false) tr (Or.inl hg1), support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl, rfl⟩
  cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
  | none =>
    rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r
      sC (g, false) tr (Or.inr (Or.inl hep)), support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl, rfl⟩
  | some s₁ =>
    by_cases hg3 : (chal.isSome && !s₁.safeCh 3 Q) = true
    · rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r
        sC (g, false) tr (Or.inr (Or.inr ⟨s₁, hep, hg3⟩)),
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl, rfl⟩
    have hg1_f : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = false :=
      Bool.eq_false_iff.mpr hg1
    have hg3_f : (chal.isSome && !s₁.safeCh 3 Q) = false := Bool.eq_false_iff.mpr hg3
    unfold kemFailSendStep at hz
    rw [stateT_run_get_bind_prod3] at hz
    simp only [hg1_f, Bool.false_eq_true, ↓reduceIte, hep, hg3_f] at hz
    obtain ⟨rq, rc, _, hz⟩ := stateT_run_kemFailSend_coins_support r (sC, (g, false), tr) _ z hz
    cases hmk : mkPub P sC.base Q rq
        (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
         else sC.base.pn Q) with
    | none =>
      simp only [hmk, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl, rfl⟩
    | some pq_pub =>
      rcases pq_pub with ⟨pq', pub⟩
      simp only [hmk, StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
        bind_pure_comp, map_eq_bind_pure_comp, Function.comp_apply,
        bind_assoc, pure_bind] at hz
      rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨⟨res_f, gh'⟩, hz_fig, hz⟩
      have hz_fig_eq : (res_f, gh') = (none, (g, false)) := by
        cases chal with
        | none =>
          rw [probeHook_lift_transmitQuery_run, ite_eq_left hg_win, support_pure,
            Set.mem_singleton_iff] at hz_fig
          exact hz_fig
        | some m₁ =>
          rw [probeHook_lift_challQuery_run, ite_eq_left hg_win, support_pure,
            Set.mem_singleton_iff] at hz_fig
          exact hz_fig
      rcases Prod.mk.injEq _ _ _ _ |>.mp hz_fig_eq with ⟨rfl, rfl⟩
      simp only [StateT.run_bind, StateT.run_set, pure_bind] at hz
      have hz' : z = (none, (sC, (g, false),
          { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand })) := hz
      subst hz'; exact ⟨rfl, rfl, rfl⟩

omit [SampleableType Pt] in
theorem probeHook_lift_send_support
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (pub : LibsignalMsgPublicPart) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (rc : Option (BitVec 256))
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hg_win : g.win = false)
    (z_fig : Option (Fig8C Pt) ×
      (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool))
    (hz : z_fig ∈ support
      (((probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)).lift
        (match chal with
         | none => CryptoGames.SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
         | some m₁ => CryptoGames.SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc)).run
        (g, false))) :
    ∃ c_cka : BitVec 256,
      (rc = none ∨ rc = some c_cka) ∧
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let f8 := chal.elim
        (transmitPure fig 3 (qep + 1) Q (pub, m₀) c_cka rc.isSome g)
        (fun m₁ => challPure fig 3 (qep + 1) CryptoGames.SM.Config.h1 Q (pub, m₀) (pub, m₁)
          c_cka rc.isSome g)
      z_fig = (f8.1, (f8.2, false)) := by
  cases chal with
  | none =>
    rw [probeHook_lift_transmitQuery_run] at hz
    cases rc with
    | none =>
      simp only [hg_win, Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.samIfNec, bind_assoc, pure_bind] at hz
      rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨c_cka, _, hz⟩
      simp only [support_pure, Set.mem_singleton_iff] at hz
      exact ⟨c_cka, Or.inl rfl, hz⟩
    | some c_cka =>
      simp only [hg_win, Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.samIfNec, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      exact ⟨c_cka, Or.inr rfl, hz⟩
  | some m₁ =>
    rw [probeHook_lift_challQuery_run] at hz
    cases rc with
    | none =>
      simp only [hg_win, Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.samIfNec, bind_assoc, pure_bind] at hz
      rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨c_cka, _, hz⟩
      simp only [support_pure, Set.mem_singleton_iff] at hz
      exact ⟨c_cka, Or.inl rfl, hz⟩
    | some c_cka =>
      simp only [hg_win, Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.samIfNec, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      exact ⟨c_cka, Or.inr rfl, hz⟩

omit [SampleableType Pt] in
theorem kemFailSendStep_support_of_guards
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (s₁ : CryptoGames.SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hg1 : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false)
    (hg_win : g.win = false)
    (z : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run
      (sC, (g, false), tr))) :
    ∃ (rq : BitVec 512) (c_cka : BitVec 256),
      (r = none ∨ r = some rq) ∧
      let pn :=
        if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
        else sC.base.pn Q
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let tr' := stepKemFailSend P.C.F K tr Q rq
      match mkPub P sC.base Q rq pn with
      | none => z = (none, (sC, (g, false), { tr with cand := tr'.cand }))
      | some (pq', pub) =>
        let f8 := chal.elim
          (transmitPure fig 3 (qep + 1) Q (pub, m₀) c_cka r.isSome g)
          (fun m₁ => challPure fig 3 (qep + 1) CryptoGames.SM.Config.h1 Q (pub, m₀) (pub, m₁)
            c_cka r.isSome g)
        match f8.1 with
        | none => z = (none, (sC, (f8.2, false), { tr with cand := tr'.cand }))
        | some c =>
          let w := toWire c
          let rec' : CryptoGames.SM.Record (Plain ℓ) (List (BitVec 8)) :=
            ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
          let base' : SimState (List (BitVec 8)) Pt ℓ :=
            { sC.base with
              mir := s₁.record 3 Q () rec' chal.isSome
              pq := Function.update sC.base.pq Q pq'
              pn := Function.update sC.base.pn Q pn
              honest := (w, c) :: sC.base.honest }
          z = (some w,
            (cxSend P Dh encPt encT idOf lam Q sC base' (some w), (f8.2, false), tr')) := by
  unfold kemFailSendStep at hz
  rw [stateT_run_get_bind_prod3] at hz
  simp only [hg1, Bool.false_eq_true, ↓reduceIte, hep, hg3] at hz
  obtain ⟨rq, rc, hrc, hz⟩ := stateT_run_kemFailSend_coins_support r (sC, (g, false), tr) _ z hz
  have hrc_some : rc.isSome = r.isSome :=
    kemFailSendStep_rc_isSome (hrc.imp id fun ⟨rq', c_cka, hr1, _, hrc1⟩ => ⟨rq', c_cka, hr1, hrc1⟩)
  have hr_or : r = none ∨ r = some rq :=
    hrc.imp (·.1) fun ⟨_, _, hr1, hrq, _⟩ => hrq ▸ hr1
  cases hmk : mkPub P sC.base Q rq
      (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
       else sC.base.pn Q) with
  | none =>
    simp only [hmk, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hz
    refine ⟨rq, 0, hr_or, ?_⟩
    dsimp only
    rw [hmk, hz]
  | some pq_pub =>
    rcases pq_pub with ⟨pq', pub⟩
    simp only [hmk, StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      bind_pure_comp, map_eq_bind_pure_comp, Function.comp_apply,
      bind_assoc, pure_bind] at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨res_f, gh'⟩, hz_fig, hz⟩
    obtain ⟨c_cka, _, hz_fig_eq⟩ :=
      probeHook_lift_send_support P ℓ Dh encPt encT idOf lam qep Q pub m₀ chal rc g hg_win
        (res_f, gh') hz_fig
    rw [hrc_some] at hz_fig_eq
    rcases Prod.mk.injEq _ _ _ _ |>.mp hz_fig_eq with ⟨hres_eq, hgh_eq⟩
    subst hres_eq hgh_eq
    refine ⟨rq, c_cka, hr_or, ?_⟩
    dsimp only
    rw [hmk]
    dsimp only
    split
    · next hf8 =>
      simp only [hf8, StateT.run_bind, StateT.run_set, pure_bind] at hz
      exact hz
    · next c hf8 =>
      simp only [hf8, StateT.run_bind, StateT.run_set, pure_bind] at hz
      exact hz

omit [DecidableEq Pt] [SampleableType Pt] in
theorem simSendStep_eq_of_mkPub_some
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : CryptoGames.SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (rq : BitVec 512) (c_cka : BitVec 256)
    (s : SimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (pq' : List (BitVec 8)) (pub : LibsignalMsgPublicPart) (c : Fig8C Pt)
    (hmk : mkPub P s Q rq
      (if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q) =
      some (pq', pub))
    (hf8 : (chal.elim
      (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
        (pub, m₀) c_cka bad g)
      (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        CryptoGames.SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad g)).1 = some c) :
    let f8 := chal.elim
      (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
        (pub, m₀) c_cka bad g)
      (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        CryptoGames.SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad g)
    let pn := if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q
    let w := toWire c
    let rec' : CryptoGames.SM.Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
    let base' : SimState (List (BitVec 8)) Pt ℓ :=
      { s with
        mir := s₁.record 3 Q () rec' chal.isSome
        pq := Function.update s.pq Q pq'
        pn := Function.update s.pn Q pn
        honest := (w, c) :: s.honest }
    simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka (s, g) =
      (some w, (base', f8.2)) := by
  unfold simSendStep
  cases chal with
  | none =>
    simp only [hmk, Option.elim] at hf8 ⊢
    cases h : transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
      (pub, m₀) c_cka bad g
    rw [h] at hf8; cases hf8; rfl
  | some m₁ =>
    simp only [hmk, Option.elim] at hf8 ⊢
    cases h : challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
      CryptoGames.SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad g
    rw [h] at hf8; cases hf8; rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem mkPub_eq_some_of_spqrCLocal
    {P : Params (List (BitVec 8)) (BitVec 512)} {Inv : ℕ → List (BitVec 8) → Prop} {q r : ℕ}
    (hS : SpqrCLocal P.spqr q Inv) (hr : 0 < r)
    (s : SimState (List (BitVec 8)) Pt ℓ) (Q : Party) (rq : BitVec 512) (pn : BitVec 32)
    (hpq : InvB Inv q r (s.pq Q)) :
    ∃ pq' salt pqMsg,
      P.spqr.send (s.pq Q) rq = some (pq', salt, pqMsg) ∧
      mkPub P s Q rq pn =
        some (pq',
          ⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == CryptoGames.Party.A && s.unackA then P.addrAB else none⟩) := by
  rcases Option.isSome_iff_exists.mp (spqrCLocal_total hS hr (s.pq Q) rq hpq) with
    ⟨⟨pq', salt, pqMsg⟩, hspqr⟩
  exact ⟨pq', salt, pqMsg, hspqr, by simp [mkPub, hspqr]⟩

theorem f8_send_eq_some_of_sameMeta
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (pub : LibsignalMsgPublicPart) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (c_cka : BitVec 256) (bad : Bool)
    (s₁ : CryptoGames.SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (s_R : CryptoGames.SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (s : SimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hmeta : SameMeta s_R s g)
    (hep_mir : s.mir.epMgmt 3 qep Q bad = some s₁)
    (hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true) :
    ∃ s_fig8₁,
      g.epMgmt 3 (qep + 1) Q bad = some s_fig8₁ ∧
      s_fig8₁.st = g.st ∧
      let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let m_enc : Plain ℓ := chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)
      let out := sm.send (g.st Q) (pub, m_enc) c_cka
      chal.elim
        (transmitPure sm 3 (qep + 1) Q (pub, m₀) c_cka bad g)
        (fun m₁ => challPure sm 3 (qep + 1) CryptoGames.SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad g) =
        (some out.2,
          s_fig8₁.record 3 Q out.1
            ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, (pub, m_enc), out.2⟩ chal.isSome) := by
  rcases hmeta.epMgmt_some Q qep bad hep_mir with
    ⟨_, s_fig8₁, _, hep_fig8, _, hst_fig8₁, hmeta₁⟩
  refine ⟨s_fig8₁, hep_fig8, hst_fig8₁, ?_⟩
  cases hchal : chal with
  | none =>
    unfold transmitPure
    rw [hep_fig8]
    dsimp only [Option.elim, Option.isSome]
    rw [hst_fig8₁]
  | some m₁ =>
    have hsafe_f : (!s_fig8₁.safeCh 3 Q) = false := by
      rw [hmeta₁.safeCh_fig8 3 Q, hsafeCh (by simp [hchal])]; rfl
    have hcond_f :
        (!s_fig8₁.safeCh 3 Q ||
          !(CryptoGames.SM.Config.h1 (Msg := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s_fig8₁.epoch Q)) = false := by
      rw [hsafe_f]; rfl
    have hmb : (if g.b = true then (pub, m₁) else (pub, m₀)) =
        (pub, if s_R.b = true then m₁ else m₀) := by
      rw [← hmeta.hb]; cases s_R.b <;> rfl
    dsimp only [Option.elim, Option.isSome]
    unfold challPure
    rw [hep_fig8]
    dsimp only
    rw [hcond_f, ite_eq_right Bool.false_ne_true, hst_fig8₁]
    change (let m := if g.b = true then (pub, m₁) else (pub, m₀);
      let out := (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q) m c_cka;
      (some out.2,
        s_fig8₁.record 3 Q out.1
          ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, m, out.2⟩ true)) = _
    rw [hmb]

theorem kemFailSendStep_support_eq_simSendStep
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r_coin : Option (BitVec 512))
    (s_R : CryptoGames.SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hmeta : SameMeta s_R sC.base { g with win := false })
    (hpq : InvB Inv q r (sC.base.pq Q))
    (z : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin).run
      (sC, (g, false), tr))) :
    (z.1 = none ∧ z.2.1 = sC ∧ z.2.2.1 = (g, false)) ∨
    (g.win = false ∧
      CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q = true ∧
      ∃ s₁, sC.base.mir.epMgmt 3 qep Q r_coin.isSome = some s₁ ∧
        (chal.isSome = true → s₁.safeCh 3 Q = true) ∧
        ∃ (rq : BitVec 512) (c_cka : BitVec 256),
          (r_coin = none ∨ r_coin = some rq) ∧
          let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r_coin.isSome s₁
            rq c_cka (sC.base, g)
          z = (res.1,
            (cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1, (res.2.2, false),
              stepKemFailSend P.C.F K tr Q rq))) := by
  by_cases hg_win : g.win = true
  · exact Or.inl (kemFailSendStep_of_fig8_win P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal
      r_coin sC g tr hg_win z hz)
  have hg_win_f : g.win = false := Bool.eq_false_iff.mpr hg_win
  have hg_clear : { g with win := false } = g := by cases g; simp_all
  rw [hg_clear] at hmeta
  by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin
      sC (g, false) tr (Or.inl hg1), support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact Or.inl ⟨rfl, rfl, rfl⟩
  have hg1_f : (sC.base.stopped || sC.base.mir.win || !CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q) = false :=
    Bool.eq_false_iff.mpr hg1
  have hnoBob : CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q = true := by
    revert hg1_f; cases sC.base.stopped <;> cases sC.base.mir.win <;>
      cases CryptoGames.SM.noBobSendInEpoch0 sC.base.mir Q <;> simp
  cases hep : sC.base.mir.epMgmt 3 qep Q r_coin.isSome with
  | none =>
    rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin
      sC (g, false) tr (Or.inr (Or.inl hep)), support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact Or.inl ⟨rfl, rfl, rfl⟩
  | some s₁ =>
    by_cases hg3 : (chal.isSome && !s₁.safeCh 3 Q) = true
    · rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin
        sC (g, false) tr (Or.inr (Or.inr ⟨s₁, hep, hg3⟩)),
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl ⟨rfl, rfl, rfl⟩
    have hg3_f : (chal.isSome && !s₁.safeCh 3 Q) = false := Bool.eq_false_iff.mpr hg3
    have hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true := by
      intro hch; revert hg3_f; rw [hch]; cases s₁.safeCh 3 Q <;> simp
    obtain ⟨rq, c_cka, hr_or, hz_eq⟩ :=
      kemFailSendStep_support_of_guards P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin s₁
        sC g tr hg1_f hep hg3_f hg_win_f z hz
    set pn :=
      if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
      else sC.base.pn Q
    obtain ⟨pq', salt, pqMsg, _, hmk⟩ :=
      mkPub_eq_some_of_spqrCLocal hS hr sC.base Q rq pn hpq
    set pub : LibsignalMsgPublicPart :=
      ⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == CryptoGames.Party.A && sC.base.unackA then P.addrAB else none⟩
    obtain ⟨s_fig8₁, _, _, hf8_eq⟩ :=
      f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ chal c_cka
        r_coin.isSome s₁ s_R sC.base g hmeta hep hsafeCh
    have hf8_1 : (chal.elim
        (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
          (pub, m₀) c_cka r_coin.isSome g)
        (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          CryptoGames.SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka r_coin.isSome g)).1 =
        some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
          (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka).2 :=
      congrArg Prod.fst hf8_eq
    have hsim_eq := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ chal
      r_coin.isSome s₁ rq c_cka sC.base g pq' pub _ hmk hf8_1
    dsimp only at hz_eq hsim_eq
    rw [hmk] at hz_eq
    dsimp only at hz_eq
    rw [hf8_1] at hz_eq
    dsimp only at hz_eq
    refine Or.inr ⟨hg_win_f, hnoBob, s₁, rfl, hsafeCh, rq, c_cka, hr_or, ?_⟩
    dsimp only
    rw [hsim_eq, hz_eq]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem lAead_enc_parse_pqRatchet
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hrt : CryptoGames.LibsignalSM.Proofs.RoundTrip.RtHyp P ℓ)
    (Q : Party) (unackA : Bool) (pq_st pq' : List (BitVec 8)) (rq : BitVec 512) (salt : CryptoGames.HKDF.Salt)
    (seed : BitVec 256) (i t : ℕ) (T : Pt) (pub : LibsignalMsgPublicPart) (m : Plain ℓ)
    (haddrs_pub : pub.addrs = if Q == CryptoGames.Party.A && unackA then P.addrAB else none)
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg)) :
    ∀ h body,
      (signalWireCodec P.codec).parse
        ((CryptoGames.Ratchet.LibsignalSim.toWire
          ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
            seed (i, (t, some T)) (pub, m)))).take
          ((CryptoGames.Ratchet.LibsignalSim.toWire
            ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
              seed (i, (t, some T)) (pub, m)))).length - 8)) = some (h, body) →
      h.pqRatchet = pub.pqmsg := by
  intro h body hparse
  let c : Fig8C Pt :=
    ((t, some T),
      (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
        seed (i, (t, some T)) (pub, m)))
  set h_hdr := lHeader encT i (t, some T) pub
  set mk := deriveMessageKeys P.C.F (some pub.salt) (keyToBytes32 seed)
  set body_enc := ((cbcPkcs7EncryptOnly P.C.E ℓ).enc (mk.1.1, mk.1.2) m).toList.flatMap blockToBytesLE
  set ser := (signalWireCodec P.codec).encode h_hdr body_enc
  set tag := (hmacScheme P.C.F).tag mk.2 ((lIds idOf t).toList ++ ser)
  have hw_eq : toWire c = ser ++ tagBytes tag := rfl
  have htag_len : (tagBytes tag).length = 8 := length_tagBytes tag
  have hw_sub : (toWire c).length - 8 = ser.length := by
    rw [hw_eq, List.length_append, htag_len]; omega
  have htake : (toWire c).take ((toWire c).length - 8) = ser := by
    rw [hw_sub, hw_eq, List.take_left]
  have hparse_hdr :
      (signalWireCodec P.codec).parse ((toWire c).take ((toWire c).length - 8)) =
        some (h_hdr, body_enc) := by
    rw [htake]
    refine CryptoGames.LibsignalSM.Proofs.RoundTrip.RtHyp.parse hrt h_hdr body_enc rfl
      (Or.inr ⟨_, _, _, _, hspqr_send⟩) ?_ (CryptoGames.LibsignalSM.Proofs.RoundTrip.length_cbcBody _)
    change CryptoGames.LibsignalSM.Proofs.RoundTrip.SentAddrs P pub.addrs
    rw [haddrs_pub]
    cases Q <;> cases unackA
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
  change (signalWireCodec P.codec).parse ((toWire c).take ((toWire c).length - 8)) =
    some (h, body) at hparse
  rw [hparse_hdr] at hparse
  injection hparse with hpair
  rcases Prod.mk.inj hpair with ⟨rfl, _⟩
  rfl

omit [SampleableType Pt] [DecidableEq Pt] in
theorem lFig8_send_eq_lAead_not_inWin
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (epExp : ℕ → BitVec 256) (Q : Party) (st : Fig8St Pt) (t : ℕ)
    (hst_id : st.id = Q) (htcur : st.tcur = t) (hsends : Q.sendsIn t = true)
    (hTcur : st.curCkaMsg = some (Dh.dh (epExp t) Dh.base))
    (v : CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)) (hvS : st.vS = some v)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (c_cka : BitVec 256) :
    ∃ seed i,
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) c_cka).2 =
        ((t, some (Dh.dh (epExp t) Dh.base)),
          (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
            seed (i, (t, some (Dh.dh (epExp t) Dh.base))) (pub, m))) := by
  have hnot_succ : st.id.sendsIn (st.tcur + 1) = false := by
    rw [hst_id, htcur]
    exact sendsIn_succ_of_sendsIn Q t hsends
  unfold lFig8 CryptoGames.SM.Construction.scheme CryptoGames.SM.Construction.send lFS CryptoGames.FSAEAD.fromAEADPRG
  dsimp only
  rw [hnot_succ, ite_eq_right Bool.false_ne_true, hvS, htcur, hTcur]
  exact ⟨_, _, rfl⟩

omit [SampleableType Pt] [DecidableEq Pt] in
theorem lFig8_send_eq_lAead_inWin
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (st : Fig8St Pt) (t : ℕ) (T_other : Pt)
    (hst_id : st.id = Q) (htcur : st.tcur + 1 = t) (hsends : Q.sendsIn t = true)
    (hγ : st.γ = .pub T_other)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (c_cka : BitVec 256) :
    ∃ seed,
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) c_cka).2 =
        ((t, some (Dh.dh c_cka Dh.base)),
          (1, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
            seed (1, (t, some (Dh.dh c_cka Dh.base))) (pub, m))) := by
  have hsends_succ : st.id.sendsIn (st.tcur + 1) = true := by
    rw [hst_id, htcur]; exact hsends
  unfold lFig8 CryptoGames.SM.Construction.scheme CryptoGames.SM.Construction.send lFS CryptoGames.FSAEAD.fromAEADPRG dhScheme
  dsimp only
  rw [hsends_succ, ite_eq_left rfl, hγ, htcur]
  dsimp only
  rw [Nat.zero_add]
  exact ⟨_, rfl⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem accept_epoch_le {St Msg C : Type}
    (mir : CryptoGames.SM.GameState St Msg C) (Q R : Party) (st' : St) (pos : CryptoGames.SM.Pos) :
    mir.epoch R ≤ (mir.accept Q st' pos).epoch R := by
  unfold CryptoGames.SM.GameState.accept CryptoGames.SM.GameState.delete
  dsimp only
  by_cases hR : R = Q
  · subst hR; simp [Function.update_self]
  · simp [Function.update_of_ne hR]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAcceptPure_epoch_le {PQ : Type}
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) (R : Party) :
    s.mir.epoch R ≤ (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.mir.epoch R := by
  unfold onAcceptPure
  dsimp only
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · exact le_rfl
    · split
      · exact accept_epoch_le s.mir Q R () ⟨Q.other, t, i⟩
      · exact le_rfl
  · simp only [↓reduceIte]
    split
    · exact le_rfl
    · exact accept_epoch_le s.mir Q R () _

theorem evalCK_some_some_epoch_eq
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt)
    {t i : ℕ} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = some (some (t, i, pm))) :
    t = c'.1.1 := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  unfold predictReceiveWithSnapshots predictReceive at heval
  cases hk : CryptoGames.Ratchet.LibsignalSimC.Kept.eval (fig := fig) (fs := fs) c' (sC.kept Q) with
  | some r_k =>
    rw [hk] at heval
    cases heval
    unfold CryptoGames.Ratchet.LibsignalSimC.Kept.eval at hk
    cases hfull : (sC.kept Q).full with
    | some st =>
      rw [hfull] at hk
      simp only [Option.some.injEq, Option.map_eq_some_iff] at hk
      rcases hk with ⟨⟨st', t₁, i₁, pm₁⟩, hrcv, hpair⟩
      rcases Prod.mk.inj hpair with ⟨rfl, _⟩
      exact (lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam st c' hrcv).1
    | none =>
      rw [hfull] at hk
      simp only [Option.map_eq_some_iff] at hk
      rcases hk with ⟨v, _, x, _, hpair⟩
      exact (congrArg Prod.fst hpair).symm
  | none =>
    rw [hk] at heval
    cases hs : sentEval (fs := fs) sC.sent c c' with
    | some r_s =>
      rw [hs] at heval
      cases heval
      unfold sentEval at hs
      simp only [Option.map_eq_some_iff] at hs
      rcases hs with ⟨e, _, x, _, hpair⟩
      exact (congrArg Prod.fst hpair).symm
    | none =>
      rw [hs] at heval
      simp only [Option.orElse_none, Option.map_eq_some_iff] at heval
      rcases heval with ⟨seed, _, hdec⟩
      unfold kDecryptFig8 at hdec
      split at hdec
      · simp only [Option.some.injEq] at hdec
        exact (congrArg Prod.fst hdec).symm
      · cases hdec

theorem fwdEvictCPure_deliver_eq_of_not_honest
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (T : PublicKey) (pq' : List (BitVec 8)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hsafe_or : c3a = false → x.1.base.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, CryptoGames.SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hc'_not_hon : ∀ wc ∈ x.1.base.honest, wc.2 ≠ c')
    (htriv_eq : ∀ pos, x.2.1.trivial 3 pos = x.1.base.mir.trivial 3 pos)
    (hep_lt : x.1.base.mir.epoch Q < c'.1.1) :
    (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w true T pq' c' x).2.1 = x.1 ∧
    clearWin (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w true T pq' c' x).2.2.1 =
      clearWin x.2.1 := by
  unfold fwdEvictCPure
  split
  · exact ⟨rfl, rfl⟩
  · rename_i hnot_probe
    have hsafe : x.1.base.mir.safeInj 3 = true := by
      cases hc3a : c3a
      · exact hsafe_or hc3a
      · subst hc3a
        revert hnot_probe
        cases x.1.base.mir.safeInj 3 <;> simp
    have hfwd :
        fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) CryptoGames.SM.Config.h1
          x.1.base Q c' x.2.1 =
        injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) CryptoGames.SM.Config.h1
          Q c' x.2.1 := by
      unfold fwdPure
      have hany :
          x.1.base.honest.any
            (fun wc => decide (wc.2 = c') && (x.1.base.mir.inTransit Q.other wc.1).isSome) =
          false := by
        rw [List.any_eq_false]
        intro wc hwc
        simp [hc'_not_hon wc hwc]
      rw [hany]
      rfl
    unfold fwdCPure clearWin
    dsimp only
    rw [hfwd]
    unfold injectPure
    split
    · unfold onAnswerPure; exact ⟨rfl, rfl⟩
    · cases hrec :
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (x.2.1.st Q) c' with
      | none => unfold onAnswerPure; exact ⟨rfl, rfl⟩
      | some val =>
        rcases val with ⟨st', t', i', pm⟩
        rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
          (x.2.1.st Q) c' hrec with ⟨ht', _⟩
        dsimp only
        split
        · unfold onAnswerPure; exact ⟨rfl, rfl⟩
        · have htriv_f : x.1.base.mir.trivial 3 ⟨Q.other, t', i'⟩ = false :=
            trivial_false_of_newChain_inject hsafe hcomp Q ⟨Q.other, t', i'⟩
              (by dsimp only; omega)
          rw [htriv_eq, htriv_f]
          simp only [Bool.false_eq_true, ↓reduceIte]
          split <;> (unfold onAnswerPure; exact ⟨rfl, rfl⟩)

theorem fwdCPure_deliver_base_cases
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ) :
    let s' := (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w true ci? T pq' honestC c' x).2.1.base
    s' = x.1.base ∨
      ∃ i m, s' = (onAcceptPure qep Q w true c'.1.1 i m ci? T pq' x.1.base).2 := by
  have hplain :
      (let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
       let z := fwdPure fig 3 (qep + 1) CryptoGames.SM.Config.h1 x.1.base Q c' x.2.1
       let a := onAnswerPure qep Q w true ci? T pq' z.1 x.1.base
       a.2) = x.1.base ∨
      ∃ i m,
        (let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
         let z := fwdPure fig 3 (qep + 1) CryptoGames.SM.Config.h1 x.1.base Q c' x.2.1
         let a := onAnswerPure qep Q w true ci? T pq' z.1 x.1.base
         a.2) = (onAcceptPure qep Q w true c'.1.1 i m ci? T pq' x.1.base).2 := by
    dsimp only
    cases hz : (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        CryptoGames.SM.Config.h1 x.1.base Q c' x.2.1).1 with
    | none => exact Or.inl rfl
    | some r8 =>
      cases r8 with
      | rejected => exact Or.inl rfl
      | accepted t₁ i₁ pm₁ =>
        have ht₁ : t₁ = c'.1.1 :=
          fwdPure_accepted_epoch_eq P ℓ Dh encPt encT idOf lam qep x.1.base Q c' x.2.1 hz
        subst ht₁
        exact Or.inr ⟨i₁, (pm₁.map (·.2)).getD default, rfl⟩
  unfold fwdCPure
  dsimp only
  cases honestC with
  | none => exact hplain
  | some c₀ =>
    dsimp only
    split
    · cases heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) P x.1 Q w c₀ c' with
      | none => exact Or.inl rfl
      | some ev =>
        cases ev with
        | none => exact Or.inl rfl
        | some tip =>
          rcases tip with ⟨t₁, i₁, pm₁⟩
          dsimp only
          have ht₁ : t₁ = c'.1.1 :=
            evalCK_some_some_epoch_eq P ℓ Dh encPt encT idOf lam x.1 Q w c₀ c' heval
          subst ht₁
          split
          · exact Or.inr ⟨i₁, pm₁.2, rfl⟩
          · exact Or.inl rfl
    · exact hplain

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAcceptPure_deliver_honest_and_mir {PQ : Type}
    (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    let s' := (onAcceptPure qep Q w true t i m ci? T pq' s).2
    s'.honest = s.honest ∧
      (s'.mir = s.mir ∨
        ∃ r, s.mir.inTransit Q.other w = some r ∧ s'.mir = s.mir.accept Q () r.pos) := by
  unfold onAcceptPure
  dsimp only
  simp only [↓reduceIte]
  cases htr : s.mir.inTransit Q.other w with
  | none => exact ⟨rfl, Or.inl rfl⟩
  | some r => exact ⟨rfl, Or.inr ⟨r, rfl, rfl⟩⟩

theorem simRecvStepC_deliver_honest_and_mir
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (gh : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    let s' := (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)).2.1.base
    s'.honest = sC.base.honest ∧
      (s'.mir = sC.base.mir ∨
        ∃ r, sC.base.mir.inTransit Q.other w = some r ∧
          s'.mir = sC.base.mir.accept Q () r.pos) := by
  have hfwd : ∀ c3a ci? T pq' honestC c' (x : JointC (List (BitVec 8)) Pt ℓ),
      x.1.base.honest = sC.base.honest → x.1.base.mir = sC.base.mir →
      let s' :=
        (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w true ci? T pq' honestC c' x).2.1.base
      s'.honest = sC.base.honest ∧
        (s'.mir = sC.base.mir ∨
          ∃ r, sC.base.mir.inTransit Q.other w = some r ∧
            s'.mir = sC.base.mir.accept Q () r.pos) := by
    intro c3a ci? T pq' honestC c' x hhon hmir
    rcases fwdCPure_deliver_base_cases P ℓ Dh encPt encT idOf lam qep c3a Q w ci? T pq'
        honestC c' x with h1 | ⟨i₁, m₁, h2⟩
    · exact ⟨(congrArg (·.honest) h1).trans hhon, Or.inl ((congrArg (·.mir) h1).trans hmir)⟩
    · obtain ⟨hh, hm⟩ := onAcceptPure_deliver_honest_and_mir qep Q w c'.1.1 i₁ m₁ ci? T pq' x.1.base
      rw [hhon] at hh
      rw [hmir] at hm
      exact ⟨(congrArg (·.honest) h2).trans hh, (congrArg (·.mir) h2) ▸ hm⟩
  have hev_fwd : ∀ c3a T pq' c' (x : JointC (List (BitVec 8)) Pt ℓ),
      x.1.base.honest = sC.base.honest → x.1.base.mir = sC.base.mir →
      let s' := (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w true T pq' c' x).2.1.base
      s'.honest = sC.base.honest ∧
        (s'.mir = sC.base.mir ∨
          ∃ r, sC.base.mir.inTransit Q.other w = some r ∧
            s'.mir = sC.base.mir.accept Q () r.pos) := by
    intro c3a T pq' c' x hhon hmir
    unfold fwdEvictCPure
    dsimp only
    split
    · exact ⟨hhon, Or.inl hmir⟩
    · exact hfwd false none T pq' none c' x hhon hmir
  unfold simRecvStepC simRecvStepCGen
  by_cases hst : sC.base.stopped = true
  · simp [hst]
  simp only [hst, Bool.false_eq_true, ↓reduceIte]
  by_cases hwin : sC.base.mir.win = true
  · simp [hwin]
  simp only [hwin, Bool.false_eq_true, ↓reduceIte]
  by_cases htr : (sC.base.mir.inTransit Q.other w).isNone = true
  · simp [htr]
  simp only [htr, Bool.and_false, Bool.not_true, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : w.length < 9
  · simp [hlen]
  simp only [hlen, ↓reduceIte]
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact ⟨rfl, Or.inl rfl⟩
  | some hb =>
    rcases hb with ⟨h, body⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · simp [haddr]
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
    · simp [hpan]
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact ⟨rfl, Or.inl rfl⟩
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        split
        · exact ⟨rfl, Or.inl rfl⟩
        · exact hfwd true _ _ _ _ _ (sC, gh) rfl rfl
      | none =>
        dsimp only
        have hstop : sC.base.stopped = false := Bool.eq_false_iff.mpr hst
        have hs_stop : { sC.base with amb := sC.base.amb + 1, stopped := false } =
            { sC.base with amb := sC.base.amb + 1 } := by
          cases h_s : sC.base; rw [h_s] at hstop; subst hstop; rfl
        simp only [hs_stop]
        let x₁ : JointC (List (BitVec 8)) Pt ℓ :=
          if inReceiveOnlyEpoch sC.base.mir Q || (Q == CryptoGames.Party.A && (sC.base.chains Q).any (·.key.isNone)) then
            ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, gh)
          else (sC, gh)
        have hx1_hon : x₁.1.base.honest = sC.base.honest := by
          dsimp only [x₁]; split <;> rfl
        have hx1_mir : x₁.1.base.mir = sC.base.mir := by
          dsimp only [x₁]; split <;> rfl
        split
        · exact ⟨rfl, Or.inl rfl⟩
        · split
          · exact ⟨rfl, Or.inl rfl⟩
          · split
            · exact ⟨hx1_hon, Or.inl hx1_mir⟩
            · cases hT : decT h.senderRatchetKey with
              | none => dsimp only; exact ⟨hx1_hon, Or.inl hx1_mir⟩
              | some T =>
                dsimp only
                split
                · exact hev_fwd true _ _ _ x₁ hx1_hon hx1_mir
                · exact hfwd true none _ _ _ _ x₁ hx1_hon hx1_mir

/-- No-forgery invariant on evicted honest wires at party `Q`. -/
@[expose] def EvictedOnlyNoForgeAt {PQ PQC : Type}
    (P : Params PQ PQC) (decT : PublicKey → Option Pt)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) : Prop :=
  ∀ w c h body pq' salt,
    (w, c) ∈ sC.base.honest →
    CryptoGames.Party.senderOf c.1.1 = Q.other →
    (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body) →
    P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt) →
    (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) = none →
    c.1.1 ≠ sC.base.mir.epoch Q + 1 →
    inReceiveOnlyEpoch sC.base.mir Q = false →
    ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1) →
    sC.base.mir.safeInj 3 = false →
    ∀ T, decT h.senderRatchetKey = some T →
      fig.receive (g.st Q)
        ((sC.base.mir.epoch Q + 1, some T),
          (h.counter.toNat + 1,
            ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) = none

/-- Lazy-coin variant of `SimInvC` bounding honest and collision epochs by the current maximum epoch. -/
structure SimInvCLazy {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ)
    (x₀ : BitVec 256)
    (s_R : CryptoGames.SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool)
    (epExp : ℕ → BitVec 256) : Prop where
  hmeta : SameMeta s_R s s_fig8
  hcomp : ∀ p ∈ s.mir.comp, CryptoGames.SM.healedBy s.mir.tL 3 p.epoch = false
  hec : ValidEagerCoins s.mir ec
  hwinBefore : ∀ j < s.amb, winBefore j = false
  hamb : s.amb + r ≤ q
  hamb_strict : (0 < s.mir.epoch .A ∨ 0 < s.mir.epoch .B) → s.amb + r < q
  hidx_le : ∀ Q, s.mir.idx Q + r ≤ q
  hhon_len : s.honest.length + r ≤ q
  hep_le : ∀ Q, s.mir.epoch Q ≤ qep
  hep_adj : ∀ Q, (inReceiveOnlyEpoch s.mir Q = true → s.mir.epoch Q ≤ s.mir.epoch Q.other) ∧
    s.mir.epoch Q ≤ s.mir.epoch Q.other + 1
  hst_R : ∀ Q,
    s_R.st Q = expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s Q (s_fig8.st Q) (ec Q)
  hst_id : ∀ Q, (s_fig8.st Q).id = Q
  htcur : ∀ Q, (s_fig8.st Q).tcur = s.mir.epoch Q
  hepExp0 : epExp 0 = x₀
  hspur : ∀ Q, ∃ rk_base T_base,
    (inReceiveOnlyEpoch s.mir Q = true →
      (s_fig8.st Q).root = rk_base ∧
      (s_fig8.st Q).γ = .pub T_base ∧
      T_base ≠ 0 ∧
      epExp (s.mir.epoch Q + 1) = ec Q) ∧
    (inReceiveOnlyEpoch s.mir Q = false →
      (s_fig8.st Q).γ = .exp (epExp (s.mir.epoch Q)) ∧
      (0 < s.mir.epoch Q →
        (s_fig8.st Q).root =
          (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s.mir.epoch Q)) T_base))).1 ∧
        (s_fig8.st Q).curCkaMsg = some (Dh.dh (epExp (s.mir.epoch Q)) Dh.base)) ∧
      ∃ vS, (s_fig8.st Q).vS = some vS ∧ vS.lastIndex = s.mir.idx Q)
  hchainsA : ChainsEpochInvA (s.mir.epoch .A) (s.chains .A)
  hchainsA_ep : (s.chains .A).map (·.epoch) = epListA (s.mir.epoch .A / 2)
  hchainsB_ep : (s.chains .B).map (·.epoch) = epListB ((s.mir.epoch .B + 1) / 2)
  hchainsB_none : ∀ g ∈ s.chains .B, g.key.isNone = false
  hcorrB0 : (.B, 0) ∈ s.mir.corrs → ∀ g ∈ s.chains .A, g.key.isNone = false
  hchains_sync : ∀ Q g, g ∈ s.chains Q →
    g.epoch ≤ s.mir.epoch Q ∧
    Q.sendsIn g.epoch = false ∧
    (if g.key.isNone then some (encT (Dh.dh x₀ Dh.base)) else g.key) =
      some (encT (Dh.dh (epExp g.epoch) Dh.base)) ∧
    ∃ v, (s_fig8.st Q).vR g.epoch = some v ∧ ChainSync g v
  hhon : ∀ wc ∈ s.honest,
    HonestEntryInvC P Inv Dh encT epExp wc ∧
    wc.2.1.1 ≤ max (s.mir.epoch .A) (s.mir.epoch .B) ∧
    (CryptoGames.Party.senderOf wc.2.1.1).sendsIn wc.2.1.1 = true ∧
    wc.2.1.1 ≤ s.mir.epoch (CryptoGames.Party.senderOf wc.2.1.1)
  htrans_hon : ∀ rec_f ∈ s_fig8.trans,
    (CryptoGames.Ratchet.LibsignalSim.toWire rec_f.ct, rec_f.ct) ∈ s.honest ∧
    rec_f.pos.sender = CryptoGames.Party.senderOf rec_f.ct.1.1 ∧
    rec_f.pos.epoch = rec_f.ct.1.1 ∧
    rec_f.pos.idx = rec_f.ct.2.1
  hcoll : ∀ t₁ t₂,
    t₁ ≤ max (s.mir.epoch .A) (s.mir.epoch .B) →
    t₂ ≤ max (s.mir.epoch .A) (s.mir.epoch .B) →
    Dh.dh (epExp t₁) Dh.base = Dh.dh (epExp t₂) Dh.base → t₁ = t₂
  hpqInv : ∀ Q, Inv (s.pq Q)

/-- Extended lazy-coin refinement invariant on `LibsignalToModularSchemeSimState`. -/
structure SimInvCXLazy {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (x₀ : BitVec 256)
    (s_R : CryptoGames.SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool)
    (epExp : ℕ → BitVec 256) : Prop where
  hsim : SimInvCLazy P (InvB Inv q r) ℓ Dh encPt encT qep q r x₀ s_R sC.base s_fig8 ec winBefore
    epExp
  huniq : PosUniq sC.base
  hkept : KeptInv P Dh encPt encT idOf lam sC s_fig8
  hidx : HonestIdxLe sC.base
  hsync : EpochSync P Dh encPt encT idOf sC.base.honest sC.sent sC.snaps s_fig8 epExp

omit [DecidableEq Pt] [SampleableType Pt] in
theorem simInvCXLazy_mono_r
    {P : Params (List (BitVec 8)) (BitVec 512)}
    {Inv : ℕ → List (BitVec 8) → Prop} {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r r' : ℕ} {x₀ : BitVec 256}
    {s_R : CryptoGames.SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8))}
    {sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {s_fig8 : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (h : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hr : r' ≤ r) :
    SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R sC s_fig8 ec winBefore epExp := by
  refine ⟨?_, h.huniq, h.hkept, h.hidx, h.hsync⟩
  have hsim := h.hsim
  exact
    { hsim with
      hamb := by have := hsim.hamb; omega
      hamb_strict := fun hpos => by have := hsim.hamb_strict hpos; omega
      hidx_le := fun Q => by have := hsim.hidx_le Q; omega
      hhon_len := by have := hsim.hhon_len; omega
      hhon := hsim.hhon
      hpqInv := fun Q => CryptoGames.LibsignalSM.Proofs.Refinement.InvB.mono hr (hsim.hpqInv Q) }

/-- Validity of the prior-accept SPQR witness `w_acc` at party `Q`. -/
@[expose] def ValidEvictAccWitness
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) {ℓ : ℕ}
    (s : SimState (List (BitVec 8)) Pt ℓ) (Q : Party)
    (w_acc : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F) : Prop :=
  1 ≤ CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir Q →
    ∃ w_acc_wire c_acc h_acc body_acc pq_acc pq_acc' salt_acc,
      (w_acc_wire, c_acc) ∈ s.honest ∧
      c_acc.1.1 = CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir Q ∧
      CryptoGames.Party.senderOf c_acc.1.1 = Q.other ∧
      (signalWireCodec P.codec).parse (w_acc_wire.take (w_acc_wire.length - 8)) =
        some (h_acc, body_acc) ∧
      CryptoVerification.SpqrV1Sync.SendTotal.TopStateW P.C.F K pq_acc w_acc ∧
      (spqrV1SessionUniformCoins P.C.F K).recv pq_acc h_acc.pqRatchet = .ok (pq_acc', salt_acc) ∧
      CryptoGames.LibsignalSM.Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) pq_acc (s.pq Q)

/-- Validity of the base root key and ratchet key witness `(rk_base, T_base)` at party `Q`. -/
@[expose] def ValidSpurBase {PQ PQC : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (epExp : ℕ → BitVec 256)
    (Q : Party) (rk_base : CryptoGames.Ratchet.RootKey) (T_base : Pt) : Prop :=
  (inReceiveOnlyEpoch s.mir Q = true →
    (s_fig8.st Q).root = rk_base ∧
    (s_fig8.st Q).γ = .pub T_base ∧
    T_base ≠ 0) ∧
  (inReceiveOnlyEpoch s.mir Q = false →
    (s_fig8.st Q).γ = .exp (epExp (s.mir.epoch Q)) ∧
    (0 < s.mir.epoch Q →
      (s_fig8.st Q).root =
        (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s.mir.epoch Q)) T_base))).1 ∧
      (s_fig8.st Q).curCkaMsg = some (Dh.dh (epExp (s.mir.epoch Q)) Dh.base)) ∧
    ∃ vS, (s_fig8.st Q).vS = some vS ∧ vS.lastIndex = s.mir.idx Q)

/-- Lazy-coin refinement invariant excluding spurious keys on evicted wires. -/
@[expose] def EvictedSpurSimInvLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  ∃ x₀ s_R ec winBefore epExp,
    SimInvCXLazy P InvPQ ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { g with win := false } ec winBefore epExp ∧
    ∀ Q, ∃ w_acc rk_base T_base,
      ValidEvictAccWitness P K sC.base Q w_acc ∧
      ValidSpurBase P ℓ Dh encPt sC.base { g with win := false } epExp Q rk_base T_base ∧
      (inReceiveOnlyEpoch sC.base.mir Q = false →
        spurBadList P encPt Dh Q rk_base T_base
          (CryptoGames.LibsignalSM.Proofs.Refinement.evictedSpurCandList P epExp w_acc
            (CryptoGames.LibsignalSM.Proofs.Refinement.honestBeforeEpoch sC.base.honest
              (CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch sC.base.mir Q)))
          (epExp (sC.base.mir.epoch Q)) = false)

/-- Combined game-level and lazy-coin refinement invariant for `kemFailSimImpl`. -/
@[expose] def EvictedSpurHistSimInvLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r w_rem : ℕ)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  EvictedSpurHistGameInv P K qep w_rem sC ∧
  EvictedSpurSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r sC g

omit [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurSimInvLazy_mono_r
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem}
    {Inv : ℕ → List (BitVec 8) → Prop} {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r r' : ℕ}
    {sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (h : EvictedSpurSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r sC g)
    (hr : r' ≤ r) :
    EvictedSpurSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r' sC g := by
  rcases h with ⟨x₀, s_R, ec, winBefore, epExp, hsim, hno_spur⟩
  exact ⟨x₀, s_R, ec, winBefore, epExp, simInvCXLazy_mono_r hsim hr, hno_spur⟩

omit [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistSimInvLazy_mono_r
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem}
    {Inv : ℕ → List (BitVec 8) → Prop} {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r r' w_rem : ℕ}
    {sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (h : EvictedSpurHistSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r w_rem sC g)
    (hr : r' ≤ r) :
    EvictedSpurHistSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r' w_rem sC g :=
  ⟨h.1, evictedSpurSimInvLazy_mono_r h.2 hr⟩

omit [DecidableEq Pt] [SampleableType Pt] in
theorem mem_chains_evictAccEpoch_of_simInvCLazy {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    {P : Params PQ PQC} {Inv : PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r : ℕ}
    {x₀ : BitVec 256}
    {s_R : CryptoGames.SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hsim : SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (hge : 1 ≤ CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir Q) :
    CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir Q ∈ (s.chains Q).map (·.epoch) := by
  unfold CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch at hge ⊢
  cases hinw : inReceiveOnlyEpoch s.mir Q <;> rw [hinw] at hge
  · simp only [Bool.false_eq_true, ↓reduceIte] at hge ⊢
    have hQ_sends : Q.sendsIn (s.mir.epoch Q) = true := by simpa [inReceiveOnlyEpoch] using hinw
    have hrecv_pred : Q.sendsIn (s.mir.epoch Q - 1) = false := by
      cases Q <;> simp [CryptoGames.Party.sendsIn] at hQ_sends ⊢ <;> omega
    exact mem_chains_epoch_of_adj Q (s.mir.epoch Q) (s.mir.epoch Q - 1) (s.chains Q)
      (fun hA => hA ▸ hsim.hchainsA_ep) (fun hB => hB ▸ hsim.hchainsB_ep)
      (by omega) (by omega) (by omega) hrecv_pred
  · simp only [↓reduceIte] at hge ⊢
    have hrecv_cur : Q.sendsIn (s.mir.epoch Q) = false := by simpa [inReceiveOnlyEpoch] using hinw
    exact mem_chains_epoch_of_adj Q (s.mir.epoch Q) (s.mir.epoch Q) (s.chains Q)
      (fun hA => hA ▸ hsim.hchainsA_ep) (fun hB => hB ▸ hsim.hchainsB_ep)
      (by omega) (by omega) (by omega) hrecv_cur

theorem not_mem_chains_epoch_of_findIdx_noneCLazy {PQ PQC : Type}
    [Inhabited PQ] [SampleableType PQC]
    {P : Params PQ PQC} {Inv : PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r : ℕ}
    {x₀ : BitVec 256}
    {s_R : CryptoGames.SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hsim : SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt) (h : SignalHeader) (body : List (BitVec 8))
    (hc_mem : (w, c) ∈ s.honest)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hfind : (s.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) = none) :
    c.1.1 ∉ (s.chains Q).map (·.epoch) := by
  rcases hsim.hhon (w, c) hc_mem with ⟨hc_inv, _, _, _⟩
  have hc_ge1 : 1 ≤ c.1.1 := hc_inv.2.2.1
  rcases CryptoGames.LibsignalSM.Proofs.Refinement.honestEntryInvC_eq_raw P Inv Dh encT epExp hc_inv hparse with
    ⟨_, hsrk, _, _⟩
  intro hmem_ep
  rcases List.mem_map.mp hmem_ep with ⟨g₀, hg₀, hep_eq⟩
  have hnone : g₀.key.isNone = false := by
    cases Q with
    | A =>
      cases hn : g₀.key.isNone
      · rfl
      · have h0 := hsim.hchainsA.1 g₀ hg₀ hn
        omega
    | B => exact hsim.hchainsB_none g₀ hg₀
  have hkey_sync := (hsim.hchains_sync Q g₀ hg₀).2.2.1
  simp only [hnone, Bool.false_eq_true, ↓reduceIte, hep_eq, ← hsrk] at hkey_sync
  have hnone_iff := List.findIdx?_eq_none_iff.mp hfind g₀ hg₀
  simp [hkey_sync] at hnone_iff

theorem mem_honestBeforeEpoch_of_evicted_simInvCLazy {PQ PQC : Type}
    [Inhabited PQ] [SampleableType PQC]
    {P : Params PQ PQC} {Inv : PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r : ℕ}
    {x₀ : BitVec 256}
    {s_R : CryptoGames.SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hsim : SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (hinw : inReceiveOnlyEpoch s.mir Q = false)
    (w : List (BitVec 8)) (c : Fig8C Pt) (h : SignalHeader) (body : List (BitVec 8))
    (hc_mem : (w, c) ∈ s.honest)
    (hc_sender : CryptoGames.Party.senderOf c.1.1 = Q.other)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hfind : (s.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 ≠ s.mir.epoch Q + 1) :
    1 < s.mir.epoch Q ∧
      s.mir.epoch Q - 1 = CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir Q ∧
      (w, c) ∈ CryptoGames.LibsignalSM.Proofs.Refinement.honestBeforeEpoch s.honest
        (CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir Q) := by
  have hc_not_mem := not_mem_chains_epoch_of_findIdx_noneCLazy hsim Q w c h body hc_mem hparse hfind
  rcases hsim.hhon (w, c) hc_mem with ⟨hc_inv, _, hc_sends, hc_le_sender⟩
  have hc_ge1 : 1 ≤ c.1.1 := hc_inv.2.2.1
  rw [hc_sender] at hc_sends hc_le_sender
  dsimp only at hc_sends hc_le_sender
  have hadj_other : s.mir.epoch Q.other ≤ s.mir.epoch Q + 1 := by
    have hadj := (hsim.hep_adj Q.other).2
    rwa [CryptoGames.Party.other_other] at hadj
  have hc_le_Q : c.1.1 ≤ s.mir.epoch Q := by omega
  have hQ_sends : Q.sendsIn (s.mir.epoch Q) = true := by simpa [inReceiveOnlyEpoch] using hinw
  have hc_recv_Q : Q.sendsIn c.1.1 = false := by
    have h := c7_sendsIn_other_false_of_sendsIn hc_sends
    rwa [CryptoGames.Party.other_other] at h
  have hc_ne_Q : c.1.1 ≠ s.mir.epoch Q := by
    intro heq; rw [heq, hQ_sends] at hc_recv_Q; cases hc_recv_Q
  have hc_ne_pred : c.1.1 ≠ s.mir.epoch Q - 1 := by
    intro heq
    have hmem := mem_chains_epoch_of_adj Q (s.mir.epoch Q) c.1.1 (s.chains Q)
      (fun hA => hA ▸ hsim.hchainsA_ep) (fun hB => hB ▸ hsim.hchainsB_ep)
      hc_ge1 hc_le_Q (by omega) hc_recv_Q
    exact hc_not_mem hmem
  have hlt : c.1.1 < s.mir.epoch Q - 1 := by omega
  have hgt1 : 1 < s.mir.epoch Q := by omega
  have hev_eq : s.mir.epoch Q - 1 = CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch s.mir Q := by
    simp [CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch, hinw]
  exact ⟨hgt1, hev_eq, List.mem_filter.mpr ⟨hc_mem, decide_eq_true (hev_eq ▸ hlt)⟩⟩

omit [SampleableType Pt] in
theorem lFig8_receive_evictedProbeRecord_isSome_eq_deliverForgeEvent_lazy
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : CryptoGames.SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (Q : Party) (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (salt : Salt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hbound : ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1)) :
    ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (CryptoGames.LibsignalSM.Proofs.Refinement.evictedProbeRecord sC Q Dh epExp c w h salt)).isSome =
      CryptoGames.LibsignalSM.Proofs.Refinement.EvictedDeliverForgeEvent P Dh encPt encT idOf sC s_fig8 Q epExp c w h
        salt := by
  have hsim := hinv.hsim
  have hst_id : (s_fig8.st Q).id = Q := hsim.hst_id Q
  have htcur : (s_fig8.st Q).tcur = sC.base.mir.epoch Q := hsim.htcur Q
  have hQ_recv : Q.sendsIn (sC.base.mir.epoch Q + 1) = false :=
    CryptoGames.LibsignalSM.Proofs.Refinement.sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
  rcases hsim.hspur Q with ⟨_, _, _, hspur_notinw⟩
  rcases hspur_notinw hinw with ⟨hγ_Q, _, _⟩
  let p₁ := (rootPRNG P.C.F encPt).up (s_fig8.st Q).root
    (Dh.dh (epExp (sC.base.mir.epoch Q)) (Dh.dh (epExp c.1.1) Dh.base))
  let sk := CryptoGames.FSAEAD.skipKeys (lChainPRG P.C.F) h.counter.toNat p₁.2 0 []
  let v' : CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) :=
    ⟨((lChainPRG P.C.F h.counter.toNat).gen sk.1).1, h.counter.toNat + 1, sk.2⟩
  have heq :
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
        (CryptoGames.LibsignalSM.Proofs.Refinement.evictedProbeRecord sC Q Dh epExp c w h salt) =
      (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (CryptoGames.LibsignalSM.Proofs.Refinement.evictedMessageKey P encPt sC s_fig8 Q Dh epExp c h)
        (h.counter.toNat + 1, (sC.base.mir.epoch Q + 1, some (Dh.dh (epExp c.1.1) Dh.base)))
        ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)).map
        (fun pm =>
          ({ (s_fig8.st Q) with
              root := p₁.1,
              vR := Function.update (s_fig8.st Q).vR (sC.base.mir.epoch Q + 1) (some v'),
              γ := .pub (Dh.dh (epExp c.1.1) Dh.base),
              tcur := sC.base.mir.epoch Q + 1 },
            sC.base.mir.epoch Q + 1, h.counter.toNat + 1, pm)) := by
    unfold lFig8 CryptoGames.SM.Construction.scheme CryptoGames.SM.Construction.receive lFS dhScheme
      CryptoGames.LibsignalSM.Proofs.Refinement.evictedProbeRecord CryptoGames.LibsignalSM.Proofs.Refinement.evictedMessageKey
      CryptoGames.LibsignalSM.Proofs.Refinement.evictedEpochStep CryptoGames.LibsignalSM.Proofs.Refinement.evictedEpochSeed
    dsimp only
    rw [htcur]
    have hcond1 :
        ((s_fig8.st Q).id.sendsIn (sC.base.mir.epoch Q + 1) ||
          decide (sC.base.mir.epoch Q + 1 < sC.base.mir.epoch Q + 1)) = false := by
      rw [hst_id, hQ_recv]; simp
    simp only [hcond1, Bool.false_eq_true, ↓reduceIte, hγ_Q, Function.update_self]
    unfold CryptoGames.FSAEAD.fromAEADPRG
    dsimp only
    have hlk : ([] : List (ℕ × BitVec 256)).lookup (h.counter.toNat + 1) = none := rfl
    have hcond_false :
        ¬ (h.counter.toNat + 1 ≤ 0 ∨ 25000 < h.counter.toNat + 1 - 0 - 1) := by
      intro hbad
      rcases hbad with hle | hgt
      · omega
      · exact hbound (Or.inl (by omega))
    have hsub1 : h.counter.toNat + 1 - 0 - 1 = h.counter.toNat := by omega
    have hsub2 : h.counter.toNat + 1 - 1 = h.counter.toNat := by omega
    rw [hlk, ite_eq_right hcond_false, hsub1, hsub2]
    cases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        ((lChainPRG P.C.F h.counter.toNat).gen
          (CryptoGames.FSAEAD.skipKeys (lChainPRG P.C.F) h.counter.toNat
            ((rootPRNG P.C.F encPt).up (s_fig8.st Q).root
              (Dh.dh (epExp (sC.base.mir.epoch Q)) (Dh.dh (epExp c.1.1) Dh.base))).2 0 []).1).2
        (h.counter.toNat + 1, (sC.base.mir.epoch Q + 1, some (Dh.dh (epExp c.1.1) Dh.base)))
        ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) with
    | none => rfl
    | some pm => simp [Function.update_idem, v', sk, p₁]
  rw [heq]
  unfold CryptoGames.LibsignalSM.Proofs.Refinement.EvictedDeliverForgeEvent
  exact Option.isSome_map

/-- `EvictedSpurHistSimInvLazy` implies `EvictedOnlyNoForgeAt` at every party. -/
theorem evictedOnlyNoForgeAt_of_evictedSpurHistSimInvLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    {InvPQ : ℕ → List (BitVec 8) → Prop}
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hdec : ∀ T, decT (encT T) = some T) (lam : Pt)
    {qep q r w_rem : ℕ}
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party)
    (hInv : EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g) :
    EvictedOnlyNoForgeAt P decT (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) sC g Q := by
  obtain ⟨x₀, s_R, ec, winBefore, epExp, hinv, hspur_lazy⟩ := hInv.2
  obtain ⟨w_acc, rk_base, T_base, hw_acc_valid, hbase_valid, hno_spur⟩ := hspur_lazy Q
  have ⟨n_top, _, hI_top⟩ : ∃ n, n + r ≤ q ∧ InvPQ n (sC.base.pq Q) := hinv.hsim.hpqInv Q
  obtain ⟨w_top, hw_top⟩ := hInv_top n_top _ hI_top
  intro w c h body pq' salt hmem hsender hparse hrecv hfind hepoch hinw hbound _ T hT
  rcases hinv.hsim.hhon (w, c) hmem with ⟨hhon_c, _, _, _⟩
  rcases CryptoGames.LibsignalSM.Proofs.Refinement.honestEntryInvC_eq_raw P (CryptoGames.LibsignalSM.Proofs.Refinement.InvB InvPQ q r) Dh encT
    epExp hhon_c hparse with ⟨_, hsrk, _, _⟩
  rw [hsrk, hdec] at hT
  injection hT with hT_eq
  subst hT_eq
  rw [hspqr_eq] at hrecv
  obtain ⟨hgt1, hev_eq, hc_before⟩ :=
    mem_honestBeforeEpoch_of_evicted_simInvCLazy hinv.hsim Q hinw w c h body hmem hsender hparse
      hfind hepoch
  have hact : 1 ≤ CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch sC.base.mir Q := by omega
  obtain ⟨w_acc_wire, c_acc, h_acc, body_acc, pq_acc, pq_acc', salt_acc,
      hc_acc_mem, hc_acc_eq, hc_acc_sender, hparse_acc, hw_acc, hrecv_acc, hreach₀⟩ :=
    hw_acc_valid hact
  have hlt_ev : c.1.1 < CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch sC.base.mir Q :=
    of_decide_eq_true (List.mem_filter.mp hc_before).2
  have hlt_acc : c.1.1 < c_acc.1.1 := by omega
  obtain ⟨pq_s₀, pq_s₀', pq_s₁, pq_s₁', r₀, r₁, salt₀, salt₁, w_s₀,
      hw_s₀, hsend₀, hreach_s, hsend₁⟩ :=
    hInv.1.hhist.hhon_ord w c h body w_acc_wire c_acc h_acc body_acc hmem hc_acc_mem
      (hsender.trans hc_acc_sender.symm) hlt_acc hparse hparse_acc
  obtain ⟨pre, pre_acc, hpre, hpre_acc, hle_acc⟩ :=
    CryptoGames.LibsignalSM.Proofs.Refinement.spqrV1_sender_reachFrom_msgChainEpoch_le P.C.F K hw_s₀ hsend₀ hreach_s hsend₁
  obtain ⟨-, -, hsalt_acc⟩ :=
    CryptoGames.LibsignalSM.Proofs.Refinement.spqrV1_prior_accept_reachFrom_recv_salt_eq P.C.F K hw_acc hw_top hrecv_acc
      hpre_acc hpre hle_acc hreach₀ (.refl _) hrecv
  have hmem_cand := CryptoGames.LibsignalSM.Proofs.Refinement.mem_evictedSpurCandList_of_honest P epExp epExp w_acc
    (CryptoGames.LibsignalSM.Proofs.Refinement.honestBeforeEpoch sC.base.honest
      (CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch sC.base.mir Q))
    w c h body hc_before hparse rfl
  rw [← hsalt_acc] at hmem_cand
  have hrk : ({ g with win := false }.st Q).root =
      (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (sC.base.mir.epoch Q)) T_base))).1 :=
    ((hbase_valid.2 hinw).2.1 (by omega)).1
  have hisSome := lFig8_receive_evictedProbeRecord_isSome_eq_deliverForgeEvent_lazy
    P InvPQ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false } ec winBefore epExp
    hinv Q c w h salt hinw hbound
  cases hev : CryptoGames.LibsignalSM.Proofs.Refinement.EvictedDeliverForgeEvent P Dh encPt encT idOf sC
      { g with win := false } Q epExp c w h salt
  · rw [hev] at hisSome
    exact Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp hisSome)
  · have hsingle := CryptoGames.LibsignalSM.Proofs.Refinement.evictedDeliverForgeEvent_implies_spurBadSingle P Dh encPt
      encT idOf hid sC { g with win := false } Q epExp c w h body salt rk_base T_base hinw hrk
      hparse (CryptoGames.LibsignalSM.Proofs.Refinement.honestEntryInvC_len_lt hhon_c) hev
    have hbad : spurBadList P encPt Dh Q rk_base T_base
        (CryptoGames.LibsignalSM.Proofs.Refinement.evictedSpurCandList P epExp w_acc
          (CryptoGames.LibsignalSM.Proofs.Refinement.honestBeforeEpoch sC.base.honest
            (CryptoGames.LibsignalSM.Proofs.Refinement.evictAccEpoch sC.base.mir Q)))
        (epExp (sC.base.mir.epoch Q)) = true :=
      List.any_eq_true.mpr ⟨(w, salt, epExp c.1.1), hmem_cand, hsingle⟩
    rw [hno_spur hinw] at hbad
    cases hbad

end CorrSimInvCX

end KemFailSimCoupling

end CryptoVerification.LibsignalSession.HeadlineV1

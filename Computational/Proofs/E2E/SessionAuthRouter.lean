/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import ToMathlib.MeasureTheory.Measure.Bool

/-!
# Session router: forward one session, simulate the rest

A multi-session adversary talks to countably many copies of one oracle interface `spec`, tagged by
a session number, plus uniform coins. This file proves the generic hybrid over sessions used in
the linear multi-session MAC bound, independent of what a session is.

* `hybSess implL implR j` answers session `s < j` with `implR` and every other session with `implL`,
  each session on its own state.
* `sessAdv implL implR M k` is the single-session adversary obtained from the multi-session
  adversary `M` by forwarding session `k` to an external `spec` oracle and simulating every other
  session itself (`implR` below `k`, `implL` above).
* `sessAdv_left_eq` / `sessAdv_right_eq`: run against `implL` (respectively `implR`), the adversary
  `sessAdv … k` behaves exactly as hybrid `k` (respectively `k + 1`).
* `sessLift_boolDist_le`: if `M` only uses sessions `< q`, the distance between "every session runs
  `implL`" and "every session runs `implR`" is at most the sum over `k < q` of the distance between
  `sessAdv … k` against `implL` and against `implR`.

In the libsignal instance, a session is one FS-AEAD instance, and `implL`/`implR` are the two ends of
one per-session hop (for example the real and the slot-salt world). The per-session adversaries
`D j` and `E j` of `SessionHybrid.sessionHybrid_mix_le` are built from `sessAdv`.-/

set_option linter.unusedSectionVars false

public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed.SessionRouter

variable {ι : Type} {spec : OracleSpec ι}

/-! ## Interfaces -/

/-- Countably many copies of `spec`, tagged by a session number. -/
abbrev multiSessSpec (spec : OracleSpec ι) : OracleSpec ((_ : ℕ) × ι) :=
  OracleSpec.sigma fun _ : ℕ => spec

/-- Lift a per-session implementation to the single-session interface `unifSpec + spec`, passing the
uniform coins through. -/
@[expose] def fwd {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl (unifSpec + spec) (StateT σ ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + impl

@[simp] theorem fwd_inl {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) (n : ℕ) :
    fwd impl (.inl n) =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) n := rfl

@[simp] theorem fwd_inr {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) (t : ι) :
    fwd impl (.inr t) = impl t := rfl

/-- Running a lifted coin computation against `fwd impl` leaves the state unchanged. -/
theorem fwd_liftM_run {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) {β : Type}
    (p : ProbComp β) (s : σ) :
    (simulateQ (fwd impl) (liftM p : OracleComp (unifSpec + spec) β)).run s =
      (fun a => (a, s)) <$> p := by
  simp [fwd, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

/-! ## The hybrid over sessions -/

section Hybrid

variable {σL σR : Type}

/-- Session part of hybrid `j`: session `s < j` runs `implR` on its right state, every other session
runs `implL` on its left state. -/
@[expose] def hybSessCore (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) (j : ℕ) :
    QueryImpl (multiSessSpec spec) (StateT ((ℕ → σL) × (ℕ → σR)) ProbComp) := fun t =>
  if t.1 < j then
    StateT.mk fun s => (fun r => (r.1, (s.1, Function.update s.2 t.1 r.2))) <$>
      (implR t.2).run (s.2 t.1)
  else
    StateT.mk fun s => (fun r => (r.1, (Function.update s.1 t.1 r.2, s.2))) <$>
      (implL t.2).run (s.1 t.1)

/-- Hybrid `j` over sessions, with uniform coins passed through. -/
@[expose] def hybSess (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) (j : ℕ) :
    QueryImpl (unifSpec + multiSessSpec spec) (StateT ((ℕ → σL) × (ℕ → σR)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT ((ℕ → σL) × (ℕ → σR)) ProbComp)
    + hybSessCore implL implR j

@[simp] theorem hybSess_inl (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) (j n : ℕ) :
    hybSess implL implR j (.inl n) =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT ((ℕ → σL) × (ℕ → σR)) ProbComp) n := rfl

@[simp] theorem hybSess_inr (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) (j : ℕ) (t : (_ : ℕ) × ι) :
    hybSess implL implR j (.inr t) = hybSessCore implL implR j t := rfl

/-- The router for session `k`. Coins and session `k` go to the external `unifSpec + spec`
oracle; session `s < k` runs `implR` and session `s > k` runs `implL`, on internal state. -/
@[expose] def sessRedImpl (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) (k : ℕ) :
    QueryImpl (unifSpec + multiSessSpec spec)
      (StateT ((ℕ → σL) × (ℕ → σR)) (OracleComp (unifSpec + spec)))
  | .inl n => StateT.lift (liftM (OracleSpec.query (spec := unifSpec + spec) (.inl n)))
  | .inr t =>
    if t.1 = k then
      StateT.lift (liftM (OracleSpec.query (spec := unifSpec + spec) (.inr t.2)))
    else if t.1 < k then
      StateT.mk fun s => liftM ((fun r => (r.1, (s.1, Function.update s.2 t.1 r.2))) <$>
        (implR t.2).run (s.2 t.1))
    else
      StateT.mk fun s => liftM ((fun r => (r.1, (Function.update s.1 t.1 r.2, s.2))) <$>
        (implL t.2).run (s.1 t.1))

/-- The single-session adversary for session `k`: run the multi-session adversary `M`, forward
session `k`, and simulate all other sessions from the initial states `sL`, `sR`. -/
@[expose] def sessAdv (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) {α : Type}
    (M : OracleComp (unifSpec + multiSessSpec spec) α) (sL : ℕ → σL) (sR : ℕ → σR) (k : ℕ) :
    OracleComp (unifSpec + spec) α :=
  Prod.fst <$> (simulateQ (sessRedImpl implL implR k) M).run (sL, sR)

/-- Left step. Running the router for session `k` against `implL` (from external state `sx`)
is hybrid `k` with session `k`'s left state set to `sx`. -/
theorem sessRed_step_left (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) (k : ℕ) {α : Type}
    (oa : OracleComp (unifSpec + multiSessSpec spec) α)
    (sL : ℕ → σL) (sR : ℕ → σR) (sx : σL) :
    (fun z => (z.1.1, (Function.update z.1.2.1 k z.2, z.1.2.2))) <$>
      (simulateQ (fwd implL) ((simulateQ (sessRedImpl implL implR k) oa).run (sL, sR))).run sx =
    (simulateQ (hybSess implL implR k) oa).run (Function.update sL k sx, sR) := by
  induction oa using OracleComp.inductionOn generalizing sL sR sx with
  | pure a => simp
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | ⟨s, t⟩
    · -- coins
      simp only [add_apply_inl, sessRedImpl, StateT.run_lift, bind_pure_comp, simulateQ_map,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, fwd_inl,
        QueryImpl.ofLift_eq_id', PFunctor.Handler.liftTarget_apply, PFunctor.selfMonomial_B,
        QueryImpl.id'_apply, id_map, StateT.run_map, StateT.run_monadLift, monadLift_self,
        Functor.map_map, bind_map_left, hybSess_inl]
      exact bind_congr fun u => ih u sL sR sx
    · by_cases heq : s = k
      · -- the forwarded session
        subst heq
        simp only [add_apply_inr, sigma_apply, sessRedImpl, ↓reduceIte, StateT.run_lift,
          bind_pure_comp, simulateQ_map, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, fwd_inr, id_map, StateT.run_map, bind_map_left, hybSess_inr,
          hybSessCore, lt_self_iff_false, StateT.run_mk, Function.update_idem,
          Function.update_self]
        exact bind_congr fun a => ih a.1 sL sR a.2
      · by_cases hlt : s < k
        · -- a session already moved to `implR`
          simp only [add_apply_inr, sigma_apply, sessRedImpl, heq, ↓reduceIte, hlt, liftM_map,
            StateT.run_mk, simulateQ_map, StateT.run_map, fwd_liftM_run, Functor.map_map,
            bind_map_left, hybSess_inr, hybSessCore]
          exact bind_congr fun a => ih a.1 sL (Function.update sR s a.2) sx
        · -- a session still on `implL`
          simp only [add_apply_inr, sigma_apply, sessRedImpl, heq, ↓reduceIte, hlt, liftM_map,
            StateT.run_mk, simulateQ_map, StateT.run_map, fwd_liftM_run, Functor.map_map,
            bind_map_left, hybSess_inr, hybSessCore, ne_eq, not_false_eq_true,
            Function.update_of_ne]
          refine bind_congr fun a => ?_
          rw [Function.update_comm (Ne.symm heq)]
          exact ih a.1 (Function.update sL s a.2) sR sx

/-- Right step. Running the router for session `k` against `implR` (from external state `sx`)
is hybrid `k + 1` with session `k`'s right state set to `sx`. -/
theorem sessRed_step_right (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) (k : ℕ) {α : Type}
    (oa : OracleComp (unifSpec + multiSessSpec spec) α)
    (sL : ℕ → σL) (sR : ℕ → σR) (sx : σR) :
    (fun z => (z.1.1, (z.1.2.1, Function.update z.1.2.2 k z.2))) <$>
      (simulateQ (fwd implR) ((simulateQ (sessRedImpl implL implR k) oa).run (sL, sR))).run sx =
    (simulateQ (hybSess implL implR (k + 1)) oa).run (sL, Function.update sR k sx) := by
  induction oa using OracleComp.inductionOn generalizing sL sR sx with
  | pure a => simp
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | ⟨s, t⟩
    · -- coins
      simp only [add_apply_inl, sessRedImpl, StateT.run_lift, bind_pure_comp, simulateQ_map,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, fwd_inl,
        QueryImpl.ofLift_eq_id', PFunctor.Handler.liftTarget_apply, PFunctor.selfMonomial_B,
        QueryImpl.id'_apply, id_map, StateT.run_map, StateT.run_monadLift, monadLift_self,
        Functor.map_map, bind_map_left, hybSess_inl]
      exact bind_congr fun u => ih u sL sR sx
    · by_cases heq : s = k
      · -- the forwarded session
        subst heq
        simp only [add_apply_inr, sigma_apply, sessRedImpl, ↓reduceIte, StateT.run_lift,
          bind_pure_comp, simulateQ_map, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, fwd_inr, id_map, StateT.run_map, bind_map_left, hybSess_inr,
          hybSessCore, lt_add_iff_pos_right, Order.lt_one_iff, StateT.run_mk,
          Function.update_idem, Function.update_self]
        exact bind_congr fun a => ih a.1 sL sR a.2
      · by_cases hlt : s < k
        · -- a session already moved to `implR`
          have hlt1 : s < k + 1 := by omega
          simp only [add_apply_inr, sigma_apply, sessRedImpl, heq, ↓reduceIte, hlt, liftM_map,
            StateT.run_mk, simulateQ_map, StateT.run_map, fwd_liftM_run, Functor.map_map,
            bind_map_left, hybSess_inr, hybSessCore, hlt1, ne_eq, not_false_eq_true,
            Function.update_of_ne]
          refine bind_congr fun a => ?_
          rw [Function.update_comm (Ne.symm heq)]
          exact ih a.1 sL (Function.update sR s a.2) sx
        · -- a session still on `implL`
          have hlt1 : ¬ s < k + 1 := by omega
          simp only [add_apply_inr, sigma_apply, sessRedImpl, heq, ↓reduceIte, hlt, liftM_map,
            StateT.run_mk, simulateQ_map, StateT.run_map, fwd_liftM_run, Functor.map_map,
            bind_map_left, hybSess_inr, hybSessCore, hlt1]
          exact bind_congr fun a => ih a.1 (Function.update sL s a.2) sR sx

/-- The session-`k` adversary against `implL`, started from session `k`'s own left state, is
hybrid `k`. -/
theorem sessAdv_left_eq (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) {α : Type}
    (M : OracleComp (unifSpec + multiSessSpec spec) α) (sL : ℕ → σL) (sR : ℕ → σR) (k : ℕ) :
    Prod.fst <$> (simulateQ (fwd implL) (sessAdv implL implR M sL sR k)).run (sL k) =
      Prod.fst <$> (simulateQ (hybSess implL implR k) M).run (sL, sR) := by
  have h := congrArg (fun x => Prod.fst <$> x) (sessRed_step_left implL implR k M sL sR (sL k))
  simp only [Function.update_eq_self, Functor.map_map] at h
  rw [← h, sessAdv, simulateQ_map, StateT.run_map, Functor.map_map]

/-- The session-`k` adversary against `implR`, started from session `k`'s own right state, is
hybrid `k + 1`. -/
theorem sessAdv_right_eq (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) {α : Type}
    (M : OracleComp (unifSpec + multiSessSpec spec) α) (sL : ℕ → σL) (sR : ℕ → σR) (k : ℕ) :
    Prod.fst <$> (simulateQ (fwd implR) (sessAdv implL implR M sL sR k)).run (sR k) =
      Prod.fst <$> (simulateQ (hybSess implL implR (k + 1)) M).run (sL, sR) := by
  have h := congrArg (fun x => Prod.fst <$> x) (sessRed_step_right implL implR k M sL sR (sR k))
  simp only [Function.update_eq_self, Functor.map_map] at h
  rw [← h, sessAdv, simulateQ_map, StateT.run_map, Functor.map_map]

end Hybrid

/-! ## The two ends of the hybrid -/

section Ends

variable {σ σL σR : Type}

/-- Session part of "every session runs its own copy of `impl`". -/
@[expose] def sessLiftCore (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl (multiSessSpec spec) (StateT (ℕ → σ) ProbComp) := fun t =>
  StateT.mk fun s => (fun r => (r.1, Function.update s t.1 r.2)) <$> (impl t.2).run (s t.1)

/-- Every session runs its own copy of `impl`, with uniform coins passed through. -/
@[expose] def sessLift (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl (unifSpec + multiSessSpec spec) (StateT (ℕ → σ) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (ℕ → σ) ProbComp) + sessLiftCore impl

@[simp] theorem sessLift_inl (impl : QueryImpl spec (StateT σ ProbComp)) (n : ℕ) :
    sessLift impl (.inl n) =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (ℕ → σ) ProbComp) n := rfl

@[simp] theorem sessLift_inr (impl : QueryImpl spec (StateT σ ProbComp)) (t : (_ : ℕ) × ι) :
    sessLift impl (.inr t) = sessLiftCore impl t := rfl

/-- Hybrid `0` is "every session runs `implL`". -/
theorem hybSess_zero (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) {α : Type}
    (oa : OracleComp (unifSpec + multiSessSpec spec) α) (sL : ℕ → σL) (sR : ℕ → σR) :
    (simulateQ (hybSess implL implR 0) oa).run (sL, sR) =
      (fun z => (z.1, (z.2, sR))) <$> (simulateQ (sessLift implL) oa).run sL := by
  induction oa using OracleComp.inductionOn generalizing sL sR with
  | pure a => simp
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | t
    · simp only [hybSess_inl, sessLift_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u sL sR
    · have hcond : ¬ t.1 < 0 := Nat.not_lt_zero _
      simp only [hybSess_inr, hybSessCore, sessLift_inr, sessLiftCore, hcond, ↓reduceIte,
        StateT.run_mk, bind_map_left]
      congr 1; ext z
      exact ih z.1 (Function.update sL t.1 z.2) sR

/-- Queries of the multi-session interface (`unifSpec + multiSessSpec spec`) addressed to a
session `≥ q`. -/
@[expose] def sessOffRange (q : ℕ) : ℕ ⊕ ((_ : ℕ) × ι) → Bool
  | .inl _ => false
  | .inr t => decide (q ≤ t.1)

/-- If `oa` only uses sessions `< q`, hybrid `q` is "every session runs `implR`". -/
theorem hybSess_eq_sessLift_of_offRange (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) (q : ℕ) {α : Type}
    (oa : OracleComp (unifSpec + multiSessSpec spec) α)
    (hoff : oa.IsQueryBoundP (fun t => sessOffRange q t = true) 0)
    (sL : ℕ → σL) (sR : ℕ → σR) :
    (simulateQ (hybSess implL implR q) oa).run (sL, sR) =
      (fun z => (z.1, (sL, z.2))) <$> (simulateQ (sessLift implR) oa).run sR := by
  induction oa using OracleComp.inductionOn generalizing sL sR with
  | pure a => simp
  | query_bind t r ih =>
    rw [isQueryBoundP_query_bind_iff] at hoff
    have hnp : ¬ (sessOffRange q t = true) := hoff.1.resolve_right (Nat.lt_irrefl 0)
    have hcont : ∀ u, (r u).IsQueryBoundP (fun t => sessOffRange q t = true) 0 :=
      fun u => by simpa [hnp] using hoff.2 u
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | t
    · simp only [hybSess_inl, sessLift_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u (hcont u) sL sR
    · have hcond : t.1 < q := by
        simp only [sessOffRange, decide_eq_true_eq, not_le] at hnp
        exact hnp
      simp only [hybSess_inr, hybSessCore, sessLift_inr, sessLiftCore, hcond, ↓reduceIte,
        StateT.run_mk, bind_map_left]
      congr 1; ext z
      exact ih z.1 (hcont z.1) sL (Function.update sR t.1 z.2)

end Ends

/-! ## Telescoping over sessions -/

section Telescope

variable {σL σR : Type}

/-- Session hybrid, generic form. If the multi-session adversary `M` only uses sessions `< q`,
then "every session runs `implL`" and "every session runs `implR`" are within the sum, over
`k < q`, of the distance between the session-`k` adversary `sessAdv … k` against `implL` and
against `implR`. Each summand is a single-session game started from session `k`'s own initial
states `sL k` and `sR k`. -/
theorem sessLift_boolDist_le (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) (q : ℕ)
    (M : OracleComp (unifSpec + multiSessSpec spec) Bool)
    (hoff : M.IsQueryBoundP (fun t => sessOffRange q t = true) 0)
    (sL : ℕ → σL) (sR : ℕ → σR) :
    𝒟[Prod.fst <$> (simulateQ (sessLift implL) M).run sL].boolDist
        𝒟[Prod.fst <$> (simulateQ (sessLift implR) M).run sR] ≤
      ∑ k ∈ Finset.range q,
        𝒟[Prod.fst <$> (simulateQ (fwd implL) (sessAdv implL implR M sL sR k)).run (sL k)].boolDist
          𝒟[Prod.fst <$> (simulateQ (fwd implR) (sessAdv implL implR M sL sR k)).run (sR k)] := by
  have h0 : Prod.fst <$> (simulateQ (sessLift implL) M).run sL =
      Prod.fst <$> (simulateQ (hybSess implL implR 0) M).run (sL, sR) := by
    rw [hybSess_zero, Functor.map_map]
  have hq : Prod.fst <$> (simulateQ (sessLift implR) M).run sR =
      Prod.fst <$> (simulateQ (hybSess implL implR q) M).run (sL, sR) := by
    rw [hybSess_eq_sessLift_of_offRange implL implR q M hoff, Functor.map_map]
  rw [h0, hq]
  refine (Measure.boolDist_le_sum_range
    (fun k => 𝒟[Prod.fst <$> (simulateQ (hybSess implL implR k) M).run (sL, sR)]) q).trans ?_
  refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
  rw [sessAdv_left_eq, sessAdv_right_eq]

end Telescope

end CryptoVerification.E2E.Signed.SessionRouter

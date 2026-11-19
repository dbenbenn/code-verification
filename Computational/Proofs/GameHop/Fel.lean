/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad

/-!
# Failure-Event Lemma, Supermartingale Potentials, and Union Bounds

Protocol-agnostic supermartingale potential bounds (`wp_simulateQ_pot_le`), the failure-event
lemma (`prEvent_bad_simulateQ_le_q_mul`), finite union bounds, and uniform index-guessing
reductions.
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.GameHop.Fel

open OracleSpec OracleComp
open scoped ENNReal
open MeasureTheory (Measure)
open OracleComp.ProgramLogic (wp wp_pure wp_bind wp_add wp_mono_of_support wp_le_const_of_support
  prEvent_eq_wp_indicator)

section PotentialSupermartingale

/-- Bounds expected final potential `V` by `V x + n * δ` when at most `n` charged queries each raise
expected `V` by at most `δ`. -/
theorem wp_simulateQ_pot_le {ι σ α : Type} {spec : OracleSpec.{0, 0} ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (charged : ι → Prop) [DecidablePred charged]
    (I : ℕ → σ → Prop) (V : σ → ℝ≥0∞) (δ : ℝ≥0∞)
    (hcharged : ∀ t n x, charged t → I (n + 1) x →
      (∀ z ∈ support ((impl t).run x), I n z.2) ∧
        wp ((impl t).run x) (fun z => V z.2) ≤ V x + δ)
    (hfree : ∀ t n x, ¬ charged t → I n x →
      (∀ z ∈ support ((impl t).run x), I n z.2) ∧
        wp ((impl t).run x) (fun z => V z.2) ≤ V x)
    (oa : OracleComp spec α) (n : ℕ) (hqb : oa.IsQueryBoundP charged n) (x : σ) (hx : I n x) :
    wp ((simulateQ impl oa).run x) (fun z => V z.2) ≤ V x + n * δ := by
  induction oa using OracleComp.inductionOn generalizing n x with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, wp_pure]
    exact le_self_add
  | query_bind t cont ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hqb
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      simulateQ_query_bind, StateT.run_bind, wp_bind]
    by_cases ht : charged t
    · rcases n with _ | m
      · exact absurd (hqb.1.resolve_left (not_not.mpr ht)) (Nat.not_lt_zero 0)
      · have hstep := hcharged t m x ht hx
        have hqb' : ∀ u, (cont u).IsQueryBoundP charged m := fun u => by
          simpa [ht] using hqb.2 u
        calc wp ((impl t).run x)
              (fun z => wp ((simulateQ impl (cont z.1)).run z.2) (fun w => V w.2))
            ≤ wp ((impl t).run x) (fun z => V z.2 + (m : ℝ≥0∞) * δ) := by
              refine wp_mono_of_support ((impl t).run x) fun z hz => ?_
              exact ih z.1 m (hqb' z.1) z.2 (hstep.1 z hz)
          _ = wp ((impl t).run x) (fun z => V z.2) + (m : ℝ≥0∞) * δ := by
              rw [wp_add]; simp
          _ ≤ (V x + δ) + (m : ℝ≥0∞) * δ := by gcongr; exact hstep.2
          _ = V x + ((m + 1 : ℕ) : ℝ≥0∞) * δ := by
              push_cast; ring
    · have hstep := hfree t n x ht hx
      have hqb' : ∀ u, (cont u).IsQueryBoundP charged n := fun u => by
        simpa [ht] using hqb.2 u
      calc wp ((impl t).run x)
            (fun z => wp ((simulateQ impl (cont z.1)).run z.2) (fun w => V w.2))
          ≤ wp ((impl t).run x) (fun z => V z.2 + (n : ℝ≥0∞) * δ) := by
            refine wp_mono_of_support ((impl t).run x) fun z hz => ?_
            exact ih z.1 n (hqb' z.1) z.2 (hstep.1 z hz)
        _ = wp ((impl t).run x) (fun z => V z.2) + (n : ℝ≥0∞) * δ := by
            rw [wp_add]; simp
        _ ≤ V x + (n : ℝ≥0∞) * δ := by gcongr; exact hstep.2

end PotentialSupermartingale

section UnionBoundsAndGuessing

theorem prEvent_exists_finset_le_sum {α ι : Type} (mx : ProbComp α) (S : Finset ι)
    (P : α → ι → Prop) :
    Pr{let a ← mx}[∃ i ∈ S, P a i] ≤ ∑ i ∈ S, Pr{let a ← mx}[P a i] :=
  prEvent_exists_finset_le S mx (fun i a => P a i)

theorem prEvent_exists_range_le_sum {α : Type} (mx : ProbComp α) (N : ℕ)
    (P : α → ℕ → Prop) :
    Pr{let a ← mx}[∃ i < N, P a i] ≤ ∑ i ∈ Finset.range N, Pr{let a ← mx}[P a i] := by
  have h := prEvent_exists_finset_le_sum mx (Finset.range N) P
  simpa only [Finset.mem_range] using h

theorem prEvent_any_list_le_sum {α β : Type} (mx : ProbComp α) (xs : List β)
    (p : α → β → Bool) :
    Pr{let a ← mx}[xs.any (p a) = true] ≤
      (xs.map fun x => Pr{let a ← mx}[p a x = true]).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.any_cons, Bool.or_eq_true, List.map_cons, List.sum_cons]
    exact (prEvent_or_le mx (fun a => p a x = true) (fun a => xs.any (p a) = true)).trans
      (add_le_add le_rfl ih)

end UnionBoundsAndGuessing

end Computational.Proofs.GameHop.Fel

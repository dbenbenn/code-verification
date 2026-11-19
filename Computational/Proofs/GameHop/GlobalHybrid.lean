/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.GameHop.Advantage
import Computational.Proofs.GameHop.Rnd
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Order.Disjoint
public import Mathlib.Order.SetNotation
public import PolyFun.Control.Monad.Support
public import VCVio.EvalDist.Defs.Measure.Core
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Multi-Instance Hybrids, Partition-Kill Hybrids, and Prefix Sandwiches

Protocol-agnostic multi-step `boolDist` and `boolBias` telescopes, partition-masking hybrids
(`gameKill`), and two-stage pause/resume prefix-sandwich reductions.
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.GameHop.GlobalHybrid

open OracleSpec OracleComp
open scoped ENNReal
open MeasureTheory (Measure)
open Computational.Proofs.GameHop.Rnd (evalDist_select_swap)
open Computational.Proofs.GameHop.Advantage (boolBias_le_add_two_mul_boolDist
  boolBias_le_two_mul_boolDist_of_eq_zero boolDist_le_of_select_eq
  boolDist_le_iSup_flip_of_beq_not_le evalDist_bind_mono_prob_of_support)

section StandardTelescope

end StandardTelescope

section PartitionKillHybrid

/-- Partition-kill hybrid replacing the output with `$ᵗ Bool` when `canon a ∈ S`, and running
`out a` otherwise. -/
def gameKill {α τ : Type} [DecidableEq τ] (run : ProbComp α) (canon : α → τ)
    (out : α → ProbComp Bool) (S : Finset τ) : ProbComp Bool := do
  let a ← run
  if canon a ∈ S then ($ᵗ Bool : ProbComp Bool)
  else out a

/-- Single-tag hybrid branch running `out a` when `canon a = t₀`, and `$ᵗ Bool` otherwise. -/
def gameOnlyTag {α τ : Type} [DecidableEq τ] (run : ProbComp α) (canon : α → τ)
    (out : α → ProbComp Bool) (t₀ : τ) : ProbComp Bool := do
  let a ← run
  if canon a = t₀ then out a
  else ($ᵗ Bool : ProbComp Bool)

@[simp]
theorem gameKill_empty {α τ : Type} [DecidableEq τ] (run : ProbComp α) (canon : α → τ)
    (out : α → ProbComp Bool) :
    gameKill run canon out ∅ = (run >>= out) := by
  simp [gameKill]

private theorem ite_bind_bool {m : Type → Type} [Monad m] {α β : Type} (c : Bool)
    (x : m α) (f g : α → m β) :
    (if c then x >>= f else x >>= g) = (x >>= fun a => if c then f a else g a) := by
  cases c <;> rfl

theorem evalDist_select_gameKill_insert {α τ : Type} [DecidableEq τ]
    (run : ProbComp α) (canon : α → τ) (out : α → ProbComp Bool)
    (S : Finset τ) (t₀ : τ) (ht₀ : t₀ ∉ S) :
    𝒟[do
        let sel ← ($ᵗ Bool : ProbComp Bool)
        if sel then gameKill run canon out S else ($ᵗ Bool : ProbComp Bool)] =
      𝒟[do
        let sel ← ($ᵗ Bool : ProbComp Bool)
        if sel then gameKill run canon out (insert t₀ S)
        else gameOnlyTag run canon out t₀] := by
  have hcoin :
      𝒟[do
          let sel ← ($ᵗ Bool : ProbComp Bool)
          if sel then gameKill run canon out S else ($ᵗ Bool : ProbComp Bool)] =
        𝒟[do
          let sel ← ($ᵗ Bool : ProbComp Bool)
          if sel then gameKill run canon out S
          else do
            let _ ← run
            ($ᵗ Bool : ProbComp Bool)] := by
    refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun sel => ?_
    cases sel
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (evalDist_bind_const run ($ᵗ Bool : ProbComp Bool)).symm
    · rfl
  rw [hcoin]
  unfold gameKill gameOnlyTag
  simp only [ite_bind_bool _ run]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) run,
    OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) run]
  refine evalDist_bind_congr run _ _ fun a => ?_
  by_cases hcan : canon a = t₀
  · simp only [hcan, ht₀, ↓reduceIte, Finset.mem_insert_self]
    exact evalDist_select_swap (out a) ($ᵗ Bool : ProbComp Bool)
  · have hmem : canon a ∈ insert t₀ S ↔ canon a ∈ S := by simp [Finset.mem_insert, hcan]
    simp [hmem, hcan]

theorem gameKill_boolDist_insert {α β τ : Type} [DecidableEq τ]
    (run₀ : ProbComp α) (canon₀ : α → τ) (out₀ : α → ProbComp Bool)
    (run₁ : ProbComp β) (canon₁ : β → τ) (out₁ : β → ProbComp Bool)
    (S : Finset τ) (t₀ : τ) (ht₀ : t₀ ∉ S) :
    𝒟[gameKill run₀ canon₀ out₀ S].boolDist 𝒟[gameKill run₁ canon₁ out₁ S] ≤
      𝒟[gameKill run₀ canon₀ out₀ (insert t₀ S)].boolDist
          𝒟[gameKill run₁ canon₁ out₁ (insert t₀ S)] +
        𝒟[gameOnlyTag run₀ canon₀ out₀ t₀].boolDist
          𝒟[gameOnlyTag run₁ canon₁ out₁ t₀] :=
  boolDist_le_of_select_eq _ _ _ _ _ _
    (evalDist_select_gameKill_insert run₀ canon₀ out₀ S t₀ ht₀)
    (evalDist_select_gameKill_insert run₁ canon₁ out₁ S t₀ ht₀)

theorem gameKill_boolDist_union_le {α β τ : Type} [DecidableEq τ]
    (run₀ : ProbComp α) (canon₀ : α → τ) (out₀ : α → ProbComp Bool)
    (run₁ : ProbComp β) (canon₁ : β → τ) (out₁ : β → ProbComp Bool)
    (T : Finset τ) :
    ∀ S : Finset τ, Disjoint S T →
      𝒟[gameKill run₀ canon₀ out₀ S].boolDist 𝒟[gameKill run₁ canon₁ out₁ S] ≤
        𝒟[gameKill run₀ canon₀ out₀ (S ∪ T)].boolDist
            𝒟[gameKill run₁ canon₁ out₁ (S ∪ T)] +
          ∑ t₀ ∈ T,
            𝒟[gameOnlyTag run₀ canon₀ out₀ t₀].boolDist
              𝒟[gameOnlyTag run₁ canon₁ out₁ t₀] := by
  induction T using Finset.induction_on with
  | empty =>
    intro S _; simp
  | @insert t₀ T ht₀_not_T ih =>
    intro S hdisj
    have ht₀_not_S : t₀ ∉ S := (Finset.disjoint_insert_right.mp hdisj).1
    have hdisj' : Disjoint (insert t₀ S) T :=
      Finset.disjoint_insert_left.mpr ⟨ht₀_not_T, (Finset.disjoint_insert_right.mp hdisj).2⟩
    have hstep := gameKill_boolDist_insert run₀ canon₀ out₀ run₁ canon₁ out₁ S t₀ ht₀_not_S
    have hih := ih (insert t₀ S) hdisj'
    have hunion : insert t₀ S ∪ T = S ∪ insert t₀ T := by ext x; simp
    rw [hunion] at hih
    rw [Finset.sum_insert ht₀_not_T]
    calc _ ≤ _ := hstep
      _ ≤ (𝒟[gameKill run₀ canon₀ out₀ (S ∪ insert t₀ T)].boolDist
              𝒟[gameKill run₁ canon₁ out₁ (S ∪ insert t₀ T)] +
            ∑ x ∈ T, 𝒟[gameOnlyTag run₀ canon₀ out₀ x].boolDist
              𝒟[gameOnlyTag run₁ canon₁ out₁ x]) +
            𝒟[gameOnlyTag run₀ canon₀ out₀ t₀].boolDist
              𝒟[gameOnlyTag run₁ canon₁ out₁ t₀] := add_le_add hih le_rfl
      _ = _ := by ac_rfl

end PartitionKillHybrid

section PrefixHybrid

/-- Priority-cascade output bit `if W1 then true else if W0 then false else b'` for two-stage
prefix hybrids. -/
@[expose] def slotStepOut (W1 W0 b' : Bool) : Bool :=
  if W1 then true else if W0 then false else b'

@[expose] def slotStepY1 (C coin W1 W0 win b' : Bool) : Bool :=
  if !C then coin else slotStepOut (W1 || win) W0 b'

@[expose] def slotStepY0 (C coin W1 W0 win b' : Bool) : Bool :=
  if !C then coin else slotStepOut W1 (W0 || win) b'

/-- Post-processed output bit emitted by a paused prefix reduction. -/
@[expose] def slotStepWRed (E C coin W1 W0 b' flip : Bool) : Bool :=
  if !E then false else if !C then (coin ^^ flip) else (slotStepOut W1 W0 b' ^^ flip)

theorem slotStep_bool_le_true (E C coin W1 W0 win b' flip : Bool) :
    (E && (slotStepY1 C coin W1 W0 win b' == !flip)) ≤
      (slotStepWRed E C coin W1 W0 b' flip || (E && win)) := by
  cases E <;> cases C <;> cases coin <;> cases W1 <;> cases W0 <;>
    cases win <;> cases b' <;> cases flip <;> decide

theorem slotStep_bool_le_false (E C coin W1 W0 win b' flip : Bool) :
    (slotStepWRed E C coin W1 W0 b' flip && !(E && win)) ≤
      (E && (slotStepY0 C coin W1 W0 win b' == !flip)) := by
  cases E <;> cases C <;> cases coin <;> cases W1 <;> cases W0 <;>
    cases win <;> cases b' <;> cases flip <;> decide

end PrefixHybrid

end Computational.Proofs.GameHop.GlobalHybrid

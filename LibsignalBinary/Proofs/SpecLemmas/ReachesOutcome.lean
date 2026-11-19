/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Lemmas
public import ProofLib.SepLogic
import ProofLib.Hoare.OutcomeSteps

/-!
# Inductive Demonic Reachability and `reaches_outcome` Combinators

Defines inductive demonic reachability (`DemonicReaches`) and provides `reaches_outcome`
introduction, consequence, congruence, `SepWPp` bridge, and `withStepsPost` combinators.
-/

public section

namespace Arm64

open ProofLib

/-! ## Inductive demonic reachability (`DemonicReaches`) -/

/-- Inductive demonic reachability: either `done s` holds now, or `s` is
    `.Running`, can take at least one `Step prog` transition (progress), and
    every `Step prog s s'` successor demonically reaches `done`. -/
inductive DemonicReaches (prog : Program) (done : State → Prop) : State → Prop where
  | here {s : State} :
      done s →
      DemonicReaches prog done s
  | step {s : State} :
      ¬ done s →
      s.status = .Running →
      (∃ s', Step prog s s') →
      (∀ s', Step prog s s' → DemonicReaches prog done s') →
      DemonicReaches prog done s

theorem DemonicReaches.mono {prog : Program} {P Q : State → Prop}
    (hPQ : ∀ ⦃s⦄, P s → Q s) {s : State} (h : DemonicReaches prog P s) :
    DemonicReaches prog Q s := by
  induction h with
  | here hp => exact .here (hPQ hp)
  | @step s _ hrun hex hall ih =>
    by_cases hq : Q s
    · exact .here hq
    · exact .step hq hrun hex (fun s' hs => ih s' hs)

theorem DemonicReaches.of_steps_deterministic {prog : Program} {done : State → Prop}
    (hdet : ∀ ⦃s s1 s2 : State⦄, Step prog s s1 → Step prog s s2 → s1 = s2)
    {s sf : State} (hsteps : Steps prog s sf) (hdone : done sf) :
    DemonicReaches prog done s := by
  induction hsteps with
  | refl => exact .here hdone
  | @step a b c hab _ ih =>
    by_cases ha : done a
    · exact .here ha
    · exact .step ha hab.status_running ⟨b, hab⟩
        (fun b' hab' => hdet hab' hab ▸ ih hdone)

/-- Lift `Steps prog s sf` and `done sf` into `DemonicReaches` under
    `Step.deterministic`. -/
theorem DemonicReaches.of_steps {prog : Program} {done : State → Prop}
    {s sf : State} (hsteps : Steps prog s sf) (hdone : done sf) :
    DemonicReaches prog done s :=
  DemonicReaches.of_steps_deterministic (fun _ _ _ h1 h2 => Step.deterministic h1 h2) hsteps hdone

/-! ## `reaches_outcome` introduction & consequence helpers -/

/-- Introduce `reaches_outcome` at a panicked terminal state reached via `Steps`. -/
theorem reaches_outcome_of_panic_steps {α : Type} {prog : Program}
    {spec : Spec α} {x : α} {R : SepProp} {s0 s sf : State}
    (hsteps : Steps prog s sf)
    (hpan : sf.status = .Panicked)
    (hq : sf.mem ⊨ spec.onPanic x s0 sf ∗ R) :
    reaches_outcome prog spec x R s0 s :=
  reaches_outcome_steps hsteps (reaches_outcome_refl_panic hpan hq)

/-! ## Congruence of `SubroutineOutcome` and `reaches_outcome` -/

/-- Congruence of `SubroutineOutcome` when the four outcome predicates agree on `x`. -/
theorem subroutineOutcome_eq_of_parts_eq {α : Type}
    {spec₁ spec₂ : Spec α} {x : α} {R : SepProp} {s0 sf : State}
    (hpost : spec₁.post x s0 sf = spec₂.post x s0 sf)
    (hpan : spec₁.onPanic x s0 sf = spec₂.onPanic x s0 sf)
    (hexit : ∀ code, spec₁.onExit x code s0 sf = spec₂.onExit x code s0 sf)
    (hoom : spec₁.onOom x s0 sf = spec₂.onOom x s0 sf) :
    SubroutineOutcome spec₁ x R s0 sf = SubroutineOutcome spec₂ x R s0 sf := by
  dsimp only [SubroutineOutcome]
  rw [hpost, hpan, hoom]
  simp only [hexit]

/-- Propositional equality of `reaches_outcome` when the four outcome predicates
    agree at `x` for all `sf`. Does not unfold `reaches_outcome`. -/
theorem reaches_outcome_eq_of_parts_eq {α : Type} {prog : Program}
    {spec₁ spec₂ : Spec α} {x : α} {R : SepProp} {s0 s : State}
    (hpost : ∀ sf, spec₁.post x s0 sf = spec₂.post x s0 sf)
    (hpan : ∀ sf, spec₁.onPanic x s0 sf = spec₂.onPanic x s0 sf)
    (hexit : ∀ code sf, spec₁.onExit x code s0 sf = spec₂.onExit x code s0 sf)
    (hoom : ∀ sf, spec₁.onOom x s0 sf = spec₂.onOom x s0 sf) :
    reaches_outcome prog spec₁ x R s0 s = reaches_outcome prog spec₂ x R s0 s := by
  have hout_eq : ∀ sf, SubroutineOutcome spec₁ x R s0 sf = SubroutineOutcome spec₂ x R s0 sf :=
    fun sf => subroutineOutcome_eq_of_parts_eq (hpost sf) (hpan sf) (fun c => hexit c sf) (hoom sf)
  exact propext ⟨
    fun h => h.mono_outcome (fun sf hout => hout_eq sf ▸ hout),
    fun h => h.mono_outcome (fun sf hout => (hout_eq sf).symm ▸ hout)⟩

/-! ## `SepWPp` → `reaches_outcome` bridges -/

namespace ReachesOutcome

/-- Lift a `SepWPp` proof (with panic handler) into `reaches_outcome` without
    unfolding `reaches_outcome` in the caller. -/
theorem reaches_outcome_of_sepWPp {α : Type} {prog : Program}
    {spec : Spec α} {x : α} {R P : SepProp} {s0 s : State}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp prog (s0.readReg64 Reg.lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    reaches_outcome prog spec x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hq, hspf, hcsf⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hmo⟩⟩ :=
    hwp R hm hL
  · exact reaches_outcome_steps hsteps
      (reaches_outcome_refl_return hpcf hrunf ⟨hq hmf, hspf, hcsf⟩)
  · exact reaches_outcome_steps hsteps (reaches_outcome_refl_panic hpan (hqp hmf))
  · exact (not_satisfies_false_sepConj hmo).elim

/-- Lift a `SepWPp` proof with a dropped frame component `Drop` and post entailment
    `Post sf ⊢ spec.post x s0 sf` into `reaches_outcome`. -/
theorem reaches_outcome_of_sepWPp_post {α : Type} {prog : Program}
    {spec : Spec α} {x : α} {R : SepProp} {s0 s : State} {P Drop : SepProp}
    {Post : State → SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hpost_imp : ∀ sf, Post sf ⊢ spec.post x s0 sf)
    (hwp : SepWPp prog (s0.readReg64 Reg.lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (Drop ∗ Post sf) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    reaches_outcome prog spec x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hq, hspf, hcsf⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · have hpost := hq hmf
    rw [sepConj_assoc] at hpost
    have hpost' := Satisfies.of_sep_right hpost
    exact reaches_outcome_steps hsteps
      (reaches_outcome_refl_return hpcf hrunf
        ⟨Satisfies.mono (sepConj_mono_left (hpost_imp sf)) hpost', hspf, hcsf⟩)
  · exact reaches_outcome_steps hsteps (reaches_outcome_refl_panic hpan (hqp hmf))
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Lift a panic-only `SepWPp` proof (`Q = fun _ _ => False`) into `reaches_outcome`. -/
theorem reaches_outcome_panic_of_sepWPp {α : Type} {prog : Program}
    {spec : Spec α} {x : α} {R : SepProp} {s0 s : State} {P : SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp prog (s0.readReg64 Reg.lr) s P
      (fun _ _ => False)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    reaches_outcome prog spec x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨_, _, _, _, hfalse⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩ := hwp R hm hL
  · exact False.elim hfalse
  · exact reaches_outcome_steps hsteps (reaches_outcome_refl_panic hpan (hqp hmf))
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## `withStepsPost`: enriching `spec.post` with `⌜Steps prog s0 sf⌝` -/

/-- `spec` with `⌜Steps prog s0 sf⌝` added to the postcondition.
    Valid under both angelic `∃ sf, Steps` and demonic `Reaches` (via `DemonicReaches.withSteps`). -/
abbrev withStepsPost {α : Type} (prog : Program) (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜Steps prog s0 sf⌝ ∗ spec.post x s0 sf }

theorem reaches_outcome_withStepsPost {α : Type} {prog : Program}
    {spec : Spec α} {x : α} {R : SepProp} {s0 : State}
    (h : reaches_outcome prog spec x R s0 s0) :
    reaches_outcome prog (withStepsPost prog spec) x R s0 s0 := by
  refine h.mono_outcome_steps fun sf hst hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    show sf.mem ⊨ (⌜Steps prog s0 sf⌝ ∗ spec.post x s0 sf) ∗ R
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hst, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem subroutine_ok_withStepsPost {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withStepsPost prog spec) :=
  subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hal _ =>
    reaches_outcome_withStepsPost (h.to_outcome x R s0 hpc hrun hpre hal)

end ReachesOutcome

end Arm64

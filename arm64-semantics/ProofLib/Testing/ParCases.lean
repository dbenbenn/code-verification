/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import ProofLib.Meta.ParCases

/-!
# `par_cases` Regression Tests

Positive and negative (`#guard_msgs`) tests for `par_cases` (`ProofLib.Meta.ParCases`): goals closed
in parallel (including `omega`, whose auxiliary lemmas are added to the main environment), a failing alternative reported
exactly as by the sequential `case`, a failing `all_goals` goal, the heartbeat budget (including an
alternative refused at the merge and charged only for its rerun), goals with metavariables in `let`
values, and the sequential mode.
-/

@[expose] public section

namespace Testing.ParCases

set_option parCases.report true in
/-- info: par_cases: 4 goals in parallel, 0 sequential alternatives -/
#guard_msgs in
theorem four (a b : Nat) (h : a < b) : (a < b + 1 ∧ a + 1 ≤ b) ∧ (0 < b ∧ a ≠ b) := by
  refine ⟨⟨?l1, ?l2⟩, ⟨?r1, ?r2⟩⟩
  par_cases
    case l1 => omega
    case r2 => omega
    all_goals omega

-- The `omega` auxiliary lemmas of the speculative runs are added to the main environment.
open Lean in
#eval show CoreM Unit from do
  let some c := (← getEnv).find? ``four | throwError "four is missing"
  let some v := c.value? (allowOpaque := true) | throwError "four has no value"
  unless v.getUsedConstants.any (fun n =>
      (`Testing.ParCases.four).isPrefixOf (privateToUserName n) && n != ``four) do
    throwError "four's proof does not use an auxiliary lemma"

/-- `case` tags select goals as `case` does (here by suffix); `all_goals` takes the rest. -/
example (p q : Prop) (hp : p) (hq : q) : (p ∧ q) ∧ (q ∧ p) := by
  refine ⟨⟨?a.x, ?a.y⟩, ⟨?b.x, ?b.y⟩⟩
  par_cases
    case a.x => exact hp
    case b.y => exact hp
    all_goals exact hq

-- A failing alternative is run again sequentially, with the same errors as the plain `case`.
/--
error: leaf failed
a : Nat
⊢ a + 1 = a
---
error: leaf failed
a : Nat
⊢ a + 1 = a
-/
#guard_msgs in
example (a : Nat) : (a = a ∧ a + 1 = a) ∧ (a = a ∧ a + 1 = a) := by
  refine ⟨⟨?l, ?r⟩, ⟨?l', ?r'⟩⟩
  par_cases
    case l => rfl
    case r => fail "leaf failed"
    case l' => rfl
    case r' => fail "leaf failed"

/--
error: unsolved goals
a : Nat
⊢ a + 1 = a
-/
#guard_msgs in
example (a : Nat) : a = a ∧ a + 1 = a := by
  refine ⟨?l, ?r⟩
  par_cases
    case l => rfl
    case r => skip

-- A failing goal of `all_goals` runs the whole `all_goals` sequentially.
/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  b ≥ 0
where
 b := ↑a
-/
#guard_msgs (error, drop info) in
example (a : Nat) : a ≤ a + 1 ∧ (a = a + 1) ∧ a < a + 1 := by
  refine ⟨?x, ?y, ?z⟩
  par_cases
    all_goals omega

/-! `maxHeartbeats` bounds the sum over all alternatives, as for the sequential proof: `burn n`
uses exactly `n` thousand heartbeats. -/

open Lean Elab Tactic in
/-- `burn n`: use `n` thousand heartbeats, then fail if the total is over `maxHeartbeats`. -/
elab "burn " n:num : tactic => do
  IO.addHeartbeats (n.getNat * 1000)
  Core.checkMaxHeartbeats "burn"

set_option parCases.report true in
set_option maxHeartbeats 100 in
/-- info: par_cases: 2 goals in parallel, 0 sequential alternatives -/
#guard_msgs in
example : True ∧ True := by
  refine ⟨?a, ?b⟩
  par_cases
    case a => burn 40; trivial
    case b => burn 40; trivial

-- Each run alone fits in the limit, but not both: the second one is refused at the merge and run
-- again sequentially, where it times out exactly as in the plain `case` proof below.
/--
error: (deterministic) timeout at `burn`, maximum number of heartbeats (100) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
info: par_cases: 1 goals in parallel, 1 sequential alternatives
-/
#guard_msgs in
set_option parCases.report true in
set_option maxHeartbeats 100 in
example : True ∧ True := by
  refine ⟨?a, ?b⟩
  par_cases
    case a => burn 60; trivial
    case b => burn 60; trivial

/--
error: (deterministic) timeout at `burn`, maximum number of heartbeats (100) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option maxHeartbeats 100 in
example : True ∧ True := by
  refine ⟨?a, ?b⟩
  case a => burn 60; trivial
  case b => burn 60; trivial

/-! An alternative refused at the merge after the budget check (here, because the two goals of
`all_goals` add the same auxiliary declaration) is charged only for its sequential rerun: the two
speculative runs (2×40) are not charged on top of the rerun (2×40), which fits in 100. -/

open Lean Elab Tactic in
/-- `aux_trivial`: close a `True` goal with the auxiliary theorem `<decl>.aux_trivial`, adding it if
    it does not exist yet. Two speculative runs both add it, so their merge collides. -/
elab "aux_trivial" : tactic => do
  let n := (← getDeclNGen).namePrefix ++ `aux_trivial
  unless (← getEnv).contains n do
    addDecl <| .thmDecl { name := n, levelParams := [], type := mkConst ``True,
                          value := mkConst ``True.intro }
  closeMainGoal `aux_trivial (mkConst n)

set_option parCases.report true in
set_option maxHeartbeats 100 in
/-- info: par_cases: 0 goals in parallel, 1 sequential alternatives -/
#guard_msgs in
theorem rerun_charged_once : True ∧ True := by
  refine ⟨?a, ?b⟩
  par_cases
    all_goals burn 40; aux_trivial

/-! A goal whose context has a `let` variable with an unassigned metavariable in its value is run
sequentially: closing it may assign the metavariable, which a speculative run cannot export. -/

open Lean Meta Elab Tactic in
/-- `let_mvar x`: introduce `x : Nat := ?m` with a fresh natural metavariable `?m`. -/
elab "let_mvar " x:ident : tactic => liftMetaTactic fun g => do
  let m ← g.withContext <| mkFreshExprMVar (mkConst ``Nat)
  let g ← g.define x.getId (mkConst ``Nat) m
  let (_, g) ← g.intro1P
  return [g]

-- Here `case a` assigns `?m := 5` through `x`'s value: run speculatively, the proof would refer to
-- an assignment lost at the merge.
set_option parCases.report true in
/-- info: par_cases: 0 goals in parallel, 2 sequential alternatives -/
#guard_msgs in
example : True ∧ True := by
  let_mvar x
  refine ⟨?a, ?b⟩
  par_cases
    case a => have _h : x = 5 := rfl; trivial
    case b => trivial

-- A closed `let` value does not prevent parallel runs.
set_option parCases.report true in
/-- info: par_cases: 2 goals in parallel, 0 sequential alternatives -/
#guard_msgs in
example : True ∧ True := by
  let x : Nat := 5
  refine ⟨?a, ?b⟩
  par_cases
    case a => have _h : x = 5 := rfl; trivial
    case b => trivial

set_option parCases.enabled false in
set_option parCases.report true in
#guard_msgs in
example (a b : Nat) (h : a < b) : a < b + 1 ∧ 0 < b := by
  refine ⟨?l, ?r⟩
  par_cases
    case l => omega
    all_goals omega

end Testing.ParCases

end

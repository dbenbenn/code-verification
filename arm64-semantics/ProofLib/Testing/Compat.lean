/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
meta import Lean

/-!
# Regression Tests for `ProofLib.Meta.Compat` and Condition-Flag Axiom Hygiene

Verifies that:
1. Standard `Init` lemmas backfilled on Lean 4.33 (`ite_eq_left`, `ite_eq_right`, `dite_eq_left`,
   `dite_eq_right`, `Bool.eq_false_of_ne_true`, `Bool.eq_true_of_ne_false`,
   `Bool.ne_false_of_eq_true`, `List.nodup_iff_eq_of_getElem_eq`, `List.Nodup.eq_of_getElem_eq`,
   `List.Nodup.getElem_inj`, `List.Nodup.getElem?_inj`) elaborate with identical binder conventions
   across supported Lean toolchains.
2. `backfill_if_missing` remains scoped to `ProofLib.Meta.Compat` rather than polluting the command
   grammar of downstream importers.
3. All compatibility theorems and relational condition-flag `@[arm64_norm]` lemmas (`addWithCarry*`,
   `conditionHolds_*_subs64`) stay strictly within `[propext, Classical.choice, Quot.sound]`
   (zero `Lean.ofReduceBool` or `Lean.trustCompiler`).
-/

public section

namespace ProofLib.Testing.Compat

theorem ite_compat_smoke (p : Prop) [Decidable p] (a b : Nat) (hp : p) (hnp : ¬p) :
    (if p then a else b) = a ∧ (if p then a else b) = b :=
  ⟨ite_eq_left hp, ite_eq_right hnp⟩

theorem dite_compat_smoke (p : Prop) [Decidable p] (t : p → Nat) (e : ¬p → Nat)
    (hp : p) : (if h : p then t h else e h) = t hp :=
  dite_eq_left hp

theorem dite_right_compat_smoke (p : Prop) [Decidable p] (t : p → Nat) (e : ¬p → Nat)
    (hnp : ¬p) : (if h : p then t h else e h) = e hnp :=
  dite_eq_right hnp

theorem bool_compat_smoke (b : Bool) (h1 : b ≠ true) : b = false :=
  Bool.eq_false_of_ne_true h1

theorem bool_true_compat_smoke (b : Bool) (h1 : b ≠ false) :
    b = true ∧ b ≠ false :=
  ⟨Bool.eq_true_of_ne_false h1, Bool.ne_false_of_eq_true (Bool.eq_true_of_ne_false h1)⟩

theorem list_nodup_compat_smoke {α : Type} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (heq : xs[i] = xs[j]) :
    i = j ∧ (xs[i] = xs[j] ↔ i = j) ∧ (xs[i]? = xs[j]? ↔ i = j) :=
  ⟨List.nodup_iff_eq_of_getElem_eq.mp hnd i j hi hj heq,
   hnd.getElem_inj (hi := hi) (hj := hj),
   hnd.getElem?_inj hi⟩

/-! ## Scoping and No-Op / Missing-Branch Regression Tests -/

#guard_msgs in
#eval show Lean.CoreM Unit from do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command
      "backfill_if_missing ite_eq_left : theorem dummy : True := trivial" with
  | .ok _ => throwError "backfill_if_missing leaked outside `open scoped ProofLib.Meta.Compat`"
  | .error _ => pure ()

section
open scoped ProofLib.Meta.Compat

#guard_msgs in
backfill_if_missing ite_eq_left :
  #eval (throwError "backfill_if_missing unexpectedly elaborated existing decl" : Lean.CoreM Unit)

/--
error: backfill_if_missing elaborated missing target as expected
-/
#guard_msgs in
backfill_if_missing ProofLib.Testing.Compat.nonExistentCompatTarget :
  #eval (throwError "backfill_if_missing elaborated missing target as expected" : Lean.CoreM Unit)

end

/-! ## Axiom-Cone Audit (Zero `Lean.ofReduceBool` / `Lean.trustCompiler`) -/

#guard_msgs in
#eval show Lean.CoreM Unit from do
  let targets := [
    ``ite_compat_smoke,
    ``dite_compat_smoke,
    ``dite_right_compat_smoke,
    ``bool_compat_smoke,
    ``bool_true_compat_smoke,
    ``list_nodup_compat_smoke,
    ``ProofLib.conditionHolds_cc_subs64,
    ``ProofLib.conditionHolds_ls_subs64,
    ``ProofLib.addWithCarry64_add_fst,
    ``ProofLib.addWithCarry32_add_fst
  ]
  for thm in targets do
    let axs ← Lean.collectAxioms thm
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected axioms for {thm}: {axs.toList}"

end ProofLib.Testing.Compat

end

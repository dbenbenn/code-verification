/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean.Elab.Command

/-!
# Standard-Library Compatibility Shims (`ProofLib.Meta.Compat`)

Conditionally defines standard `Init` lemmas present in Lean 4.34+ when elaborating under Lean 4.33,
while remaining a complete no-op (emitting zero declarations) when `Init` already provides them.
-/

public meta section

namespace ProofLib.Meta.Compat

scoped syntax (name := backfillIfMissing) "backfill_if_missing " ident " : " command : command

@[command_elab backfillIfMissing]
def elabBackfillIfMissing : Lean.Elab.Command.CommandElab := fun stx => do
  match stx with
  | `(backfill_if_missing $id:ident : $cmd:command) =>
    if !(← Lean.getEnv).contains id.getId then
      Lean.Elab.Command.elabCommand cmd
  | _ => Lean.Elab.throwUnsupportedSyntax

end ProofLib.Meta.Compat

end

public section

open scoped ProofLib.Meta.Compat

universe u

backfill_if_missing ite_eq_left :
  public theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} :
      (ite c t e) = t :=
    match h with
    | isTrue _ => rfl
    | isFalse hnc => absurd hc hnc

backfill_if_missing ite_eq_right :
  public theorem ite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t e : α} :
      (ite c t e) = e :=
    match h with
    | isTrue hc => absurd hc hnc
    | isFalse _ => rfl

backfill_if_missing dite_eq_left :
  public theorem dite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort u}
      {t : c → α} {e : ¬c → α} : (dite c t e) = t hc :=
    match h with
    | isTrue _ => rfl
    | isFalse hnc => absurd hc hnc

backfill_if_missing dite_eq_right :
  public theorem dite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u}
      {t : c → α} {e : ¬c → α} : (dite c t e) = e hnc :=
    match h with
    | isTrue hc => absurd hc hnc
    | isFalse _ => rfl

backfill_if_missing Bool.eq_false_of_ne_true :
  public theorem Bool.eq_false_of_ne_true : {b : Bool} → Not (Eq b true) → Eq b false
    | true, h => False.elim (h rfl)
    | false, _ => rfl

backfill_if_missing Bool.eq_true_of_ne_false :
  public theorem Bool.eq_true_of_ne_false : {b : Bool} → Not (Eq b false) → Eq b true
    | true, _ => rfl
    | false, h => False.elim (h rfl)

backfill_if_missing Bool.ne_false_of_eq_true :
  public theorem Bool.ne_false_of_eq_true : {b : Bool} → Eq b true → Not (Eq b false)
    | true, _, h => Bool.noConfusion h
    | false, h, _ => Bool.noConfusion h

backfill_if_missing List.nodup_iff_eq_of_getElem_eq :
  public theorem List.nodup_iff_eq_of_getElem_eq {α : Type u} {l : List α} :
      List.Nodup l ↔
        ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length), l[i] = l[j] → i = j := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    constructor
    · intro h i j hi hj heq
      rcases Nat.lt_trichotomy i j with hij | rfl | hji
      · exact False.elim (h i j hi hj hij heq)
      · rfl
      · exact False.elim (h j i hj hi hji heq.symm)
    · intro h i j hi hj hij heq
      exact Nat.ne_of_lt hij (h i j hi hj heq)

backfill_if_missing List.Nodup.eq_of_getElem_eq :
  public theorem List.Nodup.eq_of_getElem_eq {α : Type u} {xs : List α} (h : List.Nodup xs)
      {i : Nat} (hi : i < xs.length) {j : Nat} (hj : j < xs.length) : xs[i] = xs[j] → i = j :=
    List.nodup_iff_eq_of_getElem_eq.mp h i j hi hj

backfill_if_missing List.Nodup.getElem_inj :
  public theorem List.Nodup.getElem_inj {α : Type u} {xs : List α} (h : List.Nodup xs)
      {i : Nat} {hi : i < xs.length} {j : Nat} {hj : j < xs.length} : xs[i] = xs[j] ↔ i = j :=
    ⟨h.eq_of_getElem_eq hi hj, fun heq => by cases heq; rfl⟩

backfill_if_missing List.Nodup.getElem?_inj :
  public theorem List.Nodup.getElem?_inj {α : Type u} {xs : List α} {i : Nat}
      (h₀ : i < xs.length) (h₁ : List.Nodup xs) {j : Nat} : xs[i]? = xs[j]? ↔ i = j := by
    constructor
    · intro hij
      rw [List.getElem?_eq_getElem h₀] at hij
      obtain ⟨hj, heq⟩ := List.getElem?_eq_some_iff.mp hij.symm
      exact h₁.eq_of_getElem_eq h₀ hj heq.symm
    · rintro rfl; rfl

end

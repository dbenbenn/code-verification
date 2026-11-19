/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Lean
public import Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli

/-!
# Concrete Trace and PreKey Wire Parsing Facts for `KeepOpkCli` (`NoFullExplains/Parse.lean`)

Extracts the 6 `RunEvent`s `ev 0 .. ev 5` of `KeepOpkCli.trace` without unfolding `hexBytes`
globally, and proves fast kernel-checked parsing facts for Bob's two PreKey inputs (`ev 2` and
`ev 5`): both carry a non-empty `preKeyId` (`some 3`), have `runWrapped = true`, and carry distinct
33-byte ephemeral base keys (`p₂.baseKey.take 33 ≠ p₅.baseKey.take 33`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains.Parse

open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Composed.Refinement
  (PreKeyFields parsePreKeyWire RunRejected runWrapped)
open Symbolic.BugInjection (hexBytes)

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

theorem hexBytes_ofList (cs : List Char) :
    hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by
  unfold hexBytes hexDigit
  rw [String.toList_ofList]

attribute [local irreducible] Symbolic.BugInjection.hexBytes

elab "nfe_chars_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let sLit ← Lean.Meta.whnf (← Lean.Meta.whnf e).getAppArgs[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

elab "nfe_str_of_hex" t:term : term => do
  let e ← Lean.Meta.whnf (← Lean.Elab.Term.elabTerm t none)
  Lean.Meta.whnf e.getAppArgs[0]!

abbrev cliTrace : List CliEvent :=
  Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.trace

def dummyRunEvent : RunEvent :=
  { party := "", cmd := .init ⟨"", 0⟩ "", input := [], coins := [], exit := none }

def ev (k : Nat) : RunEvent :=
  match cliTrace[k]? with
  | some (.run e) => e
  | _ => dummyRunEvent

theorem trace_eq_evs :
    cliTrace = [
      .run (ev 0), .run (ev 1), .run (ev 2),
      .run (ev 3), .run (ev 4), .run (ev 5)
    ] := rfl

theorem ev_exit_ok (k : Nat) (hk : k < 6) : ∃ out, (ev k).exit = some (0, out) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨_, rfl⟩
  | n + 6 => omega

theorem ev_not_rejected (k : Nat) (hk : k < 6) : ¬ RunRejected (ev k) := by
  obtain ⟨out, hout⟩ := ev_exit_ok k hk
  intro hrej
  exact hrej out hout

theorem ev_alice_init_or_send (k : Nat) (hk : k ∈ ([0, 1, 3, 4] : List Nat)) :
    (ev k).party = "alice" ∧
      ((∃ peer bp, (ev k).cmd = .init peer bp) ∨ (∃ peer, (ev k).cmd = .send peer)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact ⟨rfl, .inl ⟨_, _, rfl⟩⟩
  · exact ⟨rfl, .inr ⟨_, rfl⟩⟩
  · exact ⟨rfl, .inl ⟨_, _, rfl⟩⟩
  · exact ⟨rfl, .inr ⟨_, rfl⟩⟩

private def ev2InChars : List Char := nfe_chars_of_hex (ev 2).input
private def ev2InFast : HwBytes := hexBytes.go hexDigit ev2InChars
private theorem ev2In_eq : (ev 2).input = ev2InFast := by
  have h1 : (ev 2).input = hexBytes (nfe_str_of_hex (ev 2).input) := rfl
  have h2 : (nfe_str_of_hex (ev 2).input) = String.ofList ev2InChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private def ev5InChars : List Char := nfe_chars_of_hex (ev 5).input
private def ev5InFast : HwBytes := hexBytes.go hexDigit ev5InChars
private theorem ev5In_eq : (ev 5).input = ev5InFast := by
  have h1 : (ev 5).input = hexBytes (nfe_str_of_hex (ev 5).input) := rfl
  have h2 : (nfe_str_of_hex (ev 5).input) = String.ofList ev5InChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

theorem ev2_bob_recv :
    (ev 2).party = "bob" ∧ (∃ peer, (ev 2).cmd = .recv peer) ∧ runWrapped (ev 2) = true := by
  refine ⟨rfl, ⟨_, rfl⟩, ?_⟩
  unfold runWrapped
  have hcmd : (ev 2).cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
  rw [hcmd, ev2In_eq]
  decide +kernel

theorem ev5_bob_recv :
    (ev 5).party = "bob" ∧ (∃ peer, (ev 5).cmd = .recv peer) ∧ runWrapped (ev 5) = true := by
  refine ⟨rfl, ⟨_, rfl⟩, ?_⟩
  unfold runWrapped
  have hcmd : (ev 5).cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
  rw [hcmd, ev5In_eq]
  decide +kernel

private theorem ev2_ev5_parse_check :
    (match parsePreKeyWire ev2InFast, parsePreKeyWire ev5InFast with
     | some p₂, some p₅ =>
       p₂.preKeyId.isSome && p₅.preKeyId.isSome && (p₂.baseKey.take 33 != p₅.baseKey.take 33)
     | _, _ => false) = true := by
  decide +kernel

theorem ev2_ev5_preKey_facts :
    ∃ p₂ p₅ : PreKeyFields,
      parsePreKeyWire (ev 2).input = some p₂ ∧
      parsePreKeyWire (ev 5).input = some p₅ ∧
      p₂.preKeyId ≠ none ∧
      p₅.preKeyId ≠ none ∧
      p₂.baseKey.take 33 ≠ p₅.baseKey.take 33 := by
  have hc := ev2_ev5_parse_check
  rw [← ev2In_eq, ← ev5In_eq] at hc
  cases hp₂ : parsePreKeyWire (ev 2).input with
  | none => rw [hp₂] at hc; cases hc
  | some p₂ =>
    cases hp₅ : parsePreKeyWire (ev 5).input with
    | none => rw [hp₂, hp₅] at hc; cases hc
    | some p₅ =>
      rw [hp₂, hp₅] at hc
      dsimp only at hc
      simp only [Bool.and_eq_true, Option.isSome_iff_ne_none, bne_iff_ne] at hc
      exact ⟨p₂, p₅, rfl, rfl, hc.1.1, hc.1.2, hc.2⟩

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains.Parse

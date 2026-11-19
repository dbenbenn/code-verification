/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticExit1EagerSessionCommit.NoSendCollision

/-!
# Machine-Checked Spec-Half Disproof for `synthetic-exit1-eager-session-commit`

Proves `spec_half_pinned`, `cliCompFitsPinned_satisfiable`, and `not_signalSessionSecurePlaced_of_implHalf`
for `Symbolic.BugInjection.Synthetic.Witnesses.Exit1EagerSessionCommitCli`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticExit1EagerSessionCommit.Top

open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Composed.Security (SignalSessionSecurePlaced)
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (CliSetupMatchesPinned)
open Symbolic.BugInjection.Proofs.SyntheticExit1EagerSessionCommit

attribute [local irreducible] Symbolic.BugInjection.hexBytes

theorem list_eq_four_splits {α : Type} {a b c d x : α} {xs ys : List α}
    (h : [a, b, c, d] = xs ++ x :: ys) :
    (xs = [] ∧ x = a ∧ ys = [b, c, d]) ∨
    (xs = [a] ∧ x = b ∧ ys = [c, d]) ∨
    (xs = [a, b] ∧ x = c ∧ ys = [d]) ∨
    (xs = [a, b, c] ∧ x = d ∧ ys = []) := by
  rcases xs with _ | ⟨x₀, _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, xs⟩⟩⟩⟩
  · simp at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · simp at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · simp at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · simp at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  · simp at h

theorem not_nextEventCollides_ev2Rej
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs₁ : List CliEvent} :
    ¬ NextEventCollides interp r S g ss vis evs₁ ev2Rej := by
  intro hcol
  have hcmd : ev2Rej.cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
  unfold NextEventCollides at hcol
  rw [hcmd] at hcol
  dsimp only at hcol
  obtain ⟨⟨out, hexit⟩, _⟩ := hcol
  change some (1, hexBytes "") = some (0, out) at hexit
  injection hexit with hexit
  injection hexit with hexit
  contradiction

/-- **SpecHalf disproof** for `synthetic-exit1-eager-session-commit`. -/
theorem spec_half_pinned :
    cliCompShape.SpecHalf (CliSetupMatchesPinned setup) trace := by
  intro (iw : cliCompShape.Interp) (r : ProtocolSetup) hfits
  have hwf : ProtocolSetupWF r := hfits.1.1.1
  have hiw : iw.1 = compI0 := hfits.1.2.1
  refine ⟨hwf, fun (S : OpaqueSymbolSemantics) _ hdisj => ?_⟩
  change (∃ g ss vis, Explains iw.1 r S g ss vis trace) ∨
    CollisionAfterExplainedPrefix iw.1 r S trace at hdisj
  rw [hiw] at hdisj
  rcases hdisj with ⟨g, ss, vis, hex⟩ | ⟨evs₁, ev, evs₂, g, ss, vis, hevs, hex, hcol⟩
  · exact not_explains_unpinned hex
  · rw [trace_eq_evs] at hevs
    rcases list_eq_four_splits hevs with
      ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩
    · injection hev with hev'; subst hev'; exact hcol
    · injection hev with hev'; subst hev'; exact not_nextEventCollides_ev1 hwf hex hcol
    · injection hev with hev'; subst hev'; exact not_nextEventCollides_ev2Rej hcol
    · injection hev with hev'; subst hev'; exact not_nextEventCollides_ev3BobSend hwf hex hcol

/-- **Non-vacuity** of `CliSetupMatchesPinned setup`. -/
theorem cliCompFitsPinned_satisfiable :
    ∃ iw r, CliSetupMatchesPinned setup iw r :=
  Symbolic.BugInjection.Proofs.SyntheticExit1EagerSessionCommit.cliCompFitsPinned_satisfiable

/-- **Top-level `SignalSessionSecurePlaced` regression disproof** for `synthetic-exit1-eager-session-commit`. -/
theorem not_signalSessionSecurePlaced_of_implHalf {bytes : List (BitVec 8)}
    {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hls : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt bytes mpl)
    (hmg : VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl)
    (hi : ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf (CliSetupMatchesPinned setup) elf trace) :
    ¬ SignalSessionSecurePlaced bytes :=
  not_signalSessionSecurePlaced_of_witness
    hls hmg
    spec_half_pinned
    hi
    coinsFresh_pinned

end Symbolic.BugInjection.Proofs.SyntheticExit1EagerSessionCommit.Top

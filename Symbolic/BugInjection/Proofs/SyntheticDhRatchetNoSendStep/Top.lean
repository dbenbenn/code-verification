/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.CoinsFresh
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.PtNoCollision
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.NoPrefixExplains
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvMemoBobStart

/-!
# Top-Level Spec-Half Disproof for `synthetic-dh-ratchet-no-send-step`

Exports `cliCompFitsPinned`, `cliCompFitsPinned_sub_fits`, `cliCompFitsPinned_satisfiable`,
`spec_half_pinned`, and `not_signalSessionSecurePlaced_of_implHalf` for `DhRatchetNoSendStepCli`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.Top

open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement (ProtocolSetup)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides)
open Symbolic.BugInjection (cliCompShape cliCompShapePlaced not_signalSessionSecurePlaced_of_witness)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0
  (dhRatchetI0 dhRatchetHooks0)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws
  (dhRatchetI0_externContractsHoldCli dhRatchetI0_hooksAgree)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.PtNoCollision
  (not_nextEventCollides_send)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.NoPrefixExplains
  (dhEv0 dhEv1 dhEv2 dhEv3 not_explains_prefix4)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvMemoBobStart
  (not_nextEventCollides_ev2)

abbrev cliCompFitsPinned : cliCompShape.Interp → ProtocolSetup → Prop :=
  Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0.cliCompFitsPinned

theorem cliCompFitsPinned_sub_fits :
    ∀ iw r, cliCompFitsPinned iw r →
      Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.fits iw r :=
  Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws.cliCompFitsPinned_sub_fits

theorem cliCompFitsPinned_satisfiable :
    ∃ iw r, cliCompFitsPinned iw r :=
  Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws.cliCompFitsPinned_satisfiable

private theorem trace_eq_prefix4 :
    ∃ e4, Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace =
      [.run dhEv0, .run dhEv1, .run dhEv2, .run dhEv3, e4] :=
  ⟨_, rfl⟩

theorem spec_half_pinned :
    cliCompShape.SpecHalf cliCompFitsPinned
      Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace := by
  intro ⟨interp, W⟩ r hfit
  have hbase := hfit.1
  obtain ⟨⟨hc, hi_eq, _, ⟨ha, _⟩, _, _⟩, _, _⟩ := hfit
  subst hi_eq
  refine ⟨hc.1, ?_⟩
  intro S _ hor
  have hfit0 : cliCompFitsPinned (dhRatchetI0, dhRatchetHooks0) r :=
    ⟨hbase, dhRatchetI0_externContractsHoldCli, dhRatchetI0_hooksAgree⟩
  obtain ⟨e4, htr_eq⟩ := trace_eq_prefix4
  rcases hor with ⟨g, ss, vis, hex⟩ | ⟨evs₁, ev, evs₂, g, ss, vis, hsplit, hex, hcol⟩
  · rw [htr_eq] at hex
    exact not_explains_prefix4 r S g ss vis [e4] ha hex
  · have hsp := htr_eq.symm.trans hsplit
    rcases evs₁ with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, rest⟩⟩⟩⟩
    · simp only [List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hsp
      rcases hsp with ⟨rfl, _⟩
      have hcmd0 : dhEv0.cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" := rfl
      unfold NextEventCollides at hcol
      rw [hcmd0] at hcol
      exact hcol
    · simp only [List.cons_append, List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hsp
      rcases hsp with ⟨rfl, rfl, _⟩
      have hcmd1 : dhEv1.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
      exact not_nextEventCollides_send r S g ss vis [.run dhEv0] dhEv1 evs₂
        hfit0 hsplit hex ⟨_, hcmd1⟩ hcol
    · simp only [List.cons_append, List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hsp
      rcases hsp with ⟨rfl, rfl, rfl, _⟩
      exact not_nextEventCollides_ev2 hfit0 hex hcol
    · simp only [List.cons_append, List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hsp
      rcases hsp with ⟨rfl, rfl, rfl, rfl, _⟩
      have hcmd3 : dhEv3.cmd = .send ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
      exact not_nextEventCollides_send r S g ss vis
        [.run dhEv0, .run dhEv1, .run dhEv2] dhEv3 evs₂
        hfit0 hsplit hex ⟨_, hcmd3⟩ hcol
    · rcases rest with _ | ⟨x4, rest'⟩
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsp
        rcases hsp with ⟨rfl, rfl, rfl, rfl, _⟩
        exact not_explains_prefix4 r S g ss vis [] ha hex
      · have hlen := congrArg List.length hsp
        simp at hlen

theorem not_signalSessionSecurePlaced_of_implHalf {bytes : List (BitVec 8)}
    {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hls : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt bytes mpl)
    (hmg : VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl)
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf cliCompFitsPinned elf
        Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecurePlaced bytes :=
  not_signalSessionSecurePlaced_of_witness hls hmg spec_half_pinned hi
    (fun _ _ hf => Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_of_compFits hf.1.1 (by decide +kernel))

end Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.Top

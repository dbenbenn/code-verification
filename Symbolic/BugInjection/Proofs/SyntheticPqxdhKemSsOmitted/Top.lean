/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.CoinsFresh
public import Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.I0Laws
public import Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.PtNoCollision
public import Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.NoPrefixExplains

/-!
# Top-Level Spec-Half Disproof for `synthetic-pqxdh-kem-ss-omitted`

Exports `cliCompFitsPinned`, `cliCompFitsPinned_sub_fits`, `cliCompFitsPinned_satisfiable`,
`spec_half_pinned`, and `not_signalSessionSecurePlaced_of_implHalf` for `PqxdhKemSsOmittedCli`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.Top

open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement (ProtocolSetup)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides)
open Symbolic.BugInjection (cliCompShape cliCompShapePlaced not_signalSessionSecurePlaced_of_witness)
open Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.DefsI0
  (pqxdhI0 pqxdhHooks0)
open Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.I0Laws
  (pqxdhI0_externContractsHoldCli pqxdhI0_hooksAgree)
open Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.PtNoCollision
  (not_nextEventCollides_send)
open Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.NoPrefixExplains
  (pqxdhEv0 pqxdhEv1 not_explains_prefix2)

abbrev cliCompFitsPinned : cliCompShape.Interp → ProtocolSetup → Prop :=
  Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.DefsI0.cliCompFitsPinned

theorem cliCompFitsPinned_sub_fits :
    ∀ iw r, cliCompFitsPinned iw r →
      Symbolic.BugInjection.Synthetic.Witnesses.PqxdhKemSsOmittedCli.fits iw r :=
  Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.I0Laws.cliCompFitsPinned_sub_fits

theorem cliCompFitsPinned_satisfiable :
    ∃ iw r, cliCompFitsPinned iw r :=
  Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.I0Laws.cliCompFitsPinned_satisfiable

private theorem trace_eq_prefix2 :
    ∃ e2, Symbolic.BugInjection.Synthetic.Witnesses.PqxdhKemSsOmittedCli.trace =
      [.run pqxdhEv0, .run pqxdhEv1, e2] :=
  ⟨_, rfl⟩

theorem spec_half_pinned :
    cliCompShape.SpecHalf cliCompFitsPinned
      Symbolic.BugInjection.Synthetic.Witnesses.PqxdhKemSsOmittedCli.trace := by
  intro ⟨interp, W⟩ r hfit
  have hbase := hfit.1
  obtain ⟨⟨hc, hi_eq, _, _, _, _⟩, _, _⟩ := hfit
  subst hi_eq
  refine ⟨hc.1, ?_⟩
  intro S _ hor
  have hfit0 : cliCompFitsPinned (pqxdhI0, pqxdhHooks0) r :=
    ⟨hbase, pqxdhI0_externContractsHoldCli, pqxdhI0_hooksAgree⟩
  obtain ⟨e2, htr_eq⟩ := trace_eq_prefix2
  rcases hor with ⟨g, ss, vis, hex⟩ | ⟨evs₁, ev, evs₂, g, ss, vis, hsplit, hex, hcol⟩
  · rw [htr_eq] at hex
    exact not_explains_prefix2 r S g ss vis [e2] hex
  · have hsp := htr_eq.symm.trans hsplit
    rcases evs₁ with _ | ⟨x0, _ | ⟨x1, rest⟩⟩
    · simp only [List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hsp
      rcases hsp with ⟨rfl, _⟩
      have hcmd0 : pqxdhEv0.cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" := rfl
      unfold NextEventCollides at hcol
      rw [hcmd0] at hcol
      exact hcol
    · simp only [List.cons_append, List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hsp
      rcases hsp with ⟨rfl, rfl, _⟩
      have hcmd1 : pqxdhEv1.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
      exact not_nextEventCollides_send r S g ss vis [.run pqxdhEv0] pqxdhEv1 evs₂
        hfit0 hsplit hex ⟨_, hcmd1⟩ hcol
    · rcases rest with _ | ⟨x2, rest'⟩
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsp
        rcases hsp with ⟨rfl, rfl, _⟩
        exact not_explains_prefix2 r S g ss vis [] hex
      · have hlen := congrArg List.length hsp
        simp at hlen

theorem not_signalSessionSecurePlaced_of_implHalf {bytes : List (BitVec 8)}
    {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hls : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt bytes mpl)
    (hmg : VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl)
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf cliCompFitsPinned elf
        Symbolic.BugInjection.Synthetic.Witnesses.PqxdhKemSsOmittedCli.trace) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecurePlaced bytes :=
  not_signalSessionSecurePlaced_of_witness hls hmg spec_half_pinned hi
    (fun _ _ hf => Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_of_compFits hf.1.1 (by decide +kernel))

end Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.Top

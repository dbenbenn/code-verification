/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.CoinsFresh
public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws
public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.PtNoCollision
public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains
public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision

/-!
# Top-Level Spec-Half Disproof for `synthetic-keep-opk`

Exports `keepOpkCompFitsPinned`, `keepOpkCompFitsPinned_sub_fits`,
`keepOpkCompFitsPinned_satisfiable`, `spec_half_pinned`, and
`not_signalSessionSecurePlaced_of_implHalf` for `KeepOpkCli`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.Top

open DY.Libsignal.Composed.Refinement (ProtocolSetup)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides)
open Symbolic.BugInjection (cliCompShape cliCompShapePlaced not_signalSessionSecurePlaced_of_witness)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
  (keepOpkI0 keepOpkHooks0)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws
  (keepOpkI0_externContractsHoldCli keepOpkI0_hooksAgree)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.PtNoCollision
  (not_nextEventCollides_send)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains
  (not_explains_full)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision
  (not_nextEventCollides_recv)

abbrev keepOpkCompFitsPinned : cliCompShape.Interp → ProtocolSetup → Prop :=
  Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0.keepOpkCompFitsPinned

theorem keepOpkCompFitsPinned_sub_fits :
    ∀ iw r, keepOpkCompFitsPinned iw r →
      Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.fits iw r :=
  Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws.keepOpkCompFitsPinned_sub_fits

theorem keepOpkCompFitsPinned_satisfiable :
    ∃ iw r, keepOpkCompFitsPinned iw r :=
  Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws.keepOpkCompFitsPinned_satisfiable

theorem spec_half_pinned :
    cliCompShape.SpecHalf keepOpkCompFitsPinned
      Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.trace := by
  intro ⟨interp, W⟩ r hfit
  have hbase := hfit.1
  have hc := hbase.1
  have hi_eq := hbase.2.1
  subst hi_eq
  refine ⟨hc.1, ?_⟩
  intro S _ hor
  have hfit0 : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r :=
    ⟨hbase, keepOpkI0_externContractsHoldCli, keepOpkI0_hooksAgree⟩
  rcases hor with ⟨g, ss, vis, hex⟩ | ⟨evs₁, ev, evs₂, g, ss, vis, hsplit, hex, hcol⟩
  · exact not_explains_full r S g ss vis hfit0 hex
  · cases hcmd : ev.cmd with
    | init a b =>
      unfold NextEventCollides at hcol
      rw [hcmd] at hcol
      exact hcol
    | send peer =>
      exact not_nextEventCollides_send r S g ss vis evs₁ ev evs₂ hfit0 hsplit hex ⟨peer, hcmd⟩ hcol
    | recv peer =>
      exact not_nextEventCollides_recv r S g ss vis evs₁ ev evs₂ hfit0
        (fun g' ss' vis' => not_explains_full r S g' ss' vis' hfit0) hsplit hex ⟨peer, hcmd⟩ hcol

theorem not_signalSessionSecurePlaced_of_implHalf {bytes : List (BitVec 8)}
    {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hls : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt bytes mpl)
    (hmg : VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl)
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf keepOpkCompFitsPinned elf
        Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.trace) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecurePlaced bytes :=
  not_signalSessionSecurePlaced_of_witness hls hmg spec_half_pinned hi
    (fun _ _ hf => Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_of_compFits_withOpk hf.1.1 (by decide +kernel))

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.Top

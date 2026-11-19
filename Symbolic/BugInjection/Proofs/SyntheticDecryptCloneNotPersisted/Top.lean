/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.CoinsFresh
public import Symbolic.BugInjection.Synthetic.Witnesses.DecryptCloneNotPersistedCli
public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PtNoCollision7003
public import Symbolic.BugInjection.Proofs.SyntheticDecryptCloneNotPersisted.Clean3NoCol

/-!
# Machine-Checked Spec-Half Disproof for `synthetic-decrypt-clone-not-persisted-cli`

Proves `cliCompFitsPinned_satisfiable`, `spec_half_pinned`, and
`not_signalSessionSecurePlaced_of_implHalf` for the round-4 synthetic mutant
`synthetic-decrypt-clone-not-persisted`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticDecryptCloneNotPersisted.Top

open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Explains)
open DY.Libsignal.Composed.Refinement.Cli (CollisionAfterExplainedPrefix)
open Symbolic.BugInjection (cliCompShape cliCompShapePlaced not_signalSessionSecurePlaced_of_witness)
open Symbolic.BugInjection.Synthetic.Witnesses
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (not_collisionAfterExplainedPrefix_of_from not_collision_step_irrelevant
   not_collision_step_run not_collision_nil)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 (compI7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003
  (compFitsPinned7003 cliCompFitsPinned7003
   cliCompFitsPinned7003_satisfiable_decryptCloneNotPersisted)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PtNoCollision7003
  (not_nextEventCollides_pt7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean2BobStart7003
  (not_nextEventCollides_ev2_m1)
open Symbolic.BugInjection.Proofs.SyntheticDecryptCloneNotPersisted
  (not_explains_m1 not_nextEventCollides_ev3_m1)

theorem coinsFresh_decryptCloneNotPersistedCli :
    ∀ iw r, cliCompFitsPinned7003 DecryptCloneNotPersistedCli.setup iw r →
      DY.Libsignal.Composed.Refinement.Cli.CoinsFresh r DecryptCloneNotPersistedCli.trace :=
  fun _ _ hf =>
    Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_of_compFits hf.1.1 (by decide +kernel)

attribute [local irreducible] Symbolic.BugInjection.hexBytes

/-- Pinned `fits` predicate for `DecryptCloneNotPersistedCli`. -/
abbrev cliCompFitsPinned := cliCompFitsPinned7003

/-- Satisfiability of `cliCompFitsPinned` on `DecryptCloneNotPersistedCli.setup`. -/
theorem cliCompFitsPinned_satisfiable :
    ∃ iw r, cliCompFitsPinned DecryptCloneNotPersistedCli.setup iw r :=
  cliCompFitsPinned7003_satisfiable_decryptCloneNotPersisted

/-- Machine-checked spec half for `DecryptCloneNotPersistedCli` at `cliCompFitsPinned`. -/
theorem spec_half_pinned :
    cliCompShape.SpecHalf (cliCompFitsPinned DecryptCloneNotPersistedCli.setup)
      DecryptCloneNotPersistedCli.trace := by
  intro (iw : cliCompShape.Interp) (r : ProtocolSetup) hfits
  have hwf : ProtocolSetupWF r := hfits.1.1.1
  have hiw : iw.1 = compI7003 := hfits.1.2.1
  have hf : compFitsPinned7003 setup7003 compI7003 r := hiw ▸ hfits.1
  refine ⟨hwf, fun (S : OpaqueSymbolSemantics) _ hdisj => ?_⟩
  change (∃ g ss vis, Explains iw.1 r S g ss vis DecryptCloneNotPersistedCli.trace) ∨
    CollisionAfterExplainedPrefix iw.1 r S DecryptCloneNotPersistedCli.trace at hdisj
  rw [← m1Events_eq, hiw] at hdisj
  rcases hdisj with ⟨g, ss, vis, hex⟩ | hcol
  · exact not_explains_m1 hf hex
  · refine not_collisionAfterExplainedPrefix_of_from ?_ hcol
    unfold m1Events
    apply not_collision_step_irrelevant rfl
    dsimp only [List.nil_append]
    apply not_collision_step_run (fun g ss vis hex =>
      not_nextEventCollides_pt7003 (b₀ := 0x74#8) hwf rfl
        (by dsimp [ev1_m1]; rw [pt1M1Raw_eq]; exact pt_noncollision_facts.1)
        (by dsimp [ev1_m1]; rw [pt1M1Raw_eq]; exact pt_noncollision_facts.2.1)
        (by dsimp [ev1_m1]; rw [pt1M1Raw_eq]; exact pt_noncollision_facts.2.2.1)
        (by dsimp [ev0]; rw [coins0Raw_eq, Bool.and_true]; exact pt_noncollision_facts.2.2.2.1)
        hex)
    dsimp only [List.cons_append, List.nil_append]
    apply not_collision_step_run (fun g ss vis hex => not_nextEventCollides_ev2_m1 hf hex)
    dsimp only [List.cons_append, List.nil_append]
    apply not_collision_step_run (fun g ss vis hex => not_nextEventCollides_ev3_m1 hf hex)
    exact not_collision_nil

/-- Conditional end-to-end disproof of `SignalSessionSecurePlaced` from an implementation half on `bytes`. -/
theorem not_signalSessionSecurePlaced_of_implHalf {bytes : List (BitVec 8)}
    {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hls : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt bytes mpl)
    (hmg : VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl)
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf (cliCompFitsPinned DecryptCloneNotPersistedCli.setup) elf
        DecryptCloneNotPersistedCli.trace) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecurePlaced bytes :=
  not_signalSessionSecurePlaced_of_witness hls hmg spec_half_pinned hi
    coinsFresh_decryptCloneNotPersistedCli

end Symbolic.BugInjection.Proofs.SyntheticDecryptCloneNotPersisted.Top

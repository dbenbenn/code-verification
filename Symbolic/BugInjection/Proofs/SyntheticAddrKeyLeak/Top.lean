/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.Defs
public import Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.NoSendCollision
public import Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.NoFullExplains
public import Symbolic.BugInjection.Proofs.Common.CoinsFresh

/-!
# Spec-Half Disproof for `AddrKeyLeakCli`

Proves `spec_half_pinned_akEvents`, `spec_half_pinned`, `cliSetupMatchesPinned_satisfiable`, and
`not_signalSessionSecurePlaced_of_implHalf` for `AddrKeyLeakCli`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.Top

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Explains)
open DY.Libsignal.Composed.Refinement.Cli (CollisionAfterExplainedPrefix)
open Symbolic.BugInjection
  (cliCompShape cliCompShapePlaced not_signalSessionSecurePlaced_of_witness)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (CliSetupMatchesPinned)
open Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.Defs
  (akEvents evInit bunBytes_eq_bundleBytes pt1_length
   cliCompFitsPinned_satisfiable_ak)
open Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.NoSendCollision
  (evInitAk not_collisionAfterExplainedPrefix_two_runs
   not_collisionAfterExplainedPrefix_of_wf)
open Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.NoFullExplains
  (invalidPreKeySendAddr not_explains_akEvents_invalidAddr
   not_explains_akTrace)

private theorem evInit_eq_evInitAk : evInit = evInitAk := by
  unfold evInit evInitAk
  rw [bunBytes_eq_bundleBytes]
  rfl

/-- Parameterized spec-half disproof for any 2-call `akEvents out1` whose Call 1 `send` stdout
`out1` satisfies `invalidPreKeySendAddr out1 = true`. -/
theorem spec_half_pinned_akEvents {out1 : HwBytes} (hbad : invalidPreKeySendAddr out1 = true) :
    cliCompShape.SpecHalf
      (CliSetupMatchesPinned Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.setup)
      (akEvents out1) := by
  intro (iw : cliCompShape.Interp) (r : ProtocolSetup) hfits
  have hwf : ProtocolSetupWF r := hfits.1.1.1
  have hiw : iw.1 = compI0 := hfits.1.2.1
  refine ⟨hwf, fun (S : OpaqueSymbolSemantics) _ hdisj => ?_⟩
  change (∃ g ss vis, Explains iw.1 r S g ss vis (akEvents out1)) ∨
    CollisionAfterExplainedPrefix iw.1 r S (akEvents out1) at hdisj
  rw [hiw] at hdisj
  rcases hdisj with hex | hcol
  · exact not_explains_akEvents_invalidAddr hbad hex
  · exact not_collisionAfterExplainedPrefix_two_runs hwf evInit_eq_evInitAk rfl pt1_length hcol

/-- Machine-checked spec-half disproof on the recorded witness trace `AddrKeyLeakCli.trace`. -/
theorem spec_half_pinned :
    cliCompShape.SpecHalf
      (CliSetupMatchesPinned Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.setup)
      Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.trace := by
  intro (iw : cliCompShape.Interp) (r : ProtocolSetup) hfits
  have hwf : ProtocolSetupWF r := hfits.1.1.1
  have hiw : iw.1 = compI0 := hfits.1.2.1
  refine ⟨hwf, fun (S : OpaqueSymbolSemantics) _ hdisj => ?_⟩
  change
    (∃ g ss vis,
      Explains iw.1 r S g ss vis Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.trace) ∨
    CollisionAfterExplainedPrefix iw.1 r S
      Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.trace at hdisj
  rw [hiw] at hdisj
  rcases hdisj with hex | hcol
  · exact not_explains_akTrace hex
  · exact not_collisionAfterExplainedPrefix_of_wf hwf hcol

theorem cliSetupMatchesPinned_satisfiable :
    ∃ iw r,
      CliSetupMatchesPinned Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.setup iw r :=
  cliCompFitsPinned_satisfiable_ak

theorem not_signalSessionSecurePlaced_of_implHalf {bytes : List (BitVec 8)}
    {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hls : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt bytes mpl)
    (hmg : VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl)
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf
        (CliSetupMatchesPinned Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.setup)
        elf Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.trace) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecurePlaced bytes :=
  not_signalSessionSecurePlaced_of_witness hls hmg spec_half_pinned hi
    (fun _ _ hf =>
      Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_of_compFits hf.1.1 (by decide +kernel))

end Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.Top

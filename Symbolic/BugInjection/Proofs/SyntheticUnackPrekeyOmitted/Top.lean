/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.Defs
public import Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.NoSendCollision
public import Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.NoFullExplains
public import Symbolic.BugInjection.Proofs.Common.CoinsFresh

/-!
# Spec-Half Disproof for `UnackPrekeyOmittedCli`

Proves `spec_half_pinned_uoEvents`, `spec_half_pinned`, `cliSetupMatchesPinned_satisfiable`, and
`not_signalSessionSecurePlaced_of_implHalf` for `UnackPrekeyOmittedCli`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.Top

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Explains)
open DY.Libsignal.Composed.Refinement.Cli (CollisionAfterExplainedPrefix)
open Symbolic.BugInjection
  (cliCompShape cliCompShapePlaced not_signalSessionSecurePlaced_of_witness)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (CliSetupMatchesPinned)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443 (compI0)
open Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.Defs
  (uoSendOut uoSendOut_head? uoEvents uoEvents_eq cliCompFitsPinned_satisfiable_uo)
open Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.NoSendCollision
  (not_collisionAfterExplainedPrefix_uo)
open Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.NoFullExplains
  (not_explains_uo)

/-- Parameterized spec-half disproof for any 2-call `uoEvents out1` whose Call 1 `send` stdout
starts with `0x02` (`wireWhisperTag`). -/
theorem spec_half_pinned_uoEvents {out1 : HwBytes} (hhead : out1.head? = some 0x02#8) :
    cliCompShape.SpecHalf
      (CliSetupMatchesPinned Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.setup)
      (uoEvents out1) := by
  intro (iw : cliCompShape.Interp) (r : ProtocolSetup) hfits
  have hwf : ProtocolSetupWF r := hfits.1.1.1
  have hiw : iw.1 = compI0 := hfits.1.2.1
  refine ⟨hwf, fun (S : OpaqueSymbolSemantics) _ hdisj => ?_⟩
  change (∃ g ss vis, Explains iw.1 r S g ss vis (uoEvents out1)) ∨
    CollisionAfterExplainedPrefix iw.1 r S (uoEvents out1) at hdisj
  rw [hiw] at hdisj
  rcases hdisj with ⟨g, ss, vis, hex⟩ | hcol
  · exact not_explains_uo hwf hhead hex
  · exact not_collisionAfterExplainedPrefix_uo out1 hwf hcol

/-- Machine-checked spec-half disproof on the recorded witness trace `UnackPrekeyOmittedCli.trace`. -/
theorem spec_half_pinned :
    cliCompShape.SpecHalf
      (CliSetupMatchesPinned Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.setup)
      Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.trace := by
  rw [← uoEvents_eq]
  exact spec_half_pinned_uoEvents uoSendOut_head?

theorem cliSetupMatchesPinned_satisfiable :
    ∃ iw r,
      CliSetupMatchesPinned Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.setup iw r :=
  cliCompFitsPinned_satisfiable_uo

theorem not_signalSessionSecurePlaced_of_implHalf {bytes : List (BitVec 8)}
    {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hls : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt bytes mpl)
    (hmg : VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl)
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf
        (CliSetupMatchesPinned Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.setup)
        elf Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.trace) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecurePlaced bytes :=
  not_signalSessionSecurePlaced_of_witness hls hmg spec_half_pinned hi
    (fun _ _ hf =>
      Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_of_compFits hf.1.1 (by decide +kernel))

end Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.Top

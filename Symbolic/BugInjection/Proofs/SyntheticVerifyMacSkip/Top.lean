/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.Defs
public import Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.NoFullExplains
public import Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.NoRecvCollision
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Common.CoinsFresh

/-!
# Spec-Half Disproof for `VerifyMacSkipCli`

Proves `spec_half_pinned`, `cliSetupMatchesPinned_satisfiable`, and
`not_signalSessionSecurePlaced_of_implHalf` for `VerifyMacSkipCli`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.Top

open Symbolic.BugInjection
  (cliCompShape cliCompShapePlaced not_signalSessionSecurePlaced_of_witness)
open Symbolic.BugInjection.Synthetic
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (CliSetupMatchesPinned)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
  (spec_half_pinned_443_of_gen)
open Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.Defs
  (msg38_vms cliEventsVMS cliEventsVMS_eq compFitsPinned_hb_of_vms msg38_vms_props)
open Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.NoFullExplains
  (no_coinSplit_matchedPrefix_vms)
open Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.NoRecvCollision (noBsc_vms_cli_swap)

theorem coinsFresh_verifyMacSkipCli :
    ∀ iw r, CliSetupMatchesPinned Witnesses.VerifyMacSkipCli.setup iw r →
      DY.Libsignal.Composed.Refinement.Cli.CoinsFresh r cliEventsVMS :=
  fun _ _ hf =>
    Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_of_compFits hf.1.1 (by decide +kernel)

attribute [local irreducible] Symbolic.BugInjection.hexBytes

theorem spec_half_pinned :
    cliCompShape.SpecHalf
      (CliSetupMatchesPinned Witnesses.VerifyMacSkipCli.setup)
      cliEventsVMS := by
  rw [cliEventsVMS_eq]
  exact spec_half_pinned_443_of_gen Witnesses.VerifyMacSkipCli.setup msg38_vms
    msg38_vms_props.1 msg38_vms_props.2.1
    (fun _ _ _ _ _ _ hcs => no_coinSplit_matchedPrefix_vms hcs)
    (fun _ hcs₁ r S g ms p hfits hnb hex hp =>
      noBsc_vms_cli_swap hcs₁ r S g ms p (compFitsPinned_hb_of_vms hfits) hnb hex hp)

theorem cliSetupMatchesPinned_satisfiable :
    ∃ iw r, CliSetupMatchesPinned Witnesses.VerifyMacSkipCli.setup iw r :=
  Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.cliSetupMatchesPinned_satisfiable_hb

theorem not_signalSessionSecurePlaced_of_implHalf {bytes : List (BitVec 8)}
    {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hls : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt bytes mpl)
    (hmg : VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl)
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf
        (CliSetupMatchesPinned Witnesses.VerifyMacSkipCli.setup)
        elf cliEventsVMS) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecurePlaced bytes :=
  not_signalSessionSecurePlaced_of_witness hls hmg spec_half_pinned hi
    coinsFresh_verifyMacSkipCli

end Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.Top

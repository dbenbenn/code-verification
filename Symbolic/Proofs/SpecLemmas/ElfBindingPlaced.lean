/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import Symbolic.Specifications.Refinement.ElfBinding

/-!
# Placement-Based ELF Binding Helpers

**Checked by Lean.** Untrusted placement-parameterized versions of `elfRel`, `CliElfProgress`,
and `CompRefinesCliBinary`, used by internal placement proofs and bug-injection disproofs.
The trusted ELF-direct definitions live in `Symbolic/Specifications/Refinement/ElfBinding.lean`.
-/

public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open Arm64 Arm64.Process
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement (ProtocolSetup ProtocolSetupWF)
open CryptoVerification.SignalSession
  (CliHooks CliReachesSampleNttStuckPlaced Inputs Outcome libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (CliElfCodeMatchesPlaced cliRunPlacedSig)

/-- Relocatable ARM64 process run relation of `elf` at multi-block placement `mpl` under hooks `W`,
guarded by per-call agreement with the executed primitives (`RealHooksAgreeOnInput W i`). -/
@[expose] def elfRelPlaced (mpl : Obj.MultiPlacement) (elf : ElfImage)
    (_interp : ExternInterpretation) (W : CliHooks) :
    Inputs → Option Outcome → Prop :=
  fun i o => runFnToRelation (cliRunPlacedSig mpl elf) i o ∧ RealHooksAgreeOnInput W i

/-- Placement-based progress guarantee for `elf` at placement `mpl`. -/
@[expose] def CliElfProgressPlaced (mpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  ∀ interp : ExternInterpretation, ExternContractsHoldCli interp →
  ∀ W : CliHooks, HooksMatchPlaced interp W →
  ∀ r : ProtocolSetup, ProtocolSetupWF r →
  ∀ t : CliTurn,
    CliReachable (elfRelPlaced mpl elf interp W) interp r
      (CliTurn.init (initDirs interp r)) t →
  ∀ (c : CliCall) (i : CryptoVerification.SignalSession.Inputs),
    ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
    RealHooksAgreeOnInput W i →
    cliRunPlacedSig mpl elf i ≠ none ∨ CliReachesSampleNttStuckPlaced mpl elf i

/-- Whole-protocol refinement and progress guarantee for ELF image `bytes` at placement `mpl`. -/
@[expose] def CompRefinesCliBinaryPlacedAt (mpl : Obj.MultiPlacement) (bytes : List (BitVec 8)) :
    Prop :=
  ∃ elf : ElfImage, ElfImage.parse bytes = .ok elf ∧ CliElfCodeMatchesPlaced mpl elf ∧
    CliElfProgressPlaced mpl elf ∧
    CompRefinesCli HooksMatchPlaced (elfRelPlaced mpl elf)

/-- Relocatable whole-protocol refinement and progress guarantee quantified over all valid
placements `mpl` of `libsignalSessionLib` in `bytes`. -/
@[expose] def CompRefinesCliBinaryPlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    CompRefinesCliBinaryPlacedAt mpl bytes

end DY.Libsignal.Composed.Refinement.Cli

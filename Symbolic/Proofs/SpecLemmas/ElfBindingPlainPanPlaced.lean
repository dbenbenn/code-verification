/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.CliPlainPanPlaced -- proof-setup: allow-public-import
public import Symbolic.Specifications.Refinement.ElfBinding

/-!
# Plain-Memory Panic-Intercepted Placed ELF Binding Helpers (`ElfBindingPlainPanPlaced`)

Untrusted placement-parameterized versions of `elfRel`, `CliElfProgress`, and
`CompRefinesCliBinary` over `cliRunPlainPanPlaced1` (starting from plain `elf.loadState` without
`.data` token patching), leaving `Symbolic/Proofs/SpecLemmas/ElfBindingPlaced.lean` untouched for
`BugInjection`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced

open Arm64 Arm64.Process
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement (ProtocolSetup ProtocolSetupWF)
open DY.Libsignal.Composed.Refinement.Cli
  (CliCall CliReachable CliTurn CompRefinesCli ExternContractsHoldCli HooksMatchPlaced InputsFor
   RealHooksAgreeOnInput ValidCall initDirs runFnToRelation)
open CryptoVerification.SignalSession (CliHooks Inputs Outcome libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (CliElfCodeMatchesPlaced)
open LibsignalBinary.Proofs.Placed.CliPlainPanPlaced
  (CliReachesSampleNttStuckPlainPanPlaced1 cliRunPlainPanPlaced1)

/-- Plain-memory panic-intercepted ARM64 process run relation of `elf` at placement `mpl`. -/
@[expose] def elfRelPlainPanPlaced (mpl : Obj.MultiPlacement) (elf : ElfImage)
    (_interp : ExternInterpretation) (W : CliHooks) :
    Inputs → Option Outcome → Prop :=
  fun i o => runFnToRelation (cliRunPlainPanPlaced1 mpl elf) i o ∧ RealHooksAgreeOnInput W i

/-- Plain-memory panic-intercepted progress guarantee for `elf` at placement `mpl`. -/
@[expose] def CliElfProgressPlainPanPlaced (mpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  ∀ interp : ExternInterpretation, ExternContractsHoldCli interp →
  ∀ W : CliHooks, HooksMatchPlaced interp W →
  ∀ r : ProtocolSetup, ProtocolSetupWF r →
  ∀ t : CliTurn,
    CliReachable (elfRelPlainPanPlaced mpl elf interp W) interp r
      (CliTurn.init (initDirs interp r)) t →
  ∀ (c : CliCall) (i : CryptoVerification.SignalSession.Inputs),
    ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
    RealHooksAgreeOnInput W i →
    cliRunPlainPanPlaced1 mpl elf i ≠ none ∨ CliReachesSampleNttStuckPlainPanPlaced1 mpl elf i

/-- Whole-protocol refinement and progress guarantee for ELF image `bytes` at placement `mpl`
under `cliRunPlainPanPlaced1`. -/
@[expose] def CompRefinesCliBinaryPlainPanPlacedAt (mpl : Obj.MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf : ElfImage, ElfImage.parse bytes = .ok elf ∧ CliElfCodeMatchesPlaced mpl elf ∧
    CliElfProgressPlainPanPlaced mpl elf ∧
    CompRefinesCli HooksMatchPlaced (elfRelPlainPanPlaced mpl elf)

/-- Relocatable plain-memory whole-protocol refinement and progress guarantee quantified over all
valid placements `mpl` of `libsignalSessionLib` in `bytes`. -/
@[expose] def CompRefinesCliBinaryPlainPanPlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    CompRefinesCliBinaryPlainPanPlacedAt mpl bytes

end Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced

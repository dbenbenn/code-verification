/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
import Symbolic.Proofs.Refinement.Composed.Cli.ElfToModelV2PlainBridge
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressPlacedKElf
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced -- proof-setup: allow-public-import
public import VerifiedLibraries.Mallocng.Spec

/-!
# Relocatable Plain-Memory Whole-Protocol CLI Refinement for `cliElfBytes` from `H2KGhostArms`

**Checked by Lean.**

Proves `CompRefinesCliBinaryPlainPanPlaced cliElfBytes` conditionally on `H2KGhostArms` by combining
`h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf`, `cliElfProgressPlaced_cliElfK`, and
`comp_refines_cli_model_b2`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementKElf

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open DY.Libsignal.Composed.Refinement.Cli (comp_refines_cli_model_b2)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
  (H2KGhostArms h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf)
open Symbolic.Proofs.Refinement.Composed.Cli.ElfToModelV2PlainBridge
  (compRefinesCliBinaryPlainPanPlaced_of_v2OomF3Bytes)
open Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced
  (CliElfProgressPlainPanPlaced CompRefinesCliBinaryPlainPanPlaced)
open Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressPlacedKElf
  (cliElfProgressPlaced_cliElfK)

/-- Plain-memory placed progress for `cliElfBytes` given `H2KGhostArms`. -/
theorem cliElfProgressPlaced_cliElfK (hG : H2KGhostArms) :
    ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf : ElfImage, ElfImage.parse cliElfBytes = .ok elf →
        CliElfProgressPlainPanPlaced mpl elf :=
  ProgressPlacedKElf.cliElfProgressPlaced_cliElfK hG

/-- Relocatable plain-memory whole-protocol CLI refinement for `cliElfBytes` given
`H2KGhostArms`. -/
theorem comp_refines_cli_placed_proofK :
    H2KGhostArms → CompRefinesCliBinaryPlainPanPlaced cliElfBytes :=
  fun hG =>
    compRefinesCliBinaryPlainPanPlaced_of_v2OomF3Bytes
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_mallocng_linkedIn
      (fun _ hLs _ hparse =>
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_trustedCodeMatchesPlaced_of_parse
          hLs hparse)
      (h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf hG)
      (cliElfProgressPlaced_cliElfK hG)
      comp_refines_cli_model_b2

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementKElf

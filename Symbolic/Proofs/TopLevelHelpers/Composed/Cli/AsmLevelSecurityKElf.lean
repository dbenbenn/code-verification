/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
import Symbolic.Proofs.Swarm.CREF.Cli.TopEvents
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementKElf
public import Symbolic.Specifications.Security.Binary
public import Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced -- proof-setup: allow-public-import

/-!
# Relocatable Plain-Memory Assembly-Level Security for `cliElfBytes` from `H2KGhostArms`

**Checked by Lean.**

Derives `SignalSessionSecurePlainPanPlaced cliElfBytes` from `H2KGhostArms` via
`signalSessionSecureFor_of_refines` and `RefinementKElf.comp_refines_cli_placed_proofK`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurityKElf

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (CliElfCodeMatchesPlaced)
open DY.Libsignal.Composed.Refinement.Cli (HooksMatchPlaced signalSessionSecureFor_of_refines)
open DY.Libsignal.Composed.Security (SignalSessionSecureFor)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms (H2KGhostArms)
open Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced
  (CliElfProgressPlainPanPlaced elfRelPlainPanPlaced)
open Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementKElf (comp_refines_cli_placed_proofK)

/-- Plain-memory assembly-level security at placement `mpl` for ELF image `bytes`. -/
@[expose] def SignalSessionSecurePlainPanPlacedAt (mpl : MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf : ElfImage, ElfImage.parse bytes = .ok elf ∧ CliElfCodeMatchesPlaced mpl elf ∧
    CliElfProgressPlainPanPlaced mpl elf ∧
    SignalSessionSecureFor HooksMatchPlaced (elfRelPlainPanPlaced mpl elf)

/-- Relocatable plain-memory assembly-level security for ELF image `bytes`. -/
@[expose] def SignalSessionSecurePlainPanPlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl : MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    SignalSessionSecurePlainPanPlacedAt mpl bytes

/-- Relocatable two-placement plain-memory assembly-level CLI security for `cliElfBytes` from
`H2KGhostArms`. -/
theorem signal_session_secure_placed_proofK :
    H2KGhostArms → SignalSessionSecurePlainPanPlaced cliElfBytes := by
  intro hG mpl hLs
  rcases comp_refines_cli_placed_proofK hG mpl hLs with ⟨elf, hparse, hcode, hprog, hRef⟩
  exact ⟨elf, hparse, hcode, hprog, signalSessionSecureFor_of_refines hRef⟩

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurityKElf

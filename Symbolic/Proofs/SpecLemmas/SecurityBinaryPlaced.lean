/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ElfBindingPlaced -- proof-setup: allow-public-import
public import Symbolic.Specifications.Security.Binary

/-!
# Placement-Based Binary Security Helpers

**Checked by Lean.** Untrusted placement-parameterized versions of `SignalSessionSecure`, used by
internal placement proofs and bug-injection disproofs. The trusted ELF-direct statement lives in
`Symbolic/Specifications/Security/Binary.lean`.
-/

public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Security

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open DY.Libsignal.Composed.Refinement.Cli
  (CliElfProgressPlaced HooksMatchPlaced elfRelPlaced)
open CryptoVerification.SignalSession (libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (CliElfCodeMatchesPlaced)

/-- Security and no-fault progress of ELF image `bytes` at placement `mpl`. -/
@[expose] def SignalSessionSecurePlacedAt (mpl : MultiPlacement) (bytes : List (BitVec 8)) :
    Prop :=
  ∃ elf : ElfImage, ElfImage.parse bytes = .ok elf ∧ CliElfCodeMatchesPlaced mpl elf ∧
    CliElfProgressPlaced mpl elf ∧
    SignalSessionSecureFor HooksMatchPlaced (elfRelPlaced mpl elf)

/-- Relocatable binary security quantified over all valid placements `mpl` of
`libsignalSessionLib` in `bytes`. -/
@[expose] def SignalSessionSecurePlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl : MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    SignalSessionSecurePlacedAt mpl bytes

end DY.Libsignal.Composed.Security

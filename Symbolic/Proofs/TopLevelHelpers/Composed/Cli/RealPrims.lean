/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliElf
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Specifications.Security.Binary
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurityElf
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RealPrimsBridge
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RealPrimsSecBridge
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RealPrimsWitness
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementElf

/-!
# Real-Primitive Headline Proofs (`RP-TOP`)

Proves the three real-primitive headline proof obligations (`RealPrimsAdmissible`,
`CompRefinesCliBinaryReal cliElfBytes`, and `SignalSessionSecureReal cliElfBytes`, blueprint node
`RP-TOP`):

1. `real_prims_admissible_proof`: delegates to `RealPrimsWitness.real_prims_admissible_witness`,
   witnessing an extern interpretation `realCliInterp` that satisfies `ExternContractsHoldCli` and
   matches `realCliHooks` (`RealPrimsMatch`).
2. `comp_refines_cli_real_proof`: combines `real_prims_admissible_proof` and `comp_refines_cli_proof`
   via `RealPrimsBridge.compRefinesCliBinaryReal_of_binary`.
3. `signal_session_secure_real_proof`: combines `real_prims_admissible_proof` and
   `signal_session_secure_proof` via `RealPrimsSecBridge.signalSessionSecureReal_of_binary`.

- **Status**: `done` (Falsification: end-to-end signature composition and non-vacuity checks across
  `RP-ADM`, `RP-REF`, and `RP-SEC`; no counterexample).
- **Handoff**: Complete with `0 sorry`; feeds `Symbolic/Theorems/Refinement.lean` and
  `Symbolic/Theorems/Security.lean`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli

open CryptoVerification.SignalSession (cliElfBytes)
open DY.Libsignal.Composed.Refinement.Cli (RealPrimsAdmissible CompRefinesCliBinaryReal)
open DY.Libsignal.Composed.Security (SignalSessionSecureReal)

theorem real_prims_admissible_proof : RealPrimsAdmissible :=
  RealPrimsWitness.real_prims_admissible_witness

theorem comp_refines_cli_real_proof : CompRefinesCliBinaryReal cliElfBytes :=
  RealPrimsBridge.compRefinesCliBinaryReal_of_binary
    real_prims_admissible_proof comp_refines_cli_proof

theorem signal_session_secure_real_proof : SignalSessionSecureReal cliElfBytes :=
  RealPrimsSecBridge.signalSessionSecureReal_of_binary
    real_prims_admissible_proof signal_session_secure_proof

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli

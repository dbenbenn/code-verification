/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliElf
public import Symbolic.Specifications.Refinement.ElfBinding

/-!
# Comparator challenge: trace refinement of the binary (`Symbolic/Theorems/Refinement.lean`)

**Trusted: the statements.** Each theorem below has the same name and the same statement, byte for
byte, as the theorem of that name in `Symbolic/Theorems/Refinement.lean` (lake library
`CliElfLib`), with `sorry` as its proof. It imports the specification modules that
`Refinement.lean` imports publicly, and no proof module. See `comparator/README.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace Proven.Refinement

open CryptoVerification.SignalSession (cliElfBytes)
open DY.Libsignal.Composed.Refinement.Cli (CompRefinesCliBinary)

theorem comp_refines_cli :
    CompRefinesCliBinary cliElfBytes :=
  sorry

open DY.Libsignal.Composed.Refinement.Cli (CompRefinesCliBinaryReal RealPrimsAdmissible)

theorem real_prims_admissible :
    RealPrimsAdmissible :=
  sorry

theorem comp_refines_cli_real :
    CompRefinesCliBinaryReal cliElfBytes :=
  sorry

end Proven.Refinement

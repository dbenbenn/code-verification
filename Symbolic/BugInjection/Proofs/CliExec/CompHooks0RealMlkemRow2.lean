/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemDefs -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemLits -- proof-setup: allow-public-import
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemRow1 -- build-order: serialize heavy leaves (CI memory)
meta import ProofLib.ProgramReflection

/-!
# Certified `compMlkem768FromSeed` Row 2 (`mlkemSeed2`)
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemRow2

open scoped ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemDefs (checkMlkemRowGivenMat)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemLits (
  compMlkemMat2Lit compMlkemRho2Lit mlkemDk2 mlkemSeed2
)

public section
set_option autoImplicit false
set_option maxRecDepth 200000

theorem mlkem_row2_ok :
    checkMlkemRowGivenMat compMlkemMat2Lit compMlkemRho2Lit mlkemSeed2 mlkemDk2 = true := by
  rfl_kernel

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemRow2

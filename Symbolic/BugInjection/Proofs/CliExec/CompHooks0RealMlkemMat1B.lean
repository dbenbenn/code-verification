/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemLits -- proof-setup: allow-public-import
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat1A -- build-order: serialize heavy leaves (CI memory)
meta import ProofLib.ProgramReflection

/-!
# Certified Row 2 of `mlkemSeed1` Matrix `A`
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat1B

open scoped ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak (arrayGetDFast)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs (checkMatrixRowFast)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemLits (compMlkemMat1Lit compMlkemRho1Lit)

public section
set_option autoImplicit false
set_option maxRecDepth 200000

theorem mlkem_mat1_2_ok :
    checkMatrixRowFast 3 2 compMlkemRho1Lit true (arrayGetDFast compMlkemMat1Lit 2 (Array.mk [])) = true := by
  rfl_kernel

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat1B

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberLits -- proof-setup: allow-public-import
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberMat01 -- build-order: serialize heavy leaves (CI memory)
meta import ProofLib.ProgramReflection

/-!
# Certified Rows 2 and 3 of `compKyberPk` Matrix `A^T`
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberMat23

open scoped ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak (arrayGetDFast)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs (checkMatrixRowFast)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberLits (compKyberATLit compKyberPk)

public section
set_option autoImplicit false
set_option maxRecDepth 200000

theorem kyber_mat_23_ok :
    (checkMatrixRowFast 4 2 ((compKyberPk.drop 1536).take 32) false
       (arrayGetDFast compKyberATLit 2 (Array.mk [])) &&
     checkMatrixRowFast 4 3 ((compKyberPk.drop 1536).take 32) false
       (arrayGetDFast compKyberATLit 3 (Array.mk []))) = true := by
  rfl_kernel

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberMat23

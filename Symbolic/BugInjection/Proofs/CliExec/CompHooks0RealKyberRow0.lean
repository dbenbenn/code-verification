/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberLits -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberSplit -- proof-setup: allow-public-import
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberKey -- build-order: serialize heavy leaves (CI memory)
meta import ProofLib.ProgramReflection

/-!
# Certified `compHooks0` Kyber-1024 Row 0 Encryption (`compKyberE0`)
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow0

open scoped ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberLits (
  compKyberATLit compKyberCt0 compKyberE0 compKyberHPkLit compKyberTHatLit
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberSplit (checkKyberRowEnc)

public section
set_option autoImplicit false
set_option maxRecDepth 200000

theorem kyber_row0_enc_ok :
    checkKyberRowEnc compKyberATLit compKyberTHatLit compKyberHPkLit
      compKyberE0 compKyberCt0 = true := by
  rfl_kernel

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberRow0

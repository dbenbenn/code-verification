/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Lits
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard
meta import ProofLib.ProgramReflection

/-!
# Isolated `ws3_dk_eq` Kernel Check for `Cheval26WeakStateIdx1Cli`
-/

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Dk

open scoped ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace (wsBob0 wsMsg3)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Lits (ws3DkLit)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuardCommon (
  drKeyEqBool eq_of_drKeyOptEq recvDkAt
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard (compP0 optEqBool)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard (realP0Hybrid)

public section

set_option autoImplicit false

theorem ws3_dk_fast :
    optEqBool drKeyEqBool (recvDkAt compP0 wsBob0 wsMsg3) (some ws3DkLit) = true := by
  rfl_kernel

theorem ws3_dk_val : recvDkAt compP0 wsBob0 wsMsg3 = some ws3DkLit :=
  eq_of_drKeyOptEq ws3_dk_fast

theorem ws3_dk_eq :
    optEqBool drKeyEqBool (recvDkAt compP0 wsBob0 wsMsg3)
      (recvDkAt realP0Hybrid wsBob0 wsMsg3) = true := by
  rfl_kernel

end

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Dk

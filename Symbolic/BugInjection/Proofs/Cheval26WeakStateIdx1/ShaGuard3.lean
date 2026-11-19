/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ElfBindingSha256 -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard
meta import ProofLib.ProgramReflection
import Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuardCommon
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Lits
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Dk
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Tail
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3TailB

/-!
# `RealHooksAgreeOnInput compHooks0` Proof for `wsInp3`
-/

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3

open CryptoVerification.E2E (wirePrekey)
open CryptoVerification.SignalSession (filesOf pqRecvInputs)
open DY.Libsignal.Composed.Refinement.Cli (InputsEquiv RealHooksAgreeOnInput)
open scoped ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace (wsBob0 wsInp3 wsMsg3 wsRc3)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Dk (ws3_dk_eq ws3_dk_val)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Lits (
  eq_of_optSessionStateEqBool recvOutEqBool recvOutEqBool_trans recvWithDkAt_some_eq_recvDecWithSt0At
)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3Tail (ws3_st0_real ws3_tail_fast)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3TailB (ws3_tail_real)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuardCommon (
  checkRecvPrekeyEqAt_of_split inputsEquiv_of_eq recvDkAt recvWithDkAt wsBody3
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard (
  compP0 optEqBool pqRecvInputsFast pqRecvInputs_eq_fast prodEqBool sessionStateEqBool
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard (
  checkRecvPrekeyEqReal realHooksAgreeOnInput_of_pqRecvPrekey_none realP0Hybrid
)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq (compHooks0_placed_eq)

public section

set_option autoImplicit false

private theorem ws3_tail_eq :
    (let dkOpt := recvDkAt compP0 wsBob0 wsMsg3
     optEqBool (optEqBool (optEqBool (prodEqBool (fun x y => x == y) sessionStateEqBool)))
       (recvWithDkAt compP0 wsBob0 wsMsg3 wsRc3 dkOpt)
       (recvWithDkAt realP0Hybrid wsBob0 wsMsg3 wsRc3 dkOpt)) = true := by
  dsimp only
  rw [ws3_dk_val, recvWithDkAt_some_eq_recvDecWithSt0At realP0Hybrid,
      ← eq_of_optSessionStateEqBool ws3_st0_real]
  exact recvOutEqBool_trans ws3_tail_fast ws3_tail_real

theorem ws3_recv_eq : checkRecvPrekeyEqReal wsBob0 wsMsg3 wsRc3 = true :=
  checkRecvPrekeyEqAt_of_split ws3_dk_eq ws3_tail_eq

theorem realHooksAgreeOnInput_wsInp3 : RealHooksAgreeOnInput compHooks0 wsInp3 := by
  rw [← compHooks0_placed_eq]
  have heq : InputsEquiv wsInp3 (pqRecvInputs compP0 wsBob0 (wirePrekey :: wsBody3) wsRc3) :=
    inputsEquiv_of_eq (pqRecvInputs_eq_fast compP0 wsBob0 (wirePrekey :: wsBody3) wsRc3)
      ⟨by rfl_kernel, by rfl_kernel, by rfl_kernel,
       fun p => congrArg (fun fs => filesOf fs p)
         (by rfl_kernel : wsInp3.files =
           (pqRecvInputsFast compP0 wsBob0 (wirePrekey :: wsBody3) wsRc3).files)⟩
  exact realHooksAgreeOnInput_of_pqRecvPrekey_none
    (st₀ := wsBob0) (body₀ := wsBody3) (m₀ := wsMsg3) (rc₀ := wsRc3)
    (by rfl_kernel) rfl (by rfl_kernel) heq (by rfl_kernel) ws3_recv_eq

end

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3

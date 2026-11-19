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
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard02
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard45
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard6

/-!
# `Sha256AgreesOnInput compHooks0` Proofs for `Cheval26WeakStateIdx1Cli`

Re-exports `Sha256AgreesOnInput compHooks0` across **all** matching `PqParty` states in
`PqxdhPartyInSpecDomain` for all 7 concrete witness calls (`wsInp0`..`wsInp6`) of
`Cheval26WeakStateIdx1Cli` from per-step modules (`ShaGuard02`, `ShaGuard3`, `ShaGuard45`,
`ShaGuard6`) so each kernel reflection step runs well within the `16 GiB` per-module RSS budget.
-/

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard

open DY.Libsignal.Composed.Refinement.Cli (RealHooksAgreeOnInput)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace (
  FileList ValidStepFiles wsInp0 wsInp1 wsInp2 wsInp3 wsInp4 wsInp5 wsInp6
)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)

public section

set_option autoImplicit false

theorem realHooksAgreeOnInput_wsInp0 : RealHooksAgreeOnInput compHooks0 wsInp0 :=
  Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard02.realHooksAgreeOnInput_wsInp0

theorem realHooksAgreeOnInput_wsInp1 {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (hValid : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    RealHooksAgreeOnInput compHooks0 (wsInp1 f0) :=
  Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard02.realHooksAgreeOnInput_wsInp1 hValid

theorem realHooksAgreeOnInput_wsInp2 {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (hValid : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    RealHooksAgreeOnInput compHooks0 (wsInp2 f1) :=
  Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard02.realHooksAgreeOnInput_wsInp2 hValid

theorem realHooksAgreeOnInput_wsInp3 : RealHooksAgreeOnInput compHooks0 wsInp3 :=
  Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3.realHooksAgreeOnInput_wsInp3

theorem realHooksAgreeOnInput_wsInp4 {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (hValid : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    RealHooksAgreeOnInput compHooks0 (wsInp4 f2) :=
  Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard45.realHooksAgreeOnInput_wsInp4 hValid

theorem realHooksAgreeOnInput_wsInp5 {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (hValid : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    RealHooksAgreeOnInput compHooks0 (wsInp5 f4) :=
  Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard45.realHooksAgreeOnInput_wsInp5 hValid

theorem realHooksAgreeOnInput_wsInp6 {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (hValid : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    RealHooksAgreeOnInput compHooks0 (wsInp6 f3) :=
  Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard6.realHooksAgreeOnInput_wsInp6 hValid

end

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard

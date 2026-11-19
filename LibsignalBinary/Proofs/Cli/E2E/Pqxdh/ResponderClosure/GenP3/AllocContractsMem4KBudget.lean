/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Heap.IfaceBudgetBase
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WP.StateNorm

public section

set_option autoImplicit false
set_option linter.dupNamespace false

/-!
# Budget-Threaded 4K-Stack Extern Contract Bundle (`AllocContractsMem4KBudget`)

`subroutine_ok` contracts on `tripleRatchetProgAtExt b ext` for `rustCliAllocBudgetSpec`,
`rustCliDeallocBudgetSpec`, `rustCliReallocBudgetSpec`, `sessionShimBudgetSpec`, and
4096-byte-stack `sessionMemcpyBudgetSpec` / `sessionMemmoveBudgetSpec` /
`sessionMemsetBudgetSpec` (`allocHookStack = 4096`), matching `CliExternsBudgetOk`.
-/

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget
   rustCliAllocBudgetSpecBase rustCliAllocNoOomSpecBase
   rustCliDeallocBudgetSpecBase rustCliDeallocNoOomSpecBase
   rustCliReallocBudgetSpecBase rustCliReallocNoOomSpecBase
   subroutine_ok_allocNoOom_of_budgetBase subroutine_ok_reallocNoOom_of_budgetBase)
open LibsignalBinary.Heap.SpecBudget (AllocHooksBudgetBase)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyBudgetSpec sessionMemmoveBudgetSpec sessionMemsetBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec subroutine_ok_noAllocShim_of_sessionShimBudget)

namespace AllocContractsMem4KBudget

variable {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
  {ext : String → Option (State → State)}

section HookHelpers

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

end HookHelpers

end AllocContractsMem4KBudget

section StandaloneDeallocHook

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

end StandaloneDeallocHook

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget

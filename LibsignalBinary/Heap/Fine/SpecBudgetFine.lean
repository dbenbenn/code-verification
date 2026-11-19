/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget

/-!
# `SpecBudget` Pool Bridge & Re-exports at `fineCostModel`

**Checked by Lean. Not trusted.**

Re-exports `fineHookRustCliAllocBudget` and the `mallocng`-backed hook discharges from
`LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget`, and proves
`fineHookBudgetPool_of_codeLoaded` upgrading `(fineRustCliAllocBudget γ mpl tp brkStart).pool` to
`(fineHookRustCliAllocBudget γ mpl tp brkStart).pool` under `VerifiedLibraries.mallocngLib.CodeLoaded`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 ProofLib
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  mallocngHookBudgetPool_of_codeLoaded
)

export LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  aesStorageCell fineHookRustCliAllocBudget fineHookBudgetPool_of_init
  fineHookRustCliAllocBudgetEntries fineHookRustCliAllocBudgetEntries_thunks
  fineHookRdlAllocZeroed_budget_placed_ok
)
export LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  fineHookRustCliAllocZeroedBudget_thunk_ok stringCloneHookMallocng
  fineAesEnc_budget_hookSat fineAesDec_budget_hookSat fineLibcruxHmac_budget_hookSat
)
export LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  fineStringClone_budget_hookSat
)

/-- Upgrade `(fineRustCliAllocBudget γ mpl tp brkStart).pool lim st s ∗ aesStorageCell brkStart ∗ R` to
    `(fineHookRustCliAllocBudget γ mpl tp brkStart).pool lim st s ∗ R` whenever
    `VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem` holds. -/
theorem fineHookBudgetPool_of_codeLoaded
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : FineBudget} {s : State} {R : SepProp}
    (hCL : VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem)
    (hsat : s.mem ⊨ (fineRustCliAllocBudget γ mpl tp brkStart).pool lim st s ∗ aesStorageCell brkStart ∗ R) :
    s.mem ⊨ (fineHookRustCliAllocBudget γ mpl tp brkStart).pool lim st s ∗ R :=
  mallocngHookBudgetPool_of_codeLoaded (M := fineCostModel) (I := fineCostModelIface) hCL hsat

end LibsignalBinary.Heap.Fine

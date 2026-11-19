/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64 -- proof-setup: allow-public-import

/-!
# Row-Owned `ExtraRowSpec` Leaf for `lsAesDecSym`

Row-owned consumer `HookOk` predicate for `signal_crypto::aes_cbc::aes_256_cbc_decrypt`
(`CliGhostHooks.extra`).

Unlike pure or stack-only rows, `aes_256_cbc_decrypt`'s `HookOk` contracts
(`aesDecBudgetSpec aes256Dec fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim`
and `aesDecWeakBudgetSpec`) depend on the placement-dependent `mallocng` parameters
`(mmpl, brkStart, lim, γ, tp)`, so they cannot live in the placement-free `ExtraRowSpec` bundle.
Instead, `AesDecRowSpec` is `True` (so `GhostRowSpecOk lsAesDecSym f` reduces to `fs_eq` and `fsT`),
and the budget-parameterized `HookOk` is supplied at the placement-aware `C2RowLayoutFacts` /
`ElfSlicesPqOom*` assembly boundary.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.AesDecRowSpec

open Arm64

/-- Row-owned consumer `HookOk` predicate for `lsAesDecSym` (`True`; placement-dependent
    `aesDecBudgetSpec` `HookOk` is discharged at the `mmpl`-parameterized top level). -/
@[expose] def AesDecRowSpec (_f : State → State) : Prop :=
  True

theorem AesDecRowSpec.intro (f : State → State) : AesDecRowSpec f :=
  trivial

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.AesDecRowSpec

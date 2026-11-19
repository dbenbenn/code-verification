/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64 -- proof-setup: allow-public-import

/-!
# Row-Owned `ExtraRowSpec` Leaf for `lsAesEncSym`

Row-owned consumer `HookOk` predicate for `signal_crypto::aes_cbc::aes_256_cbc_encrypt`
(`CliGhostHooks.extra`).

Unlike pure or stack-only rows, `aes_256_cbc_encrypt`'s `HookOk` contract
(`aesEncBudgetSpec aes256Enc fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim`)
depends on the placement-dependent `mallocng` parameters `(mmpl, brkStart, lim, γ, tp)`, so it
cannot live in the placement-free `ExtraRowSpec` bundle. Instead, `AesEncRowSpec` is `True` (so
`GhostRowSpecOk lsAesEncSym f` reduces to `fs_eq` and `fsT`), and the budget-parameterized `HookOk`
is supplied at the placement-aware `C2RowLayoutFacts` / `ElfSlicesPqOom*` assembly boundary.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.AesEncRowSpec

open Arm64

/-- Row-owned consumer `HookOk` predicate for `lsAesEncSym` (`True`; placement-dependent
    `aesEncBudgetSpec` `HookOk` is discharged at the `mmpl`-parameterized top level). -/
@[expose] def AesEncRowSpec (_f : State → State) : Prop :=
  True

theorem AesEncRowSpec.intro (f : State → State) : AesEncRowSpec f :=
  trivial

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.AesEncRowSpec

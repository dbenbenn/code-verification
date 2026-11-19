/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64

/-!
# Row-Owned `ExtraRowSpec` Leaf for `lsFmtWriteSym` (`ExtraRowSpecs.FmtWriteRowSpec`)

Consumer `HookOk` predicate for `core::fmt::write` in `CliGhostHooks.extra`.

Like `AesEncRowSpec`, `core::fmt::write` allocates via `mallocng`, so its
budget-threaded `HookOk` contract is parameterized by the placement-dependent `mallocng`
parameters `(mmpl, brkStart, lim, γ, tp)` and is discharged at the placement-aware top-level
assembly boundary rather than in the placement-free `ExtraRowSpec` bundle.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FmtWriteRowSpec

open Arm64

/-- Row-owned consumer `HookOk` predicate for `lsFmtWriteSym` (`True`; placement-dependent
    `mallocng` budget `HookOk` is discharged at the `mmpl`-parameterized top level). -/
@[expose] def FmtWriteRowSpec (_f : State → State) : Prop :=
  True

theorem FmtWriteRowSpec.intro (f : State → State) : FmtWriteRowSpec f :=
  trivial

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FmtWriteRowSpec

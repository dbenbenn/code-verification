/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64

/-!
# Row-Owned `ExtraRowSpec` Leaf for `lsWriteStdoutSym` (`ExtraRowSpecs.WriteStdoutRowSpec`)

Consumer `HookOk` predicate for `signal_session_io::write_stdout`.

`write_stdout` preserves `.fs` (`sf.fs = s0.fs`) and satisfies `HookFsTraced IsFsC` (writing
only `.stdout` bytes), while its budget-threaded `HookOk` contract (`writeStdoutSpecPlacedSat`) is
parameterized by `(A, lim, stk)` (`1024 ≤ stk ≤ 2 ^ 64`) and supplied at the `MainIoOfPlaced`
boundary.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteStdoutRowSpec

open Arm64

/-- Row-owned consumer `HookOk` predicate for `lsWriteStdoutSym` (`True`; budget-parameterized
    `writeStdoutSpecPlacedSat` `HookOk` is discharged at the `MainIoOfPlaced` boundary). -/
@[expose] def WriteStdoutRowSpec (_f : State → State) : Prop :=
  True

theorem WriteStdoutRowSpec.intro (f : State → State) : WriteStdoutRowSpec f :=
  trivial

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteStdoutRowSpec

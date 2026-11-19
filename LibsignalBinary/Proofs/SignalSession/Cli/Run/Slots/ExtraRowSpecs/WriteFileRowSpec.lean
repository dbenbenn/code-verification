/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64

/-!
# Row-Owned `ExtraRowSpec` Leaf for `lsWriteFileSym` (`ExtraRowSpecs.WriteFileRowSpec`)

Consumer `HookOk` predicate for `signal_session_io::write_file`.

`write_file` mutates `s.fs.files` (`cliIo.wr`) and therefore routes through its dedicated
block-617 `MainIoOfPlaced` / linked-I/O ghost-hook path (like `lsReadFileSym` / `lsReadStdinSym`)
rather than `GhostRowSpecOk`'s `.fs`-preserving `cliExtraGhostSyms` arm; `WriteFileRowSpec` is
provided as a companion `True` row predicate for uniform slot plumbing.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteFileRowSpec

open Arm64

/-- Row-owned consumer `HookOk` predicate for `lsWriteFileSym` (`True`; `writeFileSpecPlacedSatClamped`
    is discharged at the `MainIoOfPlaced` / Block-`617` boundary). -/
@[expose] def WriteFileRowSpec (_f : State → State) : Prop :=
  True

theorem WriteFileRowSpec.intro (f : State → State) : WriteFileRowSpec f :=
  trivial

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteFileRowSpec

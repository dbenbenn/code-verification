/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64 -- proof-setup: allow-public-import

/-!
# `libcrux_hmac::hmac` Consumer `HookOk` Row Arm (`ExtraRowSpecs.LibcruxHmacRowSpec`)

Consumer-contract leaf module for `lsLibcruxHmacSym` in `ExtraGhostSpecs.ExtraRowSpec`.

Unlike the pure non-allocating rows, `libcrux_hmac::hmac` allocates on the `mallocng` heap (`3`
transient `malloc`/`free` pairs), so its concrete `HookSat` witness depends on the active
`mallocng` placement and allocator budget (`libcruxHmacHookMallocng mmpl sha256Compress` in
`hole2_ghFixed`, `libcruxHmacGhost` in `c2LinkedExtraGhosts mmpl`) and is threaded explicitly via
`hHmac` (narrowed with `withLsRet`) on SPQR callers. In `ExtraGhostSpecs.GhostRowSpecOk`, the row
participates in key freshness, `CompleteExtraKeysList`, `fs_eq`, and `HookFsTraced IsFsC` (with
`hookNoop` in `mmpl`-free `pureExtraGhosts`), so its allocator-independent `ExtraRowSpec` arm is
`True`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.LibcruxHmacRowSpec

open Arm64

/-- Allocator-independent `ExtraRowSpec` arm for `lsLibcruxHmacSym` (`fs_eq` and `HookFsTraced`
    are carried by `GhostRowSpecOk`; budget-specific `HookSat` is threaded via `hHmac`). -/
@[expose] def LibcruxHmacRowSpec (_f : State → State) : Prop :=
  True

theorem LibcruxHmacRowSpec.intro (f : State → State) : LibcruxHmacRowSpec f :=
  trivial

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.LibcruxHmacRowSpec

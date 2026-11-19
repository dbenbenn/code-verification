/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity -- proof-setup: allow-public-import

/-!
# `IdentityFiles` Future Drop Symbol and Placeholder Offset

Provides `cliIdFutDropName` (the shared single-`ret` drop glue symbol for CLI store futures) and
the nonzero placeholder offset `cliIdFutDropOff` used in unplaced `StoreKit` baseline specs before
Placed overrides install `[LibsignalPlacement]` block addresses.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

/-- ICF-shared no-op `drop_glue` symbol (a single `ret`) for CLI store futures. -/
abbrev cliIdFutDropName : String :=
  "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"

/-- Nonzero placeholder offset (`< 0x200000`) for unplaced `StoreKit` baseline specs; Placed specs
override `*FutDropOff` with `lsmpl.base 557 - b`. -/
abbrev cliIdFutDropOff : BitVec 64 := 1#64

end CryptoVerification.SignalSession.Cli.KitInst

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp
public import ProofLib.GenDecodes
public import ProofLib.VCGen
public section

namespace CryptoVerification.LibsignalPublicApi.StoreSession

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- The poll of the `store_session` future (`0x42b38`). -/
abbrev storeSessionPollName : String :=
  "<libsignal_session_stores::HookSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"

/-! ## The poll spec -/

/-- Stack of the poll: its 32-byte frame (`0x42b38: stp x29, x30, [sp, #-0x20]!`) and the hook's. -/
abbrev storeSessionPollStack : Nat := storeHookStack + 32

/-- Ghost of a poll call: the future box (`x0`), the sret (`x8`, 48 bytes) and the hook call. -/
structure StorePollCall where
  fut : BitVec 64
  out : BitVec 64
  call : StoreSessionCall

/-- Word 0 of the `Poll<Result<(), SPE>>` the poll writes: `-2` = `Ready(Ok(()))`, else SPE
variant 26 (`ApplicationCallbackError`, `speWord 26`, the niche-encoded `Ready(Err(_))`). -/
@[expose] def pollTag : Except Unit Unit → BitVec 64
  | .ok () => 0xFFFFFFFFFFFFFFFE#64
  | .error () => 0x800000000000001A#64

end CryptoVerification.LibsignalPublicApi.StoreSession

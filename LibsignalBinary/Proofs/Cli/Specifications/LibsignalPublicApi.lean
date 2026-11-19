/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalPublicApi
public import LibsignalBinary.Proofs.SignalSession.Coins.Defs

/-!
# CLI Public API Entry Symbol and `decrypt_signal` Specification

Defines `encryptWithStoresName` and the machine-level specification `decryptSignalSpec` for
`signal_session_ratchet::decrypt_signal` on `Coins` in the CLI session image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

/-! ## Symbol names -/

/-- `message_encrypt::<HookRng>` on `dyn` stores (`(ls_off% "signal_session_ratchet::encrypt")`, 1009 instructions; `src/lib.rs`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName : String := "libsignal_cli_ratchet::encrypt"

end CryptoVerification.LibsignalPublicApi

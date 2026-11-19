/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

/-! ## Symbol names -/

/-- `try_decrypt_with_state::<HookRng>` (image offset `(ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<signal_session_ratchet::Coins>")`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName : String :=
  "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"

/-- `OutgoingTripleRatchet::encrypt::<HookRng>` (`(ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<signal_session_ratchet::Coins>")`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName : String :=
  "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>"

/-- The in-image `spqr::send::<HookRng>` (`(ls_off% "spqr::send::<signal_session_ratchet::Coins>")`, 3436 instructions). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName : String := "spqr::send::<libsignal_cli_ratchet::Coins>"

/-- `session_message_decrypt_signal` (`(ls_off% "signal_session_ratchet::decrypt_signal")`, 2451 instructions): the session crate's
`message_decrypt_signal::<HookRng>` with `try_decrypt_from_record` inlined. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName : String := "libsignal_cli_ratchet::decrypt_signal"

end CryptoVerification.LibsignalTripleRatchet

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccount -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTight -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees -- proof-setup: allow-public-import

/-!
# `DistinctSid` and Tight-Panic `try_decrypt_with_state` Specifications

Variants of `tryDecryptSpec` and `tryDecryptSpecT` relaxing `x.st.remoteIdentity ≠ some x.st.localIdentity`
to `DistinctSid` and refining `onPanic` to `tryDecryptPqOnPanicTight`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession

abbrev _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight

section Smoke
end Smoke

end CryptoVerification.LibsignalTripleRatchet.DecryptPq

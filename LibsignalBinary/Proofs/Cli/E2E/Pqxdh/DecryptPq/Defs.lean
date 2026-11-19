/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import

/-!
# Segment Checkpoints and Contracts for CLI `try_decrypt_with_state::<Coins>`

Callee `subroutine_ok` bundles, checkpoint PCs (`segS1PC` .. `segS9PC`, `errTailPC`,
`retEpiloguePC`), intermediate stack-frame predicates (`S1State` .. `S9State`, `ErrTailState`), and
segment contracts (`S0Spec` .. `S9Spec`, `ErrTailSpec`, `TryDecryptOk`) for
`libsignal_protocol::session_management::try_decrypt_with_state::<signal_session_handshake::Coins>`
in `libsignalSessionImage`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalSession

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName : String :=
  "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.dropChainName : String := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name

/-! ## Callee Symbol Names and `subroutine_ok` Hypotheses -/

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountOk_trap
    (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr isSameAccountName)
    isSameAccountSpec

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ClearUpkOk_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr clearUpkName)
    (clearUpkSpec A)

@[expose] def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.dropChainName)
    (dropChainSpec A)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ChainKeyToPbOk_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr chainKeyToPbName)
    (chainKeyToPbSpec A)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DerivePublicKeyBytesOk_trap
    (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr derivePublicKeyBytesName)
    (derivePublicKeyBytesSpec C.pubKey)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.PublicKeySerializeOk_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr publicKeySerializeName)
    (publicKeySerializeSpec A)

end CryptoVerification.LibsignalTripleRatchet.DecryptPq

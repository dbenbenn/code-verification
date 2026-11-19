/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwned -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym

/-!
# CLI Store Callback Names, Future Boxes, and Bundled Specifications

Symbol names, future-box layouts (`idOwnFutBoxAt`), sret layouts (`idKeyPairOutAt`,
`idRegIdOutAt`), and the `InitStoreCallees` specification bundle for `IdentityFiles` and
`SessionFiles`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## PQ `IdentityFiles` Callback Symbol Names -/

abbrev idKeyPairShimName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"

abbrev idKeyPairPollName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}"

abbrev idRegIdShimName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"

abbrev idRegIdPollName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"

/-- 16-byte future box allocated by `get_identity_key_pair` and `get_local_registration_id` shims:
`self` @0, `state` byte @8, 7 bytes uninitialized. -/
@[expose] def idOwnFutBoxAt (box self : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₈ st) ∗ memRegion (box + 9#64) 7

structure IdOwnPollGhost where
  fut : BitVec 64
  out : BitVec 64
  self : BitVec 64
  own : DirGhost

/-- 72-byte sret of `get_identity_key_pair::{closure#0}`: the closure copies the 72-byte local
`Result<IdentityKeyPair, SignalProtocolError>` (laid out as `identityKeyPairResultAt` in
`Specifications/RecordCodecsBinary.lean`, which `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` writes)
to `out`:
- `.ok kp`: tag byte `0`, the public key bytes @1, the private key bytes @0x21, 7 bytes unspecified.
- `.error ()`: tag byte `1`, 7 bytes unspecified, `RunDrop.SpeOwned` @8 (`InvalidState("read", _)`
  from `Dir::get`, or the error of `try_from`), 16 bytes unspecified. -/
@[expose] def idKeyPairOutAt (A : RustAlloc) (out : BitVec 64) :
    Except Unit IdentityKeyPair → SepProp
  | .ok kp =>
    (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((out + 0x21#64) ↦ₛ kp.privateKey.bytes.toList) ∗ memRegion (out + 0x41#64) 7
  | .error () =>
    (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
      (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (out + 8#64) k) ∗
      memRegion (out + 0x38#64) 16

/-- 48-byte sret of `get_local_registration_id::{closure#0}`:
- `.ok reg`: word 0 `-2`, `u32` `reg` at `out + 8`, 36 bytes uninitialized.
- `.error ()`: `RunDrop.SpeOwned` at `out`: `InvalidState("read", _)` from `Dir::get`, or
  `InvalidState("registration-id", "malformed file")` when the file's length is not 4. -/
@[expose] def idRegIdOutAt (A : RustAlloc) (out : BitVec 64) : Except Unit (BitVec 32) → SepProp
  | .ok reg =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₃₂ reg) ∗ memRegion (out + 12#64) 36
  | .error () => ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A out k

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs

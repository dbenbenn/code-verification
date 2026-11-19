/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecs -- proof-setup: allow-public-import

/-!
# Binary Layouts for Key-Record Codecs (`RecordCodecsBinary`)

**Checked by Lean.** Separation-logic result layouts (`preKeyResultAt`, `identityKeyPairResultAt`,
`identityKeyResultAt`), call ghost (`DecodeGhost`), and serialization layout helpers
(`vecOkResultAt`, `boxU8Owned`) for `<PreKeyRecord>::deserialize`,
`<IdentityKeyPair as TryFrom<&[u8]>>::try_from`, and `<IdentityKey>::decode` (`RecordCodecs.lean`).
-/

public section

namespace CryptoVerification.RecordCodecsBinary

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecs

/-! ## Entry points -/

/-- `<PreKeyRecord>::deserialize` (`protocol/src/state/prekey.rs:44–49`). -/
abbrev preKeyDeserializeName : String :=
  "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"

/-- `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (`protocol/src/identity_key.rs:181–192`). -/
abbrev identityKeyPairTryFromName : String :=
  "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"

/-- `<IdentityKey>::decode` (`protocol/src/identity_key.rs:52–55`). -/
abbrev identityKeyDecodeName : String :=
  "<libsignal_protocol::identity_key::IdentityKey>::decode"

/-! ## Layouts -/

/-- **A `PreKeyRecord` at `a` (56 bytes)**: `public_key: Vec<u8>` @0, `private_key: Vec<u8>` @0x18,
`id: u32` @0x30, 4 bytes padding. Each `Vec` is owned, with any capacity and buffer (prost's
`bytes::merge` replaces the contents and may keep a larger buffer); `vecU8At`'s `cap < 2^63`
keeps word 0 off the `Err` niche `errTag`. -/
@[expose] def preKeyRecordAt (A : RustAlloc) (a : BitVec 64) (r : PreKeyRecord) : SepProp :=
  vecU8 A a r.preKey.publicKey ∗ vecU8 A (a + 0x18#64) r.preKey.privateKey ∗
    ((a + 0x30#64) ↦₃₂ r.preKey.id) ∗ memRegion (a + 0x34#64) 4

/-- `Result<PreKeyRecord, SignalProtocolError>` at `r` (56 bytes): `Ok` = a fresh owned record at
`r`; `Err` = `errResultAt` (word 0 `errTag`, the SPE at +8). -/
@[expose] def preKeyResultAt (A : RustAlloc) (r : BitVec 64) :
    Except SignalProtocolError PreKeyRecord → SepProp
  | .ok rec => preKeyRecordAt A r rec
  | .error e => errResultAt A [] 56 r e

/-- `Result<IdentityKeyPair, SignalProtocolError>` at `r` (72 bytes): `Ok` = tag byte `0`, the
public key bytes @1, the private key bytes @0x21, 7 bytes unspecified; `Err` = tag byte `1`,
7 bytes unspecified, the SPE @8, 16 bytes unspecified. -/
@[expose] def identityKeyPairResultAt (A : RustAlloc) (r : BitVec 64) :
    Except SignalProtocolError IdentityKeyPair → SepProp
  | .ok kp =>
    (r ↦₈ 0#8) ∗ ((r + 1#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((r + 0x21#64) ↦ₛ kp.privateKey.bytes.toList) ∗ memRegion (r + 0x41#64) 7
  | .error e =>
    (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗ speAt A [] (r + 8#64) e ∗ memRegion (r + 0x38#64) 16

/-- `Result<IdentityKey, SignalProtocolError>` at `r` (48 bytes): `Ok` = `okTagVec` (`-2`), the 32
key bytes @8, 8 bytes unspecified; `Err` = the SPE in place. -/
@[expose] def identityKeyResultAt (A : RustAlloc) (r : BitVec 64) :
    Except SignalProtocolError IdentityKey → SepProp
  | .ok ik =>
    (r ↦₆₄ okTagVec) ∗ ((r + 8#64) ↦ₛ ik.publicKey.bytes.toList) ∗ memRegion (r + 0x28#64) 8
  | .error e => speAt A [] r e

/-! ## Binding specs -/

/-- Ghost of a decode call: the input bytes (`x0`, `x1`) and the sret (`x8`). -/
structure DecodeGhost where
  bytesA : BitVec 64
  bytes : List (BitVec 8)
  ret : BitVec 64

/-! ## Serialization layout helpers -/

/-- `Result<Vec<u8>, SignalProtocolError>` at `r` (48 bytes) holding `Ok bs`: `okTagVec` @0, an
owned `Vec<u8>` @8, 16 bytes unspecified (the `Ok` arm of `vecResultAt`). -/
@[expose] def vecOkResultAt (A : RustAlloc) (r : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  vecResultAt A r (.ok bs)

/-- The heap part of an owned `Box<[u8]>` with pointer `ptr` holding `bs` (`boxU8At` without its
16-byte header): a live block of exactly `bs.length` bytes with alignment 1, or, if `bs` is empty,
a dangling non-null pointer and no block. -/
@[expose] def boxU8Owned (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗ (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))

end CryptoVerification.RecordCodecsBinary

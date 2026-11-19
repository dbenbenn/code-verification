/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module


/-!
# Memory Layout Constants for Core SPQR V1 Protobuf Structs

Byte sizes, alignments, field offsets, and `Option` niche encodings for the `prost` 0.14.4 structs
`ChainParams`, `EpochDirection`, `Epoch`, `Chain`, `Authenticator`, and `VersionNegotiation` in
`libsignalSessionCode`.
-/

public section

namespace CryptoVerification.SpqrV1.ProtoRepr

/-! ## Function Entry Offsets in `libsignalSessionCode` -/

/-! ## 1. `ChainParams` (`8` B, align `4`) and `Option<ChainParams>` (`12` B, align `4`)

`ChainParams` stores `max_jump: u32` at `+0x00` (tag 1) and `max_ooo_keys: u32` at `+0x04` (tag 2);
`Option<ChainParams>` prepends a `u32` discriminant (`0` = `None`, `1` = `Some`) at `+0x00`. -/

/-! ## 2. `EpochDirection` (`56` B, align `8`)

Stores `next: Vec<u8>` at `+0x00..+0x18` (tag 2), `prev: Vec<u8>` at `+0x18..+0x30` (tag 3),
`ctr: u32` at `+0x30` (tag 1), and 4 bytes of trailing padding at `+0x34..+0x38`.
`Option<EpochDirection>` uses the `next.cap = 0xFFFFFFFFFFFFFFFF` niche at `+0x00` for `None`. -/

/-! ## 3. `chain::Epoch` (`112` B, align `8`)

Stores `send: Option<EpochDirection>` at `+0x00..+0x38` (tag 1) and `recv: Option<EpochDirection>`
at `+0x38..+0x70` (tag 2), with `Vec<Epoch>` element stride `0x70 = 112` bytes. -/

/-- Byte size of `spqr::proto::pq_ratchet::chain::Epoch` (`112` bytes = `0x70`). -/
@[expose] def chainEpochPBSize : Nat := 112

/-- Byte size / element stride of `Epoch` as a 64-bit bitvector (`0x70#64`). -/
def chainEpochPBStride : BitVec 64 := 0x70#64

/-! ## 4. `Chain` (`80` B, align `8`)

Stores `links: Vec<Epoch>` at `+0x00..+0x18` (tag 3), `next_root: Vec<u8>` at `+0x18..+0x30`
(tag 4), `current_epoch: u64` at `+0x30` (tag 2), `send_epoch: u64` at `+0x38` (tag 5),
`params: Option<ChainParams>` at `+0x40..+0x4c` (tag 6), and `direction: i32` at `+0x4c` (tag 1).
`Option<Chain>` uses the `links.cap = 0xFFFFFFFFFFFFFFFF` niche at `+0x00` for `None`. -/

/-- Byte size of `spqr::proto::pq_ratchet::Chain` (`80` bytes = `0x50`). -/
@[expose] def chainPBSize : Nat := 80

/-- Byte alignment of `Chain` (`8` bytes). -/
def chainPBAlign : BitVec 64 := 8#64

/-! ## 5. `Authenticator` (`48` B, align `8`)

Stores `root_key: Vec<u8>` at `+0x00..+0x18` (tag 1) and `mac_key: Vec<u8>` at `+0x18..+0x30`
(tag 2). -/

/-! ## 6. `VersionNegotiation` (`48` B, align `8`)

Stores `auth_key: Vec<u8>` at `+0x00..+0x18` (tag 1), `chain_params: Option<ChainParams>` at
`+0x18..+0x24` (tag 4), `direction: i32` at `+0x24` (tag 2), `min_version: i32` at `+0x28`
(tag 3), and 4 bytes of padding at `+0x2c..+0x30`. `Option<VersionNegotiation>` uses the
`auth_key.cap = 0xFFFFFFFFFFFFFFFF` niche at `+0x00` for `None`. -/

end CryptoVerification.SpqrV1.ProtoRepr

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref -- proof-setup: allow-public-import
meta import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
meta import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref

/-!
# `CryptoGames.HMAC` Adapter, FIPS 180-4 & RFC 4231 Test Vectors, and State-Bytes Lemmas

Connects `Sha256Ref.sha256CompressBlock` to `CryptoGames.HMAC.ShaState` (`sha256CompressState`),
`CryptoGames.HMAC.sha256With`, `CryptoGames.HMAC.hmacWith`, and `LibsignalHmac.shaStateBytes`.
Checks official NIST FIPS 180-4 SHA-256 vectors (`[]`, `"abc"`, 448-bit two-block message, plus
55/63/64-byte padding boundaries) and RFC 4231 HMAC-SHA-256 Test Cases 1, 2, 3, and 6 via `#guard`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState toBEBytes chunks64 sha256With hmacWith)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref
  (beBytesOfU32 sha256CompressBlock)

/-! ## 1. `CryptoGames.HMAC.ShaState` Adapter & Block-Folding Lemmas -/

theorem sha256CompressBlock_length (st : List (BitVec 32)) (block : List (BitVec 8)) :
    (sha256CompressBlock st block).length = 8 := by
  simp [sha256CompressBlock]

/-- FIPS 180-4 SHA-256 block compression typed over `CryptoGames.HMAC.ShaState`
(`List.Vector (BitVec 32) 8`), instantiating `W.C.F` for both `sha2::sha256::compress256` and
`libcrux_hmac::hmac`. -/
@[expose] def sha256CompressState (st : ShaState) (block : List (BitVec 8)) : ShaState :=
  ⟨sha256CompressBlock st.toList block, sha256CompressBlock_length st.toList block⟩

@[simp]
theorem sha256CompressState_toList (st : ShaState) (block : List (BitVec 8)) :
    (sha256CompressState st block).toList = sha256CompressBlock st.toList block :=
  rfl

private theorem extractLsb'_8_eq_truncate {n : Nat} (w : BitVec n) (s : Nat) :
    w.extractLsb' s 8 = (w >>> s).truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem toBEBytes_4_eq_beBytesOfU32 (w : BitVec 32) :
    toBEBytes 4 w = beBytesOfU32 w := by
  unfold toBEBytes beBytesOfU32
  change [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8] =
    [(w >>> 24).truncate 8, (w >>> 16).truncate 8, (w >>> 8).truncate 8, (w >>> 0).truncate 8]
  simp only [extractLsb'_8_eq_truncate]

theorem chunks64_eq_map_range (bs : List (BitVec 8)) :
    chunks64 bs = (List.range (bs.length / 64)).map fun b => (bs.drop (64 * b)).take 64 := by
  apply List.ext_getElem
  · simp [chunks64]
  · intro i h1 h2
    simp [chunks64]

theorem foldl_sha256CompressState_toList (blocks : List (List (BitVec 8))) (st : ShaState) :
    (blocks.foldl sha256CompressState st).toList =
      blocks.foldl sha256CompressBlock st.toList := by
  induction blocks generalizing st with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, ih (sha256CompressState st b), sha256CompressState_toList]

/-! ## 2. NIST FIPS 180-4 SHA-256 & RFC 4231 HMAC-SHA-256 Test Vectors (`#guard`) -/

-- NIST FIPS 180-4 official SHA-256 test vectors (empty, "abc", and 448-bit two-block message):
#guard sha256With sha256CompressState [] == [
  0xe3#8, 0xb0#8, 0xc4#8, 0x42#8, 0x98#8, 0xfc#8, 0x1c#8, 0x14#8,
  0x9a#8, 0xfb#8, 0xf4#8, 0xc8#8, 0x99#8, 0x6f#8, 0xb9#8, 0x24#8,
  0x27#8, 0xae#8, 0x41#8, 0xe4#8, 0x64#8, 0x9b#8, 0x93#8, 0x4c#8,
  0xa4#8, 0x95#8, 0x99#8, 0x1b#8, 0x78#8, 0x52#8, 0xb8#8, 0x55#8
]

#guard sha256With sha256CompressState [0x61#8, 0x62#8, 0x63#8] == [
  0xba#8, 0x78#8, 0x16#8, 0xbf#8, 0x8f#8, 0x01#8, 0xcf#8, 0xea#8,
  0x41#8, 0x41#8, 0x40#8, 0xde#8, 0x5d#8, 0xae#8, 0x22#8, 0x23#8,
  0xb0#8, 0x03#8, 0x61#8, 0xa3#8, 0x96#8, 0x17#8, 0x7a#8, 0x9c#8,
  0xb4#8, 0x10#8, 0xff#8, 0x61#8, 0xf2#8, 0x00#8, 0x15#8, 0xad#8
]

#guard sha256With sha256CompressState
    ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8.toList.map
      fun b => BitVec.ofNat 8 b.toNat) == [
  0x24#8, 0x8d#8, 0x6a#8, 0x61#8, 0xd2#8, 0x06#8, 0x38#8, 0xb8#8,
  0xe5#8, 0xc0#8, 0x26#8, 0x93#8, 0x0c#8, 0x3e#8, 0x60#8, 0x39#8,
  0xa3#8, 0x3c#8, 0xe4#8, 0x59#8, 0x64#8, 0xff#8, 0x21#8, 0x67#8,
  0xf6#8, 0xec#8, 0xed#8, 0xd4#8, 0x19#8, 0xdb#8, 0x06#8, 0xc1#8
]

-- SHA-256 boundary length 55 (`55 × 'a'`: max 1-block message, `zeroLen = 0`).
#guard sha256With sha256CompressState (List.replicate 55 0x61#8) ==
  [0x9f#8, 0x43#8, 0x90#8, 0xf8#8, 0xd3#8, 0x0c#8, 0x2d#8, 0xd9#8,
   0x2e#8, 0xc9#8, 0xf0#8, 0x95#8, 0xb6#8, 0x5e#8, 0x2b#8, 0x9a#8,
   0xe9#8, 0xb0#8, 0xa9#8, 0x25#8, 0xa5#8, 0x25#8, 0x8e#8, 0x24#8,
   0x1c#8, 0x9f#8, 0x1e#8, 0x91#8, 0x0f#8, 0x73#8, 0x43#8, 0x18#8]

-- SHA-256 boundary length 63 (`63 × 'a'`: 2-block message with `0x80` at byte 63, `zeroLen = 56`).
#guard sha256With sha256CompressState (List.replicate 63 0x61#8) ==
  [0x7d#8, 0x3e#8, 0x74#8, 0xa0#8, 0x5d#8, 0x7d#8, 0xb1#8, 0x5b#8,
   0xce#8, 0x4a#8, 0xd9#8, 0xec#8, 0x06#8, 0x58#8, 0xea#8, 0x98#8,
   0xe3#8, 0xf0#8, 0x6e#8, 0xee#8, 0xcf#8, 0x16#8, 0xb4#8, 0xc6#8,
   0xff#8, 0xf2#8, 0xda#8, 0x45#8, 0x7d#8, 0xdc#8, 0x2f#8, 0x34#8]

-- SHA-256 boundary length 64 (`64 × 'a'`: exact 1-block payload + full 64-byte padding block).
#guard sha256With sha256CompressState (List.replicate 64 0x61#8) ==
  [0xff#8, 0xe0#8, 0x54#8, 0xfe#8, 0x7a#8, 0xe0#8, 0xcb#8, 0x6d#8,
   0xc6#8, 0x5c#8, 0x3a#8, 0xf9#8, 0xb6#8, 0x1d#8, 0x52#8, 0x09#8,
   0xf4#8, 0x39#8, 0x85#8, 0x1d#8, 0xb4#8, 0x3d#8, 0x0b#8, 0xa5#8,
   0x99#8, 0x73#8, 0x37#8, 0xdf#8, 0x15#8, 0x46#8, 0x68#8, 0xeb#8]

-- RFC 4231 Test Case 1 (`key = 20 × 0x0b`, `data = "Hi There"`).
#guard hmacWith sha256CompressState
  (List.replicate 20 0x0b#8)
  [0x48#8, 0x69#8, 0x20#8, 0x54#8, 0x68#8, 0x65#8, 0x72#8, 0x65#8] ==
  [0xb0#8, 0x34#8, 0x4c#8, 0x61#8, 0xd8#8, 0xdb#8, 0x38#8, 0x53#8,
   0x5c#8, 0xa8#8, 0xaf#8, 0xce#8, 0xaf#8, 0x0b#8, 0xf1#8, 0x2b#8,
   0x88#8, 0x1d#8, 0xc2#8, 0x00#8, 0xc9#8, 0x83#8, 0x3d#8, 0xa7#8,
   0x26#8, 0xe9#8, 0x37#8, 0x6c#8, 0x2e#8, 0x32#8, 0xcf#8, 0xf7#8]

-- RFC 4231 Test Case 2 (`key = "Jefe"`, `data = "what do ya want for nothing?"`).
#guard hmacWith sha256CompressState
  [0x4a#8, 0x65#8, 0x66#8, 0x65#8]
  [0x77#8, 0x68#8, 0x61#8, 0x74#8, 0x20#8, 0x64#8, 0x6f#8, 0x20#8,
   0x79#8, 0x61#8, 0x20#8, 0x77#8, 0x61#8, 0x6e#8, 0x74#8, 0x20#8,
   0x66#8, 0x6f#8, 0x72#8, 0x20#8, 0x6e#8, 0x6f#8, 0x74#8, 0x68#8,
   0x69#8, 0x6e#8, 0x67#8, 0x3f#8] ==
  [0x5b#8, 0xdc#8, 0xc1#8, 0x46#8, 0xbf#8, 0x60#8, 0x75#8, 0x4e#8,
   0x6a#8, 0x04#8, 0x24#8, 0x26#8, 0x08#8, 0x95#8, 0x75#8, 0xc7#8,
   0x5a#8, 0x00#8, 0x3f#8, 0x08#8, 0x9d#8, 0x27#8, 0x39#8, 0x83#8,
   0x9d#8, 0xec#8, 0x58#8, 0xb9#8, 0x64#8, 0xec#8, 0x38#8, 0x43#8]

-- RFC 4231 Test Case 3 (`key = 20 × 0xaa`, `data = 50 × 0xdd`).
#guard hmacWith sha256CompressState
  (List.replicate 20 0xaa#8)
  (List.replicate 50 0xdd#8) ==
  [0x77#8, 0x3e#8, 0xa9#8, 0x1e#8, 0x36#8, 0x80#8, 0x0e#8, 0x46#8,
   0x85#8, 0x4d#8, 0xb8#8, 0xeb#8, 0xd0#8, 0x91#8, 0x81#8, 0xa7#8,
   0x29#8, 0x59#8, 0x09#8, 0x8b#8, 0x3e#8, 0xf8#8, 0xc1#8, 0x22#8,
   0xd9#8, 0x63#8, 0x55#8, 0x14#8, 0xce#8, 0xd5#8, 0x65#8, 0xfe#8]

-- RFC 4231 Test Case 6 (`key = 131 × 0xaa` > 64 B, exercising `64 < k.length` key hashing).
#guard hmacWith sha256CompressState
  (List.replicate 131 0xaa#8)
  [0x54#8, 0x65#8, 0x73#8, 0x74#8, 0x20#8, 0x55#8, 0x73#8, 0x69#8,
   0x6e#8, 0x67#8, 0x20#8, 0x4c#8, 0x61#8, 0x72#8, 0x67#8, 0x65#8,
   0x72#8, 0x20#8, 0x54#8, 0x68#8, 0x61#8, 0x6e#8, 0x20#8, 0x42#8,
   0x6c#8, 0x6f#8, 0x63#8, 0x6b#8, 0x2d#8, 0x53#8, 0x69#8, 0x7a#8,
   0x65#8, 0x20#8, 0x4b#8, 0x65#8, 0x79#8, 0x20#8, 0x2d#8, 0x20#8,
   0x48#8, 0x61#8, 0x73#8, 0x68#8, 0x20#8, 0x4b#8, 0x65#8, 0x79#8,
   0x20#8, 0x46#8, 0x69#8, 0x72#8, 0x73#8, 0x74#8] ==
  [0x60#8, 0xe4#8, 0x31#8, 0x59#8, 0x1e#8, 0xe0#8, 0xb6#8, 0x7f#8,
   0x0d#8, 0x8a#8, 0x26#8, 0xaa#8, 0xcb#8, 0xf5#8, 0xb7#8, 0x7f#8,
   0x8e#8, 0x0b#8, 0xc6#8, 0x21#8, 0x37#8, 0x28#8, 0xc5#8, 0x14#8,
   0x05#8, 0x46#8, 0x04#8, 0x0f#8, 0x0e#8, 0xe3#8, 0x7f#8, 0x54#8]

/-! ## 3. Little-Endian 32-Bit Chaining-State Encoding (`shaStateBytes`) -/

@[simp]
theorem toLEBytes_4_eq_unpack32 (w : BitVec 32) :
    toLEBytes 4 w = unpack32 w := rfl

theorem pointsToBytes_toLEBytes_4 (a : BitVec 64) (w : BitVec 32) :
    (a ↦ₛ toLEBytes 4 w) = (a ↦₃₂ w) :=
  (pointsTo32_eq_pointsToBytes a w).symm

theorem pointsToBytes_shaStateBytes_list (a : BitVec 64) (st : List (BitVec 32))
    (hst : st.length = 8) :
    (a ↦ₛ st.flatMap (toLEBytes 4)) =
      ((a ↦₃₂ st.getD 0 0#32) ∗
       ((a + 4#64) ↦₃₂ st.getD 1 0#32) ∗
       ((a + 8#64) ↦₃₂ st.getD 2 0#32) ∗
       ((a + 12#64) ↦₃₂ st.getD 3 0#32) ∗
       ((a + 16#64) ↦₃₂ st.getD 4 0#32) ∗
       ((a + 20#64) ↦₃₂ st.getD 5 0#32) ∗
       ((a + 24#64) ↦₃₂ st.getD 6 0#32) ∗
       ((a + 28#64) ↦₃₂ st.getD 7 0#32)) := by
  rcases st with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hst)
  change (a ↦ₛ (toLEBytes 4 w0 ++ (toLEBytes 4 w1 ++ (toLEBytes 4 w2 ++ (toLEBytes 4 w3 ++
    (toLEBytes 4 w4 ++ (toLEBytes 4 w5 ++ (toLEBytes 4 w6 ++ (toLEBytes 4 w7 ++ []))))))))) = _
  rw [List.append_nil]
  repeat rw [pointsToBytes_append, toLEBytes_4_eq_unpack32, unpack32_length, ← pointsTo32_eq_pointsToBytes]
  rw [toLEBytes_4_eq_unpack32, ← pointsTo32_eq_pointsToBytes]
  simp only [List.getD_cons_zero, List.getD_cons_succ, BitVec.add_assoc, BitVec.reduceAdd]

theorem pointsToBytes_shaStateBytes (a : BitVec 64) (st : ShaState) :
    (a ↦ₛ shaStateBytes st) =
      ((a ↦₃₂ st.toList.getD 0 0#32) ∗
       ((a + 4#64) ↦₃₂ st.toList.getD 1 0#32) ∗
       ((a + 8#64) ↦₃₂ st.toList.getD 2 0#32) ∗
       ((a + 12#64) ↦₃₂ st.toList.getD 3 0#32) ∗
       ((a + 16#64) ↦₃₂ st.toList.getD 4 0#32) ∗
       ((a + 20#64) ↦₃₂ st.toList.getD 5 0#32) ∗
       ((a + 24#64) ↦₃₂ st.toList.getD 6 0#32) ∗
       ((a + 28#64) ↦₃₂ st.toList.getD 7 0#32)) :=
  pointsToBytes_shaStateBytes_list a st.toList st.2

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math

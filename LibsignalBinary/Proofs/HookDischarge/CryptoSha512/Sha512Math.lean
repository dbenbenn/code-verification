/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref -- proof-setup: allow-public-import
meta import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
meta import LibsignalBinary.Specifications.SignalPqxdh.Model
meta import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
meta import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
meta import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref

/-!
# `Sha512State` Adapter, NIST FIPS 180-4 SHA-512 Test Vectors, and State-Bytes Lemmas

Connects `Sha512Ref.sha512CompressState` to `PqxdhHooksCommon` (`chunks128`, `sha512StateBytesLE`),
`PqxdhModelLink` (`sha512StateOf`, `sha512StateBytesBE`, `blockLevelPrims`, `modelPrims`), and
`SignalPqxdh.sha512Ref`. Checks official NIST FIPS 180-4 SHA-512 test vectors (`[]`, `"abc"`,
896-bit two-block message, and 111/127/128-byte padding boundaries) via `#guard` on both
`sha512With sha512CompressState` and `SignalPqxdh.sha512Ref`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Math

open Arm64 ProofLib
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.E2E
  (Sha512State chunks128 sha512StateBytesLE sha512StateOf sha512StateBytesBE ofU8)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref
  (beBytesOfU64 sha512CompressBlock sha512CompressState sha512CompressState_toList)

/-! ## 1. Pure FIPS 180-4 SHA-512 Merkle-Damgård Wrapper & Block-Folding Lemmas -/

/-- SHA-512 initial hash value `H⁽⁰⁾` (FIPS 180-4 §5.3.5). -/
@[expose] def sha512IV : Sha512State :=
  ⟨[0x6a09e667f3bcc908#64, 0xbb67ae8584caa73b#64, 0x3c6ef372fe94f82b#64, 0xa54ff53a5f1d36f1#64,
    0x510e527fade682d1#64, 0x9b05688c2b3e6c1f#64, 0x1f83d9abfb41bd6b#64, 0x5be0cd19137e2179#64], rfl⟩

/-- SHA-512 message padding (FIPS 180-4 §5.1.2): `m ‖ 0x80 ‖ 0…0 ‖ BE₁₂₈(8·|m| mod 2¹²⁸)`, padded
to a multiple of 128 bytes. -/
@[expose] def sha512Pad (m : List (BitVec 8)) : List (BitVec 8) :=
  m ++ [0x80#8] ++ List.replicate ((239 - m.length % 128) % 128) 0#8 ++
    toBEBytes 16 (BitVec.ofNat 128 (8 * m.length))

/-- SHA-512 of `m` with compression function `F` (FIPS 180-4 §6.4), outputting 64 big-endian
bytes. -/
@[expose] def sha512With (F : Sha512State → List (BitVec 8) → Sha512State)
    (m : List (BitVec 8)) : List (BitVec 8) :=
  ((chunks128 (sha512Pad m)).foldl F sha512IV).toList.flatMap (toBEBytes 8)

private theorem extractLsb'_8_eq_truncate64 {n : Nat} (w : BitVec n) (s : Nat) :
    w.extractLsb' s 8 = (w >>> s).truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem toBEBytes_8_eq_beBytesOfU64 (w : BitVec 64) :
    toBEBytes 8 w = beBytesOfU64 w := by
  unfold toBEBytes beBytesOfU64
  change [w.extractLsb' 56 8, w.extractLsb' 48 8, w.extractLsb' 40 8, w.extractLsb' 32 8,
          w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8] =
    [(w >>> 56).truncate 8, (w >>> 48).truncate 8, (w >>> 40).truncate 8, (w >>> 32).truncate 8,
     (w >>> 24).truncate 8, (w >>> 16).truncate 8, (w >>> 8).truncate 8, (w >>> 0).truncate 8]
  simp only [extractLsb'_8_eq_truncate64]

theorem chunks128_eq_map_range (bs : List (BitVec 8)) :
    chunks128 bs = (List.range (bs.length / 128)).map fun b => (bs.drop (128 * b)).take 128 := by
  apply List.ext_getElem
  · simp [chunks128]
  · intro i h1 h2
    simp [chunks128]

theorem foldl_sha512CompressState_toList (blocks : List (List (BitVec 8))) (st : Sha512State) :
    (blocks.foldl sha512CompressState st).toList =
      blocks.foldl sha512CompressBlock st.toList := by
  induction blocks generalizing st with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, ih (sha512CompressState st b), sha512CompressState_toList]

/-! ## 2. NIST FIPS 180-4 SHA-512 Test Vectors (`#guard`) & `SignalPqxdh.sha512Ref` Cross-Check -/

-- 1. NIST FIPS 180-4 official SHA-512 empty message `""`:
#guard sha512With sha512CompressState [] == [
  0xcf#8, 0x83#8, 0xe1#8, 0x35#8, 0x7e#8, 0xef#8, 0xb8#8, 0xbd#8,
  0xf1#8, 0x54#8, 0x28#8, 0x50#8, 0xd6#8, 0x6d#8, 0x80#8, 0x07#8,
  0xd6#8, 0x20#8, 0xe4#8, 0x05#8, 0x0b#8, 0x57#8, 0x15#8, 0xdc#8,
  0x83#8, 0xf4#8, 0xa9#8, 0x21#8, 0xd3#8, 0x6c#8, 0xe9#8, 0xce#8,
  0x47#8, 0xd0#8, 0xd1#8, 0x3c#8, 0x5d#8, 0x85#8, 0xf2#8, 0xb0#8,
  0xff#8, 0x83#8, 0x18#8, 0xd2#8, 0x87#8, 0x7e#8, 0xec#8, 0x2f#8,
  0x63#8, 0xb9#8, 0x31#8, 0xbd#8, 0x47#8, 0x41#8, 0x7a#8, 0x81#8,
  0xa5#8, 0x38#8, 0x32#8, 0x7a#8, 0xf9#8, 0x27#8, 0xda#8, 0x3e#8
]

-- 2. NIST FIPS 180-4 official SHA-512 `"abc"` (24-bit single-block message):
#guard sha512With sha512CompressState [0x61#8, 0x62#8, 0x63#8] == [
  0xdd#8, 0xaf#8, 0x35#8, 0xa1#8, 0x93#8, 0x61#8, 0x7a#8, 0xba#8,
  0xcc#8, 0x41#8, 0x73#8, 0x49#8, 0xae#8, 0x20#8, 0x41#8, 0x31#8,
  0x12#8, 0xe6#8, 0xfa#8, 0x4e#8, 0x89#8, 0xa9#8, 0x7e#8, 0xa2#8,
  0x0a#8, 0x9e#8, 0xee#8, 0xe6#8, 0x4b#8, 0x55#8, 0xd3#8, 0x9a#8,
  0x21#8, 0x92#8, 0x99#8, 0x2a#8, 0x27#8, 0x4f#8, 0xc1#8, 0xa8#8,
  0x36#8, 0xba#8, 0x3c#8, 0x23#8, 0xa3#8, 0xfe#8, 0xeb#8, 0xbd#8,
  0x45#8, 0x4d#8, 0x44#8, 0x23#8, 0x64#8, 0x3c#8, 0xe8#8, 0x0e#8,
  0x2a#8, 0x9a#8, 0xc9#8, 0x4f#8, 0xa5#8, 0x4c#8, 0xa4#8, 0x9f#8
]

-- 3. NIST FIPS 180-4 official SHA-512 896-bit (112-byte) two-block message:
#guard sha512With sha512CompressState
    ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu".toUTF8.toList.map
      fun b => BitVec.ofNat 8 b.toNat) == [
  0x8e#8, 0x95#8, 0x9b#8, 0x75#8, 0xda#8, 0xe3#8, 0x13#8, 0xda#8,
  0x8c#8, 0xf4#8, 0xf7#8, 0x28#8, 0x14#8, 0xfc#8, 0x14#8, 0x3f#8,
  0x8f#8, 0x77#8, 0x79#8, 0xc6#8, 0xeb#8, 0x9f#8, 0x7f#8, 0xa1#8,
  0x72#8, 0x99#8, 0xae#8, 0xad#8, 0xb6#8, 0x88#8, 0x90#8, 0x18#8,
  0x50#8, 0x1d#8, 0x28#8, 0x9e#8, 0x49#8, 0x00#8, 0xf7#8, 0xe4#8,
  0x33#8, 0x1b#8, 0x99#8, 0xde#8, 0xc4#8, 0xb5#8, 0x43#8, 0x3a#8,
  0xc7#8, 0xd3#8, 0x29#8, 0xee#8, 0xb6#8, 0xdd#8, 0x26#8, 0x54#8,
  0x5e#8, 0x96#8, 0xe5#8, 0x5b#8, 0x87#8, 0x4b#8, 0xe9#8, 0x09#8
]

-- 4. SHA-512 boundary length 111 (`111 × 'a'`: max 1-block message, `zeroLen = 0`):
#guard sha512With sha512CompressState (List.replicate 111 0x61#8) == [
  0xfa#8, 0x91#8, 0x21#8, 0xc7#8, 0xb3#8, 0x2b#8, 0x9e#8, 0x01#8,
  0x73#8, 0x3d#8, 0x03#8, 0x4c#8, 0xfc#8, 0x78#8, 0xcb#8, 0xf6#8,
  0x7f#8, 0x92#8, 0x6c#8, 0x7e#8, 0xd8#8, 0x3e#8, 0x82#8, 0x20#8,
  0x0e#8, 0xf8#8, 0x68#8, 0x18#8, 0x19#8, 0x69#8, 0x21#8, 0x76#8,
  0x0b#8, 0x4b#8, 0xef#8, 0xf4#8, 0x84#8, 0x04#8, 0xdf#8, 0x81#8,
  0x1b#8, 0x95#8, 0x38#8, 0x28#8, 0x27#8, 0x44#8, 0x61#8, 0x67#8,
  0x3c#8, 0x68#8, 0xd0#8, 0x4e#8, 0x29#8, 0x7b#8, 0x0e#8, 0xb7#8,
  0xb2#8, 0xb4#8, 0xd6#8, 0x0f#8, 0xc6#8, 0xb5#8, 0x66#8, 0xa2#8
]

-- 5. SHA-512 boundary length 127 (`127 × 'a'`: 2-block message with `0x80` at byte 127, `zeroLen = 112`):
#guard sha512With sha512CompressState (List.replicate 127 0x61#8) == [
  0x82#8, 0x86#8, 0x13#8, 0x96#8, 0x8b#8, 0x50#8, 0x1d#8, 0xc0#8,
  0x0a#8, 0x97#8, 0xe0#8, 0x8c#8, 0x73#8, 0xb1#8, 0x18#8, 0xaa#8,
  0x88#8, 0x76#8, 0xc2#8, 0x6b#8, 0x8a#8, 0xac#8, 0x93#8, 0xdf#8,
  0x12#8, 0x85#8, 0x02#8, 0xab#8, 0x36#8, 0x0f#8, 0x91#8, 0xba#8,
  0xb5#8, 0x0a#8, 0x51#8, 0xe0#8, 0x88#8, 0x76#8, 0x9a#8, 0x5c#8,
  0x1e#8, 0xff#8, 0x47#8, 0x82#8, 0xac#8, 0xe1#8, 0x47#8, 0xdc#8,
  0xe3#8, 0x64#8, 0x25#8, 0x54#8, 0x19#8, 0x98#8, 0x76#8, 0x37#8,
  0x42#8, 0x91#8, 0xf5#8, 0xd9#8, 0x21#8, 0x62#8, 0x95#8, 0x02#8
]

-- 6. SHA-512 boundary length 128 (`128 × 'a'`: exact 1-block payload + full 128-byte padding block):
#guard sha512With sha512CompressState (List.replicate 128 0x61#8) == [
  0xb7#8, 0x3d#8, 0x19#8, 0x29#8, 0xaa#8, 0x61#8, 0x59#8, 0x34#8,
  0xe6#8, 0x1a#8, 0x87#8, 0x15#8, 0x96#8, 0xb3#8, 0xf3#8, 0xb3#8,
  0x33#8, 0x59#8, 0xf4#8, 0x2b#8, 0x81#8, 0x75#8, 0x60#8, 0x2e#8,
  0x89#8, 0xf7#8, 0xe0#8, 0x6e#8, 0x5f#8, 0x65#8, 0x8a#8, 0x24#8,
  0x36#8, 0x67#8, 0x80#8, 0x7e#8, 0xd3#8, 0x00#8, 0x31#8, 0x4b#8,
  0x95#8, 0xca#8, 0xcd#8, 0xd5#8, 0x79#8, 0xf3#8, 0xe3#8, 0x3a#8,
  0xbd#8, 0xfb#8, 0xe3#8, 0x51#8, 0x90#8, 0x95#8, 0x19#8, 0xa8#8,
  0x46#8, 0xd4#8, 0x65#8, 0xc5#8, 0x95#8, 0x82#8, 0xf3#8, 0x21#8
]

-- End-to-end check that `SignalPqxdh.sha512Ref` with `PqxdhModelLink`'s `sha512Compress` adapter
-- (`sha512StateBytesBE (sha512CompressState (sha512StateOf st) (ofU8 blk))`) agrees on NIST vectors:
private meta def sha512ModelRefPrims : SignalPqxdh.Primitives where
  x25519 _ _ := []
  x25519Base _ := []
  isCanonical _ := false
  sigPkGen _ := []
  sigSign _ _ _ := []
  sigVerify _ _ _ := false
  sha512 _ := []
  scalarMul _ _ := []
  scalarAdd _ _ := []
  scalarFromBytesModOrder _ := []
  scalarFromWide _ := []
  montToEd _ _ := none
  isTorsionFree _ := false
  edNeg _ := VerifiedLibraries.Common.edZero
  doubleScalarMulBasepoint _ _ _ := VerifiedLibraries.Common.edZero
  compress _ := []
  kemKeyGen _ := ([], [])
  kemEncaps _ _ := none
  kemDecaps _ _ := none
  hkdfDerive96 _ := default
  rootCreateChain _ _ := ([], [])
  chainKdfSeed _ := []
  chainKdfNext _ := []
  spqrInitSend _ _ := none
  spqrInitRecv _ _ := none
  deriveMsgKeys _ _ := default
  aeadEnc _ _ _ := []
  aeadDec _ _ _ := none
  pow8 _ := []
  isValidDhTriple _ _ _ := false
  sha256Compress _ _ := []
  sha512Compress st blk := sha512StateBytesBE (sha512CompressState (sha512StateOf st) (ofU8 blk))
  aesEncBlock _ _ := []
  aesDecBlock _ _ := []

private meta def sha512ModelRefCheck (msg : List UInt8) : List (BitVec 8) :=
  ofU8 (SignalPqxdh.sha512Ref sha512ModelRefPrims msg)

#guard sha512ModelRefCheck [] == sha512With sha512CompressState []
#guard sha512ModelRefCheck "abc".toUTF8.toList ==
  sha512With sha512CompressState [0x61#8, 0x62#8, 0x63#8]
#guard sha512ModelRefCheck
    "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu".toUTF8.toList ==
  sha512With sha512CompressState
    ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu".toUTF8.toList.map
      fun b => BitVec.ofNat 8 b.toNat)

/-! ## 3. Little-Endian 64-Bit Chaining-State Encoding (`sha512StateBytesLE`) -/

@[simp]
theorem toLEBytes_8_eq_unpack64 (w : BitVec 64) :
    toLEBytes 8 w = unpack64 w := rfl

theorem pointsToBytes_toLEBytes_8 (a : BitVec 64) (w : BitVec 64) :
    (a ↦ₛ toLEBytes 8 w) = (a ↦₆₄ w) :=
  (pointsTo64_eq_pointsToBytes a w).symm

theorem pointsToBytes_sha512StateBytesLE_list (a : BitVec 64) (st : List (BitVec 64))
    (hst : st.length = 8) :
    (a ↦ₛ st.flatMap (toLEBytes 8)) =
      ((a ↦₆₄ st.getD 0 0#64) ∗
       ((a + 8#64) ↦₆₄ st.getD 1 0#64) ∗
       ((a + 16#64) ↦₆₄ st.getD 2 0#64) ∗
       ((a + 24#64) ↦₆₄ st.getD 3 0#64) ∗
       ((a + 32#64) ↦₆₄ st.getD 4 0#64) ∗
       ((a + 40#64) ↦₆₄ st.getD 5 0#64) ∗
       ((a + 48#64) ↦₆₄ st.getD 6 0#64) ∗
       ((a + 56#64) ↦₆₄ st.getD 7 0#64)) := by
  rcases st with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hst)
  change (a ↦ₛ (toLEBytes 8 w0 ++ (toLEBytes 8 w1 ++ (toLEBytes 8 w2 ++ (toLEBytes 8 w3 ++
    (toLEBytes 8 w4 ++ (toLEBytes 8 w5 ++ (toLEBytes 8 w6 ++ (toLEBytes 8 w7 ++ []))))))))) = _
  rw [List.append_nil]
  repeat rw [pointsToBytes_append, toLEBytes_8_eq_unpack64, unpack64_length, ← pointsTo64_eq_pointsToBytes]
  rw [toLEBytes_8_eq_unpack64, ← pointsTo64_eq_pointsToBytes]
  simp only [List.getD_cons_zero, List.getD_cons_succ, BitVec.add_assoc, BitVec.reduceAdd]

theorem pointsToBytes_sha512StateBytesLE (a : BitVec 64) (st : Sha512State) :
    (a ↦ₛ sha512StateBytesLE st) =
      ((a ↦₆₄ st.toList.getD 0 0#64) ∗
       ((a + 8#64) ↦₆₄ st.toList.getD 1 0#64) ∗
       ((a + 16#64) ↦₆₄ st.toList.getD 2 0#64) ∗
       ((a + 24#64) ↦₆₄ st.toList.getD 3 0#64) ∗
       ((a + 32#64) ↦₆₄ st.toList.getD 4 0#64) ∗
       ((a + 40#64) ↦₆₄ st.toList.getD 5 0#64) ∗
       ((a + 48#64) ↦₆₄ st.toList.getD 6 0#64) ∗
       ((a + 56#64) ↦₆₄ st.toList.getD 7 0#64)) :=
  pointsToBytes_sha512StateBytesLE_list a st.toList st.2

end LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Math

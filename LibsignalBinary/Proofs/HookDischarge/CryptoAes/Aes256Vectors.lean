/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.CryptoGames.AEAD.Aes256
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256

/-!
# Kernel-Checked FIPS 197, NIST SP 800-38A, & `libsignal` AES-256 Vector Theorems (`CryptoAes.Aes256Vectors`)

Kernel-checked `decide` theorems validating `CryptoGames.AES256` (`Spec.Aes256`) against:
1. FIPS 197 §4.2.1 `GF(2^8)` multiplication examples, S-box bijection, §5.1.3/§5.3.3 `MixColumns`
   examples, and Appendix C.3 AES-256 known-answer vector;
2. Little-endian `CBC.AesKey` / `CBC.Block` byte-order encoding (`keyToBytes32`, `bytesToKey32`,
   `blockToBytesLE`, `bytesToBlock`);
3. NIST SP 800-38A Appendix F.2.5 (`CBC-AES256`) single-block and multi-block PKCS#7 CBC roundtrips;
4. `libsignal` `rust/crypto/src/aes_cbc.rs:62` (`aes_cbc_test`, PKCS#7 padded).
-/

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Vectors

set_option maxRecDepth 2000000

open CryptoGames.AES256
  (State sbox invSbox gfMul mixColumn invMixColumn aes256Cipher aes256InvCipher
   aes256Enc aes256Dec)
open CryptoGames.CBC
  (bytesToBlock blockToBytesLE pkcs7Bytes pkcs7Unpad cbcDecryptBlocks cbcDecRaw
   cbcPkcs7EncryptOnly)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)

/-! ## Section 1: FIPS 197 §4–§5 & Appendix C.3 Known-Answer Vectors -/

@[expose] def fipsC3Key : List (BitVec 8) := List.ofFn fun i : Fin 32 => BitVec.ofNat 8 i.val
@[expose] def fipsC3Plain : State := List.ofFn fun i : Fin 16 => BitVec.ofNat 8 (0x11 * i.val)
@[expose] def fipsC3Cipher : State :=
  [0x8e#8, 0xa2#8, 0xb7#8, 0xca#8, 0x51#8, 0x67#8, 0x45#8, 0xbf#8,
   0xea#8, 0xfc#8, 0x49#8, 0x90#8, 0x4b#8, 0x49#8, 0x60#8, 0x89#8]

theorem fips197_gfMul_examples :
    gfMul 0x57#8 0x83#8 = 0xc1#8 ∧ gfMul 0x57#8 0x13#8 = 0xfe#8 := by decide

theorem fips197_sbox_spot_checks :
    sbox 0x00#8 = 0x63#8 ∧ sbox 0x53#8 = 0xed#8 ∧ sbox 0xff#8 = 0x16#8 := by decide

theorem fips197_sbox_bijection :
    ∀ b : BitVec 8, invSbox (sbox b) = b ∧ sbox (invSbox b) = b := by decide

theorem fips197_mixColumn_example :
    mixColumn 0xdb#8 0x13#8 0x53#8 0x45#8 = [0x8e#8, 0x4d#8, 0xa1#8, 0xbc#8] := by decide

theorem fips197_invMixColumn_example :
    invMixColumn 0x8e#8 0x4d#8 0xa1#8 0xbc#8 = [0xdb#8, 0x13#8, 0x53#8, 0x45#8] := by decide

theorem fips197_c3_cipher_kat :
    aes256Cipher fipsC3Key fipsC3Plain = fipsC3Cipher := by decide

theorem fips197_c3_invCipher_kat :
    aes256InvCipher fipsC3Key fipsC3Cipher = fipsC3Plain := by decide

/-! ## Section 2: Little-Endian `CBC.AesKey` / `CBC.Block` Byte-Order Checks -/

theorem blockToBytesLE_asymmetric :
    blockToBytesLE 0x0f0e0d0c0b0a09080706050403020100#128 =
      (List.ofFn fun i : Fin 16 => BitVec.ofNat 8 i.val) := by decide

theorem bytesToBlock_asymmetric :
    bytesToBlock (List.ofFn fun i : Fin 16 => BitVec.ofNat 8 i.val) =
      0x0f0e0d0c0b0a09080706050403020100#128 := by decide

theorem keyToBytes32_fipsC3 :
    keyToBytes32 0x1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100#256 =
      fipsC3Key := by decide

theorem bytesToKey32_fipsC3 :
    bytesToKey32 fipsC3Key =
      0x1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100#256 := by decide

/-! ## Section 3: NIST SP 800-38A Appendix F.2.5 (`CBC-AES256`) -/

@[expose] def nistKeyBytes : List (BitVec 8) := [
  0x60#8, 0x3d#8, 0xeb#8, 0x10#8, 0x15#8, 0xca#8, 0x71#8, 0xbe#8, 0x2b#8, 0x73#8, 0xae#8, 0xf0#8, 0x85#8, 0x7d#8, 0x77#8, 0x81#8,
  0x1f#8, 0x35#8, 0x2c#8, 0x07#8, 0x3b#8, 0x61#8, 0x08#8, 0xd7#8, 0x2d#8, 0x98#8, 0x10#8, 0xa3#8, 0x09#8, 0x14#8, 0xdf#8, 0xf4#8
]
@[expose] def nistIvBytes : List (BitVec 8) := [
  0x00#8, 0x01#8, 0x02#8, 0x03#8, 0x04#8, 0x05#8, 0x06#8, 0x07#8, 0x08#8, 0x09#8, 0x0a#8, 0x0b#8, 0x0c#8, 0x0d#8, 0x0e#8, 0x0f#8
]
@[expose] def nistPt1 : List (BitVec 8) := [
  0x6b#8, 0xc1#8, 0xbe#8, 0xe2#8, 0x2e#8, 0x40#8, 0x9f#8, 0x96#8, 0xe9#8, 0x3d#8, 0x7e#8, 0x11#8, 0x73#8, 0x93#8, 0x17#8, 0x2a#8
]
@[expose] def nistPt2 : List (BitVec 8) := [
  0xae#8, 0x2d#8, 0x8a#8, 0x57#8, 0x1e#8, 0x03#8, 0xac#8, 0x9c#8, 0x9e#8, 0xb7#8, 0x6f#8, 0xac#8, 0x45#8, 0xaf#8, 0x8e#8, 0x51#8
]
@[expose] def nistCt1 : List (BitVec 8) := [
  0xf5#8, 0x8c#8, 0x4c#8, 0x04#8, 0xd6#8, 0xe5#8, 0xf1#8, 0xba#8, 0x77#8, 0x9e#8, 0xab#8, 0xfb#8, 0x5f#8, 0x7b#8, 0xfb#8, 0xd6#8
]
@[expose] def nistCt2 : List (BitVec 8) := [
  0x9c#8, 0xfc#8, 0x4e#8, 0x96#8, 0x7e#8, 0xdb#8, 0x80#8, 0x8d#8, 0x67#8, 0x9f#8, 0x77#8, 0x7b#8, 0xc6#8, 0x70#8, 0x2c#8, 0x7d#8
]

theorem nist_f25_xor_iv :
    blockToBytesLE (bytesToBlock nistPt1 ^^^ bytesToBlock nistIvBytes) =
      List.zipWith (· ^^^ ·) nistPt1 nistIvBytes := by decide

theorem nist_f25_cipher_block1 :
    aes256Cipher nistKeyBytes (List.zipWith (· ^^^ ·) nistPt1 nistIvBytes) = nistCt1 := by decide

theorem nist_f25_cipher_block2 :
    aes256Cipher nistKeyBytes (List.zipWith (· ^^^ ·) nistPt2 nistCt1) = nistCt2 := by decide

theorem nist_f25_enc_block1 :
    aes256Enc (bytesToKey32 nistKeyBytes) (bytesToBlock nistPt1 ^^^ bytesToBlock nistIvBytes) =
      bytesToBlock nistCt1 := by decide

theorem nist_f25_enc_block2 :
    aes256Enc (bytesToKey32 nistKeyBytes) (bytesToBlock nistPt2 ^^^ bytesToBlock nistCt1) =
      bytesToBlock nistCt2 := by decide

theorem nist_f25_dec_block1 :
    (aes256Dec (bytesToKey32 nistKeyBytes) (bytesToBlock nistCt1) ^^^ bytesToBlock nistIvBytes) =
      bytesToBlock nistPt1 := by decide

theorem nist_f25_dec_block2 :
    (aes256Dec (bytesToKey32 nistKeyBytes) (bytesToBlock nistCt2) ^^^ bytesToBlock nistCt1) =
      bytesToBlock nistPt2 := by decide

theorem nist_f25_cbcDecryptBlocks :
    cbcDecryptBlocks (aes256Dec (bytesToKey32 nistKeyBytes)) (bytesToBlock nistIvBytes)
      [bytesToBlock nistCt1, bytesToBlock nistCt2] =
      [bytesToBlock nistPt1, bytesToBlock nistPt2] := by decide

/-- 3-block PKCS#7 multi-block CBC encrypt + decrypt roundtrip on 32-byte NIST plaintext. -/
theorem nist_f25_pkcs7_roundtrip :
    let k := bytesToKey32 nistKeyBytes
    let iv := bytesToBlock nistIvBytes
    let ctBlocks := (cbcPkcs7EncryptOnly aes256Enc 32).enc (k, iv) ⟨nistPt1 ++ nistPt2, rfl⟩
    let ctBytes := ctBlocks.toList.flatMap blockToBytesLE
    ctBytes.length = 48 ∧ ctBytes.take 32 = nistCt1 ++ nistCt2 ∧
      cbcDecRaw aes256Dec k iv ctBytes = some (nistPt1 ++ nistPt2) := by decide

/-! ## Section 4: `libsignal` `rust/crypto/src/aes_cbc.rs:62` (`aes_cbc_test`) -/

@[expose] def sigKeyBytes : List (BitVec 8) := [
  0x4e#8, 0x22#8, 0xeb#8, 0x16#8, 0xd9#8, 0x64#8, 0x77#8, 0x99#8, 0x94#8, 0x22#8, 0x2e#8, 0x82#8, 0x19#8, 0x2c#8, 0xe9#8, 0xf7#8,
  0x47#8, 0xda#8, 0x72#8, 0xdc#8, 0x4a#8, 0xbe#8, 0x49#8, 0xdf#8, 0xde#8, 0xeb#8, 0x71#8, 0xd0#8, 0xff#8, 0xe3#8, 0x79#8, 0x6e#8
]
@[expose] def sigIvBytes : List (BitVec 8) := [
  0x6f#8, 0x8a#8, 0x55#8, 0x7d#8, 0xdc#8, 0x0a#8, 0x14#8, 0x0c#8, 0x87#8, 0x80#8, 0x63#8, 0xa6#8, 0xd5#8, 0xf3#8, 0x1d#8, 0x3d#8
]
@[expose] def sigPtBytes : List (BitVec 8) := [
  0x30#8, 0x73#8, 0x62#8, 0x94#8, 0xa1#8, 0x24#8, 0x48#8, 0x2a#8, 0x41#8, 0x59#8
]
@[expose] def sigPaddedBytes : List (BitVec 8) := [
  0x30#8, 0x73#8, 0x62#8, 0x94#8, 0xa1#8, 0x24#8, 0x48#8, 0x2a#8,
  0x41#8, 0x59#8, 0x06#8, 0x06#8, 0x06#8, 0x06#8, 0x06#8, 0x06#8
]
@[expose] def sigCtBytes : List (BitVec 8) := [
  0xdd#8, 0x3f#8, 0x57#8, 0x3a#8, 0xb4#8, 0x50#8, 0x8b#8, 0x9e#8, 0xd0#8, 0xe4#8, 0x5e#8, 0x0b#8, 0xaf#8, 0x56#8, 0x08#8, 0xf3#8
]

theorem libsignal_aes_cbc_pkcs7_pad_unpad :
    pkcs7Bytes ⟨sigPtBytes, rfl⟩ = sigPaddedBytes ∧
      pkcs7Unpad sigPaddedBytes = some sigPtBytes := by decide

theorem libsignal_aes_cbc_encrypt_kat :
    aes256Cipher sigKeyBytes (List.zipWith (· ^^^ ·) sigPaddedBytes sigIvBytes) = sigCtBytes := by
  decide

theorem libsignal_aes_cbc_decrypt_kat :
    List.zipWith (· ^^^ ·) (aes256InvCipher sigKeyBytes sigCtBytes) sigIvBytes = sigPaddedBytes := by
  decide

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Vectors

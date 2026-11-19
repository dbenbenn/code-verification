/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs

/-!
# FIPS 197 AES-256 Block Cipher Specification

**Trusted: definitions used by the statement.** Direct transcription of NIST FIPS 197 for AES-256
(`Nk = 8`, `Nb = 4`, `Nr = 14`), bridging FIPS 197 column-major 16-byte states (`aes256Cipher`,
`aes256InvCipher`) to the repository's little-endian `CBC.AesKey` / `CBC.Block` representation
(`aes256Enc`, `aes256Dec`). See `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoGames.AES256

open CryptoGames.CBC (AesKey Block bytesToBlock blockToBytesLE)
open CryptoGames.HMAC (keyToBytes32)

/-! ## Section 1: Pure FIPS 197 AES-256 Specification -/

/-- Column-major 16-byte AES state: row `r`, column `c` (`0 ≤ r, c < 4`) sits at `s[r + 4 * c]`
(FIPS 197 §3.4, Eq. 3.3). -/
abbrev State := List (BitVec 8)

/-- A 4-byte key-schedule column word (FIPS 197 §3.2). -/
abbrev Word := List (BitVec 8)

/-- Forward AES S-box 16×16 lookup table indexed by high/low nibble (FIPS 197 §5.1.1, Figure 7). -/
def sboxTable : Vector (Vector (BitVec 8) 16) 16 := #v[
  #v[0x63#8, 0x7c#8, 0x77#8, 0x7b#8, 0xf2#8, 0x6b#8, 0x6f#8, 0xc5#8, 0x30#8, 0x01#8, 0x67#8, 0x2b#8, 0xfe#8, 0xd7#8, 0xab#8, 0x76#8],
  #v[0xca#8, 0x82#8, 0xc9#8, 0x7d#8, 0xfa#8, 0x59#8, 0x47#8, 0xf0#8, 0xad#8, 0xd4#8, 0xa2#8, 0xaf#8, 0x9c#8, 0xa4#8, 0x72#8, 0xc0#8],
  #v[0xb7#8, 0xfd#8, 0x93#8, 0x26#8, 0x36#8, 0x3f#8, 0xf7#8, 0xcc#8, 0x34#8, 0xa5#8, 0xe5#8, 0xf1#8, 0x71#8, 0xd8#8, 0x31#8, 0x15#8],
  #v[0x04#8, 0xc7#8, 0x23#8, 0xc3#8, 0x18#8, 0x96#8, 0x05#8, 0x9a#8, 0x07#8, 0x12#8, 0x80#8, 0xe2#8, 0xeb#8, 0x27#8, 0xb2#8, 0x75#8],
  #v[0x09#8, 0x83#8, 0x2c#8, 0x1a#8, 0x1b#8, 0x6e#8, 0x5a#8, 0xa0#8, 0x52#8, 0x3b#8, 0xd6#8, 0xb3#8, 0x29#8, 0xe3#8, 0x2f#8, 0x84#8],
  #v[0x53#8, 0xd1#8, 0x00#8, 0xed#8, 0x20#8, 0xfc#8, 0xb1#8, 0x5b#8, 0x6a#8, 0xcb#8, 0xbe#8, 0x39#8, 0x4a#8, 0x4c#8, 0x58#8, 0xcf#8],
  #v[0xd0#8, 0xef#8, 0xaa#8, 0xfb#8, 0x43#8, 0x4d#8, 0x33#8, 0x85#8, 0x45#8, 0xf9#8, 0x02#8, 0x7f#8, 0x50#8, 0x3c#8, 0x9f#8, 0xa8#8],
  #v[0x51#8, 0xa3#8, 0x40#8, 0x8f#8, 0x92#8, 0x9d#8, 0x38#8, 0xf5#8, 0xbc#8, 0xb6#8, 0xda#8, 0x21#8, 0x10#8, 0xff#8, 0xf3#8, 0xd2#8],
  #v[0xcd#8, 0x0c#8, 0x13#8, 0xec#8, 0x5f#8, 0x97#8, 0x44#8, 0x17#8, 0xc4#8, 0xa7#8, 0x7e#8, 0x3d#8, 0x64#8, 0x5d#8, 0x19#8, 0x73#8],
  #v[0x60#8, 0x81#8, 0x4f#8, 0xdc#8, 0x22#8, 0x2a#8, 0x90#8, 0x88#8, 0x46#8, 0xee#8, 0xb8#8, 0x14#8, 0xde#8, 0x5e#8, 0x0b#8, 0xdb#8],
  #v[0xe0#8, 0x32#8, 0x3a#8, 0x0a#8, 0x49#8, 0x06#8, 0x24#8, 0x5c#8, 0xc2#8, 0xd3#8, 0xac#8, 0x62#8, 0x91#8, 0x95#8, 0xe4#8, 0x79#8],
  #v[0xe7#8, 0xc8#8, 0x37#8, 0x6d#8, 0x8d#8, 0xd5#8, 0x4e#8, 0xa9#8, 0x6c#8, 0x56#8, 0xf4#8, 0xea#8, 0x65#8, 0x7a#8, 0xae#8, 0x08#8],
  #v[0xba#8, 0x78#8, 0x25#8, 0x2e#8, 0x1c#8, 0xa6#8, 0xb4#8, 0xc6#8, 0xe8#8, 0xdd#8, 0x74#8, 0x1f#8, 0x4b#8, 0xbd#8, 0x8b#8, 0x8a#8],
  #v[0x70#8, 0x3e#8, 0xb5#8, 0x66#8, 0x48#8, 0x03#8, 0xf6#8, 0x0e#8, 0x61#8, 0x35#8, 0x57#8, 0xb9#8, 0x86#8, 0xc1#8, 0x1d#8, 0x9e#8],
  #v[0xe1#8, 0xf8#8, 0x98#8, 0x11#8, 0x69#8, 0xd9#8, 0x8e#8, 0x94#8, 0x9b#8, 0x1e#8, 0x87#8, 0xe9#8, 0xce#8, 0x55#8, 0x28#8, 0xdf#8],
  #v[0x8c#8, 0xa1#8, 0x89#8, 0x0d#8, 0xbf#8, 0xe6#8, 0x42#8, 0x68#8, 0x41#8, 0x99#8, 0x2d#8, 0x0f#8, 0xb0#8, 0x54#8, 0xbb#8, 0x16#8]
]

/-- Inverse AES S-box 16×16 lookup table indexed by high/low nibble (FIPS 197 §5.3.2, Figure 14). -/
def invSboxTable : Vector (Vector (BitVec 8) 16) 16 := #v[
  #v[0x52#8, 0x09#8, 0x6a#8, 0xd5#8, 0x30#8, 0x36#8, 0xa5#8, 0x38#8, 0xbf#8, 0x40#8, 0xa3#8, 0x9e#8, 0x81#8, 0xf3#8, 0xd7#8, 0xfb#8],
  #v[0x7c#8, 0xe3#8, 0x39#8, 0x82#8, 0x9b#8, 0x2f#8, 0xff#8, 0x87#8, 0x34#8, 0x8e#8, 0x43#8, 0x44#8, 0xc4#8, 0xde#8, 0xe9#8, 0xcb#8],
  #v[0x54#8, 0x7b#8, 0x94#8, 0x32#8, 0xa6#8, 0xc2#8, 0x23#8, 0x3d#8, 0xee#8, 0x4c#8, 0x95#8, 0x0b#8, 0x42#8, 0xfa#8, 0xc3#8, 0x4e#8],
  #v[0x08#8, 0x2e#8, 0xa1#8, 0x66#8, 0x28#8, 0xd9#8, 0x24#8, 0xb2#8, 0x76#8, 0x5b#8, 0xa2#8, 0x49#8, 0x6d#8, 0x8b#8, 0xd1#8, 0x25#8],
  #v[0x72#8, 0xf8#8, 0xf6#8, 0x64#8, 0x86#8, 0x68#8, 0x98#8, 0x16#8, 0xd4#8, 0xa4#8, 0x5c#8, 0xcc#8, 0x5d#8, 0x65#8, 0xb6#8, 0x92#8],
  #v[0x6c#8, 0x70#8, 0x48#8, 0x50#8, 0xfd#8, 0xed#8, 0xb9#8, 0xda#8, 0x5e#8, 0x15#8, 0x46#8, 0x57#8, 0xa7#8, 0x8d#8, 0x9d#8, 0x84#8],
  #v[0x90#8, 0xd8#8, 0xab#8, 0x00#8, 0x8c#8, 0xbc#8, 0xd3#8, 0x0a#8, 0xf7#8, 0xe4#8, 0x58#8, 0x05#8, 0xb8#8, 0xb3#8, 0x45#8, 0x06#8],
  #v[0xd0#8, 0x2c#8, 0x1e#8, 0x8f#8, 0xca#8, 0x3f#8, 0x0f#8, 0x02#8, 0xc1#8, 0xaf#8, 0xbd#8, 0x03#8, 0x01#8, 0x13#8, 0x8a#8, 0x6b#8],
  #v[0x3a#8, 0x91#8, 0x11#8, 0x41#8, 0x4f#8, 0x67#8, 0xdc#8, 0xea#8, 0x97#8, 0xf2#8, 0xcf#8, 0xce#8, 0xf0#8, 0xb4#8, 0xe6#8, 0x73#8],
  #v[0x96#8, 0xac#8, 0x74#8, 0x22#8, 0xe7#8, 0xad#8, 0x35#8, 0x85#8, 0xe2#8, 0xf9#8, 0x37#8, 0xe8#8, 0x1c#8, 0x75#8, 0xdf#8, 0x6e#8],
  #v[0x47#8, 0xf1#8, 0x1a#8, 0x71#8, 0x1d#8, 0x29#8, 0xc5#8, 0x89#8, 0x6f#8, 0xb7#8, 0x62#8, 0x0e#8, 0xaa#8, 0x18#8, 0xbe#8, 0x1b#8],
  #v[0xfc#8, 0x56#8, 0x3e#8, 0x4b#8, 0xc6#8, 0xd2#8, 0x79#8, 0x20#8, 0x9a#8, 0xdb#8, 0xc0#8, 0xfe#8, 0x78#8, 0xcd#8, 0x5a#8, 0xf4#8],
  #v[0x1f#8, 0xdd#8, 0xa8#8, 0x33#8, 0x88#8, 0x07#8, 0xc7#8, 0x31#8, 0xb1#8, 0x12#8, 0x10#8, 0x59#8, 0x27#8, 0x80#8, 0xec#8, 0x5f#8],
  #v[0x60#8, 0x51#8, 0x7f#8, 0xa9#8, 0x19#8, 0xb5#8, 0x4a#8, 0x0d#8, 0x2d#8, 0xe5#8, 0x7a#8, 0x9f#8, 0x93#8, 0xc9#8, 0x9c#8, 0xef#8],
  #v[0xa0#8, 0xe0#8, 0x3b#8, 0x4d#8, 0xae#8, 0x2a#8, 0xf5#8, 0xb0#8, 0xc8#8, 0xeb#8, 0xbb#8, 0x3c#8, 0x83#8, 0x53#8, 0x99#8, 0x61#8],
  #v[0x17#8, 0x2b#8, 0x04#8, 0x7e#8, 0xba#8, 0x77#8, 0xd6#8, 0x26#8, 0xe1#8, 0x69#8, 0x14#8, 0x63#8, 0x55#8, 0x21#8, 0x0c#8, 0x7d#8]
]

/-- Single-byte S-box substitution `SBox(b)` (FIPS 197 §5.1.1). -/
def sbox (b : BitVec 8) : BitVec 8 := sboxTable[b.toNat / 16][b.toNat % 16]

/-- Single-byte inverse S-box substitution `InvSBox(b)` (FIPS 197 §5.3.2). -/
def invSbox (b : BitVec 8) : BitVec 8 := invSboxTable[b.toNat / 16][b.toNat % 16]

/-- Multiplication by $x$ (`{02}`) in $\mathrm{GF}(2^8) = \mathbb{F}_2[x]/(x^8 + x^4 + x^3 + x + 1)$
(FIPS 197 §4.2.1). -/
def xtime (b : BitVec 8) : BitVec 8 :=
  if b.msb then (b <<< 1) ^^^ 0x1b#8 else b <<< 1

/-- Multiplication in $\mathrm{GF}(2^8)$ via repeated `xtime` (FIPS 197 §4.2.1). -/
def gfMul (a b : BitVec 8) : BitVec 8 :=
  (Fin.foldl 8 (fun (acc, cur) (i : Fin 8) =>
    (if a.getLsbD i.val then acc ^^^ cur else acc, xtime cur)) (0#8, b)).1

/-- `SubBytes` state transformation (FIPS 197 §5.1.1). -/
def subBytes (s : State) : State := s.map sbox

/-- `InvSubBytes` state transformation (FIPS 197 §5.3.2). -/
def invSubBytes (s : State) : State := s.map invSbox

/-- `ShiftRows` state transformation: row `r` shifts cyclically left by `r` columns
(`s'[r, c] = s[r, (c + r) mod 4]`, FIPS 197 §5.1.2). -/
def shiftRows (s : State) : State :=
  List.ofFn fun i : Fin 16 =>
    let r := i.val % 4
    let c := i.val / 4
    s.getD (r + 4 * ((c + r) % 4)) 0#8

/-- `InvShiftRows` state transformation: row `r` shifts cyclically right by `r` columns
(`s'[r, c] = s[r, (c - r) mod 4]`, FIPS 197 §5.3.1). -/
def invShiftRows (s : State) : State :=
  List.ofFn fun i : Fin 16 =>
    let r := i.val % 4
    let c := i.val / 4
    s.getD (r + 4 * ((c + 4 - r) % 4)) 0#8

/-- Mix one 4-byte state column (FIPS 197 §5.1.3, Eq. 5.6). -/
def mixColumn (s0 s1 s2 s3 : BitVec 8) : Word :=
  [gfMul 0x02#8 s0 ^^^ gfMul 0x03#8 s1 ^^^ s2 ^^^ s3,
   s0 ^^^ gfMul 0x02#8 s1 ^^^ gfMul 0x03#8 s2 ^^^ s3,
   s0 ^^^ s1 ^^^ gfMul 0x02#8 s2 ^^^ gfMul 0x03#8 s3,
   gfMul 0x03#8 s0 ^^^ s1 ^^^ s2 ^^^ gfMul 0x02#8 s3]

/-- `MixColumns` state transformation across all four columns (FIPS 197 §5.1.3). -/
def mixColumns (s : State) : State :=
  (List.ofFn fun c : Fin 4 =>
    mixColumn (s.getD (4 * c.val) 0#8) (s.getD (4 * c.val + 1) 0#8)
      (s.getD (4 * c.val + 2) 0#8) (s.getD (4 * c.val + 3) 0#8)).flatten

/-- Inverse-mix one 4-byte state column (FIPS 197 §5.3.3, Eq. 5.10). -/
def invMixColumn (s0 s1 s2 s3 : BitVec 8) : Word :=
  [gfMul 0x0e#8 s0 ^^^ gfMul 0x0b#8 s1 ^^^ gfMul 0x0d#8 s2 ^^^ gfMul 0x09#8 s3,
   gfMul 0x09#8 s0 ^^^ gfMul 0x0e#8 s1 ^^^ gfMul 0x0b#8 s2 ^^^ gfMul 0x0d#8 s3,
   gfMul 0x0d#8 s0 ^^^ gfMul 0x09#8 s1 ^^^ gfMul 0x0e#8 s2 ^^^ gfMul 0x0b#8 s3,
   gfMul 0x0b#8 s0 ^^^ gfMul 0x0d#8 s1 ^^^ gfMul 0x09#8 s2 ^^^ gfMul 0x0e#8 s3]

/-- `InvMixColumns` state transformation across all four columns (FIPS 197 §5.3.3). -/
def invMixColumns (s : State) : State :=
  (List.ofFn fun c : Fin 4 =>
    invMixColumn (s.getD (4 * c.val) 0#8) (s.getD (4 * c.val + 1) 0#8)
      (s.getD (4 * c.val + 2) 0#8) (s.getD (4 * c.val + 3) 0#8)).flatten

/-- `AddRoundKey` state transformation (FIPS 197 §5.1.4). -/
def addRoundKey (s rk : State) : State :=
  List.ofFn fun i : Fin 16 => s.getD i.val 0#8 ^^^ rk.getD i.val 0#8

/-- Cyclic 1-byte left word rotation `[a₀, a₁, a₂, a₃] ↦ [a₁, a₂, a₃, a₀]` (FIPS 197 §5.2). -/
def rotWord (w : Word) : Word :=
  [w.getD 1 0#8, w.getD 2 0#8, w.getD 3 0#8, w.getD 0 0#8]

/-- Bytewise S-box substitution on a 4-byte word (FIPS 197 §5.2). -/
def subWord (w : Word) : Word := w.map sbox

/-- Bytewise XOR of two 4-byte words. -/
def xorWord (u v : Word) : Word :=
  List.ofFn fun j : Fin 4 => u.getD j.val 0#8 ^^^ v.getD j.val 0#8

/-- Round-constant leading bytes `Rcon[1..7]` for AES-256 (`Nk = 8`, FIPS 197 §5.2 Table 5). -/
def rcon : List (BitVec 8) :=
  [0x01#8, 0x02#8, 0x04#8, 0x08#8, 0x10#8, 0x20#8, 0x40#8]

/-- AES-256 key expansion (`Nk = 8`, `Nb = 4`, `Nr = 14` → 60 words; FIPS 197 §5.2, Algorithm 2). -/
def expandKey256 (key : List (BitVec 8)) : List Word :=
  let w0 : List Word := List.ofFn fun i : Fin 8 =>
    [key.getD (4 * i.val) 0#8, key.getD (4 * i.val + 1) 0#8,
     key.getD (4 * i.val + 2) 0#8, key.getD (4 * i.val + 3) 0#8]
  Fin.foldl 52 (fun w (k : Fin 52) =>
    let i := 8 + k.val
    let temp := w.getD (i - 1) []
    let temp :=
      if i % 8 = 0 then
        xorWord (subWord (rotWord temp)) [rcon.getD (i / 8 - 1) 0#8, 0#8, 0#8, 0#8]
      else if i % 8 = 4 then
        subWord temp
      else
        temp
    w ++ [xorWord (w.getD (i - 8) []) temp]) w0

/-- Extract 16-byte round key `r` (`0 ≤ r ≤ 14`) from the 60-word key schedule `w[4r .. 4r+3]`. -/
def roundKey (w : List Word) (r : Nat) : State :=
  List.ofFn fun i : Fin 16 => (w.getD (4 * r + i.val / 4) []).getD (i.val % 4) 0#8

/-- FIPS 197 §5.1 Algorithm 1 (`Cipher` for AES-256, `Nr = 14`). -/
def aes256Cipher (key : List (BitVec 8)) (input : State) : State :=
  let w := expandKey256 key
  let s0 := addRoundKey input (roundKey w 0)
  let s13 := Fin.foldl 13 (fun s (r : Fin 13) =>
    addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey w (r.val + 1))) s0
  addRoundKey (shiftRows (subBytes s13)) (roundKey w 14)

/-- FIPS 197 §5.3 Algorithm 3 (`InvCipher` for AES-256, `Nr = 14`). -/
def aes256InvCipher (key : List (BitVec 8)) (input : State) : State :=
  let w := expandKey256 key
  let s0 := addRoundKey input (roundKey w 14)
  let s13 := Fin.foldl 13 (fun s (j : Fin 13) =>
    invMixColumns (addRoundKey (invSubBytes (invShiftRows s)) (roundKey w (13 - j.val)))) s0
  addRoundKey (invSubBytes (invShiftRows s13)) (roundKey w 0)


/-! ## Section 2: Little-Endian `CBC.AesKey` / `CBC.Block` Byte-Order Glue -/

/-- AES-256 single-block encryption (`CBC.AesKey → CBC.Block → CBC.Block`) under the repository's
little-endian byte encoding (`HMAC.keyToBytes32`, `CBC.blockToBytesLE`, `CBC.bytesToBlock`). -/
def aes256Enc (k : AesKey) (b : Block) : Block :=
  bytesToBlock (aes256Cipher (keyToBytes32 k) (blockToBytesLE b))

/-- AES-256 single-block decryption (`CBC.AesKey → CBC.Block → CBC.Block`) under the repository's
little-endian byte encoding (`HMAC.keyToBytes32`, `CBC.blockToBytesLE`, `CBC.bytesToBlock`). -/
def aes256Dec (k : AesKey) (b : Block) : Block :=
  bytesToBlock (aes256InvCipher (keyToBytes32 k) (blockToBytesLE b))


end CryptoGames.AES256

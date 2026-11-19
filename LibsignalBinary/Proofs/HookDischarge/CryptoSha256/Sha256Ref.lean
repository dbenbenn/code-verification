/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# FIPS 180-4 SHA-256 block-compression reference

Computable, Mathlib-free reference model of FIPS 180-4 SHA-256 block compression
(`sha256CompressBlock : List (BitVec 32) → List (BitVec 8) → List (BitVec 32)`), used as the
concrete compression witness `F := sha256CompressState`. Defines the 64 round constants
`sha256K`, big-endian 32-bit word conversions (`beU32OfBytes`, `beBytesOfU32`),
$\sigma_0, \sigma_1, \Sigma_0, \Sigma_1, \text{Ch}, \text{Maj}$, the message schedule
`sha256Schedule`, and 64-round compression `sha256Round`. Full message padding (`sha256Pad`),
initial state (`sha256IV`), and `sha256With` / `hmacWith` live in `CryptoGames.HMAC`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref

/-- The 64 32-bit round constants $K_0 \dots K_{63}$ of SHA-256 (FIPS 180-4 §4.2.2). -/
@[expose] def sha256K : List (BitVec 32) := [
  0x428a2f98#32, 0x71374491#32, 0xb5c0fbcf#32, 0xe9b5dba5#32,
  0x3956c25b#32, 0x59f111f1#32, 0x923f82a4#32, 0xab1c5ed5#32,
  0xd807aa98#32, 0x12835b01#32, 0x243185be#32, 0x550c7dc3#32,
  0x72be5d74#32, 0x80deb1fe#32, 0x9bdc06a7#32, 0xc19bf174#32,
  0xe49b69c1#32, 0xefbe4786#32, 0x0fc19dc6#32, 0x240ca1cc#32,
  0x2de92c6f#32, 0x4a7484aa#32, 0x5cb0a9dc#32, 0x76f988da#32,
  0x983e5152#32, 0xa831c66d#32, 0xb00327c8#32, 0xbf597fc7#32,
  0xc6e00bf3#32, 0xd5a79147#32, 0x06ca6351#32, 0x14292967#32,
  0x27b70a85#32, 0x2e1b2138#32, 0x4d2c6dfc#32, 0x53380d13#32,
  0x650a7354#32, 0x766a0abb#32, 0x81c2c92e#32, 0x92722c85#32,
  0xa2bfe8a1#32, 0xa81a664b#32, 0xc24b8b70#32, 0xc76c51a3#32,
  0xd192e819#32, 0xd6990624#32, 0xf40e3585#32, 0x106aa070#32,
  0x19a4c116#32, 0x1e376c08#32, 0x2748774c#32, 0x34b0bcb5#32,
  0x391c0cb3#32, 0x4ed8aa4a#32, 0x5b9cca4f#32, 0x682e6ff3#32,
  0x748f82ee#32, 0x78a5636f#32, 0x84c87814#32, 0x8cc70208#32,
  0x90befffa#32, 0xa4506ceb#32, 0xbef9a3f7#32, 0xc67178f2#32
]

/-- Decode 4 big-endian bytes into a 32-bit word. -/
@[expose] def beU32OfBytes (bs : List (BitVec 8)) : BitVec 32 :=
  bs.foldl (fun acc b => (acc <<< 8) ||| b.zeroExtend 32) 0#32

/-- Encode a 32-bit word into 4 big-endian bytes. -/
@[expose] def beBytesOfU32 (w : BitVec 32) : List (BitVec 8) :=
  (List.range 4).map fun i => (w >>> ((3 - i) * 8)).truncate 8

/-- FIPS 180-4 $\sigma_0^{\{256\}}(x) = \text{ROTR}^7(x) \oplus \text{ROTR}^{18}(x) \oplus (x \gg 3)$. -/
@[expose] def sha256SmallSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

/-- FIPS 180-4 $\sigma_1^{\{256\}}(x) = \text{ROTR}^{17}(x) \oplus \text{ROTR}^{19}(x) \oplus (x \gg 10)$. -/
@[expose] def sha256SmallSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

/-- FIPS 180-4 $\Sigma_0^{\{256\}}(x) = \text{ROTR}^2(x) \oplus \text{ROTR}^{13}(x) \oplus \text{ROTR}^{22}(x)$. -/
@[expose] def sha256BigSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- FIPS 180-4 $\Sigma_1^{\{256\}}(x) = \text{ROTR}^6(x) \oplus \text{ROTR}^{11}(x) \oplus \text{ROTR}^{25}(x)$. -/
@[expose] def sha256BigSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- FIPS 180-4 $\text{Ch}(x, y, z) = (x \wedge y) \oplus (\neg x \wedge z)$. -/
@[expose] def sha256Ch (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ (~~~x &&& z)

/-- FIPS 180-4 $\text{Maj}(x, y, z) = (x \wedge y) \oplus (x \wedge z) \oplus (y \wedge z)$. -/
@[expose] def sha256Maj (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Expand 16 big-endian 32-bit block words $W_0 \dots W_{15}$ to the 64-word schedule $W_0 \dots W_{63}$. -/
@[expose] def sha256Schedule (w16 : List (BitVec 32)) : List (BitVec 32) :=
  (List.range 48).foldl (fun ws i =>
    let w16_back := ws.getD i 0#32
    let w15_back := ws.getD (i + 1) 0#32
    let w7_back  := ws.getD (i + 9) 0#32
    let w2_back  := ws.getD (i + 14) 0#32
    let next := w16_back + sha256SmallSigma0 w15_back + w7_back + sha256SmallSigma1 w2_back
    ws ++ [next]) (w16.take 16)

/-- One round of the SHA-256 compression function on working variables $[a, b, c, d, e, f, g, h]$. -/
@[expose] def sha256Round (st : List (BitVec 32)) (k w : BitVec 32) : List (BitVec 32) :=
  let a := st.getD 0 0#32
  let b := st.getD 1 0#32
  let c := st.getD 2 0#32
  let d := st.getD 3 0#32
  let e := st.getD 4 0#32
  let f := st.getD 5 0#32
  let g := st.getD 6 0#32
  let h := st.getD 7 0#32
  let t1 := h + sha256BigSigma1 e + sha256Ch e f g + k + w
  let t2 := sha256BigSigma0 a + sha256Maj a b c
  [t1 + t2, a, b, c, d + t1, e, f, g]

/-- Compress one 64-byte (512-bit) block into the 8-word SHA-256 state. -/
@[expose] def sha256CompressBlock (st : List (BitVec 32)) (block : List (BitVec 8)) : List (BitVec 32) :=
  let w16 := (List.range 16).map fun i => beU32OfBytes ((block.drop (4 * i)).take 4)
  let ws := sha256Schedule w16
  let st' := (List.range 64).foldl (fun cur i =>
    sha256Round cur (sha256K.getD i 0#32) (ws.getD i 0#32)) st
  (List.range 8).map fun i => st.getD i 0#32 + st'.getD i 0#32

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref

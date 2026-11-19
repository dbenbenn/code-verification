/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Vector.Defs

/-!
# FIPS 180-4 SHA-512 Block-Compression Specification

**Trusted: definitions used by the statement.** Direct transcription of NIST FIPS 180-4
(§4.1.3, §4.2.3, §6.4.2) for single-block SHA-512 compression (`sha512CompressState` over
`List.Vector (BitVec 64) 8`). See `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoGames.SHA512

/-- The 80 64-bit round constants $K_0^{\{512\}} \dots K_{79}^{\{512\}}$ of SHA-512 (FIPS 180-4 §4.2.3). -/
def sha512K : List (BitVec 64) := [
  0x428a2f98d728ae22#64, 0x7137449123ef65cd#64, 0xb5c0fbcfec4d3b2f#64, 0xe9b5dba58189dbbc#64,
  0x3956c25bf348b538#64, 0x59f111f1b605d019#64, 0x923f82a4af194f9b#64, 0xab1c5ed5da6d8118#64,
  0xd807aa98a3030242#64, 0x12835b0145706fbe#64, 0x243185be4ee4b28c#64, 0x550c7dc3d5ffb4e2#64,
  0x72be5d74f27b896f#64, 0x80deb1fe3b1696b1#64, 0x9bdc06a725c71235#64, 0xc19bf174cf692694#64,
  0xe49b69c19ef14ad2#64, 0xefbe4786384f25e3#64, 0x0fc19dc68b8cd5b5#64, 0x240ca1cc77ac9c65#64,
  0x2de92c6f592b0275#64, 0x4a7484aa6ea6e483#64, 0x5cb0a9dcbd41fbd4#64, 0x76f988da831153b5#64,
  0x983e5152ee66dfab#64, 0xa831c66d2db43210#64, 0xb00327c898fb213f#64, 0xbf597fc7beef0ee4#64,
  0xc6e00bf33da88fc2#64, 0xd5a79147930aa725#64, 0x06ca6351e003826f#64, 0x142929670a0e6e70#64,
  0x27b70a8546d22ffc#64, 0x2e1b21385c26c926#64, 0x4d2c6dfc5ac42aed#64, 0x53380d139d95b3df#64,
  0x650a73548baf63de#64, 0x766a0abb3c77b2a8#64, 0x81c2c92e47edaee6#64, 0x92722c851482353b#64,
  0xa2bfe8a14cf10364#64, 0xa81a664bbc423001#64, 0xc24b8b70d0f89791#64, 0xc76c51a30654be30#64,
  0xd192e819d6ef5218#64, 0xd69906245565a910#64, 0xf40e35855771202a#64, 0x106aa07032bbd1b8#64,
  0x19a4c116b8d2d0c8#64, 0x1e376c085141ab53#64, 0x2748774cdf8eeb99#64, 0x34b0bcb5e19b48a8#64,
  0x391c0cb3c5c95a63#64, 0x4ed8aa4ae3418acb#64, 0x5b9cca4f7763e373#64, 0x682e6ff3d6b2b8a3#64,
  0x748f82ee5defb2fc#64, 0x78a5636f43172f60#64, 0x84c87814a1f0ab72#64, 0x8cc702081a6439ec#64,
  0x90befffa23631e28#64, 0xa4506cebde82bde9#64, 0xbef9a3f7b2c67915#64, 0xc67178f2e372532b#64,
  0xca273eceea26619c#64, 0xd186b8c721c0c207#64, 0xeada7dd6cde0eb1e#64, 0xf57d4f7fee6ed178#64,
  0x06f067aa72176fba#64, 0x0a637dc5a2c898a6#64, 0x113f9804bef90dae#64, 0x1b710b35131c471b#64,
  0x28db77f523047d84#64, 0x32caab7b40c72493#64, 0x3c9ebe0a15c9bebc#64, 0x431d67c49c100d4c#64,
  0x4cc5d4becb3e42b6#64, 0x597f299cfc657e2a#64, 0x5fcb6fab3ad6faec#64, 0x6c44198c4a475817#64
]

/-- Decode 8 big-endian bytes into a 64-bit word. -/
def beU64OfBytes (bs : List (BitVec 8)) : BitVec 64 :=
  bs.foldl (fun acc b => (acc <<< 8) ||| b.zeroExtend 64) 0#64

/-- FIPS 180-4 $\sigma_0^{\{512\}}(x) = \operatorname{ROTR}^1(x) \oplus \operatorname{ROTR}^8(x) \oplus (x \gg 7)$. -/
def sha512SmallSigma0 (x : BitVec 64) : BitVec 64 :=
  x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ (x >>> 7)

/-- FIPS 180-4 $\sigma_1^{\{512\}}(x) = \operatorname{ROTR}^{19}(x) \oplus \operatorname{ROTR}^{61}(x) \oplus (x \gg 6)$. -/
def sha512SmallSigma1 (x : BitVec 64) : BitVec 64 :=
  x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ (x >>> 6)

/-- FIPS 180-4 $\Sigma_0^{\{512\}}(x) = \operatorname{ROTR}^{28}(x) \oplus \operatorname{ROTR}^{34}(x) \oplus \operatorname{ROTR}^{39}(x)$. -/
def sha512BigSigma0 (x : BitVec 64) : BitVec 64 :=
  x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39

/-- FIPS 180-4 $\Sigma_1^{\{512\}}(x) = \operatorname{ROTR}^{14}(x) \oplus \operatorname{ROTR}^{18}(x) \oplus \operatorname{ROTR}^{41}(x)$. -/
def sha512BigSigma1 (x : BitVec 64) : BitVec 64 :=
  x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41

/-- FIPS 180-4 $\operatorname{Ch}(x, y, z) = (x \wedge y) \oplus (\neg x \wedge z)$. -/
def sha512Ch (x y z : BitVec 64) : BitVec 64 :=
  (x &&& y) ^^^ (~~~x &&& z)

/-- FIPS 180-4 $\operatorname{Maj}(x, y, z) = (x \wedge y) \oplus (x \wedge z) \oplus (y \wedge z)$. -/
def sha512Maj (x y z : BitVec 64) : BitVec 64 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Expand 16 big-endian 64-bit block words $W_0 \dots W_{15}$ to the 80-word schedule $W_0 \dots W_{79}$. -/
def sha512Schedule (w16 : List (BitVec 64)) : List (BitVec 64) :=
  (List.range 64).foldl (fun ws i =>
    let w16_back := ws.getD i 0#64
    let w15_back := ws.getD (i + 1) 0#64
    let w7_back  := ws.getD (i + 9) 0#64
    let w2_back  := ws.getD (i + 14) 0#64
    let next := w16_back + sha512SmallSigma0 w15_back + w7_back + sha512SmallSigma1 w2_back
    ws ++ [next]) (w16.take 16)

/-- One round of the SHA-512 compression function on working variables $[a, b, c, d, e, f, g, h]$. -/
def sha512Round (st : List (BitVec 64)) (k w : BitVec 64) : List (BitVec 64) :=
  let a := st.getD 0 0#64
  let b := st.getD 1 0#64
  let c := st.getD 2 0#64
  let d := st.getD 3 0#64
  let e := st.getD 4 0#64
  let f := st.getD 5 0#64
  let g := st.getD 6 0#64
  let h := st.getD 7 0#64
  let t1 := h + sha512BigSigma1 e + sha512Ch e f g + k + w
  let t2 := sha512BigSigma0 a + sha512Maj a b c
  [t1 + t2, a, b, c, d + t1, e, f, g]

/-- Compress one 128-byte (1024-bit) block into the 8-word SHA-512 state. -/
def sha512CompressBlock (st : List (BitVec 64)) (block : List (BitVec 8)) : List (BitVec 64) :=
  let w16 := (List.range 16).map fun i => beU64OfBytes ((block.drop (8 * i)).take 8)
  let ws := sha512Schedule w16
  let st' := (List.range 80).foldl (fun cur i =>
    sha512Round cur (sha512K.getD i 0#64) (ws.getD i 0#64)) st
  (List.range 8).map fun i => st.getD i 0#64 + st'.getD i 0#64

/-- FIPS 180-4 SHA-512 single-block compression typed over `List.Vector (BitVec 64) 8`
(`CryptoVerification.E2E.Sha512State`), instantiating `W.Q.F512` for `sha2::sha512::compress512`. -/
def sha512CompressState (st : List.Vector (BitVec 64) 8)
    (block : List (BitVec 8)) : List.Vector (BitVec 64) 8 :=
  ⟨sha512CompressBlock st.toList block, by simp [sha512CompressBlock]⟩

end CryptoGames.SHA512

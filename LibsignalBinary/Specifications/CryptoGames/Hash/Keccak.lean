/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Vector.Defs

/-!
# FIPS 202 Keccak-f[1600], SHA3-256/512, and SHAKE-128/256 Specification

**Trusted in part.** Direct transcription of NIST FIPS 202 (`Keccak-f[1600]`, multi-rate sponge
padding, `SHA3-256`, `SHA3-512`, `SHAKE-128`, and `SHAKE-256`) used by the Kyber-1024 and
ML-KEM-768 specifications; unreached helper wrappers are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoGames.SHA3

/-- 25-lane Keccak-f[1600] state (`s[5 * y + x] = A[x, y]`). -/
abbrev KeccakState := Array (BitVec 64)

/-- The 24 round constants of Keccak-f[1600] (FIPS 202 §3.2.5). -/
def keccakRoundConstants : List (BitVec 64) :=
  [0x0000000000000001#64, 0x0000000000008082#64, 0x800000000000808a#64, 0x8000000080008000#64,
   0x000000000000808b#64, 0x0000000080000001#64, 0x8000000080008081#64, 0x8000000000008009#64,
   0x000000000000008a#64, 0x0000000000000088#64, 0x0000000080008009#64, 0x000000008000000a#64,
   0x000000008000808b#64, 0x800000000000008b#64, 0x8000000000008089#64, 0x8000000000008003#64,
   0x8000000000008002#64, 0x8000000000000080#64, 0x000000000000800a#64, 0x800000008000000a#64,
   0x8000000080008081#64, 0x8000000000008080#64, 0x0000000080000001#64, 0x8000000080008008#64]

/-- Rotation offsets `r[x, y]` indexed by `5 * y + x` (FIPS 202 Table 2). -/
def keccakRhoOffset (idx : Nat) : Nat :=
  match idx with
  | 0  => 0  | 1  => 1  | 2  => 62 | 3  => 28 | 4  => 27
  | 5  => 36 | 6  => 44 | 7  => 6  | 8  => 55 | 9  => 20
  | 10 => 3  | 11 => 10 | 12 => 43 | 13 => 25 | 14 => 39
  | 15 => 41 | 16 => 45 | 17 => 15 | 18 => 21 | 19 => 8
  | 20 => 18 | 21 => 2  | 22 => 61 | 23 => 56 | 24 => 14
  | _  => 0

/-- Safe lane read with `0#64` default. -/
def laneGet (s : KeccakState) (x y : Nat) : BitVec 64 :=
  s.getD (5 * y + x) 0#64

/-- One round of `Keccak-f[1600]` with round constant `rc` (FIPS 202 §3.2). -/
def keccakF1600Round (s : KeccakState) (rc : BitVec 64) : KeccakState :=
  let c : Array (BitVec 64) := Array.ofFn (n := 5) fun ⟨x, _⟩ =>
    laneGet s x 0 ^^^ laneGet s x 1 ^^^ laneGet s x 2 ^^^ laneGet s x 3 ^^^ laneGet s x 4
  let d : Array (BitVec 64) := Array.ofFn (n := 5) fun ⟨x, _⟩ =>
    c.getD ((x + 4) % 5) 0#64 ^^^ (c.getD ((x + 1) % 5) 0#64).rotateLeft 1
  let aTheta : KeccakState := Array.ofFn (n := 25) fun ⟨idx, _⟩ =>
    let x := idx % 5
    let y := idx / 5
    laneGet s x y ^^^ d.getD x 0#64
  let bRhoPi : KeccakState := Array.ofFn (n := 25) fun ⟨idx, _⟩ =>
    let x' := idx % 5
    let y' := idx / 5
    let x := (x' + 3 * y') % 5
    let y := x'
    (laneGet aTheta x y).rotateLeft (keccakRhoOffset (5 * y + x))
  Array.ofFn (n := 25) fun ⟨idx, _⟩ =>
    let x := idx % 5
    let y := idx / 5
    let chi := laneGet bRhoPi x y ^^^
      ((~~~(laneGet bRhoPi ((x + 1) % 5) y)) &&& laneGet bRhoPi ((x + 2) % 5) y)
    if idx == 0 then chi ^^^ rc else chi

/-- Full 24-round `Keccak-f[1600]` permutation (FIPS 202 §3.3). -/
def keccakF1600 (s : KeccakState) : KeccakState :=
  keccakRoundConstants.foldl keccakF1600Round s

/-- Initial all-zero 25-lane state. -/
def keccakZeroState : KeccakState :=
  Array.replicate 25 0#64

/-- Little-endian pack of 8 bytes into a 64-bit lane. -/
def packLane64 (bs : List (BitVec 8)) (off : Nat) : BitVec 64 :=
  (bs.getD off 0#8).zeroExtend 64 |||
  ((bs.getD (off + 1) 0#8).zeroExtend 64 <<< 8) |||
  ((bs.getD (off + 2) 0#8).zeroExtend 64 <<< 16) |||
  ((bs.getD (off + 3) 0#8).zeroExtend 64 <<< 24) |||
  ((bs.getD (off + 4) 0#8).zeroExtend 64 <<< 32) |||
  ((bs.getD (off + 5) 0#8).zeroExtend 64 <<< 40) |||
  ((bs.getD (off + 6) 0#8).zeroExtend 64 <<< 48) |||
  ((bs.getD (off + 7) 0#8).zeroExtend 64 <<< 56)

/-- Unpack a 64-bit lane into 8 little-endian bytes. -/
def unpackLane64 (w : BitVec 64) : List (BitVec 8) :=
  [(w >>> 0).truncate 8, (w >>> 8).truncate 8, (w >>> 16).truncate 8, (w >>> 24).truncate 8,
   (w >>> 32).truncate 8, (w >>> 40).truncate 8, (w >>> 48).truncate 8, (w >>> 56).truncate 8]

/-- XOR a `rateBytes`-byte block (`rateBytes = 8 * rateLanes`) into state `s` and permute. -/
def keccakAbsorbBlock (rateLanes : Nat) (s : KeccakState) (blk : List (BitVec 8)) :
    KeccakState :=
  let s' : KeccakState := Array.ofFn (n := 25) fun ⟨idx, _⟩ =>
    if idx < rateLanes then s.getD idx 0#64 ^^^ packLane64 blk (8 * idx)
    else s.getD idx 0#64
  keccakF1600 s'

/-- Pad `msg` with FIPS 202 multi-rate padding (`dsByte` at `msg.length`, `0x80` XORed into the
last byte of the final `rateBytes` block) into a list of `rateBytes`-byte blocks. -/
def keccakPadBlocks (rateBytes : Nat) (dsByte : BitVec 8) (msg : List (BitVec 8)) :
    List (List (BitVec 8)) :=
  if rateBytes == 0 then [] else
  let fullCount := msg.length / rateBytes
  let remLen := msg.length % rateBytes
  let fullBlocks := (List.range fullCount).map fun i => (msg.drop (i * rateBytes)).take rateBytes
  let tailBytes := msg.drop (fullCount * rateBytes)
  let lastBlock := (List.range rateBytes).map fun j =>
    let base : BitVec 8 :=
      if j < remLen then tailBytes.getD j 0#8
      else if j == remLen then dsByte
      else 0#8
    if j == rateBytes - 1 then base ^^^ 0x80#8 else base
  fullBlocks ++ [lastBlock]

/-- Absorb all padded blocks of `msg` at `rateLanes` (`rateBytes = 8 * rateLanes`). -/
def keccakAbsorb (rateLanes : Nat) (dsByte : BitVec 8) (msg : List (BitVec 8)) :
    KeccakState :=
  (keccakPadBlocks (8 * rateLanes) dsByte msg).foldl (keccakAbsorbBlock rateLanes) keccakZeroState

/-- Extract the first `rateLanes` lanes of `s` as `8 * rateLanes` little-endian bytes. -/
def keccakExtractRate (rateLanes : Nat) (s : KeccakState) : List (BitVec 8) :=
  ((List.range rateLanes).map fun idx => unpackLane64 (s.getD idx 0#64)).flatten

/-- Squeeze `numBlocks` blocks of `8 * rateLanes` bytes starting from post-absorb state `s`
(where `s` has already undergone the final absorb `keccakF1600`). -/
def keccakSqueezeBlocks (rateLanes : Nat) : Nat → KeccakState → List (BitVec 8)
  | 0, _ => []
  | 1, s => keccakExtractRate rateLanes s
  | n + 2, s => keccakExtractRate rateLanes s ++ keccakSqueezeBlocks rateLanes (n + 1) (keccakF1600 s)

/-- Generic FIPS 202 sponge producing `outLen` bytes (`rateLanes > 0`). -/
def keccakSponge (rateLanes : Nat) (dsByte : BitVec 8) (outLen : Nat)
    (msg : List (BitVec 8)) : List (BitVec 8) :=
  let rateBytes := 8 * rateLanes
  let nBlocks := (outLen + rateBytes - 1) / rateBytes
  let raw := keccakSqueezeBlocks rateLanes nBlocks (keccakAbsorb rateLanes dsByte msg)
  (List.range outLen).map fun i => raw.getD i 0#8

/-- FIPS 202 `SHA3-256` (`rate = 136 = 17 * 8`, `ds = 0x06`, `out = 32`). -/
def sha3_256List (msg : List (BitVec 8)) : List (BitVec 8) :=
  keccakSponge 17 0x06#8 32 msg

/-- FIPS 202 `SHA3-256` returning a 32-byte `List.Vector`. -/
def sha3_256 (msg : List (BitVec 8)) : List.Vector (BitVec 8) 32 :=
  ⟨sha3_256List msg, by simp [sha3_256List, keccakSponge]⟩

/-- FIPS 202 `SHA3-512` (`rate = 72 = 9 * 8`, `ds = 0x06`, `out = 64`). -/
def sha3_512List (msg : List (BitVec 8)) : List (BitVec 8) :=
  keccakSponge 9 0x06#8 64 msg

/-- FIPS 202 `SHA3-512` returning a 64-byte `List.Vector`. -/
def sha3_512 (msg : List (BitVec 8)) : List.Vector (BitVec 8) 64 :=
  ⟨sha3_512List msg, by simp [sha3_512List, keccakSponge]⟩

/-- FIPS 202 `SHAKE-256` (`rate = 136 = 17 * 8`, `ds = 0x1f`) returning `outLen` bytes. -/
def shake256List (outLen : Nat) (msg : List (BitVec 8)) : List (BitVec 8) :=
  keccakSponge 17 0x1f#8 outLen msg

/-- FIPS 202 `SHAKE-256` returning an `outLen`-byte `List.Vector`. -/
def shake256 (outLen : Nat) (msg : List (BitVec 8)) : List.Vector (BitVec 8) outLen :=
  ⟨shake256List outLen msg, by simp [shake256List, keccakSponge]⟩

/-- FIPS 202 `SHAKE-128` (`rate = 168 = 21 * 8`, `ds = 0x1f`) returning `outLen` bytes. -/
def shake128List (outLen : Nat) (msg : List (BitVec 8)) : List (BitVec 8) :=
  keccakSponge 21 0x1f#8 outLen msg

/-- Apply `keccakF1600` `n` times. -/
def keccakPermuteN : Nat → KeccakState → KeccakState
  | 0, s => s
  | n + 1, s => keccakPermuteN n (keccakF1600 s)

/-- The `blkIdx`-th 168-byte squeezed block of `SHAKE-128(msg)` (`blkIdx = 0` is bytes `0..168`). -/
def shake128BlockAt (msg : List (BitVec 8)) (blkIdx : Nat) : List (BitVec 8) :=
  let s0 := keccakAbsorb 21 0x1f#8 msg
  let sk := keccakPermuteN blkIdx s0
  keccakExtractRate 21 sk

end CryptoGames.SHA3

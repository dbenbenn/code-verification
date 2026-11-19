/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.Basic

/-!
# Shared Pure Models & Memory Layouts for ARMv8 Hardware AES-256 (`CryptoAes.Armv8.Defs`)

Pure `BitVec 32` / `BitVec 128` functional models matching the compiled `aes` `0.9.1` `aes::armv8`
routines (`expand_key::<32, 15>`, `inv_expanded_keys::<15>`, `encrypt::<15>`, `decrypt::<15>`,
`decrypt_par::<15, U17>`) and flat `↦₁₂₈` separation-logic layouts (`roundKeys15At`, `blocks17At`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs

open Arm64

/-! ## 1. Elementary `evalAesOp` Symmetry & `vd`-Irrelevance Lemmas -/

theorem evalAesOp_aese_comm (x y : BitVec 128) :
    evalAesOp .AESE x y = evalAesOp .AESE y x := by
  have h : x ^^^ y = y ^^^ x := BitVec.xor_comm x y
  simp only [evalAesOp, h]

theorem evalAesOp_aesd_comm (x y : BitVec 128) :
    evalAesOp .AESD x y = evalAesOp .AESD y x := by
  have h : x ^^^ y = y ^^^ x := BitVec.xor_comm x y
  simp only [evalAesOp, h]

@[simp] theorem evalAesOp_aesmc_vd_irrel (vd vn : BitVec 128) :
    evalAesOp .AESMC vd vn = evalAesOp .AESMC 0#128 vn := rfl

@[simp] theorem evalAesOp_aesimc_vd_irrel (vd vn : BitVec 128) :
    evalAesOp .AESIMC vd vn = evalAesOp .AESIMC 0#128 vn := rfl

/-! ## 2. Little-Endian Packing & RCON Table (`[u32; 10]`, `40` Bytes) -/

/-- The 10 little-endian `u32` round constants in `aes::armv8::expand::RCON` (`0x414478`). -/
@[expose] def aesRconWords : Vector (BitVec 32) 10 :=
  #v[0x01#32, 0x02#32, 0x04#32, 0x08#32, 0x10#32, 0x20#32, 0x40#32, 0x80#32, 0x1b#32, 0x36#32]

/-- The 40 `.rodata` bytes of `aes::armv8::expand::RCON` (`10` little-endian `u32` words). -/
@[expose] def aesRconBytes : List (BitVec 8) :=
  [0x01#8, 0x00#8, 0x00#8, 0x00#8,
   0x02#8, 0x00#8, 0x00#8, 0x00#8,
   0x04#8, 0x00#8, 0x00#8, 0x00#8,
   0x08#8, 0x00#8, 0x00#8, 0x00#8,
   0x10#8, 0x00#8, 0x00#8, 0x00#8,
   0x20#8, 0x00#8, 0x00#8, 0x00#8,
   0x40#8, 0x00#8, 0x00#8, 0x00#8,
   0x80#8, 0x00#8, 0x00#8, 0x00#8,
   0x1b#8, 0x00#8, 0x00#8, 0x00#8,
   0x36#8, 0x00#8, 0x00#8, 0x00#8]

@[expose] def u32OfBytesLE (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  b3 ++ b2 ++ b1 ++ b0

@[expose] def bytesToU32LE (bs : List (BitVec 8)) (off : Nat) : BitVec 32 :=
  u32OfBytesLE (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
    (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)

@[expose] def u32ToBytesLE (w : BitVec 32) : List (BitVec 8) :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

@[expose] def u128OfU32sLE (w0 w1 w2 w3 : BitVec 32) : BitVec 128 :=
  w3 ++ w2 ++ w1 ++ w0

@[expose] def bytesToU128LE (bs : List (BitVec 8)) : BitVec 128 :=
  u128OfU32sLE (bytesToU32LE bs 0) (bytesToU32LE bs 4)
    (bytesToU32LE bs 8) (bytesToU32LE bs 12)

@[expose] def u128ToBytesLE (v : BitVec 128) : List (BitVec 8) :=
  List.ofFn fun i : Fin 16 => v.extractLsb' (8 * i.val) 8

/-! ## 3. Pure ARMv8 AES-256 Key Schedule & Block Operations -/

/-- `dup v1.4s, w; aese v1.16b, v0.16b (v0 = 0); fmov w, s1`. -/
@[expose] def armv8SubWord (w : BitVec 32) : BitVec 32 :=
  let v1 : BitVec 128 := w ++ w ++ w ++ w
  (evalAesOp .AESE v1 0#128).extractLsb' 0 32

/-- Single loop step `k ∈ [0, 52)` (`i = k + 8`) of `expand_key::<32, 15>`. -/
@[expose] def armv8ExpandStep (ws : Vector (BitVec 32) 60) (k : Fin 52) : Vector (BitVec 32) 60 :=
  let i : Nat := k.val + 8
  let prev : BitVec 32 := ws[k.val + 7]
  let transformed : BitVec 32 :=
    if i % 8 = 4 then
      armv8SubWord prev
    else if i % 8 = 0 then
      let rc := aesRconWords.getD (i / 8 - 1) 0#32
      rc ^^^ (armv8SubWord prev).rotateRight 8
    else
      prev
  ws.setIfInBounds i (ws[k.val] ^^^ transformed)

/-- 60-word key expansion array built by `expand_key::<32, 15>`. -/
@[expose] def armv8ExpandKeyWords (keyBytes : List (BitVec 8)) : Vector (BitVec 32) 60 :=
  let init : Vector (BitVec 32) 60 :=
    Vector.ofFn fun j : Fin 60 =>
      if j.val < 8 then bytesToU32LE keyBytes (4 * j.val) else 0#32
  Fin.foldl 52 armv8ExpandStep init

/-- Pack 60 `u32` words into 15 128-bit round keys (`240` bytes). -/
@[expose] def armv8PackRoundKeys (ws : Vector (BitVec 32) 60) : Vector (BitVec 128) 15 :=
  Vector.ofFn fun r : Fin 15 =>
    u128OfU32sLE ws[4 * r.val] ws[4 * r.val + 1] ws[4 * r.val + 2] ws[4 * r.val + 3]

/-- Pure functional model of `aes::armv8::expand::expand_key::<32, 15>`. -/
@[expose] def armv8ExpandKey (keyBytes : List (BitVec 8)) : Vector (BitVec 128) 15 :=
  armv8PackRoundKeys (armv8ExpandKeyWords keyBytes)

/-- Pure functional model of `aes::armv8::expand::inv_expanded_keys::<15>`. -/
@[expose] def armv8InvExpandedKeys (ek : Vector (BitVec 128) 15) : Vector (BitVec 128) 15 :=
  #v[ek[14],
     evalAesOp .AESIMC 0#128 ek[13],
     evalAesOp .AESIMC 0#128 ek[12],
     evalAesOp .AESIMC 0#128 ek[11],
     evalAesOp .AESIMC 0#128 ek[10],
     evalAesOp .AESIMC 0#128 ek[9],
     evalAesOp .AESIMC 0#128 ek[8],
     evalAesOp .AESIMC 0#128 ek[7],
     evalAesOp .AESIMC 0#128 ek[6],
     evalAesOp .AESIMC 0#128 ek[5],
     evalAesOp .AESIMC 0#128 ek[4],
     evalAesOp .AESIMC 0#128 ek[3],
     evalAesOp .AESIMC 0#128 ek[2],
     evalAesOp .AESIMC 0#128 ek[1],
     ek[0]]

/-- Pure functional model of `aes::armv8::encdec::encrypt::<15>`. -/
@[expose] def armv8Encrypt15 (ek : Vector (BitVec 128) 15) (blk : BitVec 128) : BitVec 128 :=
  let s13 := Fin.foldl 13 (fun s (r : Fin 13) =>
    evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[r.val] s)) blk
  let s14 := evalAesOp .AESE ek[13] s13
  ek[14] ^^^ s14

/-- Pure functional model of `aes::armv8::encdec::decrypt::<15>`. -/
@[expose] def armv8Decrypt15 (dk : Vector (BitVec 128) 15) (blk : BitVec 128) : BitVec 128 :=
  let s13 := Fin.foldl 13 (fun s (r : Fin 13) =>
    evalAesOp .AESIMC 0#128 (evalAesOp .AESD dk[r.val] s)) blk
  let s14 := evalAesOp .AESD dk[13] s13
  dk[14] ^^^ s14

/-- Pure functional model of `aes::armv8::encdec::decrypt_par::<15, U17>`. -/
@[expose] def armv8DecryptPar17 (dk : Vector (BitVec 128) 15)
    (blks : Vector (BitVec 128) 17) : Vector (BitVec 128) 17 :=
  blks.map (armv8Decrypt15 dk)

/-! ## 4. Flat Separation-Logic Layouts (`roundKeys15At`, `blocks17At`) -/

@[expose] def roundKeys15Bytes (rks : Vector (BitVec 128) 15) : List (BitVec 8) :=
  (rks.toList.map u128ToBytesLE).flatten

@[expose] def blocks17Bytes (blks : Vector (BitVec 128) 17) : List (BitVec 8) :=
  (blks.toList.map u128ToBytesLE).flatten

/-- Flat 15 × 128-bit (`240`-byte) separation-logic layout for ARMv8 AES-256 round keys. -/
@[expose] def roundKeys15At (ptr : BitVec 64) (rks : Vector (BitVec 128) 15) : SepProp :=
  (ptr ↦₁₂₈ rks[0]) ∗
  ((ptr + 0x10#64) ↦₁₂₈ rks[1]) ∗
  ((ptr + 0x20#64) ↦₁₂₈ rks[2]) ∗
  ((ptr + 0x30#64) ↦₁₂₈ rks[3]) ∗
  ((ptr + 0x40#64) ↦₁₂₈ rks[4]) ∗
  ((ptr + 0x50#64) ↦₁₂₈ rks[5]) ∗
  ((ptr + 0x60#64) ↦₁₂₈ rks[6]) ∗
  ((ptr + 0x70#64) ↦₁₂₈ rks[7]) ∗
  ((ptr + 0x80#64) ↦₁₂₈ rks[8]) ∗
  ((ptr + 0x90#64) ↦₁₂₈ rks[9]) ∗
  ((ptr + 0xa0#64) ↦₁₂₈ rks[10]) ∗
  ((ptr + 0xb0#64) ↦₁₂₈ rks[11]) ∗
  ((ptr + 0xc0#64) ↦₁₂₈ rks[12]) ∗
  ((ptr + 0xd0#64) ↦₁₂₈ rks[13]) ∗
  ((ptr + 0xe0#64) ↦₁₂₈ rks[14])

/-- Flat 17 × 128-bit (`272`-byte) separation-logic layout for 17-block parallel decryption. -/
@[expose] def blocks17At (ptr : BitVec 64) (blks : Vector (BitVec 128) 17) : SepProp :=
  (ptr ↦₁₂₈ blks[0]) ∗
  ((ptr + 0x10#64) ↦₁₂₈ blks[1]) ∗
  ((ptr + 0x20#64) ↦₁₂₈ blks[2]) ∗
  ((ptr + 0x30#64) ↦₁₂₈ blks[3]) ∗
  ((ptr + 0x40#64) ↦₁₂₈ blks[4]) ∗
  ((ptr + 0x50#64) ↦₁₂₈ blks[5]) ∗
  ((ptr + 0x60#64) ↦₁₂₈ blks[6]) ∗
  ((ptr + 0x70#64) ↦₁₂₈ blks[7]) ∗
  ((ptr + 0x80#64) ↦₁₂₈ blks[8]) ∗
  ((ptr + 0x90#64) ↦₁₂₈ blks[9]) ∗
  ((ptr + 0xa0#64) ↦₁₂₈ blks[10]) ∗
  ((ptr + 0xb0#64) ↦₁₂₈ blks[11]) ∗
  ((ptr + 0xc0#64) ↦₁₂₈ blks[12]) ∗
  ((ptr + 0xd0#64) ↦₁₂₈ blks[13]) ∗
  ((ptr + 0xe0#64) ↦₁₂₈ blks[14]) ∗
  ((ptr + 0xf0#64) ↦₁₂₈ blks[15]) ∗
  ((ptr + 0x100#64) ↦₁₂₈ blks[16])

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs

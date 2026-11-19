/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref -- proof-setup: allow-public-import

/-!
# 32-Bit Block Cells, `.rodata` `K32` Cells, and 176-Byte Stack Frame Lemmas

Memory-layout helpers shared by `sha2::sha256::compress256` and `libcrux_sha2::hacl::sha256_update`:
1. Big-endian byte decoding (`rev32_64` vs. `beU32OfBytes`) and 64-byte block decomposition into
   16 `↦₃₂` cells (`pointsToBytes_64_eq_cells32`).
2. Read-only `.rodata` `K32` decomposition (`sha256KBytes`, `pointsToBytesRO_sha256KBytes_eq_chunks`).
3. O(1) 176-byte (`0xb0`) stack-frame elimination and recombination (`stackFrame176_elim`,
   `stackFrame176_entails`) and top-register `SepWP` rewrites.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref (sha256K beU32OfBytes)

/-! ## 1. Big-Endian Byte Decoding (`rev32` vs. `beU32OfBytes`) & 64-Byte Block Cells -/

theorem rev32_pack32 (b0 b1 b2 b3 : BitVec 8) :
    (rev32_64 ((pack32 b0 b1 b2 b3).zeroExtend 64)).truncate 32 =
      beU32OfBytes [b0, b1, b2, b3] := by
  unfold rev32_64 pack32 beU32OfBytes
  simp only [List.foldl_cons, List.foldl_nil]
  bv_slice

theorem take4_drop_eq_list {bs : List (BitVec 8)} {off : Nat} (h : off + 4 ≤ bs.length) :
    (bs.drop off).take 4 =
      [bs.getD off 0#8, bs.getD (off + 1) 0#8, bs.getD (off + 2) 0#8, bs.getD (off + 3) 0#8] := by
  have hd0 := List.drop_eq_getD_cons bs off 0#8 (by omega)
  have hd1 := List.drop_eq_getD_cons bs (off + 1) 0#8 (by omega)
  have hd2 := List.drop_eq_getD_cons bs (off + 2) 0#8 (by omega)
  have hd3 := List.drop_eq_getD_cons bs (off + 3) 0#8 (by omega)
  rw [hd0, List.take_succ_cons, hd1, List.take_succ_cons, hd2, List.take_succ_cons,
      hd3, List.take_succ_cons, List.take_zero]

/-- 32-bit little-endian word at byte offset `off` in `bs`. -/
def readLE32 (bs : List (BitVec 8)) (off : Nat) : BitVec 32 :=
  (ByteSlice.readLE bs off 4).truncate 32

theorem pack32_eq_readLE32 (bs : List (BitVec 8)) (off : Nat) :
    pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
      (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8) =
      readLE32 bs off := by
  unfold readLE32
  rw [ByteSlice.readLE_four]
  bv_slice

theorem rev32_readLE32_eq_beU32OfBytes (bs : List (BitVec 8)) (off : Nat)
    (h : off + 4 ≤ bs.length) :
    (rev32_64 ((readLE32 bs off).zeroExtend 64)).truncate 32 =
      beU32OfBytes ((bs.drop off).take 4) := by
  rw [← pack32_eq_readLE32, take4_drop_eq_list h, rev32_pack32]

theorem pointsToBytes_take4_eq_pointsTo32_readLE32 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 4 ≤ bs.length) :
    (a ↦ₛ (bs.drop off).take 4) = (a ↦₃₂ readLE32 bs off) := by
  rw [pointsToBytes_take4_eq_pointsTo32 a bs off h, pack32_eq_readLE32]

theorem pointsToBytes_drop_step4 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 4 ≤ bs.length) :
    ((a + BitVec.ofNat 64 off) ↦ₛ bs.drop off) =
      ((a + BitVec.ofNat 64 off) ↦₃₂ readLE32 bs off) ∗
      ((a + BitVec.ofNat 64 (off + 4)) ↦ₛ bs.drop (off + 4)) := by
  have htd := pointsToBytes_take_drop (a + BitVec.ofNat 64 off) 4 (bs.drop off) (by simp; omega)
  rw [htd, pointsToBytes_take4_eq_pointsTo32_readLE32 _ bs off h, List.drop_drop,
      BitVec.add_assoc, ← BitVec.ofNat_add]

theorem pointsToBytes_64_eq_cells32 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 64) :
    (a ↦ₛ bs) =
      ((a ↦₃₂ readLE32 bs 0) ∗
       ((a + 4#64) ↦₃₂ readLE32 bs 4) ∗
       ((a + 8#64) ↦₃₂ readLE32 bs 8) ∗
       ((a + 12#64) ↦₃₂ readLE32 bs 12) ∗
       ((a + 16#64) ↦₃₂ readLE32 bs 16) ∗
       ((a + 20#64) ↦₃₂ readLE32 bs 20) ∗
       ((a + 24#64) ↦₃₂ readLE32 bs 24) ∗
       ((a + 28#64) ↦₃₂ readLE32 bs 28) ∗
       ((a + 32#64) ↦₃₂ readLE32 bs 32) ∗
       ((a + 36#64) ↦₃₂ readLE32 bs 36) ∗
       ((a + 40#64) ↦₃₂ readLE32 bs 40) ∗
       ((a + 44#64) ↦₃₂ readLE32 bs 44) ∗
       ((a + 48#64) ↦₃₂ readLE32 bs 48) ∗
       ((a + 52#64) ↦₃₂ readLE32 bs 52) ∗
       ((a + 56#64) ↦₃₂ readLE32 bs 56) ∗
       ((a + 60#64) ↦₃₂ readLE32 bs 60)) := by
  have h0 : (a ↦ₛ bs) = ((a + BitVec.ofNat 64 0) ↦ₛ bs.drop 0) := by
    rw [BitVec.add_zero, List.drop_zero]
  rw [h0]
  repeat (rw [pointsToBytes_drop_step4 a bs _ (by omega)])
  have hdrop : bs.drop 64 = [] := List.drop_of_length_le (by omega)
  rw [hdrop, pointsToBytes_nil, sepConj_emp]
  simp only [BitVec.add_zero]

theorem pointsToBytesRO_take_drop (ptr : BitVec 64) (n : Nat) (bs : List (BitVec 8))
    (hn : n ≤ bs.length) :
    (ptr ↦ᵣ bs) = (ptr ↦ᵣ bs.take n) ∗ ((ptr + BitVec.ofNat 64 n) ↦ᵣ bs.drop n) := by
  have h := pointsToBytesRO_append ptr (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take_of_le hn] at h
  exact h

theorem pointsToBytesRO_take4_eq_pointsTo32RO_readLE32 (a : BitVec 64) (bs : List (BitVec 8))
    (off : Nat) (h : off + 4 ≤ bs.length) :
    (a ↦ᵣ (bs.drop off).take 4) = (a ↦₃₂ᵣ readLE32 bs off) := by
  rw [pointsToBytesRO_take4_eq_pointsTo32RO a bs off h, pack32_eq_readLE32]

theorem pointsToBytesRO_drop_step4 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 4 ≤ bs.length) :
    ((a + BitVec.ofNat 64 off) ↦ᵣ bs.drop off) =
      ((a + BitVec.ofNat 64 off) ↦₃₂ᵣ readLE32 bs off) ∗
      ((a + BitVec.ofNat 64 (off + 4)) ↦ᵣ bs.drop (off + 4)) := by
  have htd := pointsToBytesRO_take_drop (a + BitVec.ofNat 64 off) 4 (bs.drop off) (by simp; omega)
  rw [htd, pointsToBytesRO_take4_eq_pointsTo32RO_readLE32 _ bs off h, List.drop_drop,
      BitVec.add_assoc, ← BitVec.ofNat_add]

theorem pointsToBytesRO_64_eq_cells32 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 64) :
    (a ↦ᵣ bs) =
      ((a ↦₃₂ᵣ readLE32 bs 0) ∗
       ((a + 4#64) ↦₃₂ᵣ readLE32 bs 4) ∗
       ((a + 8#64) ↦₃₂ᵣ readLE32 bs 8) ∗
       ((a + 12#64) ↦₃₂ᵣ readLE32 bs 12) ∗
       ((a + 16#64) ↦₃₂ᵣ readLE32 bs 16) ∗
       ((a + 20#64) ↦₃₂ᵣ readLE32 bs 20) ∗
       ((a + 24#64) ↦₃₂ᵣ readLE32 bs 24) ∗
       ((a + 28#64) ↦₃₂ᵣ readLE32 bs 28) ∗
       ((a + 32#64) ↦₃₂ᵣ readLE32 bs 32) ∗
       ((a + 36#64) ↦₃₂ᵣ readLE32 bs 36) ∗
       ((a + 40#64) ↦₃₂ᵣ readLE32 bs 40) ∗
       ((a + 44#64) ↦₃₂ᵣ readLE32 bs 44) ∗
       ((a + 48#64) ↦₃₂ᵣ readLE32 bs 48) ∗
       ((a + 52#64) ↦₃₂ᵣ readLE32 bs 52) ∗
       ((a + 56#64) ↦₃₂ᵣ readLE32 bs 56) ∗
       ((a + 60#64) ↦₃₂ᵣ readLE32 bs 60)) := by
  have h0 : (a ↦ᵣ bs) = ((a + BitVec.ofNat 64 0) ↦ᵣ bs.drop 0) := by
    rw [BitVec.add_zero, List.drop_zero]
  rw [h0]
  repeat (rw [pointsToBytesRO_drop_step4 a bs _ (by omega)])
  have hdrop : bs.drop 64 = [] := List.drop_of_length_le (by omega)
  rw [hdrop, pointsToBytesRO_nil, sepConj_emp]
  simp only [BitVec.add_zero]

/-! ## 2. `.rodata` `K32` 64-Word Read-Only Cell Decomposition -/

/-- The 256 little-endian bytes of `sha2::consts::K32`. -/
@[expose] def sha256KBytes : List (BitVec 8) :=
  sha256K.flatMap unpack32

theorem sha256K_length : sha256K.length = 64 := rfl

private theorem flatMap_unpack32_4_length (w0 w1 w2 w3 : BitVec 32) :
    ([w0, w1, w2, w3].flatMap unpack32).length = 16 := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, unpack32_length]

private theorem pointsToBytesRO_4words (a : BitVec 64) (w0 w1 w2 w3 : BitVec 32) :
    (a ↦ᵣ [w0, w1, w2, w3].flatMap unpack32) =
      ((a ↦₃₂ᵣ w0) ∗ ((a + 4#64) ↦₃₂ᵣ w1) ∗ ((a + 8#64) ↦₃₂ᵣ w2) ∗ ((a + 12#64) ↦₃₂ᵣ w3)) := by
  change (a ↦ᵣ (unpack32 w0 ++ (unpack32 w1 ++ (unpack32 w2 ++ (unpack32 w3 ++ []))))) = _
  rw [List.append_nil,
      pointsToBytesRO_append, unpack32_length, ← pointsTo32RO_eq_pointsToBytesRO,
      pointsToBytesRO_append, unpack32_length, ← pointsTo32RO_eq_pointsToBytesRO,
      pointsToBytesRO_append, unpack32_length, ← pointsTo32RO_eq_pointsToBytesRO,
      ← pointsTo32RO_eq_pointsToBytesRO]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem flatMap_unpack32_16_length
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 32) :
    ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15].flatMap unpack32).length = 64 := by
  change (([w0, w1, w2, w3] ++ ([w4, w5, w6, w7] ++ ([w8, w9, w10, w11] ++ [w12, w13, w14, w15]))).flatMap unpack32).length = 64
  simp only [List.flatMap_append, List.length_append, flatMap_unpack32_4_length]

private theorem pointsToBytesRO_16words (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 32) :
    (a ↦ᵣ [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15].flatMap unpack32) =
      ((a ↦₃₂ᵣ w0) ∗ ((a + 4#64) ↦₃₂ᵣ w1) ∗ ((a + 8#64) ↦₃₂ᵣ w2) ∗ ((a + 12#64) ↦₃₂ᵣ w3) ∗
       ((a + 16#64) ↦₃₂ᵣ w4) ∗ ((a + 20#64) ↦₃₂ᵣ w5) ∗ ((a + 24#64) ↦₃₂ᵣ w6) ∗ ((a + 28#64) ↦₃₂ᵣ w7) ∗
       ((a + 32#64) ↦₃₂ᵣ w8) ∗ ((a + 36#64) ↦₃₂ᵣ w9) ∗ ((a + 40#64) ↦₃₂ᵣ w10) ∗ ((a + 44#64) ↦₃₂ᵣ w11) ∗
       ((a + 48#64) ↦₃₂ᵣ w12) ∗ ((a + 52#64) ↦₃₂ᵣ w13) ∗ ((a + 56#64) ↦₃₂ᵣ w14) ∗ ((a + 60#64) ↦₃₂ᵣ w15)) := by
  change (a ↦ᵣ (([w0, w1, w2, w3] ++ ([w4, w5, w6, w7] ++ ([w8, w9, w10, w11] ++ [w12, w13, w14, w15]))).flatMap unpack32)) = _
  rw [List.flatMap_append, pointsToBytesRO_append, flatMap_unpack32_4_length, pointsToBytesRO_4words,
      List.flatMap_append, pointsToBytesRO_append, flatMap_unpack32_4_length, pointsToBytesRO_4words,
      List.flatMap_append, pointsToBytesRO_append, flatMap_unpack32_4_length, pointsToBytesRO_4words,
      pointsToBytesRO_4words]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

@[expose] def sha2K32Cells0 (a : BitVec 64) : SepProp :=
  (a ↦₃₂ᵣ sha256K.getD 0 0#32) ∗ ((a + 4#64) ↦₃₂ᵣ sha256K.getD 1 0#32) ∗
  ((a + 8#64) ↦₃₂ᵣ sha256K.getD 2 0#32) ∗ ((a + 12#64) ↦₃₂ᵣ sha256K.getD 3 0#32) ∗
  ((a + 16#64) ↦₃₂ᵣ sha256K.getD 4 0#32) ∗ ((a + 20#64) ↦₃₂ᵣ sha256K.getD 5 0#32) ∗
  ((a + 24#64) ↦₃₂ᵣ sha256K.getD 6 0#32) ∗ ((a + 28#64) ↦₃₂ᵣ sha256K.getD 7 0#32) ∗
  ((a + 32#64) ↦₃₂ᵣ sha256K.getD 8 0#32) ∗ ((a + 36#64) ↦₃₂ᵣ sha256K.getD 9 0#32) ∗
  ((a + 40#64) ↦₃₂ᵣ sha256K.getD 10 0#32) ∗ ((a + 44#64) ↦₃₂ᵣ sha256K.getD 11 0#32) ∗
  ((a + 48#64) ↦₃₂ᵣ sha256K.getD 12 0#32) ∗ ((a + 52#64) ↦₃₂ᵣ sha256K.getD 13 0#32) ∗
  ((a + 56#64) ↦₃₂ᵣ sha256K.getD 14 0#32) ∗ ((a + 60#64) ↦₃₂ᵣ sha256K.getD 15 0#32)

@[expose] def sha2K32Cells1 (a : BitVec 64) : SepProp :=
  ((a + 64#64) ↦₃₂ᵣ sha256K.getD 16 0#32) ∗ ((a + 68#64) ↦₃₂ᵣ sha256K.getD 17 0#32) ∗
  ((a + 72#64) ↦₃₂ᵣ sha256K.getD 18 0#32) ∗ ((a + 76#64) ↦₃₂ᵣ sha256K.getD 19 0#32) ∗
  ((a + 80#64) ↦₃₂ᵣ sha256K.getD 20 0#32) ∗ ((a + 84#64) ↦₃₂ᵣ sha256K.getD 21 0#32) ∗
  ((a + 88#64) ↦₃₂ᵣ sha256K.getD 22 0#32) ∗ ((a + 92#64) ↦₃₂ᵣ sha256K.getD 23 0#32) ∗
  ((a + 96#64) ↦₃₂ᵣ sha256K.getD 24 0#32) ∗ ((a + 100#64) ↦₃₂ᵣ sha256K.getD 25 0#32) ∗
  ((a + 104#64) ↦₃₂ᵣ sha256K.getD 26 0#32) ∗ ((a + 108#64) ↦₃₂ᵣ sha256K.getD 27 0#32) ∗
  ((a + 112#64) ↦₃₂ᵣ sha256K.getD 28 0#32) ∗ ((a + 116#64) ↦₃₂ᵣ sha256K.getD 29 0#32) ∗
  ((a + 120#64) ↦₃₂ᵣ sha256K.getD 30 0#32) ∗ ((a + 124#64) ↦₃₂ᵣ sha256K.getD 31 0#32)

@[expose] def sha2K32Cells2 (a : BitVec 64) : SepProp :=
  ((a + 128#64) ↦₃₂ᵣ sha256K.getD 32 0#32) ∗ ((a + 132#64) ↦₃₂ᵣ sha256K.getD 33 0#32) ∗
  ((a + 136#64) ↦₃₂ᵣ sha256K.getD 34 0#32) ∗ ((a + 140#64) ↦₃₂ᵣ sha256K.getD 35 0#32) ∗
  ((a + 144#64) ↦₃₂ᵣ sha256K.getD 36 0#32) ∗ ((a + 148#64) ↦₃₂ᵣ sha256K.getD 37 0#32) ∗
  ((a + 152#64) ↦₃₂ᵣ sha256K.getD 38 0#32) ∗ ((a + 156#64) ↦₃₂ᵣ sha256K.getD 39 0#32) ∗
  ((a + 160#64) ↦₃₂ᵣ sha256K.getD 40 0#32) ∗ ((a + 164#64) ↦₃₂ᵣ sha256K.getD 41 0#32) ∗
  ((a + 168#64) ↦₃₂ᵣ sha256K.getD 42 0#32) ∗ ((a + 172#64) ↦₃₂ᵣ sha256K.getD 43 0#32) ∗
  ((a + 176#64) ↦₃₂ᵣ sha256K.getD 44 0#32) ∗ ((a + 180#64) ↦₃₂ᵣ sha256K.getD 45 0#32) ∗
  ((a + 184#64) ↦₃₂ᵣ sha256K.getD 46 0#32) ∗ ((a + 188#64) ↦₃₂ᵣ sha256K.getD 47 0#32)

@[expose] def sha2K32Cells3 (a : BitVec 64) : SepProp :=
  ((a + 192#64) ↦₃₂ᵣ sha256K.getD 48 0#32) ∗ ((a + 196#64) ↦₃₂ᵣ sha256K.getD 49 0#32) ∗
  ((a + 200#64) ↦₃₂ᵣ sha256K.getD 50 0#32) ∗ ((a + 204#64) ↦₃₂ᵣ sha256K.getD 51 0#32) ∗
  ((a + 208#64) ↦₃₂ᵣ sha256K.getD 52 0#32) ∗ ((a + 212#64) ↦₃₂ᵣ sha256K.getD 53 0#32) ∗
  ((a + 216#64) ↦₃₂ᵣ sha256K.getD 54 0#32) ∗ ((a + 220#64) ↦₃₂ᵣ sha256K.getD 55 0#32) ∗
  ((a + 224#64) ↦₃₂ᵣ sha256K.getD 56 0#32) ∗ ((a + 228#64) ↦₃₂ᵣ sha256K.getD 57 0#32) ∗
  ((a + 232#64) ↦₃₂ᵣ sha256K.getD 58 0#32) ∗ ((a + 236#64) ↦₃₂ᵣ sha256K.getD 59 0#32) ∗
  ((a + 240#64) ↦₃₂ᵣ sha256K.getD 60 0#32) ∗ ((a + 244#64) ↦₃₂ᵣ sha256K.getD 61 0#32) ∗
  ((a + 248#64) ↦₃₂ᵣ sha256K.getD 62 0#32) ∗ ((a + 252#64) ↦₃₂ᵣ sha256K.getD 63 0#32)

private theorem sha256K_eq_chunks :
    sha256K =
      [sha256K.getD 0 0#32, sha256K.getD 1 0#32, sha256K.getD 2 0#32, sha256K.getD 3 0#32,
       sha256K.getD 4 0#32, sha256K.getD 5 0#32, sha256K.getD 6 0#32, sha256K.getD 7 0#32,
       sha256K.getD 8 0#32, sha256K.getD 9 0#32, sha256K.getD 10 0#32, sha256K.getD 11 0#32,
       sha256K.getD 12 0#32, sha256K.getD 13 0#32, sha256K.getD 14 0#32, sha256K.getD 15 0#32] ++
      ([sha256K.getD 16 0#32, sha256K.getD 17 0#32, sha256K.getD 18 0#32, sha256K.getD 19 0#32,
        sha256K.getD 20 0#32, sha256K.getD 21 0#32, sha256K.getD 22 0#32, sha256K.getD 23 0#32,
        sha256K.getD 24 0#32, sha256K.getD 25 0#32, sha256K.getD 26 0#32, sha256K.getD 27 0#32,
        sha256K.getD 28 0#32, sha256K.getD 29 0#32, sha256K.getD 30 0#32, sha256K.getD 31 0#32] ++
       ([sha256K.getD 32 0#32, sha256K.getD 33 0#32, sha256K.getD 34 0#32, sha256K.getD 35 0#32,
         sha256K.getD 36 0#32, sha256K.getD 37 0#32, sha256K.getD 38 0#32, sha256K.getD 39 0#32,
         sha256K.getD 40 0#32, sha256K.getD 41 0#32, sha256K.getD 42 0#32, sha256K.getD 43 0#32,
         sha256K.getD 44 0#32, sha256K.getD 45 0#32, sha256K.getD 46 0#32, sha256K.getD 47 0#32] ++
        [sha256K.getD 48 0#32, sha256K.getD 49 0#32, sha256K.getD 50 0#32, sha256K.getD 51 0#32,
         sha256K.getD 52 0#32, sha256K.getD 53 0#32, sha256K.getD 54 0#32, sha256K.getD 55 0#32,
         sha256K.getD 56 0#32, sha256K.getD 57 0#32, sha256K.getD 58 0#32, sha256K.getD 59 0#32,
         sha256K.getD 60 0#32, sha256K.getD 61 0#32, sha256K.getD 62 0#32, sha256K.getD 63 0#32])) := by
  decide

theorem pointsToBytesRO_sha256KBytes_eq_chunks (a : BitVec 64) :
    (a ↦ᵣ sha256KBytes) =
      sha2K32Cells0 a ∗ sha2K32Cells1 a ∗ sha2K32Cells2 a ∗ sha2K32Cells3 a := by
  unfold sha256KBytes
  rw [sha256K_eq_chunks,
      List.flatMap_append, pointsToBytesRO_append, flatMap_unpack32_16_length, pointsToBytesRO_16words,
      List.flatMap_append, pointsToBytesRO_append, flatMap_unpack32_16_length, pointsToBytesRO_16words,
      List.flatMap_append, pointsToBytesRO_append, flatMap_unpack32_16_length, pointsToBytesRO_16words,
      pointsToBytesRO_16words]
  unfold sha2K32Cells0 sha2K32Cells1 sha2K32Cells2 sha2K32Cells3
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## 3. O(1) Stack Cell Elimination & Recombination for 176-Byte (`0xb0`) Stack Frame -/

theorem cells_sub_elim {prog : Program} {target_pc : BitVec 64}
    {s : State} {R : SepProp} {sp : BitVec 64} {a k : Nat}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hk : k ≠ 0 := by decide) (ha : 8 ≤ a := by decide)
    (h : ∀ v : BitVec 64,
      SepWP prog target_pc s ((R ∗ ((sp - BitVec.ofNat 64 a) ↦₆₄ v)) ∗
        cells (sp - BitVec.ofNat 64 (a - 8)) (k - 1)) post oom) :
    SepWP prog target_pc s (R ∗ cells (sp - BitVec.ofNat 64 a) k) post oom := by
  rw [cells_sub_succ sp a k hk ha, sepExists_sepConj_right]
  apply SepWP.exists_elim
  intro v
  rw [← sepConj_assoc]
  exact h v

theorem stackFrame176_elim {prog : Program} {target_pc : BitVec 64}
    {s : State} {s0 : State} {R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 : BitVec 64),
      SepWP prog target_pc s
        (R ∗ stackAt (s0.sp - 168#64) 8 ∗
         ((s0.sp - 168#64) ↦₆₄ v1) ∗ ((s0.sp - 160#64) ↦₆₄ v2) ∗ ((s0.sp - 152#64) ↦₆₄ v3) ∗
         ((s0.sp - 144#64) ↦₆₄ v4) ∗ ((s0.sp - 136#64) ↦₆₄ v5) ∗ ((s0.sp - 128#64) ↦₆₄ v6) ∗
         ((s0.sp - 120#64) ↦₆₄ v7) ∗ ((s0.sp - 112#64) ↦₆₄ v8) ∗ ((s0.sp - 104#64) ↦₆₄ v9) ∗
         ((s0.sp - 96#64) ↦₆₄ v10) ∗ ((s0.sp - 88#64) ↦₆₄ v11) ∗ ((s0.sp - 80#64) ↦₆₄ v12) ∗
         ((s0.sp - 72#64) ↦₆₄ v13) ∗ ((s0.sp - 64#64) ↦₆₄ v14) ∗ ((s0.sp - 56#64) ↦₆₄ v15) ∗
         ((s0.sp - 48#64) ↦₆₄ v16) ∗ ((s0.sp - 40#64) ↦₆₄ v17) ∗ ((s0.sp - 32#64) ↦₆₄ v18) ∗
         ((s0.sp - 24#64) ↦₆₄ v19) ∗ ((s0.sp - 16#64) ↦₆₄ v20) ∗ ((s0.sp - 8#64) ↦₆₄ v21)) post oom) :
    SepWP prog target_pc s (R ∗ stackFrame s0 176) post oom := by
  have hst : stackFrame s0 176 =
      stackAt (s0.sp - BitVec.ofNat 64 168) 8 ∗ cells (s0.sp - BitVec.ofNat 64 168) 21 :=
    stackAt_split_cells s0.sp 8 21 (by decide)
  rw [hst, ← sepConj_assoc]
  repeat (apply cells_sub_elim (by decide) (by decide); intro _)
  rename_i v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
  have h0 := h v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
  simpa only [Nat.reduceSub, cells_zero, sepConj_emp, BitVec.ofNat_eq_ofNat, sepConj_assoc] using h0

theorem stackFrame176_entails (s0 : State)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 : BitVec 64) :
    (stackAt (s0.sp - 168#64) 8 ∗
     ((s0.sp - 168#64) ↦₆₄ v1) ∗ ((s0.sp - 160#64) ↦₆₄ v2) ∗ ((s0.sp - 152#64) ↦₆₄ v3) ∗
     ((s0.sp - 144#64) ↦₆₄ v4) ∗ ((s0.sp - 136#64) ↦₆₄ v5) ∗ ((s0.sp - 128#64) ↦₆₄ v6) ∗
     ((s0.sp - 120#64) ↦₆₄ v7) ∗ ((s0.sp - 112#64) ↦₆₄ v8) ∗ ((s0.sp - 104#64) ↦₆₄ v9) ∗
     ((s0.sp - 96#64) ↦₆₄ v10) ∗ ((s0.sp - 88#64) ↦₆₄ v11) ∗ ((s0.sp - 80#64) ↦₆₄ v12) ∗
     ((s0.sp - 72#64) ↦₆₄ v13) ∗ ((s0.sp - 64#64) ↦₆₄ v14) ∗ ((s0.sp - 56#64) ↦₆₄ v15) ∗
     ((s0.sp - 48#64) ↦₆₄ v16) ∗ ((s0.sp - 40#64) ↦₆₄ v17) ∗ ((s0.sp - 32#64) ↦₆₄ v18) ∗
     ((s0.sp - 24#64) ↦₆₄ v19) ∗ ((s0.sp - 16#64) ↦₆₄ v20) ∗ ((s0.sp - 8#64) ↦₆₄ v21))
    ⊢ stackFrame s0 176 := by
  have hst : stackFrame s0 176 =
      stackAt (s0.sp - BitVec.ofNat 64 168) 8 ∗ cells (s0.sp - BitVec.ofNat 64 168) 21 :=
    stackAt_split_cells s0.sp 8 21 (by decide)
  rw [hst]
  refine sepConj_mono_right ?_
  change (((s0.sp - BitVec.ofNat 64 168) ↦₆₄ v1) ∗
    (((s0.sp - BitVec.ofNat 64 160) ↦₆₄ v2) ∗ (((s0.sp - BitVec.ofNat 64 152) ↦₆₄ v3) ∗
    (((s0.sp - BitVec.ofNat 64 144) ↦₆₄ v4) ∗ (((s0.sp - BitVec.ofNat 64 136) ↦₆₄ v5) ∗
    (((s0.sp - BitVec.ofNat 64 128) ↦₆₄ v6) ∗ (((s0.sp - BitVec.ofNat 64 120) ↦₆₄ v7) ∗
    (((s0.sp - BitVec.ofNat 64 112) ↦₆₄ v8) ∗ (((s0.sp - BitVec.ofNat 64 104) ↦₆₄ v9) ∗
    (((s0.sp - BitVec.ofNat 64 96) ↦₆₄ v10) ∗ (((s0.sp - BitVec.ofNat 64 88) ↦₆₄ v11) ∗
    (((s0.sp - BitVec.ofNat 64 80) ↦₆₄ v12) ∗ (((s0.sp - BitVec.ofNat 64 72) ↦₆₄ v13) ∗
    (((s0.sp - BitVec.ofNat 64 64) ↦₆₄ v14) ∗ (((s0.sp - BitVec.ofNat 64 56) ↦₆₄ v15) ∗
    (((s0.sp - BitVec.ofNat 64 48) ↦₆₄ v16) ∗ (((s0.sp - BitVec.ofNat 64 40) ↦₆₄ v17) ∗
    (((s0.sp - BitVec.ofNat 64 32) ↦₆₄ v18) ∗ (((s0.sp - BitVec.ofNat 64 24) ↦₆₄ v19) ∗
    (((s0.sp - BitVec.ofNat 64 16) ↦₆₄ v20) ∗ ((s0.sp - BitVec.ofNat 64 8) ↦₆₄ v21))))))))))))))))))))) ⊢ _
  repeat (refine cells_sub_succ_entails _ _ ?_ (by decide) (by decide))
  dsimp only [Nat.reduceSub]
  rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide)]
  exact Entails.sepExists_right v21 (by
    dsimp only [Nat.reduceSub]
    rw [cells_zero, sepConj_emp]
    exact Entails.refl _)

theorem SepWP.rw_top_reg {prog : Program} {target_pc : BitVec 64}
    {s : State} {r : Reg} {v v' : BitVec 64}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hv : v = v')
    (h : SepWP prog target_pc (s.writeReg64 r v') P post oom) :
    SepWP prog target_pc (s.writeReg64 r v) P post oom := by
  rw [hv]
  exact h

theorem SepWP.rw_top_reg_setMem {prog : Program} {target_pc : BitVec 64}
    {s : State} {m : Memory} {r : Reg} {v v' : BitVec 64}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hv : v = v')
    (h : SepWP prog target_pc ((s.writeReg64 r v').setMem m) P post oom) :
    SepWP prog target_pc ((s.writeReg64 r v).setMem m) P post oom := by
  rw [hv]
  exact h

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells

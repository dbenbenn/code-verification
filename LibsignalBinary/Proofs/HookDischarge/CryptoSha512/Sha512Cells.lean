/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref -- proof-setup: allow-public-import

/-!
# 64-Bit Block Cells, `.rodata` `K64` Cells, and 256-Byte Stack Frame Lemmas

Memory-layout helpers for `sha2::sha512::compress512`:
1. Big-endian byte decoding (`rev64` vs. `beU64OfBytes`) and 128-byte block decomposition into
   16 `↦₆₄` / `↦₆₄ᵣ` cells (`pointsToBytes_128_eq_cells64`, `pointsToBytesRO_128_eq_cells64`).
2. Read-only `.rodata` `K64` decomposition (`sha512KBytes`, `pointsToBytesRO_sha512KBytes_eq_chunks`).
3. $O(1)$ 256-byte (`0x100`) stack-frame elimination and recombination (`stackFrame256_elim`,
   `stackFrame256_entails`) and top-register `SepWP` rewrites.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref (sha512K beU64OfBytes)

/-! ## 1. Big-Endian Byte Decoding (`rev64` vs. `beU64OfBytes`) & 128-Byte Block Cells -/

theorem rev64_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    rev64 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) =
      beU64OfBytes [b0, b1, b2, b3, b4, b5, b6, b7] := by
  unfold rev64 beU64OfBytes
  simp only [List.foldl_cons, List.foldl_nil]
  bv_slice

theorem take8_drop_eq_list {bs : List (BitVec 8)} {off : Nat} (h : off + 8 ≤ bs.length) :
    (bs.drop off).take 8 =
      [bs.getD off 0#8, bs.getD (off + 1) 0#8, bs.getD (off + 2) 0#8, bs.getD (off + 3) 0#8,
       bs.getD (off + 4) 0#8, bs.getD (off + 5) 0#8, bs.getD (off + 6) 0#8, bs.getD (off + 7) 0#8] := by
  have hd0 := List.drop_eq_getD_cons bs off 0#8 (by omega)
  have hd1 := List.drop_eq_getD_cons bs (off + 1) 0#8 (by omega)
  have hd2 := List.drop_eq_getD_cons bs (off + 2) 0#8 (by omega)
  have hd3 := List.drop_eq_getD_cons bs (off + 3) 0#8 (by omega)
  have hd4 := List.drop_eq_getD_cons bs (off + 4) 0#8 (by omega)
  have hd5 := List.drop_eq_getD_cons bs (off + 5) 0#8 (by omega)
  have hd6 := List.drop_eq_getD_cons bs (off + 6) 0#8 (by omega)
  have hd7 := List.drop_eq_getD_cons bs (off + 7) 0#8 (by omega)
  rw [hd0, List.take_succ_cons, hd1, List.take_succ_cons, hd2, List.take_succ_cons,
      hd3, List.take_succ_cons, hd4, List.take_succ_cons, hd5, List.take_succ_cons,
      hd6, List.take_succ_cons, hd7, List.take_succ_cons, List.take_zero]

/-- 64-bit little-endian word at byte offset `off` in `bs`. -/
def readLE64 (bs : List (BitVec 8)) (off : Nat) : BitVec 64 :=
  bs.getD (off + 7) 0#8 ++ bs.getD (off + 6) 0#8 ++ bs.getD (off + 5) 0#8 ++ bs.getD (off + 4) 0#8 ++
  bs.getD (off + 3) 0#8 ++ bs.getD (off + 2) 0#8 ++ bs.getD (off + 1) 0#8 ++ bs.getD off 0#8

theorem rev64_readLE64_eq_beU64OfBytes (bs : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    rev64 (readLE64 bs off) = beU64OfBytes ((bs.drop off).take 8) := by
  unfold readLE64
  rw [take8_drop_eq_list h, rev64_pack64]

theorem pointsToBytes_take8_eq_pointsTo64_readLE64 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    (a ↦ₛ (bs.drop off).take 8) = (a ↦₆₄ readLE64 bs off) := by
  rw [take8_drop_eq_list h, pointsToBytes8_eq_pointsTo64]
  rfl

theorem pointsToBytes_drop_step8 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    ((a + BitVec.ofNat 64 off) ↦ₛ bs.drop off) =
      ((a + BitVec.ofNat 64 off) ↦₆₄ readLE64 bs off) ∗
      ((a + BitVec.ofNat 64 (off + 8)) ↦ₛ bs.drop (off + 8)) := by
  have htd := pointsToBytes_take_drop (a + BitVec.ofNat 64 off) 8 (bs.drop off) (by simp; omega)
  rw [htd, pointsToBytes_take8_eq_pointsTo64_readLE64 _ bs off h, List.drop_drop,
      BitVec.add_assoc, ← BitVec.ofNat_add]

theorem pointsToBytes_128_eq_cells64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 128) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ readLE64 bs 0) ∗
       ((a + 8#64) ↦₆₄ readLE64 bs 8) ∗
       ((a + 16#64) ↦₆₄ readLE64 bs 16) ∗
       ((a + 24#64) ↦₆₄ readLE64 bs 24) ∗
       ((a + 32#64) ↦₆₄ readLE64 bs 32) ∗
       ((a + 40#64) ↦₆₄ readLE64 bs 40) ∗
       ((a + 48#64) ↦₆₄ readLE64 bs 48) ∗
       ((a + 56#64) ↦₆₄ readLE64 bs 56) ∗
       ((a + 64#64) ↦₆₄ readLE64 bs 64) ∗
       ((a + 72#64) ↦₆₄ readLE64 bs 72) ∗
       ((a + 80#64) ↦₆₄ readLE64 bs 80) ∗
       ((a + 88#64) ↦₆₄ readLE64 bs 88) ∗
       ((a + 96#64) ↦₆₄ readLE64 bs 96) ∗
       ((a + 104#64) ↦₆₄ readLE64 bs 104) ∗
       ((a + 112#64) ↦₆₄ readLE64 bs 112) ∗
       ((a + 120#64) ↦₆₄ readLE64 bs 120)) := by
  have h0 : (a ↦ₛ bs) = ((a + BitVec.ofNat 64 0) ↦ₛ bs.drop 0) := by
    rw [BitVec.add_zero, List.drop_zero]
  rw [h0]
  repeat (rw [pointsToBytes_drop_step8 a bs _ (by omega)])
  have hdrop : bs.drop 128 = [] := List.drop_of_length_le (by omega)
  rw [hdrop, pointsToBytes_nil, sepConj_emp]
  simp only [BitVec.add_zero]

theorem pointsToBytesRO_take_drop (ptr : BitVec 64) (n : Nat) (bs : List (BitVec 8))
    (hn : n ≤ bs.length) :
    (ptr ↦ᵣ bs) = (ptr ↦ᵣ bs.take n) ∗ ((ptr + BitVec.ofNat 64 n) ↦ᵣ bs.drop n) := by
  have h := pointsToBytesRO_append ptr (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take_of_le hn] at h
  exact h

theorem pointsToBytesRO_take8_eq_pointsTo64RO_readLE64 (a : BitVec 64) (bs : List (BitVec 8))
    (off : Nat) (h : off + 8 ≤ bs.length) :
    (a ↦ᵣ (bs.drop off).take 8) = (a ↦₆₄ᵣ readLE64 bs off) := by
  rw [take8_drop_eq_list h, pointsToBytesRO8_eq_pointsTo64RO]
  rfl

theorem pointsToBytesRO_drop_step8 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    ((a + BitVec.ofNat 64 off) ↦ᵣ bs.drop off) =
      ((a + BitVec.ofNat 64 off) ↦₆₄ᵣ readLE64 bs off) ∗
      ((a + BitVec.ofNat 64 (off + 8)) ↦ᵣ bs.drop (off + 8)) := by
  have htd := pointsToBytesRO_take_drop (a + BitVec.ofNat 64 off) 8 (bs.drop off) (by simp; omega)
  rw [htd, pointsToBytesRO_take8_eq_pointsTo64RO_readLE64 _ bs off h, List.drop_drop,
      BitVec.add_assoc, ← BitVec.ofNat_add]

theorem pointsToBytesRO_128_eq_cells64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 128) :
    (a ↦ᵣ bs) =
      ((a ↦₆₄ᵣ readLE64 bs 0) ∗
       ((a + 8#64) ↦₆₄ᵣ readLE64 bs 8) ∗
       ((a + 16#64) ↦₆₄ᵣ readLE64 bs 16) ∗
       ((a + 24#64) ↦₆₄ᵣ readLE64 bs 24) ∗
       ((a + 32#64) ↦₆₄ᵣ readLE64 bs 32) ∗
       ((a + 40#64) ↦₆₄ᵣ readLE64 bs 40) ∗
       ((a + 48#64) ↦₆₄ᵣ readLE64 bs 48) ∗
       ((a + 56#64) ↦₆₄ᵣ readLE64 bs 56) ∗
       ((a + 64#64) ↦₆₄ᵣ readLE64 bs 64) ∗
       ((a + 72#64) ↦₆₄ᵣ readLE64 bs 72) ∗
       ((a + 80#64) ↦₆₄ᵣ readLE64 bs 80) ∗
       ((a + 88#64) ↦₆₄ᵣ readLE64 bs 88) ∗
       ((a + 96#64) ↦₆₄ᵣ readLE64 bs 96) ∗
       ((a + 104#64) ↦₆₄ᵣ readLE64 bs 104) ∗
       ((a + 112#64) ↦₆₄ᵣ readLE64 bs 112) ∗
       ((a + 120#64) ↦₆₄ᵣ readLE64 bs 120)) := by
  have h0 : (a ↦ᵣ bs) = ((a + BitVec.ofNat 64 0) ↦ᵣ bs.drop 0) := by
    rw [BitVec.add_zero, List.drop_zero]
  rw [h0]
  repeat (rw [pointsToBytesRO_drop_step8 a bs _ (by omega)])
  have hdrop : bs.drop 128 = [] := List.drop_of_length_le (by omega)
  rw [hdrop, pointsToBytesRO_nil, sepConj_emp]
  simp only [BitVec.add_zero]

/-! ## 2. `.rodata` `K64` 80-Word Read-Only Cell Decomposition -/

/-- The 640 little-endian bytes of `sha2::consts::K64`. -/
@[expose] def sha512KBytes : List (BitVec 8) :=
  sha512K.flatMap unpack64

theorem sha512K_length : sha512K.length = 80 := rfl

private theorem flatMap_unpack64_4_length (w0 w1 w2 w3 : BitVec 64) :
    ([w0, w1, w2, w3].flatMap unpack64).length = 32 := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, unpack64_length]

private theorem pointsToBytesRO_4words64 (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    (a ↦ᵣ [w0, w1, w2, w3].flatMap unpack64) =
      ((a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 16#64) ↦₆₄ᵣ w2) ∗ ((a + 24#64) ↦₆₄ᵣ w3)) := by
  change (a ↦ᵣ (unpack64 w0 ++ (unpack64 w1 ++ (unpack64 w2 ++ (unpack64 w3 ++ []))))) = _
  rw [List.append_nil,
      pointsToBytesRO_append, unpack64_length, ← pointsTo64RO_eq_pointsToBytesRO,
      pointsToBytesRO_append, unpack64_length, ← pointsTo64RO_eq_pointsToBytesRO,
      pointsToBytesRO_append, unpack64_length, ← pointsTo64RO_eq_pointsToBytesRO,
      ← pointsTo64RO_eq_pointsToBytesRO]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem flatMap_unpack64_16_length
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15].flatMap unpack64).length = 128 := by
  change (([w0, w1, w2, w3] ++ ([w4, w5, w6, w7] ++ ([w8, w9, w10, w11] ++ [w12, w13, w14, w15]))).flatMap unpack64).length = 128
  simp only [List.flatMap_append, List.length_append, flatMap_unpack64_4_length]

private theorem pointsToBytesRO_16words64 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    (a ↦ᵣ [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15].flatMap unpack64) =
      ((a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 16#64) ↦₆₄ᵣ w2) ∗ ((a + 24#64) ↦₆₄ᵣ w3) ∗
       ((a + 32#64) ↦₆₄ᵣ w4) ∗ ((a + 40#64) ↦₆₄ᵣ w5) ∗ ((a + 48#64) ↦₆₄ᵣ w6) ∗ ((a + 56#64) ↦₆₄ᵣ w7) ∗
       ((a + 64#64) ↦₆₄ᵣ w8) ∗ ((a + 72#64) ↦₆₄ᵣ w9) ∗ ((a + 80#64) ↦₆₄ᵣ w10) ∗ ((a + 88#64) ↦₆₄ᵣ w11) ∗
       ((a + 96#64) ↦₆₄ᵣ w12) ∗ ((a + 104#64) ↦₆₄ᵣ w13) ∗ ((a + 112#64) ↦₆₄ᵣ w14) ∗ ((a + 120#64) ↦₆₄ᵣ w15)) := by
  change (a ↦ᵣ (([w0, w1, w2, w3] ++ ([w4, w5, w6, w7] ++ ([w8, w9, w10, w11] ++ [w12, w13, w14, w15]))).flatMap unpack64)) = _
  rw [List.flatMap_append, pointsToBytesRO_append, flatMap_unpack64_4_length, pointsToBytesRO_4words64,
      List.flatMap_append, pointsToBytesRO_append, flatMap_unpack64_4_length, pointsToBytesRO_4words64,
      List.flatMap_append, pointsToBytesRO_append, flatMap_unpack64_4_length, pointsToBytesRO_4words64,
      pointsToBytesRO_4words64]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

@[expose] def sha2K64Cells0 (a : BitVec 64) : SepProp :=
  (a ↦₆₄ᵣ sha512K.getD 0 0#64) ∗ ((a + 8#64) ↦₆₄ᵣ sha512K.getD 1 0#64) ∗
  ((a + 16#64) ↦₆₄ᵣ sha512K.getD 2 0#64) ∗ ((a + 24#64) ↦₆₄ᵣ sha512K.getD 3 0#64) ∗
  ((a + 32#64) ↦₆₄ᵣ sha512K.getD 4 0#64) ∗ ((a + 40#64) ↦₆₄ᵣ sha512K.getD 5 0#64) ∗
  ((a + 48#64) ↦₆₄ᵣ sha512K.getD 6 0#64) ∗ ((a + 56#64) ↦₆₄ᵣ sha512K.getD 7 0#64) ∗
  ((a + 64#64) ↦₆₄ᵣ sha512K.getD 8 0#64) ∗ ((a + 72#64) ↦₆₄ᵣ sha512K.getD 9 0#64) ∗
  ((a + 80#64) ↦₆₄ᵣ sha512K.getD 10 0#64) ∗ ((a + 88#64) ↦₆₄ᵣ sha512K.getD 11 0#64) ∗
  ((a + 96#64) ↦₆₄ᵣ sha512K.getD 12 0#64) ∗ ((a + 104#64) ↦₆₄ᵣ sha512K.getD 13 0#64) ∗
  ((a + 112#64) ↦₆₄ᵣ sha512K.getD 14 0#64) ∗ ((a + 120#64) ↦₆₄ᵣ sha512K.getD 15 0#64)

@[expose] def sha2K64Cells1 (a : BitVec 64) : SepProp :=
  ((a + 128#64) ↦₆₄ᵣ sha512K.getD 16 0#64) ∗ ((a + 136#64) ↦₆₄ᵣ sha512K.getD 17 0#64) ∗
  ((a + 144#64) ↦₆₄ᵣ sha512K.getD 18 0#64) ∗ ((a + 152#64) ↦₆₄ᵣ sha512K.getD 19 0#64) ∗
  ((a + 160#64) ↦₆₄ᵣ sha512K.getD 20 0#64) ∗ ((a + 168#64) ↦₆₄ᵣ sha512K.getD 21 0#64) ∗
  ((a + 176#64) ↦₆₄ᵣ sha512K.getD 22 0#64) ∗ ((a + 184#64) ↦₆₄ᵣ sha512K.getD 23 0#64) ∗
  ((a + 192#64) ↦₆₄ᵣ sha512K.getD 24 0#64) ∗ ((a + 200#64) ↦₆₄ᵣ sha512K.getD 25 0#64) ∗
  ((a + 208#64) ↦₆₄ᵣ sha512K.getD 26 0#64) ∗ ((a + 216#64) ↦₆₄ᵣ sha512K.getD 27 0#64) ∗
  ((a + 224#64) ↦₆₄ᵣ sha512K.getD 28 0#64) ∗ ((a + 232#64) ↦₆₄ᵣ sha512K.getD 29 0#64) ∗
  ((a + 240#64) ↦₆₄ᵣ sha512K.getD 30 0#64) ∗ ((a + 248#64) ↦₆₄ᵣ sha512K.getD 31 0#64)

@[expose] def sha2K64Cells2 (a : BitVec 64) : SepProp :=
  ((a + 256#64) ↦₆₄ᵣ sha512K.getD 32 0#64) ∗ ((a + 264#64) ↦₆₄ᵣ sha512K.getD 33 0#64) ∗
  ((a + 272#64) ↦₆₄ᵣ sha512K.getD 34 0#64) ∗ ((a + 280#64) ↦₆₄ᵣ sha512K.getD 35 0#64) ∗
  ((a + 288#64) ↦₆₄ᵣ sha512K.getD 36 0#64) ∗ ((a + 296#64) ↦₆₄ᵣ sha512K.getD 37 0#64) ∗
  ((a + 304#64) ↦₆₄ᵣ sha512K.getD 38 0#64) ∗ ((a + 312#64) ↦₆₄ᵣ sha512K.getD 39 0#64) ∗
  ((a + 320#64) ↦₆₄ᵣ sha512K.getD 40 0#64) ∗ ((a + 328#64) ↦₆₄ᵣ sha512K.getD 41 0#64) ∗
  ((a + 336#64) ↦₆₄ᵣ sha512K.getD 42 0#64) ∗ ((a + 344#64) ↦₆₄ᵣ sha512K.getD 43 0#64) ∗
  ((a + 352#64) ↦₆₄ᵣ sha512K.getD 44 0#64) ∗ ((a + 360#64) ↦₆₄ᵣ sha512K.getD 45 0#64) ∗
  ((a + 368#64) ↦₆₄ᵣ sha512K.getD 46 0#64) ∗ ((a + 376#64) ↦₆₄ᵣ sha512K.getD 47 0#64)

@[expose] def sha2K64Cells3 (a : BitVec 64) : SepProp :=
  ((a + 384#64) ↦₆₄ᵣ sha512K.getD 48 0#64) ∗ ((a + 392#64) ↦₆₄ᵣ sha512K.getD 49 0#64) ∗
  ((a + 400#64) ↦₆₄ᵣ sha512K.getD 50 0#64) ∗ ((a + 408#64) ↦₆₄ᵣ sha512K.getD 51 0#64) ∗
  ((a + 416#64) ↦₆₄ᵣ sha512K.getD 52 0#64) ∗ ((a + 424#64) ↦₆₄ᵣ sha512K.getD 53 0#64) ∗
  ((a + 432#64) ↦₆₄ᵣ sha512K.getD 54 0#64) ∗ ((a + 440#64) ↦₆₄ᵣ sha512K.getD 55 0#64) ∗
  ((a + 448#64) ↦₆₄ᵣ sha512K.getD 56 0#64) ∗ ((a + 456#64) ↦₆₄ᵣ sha512K.getD 57 0#64) ∗
  ((a + 464#64) ↦₆₄ᵣ sha512K.getD 58 0#64) ∗ ((a + 472#64) ↦₆₄ᵣ sha512K.getD 59 0#64) ∗
  ((a + 480#64) ↦₆₄ᵣ sha512K.getD 60 0#64) ∗ ((a + 488#64) ↦₆₄ᵣ sha512K.getD 61 0#64) ∗
  ((a + 496#64) ↦₆₄ᵣ sha512K.getD 62 0#64) ∗ ((a + 504#64) ↦₆₄ᵣ sha512K.getD 63 0#64)

@[expose] def sha2K64Cells4 (a : BitVec 64) : SepProp :=
  ((a + 512#64) ↦₆₄ᵣ sha512K.getD 64 0#64) ∗ ((a + 520#64) ↦₆₄ᵣ sha512K.getD 65 0#64) ∗
  ((a + 528#64) ↦₆₄ᵣ sha512K.getD 66 0#64) ∗ ((a + 536#64) ↦₆₄ᵣ sha512K.getD 67 0#64) ∗
  ((a + 544#64) ↦₆₄ᵣ sha512K.getD 68 0#64) ∗ ((a + 552#64) ↦₆₄ᵣ sha512K.getD 69 0#64) ∗
  ((a + 560#64) ↦₆₄ᵣ sha512K.getD 70 0#64) ∗ ((a + 568#64) ↦₆₄ᵣ sha512K.getD 71 0#64) ∗
  ((a + 576#64) ↦₆₄ᵣ sha512K.getD 72 0#64) ∗ ((a + 584#64) ↦₆₄ᵣ sha512K.getD 73 0#64) ∗
  ((a + 592#64) ↦₆₄ᵣ sha512K.getD 74 0#64) ∗ ((a + 600#64) ↦₆₄ᵣ sha512K.getD 75 0#64) ∗
  ((a + 608#64) ↦₆₄ᵣ sha512K.getD 76 0#64) ∗ ((a + 616#64) ↦₆₄ᵣ sha512K.getD 77 0#64) ∗
  ((a + 624#64) ↦₆₄ᵣ sha512K.getD 78 0#64) ∗ ((a + 632#64) ↦₆₄ᵣ sha512K.getD 79 0#64)

private theorem sha512K_eq_chunks :
    sha512K =
      [sha512K.getD 0 0#64, sha512K.getD 1 0#64, sha512K.getD 2 0#64, sha512K.getD 3 0#64,
       sha512K.getD 4 0#64, sha512K.getD 5 0#64, sha512K.getD 6 0#64, sha512K.getD 7 0#64,
       sha512K.getD 8 0#64, sha512K.getD 9 0#64, sha512K.getD 10 0#64, sha512K.getD 11 0#64,
       sha512K.getD 12 0#64, sha512K.getD 13 0#64, sha512K.getD 14 0#64, sha512K.getD 15 0#64] ++
      ([sha512K.getD 16 0#64, sha512K.getD 17 0#64, sha512K.getD 18 0#64, sha512K.getD 19 0#64,
        sha512K.getD 20 0#64, sha512K.getD 21 0#64, sha512K.getD 22 0#64, sha512K.getD 23 0#64,
        sha512K.getD 24 0#64, sha512K.getD 25 0#64, sha512K.getD 26 0#64, sha512K.getD 27 0#64,
        sha512K.getD 28 0#64, sha512K.getD 29 0#64, sha512K.getD 30 0#64, sha512K.getD 31 0#64] ++
       ([sha512K.getD 32 0#64, sha512K.getD 33 0#64, sha512K.getD 34 0#64, sha512K.getD 35 0#64,
         sha512K.getD 36 0#64, sha512K.getD 37 0#64, sha512K.getD 38 0#64, sha512K.getD 39 0#64,
         sha512K.getD 40 0#64, sha512K.getD 41 0#64, sha512K.getD 42 0#64, sha512K.getD 43 0#64,
         sha512K.getD 44 0#64, sha512K.getD 45 0#64, sha512K.getD 46 0#64, sha512K.getD 47 0#64] ++
        ([sha512K.getD 48 0#64, sha512K.getD 49 0#64, sha512K.getD 50 0#64, sha512K.getD 51 0#64,
          sha512K.getD 52 0#64, sha512K.getD 53 0#64, sha512K.getD 54 0#64, sha512K.getD 55 0#64,
          sha512K.getD 56 0#64, sha512K.getD 57 0#64, sha512K.getD 58 0#64, sha512K.getD 59 0#64,
          sha512K.getD 60 0#64, sha512K.getD 61 0#64, sha512K.getD 62 0#64, sha512K.getD 63 0#64] ++
         [sha512K.getD 64 0#64, sha512K.getD 65 0#64, sha512K.getD 66 0#64, sha512K.getD 67 0#64,
          sha512K.getD 68 0#64, sha512K.getD 69 0#64, sha512K.getD 70 0#64, sha512K.getD 71 0#64,
          sha512K.getD 72 0#64, sha512K.getD 73 0#64, sha512K.getD 74 0#64, sha512K.getD 75 0#64,
          sha512K.getD 76 0#64, sha512K.getD 77 0#64, sha512K.getD 78 0#64, sha512K.getD 79 0#64]))) := by
  decide

theorem pointsToBytesRO_sha512KBytes_eq_chunks (a : BitVec 64) :
    (a ↦ᵣ sha512KBytes) =
      sha2K64Cells0 a ∗ sha2K64Cells1 a ∗ sha2K64Cells2 a ∗ sha2K64Cells3 a ∗ sha2K64Cells4 a := by
  unfold sha512KBytes
  rw [sha512K_eq_chunks,
      List.flatMap_append, pointsToBytesRO_append, flatMap_unpack64_16_length, pointsToBytesRO_16words64,
      List.flatMap_append, pointsToBytesRO_append, flatMap_unpack64_16_length, pointsToBytesRO_16words64,
      List.flatMap_append, pointsToBytesRO_append, flatMap_unpack64_16_length, pointsToBytesRO_16words64,
      List.flatMap_append, pointsToBytesRO_append, flatMap_unpack64_16_length, pointsToBytesRO_16words64,
      pointsToBytesRO_16words64]
  unfold sha2K64Cells0 sha2K64Cells1 sha2K64Cells2 sha2K64Cells3 sha2K64Cells4
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## 3. $O(1)$ Stack Cell Elimination & Recombination for 256-Byte (`0x100`) Stack Frame -/

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

theorem stackFrame256_elim {prog : Program} {target_pc : BitVec 64}
    {s : State} {s0 : State} {R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
            v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : BitVec 64),
      SepWP prog target_pc s
        (R ∗ stackAt (s0.sp - 248#64) 8 ∗
         ((s0.sp - 248#64) ↦₆₄ v1) ∗ ((s0.sp - 240#64) ↦₆₄ v2) ∗ ((s0.sp - 232#64) ↦₆₄ v3) ∗
         ((s0.sp - 224#64) ↦₆₄ v4) ∗ ((s0.sp - 216#64) ↦₆₄ v5) ∗ ((s0.sp - 208#64) ↦₆₄ v6) ∗
         ((s0.sp - 200#64) ↦₆₄ v7) ∗ ((s0.sp - 192#64) ↦₆₄ v8) ∗ ((s0.sp - 184#64) ↦₆₄ v9) ∗
         ((s0.sp - 176#64) ↦₆₄ v10) ∗ ((s0.sp - 168#64) ↦₆₄ v11) ∗ ((s0.sp - 160#64) ↦₆₄ v12) ∗
         ((s0.sp - 152#64) ↦₆₄ v13) ∗ ((s0.sp - 144#64) ↦₆₄ v14) ∗ ((s0.sp - 136#64) ↦₆₄ v15) ∗
         ((s0.sp - 128#64) ↦₆₄ v16) ∗ ((s0.sp - 120#64) ↦₆₄ v17) ∗ ((s0.sp - 112#64) ↦₆₄ v18) ∗
         ((s0.sp - 104#64) ↦₆₄ v19) ∗ ((s0.sp - 96#64) ↦₆₄ v20) ∗ ((s0.sp - 88#64) ↦₆₄ v21) ∗
         ((s0.sp - 80#64) ↦₆₄ v22) ∗ ((s0.sp - 72#64) ↦₆₄ v23) ∗ ((s0.sp - 64#64) ↦₆₄ v24) ∗
         ((s0.sp - 56#64) ↦₆₄ v25) ∗ ((s0.sp - 48#64) ↦₆₄ v26) ∗ ((s0.sp - 40#64) ↦₆₄ v27) ∗
         ((s0.sp - 32#64) ↦₆₄ v28) ∗ ((s0.sp - 24#64) ↦₆₄ v29) ∗ ((s0.sp - 16#64) ↦₆₄ v30) ∗
         ((s0.sp - 8#64) ↦₆₄ v31)) post oom) :
    SepWP prog target_pc s (R ∗ stackFrame s0 256) post oom := by
  have hst : stackFrame s0 256 =
      stackAt (s0.sp - BitVec.ofNat 64 248) 8 ∗ cells (s0.sp - BitVec.ofNat 64 248) 31 :=
    stackAt_split_cells s0.sp 8 31 (by decide)
  rw [hst, ← sepConj_assoc]
  repeat (apply cells_sub_elim (by decide) (by decide); intro _)
  rename_i v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
           v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31
  have h0 := h v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
               v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31
  simpa only [Nat.reduceSub, cells_zero, sepConj_emp, BitVec.ofNat_eq_ofNat, sepConj_assoc] using h0

theorem stackFrame256_entails (s0 : State)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
     v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : BitVec 64) :
    (stackAt (s0.sp - 248#64) 8 ∗
     ((s0.sp - 248#64) ↦₆₄ v1) ∗ ((s0.sp - 240#64) ↦₆₄ v2) ∗ ((s0.sp - 232#64) ↦₆₄ v3) ∗
     ((s0.sp - 224#64) ↦₆₄ v4) ∗ ((s0.sp - 216#64) ↦₆₄ v5) ∗ ((s0.sp - 208#64) ↦₆₄ v6) ∗
     ((s0.sp - 200#64) ↦₆₄ v7) ∗ ((s0.sp - 192#64) ↦₆₄ v8) ∗ ((s0.sp - 184#64) ↦₆₄ v9) ∗
     ((s0.sp - 176#64) ↦₆₄ v10) ∗ ((s0.sp - 168#64) ↦₆₄ v11) ∗ ((s0.sp - 160#64) ↦₆₄ v12) ∗
     ((s0.sp - 152#64) ↦₆₄ v13) ∗ ((s0.sp - 144#64) ↦₆₄ v14) ∗ ((s0.sp - 136#64) ↦₆₄ v15) ∗
     ((s0.sp - 128#64) ↦₆₄ v16) ∗ ((s0.sp - 120#64) ↦₆₄ v17) ∗ ((s0.sp - 112#64) ↦₆₄ v18) ∗
     ((s0.sp - 104#64) ↦₆₄ v19) ∗ ((s0.sp - 96#64) ↦₆₄ v20) ∗ ((s0.sp - 88#64) ↦₆₄ v21) ∗
     ((s0.sp - 80#64) ↦₆₄ v22) ∗ ((s0.sp - 72#64) ↦₆₄ v23) ∗ ((s0.sp - 64#64) ↦₆₄ v24) ∗
     ((s0.sp - 56#64) ↦₆₄ v25) ∗ ((s0.sp - 48#64) ↦₆₄ v26) ∗ ((s0.sp - 40#64) ↦₆₄ v27) ∗
     ((s0.sp - 32#64) ↦₆₄ v28) ∗ ((s0.sp - 24#64) ↦₆₄ v29) ∗ ((s0.sp - 16#64) ↦₆₄ v30) ∗
     ((s0.sp - 8#64) ↦₆₄ v31))
    ⊢ stackFrame s0 256 := by
  have hst : stackFrame s0 256 =
      stackAt (s0.sp - BitVec.ofNat 64 248) 8 ∗ cells (s0.sp - BitVec.ofNat 64 248) 31 :=
    stackAt_split_cells s0.sp 8 31 (by decide)
  rw [hst]
  refine sepConj_mono_right ?_
  change (((s0.sp - BitVec.ofNat 64 248) ↦₆₄ v1) ∗
    (((s0.sp - BitVec.ofNat 64 240) ↦₆₄ v2) ∗ (((s0.sp - BitVec.ofNat 64 232) ↦₆₄ v3) ∗
    (((s0.sp - BitVec.ofNat 64 224) ↦₆₄ v4) ∗ (((s0.sp - BitVec.ofNat 64 216) ↦₆₄ v5) ∗
    (((s0.sp - BitVec.ofNat 64 208) ↦₆₄ v6) ∗ (((s0.sp - BitVec.ofNat 64 200) ↦₆₄ v7) ∗
    (((s0.sp - BitVec.ofNat 64 192) ↦₆₄ v8) ∗ (((s0.sp - BitVec.ofNat 64 184) ↦₆₄ v9) ∗
    (((s0.sp - BitVec.ofNat 64 176) ↦₆₄ v10) ∗ (((s0.sp - BitVec.ofNat 64 168) ↦₆₄ v11) ∗
    (((s0.sp - BitVec.ofNat 64 160) ↦₆₄ v12) ∗ (((s0.sp - BitVec.ofNat 64 152) ↦₆₄ v13) ∗
    (((s0.sp - BitVec.ofNat 64 144) ↦₆₄ v14) ∗ (((s0.sp - BitVec.ofNat 64 136) ↦₆₄ v15) ∗
    (((s0.sp - BitVec.ofNat 64 128) ↦₆₄ v16) ∗ (((s0.sp - BitVec.ofNat 64 120) ↦₆₄ v17) ∗
    (((s0.sp - BitVec.ofNat 64 112) ↦₆₄ v18) ∗ (((s0.sp - BitVec.ofNat 64 104) ↦₆₄ v19) ∗
    (((s0.sp - BitVec.ofNat 64 96) ↦₆₄ v20) ∗ (((s0.sp - BitVec.ofNat 64 88) ↦₆₄ v21) ∗
    (((s0.sp - BitVec.ofNat 64 80) ↦₆₄ v22) ∗ (((s0.sp - BitVec.ofNat 64 72) ↦₆₄ v23) ∗
    (((s0.sp - BitVec.ofNat 64 64) ↦₆₄ v24) ∗ (((s0.sp - BitVec.ofNat 64 56) ↦₆₄ v25) ∗
    (((s0.sp - BitVec.ofNat 64 48) ↦₆₄ v26) ∗ (((s0.sp - BitVec.ofNat 64 40) ↦₆₄ v27) ∗
    (((s0.sp - BitVec.ofNat 64 32) ↦₆₄ v28) ∗ (((s0.sp - BitVec.ofNat 64 24) ↦₆₄ v29) ∗
    (((s0.sp - BitVec.ofNat 64 16) ↦₆₄ v30) ∗ ((s0.sp - BitVec.ofNat 64 8) ↦₆₄ v31))))))))))))))))))))))))))))))) ⊢ _
  repeat (refine cells_sub_succ_entails _ _ ?_ (by decide) (by decide))
  dsimp only [Nat.reduceSub]
  rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide)]
  exact Entails.sepExists_right v31 (by
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

end LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells

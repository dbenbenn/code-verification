/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import

/-!
# Portable Deserialization Specifications and `Spec.MlKem` Bridges (`B25`–`B27`)

Defines `packPoly16ChunkBytes`, `deserializeChunkCoeff`, and `deserializeChunkBytes` for the
32-byte little-endian 16-lane `u16` output of `PortableVector::deserialize_{4,5,11}`, bridges to
`Spec.MlKem` (`bytesToPoly16`, `ByteSlice.readLE` 128-bit NEON loads `q0`/`q1`, `byteDecodeRaw`,
and `decodeAndDecompress`), and placement-independent RO and RW `Spec` contracts for `B25`
(`deserialize_4`), `B26` (`deserialize_5`), and `B27` (`deserialize_11`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  bytesToBits
  byteDecodeRaw
  bytesToPoly16
  decompressCoeff
  decodeAndDecompress
)

/-! ### 16-Lane `u16` Chunk Byte Packing -/

/-- Pack 16 `BitVec 16` lanes into 32 little-endian bytes (`[lo₀, hi₀, ..., lo₁₅, hi₁₅]`). -/
@[expose] def packPoly16ChunkBytes (coeffs : Nat → BitVec 16) : List (BitVec 8) :=
  ((List.range 16).map fun j =>
    let w := coeffs j
    [w.truncate 8, (w >>> 8).truncate 8]).flatten

private theorem packPoly16ChunkBytes_expand (coeffs : Nat → BitVec 16) :
    packPoly16ChunkBytes coeffs =
      [(coeffs 0).truncate 8, (coeffs 0 >>> 8).truncate 8,
       (coeffs 1).truncate 8, (coeffs 1 >>> 8).truncate 8,
       (coeffs 2).truncate 8, (coeffs 2 >>> 8).truncate 8,
       (coeffs 3).truncate 8, (coeffs 3 >>> 8).truncate 8,
       (coeffs 4).truncate 8, (coeffs 4 >>> 8).truncate 8,
       (coeffs 5).truncate 8, (coeffs 5 >>> 8).truncate 8,
       (coeffs 6).truncate 8, (coeffs 6 >>> 8).truncate 8,
       (coeffs 7).truncate 8, (coeffs 7 >>> 8).truncate 8,
       (coeffs 8).truncate 8, (coeffs 8 >>> 8).truncate 8,
       (coeffs 9).truncate 8, (coeffs 9 >>> 8).truncate 8,
       (coeffs 10).truncate 8, (coeffs 10 >>> 8).truncate 8,
       (coeffs 11).truncate 8, (coeffs 11 >>> 8).truncate 8,
       (coeffs 12).truncate 8, (coeffs 12 >>> 8).truncate 8,
       (coeffs 13).truncate 8, (coeffs 13 >>> 8).truncate 8,
       (coeffs 14).truncate 8, (coeffs 14 >>> 8).truncate 8,
       (coeffs 15).truncate 8, (coeffs 15 >>> 8).truncate 8] := by
  rfl

@[simp] theorem packPoly16ChunkBytes_length (coeffs : Nat → BitVec 16) :
    (packPoly16ChunkBytes coeffs).length = 32 := by
  rw [packPoly16ChunkBytes_expand]
  rfl

theorem getD_packPoly16ChunkBytes_even (coeffs : Nat → BitVec 16) (j : Nat) (hj : j < 16) :
    (packPoly16ChunkBytes coeffs).getD (2 * j) 0#8 = (coeffs j).truncate 8 := by
  rw [packPoly16ChunkBytes_expand]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals try rfl
  omega

theorem getD_packPoly16ChunkBytes_odd (coeffs : Nat → BitVec 16) (j : Nat) (hj : j < 16) :
    (packPoly16ChunkBytes coeffs).getD (2 * j + 1) 0#8 = (coeffs j >>> 8).truncate 8 := by
  rw [packPoly16ChunkBytes_expand]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals try rfl
  omega

/-- Extensionality helper: any 32-byte list whose even/odd byte pairs match `coeffs j` is
`packPoly16ChunkBytes coeffs`. -/
theorem eq_packPoly16ChunkBytes_of_getD {bs : List (BitVec 8)} {coeffs : Nat → BitVec 16}
    (hlen : bs.length = 32)
    (hlo : ∀ j, j < 16 → bs.getD (2 * j) 0#8 = (coeffs j).truncate 8)
    (hhi : ∀ j, j < 16 → bs.getD (2 * j + 1) 0#8 = (coeffs j >>> 8).truncate 8) :
    bs = packPoly16ChunkBytes coeffs := by
  apply ByteSlice.ext_getD
  · simp [hlen]
  · intro i hi
    rw [hlen] at hi
    have hdiv : i / 2 < 16 := by omega
    by_cases hpar : i % 2 = 0
    · have hi_eq : i = 2 * (i / 2) := by omega
      rw [hi_eq, hlo (i / 2) hdiv, getD_packPoly16ChunkBytes_even coeffs (i / 2) hdiv]
    · have hi_eq : i = 2 * (i / 2) + 1 := by omega
      rw [hi_eq, hhi (i / 2) hdiv, getD_packPoly16ChunkBytes_odd coeffs (i / 2) hdiv]

/-! ### `deserializeChunkCoeff` & `deserializeChunkBytes` -/

/-- The `j`-th 16-bit coefficient decoded from a `2 * d`-byte slice `bs` (`j < 16`). -/
@[expose] def deserializeChunkCoeff (d : Nat) (bs : List (BitVec 8)) (j : Nat) : BitVec 16 :=
  BitVec.ofNat 16 ((byteDecodeRaw d bs).getD j 0)

/-- The 32-byte stack buffer written by `PortableVector::deserialize_d` (`d ∈ {4, 5, 11}`). -/
@[expose] def deserializeChunkBytes (d : Nat) (bs : List (BitVec 8)) : List (BitVec 8) :=
  packPoly16ChunkBytes (deserializeChunkCoeff d bs)

@[simp] theorem deserializeChunkBytes_length (d : Nat) (bs : List (BitVec 8)) :
    (deserializeChunkBytes d bs).length = 32 := by
  simp [deserializeChunkBytes]

/-! ### Bridges to `Spec.MlKem` (`bytesToPoly16`, NEON `ldr q0/q1`, `byteDecodeRaw`) -/

private theorem array_getD_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Nat) (d : α)
    (hi : i < n) : (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  unfold Array.getD
  split
  · rename_i h
    change (Array.ofFn f)[i]'h = f ⟨i, hi⟩
    exact Array.getElem_ofFn h
  · rename_i h
    exact False.elim (h (by simp [hi]))

private theorem toArray_getD_eq {α : Type _} (xs : List α) (i : Nat) (d : α) :
    xs.toArray.getD i d = xs.getD i d := by
  unfold Array.getD
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    have hi : i < xs.length := by simpa using h
    change xs.toArray[i]'h = xs[i]?.getD d
    rw [List.getElem_toArray, List.getElem?_eq_getElem hi]
    rfl
  · rename_i h
    have hi : xs.length ≤ i := by simpa using h
    rw [List.getElem?_eq_none hi]
    rfl

private theorem list_getD_append_left {α : Type _} (xs ys : List α) (i : Nat) (d : α)
    (hi : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem zeroExtend_lo_or_hi_eq (w : BitVec 16) :
    (w.truncate 8).zeroExtend 16 ||| ((w >>> 8).truncate 8).zeroExtend 16 <<< 8 = w := by
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.truncate_eq_setWidth,
    BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h8 : i < 8
  · simp [h8, hi]
  · have hsub8 : i - 8 < 8 := by omega
    have h8i : 8 + (i - 8) = i := by omega
    simp [h8, hsub8, h8i, hi]

theorem bytesToPoly16_packPoly16ChunkBytes (coeffs : Nat → BitVec 16)
    (rest : List (BitVec 8)) (j : Nat) (hj : j < 16) :
    (bytesToPoly16 (packPoly16ChunkBytes coeffs ++ rest)).getD j 0#16 = coeffs j := by
  have hj256 : j < 256 := by omega
  have hlen : (packPoly16ChunkBytes coeffs).length = 32 := packPoly16ChunkBytes_length coeffs
  have heven : (packPoly16ChunkBytes coeffs ++ rest).toArray.getD (2 * j) 0#8 =
      (coeffs j).truncate 8 := by
    rw [toArray_getD_eq, list_getD_append_left _ _ _ _ (by omega),
      getD_packPoly16ChunkBytes_even coeffs j hj]
  have hodd : (packPoly16ChunkBytes coeffs ++ rest).toArray.getD (2 * j + 1) 0#8 =
      (coeffs j >>> 8).truncate 8 := by
    rw [toArray_getD_eq, list_getD_append_left _ _ _ _ (by omega),
      getD_packPoly16ChunkBytes_odd coeffs j hj]
  unfold bytesToPoly16
  rw [array_getD_ofFn _ _ _ hj256]
  dsimp only
  rw [heven, hodd, zeroExtend_lo_or_hi_eq]

@[simp] theorem bytesToPoly16_deserializeChunkBytes (d : Nat) (bs : List (BitVec 8))
    (j : Nat) (hj : j < 16) :
    (bytesToPoly16 (deserializeChunkBytes d bs)).getD j 0#16 = deserializeChunkCoeff d bs j := by
  simpa [deserializeChunkBytes] using
    bytesToPoly16_packPoly16ChunkBytes (deserializeChunkCoeff d bs) [] j hj

private theorem extractLsb'_16_of_bytes (bs : List (BitVec 8)) (off r : Nat) (hr : r < 4) :
    (ByteSlice.readLE bs off 8).extractLsb' (16 * r) 16 =
      (bs.getD (off + 2 * r + 1) 0#8) ++ (bs.getD (off + 2 * r) 0#8) := by
  ext i hi
  by_cases hi8 : i < 8
  · have hr8 : 2 * r < 8 := by omega
    have hbit := congrArg (fun b : BitVec 8 => b.getLsbD i)
      (ByteSlice.extractLsb'_readLE bs off 8 (2 * r) (by omega))
    simp only [hr8, ↓reduceIte, BitVec.getLsbD_extractLsb', hi8, decide_true, Bool.true_and] at hbit
    have hidx : 8 * (2 * r) + i = 16 * r + i := by omega
    rw [hidx] at hbit
    rw [BitVec.getElem_extractLsb', hbit, BitVec.getElem_append]
    simp [hi8]
  · have hisub : i - 8 < 8 := by omega
    have hr8 : 2 * r + 1 < 8 := by omega
    have hbit := congrArg (fun b : BitVec 8 => b.getLsbD (i - 8))
      (ByteSlice.extractLsb'_readLE bs off 8 (2 * r + 1) (by omega))
    simp only [hr8, ↓reduceIte, BitVec.getLsbD_extractLsb', hisub, decide_true,
      Bool.true_and] at hbit
    have hidx : 8 * (2 * r + 1) + (i - 8) = 16 * r + i := by omega
    have hoff1 : off + (2 * r + 1) = off + 2 * r + 1 := by omega
    rw [hidx, hoff1] at hbit
    rw [BitVec.getElem_extractLsb', hbit, BitVec.getElem_append]
    simp [hi8, BitVec.getLsbD_eq_getElem hisub]

private theorem append_hi_lo_eq (w : BitVec 16) :
    (w >>> 8).truncate 8 ++ w.truncate 8 = w := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth,
    BitVec.getLsbD_ushiftRight]
  by_cases hi8 : i < 8
  · simp [hi8, BitVec.getLsbD_eq_getElem hi]
  · have h8 : 8 + (i - 8) = i := by omega
    simp [hi8, h8, BitVec.getLsbD_eq_getElem hi]

/-- Lane `r < 8` of the first 128-bit NEON load `ldr q0, [outPtr]` (`readLE 8 ++ readLE 0`) after
`deserialize_{4,5,11}` equals `deserializeChunkCoeff d bs r`. -/
theorem q0_lane_deserializeChunkBytes (d : Nat) (bs : List (BitVec 8)) (r : Nat) (hr : r < 8) :
    ((ByteSlice.readLE (deserializeChunkBytes d bs) 8 8 ++
      ByteSlice.readLE (deserializeChunkBytes d bs) 0 8).extractLsb' (16 * r) 16) =
      deserializeChunkCoeff d bs r := by
  have hr16 : r < 16 := by omega
  by_cases hr4 : r < 4
  · have h1 : ((ByteSlice.readLE (deserializeChunkBytes d bs) 8 8 ++
        ByteSlice.readLE (deserializeChunkBytes d bs) 0 8).extractLsb' (16 * r) 16) =
        (ByteSlice.readLE (deserializeChunkBytes d bs) 0 8).extractLsb' (16 * r) 16 := by
      ext i hi
      have hlt : 16 * r + i < 64 := by omega
      rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb', BitVec.getLsbD_append]
      simp [hlt]
    rw [h1, extractLsb'_16_of_bytes _ 0 r hr4]
    simp only [Nat.zero_add, deserializeChunkBytes,
      getD_packPoly16ChunkBytes_even _ r hr16, getD_packPoly16ChunkBytes_odd _ r hr16,
      append_hi_lo_eq]
  · have hr' : r - 4 < 4 := by omega
    have h1 : ((ByteSlice.readLE (deserializeChunkBytes d bs) 8 8 ++
        ByteSlice.readLE (deserializeChunkBytes d bs) 0 8).extractLsb' (16 * r) 16) =
        (ByteSlice.readLE (deserializeChunkBytes d bs) 8 8).extractLsb' (16 * (r - 4)) 16 := by
      ext i hi
      have hlt : ¬(16 * r + i < 64) := by omega
      have hsub : 16 * r + i - 64 = 16 * (r - 4) + i := by omega
      rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb', BitVec.getLsbD_append]
      simp [hlt, hsub]
    rw [h1, extractLsb'_16_of_bytes _ 8 (r - 4) hr']
    have hev : 8 + 2 * (r - 4) = 2 * r := by omega
    rw [hev]
    simp only [deserializeChunkBytes,
      getD_packPoly16ChunkBytes_even _ r hr16, getD_packPoly16ChunkBytes_odd _ r hr16,
      append_hi_lo_eq]

/-- Lane `r < 8` of the second 128-bit NEON load `ldr q1, [outPtr, #16]` (`readLE 24 ++ readLE 16`)
after `deserialize_{4,5,11}` equals `deserializeChunkCoeff d bs (8 + r)`. -/
theorem q1_lane_deserializeChunkBytes (d : Nat) (bs : List (BitVec 8)) (r : Nat) (hr : r < 8) :
    ((ByteSlice.readLE (deserializeChunkBytes d bs) 24 8 ++
      ByteSlice.readLE (deserializeChunkBytes d bs) 16 8).extractLsb' (16 * r) 16) =
      deserializeChunkCoeff d bs (8 + r) := by
  have hr8 : 8 + r < 16 := by omega
  by_cases hr4 : r < 4
  · have h1 : ((ByteSlice.readLE (deserializeChunkBytes d bs) 24 8 ++
        ByteSlice.readLE (deserializeChunkBytes d bs) 16 8).extractLsb' (16 * r) 16) =
        (ByteSlice.readLE (deserializeChunkBytes d bs) 16 8).extractLsb' (16 * r) 16 := by
      ext i hi
      have hlt : 16 * r + i < 64 := by omega
      rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb', BitVec.getLsbD_append]
      simp [hlt]
    rw [h1, extractLsb'_16_of_bytes _ 16 r hr4]
    have hev : 16 + 2 * r = 2 * (8 + r) := by omega
    rw [hev]
    simp only [deserializeChunkBytes, getD_packPoly16ChunkBytes_even _ (8 + r) hr8,
      getD_packPoly16ChunkBytes_odd _ (8 + r) hr8, append_hi_lo_eq]
  · have hr' : r - 4 < 4 := by omega
    have h1 : ((ByteSlice.readLE (deserializeChunkBytes d bs) 24 8 ++
        ByteSlice.readLE (deserializeChunkBytes d bs) 16 8).extractLsb' (16 * r) 16) =
        (ByteSlice.readLE (deserializeChunkBytes d bs) 24 8).extractLsb' (16 * (r - 4)) 16 := by
      ext i hi
      have hlt : ¬(16 * r + i < 64) := by omega
      have hsub : 16 * r + i - 64 = 16 * (r - 4) + i := by omega
      rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb', BitVec.getLsbD_append]
      simp [hlt, hsub]
    rw [h1, extractLsb'_16_of_bytes _ 24 (r - 4) hr']
    have hev : 24 + 2 * (r - 4) = 2 * (8 + r) := by omega
    rw [hev]
    simp only [deserializeChunkBytes, getD_packPoly16ChunkBytes_even _ (8 + r) hr8,
      getD_packPoly16ChunkBytes_odd _ (8 + r) hr8, append_hi_lo_eq]

private theorem bytesToBits_slice_eq (fullBs : List (BitVec 8)) (byteOff byteLen idx : Nat)
    (hlen : byteOff + byteLen ≤ fullBs.length) (hidx : idx < 8 * byteLen) :
    (bytesToBits ((fullBs.drop byteOff).take byteLen)).getD idx 0 =
      (bytesToBits fullBs).getD (8 * byteOff + idx) 0 := by
  have hslen : ((fullBs.drop byteOff).take byteLen).length = byteLen := by
    rw [List.length_take, List.length_drop]; omega
  have h1 : idx < 8 * ((fullBs.drop byteOff).take byteLen).length := by omega
  have h2 : 8 * byteOff + idx < 8 * fullBs.length := by omega
  unfold bytesToBits
  rw [array_getD_ofFn _ _ _ h1, array_getD_ofFn _ _ _ h2]
  dsimp only
  rw [toArray_getD_eq, toArray_getD_eq]
  have hdiv : (8 * byteOff + idx) / 8 = byteOff + idx / 8 := by omega
  have hmod : (8 * byteOff + idx) % 8 = idx % 8 := by omega
  rw [hdiv, hmod]
  have hb : idx / 8 < byteLen := by omega
  have htake : ((fullBs.drop byteOff).take byteLen).getD (idx / 8) 0#8 =
      fullBs.getD (byteOff + idx / 8) 0#8 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt hb, List.getElem?_drop]
  rw [htake]

private theorem foldl_congr_list {xs : List Nat} (f g : Nat → Nat → Nat) (init : Nat)
    (hfg : ∀ acc k, k ∈ xs → f acc k = g acc k) :
    xs.foldl f init = xs.foldl g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [hfg init x List.mem_cons_self]
    exact ih (g init x) fun acc k hk => hfg acc k (List.mem_cons_of_mem x hk)

/-- Chunk-to-polynomial bridge: decoding the `c`-th `2 * d`-byte chunk (`c < 16`) matches
coefficient `16 * c + j` (`j < 16`) of `Spec.byteDecodeRaw d fullBs`. -/
theorem byteDecodeRaw_chunk_eq (d : Nat) (fullBs : List (BitVec 8)) (c j : Nat)
    (hc : c < 16) (hj : j < 16) (hlen : 2 * d * (c + 1) ≤ fullBs.length) :
    (byteDecodeRaw d ((fullBs.drop (2 * d * c)).take (2 * d))).getD j 0 =
      (byteDecodeRaw d fullBs).getD (16 * c + j) 0 := by
  have hj256 : j < 256 := by omega
  have hij256 : 16 * c + j < 256 := by omega
  unfold byteDecodeRaw
  rw [array_getD_ofFn _ _ _ hj256, array_getD_ofFn _ _ _ hij256]
  dsimp only
  apply foldl_congr_list
  intro acc k hk
  rw [List.mem_range] at hk
  have hslice : 2 * d * c + 2 * d ≤ fullBs.length := by
    rw [← Nat.mul_succ]
    exact hlen
  have hjdk : j * d + k < 8 * (2 * d) := by
    have h1 : j * d + k < (j + 1) * d := by rw [Nat.succ_mul]; omega
    have h2 : (j + 1) * d ≤ 16 * d := Nat.mul_le_mul_right d (by omega)
    have h3 : 16 * d = 8 * (2 * d) := by rw [← Nat.mul_assoc]
    omega
  have hbit := bytesToBits_slice_eq fullBs (2 * d * c) (2 * d) (j * d + k) hslice hjdk
  have h8c : 8 * (2 * d * c) = 16 * c * d := by
    calc 8 * (2 * d * c)
        = (8 * 2) * (d * c) := by rw [Nat.mul_assoc 2 d c, ← Nat.mul_assoc 8 2 (d * c)]
      _ = 16 * (c * d) := by rw [Nat.mul_comm d c]
      _ = 16 * c * d := by rw [Nat.mul_assoc]
  have hidx : 8 * (2 * d * c) + (j * d + k) = (16 * c + j) * d + k := by
    rw [h8c, Nat.add_mul, Nat.add_assoc]
  rw [hbit, hidx]

/-- Chunk-to-polynomial bridge for `Spec.decodeAndDecompress`. -/
theorem decodeAndDecompress_chunk_eq (d : Nat) (fullBs : List (BitVec 8)) (c j : Nat)
    (hc : c < 16) (hj : j < 16) (hlen : 2 * d * (c + 1) ≤ fullBs.length) :
    decompressCoeff d
      ((byteDecodeRaw d ((fullBs.drop (2 * d * c)).take (2 * d))).getD j 0) =
      (decodeAndDecompress d fullBs).getD (16 * c + j) 0 := by
  rw [byteDecodeRaw_chunk_eq d fullBs c j hc hj hlen]
  have hij256 : 16 * c + j < 256 := by omega
  unfold decodeAndDecompress byteDecodeRaw
  rw [Array.map_ofFn, array_getD_ofFn _ _ _ hij256, array_getD_ofFn _ _ _ hij256]
  rfl

/-! ### `PortableDeserializeArgs` & `Spec` Contracts (`B25`, `B26`, `B27`) -/

/-- Arguments for `PortableVector::deserialize_{4,5,11}` (`B25`, `B26`, `B27`). -/
structure PortableDeserializeArgs where
  outPtr  : BitVec 64
  inPtr   : BitVec 64
  inBytes : List (BitVec 8)

/-- Common entry register/length precondition for `PortableVector::deserialize_d`. -/
@[expose] def PortableDeserializePurePre (d : Nat) (a : PortableDeserializeArgs)
    (s0 : State) : Prop :=
  s0.readReg64 .x8 = a.outPtr ∧
  s0.readReg64 .x0 = a.inPtr ∧
  2 * d ≤ (s0.readReg64 .x1).toNat ∧
  a.inBytes.length = 2 * d

/-- `16`-byte-stack RO-input contract for `PortableVector::deserialize_d` (`d ∈ {4, 5, 11}`),
preserving both `NonSyscallPreserved` and all 32 128-bit SIMD registers (`sf.vregs = s0.vregs`). -/
@[expose] def mlkemDeserializeROSpec (d : Nat) : Spec PortableDeserializeArgs where
  pre := fun a s0 =>
    ⌜PortableDeserializePurePre d a s0⌝ ∗
    memRegion a.outPtr 32 ∗
    (a.inPtr ↦ᵣ a.inBytes) ∗
    stackAt s0.sp 16
  post := fun a s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧ sf.vregs = s0.vregs⌝ ∗
    (a.outPtr ↦ₛ deserializeChunkBytes d a.inBytes) ∗
    (a.inPtr ↦ᵣ a.inBytes) ∗
    stackAt s0.sp 16
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `16`-byte-stack RW-input contract for `PortableVector::deserialize_d` (`d ∈ {4, 5, 11}`). -/
@[expose] def mlkemDeserializeRWSpec (d : Nat) : Spec PortableDeserializeArgs where
  pre := fun a s0 =>
    ⌜PortableDeserializePurePre d a s0⌝ ∗
    memRegion a.outPtr 32 ∗
    (a.inPtr ↦ₛ a.inBytes) ∗
    stackAt s0.sp 16
  post := fun a s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧ sf.vregs = s0.vregs⌝ ∗
    (a.outPtr ↦ₛ deserializeChunkBytes d a.inBytes) ∗
    (a.inPtr ↦ₛ a.inBytes) ∗
    stackAt s0.sp 16
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `B25` (`deserialize_4`, `8`B → `32`B) RO-input contract. -/
abbrev mlkemDeserialize4ROSpec : Spec PortableDeserializeArgs := mlkemDeserializeROSpec 4

/-- `B25` (`deserialize_4`, `8`B → `32`B) RW-input contract. -/
abbrev mlkemDeserialize4RWSpec : Spec PortableDeserializeArgs := mlkemDeserializeRWSpec 4

/-- `B26` (`deserialize_5`, `10`B → `32`B) RO-input contract. -/
abbrev mlkemDeserialize5ROSpec : Spec PortableDeserializeArgs := mlkemDeserializeROSpec 5

/-- `B26` (`deserialize_5`, `10`B → `32`B) RW-input contract. -/
abbrev mlkemDeserialize5RWSpec : Spec PortableDeserializeArgs := mlkemDeserializeRWSpec 5

/-- `B27` (`deserialize_11`, `22`B → `32`B) RO-input contract. -/
abbrev mlkemDeserialize11ROSpec : Spec PortableDeserializeArgs := mlkemDeserializeROSpec 11

/-- `B27` (`deserialize_11`, `22`B → `32`B) RW-input contract. -/
abbrev mlkemDeserialize11RWSpec : Spec PortableDeserializeArgs := mlkemDeserializeRWSpec 11

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs

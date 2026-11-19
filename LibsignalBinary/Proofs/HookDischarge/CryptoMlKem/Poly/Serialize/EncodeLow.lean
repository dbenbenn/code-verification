/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh

/-!
# NEON Inlined `serialize_{1, 4}` Bit-Packing Soundness (`Poly.Serialize.EncodeLow`)

Pure NEON vector/scalar bit-packing equivalences for `serialize_1` (`1`B / `2`B, including fused
MSB `>>> 15` pre-shift + `bfi` + `strh` in `B04`) and `serialize_4` (`4`B / `8`B, including
`bfxil` + `str x` in `B20` and `Spec.neonCompressSerialize4`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 sqdmulh32 byteEncode neonCompressSerialize4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  lane16 lane64 pack8x16 dup8x16 fin8_cases ext_lane16 lane16_pack8x16 lane16_dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdUshlElem16 simdUshl8h simdExt16b lane16_and lane16_simdUshl8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (
  simdAddv4h simdAddv8h add4_eq_or_of_disjoint add8_eq_or_of_disjoint
  byteEncodeHalf byteEncodeChunk byteEncodeChunkVec
  eq_byteEncodeHalf_of_bits byteEncodeChunk_eq_append_half byteEncodeChunkVec_eq_append_half
  byteEncode_eq_flatten_chunks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh (
  lane64_simdExt16b_8_0)

private theorem bfm_bfm_ubfm : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := rfl
private theorem bfm_bfm_sbfm : (BitfieldOp.BFM == BitfieldOp.SBFM) = false := rfl

private theorem getLsbD_mask_pow2_64 (len k : Nat) (hk : k < 64) :
    (BitVec.ofNat 64 (Nat.shiftLeft 1 len - 1)).getLsbD k = decide (k < len) := by
  have hsh : Nat.shiftLeft 1 len = 2 ^ len := Nat.one_shiftLeft len
  rw [BitVec.getLsbD_ofNat, hsh, Nat.testBit_two_pow_sub_one]; simp [hk]

private theorem getLsbD_append8 (hi lo : BitVec 8) (k : Nat) :
    (hi ++ lo : BitVec 16).getLsbD k = if k < 8 then lo.getLsbD k else hi.getLsbD (k - 8) :=
  BitVec.getLsbD_append

private theorem getLsbD_append16 (hi lo : BitVec 16) (k : Nat) :
    (hi ++ lo : BitVec 32).getLsbD k = if k < 16 then lo.getLsbD k else hi.getLsbD (k - 16) :=
  BitVec.getLsbD_append

private theorem array_getD_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Nat) (d : α)
    (hi : i < n) : (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  unfold Array.getD
  split
  · rename_i h; change (Array.ofFn f)[i]'h = f ⟨i, hi⟩; exact Array.getElem_ofFn h
  · rename_i h; exact False.elim (h (by simp [hi]))

/-! ## 1. `serialize_1` (`1` Byte per Vector / `2` Bytes per Pair, `B04 +0x39c8..+0x39f0`) -/

@[expose] def neonSerialize1Half (v : BitVec 128) : List (BitVec 8) :=
  [(simdAddv8h (simdUshl8h (v &&& dup8x16 1#16) 0x00070006000500040003000200010000#128)).truncate 8]

@[expose] def neonSerialize1Bytes (v0 v1 : BitVec 128) : List (BitVec 8) :=
  neonSerialize1Half v0 ++ neonSerialize1Half v1

/-- Fused `compress_then_serialize_1` halfword (`B04 +0x39c8..+0x39e4`) from pre-shift `vPre`. -/
@[expose] def neonSerialize1MsbHalf (vPre : BitVec 128) : BitVec 16 :=
  simdAddv8h
    (simdUshl8h vPre 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 &&&
      0x00800040002000100008000400020001#128)

private theorem getElem_and1_shl (x : BitVec 16) (s b : Nat) (hs : s < 8) (hb : b < 16) :
    ((x &&& 1#16) <<< s)[b] = (decide (b = s) && x[0]) := by
  have h1 : ∀ r (hr : r < 16), (1#16)[r]'hr = decide (r = 0) := by intro r hr; revert r hr; decide
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_and]
  by_cases hbs : b < s
  · simp [hbs, show b ≠ s by omega]
  · rw [h1 (b - s) (by omega)]
    by_cases heq : b = s
    · subst heq; simp
    · simp [hbs, heq, show b - s ≠ 0 by omega]

private theorem getElem_single_shl (x : BitVec 16) (j : Fin 8) (b : Nat) (hb : b < 16) :
    ((x &&& 1#16) <<< j.val)[b] = (decide (b = j.val) && x[0]) :=
  getElem_and1_shl x j.val b j.isLt hb

private theorem add8_single_bits (x : Fin 8 → BitVec 16) :
    let f : Fin 8 → BitVec 16 := fun j => (x j &&& 1#16) <<< j.val
    ((f 0 + f 1) + (f 2 + f 3)) + ((f 4 + f 5) + (f 6 + f 7)) =
      ((f 0 ||| f 1) ||| (f 2 ||| f 3)) ||| ((f 4 ||| f 5) ||| (f 6 ||| f 7)) := by
  dsimp only
  apply add8_eq_or_of_disjoint <;> {
    ext b hb
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero, getElem_single_shl]
    rcases b with _ | _ | _ | _ | _ | _ | _ | _ | b <;> simp
  }

theorem neonSerialize1Half_eq (v : BitVec 128) :
    neonSerialize1Half v = byteEncodeHalf 1 (lane16 v) := by
  set w := simdUshl8h (v &&& dup8x16 1#16) 0x00070006000500040003000200010000#128
  have hcst : ∀ j : Fin 8,
      ((lane16 0x00070006000500040003000200010000#128 j).truncate 8).toInt = (j.val : Int) := by
    intro j; induction j using fin8_cases <;> decide
  have hsh : ∀ j : Fin 8, lane16 w j = (lane16 v j &&& 1#16) <<< j.val := by
    intro j; dsimp only [w]
    rw [lane16_simdUshl8h, lane16_and, lane16_dup8x16, simdUshlElem16, hcst j]
    simp only [Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
  have hsum : simdAddv8h w =
      (((lane16 v 0 &&& 1#16) <<< (0 : Fin 8).val ||| (lane16 v 1 &&& 1#16) <<< (1 : Fin 8).val) |||
       ((lane16 v 2 &&& 1#16) <<< (2 : Fin 8).val ||| (lane16 v 3 &&& 1#16) <<< (3 : Fin 8).val)) |||
      (((lane16 v 4 &&& 1#16) <<< (4 : Fin 8).val ||| (lane16 v 5 &&& 1#16) <<< (5 : Fin 8).val) |||
       ((lane16 v 6 &&& 1#16) <<< (6 : Fin 8).val ||| (lane16 v 7 &&& 1#16) <<< (7 : Fin 8).val)) := by
    unfold simdAddv8h
    rw [hsh 0, hsh 1, hsh 2, hsh 3, hsh 4, hsh 5, hsh 6, hsh 7]
    exact add8_single_bits (lane16 v)
  refine eq_byteEncodeHalf_of_bits ?_ ?_
  · rfl
  · intro k b hk hb
    have hk0 : k = 0 := by omega
    subst hk0
    change ([(simdAddv8h w).truncate 8].getD 0 0#8)[b] = _
    simp only [List.getD_cons_zero]
    rw [hsum, BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.div_one, Nat.mod_one]
    rcases b with _ | _ | _ | _ | _ | _ | _ | _ | b <;>
      try (simp [BitVec.getLsbD_eq_getElem])
    omega

theorem neonSerialize1Bytes_eq (v0 v1 : BitVec 128) :
    neonSerialize1Bytes v0 v1 = byteEncodeChunkVec 1 v0 v1 := by
  rw [neonSerialize1Bytes, neonSerialize1Half_eq, neonSerialize1Half_eq,
    byteEncodeChunkVec_eq_append_half]

private theorem fused1_lane_eq (p : BitVec 16) (j : Fin 8) :
    (p >>> (15 - j.val)) &&& (1#16 <<< j.val) = ((p >>> 15) &&& 1#16) <<< j.val := by
  have hm : ∀ (s : Fin 8) (r : Fin 16), (1#16 <<< s.val)[r.val] = decide (r.val = s.val) := by
    intro s r; revert s r; decide
  ext b hb
  rw [BitVec.getElem_and, hm j ⟨b, hb⟩, getElem_and1_shl (p >>> 15) j.val b j.isLt hb]
  by_cases heq : b = j.val
  · subst heq
    simp [BitVec.getElem_ushiftRight, show 15 - j.val + j.val = 15 by omega,
      BitVec.getLsbD_eq_getElem]
  · simp [heq]

theorem neonSerialize1MsbHalf_eq (vPre : BitVec 128) :
    [(neonSerialize1MsbHalf vPre).truncate 8] =
      byteEncodeHalf 1 (fun j => lane16 vPre j >>> 15) := by
  have hcst1 : ∀ j : Fin 8,
      ((lane16 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 j).truncate 8).toInt =
        -((15 - j.val : Nat) : Int) := by intro j; induction j using fin8_cases <;> decide
  have hcst2 : ∀ j : Fin 8,
      lane16 0x00800040002000100008000400020001#128 j = 1#16 <<< j.val := by
    intro j; induction j using fin8_cases <;> decide
  have hcst3 : ∀ j : Fin 8,
      ((lane16 0x00070006000500040003000200010000#128 j).truncate 8).toInt = (j.val : Int) := by
    intro j; induction j using fin8_cases <;> decide
  have hvec :
      simdUshl8h vPre 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 &&&
        0x00800040002000100008000400020001#128 =
      simdUshl8h (pack8x16 (fun j => lane16 vPre j >>> 15) &&& dup8x16 1#16)
        0x00070006000500040003000200010000#128 := by
    apply ext_lane16; intro j
    rw [lane16_and, lane16_simdUshl8h, lane16_simdUshl8h, lane16_and, lane16_pack8x16,
      lane16_dup8x16, hcst2 j, simdUshlElem16, simdUshlElem16, hcst1 j, hcst3 j]
    have hneg : ¬(-((15 - j.val : Nat) : Int) ≥ 0) := by omega
    simp only [hneg, ↓reduceIte, Int.neg_neg, Int.toNat_natCast, Int.natCast_nonneg]
    exact fused1_lane_eq (lane16 vPre j) j
  have heq : [(neonSerialize1MsbHalf vPre).truncate 8] =
      neonSerialize1Half (pack8x16 fun j => lane16 vPre j >>> 15) := by
    unfold neonSerialize1MsbHalf neonSerialize1Half; rw [hvec]
  rw [heq, neonSerialize1Half_eq]; congr 1; funext j; exact lane16_pack8x16 _ j

/-- `bfi w11, w12, #8, #24` (`evalBitfield .W32 .BFM dst src 24 23`) + `strh` (`unpack16`) (`B04`). -/
theorem evalBitfield_bfi_8_24_unpack16 (dst src : BitVec 64) :
    unpack16 ((evalBitfield .W32 .BFM dst src 24 23).truncate 16) =
      [dst.truncate 8, src.truncate 8] := by
  have hw : (evalBitfield .W32 .BFM dst src 24 23).truncate 16 =
      src.truncate 8 ++ dst.truncate 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    rw [getLsbD_append8]
    unfold evalBitfield
    dsimp only [Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd]
    simp only [bfm_bfm_ubfm, bfm_bfm_sbfm, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      show ¬(23 ≥ 24) by decide, BitVec.truncate_eq_setWidth, BitVec.zeroExtend,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, hk, show k < 32 by omega, show k < 64 by omega, decide_true,
      Bool.true_and]
    by_cases hk8 : k < 8
    · simp [hk8]
    · rw [getLsbD_mask_pow2_64 24 (k - 8) (by omega)]
      simp [hk8, show k - 8 < 8 by omega, show k - 8 < 24 by omega, show k - 8 < 32 by omega,
        show k - 8 < 64 by omega]
  rw [hw]; simp only [unpack16, List.cons.injEq, and_true]
  constructor
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', getLsbD_append8]; simp [hi]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', getLsbD_append8]
    simp [hi, show ¬(8 + i < 8) by omega, show 8 + i - 8 = i by omega]

theorem neonSerialize1Msb_bfi_eq (vPre0 vPre1 : BitVec 128) :
    unpack16 ((evalBitfield .W32 .BFM
      ((neonSerialize1MsbHalf vPre0).zeroExtend 64)
      ((neonSerialize1MsbHalf vPre1).zeroExtend 64) 24 23).truncate 16) =
      byteEncodeChunk 1 (fun j =>
        if h : j < 8 then lane16 vPre0 ⟨j, h⟩ >>> 15
        else if h2 : j - 8 < 8 then lane16 vPre1 ⟨j - 8, h2⟩ >>> 15
        else 0#16) := by
  have htr (x : BitVec 16) : (x.zeroExtend 64).truncate 8 = x.truncate 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hi]
  rw [evalBitfield_bfi_8_24_unpack16, htr, htr,
    show [(neonSerialize1MsbHalf vPre0).truncate 8, (neonSerialize1MsbHalf vPre1).truncate 8] =
      [(neonSerialize1MsbHalf vPre0).truncate 8] ++ [(neonSerialize1MsbHalf vPre1).truncate 8]
      from rfl,
    neonSerialize1MsbHalf_eq, neonSerialize1MsbHalf_eq, byteEncodeChunk_eq_append_half]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · congr 1; funext j; simp [j.isLt]
  · congr 1; funext j; simp [show ¬(8 + j.val < 8) by omega, j.isLt]

/-! ## 2. `serialize_4` (`4` Bytes per Vector / `8` Bytes per Pair, `B20 +0x2a58..+0x2aa8`) -/

@[expose] def neonSerialize4Lowt (v : BitVec 128) : BitVec 128 :=
  simdUshl8h (v &&& dup8x16 0x000f#16) 0x000c000800040000000c000800040000#128
@[expose] def neonSerialize4HalfWord32 (v : BitVec 128) : BitVec 32 :=
  let lowt := neonSerialize4Lowt v
  simdAddv4h (simdExt16b lowt lowt 8) ++ simdAddv4h lowt
@[expose] def neonSerialize4Half (v : BitVec 128) : List (BitVec 8) :=
  unpack32 (neonSerialize4HalfWord32 v)
@[expose] def neonSerialize4Word64 (v0 v1 : BitVec 128) : BitVec 64 :=
  neonSerialize4HalfWord32 v1 ++ neonSerialize4HalfWord32 v0
@[expose] def neonSerialize4Bytes (v0 v1 : BitVec 128) : List (BitVec 8) :=
  unpack64 (neonSerialize4Word64 v0 v1)

private theorem lane16_simdExt16b_8_low4 (u : BitVec 128) (r : Nat) (hr : r < 4) :
    lane16 (simdExt16b u u 8) ⟨r, by omega⟩ = lane16 u ⟨4 + r, by omega⟩ := by
  have h := congrArg (fun w : BitVec 64 => w.extractLsb' (16 * r) 16) (lane64_simdExt16b_8_0 u)
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hb64 := congrArg (fun x : BitVec 16 => x.getLsbD b) h
  simp only [lane64, lane16, BitVec.getLsbD_extractLsb', hb, show 16 * r + b < 64 by omega,
    decide_true, Bool.true_and, Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.zero_add,
    Nat.mul_one] at hb64 ⊢
  rwa [show 64 + (16 * r + b) = 16 * (4 + r) + b by omega] at hb64

private theorem getElem_nibble_shl (x : BitVec 16) (q b : Nat) (hq : q < 4) (hb : b < 16) :
    ((x &&& 0x000f#16) <<< (4 * q))[b] =
      (decide (4 * q ≤ b ∧ b < 4 * q + 4) && x.getLsbD (b - 4 * q)) := by
  have hm4 : ∀ r (hr : r < 16), (0x000f#16)[r]'hr = decide (r < 4) := by
    intro r hr; revert r hr; decide
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_and]
  by_cases hlo : b < 4 * q
  · simp [hlo, show ¬(4 * q ≤ b) by omega]
  · rw [hm4 (b - 4 * q) (by omega)]
    by_cases hhi : b < 4 * q + 4
    · simp [hlo, show 4 * q ≤ b by omega, hhi, show b - 4 * q < 4 by omega,
        BitVec.getLsbD_eq_getElem (show b - 4 * q < 16 by omega)]
    · simp [hlo, hhi, show ¬(b - 4 * q < 4) by omega]

private theorem getElem_nibble_shl_fin (x : BitVec 16) (q : Fin 4) (b : Nat) (hb : b < 16) :
    ((x &&& 0x000f#16) <<< (4 * q.val))[b] =
      (decide (4 * q.val ≤ b ∧ b < 4 * q.val + 4) && x.getLsbD (b - 4 * q.val)) :=
  getElem_nibble_shl x q.val b q.isLt hb

private theorem add4_nibbles (x : Fin 4 → BitVec 16) :
    let f : Fin 4 → BitVec 16 := fun q => (x q &&& 0x000f#16) <<< (4 * q.val)
    (f 0 + f 1) + (f 2 + f 3) = (f 0 ||| f 1) ||| (f 2 ||| f 3) := by
  dsimp only
  apply add4_eq_or_of_disjoint <;> {
    ext b hb
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero, getElem_nibble_shl_fin]
    rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | b <;> simp
  }

theorem neonSerialize4Half_eq (v : BitVec 128) :
    neonSerialize4Half v = byteEncodeHalf 4 (lane16 v) := by
  have hcst : ∀ j : Fin 8,
      ((lane16 0x000c000800040000000c000800040000#128 j).truncate 8).toInt =
        ((4 * (j.val % 4) : Nat) : Int) := by
    intro j; induction j using fin8_cases <;> decide
  have hlowt : ∀ j : Fin 8,
      lane16 (neonSerialize4Lowt v) j = (lane16 v j &&& 0x000f#16) <<< (4 * (j.val % 4)) := by
    intro j; unfold neonSerialize4Lowt
    rw [lane16_simdUshl8h, lane16_and, lane16_dup8x16, simdUshlElem16, hcst j]
    simp only [Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
  refine eq_byteEncodeHalf_of_bits ?_ ?_
  · simp [neonSerialize4Half]
  · intro k b hk hb
    have hsum0 : simdAddv4h (neonSerialize4Lowt v) =
        (((lane16 v 0 &&& 0x000f#16) <<< (4 * (0 : Fin 4).val) |||
          (lane16 v 1 &&& 0x000f#16) <<< (4 * (1 : Fin 4).val)) |||
         ((lane16 v 2 &&& 0x000f#16) <<< (4 * (2 : Fin 4).val) |||
          (lane16 v 3 &&& 0x000f#16) <<< (4 * (3 : Fin 4).val))) := by
      unfold simdAddv4h; rw [hlowt 0, hlowt 1, hlowt 2, hlowt 3]
      exact add4_nibbles (fun q => lane16 v ⟨q.val, by omega⟩)
    have hsum1 : simdAddv4h (simdExt16b (neonSerialize4Lowt v) (neonSerialize4Lowt v) 8) =
        (((lane16 v 4 &&& 0x000f#16) <<< (4 * (0 : Fin 4).val) |||
          (lane16 v 5 &&& 0x000f#16) <<< (4 * (1 : Fin 4).val)) |||
         ((lane16 v 6 &&& 0x000f#16) <<< (4 * (2 : Fin 4).val) |||
          (lane16 v 7 &&& 0x000f#16) <<< (4 * (3 : Fin 4).val))) := by
      let u := neonSerialize4Lowt v
      change (lane16 (simdExt16b u u 8) ⟨0, by decide⟩ + lane16 (simdExt16b u u 8) ⟨1, by decide⟩) +
        (lane16 (simdExt16b u u 8) ⟨2, by decide⟩ + lane16 (simdExt16b u u 8) ⟨3, by decide⟩) = _
      rw [lane16_simdExt16b_8_low4 u 0 (by decide), lane16_simdExt16b_8_low4 u 1 (by decide),
        lane16_simdExt16b_8_low4 u 2 (by decide), lane16_simdExt16b_8_low4 u 3 (by decide)]
      change (lane16 u 4 + lane16 u 5) + (lane16 u 6 + lane16 u 7) = _
      rw [hlowt 4, hlowt 5, hlowt 6, hlowt 7]
      exact add4_nibbles (fun q => lane16 v ⟨4 + q.val, by omega⟩)
    unfold neonSerialize4Half neonSerialize4HalfWord32 unpack32
    rcases k with _ | _ | _ | _ | k <;> try omega
    all_goals {
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [BitVec.getElem_extractLsb', getLsbD_append16]
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | b <;> try omega
      all_goals {
        simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceIte]
        rw [BitVec.getLsbD_eq_getElem (by decide)]
        first | rw [hsum0] | rw [hsum1]
        simp only [BitVec.getElem_or, getElem_nibble_shl_fin]
        simp
      }
    }

theorem neonSerialize4Bytes_eq (v0 v1 : BitVec 128) :
    neonSerialize4Bytes v0 v1 = byteEncodeChunkVec 4 v0 v1 := by
  rw [neonSerialize4Bytes, neonSerialize4Word64, unpack64_append32,
    ← neonSerialize4Half, ← neonSerialize4Half,
    neonSerialize4Half_eq, neonSerialize4Half_eq, byteEncodeChunkVec_eq_append_half]

/-- `bfxil x11, x12, #0, #16` (`evalBitfield .W64 .BFM (sum1.zeroExtend 64 <<< 16) (sum0.zeroExtend 64) 0 15`). -/
theorem evalBitfield_bfxil_0_16 (sum1 sum0 : BitVec 16) :
    evalBitfield .W64 .BFM ((sum1.zeroExtend 64) <<< 16) (sum0.zeroExtend 64) 0 15 =
      (sum1 ++ sum0).zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  unfold evalBitfield
  dsimp only [Nat.reduceMod, Nat.sub_zero, Nat.reduceAdd]
  simp only [bfm_bfm_ubfm, bfm_bfm_sbfm, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    show 15 ≥ 0 by decide, BitVec.ushiftRight_zero, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    getLsbD_append16, getLsbD_mask_pow2_64 16 k hk, hk, decide_true, Bool.true_and]
  by_cases hk16 : k < 16
  · simp [hk16]
  · by_cases hk32 : k < 32
    · simp [hk16, show k - 16 < 64 by omega, BitVec.getLsbD_of_ge sum0 k (by omega)]
    · simp [hk16, BitVec.getLsbD_of_ge sum0 k (by omega),
        BitVec.getLsbD_of_ge sum1 (k - 16) (by omega)]

/-- Exact 1-lane nibble expression in `Spec.neonCompressSerialize4`. -/
@[expose] def neonCompress4Nibble16 (x : BitVec 16) : BitVec 16 :=
  let u16 := x + ((x.sshiftRight 15) &&& 3329#16)
  let comp : BitVec 32 := (u16.zeroExtend 32 <<< 4) + 1664#32
  let qd := sqdmulh32 comp 10321340#32
  ((qd >>> 4).truncate 16) &&& 0x000f#16

/-- Full-polynomial bridge to `Spec.neonCompressSerialize4 re`. -/
theorem neonCompressSerialize4_eq_flatten (re : Poly16) (w0 w1 : Nat → BitVec 128)
    (hw0 : ∀ c < 16, ∀ j : Fin 8, lane16 (w0 c) j = neonCompress4Nibble16 (re.getD (16 * c + j.val) 0#16))
    (hw1 : ∀ c < 16, ∀ j : Fin 8,
      lane16 (w1 c) j = neonCompress4Nibble16 (re.getD (16 * c + 8 + j.val) 0#16)) :
    ((List.range 16).map fun c => neonSerialize4Bytes (w0 c) (w1 c)).flatten =
      neonCompressSerialize4 re := by
  unfold neonCompressSerialize4
  rw [byteEncode_eq_flatten_chunks 4 (by decide)]
  congr 1; apply List.map_congr_left; intro c hc
  have hc16 : c < 16 := List.mem_range.mp hc
  rw [neonSerialize4Bytes_eq, byteEncodeChunkVec_eq_append_half, byteEncodeChunk_eq_append_half]
  have hcell (idx : Nat) (hidx : idx < 256) :
      neonCompress4Nibble16 (re.getD idx 0#16) =
        BitVec.ofNat 16 ((Array.ofFn (n := 256) fun ⟨i, _⟩ =>
          let x := re.getD i 0#16
          let u16 := x + ((x.sshiftRight 15) &&& 3329#16)
          let u32 : BitVec 32 := u16.zeroExtend 32
          let comp := (u32 <<< 4) + 1664#32
          let qd := sqdmulh32 comp 10321340#32
          (((qd >>> 4).truncate 16) &&& 0x000f#16).toNat).getD idx 0) := by
    rw [array_getD_ofFn _ idx 0 hidx]; dsimp only
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  refine congrArg₂ (· ++ ·) ?_ ?_
  · apply congrArg (byteEncodeHalf 4); funext j; rw [hw0 c hc16 j, hcell _ (by omega)]
  · apply congrArg (byteEncodeHalf 4); funext j
    rw [hw1 c hc16 j, show 16 * c + 8 + j.val = 16 * c + (8 + j.val) by omega, hcell _ (by omega)]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common -- proof-setup: allow-public-import

/-!
# NEON Inlined `serialize_{5, 11}` Bit-Packing Soundness (`Poly.Serialize.EncodeMid`)

Pure NEON/scalar lane-extraction bit-packing equivalences for `serialize_5` (`5`B / `10`B,
`B07 +0x9df4..+0x9ecc`) and `serialize_11` (`11`B / `22`B, `B07 +0x77e0..+0x78f8`), including
LLVM `bfxil` (`evalBitfield .W32 .BFM`) and 32-bit shift-merge idioms.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (
  byteEncodeHalf byteEncodeChunkVec eq_byteEncodeHalf_of_bits byteEncodeChunkVec_eq_append_half
)

private theorem bfm_bfm_ubfm : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := rfl
private theorem bfm_bfm_sbfm : (BitfieldOp.BFM == BitfieldOp.SBFM) = false := rfl

private theorem getLsbD_mask_pow2_64 (len k : Nat) (hk : k < 64) :
    (BitVec.ofNat 64 (Nat.shiftLeft 1 len - 1)).getLsbD k = decide (k < len) := by
  have hsh : Nat.shiftLeft 1 len = 2 ^ len := Nat.one_shiftLeft len
  rw [BitVec.getLsbD_ofNat, hsh, Nat.testBit_two_pow_sub_one]
  simp [hk]

private theorem getLsbD_mask11_16 (r : Nat) : (0x07ff#16).getLsbD r = decide (r < 11) := by
  rw [show 0x07ff#16 = BitVec.ofNat 16 (2 ^ 11 - 1) from rfl, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases hr : r < 16
  · simp [hr]
  · simp [hr, show ¬(r < 11) by omega]

/-! ## 1. `serialize_5` (`5` Bytes per Vector / `10` Bytes per Pair, `B07 +0x9df4..+0x9ecc`) -/

@[expose] def neonSerialize5Half (v : BitVec 128) : List (BitVec 8) :=
  let c : Fin 8 → BitVec 16 := fun j => lane16 v j &&& 0x001f#16
  [(c 0 ||| (c 1 <<< 5)).truncate 8,
   ((c 1 >>> 3) ||| (c 2 <<< 2) ||| (c 3 <<< 7)).truncate 8,
   ((c 3 >>> 1) ||| (c 4 <<< 4)).truncate 8,
   ((c 4 >>> 4) ||| (c 5 <<< 1) ||| (c 6 <<< 6)).truncate 8,
   ((c 6 >>> 2) ||| (c 7 <<< 3)).truncate 8]

@[expose] def neonSerialize5Bytes (v0 v1 : BitVec 128) : List (BitVec 8) :=
  neonSerialize5Half v0 ++ neonSerialize5Half v1

theorem neonSerialize5Half_eq (v : BitVec 128) :
    neonSerialize5Half v = byteEncodeHalf 5 (lane16 v) := by
  refine eq_byteEncodeHalf_of_bits ?_ ?_
  · rfl
  · intro k b hk hb
    rcases k with _ | _ | _ | _ | _ | k <;> try omega
    all_goals {
      dsimp only [neonSerialize5Half, List.getD_cons_zero, List.getD_cons_succ]
      rw [← BitVec.getLsbD_eq_getElem hb]
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | b <;> try omega
      all_goals simp [BitVec.truncate_eq_setWidth]
    }

theorem neonSerialize5Bytes_eq (v0 v1 : BitVec 128) :
    neonSerialize5Bytes v0 v1 = byteEncodeChunkVec 5 v0 v1 := by
  rw [neonSerialize5Bytes, neonSerialize5Half_eq, neonSerialize5Half_eq,
    byteEncodeChunkVec_eq_append_half]

/-- `B07` LLVM idiom for byte 1 of `serialize_5` when `c1, c2` are already 5-bit masked. -/
theorem serialize5_byte1_llvm (c1 c2 c3 : BitVec 16)
    (hc1 : c1 &&& 0x001f#16 = c1) (hc2 : c2 &&& 0x001f#16 = c2) :
    ((((c2.zeroExtend 32 <<< 10) ||| (c3.zeroExtend 32 <<< 15)) ||| (c1.zeroExtend 32 <<< 5)) >>>
        8).truncate 8 =
      (((c1 >>> 3) ||| (c2 <<< 2) ||| ((c3 &&& 0x001f#16) <<< 7))).truncate 8 := by
  rw [← hc1, ← hc2]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> try omega
  all_goals simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend]

/-- `B07` LLVM idiom for byte 4 of `serialize_5`: `(c7 <<< 3).truncate 8` ignores bits `5..15` of `c7`. -/
theorem serialize5_byte4_unmasked (c6 c7 : BitVec 16) :
    (((c6 &&& 0x001f#16) >>> 2) ||| (c7 <<< 3)).truncate 8 =
      (((c6 &&& 0x001f#16) >>> 2) ||| ((c7 &&& 0x001f#16) <<< 3)).truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> try omega
  all_goals simp [BitVec.truncate_eq_setWidth]

/-! ## 2. `serialize_11` (`11` Bytes per Vector / `22` Bytes per Pair, `B07 +0x77e0..+0x78f8`) -/

@[expose] def neonSerialize11Half (v : BitVec 128) : List (BitVec 8) :=
  let c : Fin 8 → BitVec 16 := fun j => lane16 v j &&& 0x07ff#16
  [(c 0).truncate 8,
   ((c 0 >>> 8) ||| (c 1 <<< 3)).truncate 8,
   ((c 1 >>> 5) ||| (c 2 <<< 6)).truncate 8,
   (c 2 >>> 2).truncate 8,
   ((c 2 >>> 10) ||| (c 3 <<< 1)).truncate 8,
   ((c 3 >>> 7) ||| (c 4 <<< 4)).truncate 8,
   ((c 4 >>> 4) ||| (c 5 <<< 7)).truncate 8,
   (c 5 >>> 1).truncate 8,
   ((c 5 >>> 9) ||| (c 6 <<< 2)).truncate 8,
   ((c 6 >>> 6) ||| (c 7 <<< 5)).truncate 8,
   (c 7 >>> 3).truncate 8]

@[expose] def neonSerialize11Bytes (v0 v1 : BitVec 128) : List (BitVec 8) :=
  neonSerialize11Half v0 ++ neonSerialize11Half v1

theorem neonSerialize11Half_eq (v : BitVec 128) :
    neonSerialize11Half v = byteEncodeHalf 11 (lane16 v) := by
  refine eq_byteEncodeHalf_of_bits ?_ ?_
  · rfl
  · intro k b hk hb
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
    all_goals {
      dsimp only [neonSerialize11Half, List.getD_cons_zero, List.getD_cons_succ]
      rw [← BitVec.getLsbD_eq_getElem hb]
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | b <;> try omega
      all_goals simp [BitVec.truncate_eq_setWidth]
    }

theorem neonSerialize11Bytes_eq (v0 v1 : BitVec 128) :
    neonSerialize11Bytes v0 v1 = byteEncodeChunkVec 11 v0 v1 := by
  rw [neonSerialize11Bytes, neonSerialize11Half_eq, neonSerialize11Half_eq,
    byteEncodeChunkVec_eq_append_half]

/-- `B07` `bfxil w, c2, #10, #1` (`evalBitfield .W32 .BFM (c3 <<< 1) c2 10 10`) produces byte 4 of `serialize_11`. -/
theorem serialize11_byte4_bfxil (c2 c3 : BitVec 16) :
    (evalBitfield .W32 .BFM ((c3.zeroExtend 64) <<< 1) (c2.zeroExtend 64) 10 10).truncate 8 =
      (((c2 &&& 0x07ff#16) >>> 10) ||| ((c3 &&& 0x07ff#16) <<< 1)).truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold evalBitfield
  dsimp only [Nat.reduceMod, Nat.sub_self, Nat.reduceAdd]
  simp only [bfm_bfm_ubfm, bfm_bfm_sbfm, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    show 10 ≥ 10 by decide, BitVec.truncate_eq_setWidth, BitVec.zeroExtend,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, getLsbD_mask11_16,
    getLsbD_mask_pow2_64 1 i (by omega), hi, show i < 32 by omega, show i < 64 by omega,
    decide_true, Bool.true_and]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> try omega
  all_goals simp

/-- `B07` `bfxil w, c5, #9, #2` (`evalBitfield .W32 .BFM (c6 <<< 2) c5 9 10`) produces byte 8 of `serialize_11`. -/
theorem serialize11_byte8_bfxil (c5 c6 : BitVec 16) :
    (evalBitfield .W32 .BFM ((c6.zeroExtend 64) <<< 2) (c5.zeroExtend 64) 9 10).truncate 8 =
      (((c5 &&& 0x07ff#16) >>> 9) ||| ((c6 &&& 0x07ff#16) <<< 2)).truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold evalBitfield
  dsimp only [Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd]
  simp only [bfm_bfm_ubfm, bfm_bfm_sbfm, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    show 10 ≥ 9 by decide, BitVec.truncate_eq_setWidth, BitVec.zeroExtend,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, getLsbD_mask11_16,
    getLsbD_mask_pow2_64 2 i (by omega), hi, show i < 32 by omega, show i < 64 by omega,
    decide_true, Bool.true_and]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> try omega
  all_goals simp

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid

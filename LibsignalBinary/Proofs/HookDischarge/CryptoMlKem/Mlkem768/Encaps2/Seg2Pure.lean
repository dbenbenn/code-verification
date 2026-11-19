/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base

/-!
# `encapsulate2` (`B20`) — Segment 2 Pure Equivalences & Slice Decompositions (`Seg2Pure`)

Proves vector-to-spec equivalences for `deserialize_12` (`tHat[0..2]`), `decompress_1(m)`
(`msgPoly`), and stack/slice decompositions used across `Seg2a`–`Seg2c`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16
  byteDecodeRaw
  decodeAndDecompress
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16
  ext_lane16
  fin8_cases
  lane8
  lane16
  lane16_pack8x16
  pack8x16
  pack16x8
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_and
  lane16_simdSshl8h
  lane16_simdUshl8h
  simdSshl8h
  simdSshlElem16
  simdTbl16b
  simdUshl8h
  simdUshlElem16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (
  lane16_neonDecompress1_eq_decodeAndDecompress
  neonDecompress1_8h
  neonDeserialize1_8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem
  PolyMem
  Vec32
  VecRangeMem
  poly32Mem_ofFn
  polyVecNat
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base (
  byteDecodeRaw12_even
  byteDecodeRaw12_odd
  rawCoeff0
  rawCoeff1
)

/-! ## 1. Pure `deserialize_12` (`tHat[0..2]`) & `decompress_1` (`msgPoly`) Definitions -/

@[expose] def loadVec12 (bs : List (BitVec 8)) (off : Nat) : BitVec 128 :=
  setSimdLane
    ((pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
        (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
        (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)).zeroExtend 128)
    32 2
    ((pack32 (bs.getD (off + 8) 0#8) (bs.getD (off + 9) 0#8)
        (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8)).zeroExtend 128)

@[expose] def rawDeser12 (v : BitVec 128) : BitVec 128 :=
  let t := simdTbl16b v 0x0b0a0a09080707060504040302010100#128
  let u := simdUshl8h t 0xfffc0000fffc0000fffc0000fffc0000#128
  u &&& 0x0fff0fff0fff0fff0fff0fff0fff0fff#128

@[expose] def tHatPoly16 (bs : List (BitVec 8)) : Poly16 :=
  (byteDecodeRaw 12 bs).map fun c => BitVec.ofNat 16 c

@[expose] def msgPoly16 (m : List (BitVec 8)) : Poly16 :=
  (decodeAndDecompress 1 m).map fun c => BitVec.ofNat 16 c

@[expose] def neonDecompress1Byte (w16 : BitVec 16) : BitVec 128 :=
  neonDecompress1_8h
    (simdSshl8h (dup8x16 w16) 0xfff9fffafffbfffcfffdfffe00ff0000#128 &&& dup8x16 1#16)

private theorem getLsbD_0xffffffff128 :
    ∀ k : Fin 128, (0xffffffff#128).getLsbD k.val = decide (k.val < 32) := by
  decide +kernel

private theorem getLsbD_not_lane2_mask128 :
    ∀ k : Fin 128,
      (~~~(0xffffffff#128 <<< 64)).getLsbD k.val = decide (k.val < 64 ∨ 96 ≤ k.val) := by
  decide +kernel

private theorem loadVec12_eq_bytes (bs : List (BitVec 8)) (off : Nat) :
    loadVec12 bs off =
      0#32 ++
      pack32 (bs.getD (off + 8) 0#8) (bs.getD (off + 9) 0#8)
        (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8) ++
      pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
        (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
        (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8) := by
  have hm1_eq : (~~~((1#128 <<< 32 - 1#128) <<< (2 * 32))) = ~~~(0xffffffff#128 <<< 64) := rfl
  have hm2_eq : (1#128 <<< 32 - 1#128) = 0xffffffff#128 := rfl
  unfold loadVec12 setSimdLane
  dsimp only
  set lo := pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
      (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
      (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have hm1 := getLsbD_not_lane2_mask128 ⟨k, hk⟩; dsimp only at hm1
  rw [hm1_eq, hm2_eq, show (2 * 32 : Nat) = 64 from rfl]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hm1, hk, decide_true, Bool.true_and]
  repeat rw [BitVec.getLsbD_append]
  by_cases hk64 : k < 64
  · simp [hk64]
  · by_cases hk96 : k < 96
    · have hm2 := getLsbD_0xffffffff128 ⟨k - 64, by omega⟩; dsimp only at hm2
      rw [hm2]
      simp [hk64, show ¬ (96 ≤ k) by omega, show k - 64 < 32 by omega,
        show k - 64 < 128 by omega]
    · have hm2 := getLsbD_0xffffffff128 ⟨k - 64, by omega⟩; dsimp only at hm2
      have hlo : lo.getLsbD k = false := BitVec.getLsbD_of_ge lo k (by omega)
      rw [hm2, hlo]
      simp [hk64, show 96 ≤ k by omega, show ¬ (k - 64 < 32) by omega]

private theorem getLsbD_append3 {a b c : Nat} (x : BitVec a) (y : BitVec b) (z : BitVec c)
    (k : Nat) :
    (x ++ (y ++ z)).getLsbD k = ((x ++ y) ++ z).getLsbD k := by
  simp only [BitVec.getLsbD_append]
  by_cases h1 : k < c
  · simp [h1, show k < b + c by omega]
  · by_cases h2 : k < b + c
    · simp [h1, h2, show k - c < b by omega]
    · simp [h1, h2, show ¬ (k - c < b) by omega, show k - (b + c) = k - c - b by omega]

private theorem lane8_pack12 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : BitVec 8) :
    let v : BitVec 128 := 0#32 ++ pack32 b8 b9 b10 b11 ++ pack64 b0 b1 b2 b3 b4 b5 b6 b7
    lane8 v 0 = b0 ∧ lane8 v 1 = b1 ∧ lane8 v 2 = b2 ∧ lane8 v 3 = b3 ∧
    lane8 v 4 = b4 ∧ lane8 v 5 = b5 ∧ lane8 v 6 = b6 ∧ lane8 v 7 = b7 ∧
    lane8 v 8 = b8 ∧ lane8 v 9 = b9 ∧ lane8 v 10 = b10 ∧ lane8 v 11 = b11 := by
  dsimp only [lane8, pack32, pack64]
  simp only [show (0 : Fin 16).val = 0 from rfl, show (1 : Fin 16).val = 1 from rfl,
    show (2 : Fin 16).val = 2 from rfl, show (3 : Fin 16).val = 3 from rfl,
    show (4 : Fin 16).val = 4 from rfl, show (5 : Fin 16).val = 5 from rfl,
    show (6 : Fin 16).val = 6 from rfl, show (7 : Fin 16).val = 7 from rfl,
    show (8 : Fin 16).val = 8 from rfl, show (9 : Fin 16).val = 9 from rfl,
    show (10 : Fin 16).val = 10 from rfl, show (11 : Fin 16).val = 11 from rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits

private theorem tbl_loadVec12_eq (bs : List (BitVec 8)) (off : Nat) :
    simdTbl16b (loadVec12 bs off) 0x0b0a0a09080707060504040302010100#128 =
      pack8x16 fun i =>
        let t := i.val / 2
        if i.val % 2 == 0 then
          bs.getD (off + 3 * t + 1) 0#8 ++ bs.getD (off + 3 * t) 0#8
        else
          bs.getD (off + 3 * t + 2) 0#8 ++ bs.getD (off + 3 * t + 1) 0#8 := by
  rw [loadVec12_eq_bytes]
  obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11⟩ :=
    lane8_pack12 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
      (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
      (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8) (bs.getD (off + 8) 0#8)
      (bs.getD (off + 9) 0#8) (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8)
  unfold simdTbl16b
  simp only [pack16x8, pack8x16,
    show (lane8 0x0b0a0a09080707060504040302010100#128 0).toNat = 0 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 1).toNat = 1 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 2).toNat = 1 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 3).toNat = 2 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 4).toNat = 3 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 5).toNat = 4 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 6).toNat = 4 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 7).toNat = 5 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 8).toNat = 6 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 9).toNat = 7 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 10).toNat = 7 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 11).toNat = 8 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 12).toNat = 9 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 13).toNat = 10 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 14).toNat = 10 by decide +kernel,
    show (lane8 0x0b0a0a09080707060504040302010100#128 15).toNat = 11 by decide +kernel,
    Nat.reduceLT, ↓reduceDIte]
  rw [show (⟨0, by decide⟩ : Fin 16) = 0 from rfl, hl0,
      show (⟨1, by decide⟩ : Fin 16) = 1 from rfl, hl1,
      show (⟨2, by decide⟩ : Fin 16) = 2 from rfl, hl2,
      show (⟨3, by decide⟩ : Fin 16) = 3 from rfl, hl3,
      show (⟨4, by decide⟩ : Fin 16) = 4 from rfl, hl4,
      show (⟨5, by decide⟩ : Fin 16) = 5 from rfl, hl5,
      show (⟨6, by decide⟩ : Fin 16) = 6 from rfl, hl6,
      show (⟨7, by decide⟩ : Fin 16) = 7 from rfl, hl7,
      show (⟨8, by decide⟩ : Fin 16) = 8 from rfl, hl8,
      show (⟨9, by decide⟩ : Fin 16) = 9 from rfl, hl9,
      show (⟨10, by decide⟩ : Fin 16) = 10 from rfl, hl10,
      show (⟨11, by decide⟩ : Fin 16) = 11 from rfl, hl11]
  have hpairs : ∀ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : BitVec 8),
      (x15 ++ x14 ++ x13 ++ x12 ++ x11 ++ x10 ++ x9 ++ x8 ++
        x7 ++ x6 ++ x5 ++ x4 ++ x3 ++ x2 ++ x1 ++ x0) =
      ((x15 ++ x14) ++ (x13 ++ x12) ++ (x11 ++ x10) ++ (x9 ++ x8) ++
        (x7 ++ x6) ++ (x5 ++ x4) ++ (x3 ++ x2) ++ (x1 ++ x0)) := by
    intro x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
    apply BitVec.eq_of_getLsbD_eq; intro k _
    symm
    repeat (rw [getLsbD_append3]; rw [BitVec.getLsbD_append]; rw [BitVec.getLsbD_append])
    symm
    repeat rw [BitVec.getLsbD_append]
  rw [hpairs]
  simp only [show (0 : Fin 8).val = 0 from rfl, show (1 : Fin 8).val = 1 from rfl,
    show (2 : Fin 8).val = 2 from rfl, show (3 : Fin 8).val = 3 from rfl,
    show (4 : Fin 8).val = 4 from rfl, show (5 : Fin 8).val = 5 from rfl,
    show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl,
    Nat.reduceDiv, Nat.reduceMod, Nat.reduceBEq, ↓reduceIte, Bool.false_eq_true,
    Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc]

private theorem getLsbD_0x0fff16 :
    ∀ k : Fin 16, (0x0fff#16).getLsbD k.val = decide (k.val < 12) := by decide +kernel

private theorem getLsbD_0x0f16 :
    ∀ k : Fin 16, (0x0f#16).getLsbD k.val = decide (k.val < 4) := by decide +kernel

private theorem even_mask_rawCoeff0 (b0 b1 : BitVec 8) :
    (b1 ++ b0) &&& 0x0fff#16 = BitVec.ofNat 16 (rawCoeff0 b0 b1) := by
  have h : (b1 ++ b0) &&& 0x0fff#16 =
      b0.zeroExtend 16 ||| ((b1.zeroExtend 16 &&& 0x0f#16) <<< 8) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hm12 := getLsbD_0x0fff16 ⟨i, hi⟩; dsimp only at hm12
    simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_setWidth, hm12, hi,
      decide_true, Bool.true_and]
    by_cases hi8 : i < 8
    · simp only [hi8, show i < 12 by omega, decide_true, Bool.and_true, Bool.not_true,
        Bool.false_and, Bool.or_false, ↓reduceIte]
    · by_cases hi12 : i < 12
      · have hm4 := getLsbD_0x0f16 ⟨i - 8, by omega⟩; dsimp only at hm4
        have hb0 : b0.getLsbD i = false := BitVec.getLsbD_of_ge b0 i (by omega)
        simp only [hi8, hi12, hm4, hb0, show i - 8 < 4 by omega, show i - 8 < 16 by omega,
          decide_true, decide_false, Bool.and_true, Bool.not_false, Bool.true_and,
          Bool.false_or, ↓reduceIte]
      · have hm4 := getLsbD_0x0f16 ⟨i - 8, by omega⟩; dsimp only at hm4
        have hb0 : b0.getLsbD i = false := BitVec.getLsbD_of_ge b0 i (by omega)
        simp only [hi8, hi12, hm4, hb0, show ¬ (i - 8 < 4) by omega, show i - 8 < 16 by omega,
          decide_true, decide_false, Bool.and_false, Bool.not_false, Bool.true_and,
          Bool.false_or, ↓reduceIte]
  rw [h, rawCoeff0, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem odd_mask_rawCoeff1 (b1 b2 : BitVec 8) :
    ((b2 ++ b1) >>> 4) &&& 0x0fff#16 = BitVec.ofNat 16 (rawCoeff1 b1 b2) := by
  have h : ((b2 ++ b1) >>> 4) &&& 0x0fff#16 =
      (b1.zeroExtend 16 >>> 4) ||| (b2.zeroExtend 16 <<< 4) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hm12 := getLsbD_0x0fff16 ⟨i, hi⟩; dsimp only at hm12
    simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
      BitVec.getLsbD_setWidth, hm12, hi, decide_true, Bool.true_and]
    by_cases hi4 : i < 4
    · simp [hi4, show i < 12 by omega, show 4 + i < 16 by omega, show 4 + i < 8 by omega]
    · by_cases hi12 : i < 12
      · have hb1 : b1.getLsbD (4 + i) = false := BitVec.getLsbD_of_ge b1 (4 + i) (by omega)
        simp [hi4, hi12, hb1, show 4 + i < 16 by omega, show ¬ (4 + i < 8) by omega,
          show 4 + i - 8 = i - 4 by omega, show i - 4 < 16 by omega]
      · have hb2 : b2.getLsbD (i - 4) = false := BitVec.getLsbD_of_ge b2 (i - 4) (by omega)
        by_cases h16 : 4 + i < 16
        · have hb1 : b1.getLsbD (4 + i) = false := BitVec.getLsbD_of_ge b1 (4 + i) (by omega)
          simp [hi4, hi12, h16, hb1, hb2, show ¬ (4 + i < 8) by omega,
            show 4 + i - 8 = i - 4 by omega, show i - 4 < 16 by omega]
        · simp [hi4, hi12, h16, hb2, show ¬ (4 + i < 8) by omega,
            show 4 + i - 8 = i - 4 by omega, show i - 4 < 16 by omega]
  rw [h, rawCoeff1, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem array_getD_map_ofNat16 (a : Array Nat) (idx : Nat) (h : idx < a.size) :
    (a.map fun c => BitVec.ofNat 16 c).getD idx 0#16 = BitVec.ofNat 16 (a.getD idx 0) := by
  simp [Array.getD, h]

theorem rawDeser12_loadVec12_eq {bs : List (BitVec 8)} (hlen : bs.length = 384)
    (k : Nat) (hk : k < 32) :
    rawDeser12 (loadVec12 bs (12 * k)) = polyVecNat (tHatPoly16 bs) k := by
  unfold rawDeser12
  rw [tbl_loadVec12_eq]
  apply ext_lane16
  have hushl0 (x : BitVec 16) : simdUshlElem16 x 0x0000#16 = x := by simp [simdUshlElem16]
  have hushl4 (x : BitVec 16) : simdUshlElem16 x 0xfffc#16 = x >>> 4 := by
    simp [simdUshlElem16]
  have hsize : (byteDecodeRaw 12 bs).size = 256 := by simp [byteDecodeRaw]
  intro i
  rw [lane16_and, lane16_simdUshl8h, lane16_pack8x16]
  unfold polyVecNat tHatPoly16
  rw [lane16_pack8x16, array_getD_map_ofNat16 _ _ (by omega)]
  induction i using fin8_cases
  · simp only [show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 0 = 0x0000#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 0 = 0x0fff#16 from rfl,
      show (0 : Fin 8).val = 0 from rfl, show 0 / 2 = 0 from rfl, show (0 % 2 == 0) = true from rfl,
      ↓reduceIte, Nat.mul_zero, Nat.add_zero, hushl0, even_mask_rawCoeff0,
      show 8 * k = 2 * (4 * k) by omega, byteDecodeRaw12_even hlen (by omega : 4 * k < 128),
      show 3 * (4 * k) = 12 * k by omega]
  · simp only [show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 1 = 0xfffc#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 1 = 0x0fff#16 from rfl,
      show (1 : Fin 8).val = 1 from rfl, show 1 / 2 = 0 from rfl,
      show (1 % 2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      Nat.mul_zero, Nat.add_zero, hushl4, odd_mask_rawCoeff1,
      show 8 * k + 1 = 2 * (4 * k) + 1 by omega, byteDecodeRaw12_odd hlen (by omega : 4 * k < 128),
      show 3 * (4 * k) = 12 * k by omega]
  · simp only [show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 2 = 0x0000#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 2 = 0x0fff#16 from rfl,
      show (2 : Fin 8).val = 2 from rfl, show 2 / 2 = 1 from rfl, show (2 % 2 == 0) = true from rfl,
      ↓reduceIte, hushl0, even_mask_rawCoeff0,
      show 8 * k + 2 = 2 * (4 * k + 1) by omega,
      byteDecodeRaw12_even hlen (by omega : 4 * k + 1 < 128),
      show 3 * (4 * k + 1) = 12 * k + 3 * 1 by omega]
  · simp only [show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 3 = 0xfffc#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 3 = 0x0fff#16 from rfl,
      show (3 : Fin 8).val = 3 from rfl, show 3 / 2 = 1 from rfl,
      show (3 % 2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, hushl4, odd_mask_rawCoeff1,
      show 8 * k + 3 = 2 * (4 * k + 1) + 1 by omega,
      byteDecodeRaw12_odd hlen (by omega : 4 * k + 1 < 128),
      show 3 * (4 * k + 1) = 12 * k + 3 * 1 by omega]
  · simp only [show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 4 = 0x0000#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 4 = 0x0fff#16 from rfl,
      show (4 : Fin 8).val = 4 from rfl, show 4 / 2 = 2 from rfl, show (4 % 2 == 0) = true from rfl,
      ↓reduceIte, hushl0, even_mask_rawCoeff0,
      show 8 * k + 4 = 2 * (4 * k + 2) by omega,
      byteDecodeRaw12_even hlen (by omega : 4 * k + 2 < 128),
      show 3 * (4 * k + 2) = 12 * k + 3 * 2 by omega]
  · simp only [show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 5 = 0xfffc#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 5 = 0x0fff#16 from rfl,
      show (5 : Fin 8).val = 5 from rfl, show 5 / 2 = 2 from rfl,
      show (5 % 2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, hushl4, odd_mask_rawCoeff1,
      show 8 * k + 5 = 2 * (4 * k + 2) + 1 by omega,
      byteDecodeRaw12_odd hlen (by omega : 4 * k + 2 < 128),
      show 3 * (4 * k + 2) = 12 * k + 3 * 2 by omega]
  · simp only [show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 6 = 0x0000#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 6 = 0x0fff#16 from rfl,
      show (6 : Fin 8).val = 6 from rfl, show 6 / 2 = 3 from rfl, show (6 % 2 == 0) = true from rfl,
      ↓reduceIte, hushl0, even_mask_rawCoeff0,
      show 8 * k + 6 = 2 * (4 * k + 3) by omega,
      byteDecodeRaw12_even hlen (by omega : 4 * k + 3 < 128),
      show 3 * (4 * k + 3) = 12 * k + 3 * 3 by omega]
  · simp only [show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 7 = 0xfffc#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 7 = 0x0fff#16 from rfl,
      show (7 : Fin 8).val = 7 from rfl, show 7 / 2 = 3 from rfl,
      show (7 % 2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, hushl4, odd_mask_rawCoeff1,
      show 8 * k + 7 = 2 * (4 * k + 3) + 1 by omega,
      byteDecodeRaw12_odd hlen (by omega : 4 * k + 3 < 128),
      show 3 * (4 * k + 3) = 12 * k + 3 * 3 by omega]

private theorem simdSshl_cst16_6_eq (v : BitVec 128) :
    simdSshl8h v 0xfff9fffafffbfffcfffdfffe00ff0000#128 =
      simdSshl8h v 0xfff9fffafffbfffcfffdfffeffff0000#128 := by
  apply ext_lane16
  intro i
  rw [lane16_simdSshl8h, lane16_simdSshl8h]
  unfold simdSshlElem16
  have htr : (lane16 0xfff9fffafffbfffcfffdfffe00ff0000#128 i).truncate 8 =
      (lane16 0xfff9fffafffbfffcfffdfffeffff0000#128 i).truncate 8 := by
    induction i using fin8_cases <;> rfl
  rw [htr]

theorem neonDecompress1Byte_eq {m : List (BitVec 8)} (hlen : m.length = 32)
    (k : Nat) (hk : k < 32) (w16 : BitVec 16) (hw : w16.truncate 8 = m.getD k 0#8) :
    neonDecompress1Byte w16 = polyVecNat (msgPoly16 m) k := by
  unfold neonDecompress1Byte
  rw [simdSshl_cst16_6_eq]
  change neonDecompress1_8h (neonDeserialize1_8h w16) = polyVecNat (msgPoly16 m) k
  have hsize : (decodeAndDecompress 1 m).size = 256 := by
    unfold decodeAndDecompress
    rw [Array.size_map]
    simp [byteDecodeRaw]
  apply ext_lane16; intro j
  unfold polyVecNat msgPoly16
  rw [lane16_pack8x16, array_getD_map_ofNat16 _ _ (by omega)]
  have hc : k / 2 < 16 := by omega
  have hclen : 2 * (k / 2 + 1) ≤ m.length := by omega
  have htr8 (b : BitVec 8) : (b.zeroExtend 16).truncate 8 = b := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    unfold BitVec.zeroExtend BitVec.truncate
    simp [hi]
  rcases (show k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 by omega) with hev | hod
  · have h := (lane16_neonDecompress1_eq_decodeAndDecompress m (k / 2) hc hclen
      w16 ((m.getD (2 * (k / 2) + 1) 0#8).zeroExtend 16) (hev ▸ hw) (htr8 _) j).1
    rw [h]; congr 2; omega
  · have h := (lane16_neonDecompress1_eq_decodeAndDecompress m (k / 2) hc hclen
      ((m.getD (2 * (k / 2)) 0#8).zeroExtend 16) w16 (htr8 _) (hod ▸ hw) j).2
    rw [h]; congr 2; omega

theorem ek_pointsTo_split (ekA : BitVec 64) {ek : List (BitVec 8)} (hek : ek.length = 1152) :
    (ekA ↦ₛ ek) =
      (ekA ↦ₛ ek.take 384) ∗
      ((ekA + 384#64) ↦ₛ (ek.drop 384).take 384) ∗
      ((ekA + 768#64) ↦ₛ (ek.drop 768).take 384) := by
  have h1 : ek = ek.take 384 ++ ek.drop 384 := (List.take_append_drop 384 ek).symm
  have h2 : ek.drop 384 = (ek.drop 384).take 384 ++ (ek.drop 768).take 384 := by
    have hd : (ek.drop 384).drop 384 = (ek.drop 768).take 384 := by
      rw [List.drop_drop, show 384 + 384 = 768 from rfl]
      symm; exact List.take_of_length_le (by simp [hek])
    rw [← hd, List.take_append_drop]
  conv_lhs => rw [h1, h2]
  have hl0 : (ek.take 384).length = 384 := by simp [hek]
  have hl1 : ((ek.drop 384).take 384).length = 384 := by simp [hek]
  rw [pointsToBytes_append, pointsToBytes_append, hl0, hl1]
  change (ekA ↦ₛ ek.take 384) ∗
    (((ekA + 384#64) ↦ₛ (ek.drop 384).take 384) ∗
      (((ekA + 384#64 + 384#64) ↦ₛ (ek.drop 768).take 384))) = _
  rw [BitVec.add_assoc, show (384#64 + 384#64 : BitVec 64) = 768#64 from rfl]

theorem sepWP_elim_poly32 {prog : Program} {target_pc : BitVec 64} {s : State}
    {ptr : BitVec 64} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ t : Vec32, SepWP prog target_pc s (Poly32Mem ptr t ∗ F) post oom) :
    SepWP prog target_pc s (memRegion ptr 512 ∗ F) post oom :=
  VecMem.SepWP.of_memRegion_vecRangeMem 32 ptr (by decide) rfl fun f => by
    rw [show VecRangeMem 32 ptr f = Poly32Mem ptr (Vec32.ofFn f) from
      (poly32Mem_ofFn ptr f).symm]
    exact h (Vec32.ofFn f)

theorem memRegion_2560_split (sp : BitVec 64) :
    memRegion (sp + 2928#64) 2560 =
      memRegion (sp + 2928#64) 512 ∗
      memRegion (sp + 3440#64) 512 ∗
      memRegion (sp + 3952#64) 512 ∗
      memRegion (sp + 4464#64) 512 ∗
      memRegion (sp + 4976#64) 512 := by
  rw [show (2560 : Nat) = 512 + 2048 from rfl, memRegion_split _ 512 2048 (by decide),
      show (2048 : Nat) = 512 + 1536 from rfl, memRegion_split _ 512 1536 (by decide),
      show (1536 : Nat) = 512 + 1024 from rfl, memRegion_split _ 512 1024 (by decide),
      show (1024 : Nat) = 512 + 512 from rfl, memRegion_split _ 512 512 (by decide)]
  simp only [BitVec.add_assoc,
    show (2928#64 + BitVec.ofNat 64 512 : BitVec 64) = 3440#64 from rfl,
    show (3440#64 + BitVec.ofNat 64 512 : BitVec 64) = 3952#64 from rfl,
    show (3952#64 + BitVec.ofNat 64 512 : BitVec 64) = 4464#64 from rfl,
    show (4464#64 + BitVec.ofNat 64 512 : BitVec 64) = 4976#64 from rfl]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure

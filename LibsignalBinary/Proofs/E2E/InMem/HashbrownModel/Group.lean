/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# Hashbrown 8-Byte Control-Group Lemmas

Bitvector definitions and lane characterizations for `hashbrown`'s 8-byte NEON and scalar SWAR
control-group operations (`Group::WIDTH = 8`).
-/

public section

namespace CryptoVerification.E2E.InMem.HashbrownModel

/-- `hashbrown`'s `Group::WIDTH` on `aarch64` (8 control bytes per group). -/
abbrev groupWidth : Nat := 8

abbrev emptyTag : BitVec 8 := 0xff#8

abbrev deletedTag : BitVec 8 := 0x80#8

/-- `BITMASK_ITER_MASK = 0x8080_8080_8080_8080`: keeps the MSB (bit 7) of each 8-bit lane. -/
abbrev bitmaskIterMask : BitVec 64 := 0x8080808080808080#64

/-- `Tag::is_full`: a control byte represents a full bucket iff its top bit (MSB) is clear. -/
@[expose] def isFullTag (b : BitVec 8) : Bool := !b.msb

/-- `Tag::is_special`: a control byte represents `EMPTY` or `DELETED` iff its top bit is set. -/
@[expose] def isSpecialTag (b : BitVec 8) : Bool := b.msb

/-- `Tag::full(hash)`: top 7 bits of a 64-bit hash, with MSB = 0 (`(hash >> 57) & 0x7f`). -/
@[expose] def h2Tag (hash : BitVec 64) : BitVec 8 :=
  (hash >>> 57).truncate 8 &&& 0x7f#8

/-- Primary hash `h1(hash)`: the full 64-bit hash word. -/
def h1Word (hash : BitVec 64) : BitVec 64 := hash

/-- Extract byte lane `i` (`0 ≤ i < 8`) from a 64-bit little-endian group word. -/
@[expose] def groupByte (w : BitVec 64) (i : Nat) : BitVec 8 :=
  w.extractLsb' (8 * i) 8

/-- Pack 8 control bytes `b0..b7` into a 64-bit little-endian group word (byte `0` in bits `0..7`). -/
@[expose] def packGroupWord (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b0.zeroExtend 64 |||
  (b1.zeroExtend 64 <<< 8) |||
  (b2.zeroExtend 64 <<< 16) |||
  (b3.zeroExtend 64 <<< 24) |||
  (b4.zeroExtend 64 <<< 32) |||
  (b5.zeroExtend 64 <<< 40) |||
  (b6.zeroExtend 64 <<< 48) |||
  (b7.zeroExtend 64 <<< 56)

/-- Replicate an 8-bit tag across all 8 lanes of a 64-bit word (`vdup_n_u8(tag)` / `repeat(tag)`). -/
@[expose] def repeatByte (b : BitVec 8) : BitVec 64 :=
  packGroupWord b b b b b b b b

/-- Extract the 8-bit mask for lane `i` (`0x80` in lane `i`, `0x00` elsewhere). -/
@[expose] def laneBit (i : Nat) : BitVec 64 :=
  (0x80#64) <<< (8 * i)

/-- Extract the full 8-bit lane mask (`0xff` in lane `i`, `0x00` elsewhere). -/
@[expose] def laneFullMask (i : Nat) : BitVec 64 :=
  (0xff#64) <<< (8 * i)

/-- NEON bytewise equality (`vceq_u8(w, vdup_n_u8(tag))` / `cmeq v0.8b, v0.8b, v1.8b`):
lane `i` is `0xff` if `groupByte w i == tag`, else `0x00`. -/
@[expose] def neonMatchTag (w : BitVec 64) (tag : BitVec 8) : BitVec 64 :=
  packGroupWord
    (if groupByte w 0 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 1 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 2 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 3 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 4 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 5 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 6 == tag then 0xff#8 else 0x00#8)
    (if groupByte w 7 == tag then 0xff#8 else 0x00#8)

/-- NEON `match_empty`: `vceq_u8(w, vdup_n_u8(0xff))` (`cmtst` / `cmeq` against `0xff`). -/
@[expose] def neonMatchEmpty (w : BitVec 64) : BitVec 64 :=
  neonMatchTag w emptyTag

/-- NEON `match_empty_or_deleted`: `vcltz_s8(w)` (`cmlt v0.8b, v0.8b, #0`):
lane `i` is `0xff` iff `(groupByte w i).msb = true` (signed `< 0`), else `0x00`. -/
@[expose] def neonMatchEmptyOrDeleted (w : BitVec 64) : BitVec 64 :=
  packGroupWord
    (if (groupByte w 0).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 1).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 2).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 3).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 4).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 5).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 6).msb then 0xff#8 else 0x00#8)
    (if (groupByte w 7).msb then 0xff#8 else 0x00#8)

/-- NEON `match_full`: `vcgez_s8(w)` (`cmge v0.8b, v0.8b, #0`):
lane `i` is `0xff` iff `(groupByte w i).msb = false` (signed `≥ 0`), else `0x00`. -/
@[expose] def neonMatchFull (w : BitVec 64) : BitVec 64 :=
  packGroupWord
    (if !(groupByte w 0).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 1).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 2).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 3).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 4).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 5).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 6).msb then 0xff#8 else 0x00#8)
    (if !(groupByte w 7).msb then 0xff#8 else 0x00#8)

/-- Scalar SWAR (`generic.rs`) `match_tag`:
`let cmp = w ^ repeat(tag); (cmp.wrapping_sub(0x0101_0101_0101_0101) & !cmp & 0x8080_8080_8080_8080)`. -/
def swarMatchTag (w : BitVec 64) (tag : BitVec 8) : BitVec 64 :=
  let cmp := w ^^^ repeatByte tag
  (cmp - 0x0101010101010101#64) &&& (~~~cmp) &&& 0x8080808080808080#64

/-! ## Basic `h2Tag` / `isFullTag` / `isSpecialTag` Lemmas -/

@[simp]
theorem emptyTag_msb : emptyTag.msb = true := rfl

@[simp]
theorem deletedTag_msb : deletedTag.msb = true := rfl

@[simp]
theorem isFullTag_emptyTag : isFullTag emptyTag = false := rfl

@[simp]
theorem isFullTag_deletedTag : isFullTag deletedTag = false := rfl

@[simp]
theorem isSpecialTag_emptyTag : isSpecialTag emptyTag = true := rfl

@[simp]
theorem isSpecialTag_deletedTag : isSpecialTag deletedTag = true := rfl

theorem h2Tag_msb (hash : BitVec 64) : (h2Tag hash).msb = false := by
  simp [h2Tag, BitVec.msb_eq_getLsbD_last]

@[simp]
theorem isFullTag_h2Tag (hash : BitVec 64) : isFullTag (h2Tag hash) = true := by
  simp [isFullTag, h2Tag_msb]

@[simp]
theorem isSpecialTag_h2Tag (hash : BitVec 64) : isSpecialTag (h2Tag hash) = false := by
  simp [isSpecialTag, h2Tag_msb]

theorem h2Tag_ne_emptyTag (hash : BitVec 64) : h2Tag hash ≠ emptyTag := by
  intro h
  have := congrArg BitVec.msb h
  rw [h2Tag_msb, emptyTag_msb] at this
  exact Bool.false_ne_true this

/-! ## Extracting Bytes from `packGroupWord` -/

@[simp]
theorem groupByte_packGroupWord_0 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 0 = b0 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_1 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 1 = b1 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_2 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 2 = b2 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_3 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 3 = b3 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_4 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 4 = b4 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_5 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 5 = b5 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_6 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 6 = b6 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

@[simp]
theorem groupByte_packGroupWord_7 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    groupByte (packGroupWord b0 b1 b2 b3 b4 b5 b6 b7) 7 = b7 := by
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [groupByte, packGroupWord]

/-! ## NEON Group Match Byte-Lane Characterization (`neon.rs`) -/

/-- Whether lane `i` (`0 ≤ i < 8`) is active in a `BitMask` after applying `BITMASK_ITER_MASK`
(`0x8080_8080_8080_8080`): bit `8 * i + 7` is set. -/
@[expose] def laneSet (m : BitVec 64) (i : Nat) : Bool :=
  m.getLsbD (8 * i + 7)

/-- Applying `BITMASK_ITER_MASK` (`0x8080_8080_8080_8080`) preserves `laneSet` for every lane `i < 8`. -/
theorem laneSet_and_bitmaskIterMask (m : BitVec 64) (i : Nat) (hi : i < 8) :
    laneSet (m &&& bitmaskIterMask) i = laneSet m i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [laneSet, bitmaskIterMask]

theorem laneSet_eq_groupByte_msb (m : BitVec 64) (i : Nat) :
    laneSet m i = (groupByte m i).msb := by
  simp [laneSet, groupByte, BitVec.msb_eq_getLsbD_last]

/-! ## `umaxv` (`match_empty().any_bit_set()`) and `convert_special_to_empty_and_full_to_deleted` -/

/-- `umaxv b0, v0.8b` on an 8-byte NEON vector: unsigned maximum across the 8 byte lanes. -/
@[expose] def neonUmaxv8 (w : BitVec 64) : BitVec 8 :=
  let m01 := if (groupByte w 0).toNat ≤ (groupByte w 1).toNat then groupByte w 1 else groupByte w 0
  let m23 := if (groupByte w 2).toNat ≤ (groupByte w 3).toNat then groupByte w 3 else groupByte w 2
  let m45 := if (groupByte w 4).toNat ≤ (groupByte w 5).toNat then groupByte w 5 else groupByte w 4
  let m67 := if (groupByte w 6).toNat ≤ (groupByte w 7).toNat then groupByte w 7 else groupByte w 6
  let m03 := if m01.toNat ≤ m23.toNat then m23 else m01
  let m47 := if m45.toNat ≤ m67.toNat then m67 else m45
  if m03.toNat ≤ m47.toNat then m47 else m03

/-- On `neonMatchTag w tag` (where every byte lane is `0xff#8` or `0x00#8`), `neonUmaxv8` is `0xff#8`
if some lane matches `tag`, else `0x00#8`. -/
theorem neonUmaxv8_neonMatchTag (w : BitVec 64) (tag : BitVec 8) :
    neonUmaxv8 (neonMatchTag w tag) =
      if (groupByte w 0 == tag) || (groupByte w 1 == tag) ||
         (groupByte w 2 == tag) || (groupByte w 3 == tag) ||
         (groupByte w 4 == tag) || (groupByte w 5 == tag) ||
         (groupByte w 6 == tag) || (groupByte w 7 == tag)
      then 0xff#8 else 0x00#8 := by
  simp only [neonUmaxv8, neonMatchTag,
    groupByte_packGroupWord_0, groupByte_packGroupWord_1,
    groupByte_packGroupWord_2, groupByte_packGroupWord_3,
    groupByte_packGroupWord_4, groupByte_packGroupWord_5,
    groupByte_packGroupWord_6, groupByte_packGroupWord_7]
  cases (groupByte w 0 == tag) <;>
  cases (groupByte w 1 == tag) <;>
  cases (groupByte w 2 == tag) <;>
  cases (groupByte w 3 == tag) <;>
  cases (groupByte w 4 == tag) <;>
  cases (groupByte w 5 == tag) <;>
  cases (groupByte w 6 == tag) <;>
  cases (groupByte w 7 == tag) <;> rfl

/-- Bit 0 of `neonUmaxv8 (neonMatchEmpty w)` (tested by `tbnz w8, #0` in compiled `find_inner` /
`find_or_find_insert_index_inner`) is `true` iff at least one byte lane of `w` is `emptyTag` (`0xff`). -/
theorem neonUmaxv8_neonMatchEmpty_getLsbD_zero (w : BitVec 64) :
    (neonUmaxv8 (neonMatchEmpty w)).getLsbD 0 =
      ((groupByte w 0 == emptyTag) || (groupByte w 1 == emptyTag) ||
       (groupByte w 2 == emptyTag) || (groupByte w 3 == emptyTag) ||
       (groupByte w 4 == emptyTag) || (groupByte w 5 == emptyTag) ||
       (groupByte w 6 == emptyTag) || (groupByte w 7 == emptyTag)) := by
  rw [neonMatchEmpty, neonUmaxv8_neonMatchTag]
  cases ((groupByte w 0 == emptyTag) || (groupByte w 1 == emptyTag) ||
         (groupByte w 2 == emptyTag) || (groupByte w 3 == emptyTag) ||
         (groupByte w 4 == emptyTag) || (groupByte w 5 == emptyTag) ||
         (groupByte w 6 == emptyTag) || (groupByte w 7 == emptyTag)) <;> rfl

/-- If at least one lane `i < 8` of `w` is `emptyTag` (`0xff`), then bit 0 of
`neonUmaxv8 (neonMatchEmpty w)` is `true` (`tbnz w8, #0` branches). -/
theorem neonUmaxv8_neonMatchEmpty_getLsbD_zero_of_exists (w : BitVec 64)
    (i : Nat) (hi : i < 8) (hemp : groupByte w i = emptyTag) :
    (neonUmaxv8 (neonMatchEmpty w)).getLsbD 0 = true := by
  rw [neonUmaxv8_neonMatchEmpty_getLsbD_zero]
  have hb : (groupByte w i == emptyTag) = true := beq_iff_eq.mpr hemp
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [hb]

@[simp]
private theorem getElem_if_ff_00_7 (b : Bool) :
    (if b then 0xff#8 else 0x00#8)[7] = b := by
  cases b <;> decide

@[simp]
private theorem getElem_if_false_ff_00_7 (b : Bool) :
    (if b = false then 0xff#8 else 0x00#8)[7] = !b := by
  cases b <;> decide

@[simp]
theorem groupByte_repeatByte (b : BitVec 8) (i : Nat) (hi : i < 8) :
    groupByte (repeatByte b) i = b := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [repeatByte]

/-! ## Scalar SWAR (`generic.rs`) Group Match Byte-Lane Characterization -/

/-- All-empty group word (`0xffff_ffff_ffff_ffff`). -/
abbrev emptyGroupWord : BitVec 64 := 0xffffffffffffffff#64

@[simp]
theorem repeatByte_emptyTag : repeatByte emptyTag = emptyGroupWord := rfl

@[simp]
theorem groupByte_emptyGroupWord (i : Nat) (hi : i < 8) :
    groupByte emptyGroupWord i = emptyTag := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp]
theorem neonMatchEmpty_emptyGroupWord :
    neonMatchEmpty emptyGroupWord = emptyGroupWord := rfl

@[simp]
theorem neonMatchEmptyOrDeleted_emptyGroupWord :
    neonMatchEmptyOrDeleted emptyGroupWord = emptyGroupWord := rfl

@[simp]
theorem neonMatchFull_emptyGroupWord :
    neonMatchFull emptyGroupWord = 0#64 := rfl

/-- On `emptyGroupWord`, `neonMatchTag emptyGroupWord (h2Tag hash)` is always `0#64`
because `h2Tag hash` has MSB `false` whereas `emptyTag` (`0xff`) has MSB `true`. -/
@[simp]
theorem neonMatchTag_emptyGroupWord_h2Tag (hash : BitVec 64) :
    neonMatchTag emptyGroupWord (h2Tag hash) = 0#64 := by
  have hne : (emptyTag == h2Tag hash) = false :=
    beq_false_of_ne (Ne.symm (h2Tag_ne_emptyTag hash))
  simp [neonMatchTag, groupByte_emptyGroupWord, hne, packGroupWord]

end CryptoVerification.E2E.InMem.HashbrownModel

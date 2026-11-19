/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownModel.Group -- proof-setup: allow-public-import

/-!
# Hashbrown `BitMask` and `BitMaskIter` Lemmas

Bitvector lemmas for `hashbrown`'s 64-bit `BitMask` and `BitMaskIter` on AArch64
(`BITMASK_STRIDE = 8`, `BITMASK_ITER_MASK = 0x8080_8080_8080_8080`), modeling
`trailing_zeros() / 8` as `w.reverse.clz >>> 3`.
-/

public section

namespace CryptoVerification.E2E.InMem.HashbrownModel

/-- Trailing zeros of a 64-bit word, modeled via `(w.reverse).clz` (`RBIT` + `CLZ` on `aarch64`). -/
@[expose] def ctz64 (w : BitVec 64) : BitVec 64 :=
  w.reverse.clz

/-- `BitMask::trailing_zeros`: `self.0.trailing_zeros() / BITMASK_STRIDE` (`(rbit w).clz >>> 3`). -/
@[expose] def bitmaskTrailingZeros (w : BitVec 64) : Nat :=
  ((ctz64 w) >>> 3).toNat

/-- `BitMask::lowest_set_bit`: `if w = 0 then none else some (bitmaskTrailingZeros w)`. -/
@[expose] def lowestSetBit (w : BitVec 64) : Option Nat :=
  if w = 0#64 then none else some (bitmaskTrailingZeros w)

/-- `BitMask::remove_lowest_bit`: `w & (w - 1)`. -/
@[expose] def removeLowestBit (w : BitVec 64) : BitVec 64 :=
  w &&& (w - 1#64)

/-- `BitMask::any_bit_set`: `w != 0`. -/
@[expose] def anyBitSet (w : BitVec 64) : Bool :=
  w != 0#64

/-- Canonical 8-lane iteration mask built from 8 lane booleans `b0..b7`:
lane `i` has bit `8 * i + 7` set (`0x80 <<< (8 * i)`) iff `bi = true`, and all other bits are `0`. -/
@[expose] def mkIterMask (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : BitVec 64 :=
  packGroupWord
    (if b0 then 0x80#8 else 0x00#8)
    (if b1 then 0x80#8 else 0x00#8)
    (if b2 then 0x80#8 else 0x00#8)
    (if b3 then 0x80#8 else 0x00#8)
    (if b4 then 0x80#8 else 0x00#8)
    (if b5 then 0x80#8 else 0x00#8)
    (if b6 then 0x80#8 else 0x00#8)
    (if b7 then 0x80#8 else 0x00#8)

/-! ## Equivalence of NEON `match_* &&& bitmaskIterMask` and `mkIterMask` -/

private theorem zext_shift_and_bitmaskIterMask_0 (b : BitVec 8) :
    b.zeroExtend 64 &&& bitmaskIterMask = (if b.msb then 0x80#8 else 0x00#8).zeroExtend 64 := by
  revert b; decide

@[simp]
private theorem msb_if_ff_00 (b : Bool) : (if b then 0xff#8 else 0x00#8).msb = b := by
  cases b <;> rfl

/-- Canonical 8-lane full byte mask (`0xff` in lane `i` iff `bi = true`, `0x00` otherwise),
matching raw NEON comparison outputs (`vceq_u8`, `vcltz_s8`, `vcgez_s8`) prior to `BITMASK_ITER_MASK`. -/
@[expose] def mkFullMask (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : BitVec 64 :=
  packGroupWord
    (if b0 then 0xff#8 else 0x00#8)
    (if b1 then 0xff#8 else 0x00#8)
    (if b2 then 0xff#8 else 0x00#8)
    (if b3 then 0xff#8 else 0x00#8)
    (if b4 then 0xff#8 else 0x00#8)
    (if b5 then 0xff#8 else 0x00#8)
    (if b6 then 0xff#8 else 0x00#8)
    (if b7 then 0xff#8 else 0x00#8)

theorem neonMatchTag_eq_mkFullMask (w : BitVec 64) (tag : BitVec 8) :
    neonMatchTag w tag =
      mkFullMask
        (groupByte w 0 == tag) (groupByte w 1 == tag)
        (groupByte w 2 == tag) (groupByte w 3 == tag)
        (groupByte w 4 == tag) (groupByte w 5 == tag)
        (groupByte w 6 == tag) (groupByte w 7 == tag) := rfl

/-! ## `laneSet` on `mkIterMask` and `mkFullMask` -/

@[simp]
theorem laneSet_mkIterMask_0 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 0 = b0 := by
  cases b0 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_1 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 1 = b1 := by
  cases b1 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_2 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 2 = b2 := by
  cases b2 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_3 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 3 = b3 := by
  cases b3 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_4 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 4 = b4 := by
  cases b4 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_5 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 5 = b5 := by
  cases b5 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_6 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 6 = b6 := by
  cases b6 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkIterMask_7 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkIterMask b0 b1 b2 b3 b4 b5 b6 b7) 7 = b7 := by
  cases b7 <;> simp [laneSet_eq_groupByte_msb, mkIterMask]

@[simp]
theorem laneSet_mkFullMask_0 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 0 = b0 := by
  cases b0 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_1 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 1 = b1 := by
  cases b1 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_2 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 2 = b2 := by
  cases b2 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_3 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 3 = b3 := by
  cases b3 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_4 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 4 = b4 := by
  cases b4 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_5 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 5 = b5 := by
  cases b5 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_6 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 6 = b6 := by
  cases b6 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

@[simp]
theorem laneSet_mkFullMask_7 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    laneSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) 7 = b7 := by
  cases b7 <;> simp [laneSet_eq_groupByte_msb, mkFullMask]

/-! ## `firstTrueLane`: Lowest Set Bit / Trailing Zeros Div 8 = First Matching Lane -/

/-- Index of the first `true` boolean among 8 lanes `b0..b7`, or `none` if all are `false`. -/
@[expose] def firstTrueLane (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Option Nat :=
  if b0 then some 0
  else if b1 then some 1
  else if b2 then some 2
  else if b3 then some 3
  else if b4 then some 4
  else if b5 then some 5
  else if b6 then some 6
  else if b7 then some 7
  else none

set_option maxRecDepth 4096 in
set_option maxRecDepth 4096 in
theorem anyBitSet_mkFullMask (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    anyBitSet (mkFullMask b0 b1 b2 b3 b4 b5 b6 b7) =
      (b0 || b1 || b2 || b3 || b4 || b5 || b6 || b7) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl

/-- `anyBitSet (neonMatchEmpty w)` equals `(neonUmaxv8 (neonMatchEmpty w)).getLsbD 0`
(confirming that `umaxv` + `tbnz w8, #0` in the compiled binary implements `match_empty().any_bit_set()`). -/
theorem anyBitSet_neonMatchEmpty_eq_umaxv (w : BitVec 64) :
    anyBitSet (neonMatchEmpty w) = (neonUmaxv8 (neonMatchEmpty w)).getLsbD 0 := by
  rw [neonUmaxv8_neonMatchEmpty_getLsbD_zero]
  unfold neonMatchEmpty
  rw [neonMatchTag_eq_mkFullMask, anyBitSet_mkFullMask]

/-! ## `BitMask::remove_lowest_bit` (`w &&& (w - 1#64)`) Removes the Lowest Lane -/

/-! ## Single-Lane `laneBit` / `laneFullMask` and Zero `BitMask` Concrete Lemmas -/

@[simp]
theorem lowestSetBit_zero : lowestSetBit 0#64 = none := rfl

@[simp]
theorem removeLowestBit_zero : removeLowestBit 0#64 = 0#64 := rfl

@[simp]
theorem anyBitSet_zero : anyBitSet 0#64 = false := rfl

@[simp]
theorem mkIterMask_all_false :
    mkIterMask false false false false false false false false = 0#64 := rfl

@[simp]
theorem mkFullMask_all_false :
    mkFullMask false false false false false false false false = 0#64 := rfl

@[simp]
theorem laneBit_ne_zero (i : Nat) (hi : i < 8) : laneBit i ≠ 0#64 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

@[simp]
theorem anyBitSet_laneBit (i : Nat) (hi : i < 8) : anyBitSet (laneBit i) = true := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp]
theorem laneBit_and_bitmaskIterMask (i : Nat) (hi : i < 8) :
    laneBit i &&& bitmaskIterMask = laneBit i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp]
theorem laneFullMask_and_bitmaskIterMask (i : Nat) (hi : i < 8) :
    laneFullMask i &&& bitmaskIterMask = laneBit i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
@[simp]
theorem bitmaskTrailingZeros_laneBit (i : Nat) (hi : i < 8) :
    bitmaskTrailingZeros (laneBit i) = i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
@[simp]
theorem lowestSetBit_laneBit (i : Nat) (hi : i < 8) :
    lowestSetBit (laneBit i) = some i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp]
theorem removeLowestBit_laneBit (i : Nat) (hi : i < 8) :
    removeLowestBit (laneBit i) = 0#64 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
@[simp]
theorem bitmaskTrailingZeros_laneFullMask (i : Nat) (hi : i < 8) :
    bitmaskTrailingZeros (laneFullMask i) = i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
@[simp]
theorem lowestSetBit_laneFullMask (i : Nat) (hi : i < 8) :
    lowestSetBit (laneFullMask i) = some i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end CryptoVerification.E2E.InMem.HashbrownModel

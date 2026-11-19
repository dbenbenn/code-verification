/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownModel.Table -- proof-setup: allow-public-import

/-!
# Hashbrown `find` and `find_insert_slot` on 4-Bucket Tables

Pure lookup (`find4`) and insertion-slot (`findInsertIndexInGroup`, `fixInsertIndex4`,
`findInsertSlot4At`) lemmas for 4-bucket (`mask = 3#64`) `hashbrown` tables.
-/

public section

namespace CryptoVerification.E2E.InMem.HashbrownModel

/-! ## `find` (`find_inner`) on 4-Bucket Tables -/

/-- The initial `BitMaskIter` word produced by `g.match_tag(h2_hash).into_iter()` at probe position
`pos` on control byte list `cbs`:
`ldr d9, [ctrl, pos]`, `cmeq v0.8b, v9.8b, v8.8b`, `fmov x8, d0`, `ands x27, x8, #0x8080808080808080`. -/
@[expose] def findGroupIterMask (cbs : List (BitVec 8)) (pos : Nat) (qtag : BitVec 8) : BitVec 64 :=
  neonMatchTag (loadGroupAt cbs pos) qtag &&& bitmaskIterMask

/-- Bounded loop of `find_inner` on the initial group mask at probe position `pos < 4` (since a
4-bucket table's first group always contains an `EMPTY` padding lane, `find_inner` inspects at most
one group). -/
@[expose] def findIterMaskLoop (pos : Nat) (m : BitVec 64) (eqAt : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    match lowestSetBit m with
    | none => none
    | some bit =>
      let idx := (pos + bit) % 4
      if eqAt idx then some idx
      else findIterMaskLoop pos (removeLowestBit m) eqAt fuel

/-- Pure model of `RawTableInner::find_inner` on a 4-bucket table (`mask = 3#64`). -/
@[expose] def find4 (cbs : List (BitVec 8)) (hash : BitVec 64) (eqAt : Nat → Bool) : Option Nat :=
  let pos := (probePos hash 3#64).toNat
  let qtag := h2Tag hash
  findIterMaskLoop pos (findGroupIterMask cbs pos qtag) eqAt 8

@[simp]
theorem findIterMaskLoop_zero_mask (pos : Nat) (eqAt : Nat → Bool) (fuel : Nat) :
    findIterMaskLoop pos 0#64 eqAt (fuel + 1) = none := rfl

@[simp]
theorem findIterMaskLoop_laneBit (pos bit : Nat) (hbit : bit < 8) (eqAt : Nat → Bool) (fuel : Nat) :
    findIterMaskLoop pos (laneBit bit) eqAt (fuel + 2) =
      if eqAt ((pos + bit) % 4) then some ((pos + bit) % 4) else none := by
  simp [findIterMaskLoop, lowestSetBit_laneBit bit hbit, removeLowestBit_laneBit bit hbit]

@[simp]
theorem findGroupIterMask_emptyCtrl4 (pos : Nat) (hpos : pos < 4) (hash : BitVec 64) :
    findGroupIterMask emptyCtrl4 pos (h2Tag hash) = 0#64 :=
  neonMatchTag_loadGroupAt_emptyCtrl4_and_bitmaskIterMask pos hpos (h2Tag hash) (h2Tag_msb hash)

@[simp]
theorem lowestSetBit_findGroupIterMask_emptyCtrl4 (pos : Nat) (hpos : pos < 4) (hash : BitVec 64) :
    lowestSetBit (findGroupIterMask emptyCtrl4 pos (h2Tag hash)) = none := by
  rw [findGroupIterMask_emptyCtrl4 pos hpos hash, lowestSetBit_zero]

@[simp]
theorem find4_emptyCtrl4 (hash : BitVec 64) (eqAt : Nat → Bool) :
    find4 emptyCtrl4 hash eqAt = none := by
  dsimp only [find4]
  have hpos : (probePos hash 3#64).toNat < 4 := probePos_3_toNat_lt hash
  rw [findGroupIterMask_emptyCtrl4 _ hpos hash]
  rfl

/-- On `singleCtrl4 k tag` (`k < 4`, `pos < 4`), `findGroupIterMask` is `laneBit (laneOfBucket4 pos k)`
if `tag == h2Tag hash` and `0#64` otherwise. -/
theorem findGroupIterMask_singleCtrl4 (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (tag : BitVec 8) (hash : BitVec 64) :
    findGroupIterMask (singleCtrl4 k tag) pos (h2Tag hash) =
      if tag == h2Tag hash then laneBit (laneOfBucket4 pos k) else 0#64 :=
  neonMatchTag_loadGroupAt_singleCtrl4_and_bitmaskIterMask
    k pos hk hpos tag (h2Tag hash) (h2Tag_msb hash)

/-- On `singleCtrl4 k tag` (`k < 4`), `find4` returns `some k` if `tag == h2Tag hash` and
`eqAt k = true`, and `none` otherwise. -/
theorem find4_singleCtrl4 (k : Nat) (hk : k < 4) (tag : BitVec 8)
    (hash : BitVec 64) (eqAt : Nat → Bool) :
    find4 (singleCtrl4 k tag) hash eqAt =
      if (tag == h2Tag hash) && eqAt k then some k else none := by
  dsimp only [find4]
  have hpos : (probePos hash 3#64).toNat < 4 := probePos_3_toNat_lt hash
  generalize (probePos hash 3#64).toNat = pos at hpos ⊢
  rw [findGroupIterMask_singleCtrl4 k pos hk hpos tag hash]
  cases hbeq : (tag == h2Tag hash)
  · simp
  · have hlt : laneOfBucket4 pos k < 8 := laneOfBucket4_lt_8 pos k hpos hk
    have hmod : (pos + laneOfBucket4 pos k) % 4 = k :=
      (probe4_reaches_every_bucket emptyTag emptyTag emptyTag emptyTag pos k hpos hk).2.1
    simp [findIterMaskLoop_laneBit pos (laneOfBucket4 pos k) hlt eqAt 6, hmod]

/-! ## `find_insert_slot` on 4-Bucket Tables -/

/-- `RawTableInner::find_insert_index_in_group`:
`group.match_empty_or_deleted().lowest_set_bit()`.
In the compiled `aarch64` binary (`store_session::{closure#0}` at `0x90a4..0x90bc`), this is:
`cmlt v0.8b, v0.8b, #0`, `fmov x9, d0`, `cbz x9`, `rbit x9, x9`, `clz x9, x9`, `lsr #3`. -/
def findInsertIndexInGroup (g : BitVec 64) : Option Nat :=
  lowestSetBit (neonMatchEmptyOrDeleted g)

set_option maxRecDepth 4096 in
@[simp]
theorem findInsertIndexInGroup_emptyCtrl4 (pos : Nat) (hpos : pos < 4) :
    findInsertIndexInGroup (loadGroupAt emptyCtrl4 pos) = some 0 := by
  unfold findInsertIndexInGroup
  rw [neonMatchEmptyOrDeleted_loadGroupAt_emptyCtrl4 pos hpos]
  rfl

set_option maxRecDepth 4096 in
@[simp]
theorem bitmaskTrailingZeros_neonMatchEmptyOrDeleted_emptyCtrl4 (pos : Nat) (hpos : pos < 4) :
    bitmaskTrailingZeros (neonMatchEmptyOrDeleted (loadGroupAt emptyCtrl4 pos)) = 0 := by
  rw [neonMatchEmptyOrDeleted_loadGroupAt_emptyCtrl4 pos hpos]
  rfl

/-! ### `find_insert_slot` on a 1-Item 4-Bucket Table (`singleCtrl4 k tag`) -/

@[simp]
theorem not_laneFullMask_ne_zero (i : Nat) (hi : i < 8) :
    ~~~(laneFullMask i) ≠ 0#64 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 4096 in
@[simp]
theorem bitmaskTrailingZeros_not_laneFullMask (i : Nat) (hi : i < 8) :
    bitmaskTrailingZeros (~~~(laneFullMask i)) = if i = 0 then 1 else 0 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
@[simp]
theorem lowestSetBit_not_laneFullMask (i : Nat) (hi : i < 8) :
    lowestSetBit (~~~(laneFullMask i)) = some (if i = 0 then 1 else 0) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp]
theorem laneOfBucket4_eq_zero_iff (pos k : Nat) (hpos : pos < 4) (hk : k < 4) :
    laneOfBucket4 pos k = 0 ↔ pos = k := by
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  decide

/-! ### General `fix_insert_index` on Any Non-Full 4-Bucket Table (`mkCtrl4 b0 b1 b2 b3`) -/

/-! ## `CtrlMirrorInv` and `FullBucketsInv` Corollaries (`n ≤ 1`, `mask = 3#64`) -/

end CryptoVerification.E2E.InMem.HashbrownModel

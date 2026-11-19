/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownModel.BitMask -- proof-setup: allow-public-import

/-!
# Hashbrown 4-Bucket Table Control-Array and Probe Lemmas

Control-byte mirror invariants (`CtrlMirrorInv`, `FullBucketsInv`), `set_ctrl` mirror-index updates
(`setCtrlMirrorIdx`, `setCtrlList`), and single-group reachability over the 12-byte mirrored control
array of a 4-bucket (`mask = 3#64`) `hashbrown` table.
-/

public section

namespace CryptoVerification.E2E.InMem.HashbrownModel

/-! ## Control-Byte Invariants (`tableAt` Conventions) -/

/-- Control-byte length and mirrored-tail invariant (`cbs.length = mask.toNat + 1 + 8`) of
`tableAt`. -/
@[expose] def CtrlMirrorInv (mask : BitVec 64) (cbs : List (BitVec 8)) : Prop :=
  cbs.length = mask.toNat + 1 + groupWidth ∧
  ∀ i < groupWidth, cbs[mask.toNat + 1 + i]? =
    if mask.toNat + 1 + i < groupWidth then some emptyTag
    else cbs[i % (mask.toNat + 1)]?

/-- Full-bucket index-list invariant of `tableAt`: `full` lists the deduplicated indices
`i < mask.toNat + 1` whose control byte has `msb = false`. -/
@[expose] def FullBucketsInv (mask : BitVec 64) (cbs : List (BitVec 8)) (full : List Nat) : Prop :=
  full.Nodup ∧
  ∀ i, i ∈ full ↔ i < mask.toNat + 1 ∧ ∃ b, cbs[i]? = some b ∧ b.msb = false

/-- The 12-byte control array of a 4-bucket table (`mask = 3#64`) with bucket tags `b0, b1, b2, b3`:
4 real control bytes, 4 `EMPTY` (`0xff`) padding bytes, and 4 mirrored control bytes `b0, b1, b2, b3`. -/
@[expose] def mkCtrl4 (b0 b1 b2 b3 : BitVec 8) : List (BitVec 8) :=
  [b0, b1, b2, b3, emptyTag, emptyTag, emptyTag, emptyTag, b0, b1, b2, b3]

/-- The 12-byte control array of an empty 4-bucket table (all 12 bytes are `0xff#8`). -/
@[expose] def emptyCtrl4 : List (BitVec 8) :=
  mkCtrl4 emptyTag emptyTag emptyTag emptyTag

/-- The 12-byte control array of a 4-bucket table with a single entry at bucket `k < 4` (with tag `tag`)
and `EMPTY` (`0xff#8`) in the other 3 buckets. -/
@[expose] def singleCtrl4 (k : Nat) (tag : BitVec 8) : List (BitVec 8) :=
  mkCtrl4
    (if k = 0 then tag else emptyTag)
    (if k = 1 then tag else emptyTag)
    (if k = 2 then tag else emptyTag)
    (if k = 3 then tag else emptyTag)

@[simp]
theorem length_mkCtrl4 (b0 b1 b2 b3 : BitVec 8) :
    (mkCtrl4 b0 b1 b2 b3).length = 12 := rfl

@[simp]
theorem length_emptyCtrl4 : emptyCtrl4.length = 12 := rfl

@[simp]
theorem length_singleCtrl4 (k : Nat) (tag : BitVec 8) :
    (singleCtrl4 k tag).length = 12 := rfl

theorem ctrlMirrorInv_mkCtrl4 (b0 b1 b2 b3 : BitVec 8) :
    CtrlMirrorInv 3#64 (mkCtrl4 b0 b1 b2 b3) := by
  refine ⟨rfl, ?_⟩
  intro i hi
  change i < 8 at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem ctrlMirrorInv_emptyCtrl4 : CtrlMirrorInv 3#64 emptyCtrl4 :=
  ctrlMirrorInv_mkCtrl4 _ _ _ _

theorem ctrlMirrorInv_singleCtrl4 (k : Nat) (tag : BitVec 8) :
    CtrlMirrorInv 3#64 (singleCtrl4 k tag) :=
  ctrlMirrorInv_mkCtrl4 _ _ _ _

theorem fullBucketsInv_emptyCtrl4 : FullBucketsInv 3#64 emptyCtrl4 [] := by
  refine ⟨List.Pairwise.nil, ?_⟩
  intro i
  simp only [List.not_mem_nil, false_iff, not_and, not_exists]
  intro hi b hb
  have hlt : i < 4 := by simpa using hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp [emptyCtrl4, mkCtrl4] at hb
    subst hb
    decide

theorem fullBucketsInv_singleCtrl4 (k : Nat) (hk : k < 4) (tag : BitVec 8) (htag : tag.msb = false) :
    FullBucketsInv 3#64 (singleCtrl4 k tag) [k] := by
  refine ⟨List.Pairwise.cons (by simp) List.Pairwise.nil, ?_⟩
  intro i
  simp only [List.mem_singleton]
  have hm : (3#64).toNat + 1 = 4 := rfl
  rw [hm]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  all_goals
    constructor
    · rintro rfl
      refine ⟨by omega, tag, ?_, htag⟩
      simp [singleCtrl4, mkCtrl4]
    · rintro ⟨hi, b, hb, hmsb⟩
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      · simp [singleCtrl4, mkCtrl4] at hb
        subst hb
        first | rfl | (rw [emptyTag_msb] at hmsb; cases hmsb)

/-! ## `set_ctrl` Mirror Index `((i - 8) & mask) + 8` -/

/-- `hashbrown`'s `RawTableInner::set_ctrl` mirror index on 64-bit words:
`index2 = ((index.wrapping_sub(Group::WIDTH)) & self.bucket_mask) + Group::WIDTH`. -/
@[expose] def setCtrlMirrorIdx (mask i : BitVec 64) : BitVec 64 :=
  ((i - 8#64) &&& mask) + 8#64

@[simp]
theorem setCtrlMirrorIdx_3_0 : setCtrlMirrorIdx 3#64 0#64 = 8#64 := rfl

@[simp]
theorem setCtrlMirrorIdx_3_1 : setCtrlMirrorIdx 3#64 1#64 = 9#64 := rfl

@[simp]
theorem setCtrlMirrorIdx_3_2 : setCtrlMirrorIdx 3#64 2#64 = 10#64 := rfl

@[simp]
theorem setCtrlMirrorIdx_3_3 : setCtrlMirrorIdx 3#64 3#64 = 11#64 := rfl

/-- On a 4-bucket table (`mask = 3#64`), for any bucket index `k < 4`,
`setCtrlMirrorIdx 3#64 (BitVec.ofNat 64 k) = BitVec.ofNat 64 (k + 8)`. -/
theorem setCtrlMirrorIdx_3_ofNat (k : Nat) (hk : k < 4) :
    setCtrlMirrorIdx 3#64 (BitVec.ofNat 64 k) = BitVec.ofNat 64 (k + 8) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- Pure list model of `RawTableInner::set_ctrl(index, tag)`: writes `tag` at `index` and at
`setCtrlMirrorIdx mask index`. -/
@[expose] def setCtrlList (mask : BitVec 64) (cbs : List (BitVec 8)) (i : BitVec 64) (tag : BitVec 8) :
    List (BitVec 8) :=
  (cbs.set i.toNat tag).set (setCtrlMirrorIdx mask i).toNat tag

@[simp]
theorem setCtrlList_mkCtrl4_0 (b0 b1 b2 b3 tag : BitVec 8) :
    setCtrlList 3#64 (mkCtrl4 b0 b1 b2 b3) 0#64 tag = mkCtrl4 tag b1 b2 b3 := rfl

@[simp]
theorem setCtrlList_mkCtrl4_1 (b0 b1 b2 b3 tag : BitVec 8) :
    setCtrlList 3#64 (mkCtrl4 b0 b1 b2 b3) 1#64 tag = mkCtrl4 b0 tag b2 b3 := rfl

@[simp]
theorem setCtrlList_mkCtrl4_2 (b0 b1 b2 b3 tag : BitVec 8) :
    setCtrlList 3#64 (mkCtrl4 b0 b1 b2 b3) 2#64 tag = mkCtrl4 b0 b1 tag b3 := rfl

@[simp]
theorem setCtrlList_mkCtrl4_3 (b0 b1 b2 b3 tag : BitVec 8) :
    setCtrlList 3#64 (mkCtrl4 b0 b1 b2 b3) 3#64 tag = mkCtrl4 b0 b1 b2 tag := rfl

/-! ## Probe Sequence on 4-Bucket Tables (`mask = 3#64`) & Unaligned Group Load Over Mirrored Tail -/

/-- Initial probe position `pos = h1(hash) & bucket_mask`. -/
@[expose] def probePos (hash mask : BitVec 64) : BitVec 64 :=
  hash &&& mask

/-- Bucket index corresponding to matching lane `bit` at probe position `pos`:
`index = (pos + bit) & bucket_mask`. -/
@[expose] def probeBucketIdx (pos : BitVec 64) (bit : Nat) (mask : BitVec 64) : BitVec 64 :=
  (pos + BitVec.ofNat 64 bit) &&& mask

/-- Next triangular probe state (`ProbeSeq::move_next`):
`stride' = stride + Group::WIDTH`, `pos' = (pos + stride') & bucket_mask`. -/
def probeMoveNext (pos stride mask : BitVec 64) : BitVec 64 × BitVec 64 :=
  let stride' := stride + 8#64
  ((pos + stride') &&& mask, stride')

theorem probePos_3_toNat (hash : BitVec 64) : (probePos hash 3#64).toNat = hash.toNat % 4 := by
  unfold probePos
  rw [BitVec.toNat_and]
  change hash.toNat &&& (2 ^ 2 - 1) = hash.toNat % 4
  exact Nat.and_two_pow_sub_one_eq_mod hash.toNat 2

theorem probePos_3_toNat_lt (hash : BitVec 64) : (probePos hash 3#64).toNat < 4 := by
  rw [probePos_3_toNat]
  omega

/-- Unaligned 8-byte group load (`Group::load(self.ctrl(pos))`) from control byte list `cbs`
starting at byte offset `pos`. -/
@[expose] def loadGroupAt (cbs : List (BitVec 8)) (pos : Nat) : BitVec 64 :=
  packGroupWord
    (cbs.getD (pos + 0) emptyTag)
    (cbs.getD (pos + 1) emptyTag)
    (cbs.getD (pos + 2) emptyTag)
    (cbs.getD (pos + 3) emptyTag)
    (cbs.getD (pos + 4) emptyTag)
    (cbs.getD (pos + 5) emptyTag)
    (cbs.getD (pos + 6) emptyTag)
    (cbs.getD (pos + 7) emptyTag)

@[simp]
theorem groupByte_loadGroupAt (cbs : List (BitVec 8)) (pos i : Nat) (hi : i < 8) :
    groupByte (loadGroupAt cbs pos) i = cbs.getD (pos + i) emptyTag := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [loadGroupAt]

@[simp]
theorem loadGroupAt_mkCtrl4_0 (b0 b1 b2 b3 : BitVec 8) :
    loadGroupAt (mkCtrl4 b0 b1 b2 b3) 0 =
      packGroupWord b0 b1 b2 b3 emptyTag emptyTag emptyTag emptyTag := rfl

@[simp]
theorem loadGroupAt_mkCtrl4_1 (b0 b1 b2 b3 : BitVec 8) :
    loadGroupAt (mkCtrl4 b0 b1 b2 b3) 1 =
      packGroupWord b1 b2 b3 emptyTag emptyTag emptyTag emptyTag b0 := rfl

@[simp]
theorem loadGroupAt_mkCtrl4_2 (b0 b1 b2 b3 : BitVec 8) :
    loadGroupAt (mkCtrl4 b0 b1 b2 b3) 2 =
      packGroupWord b2 b3 emptyTag emptyTag emptyTag emptyTag b0 b1 := rfl

@[simp]
theorem loadGroupAt_mkCtrl4_3 (b0 b1 b2 b3 : BitVec 8) :
    loadGroupAt (mkCtrl4 b0 b1 b2 b3) 3 =
      packGroupWord b3 emptyTag emptyTag emptyTag emptyTag b0 b1 b2 := rfl

@[simp]
theorem loadGroupAt_emptyCtrl4 (pos : Nat) (hpos : pos < 4) :
    loadGroupAt emptyCtrl4 pos = emptyGroupWord := by
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The lane index (`0 ≤ bit < 8`) at which bucket `k < 4` appears in the unaligned group load at
`pos < 4` on a 4-bucket table:
- if `pos ≤ k`, bucket `k` is in the primary prefix at lane `k - pos`;
- if `k < pos`, bucket `k` is in the mirrored tail at lane `k + 8 - pos`. -/
@[expose] def laneOfBucket4 (pos k : Nat) : Nat :=
  if pos ≤ k then k - pos else k + 8 - pos

theorem laneOfBucket4_lt_8 (pos k : Nat) (hpos : pos < 4) (hk : k < 4) :
    laneOfBucket4 pos k < 8 := by
  unfold laneOfBucket4
  split <;> omega

/-- Every bucket `k < 4` of `mkCtrl4 b0 b1 b2 b3` appears at lane `laneOfBucket4 pos k < 8` of the
single unaligned 8-byte group load at `pos < 4`, with `(pos + bit) & 3 = k`. -/
theorem probe4_reaches_every_bucket (b0 b1 b2 b3 : BitVec 8) (pos k : Nat)
    (hpos : pos < 4) (hk : k < 4) :
    groupByte (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) (laneOfBucket4 pos k) =
      (mkCtrl4 b0 b1 b2 b3).getD k emptyTag ∧
    (pos + laneOfBucket4 pos k) % 4 = k ∧
    probeBucketIdx (BitVec.ofNat 64 pos) (laneOfBucket4 pos k) 3#64 = BitVec.ofNat 64 k := by
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  refine ⟨by simp [laneOfBucket4, mkCtrl4], rfl, rfl⟩

/-- Lane `4 - pos < 8` of `loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos` (`pos < 4`) is always `emptyTag`
(`0xff#8`), so `match_empty().any_bit_set()` holds on the first group load. -/
theorem groupByte_loadGroupAt_mkCtrl4_padding_empty (b0 b1 b2 b3 : BitVec 8) (pos : Nat)
    (hpos : pos < 4) :
    groupByte (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) (4 - pos) = emptyTag := by
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  simp [mkCtrl4]

@[simp]
theorem anyBitSet_neonMatchEmpty_loadGroupAt_mkCtrl4 (b0 b1 b2 b3 : BitVec 8) (pos : Nat)
    (hpos : pos < 4) :
    anyBitSet (neonMatchEmpty (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos)) = true := by
  rw [anyBitSet_neonMatchEmpty_eq_umaxv]
  exact neonUmaxv8_neonMatchEmpty_getLsbD_zero_of_exists
    (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) (4 - pos) (by omega)
    (groupByte_loadGroupAt_mkCtrl4_padding_empty b0 b1 b2 b3 pos hpos)

@[simp]
theorem neonUmaxv8_neonMatchEmpty_loadGroupAt_mkCtrl4 (b0 b1 b2 b3 : BitVec 8) (pos : Nat)
    (hpos : pos < 4) :
    (neonUmaxv8 (neonMatchEmpty (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos))).getLsbD 0 = true := by
  rw [← anyBitSet_neonMatchEmpty_eq_umaxv]
  exact anyBitSet_neonMatchEmpty_loadGroupAt_mkCtrl4 b0 b1 b2 b3 pos hpos

/-! ## Additional `set_ctrl` Mirror Index & Two-Entry Table Lemmas -/

/-- The 12-byte control array of a 4-bucket table with two entries at buckets `k1, k2 < 4`
(where `k2` takes precedence if `k1 = k2`). -/
@[expose] def doubleCtrl4 (k1 : Nat) (tag1 : BitVec 8) (k2 : Nat) (tag2 : BitVec 8) : List (BitVec 8) :=
  mkCtrl4
    (if k2 = 0 then tag2 else if k1 = 0 then tag1 else emptyTag)
    (if k2 = 1 then tag2 else if k1 = 1 then tag1 else emptyTag)
    (if k2 = 2 then tag2 else if k1 = 2 then tag1 else emptyTag)
    (if k2 = 3 then tag2 else if k1 = 3 then tag1 else emptyTag)

theorem ctrlMirrorInv_doubleCtrl4 (k1 : Nat) (tag1 : BitVec 8) (k2 : Nat) (tag2 : BitVec 8) :
    CtrlMirrorInv 3#64 (doubleCtrl4 k1 tag1 k2 tag2) :=
  ctrlMirrorInv_mkCtrl4 _ _ _ _

@[simp]
theorem doubleCtrl4_same (k : Nat) (hk : k < 4) (tag1 tag2 : BitVec 8) :
    doubleCtrl4 k tag1 k tag2 = singleCtrl4 k tag2 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- On a 4-bucket table (`mask = 3#64`), for any `idx < 4`,
`((BitVec.ofNat 64 idx - 8#64) &&& 3#64) = BitVec.ofNat 64 idx`. -/
@[simp]
theorem sub_eight_and_three_ofNat (idx : Nat) (hidx : idx < 4) :
    (BitVec.ofNat 64 idx - 8#64) &&& 3#64 = BitVec.ofNat 64 idx := by
  rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3) with rfl | rfl | rfl | rfl <;> rfl

/-! ## Group Match Masks on `emptyCtrl4` and `singleCtrl4` -/

/-- On `emptyCtrl4`, `neonMatchTag (loadGroupAt emptyCtrl4 pos) qtag` is `0#64` for any full tag
`qtag` (`qtag.msb = false`, hence `qtag ≠ 0xff#8`). -/
theorem neonMatchTag_loadGroupAt_emptyCtrl4 (pos : Nat) (hpos : pos < 4)
    (qtag : BitVec 8) (hq : qtag.msb = false) :
    neonMatchTag (loadGroupAt emptyCtrl4 pos) qtag = 0#64 := by
  rw [loadGroupAt_emptyCtrl4 pos hpos]
  have hne : emptyTag ≠ qtag := by
    intro h
    have := congrArg BitVec.msb h
    rw [emptyTag_msb, hq] at this
    cases this
  have hbeq : (emptyTag == qtag) = false := beq_false_of_ne hne
  simp [neonMatchTag, emptyGroupWord, hbeq, packGroupWord]

@[simp]
theorem neonMatchTag_loadGroupAt_emptyCtrl4_and_bitmaskIterMask (pos : Nat) (hpos : pos < 4)
    (qtag : BitVec 8) (hq : qtag.msb = false) :
    neonMatchTag (loadGroupAt emptyCtrl4 pos) qtag &&& bitmaskIterMask = 0#64 := by
  rw [neonMatchTag_loadGroupAt_emptyCtrl4 pos hpos qtag hq]
  rfl

@[simp]
theorem neonMatchEmpty_loadGroupAt_emptyCtrl4 (pos : Nat) (hpos : pos < 4) :
    neonMatchEmpty (loadGroupAt emptyCtrl4 pos) = 0xffffffffffffffff#64 := by
  rw [loadGroupAt_emptyCtrl4 pos hpos, neonMatchEmpty_emptyGroupWord]

@[simp]
theorem neonMatchEmptyOrDeleted_loadGroupAt_emptyCtrl4 (pos : Nat) (hpos : pos < 4) :
    neonMatchEmptyOrDeleted (loadGroupAt emptyCtrl4 pos) = 0xffffffffffffffff#64 := by
  rw [loadGroupAt_emptyCtrl4 pos hpos, neonMatchEmptyOrDeleted_emptyGroupWord]

@[simp]
theorem neonMatchFull_loadGroupAt_emptyCtrl4 (pos : Nat) (hpos : pos < 4) :
    neonMatchFull (loadGroupAt emptyCtrl4 pos) = 0#64 := by
  rw [loadGroupAt_emptyCtrl4 pos hpos, neonMatchFull_emptyGroupWord]

@[simp]
theorem singleCtrl4_0 (tag : BitVec 8) :
    singleCtrl4 0 tag = mkCtrl4 tag emptyTag emptyTag emptyTag := rfl

@[simp]
theorem singleCtrl4_1 (tag : BitVec 8) :
    singleCtrl4 1 tag = mkCtrl4 emptyTag tag emptyTag emptyTag := rfl

@[simp]
theorem singleCtrl4_2 (tag : BitVec 8) :
    singleCtrl4 2 tag = mkCtrl4 emptyTag emptyTag tag emptyTag := rfl

@[simp]
theorem singleCtrl4_3 (tag : BitVec 8) :
    singleCtrl4 3 tag = mkCtrl4 emptyTag emptyTag emptyTag tag := rfl

/-- On `singleCtrl4 k tag` (`k < 4`, `pos < 4`), for any full query tag `qtag` (`qtag.msb = false`):
- the only lane in `loadGroupAt (singleCtrl4 k tag) pos` that can equal `qtag` is
  `laneOfBucket4 pos k` (since all other 7 lanes are `emptyTag = 0xff#8`, which has `msb = true`);
- therefore `neonMatchTag (loadGroupAt (singleCtrl4 k tag) pos) qtag` equals
  `if tag == qtag then laneFullMask (laneOfBucket4 pos k) else 0#64`. -/
theorem neonMatchTag_loadGroupAt_singleCtrl4 (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (tag qtag : BitVec 8) (hq : qtag.msb = false) :
    neonMatchTag (loadGroupAt (singleCtrl4 k tag) pos) qtag =
      if tag == qtag then laneFullMask (laneOfBucket4 pos k) else 0#64 := by
  have hne : emptyTag ≠ qtag := by
    intro h
    have := congrArg BitVec.msb h
    rw [emptyTag_msb, hq] at this
    cases this
  have hbeq : (emptyTag == qtag) = false := beq_false_of_ne hne
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [singleCtrl4_0, singleCtrl4_1, singleCtrl4_2, singleCtrl4_3,
               loadGroupAt_mkCtrl4_0, loadGroupAt_mkCtrl4_1,
               loadGroupAt_mkCtrl4_2, loadGroupAt_mkCtrl4_3,
               neonMatchTag, groupByte_packGroupWord_0, groupByte_packGroupWord_1,
               groupByte_packGroupWord_2, groupByte_packGroupWord_3,
               groupByte_packGroupWord_4, groupByte_packGroupWord_5,
               groupByte_packGroupWord_6, groupByte_packGroupWord_7, hbeq]
    cases (tag == qtag) <;> rfl

/-- On `singleCtrl4 k tag` (`k < 4`, `pos < 4`), the `BitMask` iteration mask
`neonMatchTag (loadGroupAt (singleCtrl4 k tag) pos) qtag &&& bitmaskIterMask` for a full query tag
`qtag` (`qtag.msb = false`) is `laneBit (laneOfBucket4 pos k)` if `tag == qtag` and `0#64` otherwise. -/
theorem neonMatchTag_loadGroupAt_singleCtrl4_and_bitmaskIterMask
    (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (tag qtag : BitVec 8) (hq : qtag.msb = false) :
    neonMatchTag (loadGroupAt (singleCtrl4 k tag) pos) qtag &&& bitmaskIterMask =
      if tag == qtag then laneBit (laneOfBucket4 pos k) else 0#64 := by
  rw [neonMatchTag_loadGroupAt_singleCtrl4 k pos hk hpos tag qtag hq]
  have hlt : laneOfBucket4 pos k < 8 := laneOfBucket4_lt_8 pos k hpos hk
  cases (tag == qtag)
  · simp
  · simp [laneFullMask_and_bitmaskIterMask (laneOfBucket4 pos k) hlt]

end CryptoVerification.E2E.InMem.HashbrownModel

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.ChainKeyEpilogue
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Tag-3 Field Leaf (`chainKeyFieldG_ok`) for General `message::merge<Chain>`

Proves `chainKeyFieldG_ok` (`+0x120 → +0x120`, `k → k + 1`) for nested `ChainKey` messages (tag `3`,
with optional varint `index` tag `1` and 32-byte `key` tag `2` written into `Option<ChainKey>` at
`a + 0x48`).
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## Pure `ChainG`, `ChainField.ck`, and Cursor Helpers -/

theorem chainG_enc_eq_fields_local (c : ChainG) : c.enc = c.fields.flatMap ChainField.enc := by
  unfold ChainG.enc ChainG.fields
  have h4 : (c.keys.map ChainField.key).flatMap ChainField.enc =
      (c.keys.map fun m => lenField 4 (encMessageKey m)).flatten := by
    induction c.keys with
    | nil => rfl
    | cons m ms ih => simp [ChainField.enc, ih]
  simp only [List.flatMap_append, h4, List.append_assoc]
  by_cases hsrk : c.srk = [] <;> by_cases hpriv : c.priv = [] <;>
    rcases hck : c.ck with _ | ⟨i, k⟩ <;>
    simp [hsrk, hpriv, bytesField, msgField, ChainField.enc]

private theorem map_key_getElem_tag_ne_three (keys : List MessageKeyGenerator) (j : Nat)
    (hj : j < (keys.map ChainField.key).length) :
    ((keys.map ChainField.key)[j]'hj).tag ≠ 3 := by
  simp [ChainField.tag]

theorem chainField_tag_three_info (c : ChainG) (k : Nat)
    (hk : k < c.fields.length) (htag : (c.fields[k]'hk).tag = 3) :
    (∃ i key, c.ck = some (i, key) ∧ c.fields[k]'hk = ChainField.ck i key) ∧
    (chainGAfter c k).ck = none := by
  rcases c with ⟨srk, priv, _ | ⟨i, key⟩, keys⟩ <;>
    unfold chainGAfter <;>
    unfold ChainG.fields at hk htag ⊢ <;>
    by_cases hsrk : srk = [] <;> by_cases hpriv : priv = [] <;>
    simp only [hsrk, hpriv, ↓reduceIte, List.nil_append, List.cons_append] at hk htag ⊢
  · exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | k
    · simp [ChainField.tag] at htag
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | k
    · simp [ChainField.tag] at htag
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | _ | k
    · simp [ChainField.tag] at htag
    · simp [ChainField.tag] at htag
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | k
    · exact ⟨⟨i, key, rfl, rfl⟩, rfl⟩
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | _ | k
    · simp [ChainField.tag] at htag
    · exact ⟨⟨i, key, rfl, rfl⟩, rfl⟩
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | _ | k
    · simp [ChainField.tag] at htag
    · exact ⟨⟨i, key, rfl, rfl⟩, rfl⟩
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim
  · rcases k with _ | _ | _ | k
    · simp [ChainField.tag] at htag
    · simp [ChainField.tag] at htag
    · exact ⟨⟨i, key, rfl, rfl⟩, rfl⟩
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact (map_key_getElem_tag_ne_three keys k hk htag).elim

theorem chainGAfter_succ (c : ChainG) (k : Nat) (hk : k < c.fields.length) :
    chainGAfter c (k + 1) = (chainGAfter c k).apply (c.fields[k]'hk) := by
  unfold chainGAfter
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem uint32Field_one_eq_pbVarint (i : BitVec 32) :
    uint32Field 1 i = pbVarint 1 i.toNat := by
  unfold uint32Field pbVarint
  by_cases hi : i = 0
  · subst hi; rfl
  · have hi_nat : i.toNat ≠ 0 := by
      intro h; apply hi; apply BitVec.eq_of_toNat_eq; simpa using h
    simp only [hi, hi_nat, ↓reduceIte]
    have hkey : encodeKey 1 .varint = pbKey 1 0 := rfl
    have hbody : encodeVarint (i.setWidth 64) = pbVarintBody 5 i.toNat :=
      (pbVarintBody_u32_eq_encodeVarint_seedChain i).symm
    rw [hkey, hbody]

theorem bytesField_two_eq_pbBytes {key : List (BitVec 8)} (hkey : key.length = 32) :
    bytesField 2 key = pbBytes 2 key := by
  have hne : key ≠ [] := by intro h; subst h; simp at hkey
  have hlt : key.length < 128 := by omega
  unfold bytesField lenField pbBytes pbKey encodeKey WireType.toNat
  simp only [hne, ↓reduceIte]
  rw [encodeVarint_lt128_seedChain key.length hlt]
  rfl

theorem chainField_ck_enc_eq (i : BitVec 32) {key : List (BitVec 8)} (hkey : key.length = 32) :
    let ck_body := pbVarint 1 i.toNat ++ pbBytes 2 key
    (ChainField.ck i key).enc =
      [0x1a#8, BitVec.ofNat 8 ck_body.length] ++ (pbVarint 1 i.toNat ++ pbBytes 2 key) := by
  intro ck_body
  have hck_bounds := ckEnc_length_bounds_seedChain i hkey
  have hck_lt : ck_body.length < 128 := by dsimp [ck_body]; omega
  dsimp only [ChainField.enc]
  rw [uint32Field_one_eq_pbVarint i, bytesField_two_eq_pbBytes hkey]
  change lenField 3 ck_body = [0x1a#8, BitVec.ofNat 8 ck_body.length] ++ ck_body
  unfold lenField encodeKey WireType.toNat
  rw [encodeVarint_lt128_seedChain ck_body.length hck_lt]
  rfl

theorem prostChainGAt_ck_none_eq (a : BitVec 64) (c0 : ChainG) (hck : c0.ck = none) :
    prostChainGAt A0 a c0 =
      vecU8 A0 a c0.srk ∗ vecU8 A0 (a + 0x18#64) c0.priv ∗
      vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (a + 0x30#64) c0.keys ∗
      ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 := by
  unfold prostChainGAt
  rw [hck]

theorem prostChainGAt_apply_ck_eq (a : BitVec 64) (c0 : ChainG) (i : BitVec 32) (key : List (BitVec 8)) :
    prostChainGAt A0 a (c0.apply (ChainField.ck i key)) =
      vecU8 A0 a c0.srk ∗ vecU8 A0 (a + 0x18#64) c0.priv ∗
      vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (a + 0x30#64) c0.keys ∗
      vecU8 A0 (a + 0x48#64) key ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4 := by
  unfold prostChainGAt ChainG.apply
  rfl

/-- Prefix of `c.payload ++ tail` consumed before field `k`. -/
@[expose] def pfx_k (c : ChainG) (k : Nat) : List (BitVec 8) :=
  encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.fields.take k).flatMap ChainField.enc

/-- Suffix of `c.payload ++ tail` remaining from field `k` onward. -/
@[expose] def rem_k (c : ChainG) (k : Nat) (tail : List (BitVec 8)) : List (BitVec 8) :=
  ((c.fields.drop k).flatMap ChainField.enc) ++ tail

theorem payload_append_eq_pfx_rem (c : ChainG) (k : Nat) (tail : List (BitVec 8)) :
    c.payload ++ tail = pfx_k c k ++ rem_k c k tail := by
  unfold ChainG.payload pfx_k rem_k
  rw [chainG_enc_eq_fields_local c]
  have htd : c.fields.flatMap ChainField.enc =
      (c.fields.take k).flatMap ChainField.enc ++ (c.fields.drop k).flatMap ChainField.enc := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [htd]
  simp only [List.append_assoc]

theorem rem_k_eq_cons (c : ChainG) (k : Nat) (tail : List (BitVec 8)) (hk : k < c.fields.length) :
    rem_k c k tail = (c.fields[k]'hk).enc ++ rem_k c (k + 1) tail := by
  unfold rem_k
  rw [List.drop_eq_getElem_cons hk, List.flatMap_cons, List.append_assoc]

theorem pfx_k_succ (c : ChainG) (k : Nat) (hk : k < c.fields.length) :
    pfx_k c (k + 1) = pfx_k c k ++ (c.fields[k]'hk).enc := by
  unfold pfx_k
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem combine_tag3_cursor (slot ptr : BitVec 64)
    (pfx b3a b3b b3c afterCk : List (BitVec 8))
    (hb3a_len : b3a.length = 2) :
    let ptr3a := ptr + BitVec.ofNat 64 pfx.length
    let ptr3b := ptr3a + 2#64
    let ptr3c := ptr3b + BitVec.ofNat 64 b3b.length
    let ptrEnd := ptr3c + BitVec.ofNat 64 b3c.length
    (ptr ↦ₛ pfx) ∗
      (ptr3a ↦ₛ b3a) ∗
      (ptr3b ↦ₛ b3b) ∗
      (ptr3c ↦ₛ b3c) ∗
      sliceCursorAt slot ptrEnd afterCk =
    sliceCursorAfter slot ptr
      ((pfx ++ (b3a ++ (b3b ++ b3c))) ++ afterCk) afterCk := by
  intro ptr3a ptr3b ptr3c ptrEnd
  rw [sliceCursorAfter_append_eq_seedChain slot ptr (pfx ++ (b3a ++ (b3b ++ b3c))) afterCk]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  have hp3a : ptr + BitVec.ofNat 64 pfx.length = ptr3a := rfl
  have hp3b : ptr3a + BitVec.ofNat 64 b3a.length = ptr3b := by dsimp [ptr3b]; rw [hb3a_len]
  have hp3c : ptr3b + BitVec.ofNat 64 b3b.length = ptr3c := rfl
  have hpEnd : ptr + BitVec.ofNat 64 (pfx ++ (b3a ++ (b3b ++ b3c))).length = ptrEnd := by
    dsimp [ptrEnd, ptr3c, ptr3b, ptr3a]
    simp only [List.length_append, hb3a_len]
    bv_omega
  rw [hp3a, hp3b, hp3c, hpEnd]
  ac_rfl

theorem sp0_aligned_of_sub_256_aligned {sp0 : BitVec 64} (h : (sp0 - 256#64) &&& 15#64 = 0#64) :
    sp0 &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

/-! ## Segment Steps for Tag 3 (`+0x120 → +0x4c8 → +0x120`) -/

/-- Reg bundle preserved across the inner `ChainKey` loop (`+0x4c8`). -/
@[expose] def InnerLoopRegs (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat) (s : State) : Prop :=
  s.sp = sp0 - 256#64 ∧
  s.readReg64 .x29 = sp0 - 0x60#64 ∧
  s.readReg64 .x19 = bufRef ∧
  s.readReg64 .x20 = a ∧
  s.readReg64 .x21 = 98#64 ∧
  s.readReg64 .x22 = 97#64 ∧
  s.readReg64 .x23 = BitVec.ofNat 64 innerTailLen ∧
  s.readReg64 .x24 = BitVec.ofNat 64 outerTailLen ∧
  s.readReg64 .x25 = sp0 - 0xf8#64 ∧
  s.readReg64 .x26 = 1#64

theorem InnerLoopRegs.of_calleeSaved {sp0 bufRef a : BitVec 64} {outerTailLen innerTailLen : Nat}
    {s1 s2 : State} (h1 : InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s1)
    (hsp2 : s2.sp = sp0 - 256#64) (hcs : CalleeSavedPreserved s1 s2) :
    InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s2 :=
  ⟨hsp2,
   hcs.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.1,
   hcs.1.trans h1.2.2.1,
   hcs.2.1.trans h1.2.2.2.1,
   hcs.2.2.1.trans h1.2.2.2.2.1,
   hcs.2.2.2.1.trans h1.2.2.2.2.2.1,
   hcs.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2⟩

/-- Dummy seed ghost to reuse `step_chainMerge_int32Merge_seedChain` / `step_chainMerge_bytesMerge_seedChain`,
since `chainMergeSeedSpec.onPanic` and `chainMergeGenSpec.onPanic` are both `Serialization.allocPanic`. -/
@[expose] def dummySeedGhost : ChainMergeGhost :=
  ⟨0#64, ⟨[], [], none⟩, 0#64, 0#64, 0#64, [], []⟩

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG

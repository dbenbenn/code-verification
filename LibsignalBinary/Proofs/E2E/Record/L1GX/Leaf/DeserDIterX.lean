/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.BodyDefs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.LoopIter -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.L1GX.Fields
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Loop-iteration leaf `deserLoopIterG_ok` in PQXDH scope

Proves one iteration of the `SessionRecord::deserialize` field-dispatch loop over `recFieldsX`:
tag/wire-type key decoding and `SessionStructure::merge_field` invocation.
-/

public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.DeserDIterX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)
open CryptoVerification.E2E.Record.DeserializeSeed.LoopIterStateSimp
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.E2E.RecordX (DeserializeScopeP)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero ofNat_succ_sub_one_loopIter

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_pre_diterX (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_pre_diterX (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre_diterX (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre_diterX (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre_diterX (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre_diterX (s : State) (pc : BitVec 64) (m : Memory) (r :
    Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre_diterX (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre_diterX (s : State) (pc : BitVec 64) (m : Memory) (r :
    Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre_diterX (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre_diterX (s : State) (pc : BitVec 64) (m : Memory) (w :
    RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

/-! ## Field key-byte and prefix-fold lemmas -/

@[expose] def keyByte_diterX (fl : GenFieldX) : BitVec 8 :=
  BitVec.ofNat 8 (fl.tag * 8 + if fl.wt = .varint then 0 else 2)

theorem enc_eq_keyByte_cons_diterX (fl : GenFieldX) :
    fl.enc = keyByte_diterX fl :: fl.payload := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> rfl

theorem drop_flatMap_enc_diterX {r : SessionRecord (List (BitVec 8))} {k : Nat}
    (hk : k < (recFieldsX r).length) :
    ((recFieldsX r).drop k).flatMap GenFieldX.enc =
      (recFieldsX r)[k].enc ++ ((recFieldsX r).drop (k + 1)).flatMap GenFieldX.enc := by
  rw [List.drop_eq_getElem_cons hk, List.flatMap_cons]

theorem ssgAfter_succ_diterX {r : SessionRecord (List (BitVec 8))} {k : Nat}
    (hk : k < (recFieldsX r).length) :
    ssgxAfter r (k + 1) = (ssgxAfter r k).apply (recFieldsX r)[k] := by
  simp only [ssgxAfter, List.take_succ_eq_append_getElem hk, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-! ## Slice-cursor and remaining-length lemmas -/

def preBytes_diterX (r : SessionRecord (List (BitVec 8))) (k : Nat) : List (BitVec 8) :=
  encodeKey 1 .lengthDelimited ++
    encodeVarint (BitVec.ofNat 64 ((recFieldsX r).flatMap GenFieldX.enc).length) ++
    ((recFieldsX r).take k).flatMap GenFieldX.enc

def curPtr_diterX (p : BitVec 64) (r : SessionRecord (List (BitVec 8))) (k : Nat) : BitVec 64 :=
  p + BitVec.ofNat 64 (preBytes_diterX r k).length

theorem encodeRecord_eq_preBytes_append_diterX {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP r) (k : Nat) :
    encodeRecord r = preBytes_diterX r k ++ ((recFieldsX r).drop k).flatMap GenFieldX.enc := by
  have hs : (recFieldsX r).flatMap GenFieldX.enc =
      ((recFieldsX r).take k).flatMap GenFieldX.enc ++
        ((recFieldsX r).drop k).flatMap GenFieldX.enc := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [encodeRecord_eq_recFieldsX r hr, preBytes_diterX, List.append_assoc, List.append_assoc, ← hs,
    ← List.append_assoc]

theorem rem_length_lt_diterX {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP r) (k :
    Nat) :
    (((recFieldsX r).drop k).flatMap GenFieldX.enc).length < 2 ^ 20 := by
  have h1 := encodeRecord_length_ltX hr
  rw [encodeRecord_eq_preBytes_append_diterX hr k, List.length_append] at h1
  omega

theorem payload_rest_length_lt_diterX {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP
    r)
    {k : Nat} (hk : k < (recFieldsX r).length) :
    ((recFieldsX r)[k].payload ++ ((recFieldsX r).drop (k + 1)).flatMap GenFieldX.enc).length <
      2 ^ 20 := by
  have h := rem_length_lt_diterX hr k
  rw [drop_flatMap_enc_diterX hk, enc_eq_keyByte_cons_diterX, List.cons_append,
    List.length_cons] at h
  omega

theorem encodeRecord_sub_rem_length_diterX {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP r) (k : Nat) :
    (encodeRecord r).length - (((recFieldsX r).drop k).flatMap GenFieldX.enc).length =
      (preBytes_diterX r k).length := by
  rw [encodeRecord_eq_preBytes_append_diterX hr k, List.length_append]
  omega

theorem sliceCursorAfter_split_key_diterX (L p : BitVec 64) {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP r) {k : Nat} (hk : k < (recFieldsX r).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r)
      (((recFieldsX r).drop k).flatMap GenFieldX.enc) =
      ((L + 0x3f8#64) ↦₆₄ curPtr_diterX p r k) ∗
        ((L + 0x400#64) ↦₆₄ BitVec.ofNat 64
          (((recFieldsX r)[k].payload ++
            ((recFieldsX r).drop (k + 1)).flatMap GenFieldX.enc).length + 1)) ∗
        (curPtr_diterX p r k ↦₈ keyByte_diterX (recFieldsX r)[k]) ∗
        ((curPtr_diterX p r k + 1#64) ↦ₛ
          ((recFieldsX r)[k].payload ++ ((recFieldsX r).drop (k + 1)).flatMap GenFieldX.enc)) ∗
        (p ↦ₛ preBytes_diterX r k) := by
  unfold Prost.sliceCursorAfter
  have hsub := encodeRecord_sub_rem_length_diterX hr k
  have hrem : ((recFieldsX r).drop k).flatMap GenFieldX.enc =
      keyByte_diterX (recFieldsX r)[k] ::
        ((recFieldsX r)[k].payload ++ ((recFieldsX r).drop (k + 1)).flatMap GenFieldX.enc) := by
    rw [drop_flatMap_enc_diterX hk, enc_eq_keyByte_cons_diterX, List.cons_append]
  have hbs_split : (p ↦ₛ encodeRecord r) =
      (p ↦ₛ preBytes_diterX r k) ∗
        (curPtr_diterX p r k ↦₈ keyByte_diterX (recFieldsX r)[k]) ∗
        ((curPtr_diterX p r k + 1#64) ↦ₛ
          ((recFieldsX r)[k].payload ++ ((recFieldsX r).drop (k + 1)).flatMap GenFieldX.enc)) := by
    conv_lhs => rw [encodeRecord_eq_preBytes_append_diterX hr k, hrem]
    rw [pointsToBytes_append, ← curPtr_diterX, pointsToBytes_cons]
  have ha : L + 0x3f8#64 + 8#64 = L + 0x400#64 := by bv_omega
  rw [hsub, ← curPtr_diterX, ha, hbs_split, hrem, List.length_cons]
  ac_rfl

theorem sliceCursorAfter_unsplit_key_diterX (L p : BitVec 64) {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP r) {k : Nat} (hk : k < (recFieldsX r).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr_diterX p r k + 1#64)
      ((recFieldsX r)[k].payload ++ ((recFieldsX r).drop (k + 1)).flatMap GenFieldX.enc)
      (((recFieldsX r).drop (k + 1)).flatMap GenFieldX.enc) ∗
      (curPtr_diterX p r k ↦₈ keyByte_diterX (recFieldsX r)[k]) ∗
      (p ↦ₛ preBytes_diterX r k) =
    Prost.sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r)
      (((recFieldsX r).drop (k + 1)).flatMap GenFieldX.enc) := by
  let fl := (recFieldsX r)[k]
  let rest := ((recFieldsX r).drop (k + 1)).flatMap GenFieldX.enc
  have hrem : ((recFieldsX r).drop k).flatMap GenFieldX.enc =
      keyByte_diterX fl :: (fl.payload ++ rest) := by
    rw [drop_flatMap_enc_diterX hk, enc_eq_keyByte_cons_diterX, List.cons_append]
  have hbs_eq : encodeRecord r =
      preBytes_diterX r k ++ (keyByte_diterX fl :: (fl.payload ++ rest)) := by
    rw [encodeRecord_eq_preBytes_append_diterX hr k, hrem]
  have hpay_sub : (fl.payload ++ rest).length - rest.length = fl.payload.length := by
    rw [List.length_append]; omega
  have hbs_sub : (encodeRecord r).length - rest.length =
      (preBytes_diterX r k).length + 1 + fl.payload.length := by
    rw [hbs_eq, List.length_append, List.length_cons, List.length_append]; omega
  have hptr : curPtr_diterX p r k + 1#64 +
      BitVec.ofNat 64 ((fl.payload ++ rest).length - rest.length) =
      p + BitVec.ofNat 64 ((encodeRecord r).length - rest.length) := by
    rw [hpay_sub, hbs_sub, curPtr_diterX]
    have hadd : BitVec.ofNat 64 ((preBytes_diterX r k).length + 1 + fl.payload.length) =
        BitVec.ofNat 64 (preBytes_diterX r k).length + 1#64 +
          BitVec.ofNat 64 fl.payload.length := by
      rw [BitVec.ofNat_add, BitVec.ofNat_add]
    rw [hadd]
    bv_omega
  have hbs_pts : (p ↦ₛ encodeRecord r) =
      (p ↦ₛ preBytes_diterX r k) ∗
        (curPtr_diterX p r k ↦₈ keyByte_diterX fl) ∗
        ((curPtr_diterX p r k + 1#64) ↦ₛ (fl.payload ++ rest)) := by
    conv_lhs => rw [hbs_eq]
    rw [pointsToBytes_append, ← curPtr_diterX, pointsToBytes_cons]
  unfold Prost.sliceCursorAfter
  rw [hptr, hbs_pts]
  ac_rfl

theorem deserLocalsX_decomp_diterX (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSGX) :
    deserLocalsX L p bs rest v =
      Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
      prostSSGXAt A0 (L + 0x420#64) v ∗
      ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      deserFixed_loopIter L := by
  unfold deserLocalsX deserFixed_loopIter
  generalize memRegion L 0x3f8 = m1
  generalize memRegion (L + 0x578#64) 0x170 = m2
  generalize memRegion (L + 0x6f0#64) 0x20 = m3
  ac_rfl

theorem ule_zero_ofNat_succ_diterX {n : Nat} (hn : n < 2 ^ 20) :
    (BitVec.ofNat 64 (n + 1)).ule 0#64 = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_zero,
    Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64)]
  omega

@[local arm64_norm]
theorem keyByte_signExtend_lsb63_diterX (fl : GenFieldX) :
    (BitVec.signExtend 64 (keyByte_diterX fl)).getLsbD 63 = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterX,
      GenFieldX.tag, GenFieldX.wt, GenField.tag, GenField.wt]

@[local arm64_norm]
theorem keyByte_signExtend_lsr32_diterX (fl : GenFieldX) :
    (BitVec.signExtend 64 (keyByte_diterX fl)) >>> 32 = 0#64 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterX,
      GenFieldX.tag, GenFieldX.wt, GenField.tag, GenField.wt]

@[local arm64_norm]
theorem keyByte_signExtend_and7_ule6_diterX (fl : GenFieldX) :
    (6#64).ule (BitVec.signExtend 64 (keyByte_diterX fl) &&& 7#64) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterX,
      GenFieldX.tag, GenFieldX.wt, GenField.tag, GenField.wt]

@[local arm64_norm]
theorem keyByte_signExtend_tag_w1_diterX (fl : GenFieldX) :
    BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (keyByte_diterX fl))) >>>
          3)) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterX,
      GenFieldX.tag, GenFieldX.wt, GenField.tag, GenField.wt]

@[local arm64_norm]
theorem tag_zeroExtend_ofNat32_diterX (fl : GenFieldX) :
    BitVec.zeroExtend 64 (BitVec.ofNat 32 fl.tag) = BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [GenFieldX.tag, GenField.tag]

@[local arm64_norm]
theorem tag_ofNat64_beq0_diterX (fl : GenFieldX) :
    (BitVec.ofNat 64 fl.tag == 0#64) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [GenFieldX.tag, GenField.tag]

@[local arm64_norm]
theorem tag_ofNat64_setWidth32_diterX (fl : GenFieldX) :
    (BitVec.ofNat 64 fl.tag).setWidth 32 = BitVec.ofNat 32 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [GenFieldX.tag, GenField.tag]

end CryptoVerification.E2E.Record.L1GX.Leaf.DeserDIterX

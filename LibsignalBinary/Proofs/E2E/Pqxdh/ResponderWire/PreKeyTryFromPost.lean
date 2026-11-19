/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeser -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp
/-!
# `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`: Post-Loop and Epilogue Helpers
-/

public section namespace CryptoVerification.E2E.Pqxdh.ResponderWire
open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
set_option maxRecDepth 200000
set_option maxHeartbeats 800000
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
  zeroExtend32_lsr4_truncate8
/-! ## 1. `Wire.vecU8Buf` Slice Exposure -/
/-- The allocation/excess-capacity part of `Wire.vecU8Buf A cap ptr bs` without `(ptr ↦ₛ bs)`. -/
@[expose] def vecU8Rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat -
       bs.length))
theorem vecU8Buf_to_slice_rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢ (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs := by
  unfold Wire.vecU8Buf vecU8Rest
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  rw [pure_true_emp ⟨hle, hlt, hptr⟩, emp_sepConj]
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst hbs
    simp [pointsToBytes_nil]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    apply entails_of_eq; ac_rfl
theorem slice_rest_to_vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs ⊢ Wire.vecU8Buf A cap ptr bs := by
  unfold Wire.vecU8Buf vecU8Rest
  rw [sepConj_comm (ptr ↦ₛ bs), sepConj_assoc]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  rw [pure_true_emp ⟨hle, hlt, hptr⟩, emp_sepConj]
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst hbs
    simp [pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    apply entails_of_eq; ac_rfl
/-! ## 2. Segment 1 Helpers -/
theorem deserialize_djb_ok (v : List.Vector (BitVec 8) 32) :
    PublicKey.deserialize (0x05#8 :: v.toList) = .ok ⟨v⟩ := by
  rcases v with ⟨l, hl⟩
  simp [PublicKey.deserialize, djbType, hl, List.take_of_length_le (Nat.le_of_eq hl)]
theorem post_vecU8At_lt (A : RustAlloc) (addr cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A addr cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8At A addr cap ptr bs := by
  rw [vecU8At_eq_header_buf]
  refine Entails.trans (sepConj_mono_right (post_vecU8Buf_lt A cap ptr bs)) ?_
  rw [sepConj_pure_left_comm]
  exact Entails.refl _
theorem post_vecU8At2_lt (A : RustAlloc) (a1 c1 p1 a2 c2 p2 : BitVec 64) (b1 b2 : List (BitVec 8)) :
    vecU8At A a1 c1 p1 b1 ∗ vecU8At A a2 c2 p2 b2 ⊢
      ⌜c1.toNat < 2 ^ 63 ∧ c2.toNat < 2 ^ 63⌝ ∗ vecU8At A a1 c1 p1 b1 ∗ vecU8At A a2 c2 p2 b2 := by
  refine Entails.trans (sepConj_mono (post_vecU8At_lt A a1 c1 p1 b1) (post_vecU8At_lt A a2 c2 p2
    b2)) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun h1 => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun h2 => ?_
  rw [pure_true_emp ⟨h1, h2⟩, emp_sepConj]
  exact Entails.refl _
theorem post_vecU8At4_lt (A : RustAlloc) (a1 c1 p1 a2 c2 p2 a3 c3 p3 a4 c4 p4 : BitVec 64)
    (b1 b2 b3 b4 : List (BitVec 8)) :
    vecU8At A a1 c1 p1 b1 ∗ vecU8At A a2 c2 p2 b2 ∗ vecU8At A a3 c3 p3 b3 ∗ vecU8At A a4 c4 p4 b4 ⊢
      ⌜c1.toNat < 2 ^ 63 ∧ c2.toNat < 2 ^ 63 ∧ c3.toNat < 2 ^ 63 ∧ c4.toNat < 2 ^ 63⌝ ∗
        vecU8At A a1 c1 p1 b1 ∗ vecU8At A a2 c2 p2 b2 ∗
      vecU8At A a3 c3 p3 b3 ∗ vecU8At A a4 c4 p4 b4 := by
  rw [← sepConj_assoc (vecU8At A a1 c1 p1 b1) (vecU8At A a2 c2 p2 b2)]
  refine Entails.trans (sepConj_mono (post_vecU8At2_lt A a1 c1 p1 a2 c2 p2 b1 b2)
    (post_vecU8At2_lt A a3 c3 p3 a4 c4 p4 b3 b4)) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨h1, h2⟩ => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨h3, h4⟩ => ?_
  rw [pure_true_emp ⟨h1, h2, h3, h4⟩, emp_sepConj]
  apply entails_of_eq; ac_rfl
/-- Stack spill layout at `sp' + 16 .. sp' + 112` (96 bytes). -/
@[expose] def seg1SpillsAt (sp' : BitVec 64) (x : PreKeyTryFromArgs) (opkVal : BitVec 32)
    (bkCap bkPtr msgPtr ikPtr : BitVec 64) : SepProp :=
  ((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' +
    28#64) ↦₃₂ x.spkId) ∗
  ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
  ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₆₄ 33#64) ∗
  memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' +
    80#64) ↦₆₄ bkPtr) ∗
  ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr)
theorem memRegion96_seg1_unpack (sp' : BitVec 64) :
    memRegion (sp' + 16#64) 96 ⊢
      ∃∗ w16 : BitVec 32, ∃∗ w20 : BitVec 32, ∃∗ w24 : BitVec 32, ∃∗ w28 : BitVec 32,
      ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 32, ∃∗ w52 : BitVec 32,
      ∃∗ w56 : BitVec 64, ∃∗ w68 : BitVec 32, ∃∗ w72 : BitVec 64, ∃∗ w80 : BitVec 64,
      ∃∗ w88 : BitVec 64, ∃∗ w96 : BitVec 64, ∃∗ w104 : BitVec 64,
        ((sp' + 16#64) ↦₃₂ w16) ∗ ((sp' + 20#64) ↦₃₂ w20) ∗ ((sp' + 24#64) ↦₃₂ w24) ∗ ((sp' +
        28#64) ↦₃₂ w28) ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗ ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' +
        52#64) ↦₃₂ w52) ∗
        ((sp' + 56#64) ↦₆₄ w56) ∗ memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
        ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
        ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) := by
  rw [show (96 : Nat) = 4 + (4 + (4 + (4 + (8 + (8 + (4 + (4 + (8 + (4 + (4 + (8 + (8 + (8 + (8 +
    8)))))))))))))) by decide, memRegion_split (sp' + 16#64) 4 92 (by decide),
    memRegion_split (sp' + 16#64 + 4#64) 4 88 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64) 4 84 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64) 4 80 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64) 8 72 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64) 8 64 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64) 4 60 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64) 4 56 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 48
      (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 +
      8#64) 4 44 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 +
      4#64) 4 40 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 +
      4#64 + 4#64) 8 32 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 +
      4#64 + 4#64 + 8#64) 8 24 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 +
      4#64 + 4#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 +
      4#64 + 4#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight (sp' + 32#64), ProofLib.memRegion_eight (sp' + 40#64),
    ProofLib.memRegion_eight (sp' + 56#64), ProofLib.memRegion_eight (sp' + 72#64),
    ProofLib.memRegion_eight (sp' + 80#64), ProofLib.memRegion_eight (sp' + 88#64),
    ProofLib.memRegion_eight (sp' + 96#64), ProofLib.memRegion_eight (sp' + 104#64)]
  refine Entails.trans (sepConj_mono (memRegion_four_entails (sp' + 16#64))
    (sepConj_mono (memRegion_four_entails (sp' + 20#64))
      (sepConj_mono (memRegion_four_entails (sp' + 24#64))
        (sepConj_mono (memRegion_four_entails (sp' + 28#64)) (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (memRegion_four_entails (sp' + 48#64))
              (sepConj_mono (memRegion_four_entails (sp' + 52#64))
                (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_left (memRegion_four_entails (sp' + 68#64))))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w104 => Entails.sepExists_elim fun w96 =>
    Entails.sepExists_elim fun w88 => Entails.sepExists_elim fun w80 =>
    Entails.sepExists_elim fun w72 => Entails.sepExists_elim fun w68 =>
    Entails.sepExists_elim fun w56 => Entails.sepExists_elim fun w52 =>
    Entails.sepExists_elim fun w48 => Entails.sepExists_elim fun w40 =>
    Entails.sepExists_elim fun w32 => Entails.sepExists_elim fun w28 =>
    Entails.sepExists_elim fun w24 => Entails.sepExists_elim fun w20 =>
    Entails.sepExists_elim fun w16 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w16)
  refine Entails.trans ?_ (Entails.sepExists_intro w20)
  refine Entails.trans ?_ (Entails.sepExists_intro w24)
  refine Entails.trans ?_ (Entails.sepExists_intro w28)
  refine Entails.trans ?_ (Entails.sepExists_intro w32)
  refine Entails.trans ?_ (Entails.sepExists_intro w40)
  refine Entails.trans ?_ (Entails.sepExists_intro w48)
  refine Entails.trans ?_ (Entails.sepExists_intro w52)
  refine Entails.trans ?_ (Entails.sepExists_intro w56)
  refine Entails.trans ?_ (Entails.sepExists_intro w68)
  refine Entails.trans ?_ (Entails.sepExists_intro w72)
  refine Entails.trans ?_ (Entails.sepExists_intro w80)
  refine Entails.trans ?_ (Entails.sepExists_intro w88)
  refine Entails.trans ?_ (Entails.sepExists_intro w96)
  refine Entails.trans ?_ (Entails.sepExists_intro w104)
  exact Entails.refl _
theorem post_headers_entails_memRegion80 (sp' ikCap ikPtr msgCap msgPtr : BitVec 64)
    (msgLen : BitVec 64) (regId opkT opkV spkId kpkId : BitVec 32) :
    vecHeader (sp' + 360#64) ikCap ikPtr 33#64 ∗ vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
    ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ regId) ∗ ((sp' + 416#64) ↦₃₂ opkT) ∗ ((sp' +
      420#64) ↦₃₂ opkV) ∗
    ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ spkId) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' +
      436#64) ↦₃₂ kpkId) ⊢
      memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 := by
  have h1 := vecHeader_entails_memRegion24 (sp' + 360#64) ikCap ikPtr 33#64
  have h2 := vecHeader_entails_memRegion24 (sp' + 384#64) msgCap msgPtr msgLen
  have h3 : ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ regId) ⊢ memRegion (sp' + 408#64) 8 :=
    by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' +
      408#64) 1#32 regId
  have h4 : ((sp' + 416#64) ↦₃₂ opkT) ∗ ((sp' + 420#64) ↦₃₂ opkV) ⊢ memRegion (sp' + 416#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' +
      416#64) opkT opkV
  have h5 : ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ spkId) ⊢ memRegion (sp' + 424#64) 8 :=
    by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' +
      424#64) 1#32 spkId
  have h6 : ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ kpkId) ⊢ memRegion (sp' + 432#64) 8 :=
    by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' +
      432#64) 1#32 kpkId
  rw [show (72 : Nat) = 24 + (24 + (8 + (8 + 8))) by decide,
    memRegion_split (sp' + 360#64) 24 48 (by decide),
    memRegion_split (sp' + 360#64 + 24#64) 24 24 (by decide),
    memRegion_split (sp' + 360#64 + 24#64 + 24#64) 8 16 (by decide),
    memRegion_split (sp' + 360#64 + 24#64 + 24#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Q := memRegion (sp' + 360#64) 24 ∗ memRegion (sp' + 384#64) 24 ∗
      memRegion (sp' + 408#64) 8 ∗ memRegion (sp' + 416#64) 8 ∗ memRegion (sp' + 424#64) 8 ∗
        memRegion (sp' + 432#64) 8) ?_ ?_
  · rw [← sepConj_assoc ((sp' + 408#64) ↦₃₂ 1#32), ← sepConj_assoc ((sp' + 416#64) ↦₃₂ opkT),
        ← sepConj_assoc ((sp' + 424#64) ↦₃₂ 1#32)]
    exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono h5 h6))))
  · apply entails_of_eq; ac_rfl
theorem post_memRegion48_split8 (a : BitVec 64) :
    memRegion a 48 ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 := by
  rw [memRegion_split a 8 40 (by decide), ProofLib.memRegion_eight a]
  rw [sepExists_sepConj_left]
  exact Entails.refl _
theorem post_memRegion48_split33_15 (sp' : BitVec 64) :
    memRegion (sp' + 312#64) 48 = memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 := by
  simpa [BitVec.add_assoc, BitVec.reduceAdd] using memRegion_split (sp' + 312#64) 33 15 (by decide)
/-! ## 3. Segment 2 Helpers -/
@[expose] def spUnused112 (sp' : BitVec 64) : SepProp :=
  memRegion (sp' + 121#64) 7 ∗ memRegion (sp' + 134#64) 2 ∗ memRegion (sp' + 143#64) 1
theorem memRegion32_112_pack (sp' w112 : BitVec 64)
    (w128 : BitVec 32) (w132 : BitVec 16) (b120 c0 c1 c2 c3 c4 c5 c6 : BitVec 8) :
    spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗ ((sp' +
      128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗
      sevenBytesHeadAt (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6 ⊢
      memRegion (sp' + 112#64) 32 := by
  have hs1 := memRegion_split (sp' + 112#64) 8 24 (by decide)
  have hs2 := memRegion_split (sp' + 112#64 + 8#64) 1 23 (by decide)
  have hs3 := memRegion_split (sp' + 112#64 + 8#64 + 1#64) 7 16 (by decide)
  have hs4 := memRegion_split (sp' + 112#64 + 8#64 + 1#64 + 7#64) 4 12 (by decide)
  have hs5 := memRegion_split (sp' + 112#64 + 8#64 + 1#64 + 7#64 + 4#64) 2 10 (by decide)
  have hs6 := memRegion_split (sp' + 112#64 + 8#64 + 1#64 + 7#64 + 4#64 + 2#64) 2 8 (by decide)
  have hs7 := memRegion_split (sp' + 112#64 + 8#64 + 1#64 + 7#64 + 4#64 + 2#64 + 2#64) 7 1
    (by decide)
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [spUnused112]
  refine Entails.trans (Q := ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗
      memRegion (sp' + 121#64) 7 ∗ ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗
        memRegion (sp' + 134#64) 2 ∗
      sevenBytesHeadAt (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6 ∗ memRegion (sp' + 143#64) 1)
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono (pointsTo64_entails_memRegion (sp' + 112#64) w112)
    (sepConj_mono (pointsTo8_entails_memRegion (sp' + 120#64) b120)
      (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion (sp' + 128#64) w128)
        (sepConj_mono (pointsTo16_entails_memRegion (sp' + 132#64) w132)
          (sepConj_mono_right (sepConj_mono_left
            (sevenBytesHeadAt_entails_memRegion7 (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6)))))))
theorem memRegion32_112_unpack (sp' : BitVec 64) :
    memRegion (sp' + 112#64) 32 ⊢
      ∃∗ w112 : BitVec 64, ∃∗ b120 : BitVec 8, ∃∗ w128 : BitVec 32, ∃∗ w132 : BitVec 16,
      ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
      ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8,
        spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗
        ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗ sevenBytesHeadAt (sp' +
        136#64) c0 c1 c2 c3 c4 c5 c6 := by
  have hs1 := memRegion_split (sp' + 112#64) 8 24 (by decide)
  have hs2 := memRegion_split (sp' + 120#64) 1 23 (by decide)
  have hs3 := memRegion_split (sp' + 121#64) 7 16 (by decide)
  have hs4 := memRegion_split (sp' + 128#64) 4 12 (by decide)
  have hs5 := memRegion_split (sp' + 132#64) 2 10 (by decide)
  have hs6 := memRegion_split (sp' + 134#64) 2 8 (by decide)
  have hs7 := memRegion_split (sp' + 136#64) 7 1 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, ProofLib.memRegion_eight (sp' + 112#64)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (post_memRegion_one_entails (sp' + 120#64))
      (sepConj_mono_right (sepConj_mono (memRegion_four_entails (sp' + 128#64))
        (sepConj_mono (post_memRegion_two_entails (sp' + 132#64))
          (sepConj_mono_right (sepConj_mono_left (post_memRegion_seven_entails (sp' +
          136#64))))))))) ?_
  simp only [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w112 => Entails.sepExists_elim fun b120 =>
    Entails.sepExists_elim fun w128 => Entails.sepExists_elim fun w132 =>
    Entails.sepExists_elim fun c0 => Entails.sepExists_elim fun c1 =>
    Entails.sepExists_elim fun c2 => Entails.sepExists_elim fun c3 =>
    Entails.sepExists_elim fun c4 => Entails.sepExists_elim fun c5 =>
    Entails.sepExists_elim fun c6 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w112)
  refine Entails.trans ?_ (Entails.sepExists_intro b120)
  refine Entails.trans ?_ (Entails.sepExists_intro w128)
  refine Entails.trans ?_ (Entails.sepExists_intro w132)
  refine Entails.trans ?_ (Entails.sepExists_intro c0)
  refine Entails.trans ?_ (Entails.sepExists_intro c1)
  refine Entails.trans ?_ (Entails.sepExists_intro c2)
  refine Entails.trans ?_ (Entails.sepExists_intro c3)
  refine Entails.trans ?_ (Entails.sepExists_intro c4)
  refine Entails.trans ?_ (Entails.sepExists_intro c5)
  refine Entails.trans ?_ (Entails.sepExists_intro c6)
  dsimp only [spUnused112]
  apply entails_of_eq; ac_rfl
theorem deser_ok_entails_vecHeader_region (sp' : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    ((sp' + 312#64) ↦₈ 0#8) ∗ sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗ pkRestAt (sp' +
      313#64) b7 b8 w9 w13 w15 w23 b31 ∗ memRegion (sp' + 345#64) 15 ⊢
      ∃∗ w320 : BitVec 64, ∃∗ w328 : BitVec 64,
        ((sp' + 312#64) ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8)) ∗ ((sp' +
        320#64) ↦₆₄ w320) ∗ ((sp' + 328#64) ↦₆₄ w328) ∗ memRegion (sp' + 336#64) 24 := by
  have h1 : ((sp' + 312#64) ↦₈ 0#8) ∗ sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗ memRegion (sp' + 345#64) 15 ⊢
      ((sp' + 312#64) ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8)) ∗ memRegion (sp' +
        320#64) 40 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      deser_ok_entails_spe_region (sp' + 312#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
  refine Entails.trans h1 ?_
  rw [memRegion_split (sp' + 320#64) 8 32 (by decide),
      memRegion_split (sp' + 320#64 + 8#64) 8 24 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight (sp' + 320#64), ProofLib.memRegion_eight (sp' + 328#64),
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w328 => Entails.sepExists_elim fun w320 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w320)
  refine Entails.trans ?_ (Entails.sepExists_intro w328)
  exact Entails.refl _
/-! ## 4. Segment 3 Helpers -/
theorem memRegion32_words4 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗ (∃∗ w2 : BitVec 64,
        (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) := by
  rw [memRegion_split a 8 24 (by decide), memRegion_split (a + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd]
theorem words5_memRegion8_72_entails_120 (sp' w0 w1 w2 w3 w4 : BitVec 64) :
    ((sp' + 312#64) ↦₆₄ w0) ∗ ((sp' + 320#64) ↦₆₄ w1) ∗ ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' +
      336#64) ↦₆₄ w3) ∗
    ((sp' + 344#64) ↦₆₄ w4) ∗ memRegion (sp' + 352#64) 8 ∗ memRegion (sp' +
      360#64) 72 ⊢ memRegion (sp' + 312#64) 120 := by
  have hw5 :
      ((sp' + 312#64) ↦₆₄ w0) ∗ ((sp' + 320#64) ↦₆₄ w1) ∗ ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' +
        336#64) ↦₆₄ w3) ∗
      ((sp' + 344#64) ↦₆₄ w4) ⊢ memRegion (sp' + 312#64) 40 := by
    simpa [words5At, BitVec.add_assoc, BitVec.reduceAdd] using
      words5At_entails_memRegion (sp' + 312#64) w0 w1 w2 w3 w4
  rw [show (120 : Nat) = 40 + (8 + 72) by decide, memRegion_split (sp' + 312#64) 40 80 (by decide),
      memRegion_split (sp' + 312#64 + 40#64) 8 72 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (Q := (((sp' + 312#64) ↦₆₄ w0) ∗ ((sp' + 320#64) ↦₆₄ w1) ∗ ((sp' + 328#64) ↦₆₄ w2) ∗ ((sp' +
      336#64) ↦₆₄ w3) ∗
        ((sp' + 344#64) ↦₆₄ w4)) ∗ (memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono_left hw5
/-! ## 5. Segment 4 Error Helpers -/
theorem deserialize_error_cases {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : PublicKey.deserialize bs = .error e) :
    e = .noKeyTypeIdentifier ∨ (∃ t, e = .badKeyType t) ∨ (∃ n, e = .badKeyLength n) := by
  unfold PublicKey.deserialize at h
  rcases bs with _ | ⟨t, rest⟩
  · simp at h; exact Or.inl h.symm
  · by_cases ht : t ≠ djbType
    · simp [ht] at h; exact Or.inr (Or.inl ⟨t, h.symm⟩)
    · by_cases hlen : 32 ≤ rest.length
      · simp [ht, hlen] at h
      · simp [ht, hlen] at h; exact Or.inr (Or.inr ⟨rest.length + 1, h.symm⟩)
theorem tryFrom_error_cases {codec : SignalMessageProtoCodec} {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : SignalMessage.tryFrom codec bs = .error e) : (∃ n, e = .ciphertextMessageTooShort n) ∨
    (∃ v, e = .legacyCiphertextVersion v) ∨ (∃ v, e = .unrecognizedCiphertextVersion v) ∨
    e = .invalidProtobufEncoding ∨ e = .noKeyTypeIdentifier ∨ (∃ t, e = .badKeyType t) ∨
    (∃ n, e = .badKeyLength n) := by
  simp only [SignalMessage.tryFrom, Bind.bind, Except.bind, Pure.pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at h
  split_ifs at h
  · injection h with h; exact Or.inl ⟨_, h.symm⟩
  · injection h with h; exact Or.inr (Or.inl ⟨_, h.symm⟩)
  · injection h with h; exact Or.inr (Or.inr (Or.inl ⟨_, h.symm⟩))
  · rcases hdec : codec.decode ((bs.take (bs.length - macLength)).drop 1) with _ | p
    · rw [hdec] at h; injection h with h; exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
    · rw [hdec] at h; dsimp only at h
      rcases hrk : p.ratchetKey with _ | rk
      · rw [hrk] at h; injection h with h; exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
      · rw [hrk] at h; dsimp only at h
        rcases hpk : PublicKey.deserialize rk with e' | pk
        · rw [hpk] at h; injection h with h; subst h
          rcases deserialize_error_cases hpk with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, rfl⟩)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, rfl⟩)))))
        · rw [hpk] at h; dsimp only at h
          rcases hcnt : p.counter with _ | cnt
          · rw [hcnt] at h; injection h with h; exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
          · rw [hcnt] at h; dsimp only at h
            rcases hct : p.ciphertext with _ | ct
            · rw [hct] at h; injection h with h; exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
            · rw [hct] at h; contradiction
private theorem speAt_words2_u64 (a tag val : BitVec 64) :
    (a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ val) ∗ memRegion (a + 16#64) 32 ⊢
      ∃∗ ew0 : BitVec 64, ∃∗ ew1 : BitVec 64,
        (a ↦₆₄ ew0) ∗ ((a + 8#64) ↦₆₄ ew1) ∗ memRegion (a + 16#64) 32 ∗ ⌜∀ b : BitVec 64,
          (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
            (b ↦₆₄ tag) ∗ ((b + 8#64) ↦₆₄ val) ∗ memRegion (b + 16#64) 32⌝ := by
  refine Entails.trans ?_ (Entails.sepExists_intro tag)
  refine Entails.trans ?_ (Entails.sepExists_intro val)
  rw [pure_true_emp (fun _ => Entails.refl _), sepConj_emp]
  exact Entails.refl _
private theorem speAt_words2_unit (a tag : BitVec 64) : (a ↦₆₄ tag) ∗ memRegion (a + 8#64) 40 ⊢
      ∃∗ ew0 : BitVec 64, ∃∗ ew1 : BitVec 64,
        (a ↦₆₄ ew0) ∗ ((a + 8#64) ↦₆₄ ew1) ∗ memRegion (a + 16#64) 32 ∗ ⌜∀ b : BitVec 64,
          (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
            (b ↦₆₄ tag) ∗ memRegion (b + 8#64) 40⌝ := by
  rw [memRegion_split (a + 8#64) 8 32 (by decide), ProofLib.memRegion_eight (a + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ew1 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro tag)
  refine Entails.trans ?_ (Entails.sepExists_intro ew1)
  have hp : ∀ b : BitVec 64, (b ↦₆₄ tag) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
        (b ↦₆₄ tag) ∗ memRegion (b + 8#64) 40 := fun b => by
    rw [memRegion_split (b + 8#64) 8 32 (by decide), ProofLib.memRegion_eight (b + 8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro ew1))
  rw [pure_true_emp hp, sepConj_emp]
  exact Entails.refl _
private theorem speAt_words2_u8 (a tag : BitVec 64) (v : BitVec 8) :
    (a ↦₆₄ tag) ∗ ((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39 ⊢
      ∃∗ ew0 : BitVec 64, ∃∗ ew1 : BitVec 64,
        (a ↦₆₄ ew0) ∗ ((a + 8#64) ↦₆₄ ew1) ∗ memRegion (a + 16#64) 32 ∗ ⌜∀ b : BitVec 64,
          (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
            (b ↦₆₄ tag) ∗ ((b + 8#64) ↦₈ v) ∗ memRegion (b + 9#64) 39⌝ := by
  rw [memRegion_split (a + 9#64) 7 32 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h1 := pointsTo8_memRegion7_to_64 (a + 8#64) v
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  rw [← sepConj_assoc ((a + 8#64) ↦₈ v)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h1)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun hi56 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro tag)
  refine Entails.trans ?_ (Entails.sepExists_intro (hi56 ++ v))
  have hp : ∀ b : BitVec 64, (b ↦₆₄ tag) ∗ ((b + 8#64) ↦₆₄ (hi56 ++ v)) ∗ memRegion (b + 16#64) 32 ⊢
        (b ↦₆₄ tag) ∗ ((b + 8#64) ↦₈ v) ∗ memRegion (b + 9#64) 39 := fun b => by
    rw [memRegion_split (b + 9#64) 7 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have h2 := pointsTo64_to_8_memRegion7 (b + 8#64) hi56 v
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2
    rw [← sepConj_assoc ((b + 8#64) ↦₈ v)]
    exact sepConj_mono_right (sepConj_mono_left h2)
  rw [pure_true_emp hp, sepConj_emp]
  exact Entails.refl _
theorem speAt_tryFrom_words2 (A : RustAlloc) (a : BitVec 64)
    {codec : SignalMessageProtoCodec} {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : SignalMessage.tryFrom codec bs = .error e) :
    speAt A [] a e ⊢
      ∃∗ ew0 : BitVec 64, ∃∗ ew1 : BitVec 64,
        (a ↦₆₄ ew0) ∗ ((a + 8#64) ↦₆₄ ew1) ∗ memRegion (a + 16#64) 32 ∗ ⌜∀ b : BitVec 64,
          (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
            speAt A [] b e⌝ := by
  rcases tryFrom_error_cases h with ⟨n, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · exact speAt_words2_u64 a (speWord 3) (BitVec.ofNat 64 n)
  · exact speAt_words2_u8 a (speWord 4) v
  · exact speAt_words2_u8 a (speWord 5) v
  · exact speAt_words2_unit a (speWord 2)
  · exact speAt_words2_unit a (speWord 7)
  · exact speAt_words2_u8 a (speWord 8) t
  · exact speAt_words2_u64 a (speWord 9) (BitVec.ofNat 64 n)
theorem words4_entails_memRegion32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [memRegion32_words4 a]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (sepConj_mono (Entails.sepExists_intro w2)
        (Entails.sepExists_intro w3)))
theorem boxU8Buf_kyber_dealloc (A : RustAlloc) (ptr : BitVec 64) (x : PreKeyTryFromArgs) :
    boxU8Buf A ptr x.kyberBytes ⊢ ⌜ptr ≠ 0#64⌝ ∗ A.live ptr 1569 1 ∗ memRegion ptr 1569 := by
  unfold boxU8Buf
  have hne : x.kyberBytes ≠ [] := by simp [PreKeyTryFromArgs.kyberBytes]
  simp only [hne, ↓reduceIte, PreKeyTryFromArgs.kyberBytes_length]
  refine Entails.pure_left fun ⟨hptr, _⟩ => ?_
  rw [pure_true_emp hptr, emp_sepConj]
  exact sepConj_mono_right (by simpa using pointsToBytes_entails_memRegion ptr x.kyberBytes)
theorem memRegion48_words6 (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗ (∃∗ w2 : BitVec 64,
        (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) ∗ (∃∗ w4 : BitVec 64, (a + 32#64) ↦₆₄ w4) ∗ (∃∗
        w5 : BitVec 64, (a + 40#64) ↦₆₄ w5) := by
  rw [show (48 : Nat) = 8 + (8 + 32) by decide, memRegion_split a 8 40 (by decide),
    memRegion_split (a + 8#64) 8 32 (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
    memRegion32_words4 (a + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem words6_entails_memRegion48 (a w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a +
      32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢
      memRegion a 48 := by
  rw [memRegion48_words6 a]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (sepConj_mono (Entails.sepExists_intro w2)
        (sepConj_mono (Entails.sepExists_intro w3) (sepConj_mono (Entails.sepExists_intro w4)
            (Entails.sepExists_intro w5)))))
theorem words7_memRegion64_entails_memRegion120 (a w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a +
      32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
    ((a + 48#64) ↦₆₄ w6) ∗ memRegion (a + 56#64) 64 ⊢ memRegion a 120 := by
  rw [show (120 : Nat) = 8 + (48 + 64) by decide, memRegion_split a 8 112 (by decide),
    memRegion_split (a + 8#64) 48 64 (by decide),
    ProofLib.memRegion_eight a, memRegion48_words6 (a + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (sepConj_mono (Entails.sepExists_intro w2)
        (sepConj_mono (Entails.sepExists_intro w3) (sepConj_mono (Entails.sepExists_intro w4)
            (sepConj_mono (Entails.sepExists_intro w5) (sepConj_mono (Entails.sepExists_intro w6)
                (Entails.refl _)))))))
theorem err_result_entails_preKeyResultAt (A : RustAlloc) (x : PreKeyTryFromArgs)
    {e : SignalProtocolError} (hsig : SignalMessage.tryFrom protoSignalCodec x.inner = .error e)
    (ew0 ew1 ew2 ew3 ew4 ew5 : BitVec 64) (hpack : ∀ b : BitVec 64,
      (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢ speAt A [] b e) :
    (x.sret ↦₆₄ 18446744073709551615#64) ∗ ((x.sret + 8#64) ↦₆₄ ew0) ∗ ((x.sret + 16#64) ↦₆₄ ew1) ∗
    ((x.sret + 24#64) ↦₆₄ ew2) ∗ ((x.sret + 32#64) ↦₆₄ ew3) ∗ ((x.sret + 40#64) ↦₆₄ ew4) ∗
      ((x.sret + 48#64) ↦₆₄ ew5) ∗
    memRegion (x.sret + 56#64) 192 ⊢ preKeyResultAt A x.sret x := by
  unfold preKeyResultAt
  rw [hsig]
  have hm32 := words4_entails_memRegion32 (x.sret + 24#64) ew2 ew3 ew4 ew5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm32
  have hsp_b := hpack (x.sret + 8#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsp_b
  have h1 :
      ((x.sret + 8#64) ↦₆₄ ew0) ∗ ((x.sret + 16#64) ↦₆₄ ew1) ∗ ((x.sret + 24#64) ↦₆₄ ew2) ∗
        ((x.sret + 32#64) ↦₆₄ ew3) ∗
      ((x.sret + 40#64) ↦₆₄ ew4) ∗ ((x.sret + 48#64) ↦₆₄ ew5) ⊢
        speAt A [] (x.sret + 8#64) e :=
    Entails.trans (sepConj_mono_right (sepConj_mono_right hm32)) hsp_b
  have h2 :
      (((x.sret + 8#64) ↦₆₄ ew0) ∗ ((x.sret + 16#64) ↦₆₄ ew1) ∗ ((x.sret + 24#64) ↦₆₄ ew2) ∗
        ((x.sret + 32#64) ↦₆₄ ew3) ∗
        ((x.sret + 40#64) ↦₆₄ ew4) ∗ ((x.sret + 48#64) ↦₆₄ ew5)) ∗ memRegion (x.sret + 56#64) 192 ⊢
        speAt A [] (x.sret + 8#64) e ∗ memRegion (x.sret + 56#64) 192 :=
    sepConj_mono_left h1
  simpa [sepConj_assoc, errTag] using sepConj_mono_right (P :=
    x.sret ↦₆₄ 18446744073709551615#64) h2
theorem memRegion248_split_err (r : BitVec 64) :
    memRegion r 248 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (r + 8#64) ↦₆₄ w1) ∗ (∃∗ w2 : BitVec 64,
        (r + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (r + 24#64) ↦₆₄ w3) ∗ (∃∗ w4 : BitVec 64, (r + 32#64) ↦₆₄ w4) ∗ (∃∗
        w5 : BitVec 64, (r + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (r + 48#64) ↦₆₄ w6) ∗ memRegion (r + 56#64) 192 := by
  rw [show (248 : Nat) = 8 + (48 + 192) by decide, memRegion_split r 8 240 (by decide),
    memRegion_split (r + 8#64) 48 192 (by decide),
    ProofLib.memRegion_eight r, memRegion48_words6 (r + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
end CryptoVerification.E2E.Pqxdh.ResponderWire

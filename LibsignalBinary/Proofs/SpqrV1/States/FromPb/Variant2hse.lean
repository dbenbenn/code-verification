/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsc
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part E

`Unchunked::EkSent` stack assembly (`+8908..+9032`), `sendingEk = none` branch (`+9032 -> +9212`),
and 56-byte `ProtoPolynomialEncoder` staging (`+9036..+9096`).
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



theorem v2hse_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## `unchunkedEkSentAt` Word/Heap Decomposition & `+8908 .. +9032` Stepping -/

@[expose] def v2hse_unchunkedEkSentWordsAt (a ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64) : SepProp :=
  (a ↦₆₄ ca1) ∗ ((a + 8#64) ↦₆₄ pa1) ∗ ((a + 16#64) ↦₆₄ la1) ∗
  ((a + 24#64) ↦₆₄ ca2) ∗ ((a + 32#64) ↦₆₄ pa2) ∗ ((a + 40#64) ↦₆₄ la2) ∗
  ((a + 48#64) ↦₆₄ ca3) ∗ ((a + 56#64) ↦₆₄ pa3) ∗ ((a + 64#64) ↦₆₄ la3) ∗
  ((a + 72#64) ↦₆₄ epoch)

@[expose] def v2hse_vecU8Heap (A : RustAlloc) (cap ptr len : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜len = BitVec.ofNat 64 bs.length ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
  (if cap = 0#64 then emp
   else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
     memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem v2hse_vecU8_unpack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
        ⌜cap.toNat < 2 ^ 63⌝ ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
        v2hse_vecU8Heap A cap ptr len bs := by
  unfold vecU8 vecU8At vecHeader v2hse_vecU8Heap
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap ?_
  refine Entails.sepExists_right ptr ?_
  refine Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
     (if cap = 0#64 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hle, hcap, hptr⟩
  refine Entails.pure_right hcap ?_
  have hpure : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length ∧
      bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 := ⟨rfl, hle, hcap, hptr⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v2hse_vecU8_pack (A : RustAlloc) (a cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
      v2hse_vecU8Heap A cap ptr len bs ⊢
    vecU8 A a bs := by
  unfold vecU8 vecU8At vecHeader v2hse_vecU8Heap
  refine Entails.sepExists_right cap ?_
  refine Entails.sepExists_right ptr ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜len = BitVec.ofNat 64 bs.length ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len) ∗
     (if cap = 0#64 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, hle, hcap, hptr⟩
  have hpure : bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 := ⟨hle, hcap, hptr⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v2hse_vecU8Heap_entails_dealloc (A : RustAlloc) (cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    v2hse_vecU8Heap A cap ptr len bs ⊢ vecCapPtrDealloc A cap ptr := by
  unfold v2hse_vecU8Heap vecCapPtrDealloc
  apply Entails.pure_left; rintro ⟨_, hle, hcap, _⟩
  by_cases hc : cap = 0#64
  · subst hc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · have hcf : (cap == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcf, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepConj_mono_right
    have h1 := ProofLib.pointsToBytes_entails_memRegion ptr bs
    have hadd : bs.length + (cap.toNat - bs.length) = cap.toNat := Nat.add_sub_of_le hle
    have h2 : memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
        memRegion ptr cap.toNat := by
      rw [← ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length) hadd.symm rfl (by omega)]
    rw [← h2]
    exact sepConj_mono_left h1

theorem v2hse_unchunkedEkSentAt_pack (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (uc : Unchunked.SendEk.EkSent (spqrAuthApi F))
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 : BitVec 64) :
    v2hse_unchunkedEkSentWordsAt a ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 uc.epoch ∗
      v2hse_vecU8Heap A ca1 pa1 la1 uc.auth.rootKey ∗
      v2hse_vecU8Heap A ca2 pa2 la2 uc.auth.macKey ∗
      v2hse_vecU8Heap A ca3 pa3 la3 uc.dk ⊢
    unchunkedEkSentAt A a uc := by
  unfold unchunkedEkSentAt authenticatorAt v2hse_unchunkedEkSentWordsAt
  have h1 := v2hse_vecU8_pack A a ca1 pa1 la1 uc.auth.rootKey
  have h2 := v2hse_vecU8_pack A (a + 24#64) ca2 pa2 la2 uc.auth.macKey
  have h3 := v2hse_vecU8_pack A (a + 48#64) ca3 pa3 la3 uc.dk
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h2 h3 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    (((a ↦₆₄ ca1) ∗ ((a + 8#64) ↦₆₄ pa1) ∗ ((a + 16#64) ↦₆₄ la1)) ∗
     v2hse_vecU8Heap A ca1 pa1 la1 uc.auth.rootKey) ∗
    ((((a + 24#64) ↦₆₄ ca2) ∗ ((a + 32#64) ↦₆₄ pa2) ∗ ((a + 40#64) ↦₆₄ la2)) ∗
     v2hse_vecU8Heap A ca2 pa2 la2 uc.auth.macKey) ∗
    ((((a + 48#64) ↦₆₄ ca3) ∗ ((a + 56#64) ↦₆₄ pa3) ∗ ((a + 64#64) ↦₆₄ la3)) ∗
     v2hse_vecU8Heap A ca3 pa3 la3 uc.dk) ∗
    ((a + 72#64) ↦₆₄ uc.epoch) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem v2hse_unchunkedEkSentWordsAt_entails_80
    (a ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64) :
    v2hse_unchunkedEkSentWordsAt a ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ⊢
      memRegion a 80 := by
  unfold v2hse_unchunkedEkSentWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v2hse_memRegion_1264_80_split (fsp : BitVec 64) :
    memRegion (fsp + 1264#64) 80 ⊢
      (∃∗ u0 : BitVec 64, (fsp + 1264#64) ↦₆₄ u0) ∗
      (∃∗ u8 : BitVec 64, (fsp + 1272#64) ↦₆₄ u8) ∗
      (∃∗ u16 : BitVec 64, (fsp + 1280#64) ↦₆₄ u16) ∗
      (∃∗ u24 : BitVec 64, (fsp + 1288#64) ↦₆₄ u24) ∗
      (∃∗ u32 : BitVec 64, (fsp + 1296#64) ↦₆₄ u32) ∗
      (∃∗ u40 : BitVec 64, (fsp + 1304#64) ↦₆₄ u40) ∗
      (∃∗ u48 : BitVec 64, (fsp + 1312#64) ↦₆₄ u48) ∗
      (∃∗ u56 : BitVec 64, (fsp + 1320#64) ↦₆₄ u56) ∗
      (∃∗ u64 : BitVec 64, (fsp + 1328#64) ↦₆₄ u64) ∗
      (∃∗ u72 : BitVec 64, (fsp + 1336#64) ↦₆₄ u72) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    mem64_entails _

theorem v2hse_pointsTo64_split_1_4_2_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗
      ((a + 1#64) ↦₃₂ w.extractLsb' 8 32) ∗
      ((a + 5#64) ↦₁₆ w.extractLsb' 40 16) ∗
      ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hb1 : (w.extractLsb' 8 32).extractLsb' 0 8 = w.extractLsb' 8 8 := by bv_kernel
  have hb2 : (w.extractLsb' 8 32).extractLsb' 8 8 = w.extractLsb' 16 8 := by bv_kernel
  have hb3 : (w.extractLsb' 8 32).extractLsb' 16 8 = w.extractLsb' 24 8 := by bv_kernel
  have hb4 : (w.extractLsb' 8 32).extractLsb' 24 8 = w.extractLsb' 32 8 := by bv_kernel
  have hb5 : (w.extractLsb' 40 16).extractLsb' 0 8 = w.extractLsb' 40 8 := by bv_kernel
  have hb6 : (w.extractLsb' 40 16).extractLsb' 8 8 = w.extractLsb' 48 8 := by bv_kernel
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo32_eq_pointsToBytes (a + 1#64) (w.extractLsb' 8 32),
      ProofLib.pointsTo16_eq_pointsToBytes (a + 5#64) (w.extractLsb' 40 16)]
  simp only [unpack64, unpack32, unpack16,
    ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
    hb1, hb2, hb3, hb4, hb5, hb6,
    sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

theorem v2hse_1272_split_rest (fsp u8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1272#64) ↦₆₄ u8) ∗ Rest =
      ((fsp + 1272#64) ↦₈ u8.extractLsb' 0 8) ∗
      ((fsp + 1273#64) ↦₃₂ u8.extractLsb' 8 32) ∗
      ((fsp + 1277#64) ↦₁₆ u8.extractLsb' 40 16) ∗
      ((fsp + 1279#64) ↦₈ u8.extractLsb' 56 8) ∗ Rest := by
  have h := v2hse_pointsTo64_split_1_4_2_1 (fsp + 1272#64) u8
  have ha1 : (fsp + 1272#64) + 1#64 = fsp + 1273#64 := by bv_omega
  have ha5 : (fsp + 1272#64) + 5#64 = fsp + 1277#64 := by bv_omega
  have ha7 : (fsp + 1272#64) + 7#64 = fsp + 1279#64 := by bv_omega
  rw [ha1, ha5, ha7] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v2hse_1272_unsplit_rest (fsp u8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1272#64) ↦₈ u8.extractLsb' 0 8) ∗
      ((fsp + 1273#64) ↦₃₂ u8.extractLsb' 8 32) ∗
      ((fsp + 1277#64) ↦₁₆ u8.extractLsb' 40 16) ∗
      ((fsp + 1279#64) ↦₈ u8.extractLsb' 56 8) ∗ Rest =
      ((fsp + 1272#64) ↦₆₄ u8) ∗ Rest :=
  (v2hse_1272_split_rest fsp u8 Rest).symm

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_pa1_d1273 (pa1 : BitVec 64) :
    ((pa1.extractLsb' 8 56).zeroExtend 64).setWidth 32 = pa1.extractLsb' 8 32 := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_pa1_b1279 (pa1 : BitVec 64) :
    (((pa1.extractLsb' 8 56).setWidth 64).extractLsb' 48 16).setWidth 8 =
      pa1.extractLsb' 56 8 := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_pa1_h1277 (pa1 : BitVec 64) :
    (((pa1.extractLsb' 8 56).setWidth 64).extractLsb' 32 32).setWidth 16 =
      pa1.extractLsb' 40 16 := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_pa1_b1272 (pa1 : BitVec 64) :
    (pa1.setWidth 32).setWidth 8 = pa1.extractLsb' 0 8 := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_fsp_1264_add_9 (fsp : BitVec 64) :
    (fsp + 1264#64) + 9#64 = fsp + 1273#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse_fsp_1264_add_13 (fsp : BitVec 64) :
    (fsp + 1264#64) + 13#64 = fsp + 1277#64 := by bv_omega

@[expose] def v2hse_withLoByte (b : BitVec 8) (w : BitVec 64) : BitVec 64 :=
  (w &&& 0xffffffffffffff00#64) ||| b.zeroExtend 64

theorem v2hse_loByte_withLoByte (b : BitVec 8) (w : BitVec 64) :
    EncoderFromPb.loByte (v2hse_withLoByte b w) = b := by
  dsimp only [EncoderFromPb.loByte, v2hse_withLoByte]
  bv_kernel

theorem v2hse_hiBytes7_withLoByte (b : BitVec 8) (w : BitVec 64) :
    EncoderFromPb.hiBytes7 (v2hse_withLoByte b w) = EncoderFromPb.hiBytes7 w := by
  simp only [EncoderFromPb.hiBytes7, unpack64, v2hse_withLoByte, List.drop, List.cons.injEq]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem v2hse_threeWords_to_unaligned16 (a u0 u8 u16 : BitVec 64) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u8) ∗ ((a + 16#64) ↦₆₄ u16) =
      (a ↦₈ EncoderFromPb.loByte u0) ∗
      ((a + 1#64) ↦₆₄ EncoderFromPb.unshiftWord u0 (EncoderFromPb.loByte u8)) ∗
      ((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord u8 (EncoderFromPb.loByte u16)) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 u16) := by
  have h1 := EncoderFromPb.pair64_to_byte_word_tail7 (a + 8#64) u8 u16
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have ha17 : (a + 8#64) + 9#64 = a + 17#64 := by bv_omega
  rw [ha16, ha9, ha17] at h1
  have h0 : ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₈ EncoderFromPb.loByte u8)) =
      ((a ↦₈ EncoderFromPb.loByte u0) ∗ ((a + 1#64) ↦₆₄ EncoderFromPb.unshiftWord u0 (EncoderFromPb.loByte u8))) := by
    rw [ProofLib.pointsTo64_eq_pointsToBytes a u0,
        ProofLib.pointsTo64_eq_pointsToBytes (a + 1#64),
        ← ProofLib.pointsToBytes_cons,
        EncoderFromPb.loByte_cons_unpack64_unshiftWord u0 (EncoderFromPb.loByte u8),
        ProofLib.pointsToBytes_append a (unpack64 u0) [EncoderFromPb.loByte u8],
        unpack64_length]
    simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]
  rw [h1, ← sepConj_assoc, ← sepConj_assoc, h0, sepConj_assoc, sepConj_assoc]

theorem v2hse_unaligned16_to_threeWords (a u0 u8 u16 : BitVec 64) :
    (a ↦₈ EncoderFromPb.loByte u0) ∗
      ((a + 1#64) ↦₆₄ EncoderFromPb.unshiftWord u0 (EncoderFromPb.loByte u8)) ∗
      ((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord u8 (EncoderFromPb.loByte u16)) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 u16) =
      (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u8) ∗ ((a + 16#64) ↦₆₄ u16) :=
  (v2hse_threeWords_to_unaligned16 a u0 u8 u16).symm

theorem v2hse_unaligned16_to_threeWords_mixed (a u0 u8 u16 d16 : BitVec 64) :
    (a ↦₈ EncoderFromPb.loByte u0) ∗
      ((a + 1#64) ↦₆₄ EncoderFromPb.unshiftWord u0 (EncoderFromPb.loByte u8)) ∗
      ((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord u8 (EncoderFromPb.loByte u16)) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 d16) =
      (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u8) ∗
      ((a + 16#64) ↦₆₄ v2hse_withLoByte (EncoderFromPb.loByte u16) d16) := by
  have h := v2hse_unaligned16_to_threeWords a u0 u8 (v2hse_withLoByte (EncoderFromPb.loByte u16) d16)
  rwa [v2hse_loByte_withLoByte, v2hse_hiBytes7_withLoByte] at h

theorem v2hse_pbA96_to_unaligned16_rest (pbA w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗ Rest =
      ((pbA + 96#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((pbA + 97#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
      ((pbA + 105#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
      ((pbA + 113#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ Rest := by
  have h := v2hse_threeWords_to_unaligned16 (pbA + 96#64) w8 w16 w24
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hse_pbA96_to_threeWords_rest (pbA w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((pbA + 96#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((pbA + 97#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
      ((pbA + 105#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
      ((pbA + 113#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ Rest =
      ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗ Rest :=
  (v2hse_pbA96_to_unaligned16_rest pbA w8 w16 w24 Rest).symm

theorem v2hse_fsp1800_to_unaligned16_rest (fsp e8 e16 e24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1800#64) ↦₆₄ e8) ∗ ((fsp + 1808#64) ↦₆₄ e16) ∗ ((fsp + 1816#64) ↦₆₄ e24) ∗ Rest =
      ((fsp + 1800#64) ↦₈ EncoderFromPb.loByte e8) ∗
      ((fsp + 1801#64) ↦₆₄ EncoderFromPb.unshiftWord e8 (EncoderFromPb.loByte e16)) ∗
      ((fsp + 1809#64) ↦₆₄ EncoderFromPb.unshiftWord e16 (EncoderFromPb.loByte e24)) ∗
      ((fsp + 1817#64) ↦ₛ EncoderFromPb.hiBytes7 e24) ∗ Rest := by
  have h := v2hse_threeWords_to_unaligned16 (fsp + 1800#64) e8 e16 e24
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hse_fsp1800_to_threeWords_mixed_rest (fsp w8 w16 w24 e24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1800#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 1801#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
      ((fsp + 1809#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
      ((fsp + 1817#64) ↦ₛ EncoderFromPb.hiBytes7 e24) ∗ Rest =
      ((fsp + 1800#64) ↦₆₄ w8) ∗ ((fsp + 1808#64) ↦₆₄ w16) ∗
      ((fsp + 1816#64) ↦₆₄ v2hse_withLoByte (EncoderFromPb.loByte w24) e24) ∗ Rest := by
  have h := v2hse_unaligned16_to_threeWords_mixed (fsp + 1800#64) w8 w16 w24 e24
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hse_fsp984_split_rest (fsp w8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 984#64) ↦₆₄ w8) ∗ Rest =
      ((fsp + 984#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 985#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 984#64) w8
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h
  exact Eq.trans (by ac_rfl) (Eq.trans (congrArg (· ∗ Rest) h) (by ac_rfl))

theorem v2hse_fsp984_unsplit_rest (fsp w8 : BitVec 64) (Rest : SepProp) :
    ((fsp + 984#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((fsp + 985#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗ Rest =
      ((fsp + 984#64) ↦₆₄ w8) ∗ Rest :=
  (v2hse_fsp984_split_rest fsp w8 Rest).symm

structure v2hse_ProtoPolyEncoderPure (pb : ProtoPolynomialEncoder) (w16 w40 w48 : BitVec 64) : Prop where
  hw16 : w16 = BitVec.ofNat 64 pb.pts.length
  hw40 : w40 = BitVec.ofNat 64 pb.polys.length
  hw48 : w48.setWidth 32 = pb.idx

@[expose] def v2hse_protoPolyEncoderWordsAt (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
  ((a + 48#64) ↦₆₄ w48)

@[expose] def v2hse_protoPolyEncoderHeap (A : RustAlloc) (pb : ProtoPolynomialEncoder)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  ⌜v2hse_ProtoPolyEncoderPure pb w16 w40 w48⌝ ∗
  vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
  vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys

theorem v2hse_pointsTo32_pad4_entails_64 (a : BitVec 64) (idx : BitVec 32) :
    (a ↦₃₂ idx) ∗ memRegion (a + 4#64) 4 ⊢
      ∃∗ w : BitVec 64, ⌜w.setWidth 32 = idx⌝ ∗ (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_four (a + 4#64), sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro hi
  refine Entails.sepExists_right (hi ++ idx) ?_
  have hlo : (hi ++ idx).setWidth 32 = idx := by bv_kernel
  have h64 : (a ↦₆₄ (hi ++ idx)) = (a ↦₃₂ idx) ∗ ((a + 4#64) ↦₃₂ hi) := by
    rw [ProofLib.pointsTo64_eq_pointsToBytes, ProofLib.pointsTo32_eq_pointsToBytes,
        ProofLib.pointsTo32_eq_pointsToBytes]
    simp only [unpack64, unpack32, ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
      sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    have b0 : (hi ++ idx).extractLsb' 0 8 = idx.extractLsb' 0 8 := by bv_kernel
    have b1 : (hi ++ idx).extractLsb' 8 8 = idx.extractLsb' 8 8 := by bv_kernel
    have b2 : (hi ++ idx).extractLsb' 16 8 = idx.extractLsb' 16 8 := by bv_kernel
    have b3 : (hi ++ idx).extractLsb' 24 8 = idx.extractLsb' 24 8 := by bv_kernel
    have b4 : (hi ++ idx).extractLsb' 32 8 = hi.extractLsb' 0 8 := by bv_kernel
    have b5 : (hi ++ idx).extractLsb' 40 8 = hi.extractLsb' 8 8 := by bv_kernel
    have b6 : (hi ++ idx).extractLsb' 48 8 = hi.extractLsb' 16 8 := by bv_kernel
    have b7 : (hi ++ idx).extractLsb' 56 8 = hi.extractLsb' 24 8 := by bv_kernel
    rw [b0, b1, b2, b3, b4, b5, b6, b7]
  rw [h64]
  exact Entails.pure_right hlo (Entails.refl _)

theorem v2hse_pointsTo64_entails_32_pad4 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦₃₂ w.setWidth 32) ∗ memRegion (a + 4#64) 4 := by
  have hsplit : (a ↦₆₄ w) = (a ↦₃₂ w.setWidth 32) ∗ ((a + 4#64) ↦₃₂ (w.extractLsb' 32 32)) := by
    rw [ProofLib.pointsTo64_eq_pointsToBytes, ProofLib.pointsTo32_eq_pointsToBytes,
        ProofLib.pointsTo32_eq_pointsToBytes]
    simp only [unpack64, unpack32, ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
      sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    have b0 : (w.setWidth 32).extractLsb' 0 8 = w.extractLsb' 0 8 := by bv_kernel
    have b1 : (w.setWidth 32).extractLsb' 8 8 = w.extractLsb' 8 8 := by bv_kernel
    have b2 : (w.setWidth 32).extractLsb' 16 8 = w.extractLsb' 16 8 := by bv_kernel
    have b3 : (w.setWidth 32).extractLsb' 24 8 = w.extractLsb' 24 8 := by bv_kernel
    have b4 : (w.extractLsb' 32 32).extractLsb' 0 8 = w.extractLsb' 32 8 := by bv_kernel
    have b5 : (w.extractLsb' 32 32).extractLsb' 8 8 = w.extractLsb' 40 8 := by bv_kernel
    have b6 : (w.extractLsb' 32 32).extractLsb' 16 8 = w.extractLsb' 48 8 := by bv_kernel
    have b7 : (w.extractLsb' 32 32).extractLsb' 24 8 = w.extractLsb' 56 8 := by bv_kernel
    rw [b0, b1, b2, b3, b4, b5, b6, b7]
  rw [hsplit]
  exact sepConj_mono_right (pointsTo32_entails_memRegion_4 _ _)

theorem v2hse_protoPolyEncoderAt_unpack (A : RustAlloc) (a : BitVec 64) (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderAt A a pb ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64,
        ⌜w0.toNat < 2 ^ 63⌝ ∗
        v2hse_protoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
        v2hse_protoPolyEncoderHeap A pb w0 w8 w16 w24 w32 w40 w48 := by
  unfold protoPolynomialEncoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
    v2hse_protoPolyEncoderWordsAt v2hse_protoPolyEncoderHeap
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w8
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w24
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w32
  have htail := v2hse_pointsTo32_pad4_entails_64 (a + 0x30#64) pb.idx
  have ha52 : (a + 0x30#64) + 4#64 = a + 0x34#64 := by bv_omega
  rw [ha52] at htail
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right htail)) ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w48
  have hw0 : vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ⊢
      ⌜w0.toNat < 2 ^ 63⌝ ∗ vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts := by
    unfold vecBuf Poly.vecHeaderBytes
    apply Entails.pure_left; rintro ⟨hle, hcap, hptr⟩
    have hlt : w0.toNat < 2 ^ 63 := by omega
    exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hcap, hptr⟩ (Entails.refl _))
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right hw0)) ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right w8
    (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length) (Entails.sepExists_right w24
      (Entails.sepExists_right w32 (Entails.sepExists_right (BitVec.ofNat 64 pb.polys.length)
        (Entails.sepExists_right w48 ?_))))))
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w0.toNat < 2 ^ 63⌝ ∗ ⌜w48.setWidth 32 = pb.idx⌝ ∗
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((a + 48#64) ↦₆₄ w48)) ∗
     (vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
      vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys)) by ac_rfl)) ?_
  apply Entails.pure_left; intro hlt
  apply Entails.pure_left; intro hidx
  refine Entails.pure_right hlt ?_
  have hpure : v2hse_ProtoPolyEncoderPure pb (BitVec.ofNat 64 pb.pts.length)
      (BitVec.ofNat 64 pb.polys.length) w48 := ⟨rfl, rfl, hidx⟩
  exact sepConj_mono_right (Entails.pure_right hpure (Entails.refl _))

theorem v2hse_protoPolyEncoderAt_pack (A : RustAlloc) (a : BitVec 64) (pb : ProtoPolynomialEncoder)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v2hse_protoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
      v2hse_protoPolyEncoderHeap A pb w0 w8 w16 w24 w32 w40 w48 ⊢
    protoPolynomialEncoderAt A a pb := by
  unfold protoPolynomialEncoderAt vecVecU8At vecOf vecAt vecHeader
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
    v2hse_protoPolyEncoderWordsAt v2hse_protoPolyEncoderHeap
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜v2hse_ProtoPolyEncoderPure pb w16 w40 w48⌝ ∗
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
     ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
     ((a + 48#64) ↦₆₄ w48) ∗
     vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
     vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, rfl, hidx⟩
  rw [sepExists_sepConj_left]; refine Entails.sepExists_right w0 ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_right w8 ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; refine Entails.sepExists_right w24 ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; refine Entails.sepExists_right w32 ?_
  have htail := v2hse_pointsTo64_entails_32_pad4 (a + 48#64) w48
  rw [hidx] at htail
  simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at htail ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    ((a + 48#64) ↦₆₄ w48) ∗
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts) ∗
     (((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      vecBuf A Poly.vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys)) by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))

theorem v2hse_memRegion_1792_56_split (fsp : BitVec 64) :
    memRegion (fsp + 1792#64) 56 ⊢
      (∃∗ e0 : BitVec 64, (fsp + 1792#64) ↦₆₄ e0) ∗
      (∃∗ e8 : BitVec 64, (fsp + 1800#64) ↦₆₄ e8) ∗
      (∃∗ e16 : BitVec 64, (fsp + 1808#64) ↦₆₄ e16) ∗
      (∃∗ e24 : BitVec 64, (fsp + 1816#64) ↦₆₄ e24) ∗
      (∃∗ e32 : BitVec 64, (fsp + 1824#64) ↦₆₄ e32) ∗
      (∃∗ e40 : BitVec 64, (fsp + 1832#64) ↦₆₄ e40) ∗
      (∃∗ e48 : BitVec 64, (fsp + 1840#64) ↦₆₄ e48) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    mem64_entails _

end CryptoVerification.SpqrV1.States.FromPb


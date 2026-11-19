/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7e -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7c -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# SPQR V1 `<States>::from_pb`: Variant 7 (`Ct1Sampled`, niche variant) — Part F

`<Ct1Sent>::from_pb` copy (`+3480 -> +3548`), call (`+3548`), error branch (`+3552 -> +5444`),
`Ok` spill (`+3552 -> +3648`) and `sendingCt1 = none` branch (`+3648 -> +7100`), plus
`<PolyEncoder>::from_pb` copy (`+3652 -> +3716`), call (`+3716`), error branch (`+3720 -> +3732`),
and `Ok` move (`+3720 -> +7260 -> +7348`).
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero



/-! ## 1. `<Ct1Sent>::from_pb` Copy (`+3480 -> +3548`) -/

theorem v7_memRegion_240_split_ucCopy (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 128 ⊢
      (∃∗ d0 : BitVec 64, (fsp + 240#64) ↦₆₄ d0) ∗
      (∃∗ b8 : BitVec 8, (fsp + 248#64) ↦₈ b8) ∗
      (∃∗ q9_lo : BitVec 64, (fsp + 249#64) ↦₆₄ q9_lo) ∗
      (∃∗ q9_hi : BitVec 64, (fsp + 257#64) ↦₆₄ q9_hi) ∗
      memRegion (fsp + 265#64) 7 ∗
      (∃∗ d32 : BitVec 64, (fsp + 272#64) ↦₆₄ d32) ∗
      (∃∗ d40 : BitVec 64, (fsp + 280#64) ↦₆₄ d40) ∗
      (∃∗ d48 : BitVec 64, (fsp + 288#64) ↦₆₄ d48) ∗
      (∃∗ d56 : BitVec 64, (fsp + 296#64) ↦₆₄ d56) ∗
      (∃∗ d64 : BitVec 64, (fsp + 304#64) ↦₆₄ d64) ∗
      (∃∗ d72 : BitVec 64, (fsp + 312#64) ↦₆₄ d72) ∗
      (∃∗ d80 : BitVec 64, (fsp + 320#64) ↦₆₄ d80) ∗
      (∃∗ d88 : BitVec 64, (fsp + 328#64) ↦₆₄ d88) ∗
      (∃∗ d96 : BitVec 64, (fsp + 336#64) ↦₆₄ d96) ∗
      (∃∗ d104 : BitVec 64, (fsp + 344#64) ↦₆₄ d104) ∗
      (∃∗ d112 : BitVec 64, (fsp + 352#64) ↦₆₄ d112) ∗
      (∃∗ d120 : BitVec 64, (fsp + 360#64) ↦₆₄ d120) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem8_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
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

theorem v7_ucTailWordsAt_to_step3480
    (a w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : BitVec 64) :
    v7_ucTailWordsAt a w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ⊢
      ((a + 8#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((a + 9#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗
      ((a + 16#64) ↦₆₄ w16) ∗
      ((a + 24#64) ↦₆₄ w24) ∗
      ((a + 32#64) ↦₆₄ w32) ∗
      ((a + 40#64) ↦₆₄ w40) ∗
      ((a + 48#64) ↦₆₄ w48) ∗
      ((a + 56#64) ↦₆₄ w56) ∗
      ((a + 64#64) ↦₆₄ w64) ∗
      ((a + 72#64) ↦₆₄ w72) ∗
      ((a + 80#64) ↦₆₄ w80) ∗
      ((a + 88#64) ↦₆₄ w88) ∗
      ((a + 96#64) ↦₆₄ w96) ∗
      ((a + 104#64) ↦₆₄ w104) ∗
      ((a + 112#64) ↦₆₄ w112) ∗
      ((a + 120#64) ↦₆₄ w120) := by
  unfold v7_ucTailWordsAt
  have h8 := pointsTo64_split_1_7 (a + 8#64) w8
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  rw [ha9] at h8
  rw [h8]
  exact Entails.of_eq (by ac_rfl)

theorem v7_byte_word_eq_word_byte (a : BitVec 64) (b0 : BitVec 8) (u : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ u)) =
      ((a ↦₆₄ ((u <<< 8) ||| b0.zeroExtend 64)) ∗ ((a + 8#64) ↦₈ EncoderFromPb.hiByte u)) := by
  let w : BitVec 64 := (u <<< 8) ||| b0.zeroExtend 64
  have hlo : EncoderFromPb.loByte w = b0 := by
    simp only [EncoderFromPb.loByte, w]
    bv_kernel
  have hun : EncoderFromPb.unshiftWord w (EncoderFromPb.hiByte u) = u := by
    simp only [EncoderFromPb.unshiftWord, EncoderFromPb.hiByte, w]
    bv_kernel
  conv_lhs => rw [← hlo, ← hun]
  rw [ProofLib.pointsTo64_eq_pointsToBytes (a + 1#64),
      ← ProofLib.pointsToBytes_cons,
      EncoderFromPb.loByte_cons_unpack64_unshiftWord w (EncoderFromPb.hiByte u),
      ProofLib.pointsToBytes_append a (unpack64 w) [EncoderFromPb.hiByte u],
      unpack64_length,
      ← ProofLib.pointsTo64_eq_pointsToBytes a w]
  simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp, w]

theorem v7_byte_region119_to_words (a : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗ memRegion (a + 1#64) 119 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
        ⌜w0.extractLsb' 0 8 = b0⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
        memRegion (a + 24#64) 96 := by
  rw [ProofLib.memRegion_split' (b := a + 1#64) (n := 8) (k := 111)
        (b' := a + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 1#64),
      sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u
  rw [← sepConj_assoc, v7_byte_word_eq_word_byte a b0 u, sepConj_assoc]
  have h112 : ((a + 8#64) ↦₈ EncoderFromPb.hiByte u) ∗ memRegion (a + 9#64) 111 ⊢
      (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
      (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
      memRegion (a + 24#64) 96 := by
    have hjoin : ((a + 8#64) ↦₈ EncoderFromPb.hiByte u) ∗ memRegion (a + 9#64) 111 ⊢
        memRegion (a + 8#64) 112 := by
      rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 111)
            (b' := a + 9#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)
    refine Entails.trans hjoin ?_
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 104)
          (b' := a + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 96)
          (b' := a + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (a + 8#64),
        ProofLib.memRegion_eight (a + 16#64)]
    exact Entails.refl _
  refine Entails.trans (sepConj_mono_right h112) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w8
  have hlo : (((u <<< 8) ||| b0.zeroExtend 64).extractLsb' 0 8) = b0 := by bv_kernel
  refine Entails.sepExists_right ((u <<< 8) ||| b0.zeroExtend 64)
    (Entails.sepExists_right w8 (Entails.sepExists_right w16 ?_))
  exact Entails.pure_right hlo (Entails.refl _)

theorem v7_ct1SentResult_err_unpack
    (A : RustAlloc) {F : ShaCompress} (fsp : BitVec 64) (e : StatesError) :
    ct1SentResultAt A (F := F) (fsp + 1888#64) (.error e) ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
        ⌜w8.extractLsb' 0 8 = 0#8⌝ ∗
        (((fsp + 1888#64) ↦₆₄ noneCap) ∗
         ((fsp + 1896#64) ↦₆₄ w8) ∗
         ((fsp + 1904#64) ↦₆₄ w16) ∗
         ((fsp + 1912#64) ↦₆₄ w24) ∗
         memRegion (fsp + 1920#64) 96) := by
  unfold ct1SentResultAt
  have hbm := v7_byte_region119_to_words (fsp + 1896#64) 0#8
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbm ⊢
  refine Entails.trans (sepConj_mono_right hbm) ?_
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w24
  refine Entails.sepExists_right w8 (Entails.sepExists_right w16 (Entails.sepExists_right w24 ?_))
  rw [← sepConj_assoc, sepConj_comm ((fsp + 1888#64) ↦₆₄ noneCap), sepConj_assoc]
  apply Entails.pure_left; intro hw8
  exact Entails.pure_right hw8 (Entails.of_eq (by ac_rfl))

theorem v7_1888_words_to_memRegion_128 (fsp w0 w8 w16 w24 : BitVec 64) :
    ((fsp + 1888#64) ↦₆₄ w0) ∗
    ((fsp + 1896#64) ↦₆₄ w8) ∗
    ((fsp + 1904#64) ↦₆₄ w16) ∗
    ((fsp + 1912#64) ↦₆₄ w24) ∗
    memRegion (fsp + 1920#64) 96 ⊢
      memRegion (fsp + 1888#64) 128 := by
  exact collapse_top <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

theorem v7_vecU8Heap_entails_dealloc (A : RustAlloc) (bs : List (BitVec 8)) (cap ptr len : BitVec 64) :
    v7_vecU8Heap A bs cap ptr len ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A cap ptr := by
  unfold v7_vecU8Heap
  apply Entails.pure_left; intro hp
  exact Entails.pure_right hp.2 (vecU8Payload_entails_dealloc A cap ptr bs)

@[expose] def v7_ct1SentWordsAt
    (a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64) : SepProp :=
  (a ↦₆₄ c1) ∗
  ((a + 8#64) ↦₆₄ p1) ∗
  ((a + 16#64) ↦₆₄ l1) ∗
  ((a + 24#64) ↦₆₄ c2) ∗
  ((a + 32#64) ↦₆₄ p2) ∗
  ((a + 40#64) ↦₆₄ l2) ∗
  ((a + 48#64) ↦₆₄ c3) ∗
  ((a + 56#64) ↦₆₄ p3) ∗
  ((a + 64#64) ↦₆₄ l3) ∗
  ((a + 72#64) ↦₆₄ c4) ∗
  ((a + 80#64) ↦₆₄ p4) ∗
  ((a + 88#64) ↦₆₄ l4) ∗
  ((a + 96#64) ↦₆₄ c5) ∗
  ((a + 104#64) ↦₆₄ p5) ∗
  ((a + 112#64) ↦₆₄ l5) ∗
  ((a + 120#64) ↦₆₄ epoch)

@[expose] def v7_ct1SentHeap (A : RustAlloc) {F : ShaCompress}
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64) : SepProp :=
  v7_vecU8Heap A uc.auth.rootKey c1 p1 l1 ∗
  v7_vecU8Heap A uc.auth.macKey c2 p2 l2 ∗
  v7_vecU8Heap A uc.hdr c3 p3 l3 ∗
  v7_vecU8Heap A uc.es c4 p4 l4 ∗
  v7_vecU8Heap A uc.ct1 c5 p5 l5

theorem v7_ct1SentAt_unpack (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    ct1SentAt A (F := F) a uc ⊢
      ∃∗ c1 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ l1 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ l2 : BitVec 64,
      ∃∗ c3 : BitVec 64, ∃∗ p3 : BitVec 64, ∃∗ l3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ p4 : BitVec 64, ∃∗ l4 : BitVec 64,
      ∃∗ c5 : BitVec 64, ∃∗ p5 : BitVec 64, ∃∗ l5 : BitVec 64,
        ⌜c1.toNat < 2 ^ 63⌝ ∗
        v7_ct1SentWordsAt a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 := by
  dsimp only [ct1SentAt, authenticatorAt]
  refine Entails.trans
    (sepConj_mono
      (sepConj_mono (v7_vecU8_unpack A a uc.auth.rootKey)
        (v7_vecU8_unpack A (a + 24#64) uc.auth.macKey))
      (sepConj_mono (v7_vecU8_unpack A (a + 48#64) uc.hdr)
        (sepConj_mono (v7_vecU8_unpack A (a + 72#64) uc.es)
          (sepConj_mono_left (v7_vecU8_unpack A (a + 96#64) uc.ct1))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro c5
  apply Entails.sepExists_elim; intro p5
  apply Entails.sepExists_elim; intro l5
  apply Entails.sepExists_elim; intro c4
  apply Entails.sepExists_elim; intro p4
  apply Entails.sepExists_elim; intro l4
  apply Entails.sepExists_elim; intro c3
  apply Entails.sepExists_elim; intro p3
  apply Entails.sepExists_elim; intro l3
  apply Entails.sepExists_elim; intro c2
  apply Entails.sepExists_elim; intro p2
  apply Entails.sepExists_elim; intro l2
  apply Entails.sepExists_elim; intro c1
  apply Entails.sepExists_elim; intro p1
  apply Entails.sepExists_elim; intro l1
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right l1 (Entails.sepExists_right c2
      (Entails.sepExists_right p2 (Entails.sepExists_right l2
        (Entails.sepExists_right c3 (Entails.sepExists_right p3
          (Entails.sepExists_right l3 (Entails.sepExists_right c4
            (Entails.sepExists_right p4 (Entails.sepExists_right l4
              (Entails.sepExists_right c5 (Entails.sepExists_right p5
                (Entails.sepExists_right l5 ?_))))))))))))))
  unfold v7_ct1SentWordsAt v7_ct1SentHeap
  have hc1 : v7_vecU8Heap A uc.auth.rootKey c1 p1 l1 ⊢
      ⌜c1.toNat < 2 ^ 63⌝ ∗ v7_vecU8Heap A uc.auth.rootKey c1 p1 l1 := by
    unfold v7_vecU8Heap
    apply Entails.pure_left; intro hp
    exact Entails.pure_right hp.2 (Entails.pure_right hp (Entails.refl _))
  refine Entails.trans
    (Entails.of_eq (show _ =
      v7_vecU8Heap A uc.auth.rootKey c1 p1 l1 ∗
      (((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ l1) ∗
        ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ l2) ∗
        ((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ l3) ∗
        ((a + 72#64) ↦₆₄ c4) ∗ ((a + 80#64) ↦₆₄ p4) ∗ ((a + 88#64) ↦₆₄ l4) ∗
        ((a + 96#64) ↦₆₄ c5) ∗ ((a + 104#64) ↦₆₄ p5) ∗ ((a + 112#64) ↦₆₄ l5) ∗
        ((a + 120#64) ↦₆₄ uc.epoch)) ∗
       (v7_vecU8Heap A uc.auth.macKey c2 p2 l2 ∗
        v7_vecU8Heap A uc.hdr c3 p3 l3 ∗
        v7_vecU8Heap A uc.es c4 p4 l4 ∗
        v7_vecU8Heap A uc.ct1 c5 p5 l5)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hc1) ?_
  exact Entails.of_eq (by ac_rfl)

theorem v7_ct1SentAt_pack (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64) :
    v7_ct1SentWordsAt a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
      v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ⊢
      ct1SentAt A (F := F) a uc := by
  dsimp only [v7_ct1SentWordsAt, v7_ct1SentHeap, ct1SentAt, authenticatorAt]
  have h1 := v7_vecU8_pack A a uc.auth.rootKey c1 p1 l1
  have h2 := v7_vecU8_pack A (a + 24#64) uc.auth.macKey c2 p2 l2
  have h3 := v7_vecU8_pack A (a + 48#64) uc.hdr c3 p3 l3
  have h4 := v7_vecU8_pack A (a + 72#64) uc.es c4 p4 l4
  have h5 := v7_vecU8_pack A (a + 96#64) uc.ct1 c5 p5 l5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2 h3 h4 h5
  refine Entails.trans (Entails.of_eq (show _ =
    (((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ l1)) ∗
     v7_vecU8Heap A uc.auth.rootKey c1 p1 l1) ∗
    ((((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ l2)) ∗
     v7_vecU8Heap A uc.auth.macKey c2 p2 l2) ∗
    ((((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ l3)) ∗
     v7_vecU8Heap A uc.hdr c3 p3 l3) ∗
    ((((a + 72#64) ↦₆₄ c4) ∗ ((a + 80#64) ↦₆₄ p4) ∗ ((a + 88#64) ↦₆₄ l4)) ∗
     v7_vecU8Heap A uc.es c4 p4 l4) ∗
    ((((a + 96#64) ↦₆₄ c5) ∗ ((a + 104#64) ↦₆₄ p5) ∗ ((a + 112#64) ↦₆₄ l5)) ∗
     v7_vecU8Heap A uc.ct1 c5 p5 l5) ∗
    ((a + 120#64) ↦₆₄ uc.epoch) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono_left h5))))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem v7_ct1SentWordsAt_entails_128
    (a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64) :
    v7_ct1SentWordsAt a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ⊢
      memRegion a 128 := by
  unfold v7_ct1SentWordsAt
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
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v7_memRegion_128_to_ct1SentWordsAt (a : BitVec 64) :
    memRegion a 128 ⊢
      ∃∗ c1 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ l1 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ l2 : BitVec 64,
      ∃∗ c3 : BitVec 64, ∃∗ p3 : BitVec 64, ∃∗ l3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ p4 : BitVec 64, ∃∗ l4 : BitVec 64,
      ∃∗ c5 : BitVec 64, ∃∗ p5 : BitVec 64, ∃∗ l5 : BitVec 64,
      ∃∗ epoch : BitVec 64,
        v7_ct1SentWordsAt a c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch := by
  have hsplit : memRegion a 128 ⊢
      (∃∗ c1 : BitVec 64, a ↦₆₄ c1) ∗
      (∃∗ p1 : BitVec 64, (a + 8#64) ↦₆₄ p1) ∗
      (∃∗ l1 : BitVec 64, (a + 16#64) ↦₆₄ l1) ∗
      (∃∗ c2 : BitVec 64, (a + 24#64) ↦₆₄ c2) ∗
      (∃∗ p2 : BitVec 64, (a + 32#64) ↦₆₄ p2) ∗
      (∃∗ l2 : BitVec 64, (a + 40#64) ↦₆₄ l2) ∗
      (∃∗ c3 : BitVec 64, (a + 48#64) ↦₆₄ c3) ∗
      (∃∗ p3 : BitVec 64, (a + 56#64) ↦₆₄ p3) ∗
      (∃∗ l3 : BitVec 64, (a + 64#64) ↦₆₄ l3) ∗
      (∃∗ c4 : BitVec 64, (a + 72#64) ↦₆₄ c4) ∗
      (∃∗ p4 : BitVec 64, (a + 80#64) ↦₆₄ p4) ∗
      (∃∗ l4 : BitVec 64, (a + 88#64) ↦₆₄ l4) ∗
      (∃∗ c5 : BitVec 64, (a + 96#64) ↦₆₄ c5) ∗
      (∃∗ p5 : BitVec 64, (a + 104#64) ↦₆₄ p5) ∗
      (∃∗ l5 : BitVec 64, (a + 112#64) ↦₆₄ l5) ∗
      (∃∗ epoch : BitVec 64, (a + 120#64) ↦₆₄ epoch) := by
    exact split_top <|
      split_step0 (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
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
  refine Entails.trans hsplit ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro epoch
  apply Entails.sepExists_elim; intro l5
  apply Entails.sepExists_elim; intro p5
  apply Entails.sepExists_elim; intro c5
  apply Entails.sepExists_elim; intro l4
  apply Entails.sepExists_elim; intro p4
  apply Entails.sepExists_elim; intro c4
  apply Entails.sepExists_elim; intro l3
  apply Entails.sepExists_elim; intro p3
  apply Entails.sepExists_elim; intro c3
  apply Entails.sepExists_elim; intro l2
  apply Entails.sepExists_elim; intro p2
  apply Entails.sepExists_elim; intro c2
  apply Entails.sepExists_elim; intro l1
  apply Entails.sepExists_elim; intro p1
  apply Entails.sepExists_elim; intro c1
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right l1 (Entails.sepExists_right c2
      (Entails.sepExists_right p2 (Entails.sepExists_right l2
        (Entails.sepExists_right c3 (Entails.sepExists_right p3
          (Entails.sepExists_right l3 (Entails.sepExists_right c4
            (Entails.sepExists_right p4 (Entails.sepExists_right l4
              (Entails.sepExists_right c5 (Entails.sepExists_right p5
                (Entails.sepExists_right l5 (Entails.sepExists_right epoch ?_)))))))))))))))
  unfold v7_ct1SentWordsAt
  exact Entails.of_eq (by ac_rfl)

theorem v7_ct1SentHeap_entails_dealloc (A : RustAlloc) {F : ShaCompress}
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64) :
    v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ⊢
      vecCapPtrDealloc A c1 p1 ∗
      vecCapPtrDealloc A c2 p2 ∗
      vecCapPtrDealloc A c3 p3 ∗
      vecCapPtrDealloc A c4 p4 ∗
      vecCapPtrDealloc A c5 p5 := by
  unfold v7_ct1SentHeap
  refine Entails.trans
    (sepConj_mono (v7_vecU8Heap_entails_dealloc A uc.auth.rootKey c1 p1 l1)
      (sepConj_mono (v7_vecU8Heap_entails_dealloc A uc.auth.macKey c2 p2 l2)
        (sepConj_mono (v7_vecU8Heap_entails_dealloc A uc.hdr c3 p3 l3)
          (sepConj_mono (v7_vecU8Heap_entails_dealloc A uc.es c4 p4 l4)
            (v7_vecU8Heap_entails_dealloc A uc.ct1 c5 p5 l5))))) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜c1.toNat < 2 ^ 63⌝ ∗ ⌜c2.toNat < 2 ^ 63⌝ ∗ ⌜c3.toNat < 2 ^ 63⌝ ∗
    ⌜c4.toNat < 2 ^ 63⌝ ∗ ⌜c5.toNat < 2 ^ 63⌝ ∗
    (vecCapPtrDealloc A c1 p1 ∗
     vecCapPtrDealloc A c2 p2 ∗
     vecCapPtrDealloc A c3 p3 ∗
     vecCapPtrDealloc A c4 p4 ∗
     vecCapPtrDealloc A c5 p5) by ac_rfl)) ?_
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  exact Entails.refl _

@[expose] def v7_ct1SentOtherCells
    (fsp c1 p1 l1 c2 l2 l3 l4 l5 epoch : BitVec 64) : SepProp :=
  ((fsp + 1264#64) ↦₆₄ c1) ∗
  ((fsp + 1272#64) ↦₆₄ p1) ∗
  ((fsp + 1280#64) ↦₆₄ l1) ∗
  ((fsp + 1288#64) ↦₆₄ c2) ∗
  ((fsp + 1304#64) ↦₆₄ l2) ∗
  ((fsp + 1328#64) ↦₆₄ l3) ∗
  ((fsp + 1352#64) ↦₆₄ l4) ∗
  ((fsp + 1376#64) ↦₆₄ l5) ∗
  ((fsp + 1384#64) ↦₆₄ epoch)

theorem v7_ct1SentWordsAt_1264_eq_spill_other
    (fsp c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64) :
    v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch =
      v7_ct1SentSpillCells fsp p2 c3 p3 c4 p4 c5 p5 ∗
      v7_ct1SentOtherCells fsp c1 p1 l1 c2 l2 l3 l4 l5 epoch := by
  unfold v7_ct1SentWordsAt v7_ct1SentSpillCells v7_ct1SentOtherCells
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

end CryptoVerification.SpqrV1.States.FromPb

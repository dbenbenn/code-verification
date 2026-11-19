/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c0 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4a
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 4 (`EkSentCt1Received`, `+248`) — Part C

Post-`<PolyDecoder>::from_pb` `Ok` epilogue (`+2472 -> +8180 -> ret`) and `Err` cleanup
(`+2472 -> +8500 -> +5348 -> ret`).
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

theorem v4c_loBytes7_unshiftWord (u1 : BitVec 64) (b2 : BitVec 8) :
    EncoderFromPb.loBytes7 (unshiftWord u1 b2) = EncoderFromPb.hiBytes7 u1 := by
  simp only [EncoderFromPb.loBytes7, EncoderFromPb.hiBytes7, unshiftWord, unpack64,
    List.take, List.drop, List.cons.injEq]
  refine ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem v4c_out_120_recombine (out u8 w16 : BitVec 64) :
    ((out + 120#64) ↦₈ loByte u8) ∗
    ((out + 121#64) ↦₆₄ unshiftWord u8 (loByte w16)) ∗
    ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 w16) =
    ((out + 120#64) ↦₆₄ u8) ∗ ((out + 128#64) ↦₆₄ w16) := by
  have h := (EncoderFromPb.pair64_to_byte_word_tail7 (out + 120#64) u8 w16).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h
  exact h

theorem v4c_out_144_recombine (out u32 u40 u48 : BitVec 64) :
    ((out + 144#64) ↦₈ loByte u32) ∗
    ((out + 145#64) ↦₆₄ unshiftWord u32 (loByte u40)) ∗
    ((out + 153#64) ↦ₛ EncoderFromPb.hiBytes7 u40) ∗
    ((out + 160#64) ↦₆₄ u48) =
    ((out + 144#64) ↦₆₄ u32) ∗ ((out + 152#64) ↦₆₄ u40) ∗ ((out + 160#64) ↦₆₄ u48) := by
  have h1 := (v4c_byte_q128_tail7_to_byte_word_tail7_word (out + 144#64) u32 u40 u48).symm
  have h2 := (v4c_triple64_to_byte_q128_tail7 (out + 144#64) u32 u40 u48).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h1 h2
  exact h1.trans h2

theorem v4c_epilogueOutFull_entails_ok (A : RustAlloc) (F : ShaCompress) (out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (dec : PolyDecoder) (dw : v4c_DecWords)
    (w104 w112 w120 : BitVec 64) (d92 : BitVec 32)
    (q576 : BitVec 128) (w592 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out
      6#64 rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr
      ((((ct1Len.extractLsb' 0 8).zeroExtend 64).setWidth 32).setWidth 8)
      ((v4c_ct1Len_x27 ct1Len).setWidth 32)
      (((v4c_ct1Len_x27 ct1Len >>> 32).setWidth 32).setWidth 16)
      (((v4c_ct1Len_x27 ct1Len >>> 48).setWidth 32).setWidth 8)
      uc.epoch dw.g0.w0 (((loByte dw.g0.u8).zeroExtend 32).setWidth 8)
      (unshiftWord dw.g0.u8 (loByte dw.g0.w16))
      (overlapWord7 (unshiftWord dw.g0.u8 (loByte dw.g0.w16)) (dw.g0.w16 >>> 8))
      dw.g0.u24
      (((loByte dw.g0.u32).zeroExtend 32).setWidth 8)
      (unshiftWord dw.g0.u40 (loByte dw.g0.u48) ++ unshiftWord dw.g0.u32 (loByte dw.g0.u40))
      (overlapWord7
        ((unshiftWord dw.g0.u40 (loByte dw.g0.u48) ++ unshiftWord dw.g0.u32 (loByte dw.g0.u40)).extractLsb' 64 64)
        (dw.g0.u48 >>> 8))
      dw.g1.q56 dw.g1.q72 dw.g1.q88 dw.g1.q104 dw.g1.q120 dw.g1.q136 dw.g1.q152
      dw.g2.q168 dw.g2.q184 dw.g2.q200 dw.g2.q216 dw.g2.q232 dw.g2.q248 dw.g2.q264
      dw.g3.u280 dw.g3.u288 dw.g3.u296 dw.g3.u304
      dw.g3.u312 dw.g3.u320 dw.g3.u328 dw.g3.u336
      dw.g4.u344 dw.g4.u352 dw.g4.u360 dw.g4.u368
      dw.g4.u376 dw.g4.u384 dw.g4.u392 w104
      w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
      bs240 q888 q904 w920 ∗
    v4b_ekSentCt1ReceivedHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
    v4c_decHeap A dec dw ⊢
    resultChunkedStatesAt A (F := F) out
      (.ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) := by
  rw [v4c_ct1Len_b96, v4c_ct1Len_d97, v4c_ct1Len_h101, v4c_ct1Len_b103,
      v4c_zeroExtend32_setWidth8 (loByte dw.g0.u8),
      v4c_zeroExtend32_setWidth8 (loByte dw.g0.u32),
      extractLsb'_64_64_append,
      v4c_overlapWord7_unshift dw.g0.u8 dw.g0.w16,
      v4c_overlapWord7_unshift dw.g0.u40 dw.g0.u48,
      v4c_resultChunkedStatesAt_ok_eq]
  unfold epilogueOutFull
  simp only [extractLsb'_0_64_append, extractLsb'_64_64_append, v4c_loBytes7_unshiftWord]
  have htail := epilogueOut_tail_512_entails_416 out w104 w112 w120 (d92.setWidth 8)
    q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240 hbs240 q888 q904 w920
  have huc := v4c_ekSentCt1ReceivedAt_pack A (F := F) (out + 8#64)
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc
  have hdec := v4c_polyDecoderAt_pack A (out + 112#64) dec dw
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono huc (sepConj_mono hdec htail)))
  dsimp only [v4b_optProtoUcWordsAt, v4c_decWordsAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [← sepConj_assoc ((out + 96#64) ↦₈ _), ← sepConj_assoc (((out + 96#64) ↦₈ _) ∗ _),
      ← sepConj_assoc ((((out + 96#64) ↦₈ _) ∗ _) ∗ _),
      show (((out + 96#64) ↦₈ ct1Len.extractLsb' 0 8 ∗
        (out + 97#64) ↦₃₂ ct1Len.extractLsb' 8 32) ∗
        (out + 101#64) ↦₁₆ ct1Len.extractLsb' 40 16) ∗
        (out + 103#64) ↦₈ ct1Len.extractLsb' 56 8 =
        ((out + 96#64) ↦₈ ct1Len.extractLsb' 0 8) ∗
        ((out + 97#64) ↦₃₂ ct1Len.extractLsb' 8 32) ∗
        ((out + 101#64) ↦₁₆ ct1Len.extractLsb' 40 16) ∗
        ((out + 103#64) ↦₈ ct1Len.extractLsb' 56 8) by ac_rfl,
      v4c_out_96_recombine out ct1Len,
      ← sepConj_assoc ((out + 120#64) ↦₈ _), ← sepConj_assoc (((out + 120#64) ↦₈ _) ∗ _),
      show ((out + 120#64) ↦₈ loByte dw.g0.u8 ∗
        (out + 121#64) ↦₆₄ unshiftWord dw.g0.u8 (loByte dw.g0.w16)) ∗
        (out + 129#64) ↦ₛ hiBytes7 dw.g0.w16 =
        ((out + 120#64) ↦₈ loByte dw.g0.u8) ∗
        ((out + 121#64) ↦₆₄ unshiftWord dw.g0.u8 (loByte dw.g0.w16)) ∗
        ((out + 129#64) ↦ₛ hiBytes7 dw.g0.w16) by ac_rfl,
      v4c_out_120_recombine out dw.g0.u8 dw.g0.w16,
      ← sepConj_assoc ((out + 144#64) ↦₈ _), ← sepConj_assoc (((out + 144#64) ↦₈ _) ∗ _),
      ← sepConj_assoc ((((out + 144#64) ↦₈ _) ∗ _) ∗ _),
      show (((out + 144#64) ↦₈ loByte dw.g0.u32 ∗
        (out + 145#64) ↦₆₄ unshiftWord dw.g0.u32 (loByte dw.g0.u40)) ∗
        (out + 153#64) ↦ₛ hiBytes7 dw.g0.u40) ∗
        (out + 160#64) ↦₆₄ dw.g0.u48 =
        ((out + 144#64) ↦₈ loByte dw.g0.u32) ∗
        ((out + 145#64) ↦₆₄ unshiftWord dw.g0.u32 (loByte dw.g0.u40)) ∗
        ((out + 153#64) ↦ₛ hiBytes7 dw.g0.u40) ∗
        ((out + 160#64) ↦₆₄ dw.g0.u48) by ac_rfl,
      v4c_out_144_recombine out dw.g0.u32 dw.g0.u40 dw.g0.u48]
  exact Entails.of_eq (by ac_rfl)

theorem v4c_memRegion_224_to_ucSpillSlots (fsp : BitVec 64) :
    memRegion fsp 224 ⊢
      ∃∗ v32 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v48 : BitVec 64,
      ∃∗ v56 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v80 : BitVec 64,
      ∃∗ v128 : BitVec 64, ∃∗ v136 : BitVec 64, ∃∗ v144 : BitVec 64,
      ∃∗ v216 : BitVec 64,
        memRegion fsp 32 ∗
        memRegion (fsp + 64#64) 8 ∗
        memRegion (fsp + 88#64) 40 ∗
        memRegion (fsp + 152#64) 64 ∗
        v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 := by
  have hsplit : memRegion fsp 224 ⊢
      memRegion fsp 32 ∗
      (∃∗ v32 : BitVec 64, (fsp + 32#64) ↦₆₄ v32) ∗
      (∃∗ v40 : BitVec 64, (fsp + 40#64) ↦₆₄ v40) ∗
      (∃∗ v48 : BitVec 64, (fsp + 48#64) ↦₆₄ v48) ∗
      (∃∗ v56 : BitVec 64, (fsp + 56#64) ↦₆₄ v56) ∗
      memRegion (fsp + 64#64) 8 ∗
      (∃∗ v72 : BitVec 64, (fsp + 72#64) ↦₆₄ v72) ∗
      (∃∗ v80 : BitVec 64, (fsp + 80#64) ↦₆₄ v80) ∗
      memRegion (fsp + 88#64) 40 ∗
      (∃∗ v128 : BitVec 64, (fsp + 128#64) ↦₆₄ v128) ∗
      (∃∗ v136 : BitVec 64, (fsp + 136#64) ↦₆₄ v136) ∗
      (∃∗ v144 : BitVec 64, (fsp + 144#64) ↦₆₄ v144) ∗
      memRegion (fsp + 152#64) 64 ∗
      (∃∗ v216 : BitVec 64, (fsp + 216#64) ↦₆₄ v216) := by
    exact split_top <|
      split_step0 (Entails.refl _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (Entails.refl _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (Entails.refl _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (Entails.refl _) <| mem64_entails _
  refine Entails.trans hsplit ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro v216
  apply Entails.sepExists_elim; intro v144
  apply Entails.sepExists_elim; intro v136
  apply Entails.sepExists_elim; intro v128
  apply Entails.sepExists_elim; intro v80
  apply Entails.sepExists_elim; intro v72
  apply Entails.sepExists_elim; intro v56
  apply Entails.sepExists_elim; intro v48
  apply Entails.sepExists_elim; intro v40
  apply Entails.sepExists_elim; intro v32
  refine Entails.sepExists_right v32 (Entails.sepExists_right v40
    (Entails.sepExists_right v48 (Entails.sepExists_right v56
      (Entails.sepExists_right v72 (Entails.sepExists_right v80
        (Entails.sepExists_right v128 (Entails.sepExists_right v136
          (Entails.sepExists_right v144 (Entails.sepExists_right v216 ?_)))))))))
  unfold v4c_ucSpillSlots
  exact Entails.of_eq (by ac_rfl)

theorem v4c_ucSpillSlots_collapse_224 (fsp : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 : BitVec 64) :
    memRegion fsp 32 ∗
      memRegion (fsp + 64#64) 8 ∗
      memRegion (fsp + 88#64) 40 ∗
      memRegion (fsp + 152#64) 64 ∗
      v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ⊢
    memRegion fsp 224 := by
  unfold v4c_ucSpillSlots
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion fsp 32 ∗
    ((fsp + 32#64) ↦₆₄ v32) ∗
    ((fsp + 40#64) ↦₆₄ v40) ∗
    ((fsp + 48#64) ↦₆₄ v48) ∗
    ((fsp + 56#64) ↦₆₄ v56) ∗
    memRegion (fsp + 64#64) 8 ∗
    ((fsp + 72#64) ↦₆₄ v72) ∗
    ((fsp + 80#64) ↦₆₄ v80) ∗
    memRegion (fsp + 88#64) 40 ∗
    ((fsp + 128#64) ↦₆₄ v128) ∗
    ((fsp + 136#64) ↦₆₄ v136) ∗
    ((fsp + 144#64) ↦₆₄ v144) ∗
    memRegion (fsp + 152#64) 64 ∗
    ((fsp + 216#64) ↦₆₄ v216) by ac_rfl)) ?_
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| Drop.pointsTo64_entails_memRegion _ _

theorem v4c_memRegion_1652_split_896 (fsp : BitVec 64) :
    memRegion (fsp + 236#64) 1652 ⊢
      ∃∗ s896 : BitVec 64, ∃∗ s904 : BitVec 64, ∃∗ s912 : BitVec 64,
      ∃∗ s920 : BitVec 32, ∃∗ s924 : BitVec 32, ∃∗ s928 : BitVec 64,
        memRegion (fsp + 236#64) 660 ∗
        v4b_optProtoPolyDecoderWordsAt (fsp + 896#64) s896 s904 s912 s920 s924 s928 ∗
        memRegion (fsp + 936#64) 952 := by
  have hsplit : memRegion (fsp + 236#64) 1652 ⊢
      memRegion (fsp + 236#64) 660 ∗
      (∃∗ s896 : BitVec 64, (fsp + 896#64) ↦₆₄ s896) ∗
      (∃∗ s904 : BitVec 64, (fsp + 904#64) ↦₆₄ s904) ∗
      (∃∗ s912 : BitVec 64, (fsp + 912#64) ↦₆₄ s912) ∗
      (∃∗ s920 : BitVec 32, (fsp + 920#64) ↦₃₂ s920) ∗
      (∃∗ s924 : BitVec 32, (fsp + 924#64) ↦₃₂ s924) ∗
      (∃∗ s928 : BitVec 64, (fsp + 928#64) ↦₆₄ s928) ∗
      memRegion (fsp + 936#64) 952 := by
    exact split_top <|
      split_step (Entails.refl _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem32_entails _) <| split_step (mem32_entails _) <|
      split_step (mem64_entails _) <| Entails.refl _
  refine Entails.trans hsplit ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro s928
  apply Entails.sepExists_elim; intro s924
  apply Entails.sepExists_elim; intro s920
  apply Entails.sepExists_elim; intro s912
  apply Entails.sepExists_elim; intro s904
  apply Entails.sepExists_elim; intro s896
  refine Entails.sepExists_right s896 (Entails.sepExists_right s904
    (Entails.sepExists_right s912 (Entails.sepExists_right s920
      (Entails.sepExists_right s924 (Entails.sepExists_right s928 ?_)))))
  unfold v4b_optProtoPolyDecoderWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem v4c_memRegion_660_40_952_entails_1652 (fsp : BitVec 64) :
    memRegion (fsp + 236#64) 660 ∗ memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952 ⊢
      memRegion (fsp + 236#64) 1652 := by
  exact collapse_top <|
    collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _

theorem v4c_ucWords_312_entails_400_16 (fsp : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) :
    v4b_optProtoUcWordsAt (fsp + 1888#64) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 ∗
      memRegion (fsp + 1992#64) 312 ⊢
    memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16 := by
  have h104 := v4b_optProtoUcWordsAt_entails_104 (fsp + 1888#64)
    w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96
  have hsplit : memRegion (fsp + 1992#64) 312 ⊢
      memRegion (fsp + 1992#64) 296 ∗ memRegion (fsp + 2288#64) 16 := by
    exact split_top <| split_step (Entails.refl _) <| Entails.refl _
  refine Entails.trans (sepConj_mono h104 hsplit) ?_
  rw [← sepConj_assoc]
  refine sepConj_mono_left ?_
  exact collapse_top <| collapse_step (Entails.refl _) <| Entails.refl _

theorem v4c_err_8500_stack_collapse (fsp : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 d32 : BitVec 64) (d28 : BitVec 32) :
    memRegion fsp 32 ∗
      memRegion (fsp + 64#64) 8 ∗
      memRegion (fsp + 88#64) 40 ∗
      memRegion (fsp + 152#64) 64 ∗
      v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ∗
      ((fsp + 224#64) ↦₆₄ d32) ∗
      ((fsp + 232#64) ↦₃₂ d28) ∗
      memRegion (fsp + 236#64) 1652 ∗
      memRegion (fsp + 1888#64) 400 ∗
      memRegion (fsp + 2288#64) 16 ⊢
    memRegion fsp 2304 := by
  have h224 := v4c_ucSpillSlots_collapse_224 fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216
  refine Entails.trans
    (Entails.of_eq (show _ =
      (memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
       memRegion (fsp + 152#64) 64 ∗ v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216) ∗
      ((fsp + 224#64) ↦₆₄ d32) ∗
      ((fsp + 232#64) ↦₃₂ d28) ∗
      memRegion (fsp + 236#64) 1652 ∗
      memRegion (fsp + 1888#64) 400 ∗
      memRegion (fsp + 2288#64) 16 by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left h224) ?_
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v4c_memRegion_loBytes7_gap_at (a o1 o2 : BitVec 64) (k : Nat)
    (ho : o1 + 7#64 = o2 := by rfl)
    (hk : 8 + k ≤ 2 ^ 64 := by decide) :
    ProofLib.memRegion (a + o1) (7 + (1 + k)) ⊢
      (∃∗ u0 : BitVec 64, ((a + o1) ↦ₛ EncoderFromPb.loBytes7 u0)) ∗
      ProofLib.memRegion (a + o2) (1 + k) := by
  have h1 : 7 + (1 + k) = 8 + k := by omega
  rw [h1, ProofLib.memRegion_split' (b := a + o1) (n := 8) (k := k)
    (b' := a + o1 + 8#64) rfl rfl hk,
    ProofLib.memRegion_eight (a + o1), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro u0
  rw [pointsTo64_split_7_1 (a + o1) u0, sepConj_assoc, sepExists_sepConj_left]
  refine Entails.sepExists_right u0 (sepConj_mono_right ?_)
  have ha7 : a + o1 + 7#64 = a + o2 := by rw [BitVec.add_assoc, ho]
  have ha8 : a + o1 + 8#64 = a + o2 + 1#64 := by rw [← ha7]; bv_omega
  rw [ha7, ha8, ProofLib.memRegion_split' (b := a + o2) (n := 1) (k := k)
    (b' := a + o2 + 1#64) rfl rfl (by omega)]
  exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)

theorem v4c_ok_2472_stack_split (fsp d32 : BitVec 64) (d28 : BitVec 32) :
    memRegion (fsp + 152#64) 64 ∗
      ((fsp + 224#64) ↦₆₄ d32) ∗
      ((fsp + 232#64) ↦₃₂ d28) ∗
      memRegion (fsp + 236#64) 1652 ⊢
    ∃∗ w160 : BitVec 64, ∃∗ d172 : BitVec 32, ∃∗ w192 : BitVec 64,
    ∃∗ w208 : BitVec 64, ∃∗ w224 : BitVec 64, ∃∗ w232 : BitVec 64,
    ∃∗ q608 : BitVec 128, ∃∗ q624 : BitVec 128, ∃∗ q640 : BitVec 128, ∃∗ q656 : BitVec 128,
    ∃∗ q672 : BitVec 128, ∃∗ q688 : BitVec 128, ∃∗ q704 : BitVec 128, ∃∗ q720 : BitVec 128,
    ∃∗ q736 : BitVec 128, ∃∗ q752 : BitVec 128, ∃∗ q768 : BitVec 128, ∃∗ q784 : BitVec 128,
    ∃∗ q800 : BitVec 128, ∃∗ q816 : BitVec 128,
    ∃∗ w832 : BitVec 64, ∃∗ q848 : BitVec 128, ∃∗ w864 : BitVec 64,
    ∃∗ w880 : BitVec 64, ∃∗ w888 : BitVec 64,
      v4c_destStackSlots fsp w160 d172 w192 w208 w224 w232
        q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
        w832 q848 w864 w880 w888 ∗
      memRegion (fsp + 152#64) 8 ∗
      memRegion (fsp + 168#64) 4 ∗
      memRegion (fsp + 176#64) 16 ∗
      memRegion (fsp + 200#64) 8 ∗
      memRegion (fsp + 240#64) 368 ∗
      memRegion (fsp + 840#64) 8 ∗
      memRegion (fsp + 871#64) 9 ∗
      memRegion (fsp + 895#64) 993 := by
  have h152 : memRegion (fsp + 152#64) 64 ⊢
      memRegion (fsp + 152#64) 8 ∗
      (∃∗ w160 : BitVec 64, (fsp + 160#64) ↦₆₄ w160) ∗
      memRegion (fsp + 168#64) 4 ∗
      (∃∗ d172 : BitVec 32, (fsp + 172#64) ↦₃₂ d172) ∗
      memRegion (fsp + 176#64) 16 ∗
      (∃∗ w192 : BitVec 64, (fsp + 192#64) ↦₆₄ w192) ∗
      memRegion (fsp + 200#64) 8 ∗
      (∃∗ w208 : BitVec 64, (fsp + 208#64) ↦₆₄ w208) := by
    exact split_top <|
      split_step (Entails.refl _) <| split_step (mem64_entails _) <|
      split_step (Entails.refl _) <| split_step (mem32_entails _) <|
      split_step (Entails.refl _) <| split_step (mem64_entails _) <|
      split_step (Entails.refl _) <| mem64_entails _
  have h224_col : ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗ memRegion (fsp + 236#64) 1652 ⊢
      memRegion (fsp + 224#64) 1664 := by
    exact collapse_top <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
      Entails.refl _
  have h224 : memRegion (fsp + 224#64) 1664 ⊢
      (∃∗ w224 : BitVec 64, (fsp + 224#64) ↦₆₄ w224) ∗
      (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 368 ∗
      (∃∗ q608 : BitVec 128, (fsp + 608#64) ↦₁₂₈ q608) ∗
      (∃∗ q624 : BitVec 128, (fsp + 624#64) ↦₁₂₈ q624) ∗
      (∃∗ q640 : BitVec 128, (fsp + 640#64) ↦₁₂₈ q640) ∗
      (∃∗ q656 : BitVec 128, (fsp + 656#64) ↦₁₂₈ q656) ∗
      (∃∗ q672 : BitVec 128, (fsp + 672#64) ↦₁₂₈ q672) ∗
      (∃∗ q688 : BitVec 128, (fsp + 688#64) ↦₁₂₈ q688) ∗
      (∃∗ q704 : BitVec 128, (fsp + 704#64) ↦₁₂₈ q704) ∗
      (∃∗ q720 : BitVec 128, (fsp + 720#64) ↦₁₂₈ q720) ∗
      (∃∗ q736 : BitVec 128, (fsp + 736#64) ↦₁₂₈ q736) ∗
      (∃∗ q752 : BitVec 128, (fsp + 752#64) ↦₁₂₈ q752) ∗
      (∃∗ q768 : BitVec 128, (fsp + 768#64) ↦₁₂₈ q768) ∗
      (∃∗ q784 : BitVec 128, (fsp + 784#64) ↦₁₂₈ q784) ∗
      (∃∗ q800 : BitVec 128, (fsp + 800#64) ↦₁₂₈ q800) ∗
      (∃∗ q816 : BitVec 128, (fsp + 816#64) ↦₁₂₈ q816) ∗
      (∃∗ w832 : BitVec 64, (fsp + 832#64) ↦₆₄ w832) ∗
      memRegion (fsp + 840#64) 8 ∗
      (∃∗ q848 : BitVec 128, (fsp + 848#64) ↦₁₂₈ q848) ∗
      ((∃∗ w864 : BitVec 64, (fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
        memRegion (fsp + 871#64) 9) ∗
      (∃∗ w880 : BitVec 64, (fsp + 880#64) ↦₆₄ w880) ∗
      ((∃∗ w888 : BitVec 64, (fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗
        memRegion (fsp + 895#64) 993) := by
    exact split_top <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem64_entails _) <| split_step (Entails.refl _) <|
      split_step (mem128_entails _) <|
      split_step (v4c_memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <|
      split_step (mem64_entails _) <|
      v4c_memRegion_loBytes7_gap_at fsp 888#64 895#64 992
  refine Entails.trans (sepConj_mono h152 (Entails.trans h224_col h224)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w888
  apply Entails.sepExists_elim; intro w880
  apply Entails.sepExists_elim; intro w864
  apply Entails.sepExists_elim; intro q848
  apply Entails.sepExists_elim; intro w832
  apply Entails.sepExists_elim; intro q816
  apply Entails.sepExists_elim; intro q800
  apply Entails.sepExists_elim; intro q784
  apply Entails.sepExists_elim; intro q768
  apply Entails.sepExists_elim; intro q752
  apply Entails.sepExists_elim; intro q736
  apply Entails.sepExists_elim; intro q720
  apply Entails.sepExists_elim; intro q704
  apply Entails.sepExists_elim; intro q688
  apply Entails.sepExists_elim; intro q672
  apply Entails.sepExists_elim; intro q656
  apply Entails.sepExists_elim; intro q640
  apply Entails.sepExists_elim; intro q624
  apply Entails.sepExists_elim; intro q608
  apply Entails.sepExists_elim; intro w232
  apply Entails.sepExists_elim; intro w224
  apply Entails.sepExists_elim; intro w208
  apply Entails.sepExists_elim; intro w192
  apply Entails.sepExists_elim; intro d172
  apply Entails.sepExists_elim; intro w160
  refine Entails.sepExists_right w160 (Entails.sepExists_right d172
    (Entails.sepExists_right w192 (Entails.sepExists_right w208
      (Entails.sepExists_right w224 (Entails.sepExists_right w232
        (Entails.sepExists_right q608 (Entails.sepExists_right q624
          (Entails.sepExists_right q640 (Entails.sepExists_right q656
            (Entails.sepExists_right q672 (Entails.sepExists_right q688
              (Entails.sepExists_right q704 (Entails.sepExists_right q720
                (Entails.sepExists_right q736 (Entails.sepExists_right q752
                  (Entails.sepExists_right q768 (Entails.sepExists_right q784
                    (Entails.sepExists_right q800 (Entails.sepExists_right q816
                      (Entails.sepExists_right w832 (Entails.sepExists_right q848
                        (Entails.sepExists_right w864 (Entails.sepExists_right w880
                          (Entails.sepExists_right w888 ?_))))))))))))))))))))))))
  unfold v4c_destStackSlots
  exact Entails.of_eq (by ac_rfl)

theorem v4c_triplesWordsAt_entails_memRegion
    (ts : List (BitVec 64 × BitVec 64 × BitVec 64)) (a : BitVec 64)
    (hle : ts.length * 24 ≤ 2 ^ 64) :
    v4c_triplesWordsAt a ts ⊢ memRegion a (ts.length * 24) := by
  induction ts generalizing a with
  | nil =>
    simp only [v4c_triplesWordsAt, List.length_nil, Nat.zero_mul, ProofLib.memRegion_zero]
    exact Entails.refl _
  | cons hd ts ih =>
    rcases hd with ⟨c, p, l⟩
    dsimp only [v4c_triplesWordsAt, List.length_cons] at hle ⊢
    have h24 : (a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l) ⊢ memRegion a 24 := by
      exact collapse_top <|
        collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
        collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
        Drop.pointsTo64_entails_memRegion _ _
    have htl : ts.length * 24 ≤ 2 ^ 64 := by omega
    have hrec := ih (a + 24#64) htl
    refine Entails.trans (Entails.of_eq (show
        (a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l) ∗ v4c_triplesWordsAt (a + 24#64) ts =
        ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l)) ∗ v4c_triplesWordsAt (a + 24#64) ts
        by ac_rfl))
      (Entails.trans (sepConj_mono h24 hrec) ?_)
    have hsplit : (ts.length + 1) * 24 = 24 + ts.length * 24 := by omega
    rw [hsplit, ProofLib.memRegion_split a 24 (ts.length * 24) (by omega)]
    exact Entails.refl _

theorem v4c_decWordsAt_entails_400 (a : BitVec 64) (dw : v4c_DecWords) :
    v4c_decWordsAt a dw ⊢ memRegion a 400 := by
  rw [← v4c_triplesWordsAt_decoderTriples_eq a dw]
  have h384 : v4c_triplesWordsAt a (v4c_decoderTriples dw) ⊢ memRegion a 384 :=
    v4c_triplesWordsAt_entails_memRegion (v4c_decoderTriples dw) a
      (by dsimp [v4c_decoderTriples]; decide)
  exact collapse_top <|
    collapse_step0 h384 <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v4c_memRegion_328_entails_bs (a : BitVec 64) :
    ProofLib.memRegion a 328 ⊢
      ∃∗ bs : { l : List (BitVec 8) // l.length = 328 }, (a ↦ₛ bs.val) := by
  rw [ProofLib.memRegion_eq_exists_bytes a 328 (by decide)]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  exact Entails.sepExists_right ⟨bs, hlen⟩ (Entails.refl _)

@[expose] def v4c_epilogueSlotsLo (fsp : BitVec 64) (d92 : BitVec 32) (w104 w112 w120 : BitVec 64) : SepProp :=
  ((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 104#64) ↦₆₄ w104) ∗
  ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120)

@[expose] def v4c_epilogueGapsLo (fsp : BitVec 64) : SepProp :=
  memRegion fsp 92 ∗ memRegion (fsp + 96#64) 8 ∗
  memRegion (fsp + 128#64) 32 ∗ memRegion (fsp + 216#64) 8

@[expose] def v4c_epilogueSlots240 (fsp : BitVec 64) (bs240 : List (BitVec 8))
    (q576 : BitVec 128) (w592 : BitVec 64) : SepProp :=
  ((fsp + 240#64) ↦ₛ bs240) ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗
  ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)

@[expose] def v4c_epilogueGaps240 (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 599#64) 9

@[expose] def v4c_epilogueSlots1888 (fsp : BitVec 64) (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) : SepProp :=
  ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
  ((fsp + 1920#64) ↦₆₄ w1920)

@[expose] def v4c_epilogueGapsFixed (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗
  memRegion (fsp + 200#64) 8 ∗ memRegion (fsp + 840#64) 8 ∗
  memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 993

theorem v4c_stack_lo_entails (fsp : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 : BitVec 64) :
    memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
      memRegion (fsp + 152#64) 8 ∗
      v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ⊢
    ∃∗ d92 : BitVec 32, ∃∗ w104 : BitVec 64, ∃∗ w112 : BitVec 64, ∃∗ w120 : BitVec 64,
      v4c_epilogueSlotsLo fsp d92 w104 w112 w120 ∗ v4c_epilogueGapsLo fsp := by
  unfold v4c_ucSpillSlots
  have h160 : memRegion fsp 32 ∗ ((fsp + 32#64) ↦₆₄ v32) ∗ ((fsp + 40#64) ↦₆₄ v40) ∗
      ((fsp + 48#64) ↦₆₄ v48) ∗ ((fsp + 56#64) ↦₆₄ v56) ∗ memRegion (fsp + 64#64) 8 ∗
      ((fsp + 72#64) ↦₆₄ v72) ∗ ((fsp + 80#64) ↦₆₄ v80) ∗ memRegion (fsp + 88#64) 40 ∗
      ((fsp + 128#64) ↦₆₄ v128) ∗ ((fsp + 136#64) ↦₆₄ v136) ∗ ((fsp + 144#64) ↦₆₄ v144) ∗
      memRegion (fsp + 152#64) 8 ⊢ memRegion fsp 160 := by
    exact collapse_top <|
      collapse_step0 (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Entails.refl _
  have h160_split : memRegion fsp 160 ⊢
      memRegion fsp 92 ∗
      (∃∗ d92 : BitVec 32, (fsp + 92#64) ↦₃₂ d92) ∗
      memRegion (fsp + 96#64) 8 ∗
      (∃∗ w104 : BitVec 64, (fsp + 104#64) ↦₆₄ w104) ∗
      (∃∗ w112 : BitVec 64, (fsp + 112#64) ↦₆₄ w112) ∗
      (∃∗ w120 : BitVec 64, (fsp + 120#64) ↦₆₄ w120) ∗
      memRegion (fsp + 128#64) 32 := by
    exact split_top <|
      split_step0 (Entails.refl _) <| split_step (mem32_entails _) <|
      split_step (Entails.refl _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion fsp 32 ∗ ((fsp + 32#64) ↦₆₄ v32) ∗ ((fsp + 40#64) ↦₆₄ v40) ∗
     ((fsp + 48#64) ↦₆₄ v48) ∗ ((fsp + 56#64) ↦₆₄ v56) ∗ memRegion (fsp + 64#64) 8 ∗
     ((fsp + 72#64) ↦₆₄ v72) ∗ ((fsp + 80#64) ↦₆₄ v80) ∗ memRegion (fsp + 88#64) 40 ∗
     ((fsp + 128#64) ↦₆₄ v128) ∗ ((fsp + 136#64) ↦₆₄ v136) ∗ ((fsp + 144#64) ↦₆₄ v144) ∗
     memRegion (fsp + 152#64) 8) ∗ ((fsp + 216#64) ↦₆₄ v216) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono (Entails.trans h160 h160_split)
    (Drop.pointsTo64_entails_memRegion _ _)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w120
  apply Entails.sepExists_elim; intro w112
  apply Entails.sepExists_elim; intro w104
  apply Entails.sepExists_elim; intro d92
  refine Entails.sepExists_right d92 (Entails.sepExists_right w104
    (Entails.sepExists_right w112 (Entails.sepExists_right w120 ?_)))
  unfold v4c_epilogueSlotsLo v4c_epilogueGapsLo
  exact Entails.of_eq (by ac_rfl)

theorem v4c_stack_240_entails (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 368 ⊢
    ∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 },
    ∃∗ q576 : BitVec 128, ∃∗ w592 : BitVec 64,
      v4c_epilogueSlots240 fsp bs240.val q576 w592 ∗ v4c_epilogueGaps240 fsp := by
  have h240 : memRegion (fsp + 240#64) 368 ⊢
      (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, (fsp + 240#64) ↦ₛ bs240.val) ∗
      memRegion (fsp + 568#64) 8 ∗
      (∃∗ q576 : BitVec 128, (fsp + 576#64) ↦₁₂₈ q576) ∗
      ((∃∗ w592 : BitVec 64, (fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
        memRegion (fsp + 599#64) 9) := by
    exact split_top <|
      split_step (v4c_memRegion_328_entails_bs _) <| split_step (Entails.refl _) <|
      split_step (mem128_entails _) <|
      v4c_memRegion_loBytes7_gap_at fsp 592#64 599#64 8
  refine Entails.trans h240 ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w592
  apply Entails.sepExists_elim; intro q576
  apply Entails.sepExists_elim; intro bs240
  refine Entails.sepExists_right bs240 (Entails.sepExists_right q576
    (Entails.sepExists_right w592 ?_))
  unfold v4c_epilogueSlots240 v4c_epilogueGaps240
  exact Entails.of_eq (by ac_rfl)

theorem v4c_stack_1888_entails (fsp : BitVec 64) (dw : v4c_DecWords) :
    v4c_decWordsAt (fsp + 1888#64) dw ∗ memRegion (fsp + 2288#64) 16 ⊢
    ∃∗ q1888 : BitVec 128, ∃∗ q1904 : BitVec 128, ∃∗ w1920 : BitVec 64,
      v4c_epilogueSlots1888 fsp q1888 q1904 w1920 ∗ memRegion (fsp + 1928#64) 376 := by
  have h416 : v4c_decWordsAt (fsp + 1888#64) dw ∗ memRegion (fsp + 2288#64) 16 ⊢
      memRegion (fsp + 1888#64) 416 := by
    exact collapse_top <|
      collapse_step (v4c_decWordsAt_entails_400 (fsp + 1888#64) dw) <|
      Entails.refl _
  have hsplit : memRegion (fsp + 1888#64) 416 ⊢
      (∃∗ q1888 : BitVec 128, (fsp + 1888#64) ↦₁₂₈ q1888) ∗
      (∃∗ q1904 : BitVec 128, (fsp + 1904#64) ↦₁₂₈ q1904) ∗
      (∃∗ w1920 : BitVec 64, (fsp + 1920#64) ↦₆₄ w1920) ∗
      memRegion (fsp + 1928#64) 376 := by
    exact split_top <|
      split_step (mem128_entails _) <| split_step (mem128_entails _) <|
      split_step (mem64_entails _) <| Entails.refl _
  refine Entails.trans h416 (Entails.trans hsplit ?_)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w1920
  apply Entails.sepExists_elim; intro q1904
  apply Entails.sepExists_elim; intro q1888
  refine Entails.sepExists_right q1888 (Entails.sepExists_right q1904
    (Entails.sepExists_right w1920 ?_))
  unfold v4c_epilogueSlots1888
  exact Entails.of_eq (by ac_rfl)

theorem v4c_epilogueStackSlots_eq (fsp : BitVec 64)
    (d92 d172 : BitVec 32) (w104 w112 w120 w160 w192 w208 w224 w232 : BitVec 64)
    (bs240 : List (BitVec 8)) (q576 : BitVec 128) (w592 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) :
    v4c_epilogueSlotsLo fsp d92 w104 w112 w120 ∗
      v4c_destStackSlots fsp w160 d172 w192 w208 w224 w232
        q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
        w832 q848 w864 w880 w888 ∗
      v4c_epilogueSlots240 fsp bs240 q576 w592 ∗
      v4c_epilogueSlots1888 fsp q1888 q1904 w1920 =
    epilogueStackSlots fsp
      d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240
      q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      w832 q848 w864 w880 w888 q1888 q1904 w1920 := by
  unfold v4c_epilogueSlotsLo v4c_destStackSlots v4c_epilogueSlots240 v4c_epilogueSlots1888 epilogueStackSlots
  ac_rfl

theorem v4c_epilogueStackGaps_eq (fsp : BitVec 64) :
    v4c_epilogueGapsLo fsp ∗ v4c_epilogueGaps240 fsp ∗
      v4c_epilogueGapsFixed fsp ∗ memRegion (fsp + 1928#64) 376 =
    epilogueStackGaps fsp := by
  unfold v4c_epilogueGapsLo v4c_epilogueGaps240 v4c_epilogueGapsFixed epilogueStackGaps
  ac_rfl

attribute [local irreducible]
  epilogueStackSlots epilogueStackGaps
  v4c_destStackSlots v4c_ucSpillSlots v4c_decWordsAt
  v4c_epilogueSlotsLo v4c_epilogueGapsLo
  v4c_epilogueSlots240 v4c_epilogueGaps240
  v4c_epilogueSlots1888

theorem v4c_ok_8180_stack_rearrange (fsp : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 : BitVec 64)
    (w160 : BitVec 64) (d172 : BitVec 32) (w192 w208 w224 w232 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (dw : v4c_DecWords) :
    memRegion fsp 32 ∗
      memRegion (fsp + 64#64) 8 ∗
      memRegion (fsp + 88#64) 40 ∗
      memRegion (fsp + 152#64) 8 ∗
      v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ∗
      v4c_destStackSlots fsp w160 d172 w192 w208 w224 w232
        q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
        w832 q848 w864 w880 w888 ∗
      memRegion (fsp + 168#64) 4 ∗
      memRegion (fsp + 176#64) 16 ∗
      memRegion (fsp + 200#64) 8 ∗
      memRegion (fsp + 240#64) 368 ∗
      memRegion (fsp + 840#64) 8 ∗
      memRegion (fsp + 871#64) 9 ∗
      memRegion (fsp + 895#64) 993 ∗
      v4c_decWordsAt (fsp + 1888#64) dw ∗
      memRegion (fsp + 2288#64) 16 =
    (memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
     memRegion (fsp + 152#64) 8 ∗ v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216) ∗
    memRegion (fsp + 240#64) 368 ∗
    (v4c_decWordsAt (fsp + 1888#64) dw ∗ memRegion (fsp + 2288#64) 16) ∗
    (v4c_destStackSlots fsp w160 d172 w192 w208 w224 w232
       q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
       w832 q848 w864 w880 w888 ∗
     v4c_epilogueGapsFixed fsp) := by
  unfold v4c_epilogueGapsFixed
  ac_rfl

attribute [local irreducible] v4c_epilogueGapsFixed

theorem v4c_sepExists_pull_left {α : Type} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x, P x ∗ Q ⊢ R) : (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [sepExists_sepConj_left]
  exact Entails.sepExists_elim h

theorem v4c_sepExists_pull_mid {α : Type} {A : SepProp} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x, A ∗ P x ∗ Q ⊢ R) : A ∗ (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim h

theorem v4c_ok_8180_stack_to_epilogue (fsp : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 : BitVec 64)
    (w160 : BitVec 64) (d172 : BitVec 32) (w192 w208 w224 w232 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (dw : v4c_DecWords) :
    memRegion fsp 32 ∗
      memRegion (fsp + 64#64) 8 ∗
      memRegion (fsp + 88#64) 40 ∗
      memRegion (fsp + 152#64) 8 ∗
      v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ∗
      v4c_destStackSlots fsp w160 d172 w192 w208 w224 w232
        q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
        w832 q848 w864 w880 w888 ∗
      memRegion (fsp + 168#64) 4 ∗
      memRegion (fsp + 176#64) 16 ∗
      memRegion (fsp + 200#64) 8 ∗
      memRegion (fsp + 240#64) 368 ∗
      memRegion (fsp + 840#64) 8 ∗
      memRegion (fsp + 871#64) 9 ∗
      memRegion (fsp + 895#64) 993 ∗
      v4c_decWordsAt (fsp + 1888#64) dw ∗
      memRegion (fsp + 2288#64) 16 ⊢
    ∃∗ d92 : BitVec 32, ∃∗ w104 : BitVec 64, ∃∗ w112 : BitVec 64, ∃∗ w120 : BitVec 64,
    ∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 },
    ∃∗ q576 : BitVec 128, ∃∗ w592 : BitVec 64,
    ∃∗ q1888 : BitVec 128, ∃∗ q1904 : BitVec 128, ∃∗ w1920 : BitVec 64,
      epilogueStackSlots fsp
        d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240.val
        q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
        w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
      epilogueStackGaps fsp := by
  rw [v4c_ok_8180_stack_rearrange]
  refine Entails.trans (sepConj_mono
    (v4c_stack_lo_entails fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216)
    (sepConj_mono (v4c_stack_240_entails fsp)
      (sepConj_mono_left (v4c_stack_1888_entails fsp dw)))) ?_
  apply v4c_sepExists_pull_left; intro d92
  apply v4c_sepExists_pull_left; intro w104
  apply v4c_sepExists_pull_left; intro w112
  apply v4c_sepExists_pull_left; intro w120
  apply v4c_sepExists_pull_mid; intro bs240
  apply v4c_sepExists_pull_mid; intro q576
  apply v4c_sepExists_pull_mid; intro w592
  rw [← sepConj_assoc]
  apply v4c_sepExists_pull_mid; intro q1888
  apply v4c_sepExists_pull_mid; intro q1904
  apply v4c_sepExists_pull_mid; intro w1920
  refine Entails.sepExists_right d92 (Entails.sepExists_right w104
    (Entails.sepExists_right w112 (Entails.sepExists_right w120
      (Entails.sepExists_right bs240 (Entails.sepExists_right q576
        (Entails.sepExists_right w592 (Entails.sepExists_right q1888
          (Entails.sepExists_right q1904 (Entails.sepExists_right w1920 ?_)))))))))
  rw [← v4c_epilogueStackSlots_eq, ← v4c_epilogueStackGaps_eq]
  exact Entails.of_eq (by ac_rfl)

theorem v4c_wp_exists_left {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {Q : SepProp} {post : State → SepProp → Prop}
    (h : ∀ x, SepWP prog target_pc s (P x ∗ Q) post) :
    SepWP prog target_pc s ((∃∗ x, P x) ∗ Q) post := by
  rw [sepExists_sepConj_left]
  exact ProofLib.SepWP.exists_left h

theorem v4c_decHeap_entails_w0_lt (A : RustAlloc) (dec : PolyDecoder) (dw : v4c_DecWords) :
    v4c_decHeap A dec dw ⊢ ⌜dw.g0.w0.toNat < 2 ^ 63⌝ ∗ v4c_decHeap A dec dw := by
  unfold v4c_decHeap
  apply Entails.pure_left; rintro ⟨h1, h2, hw0, h4, h5⟩
  exact Entails.pure_right hw0 (Entails.pure_right ⟨h1, h2, hw0, h4, h5⟩ (Entails.refl _))

theorem v4c_ekSentCt1ReceivedHeap_entails_dealloc4 (A : RustAlloc) {F : ShaCompress}
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    v4b_ekSentCt1ReceivedHeap A
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ⊢
      vecCapPtrDealloc A rkCap rkPtr ∗
      vecCapPtrDealloc A mkCap mkPtr ∗
      vecCapPtrDealloc A dkCap dkPtr ∗
      vecCapPtrDealloc A ct1Cap ct1Ptr :=
  Entails.trans
    (v4b_ekSentCt1ReceivedHeap_entails_dealloc A
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc)
    (Entails.pure_left fun _ => Entails.refl _)

end CryptoVerification.SpqrV1.States.FromPb

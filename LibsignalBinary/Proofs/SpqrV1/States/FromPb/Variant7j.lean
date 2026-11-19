/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7i -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7g -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7h
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 7 (`Ct1Sampled`, `+1056`) Part J

Final epilogue output assembly `v7_epilogueOutFull_entails_ct1Sampled` and the
complete `+7404 (.ok dec) -> s0.x30` return path `v7_dec_ok_7404_to_ret` for
`InnerState.ct1Sampled`.
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

/-! ## 1. Reassembly of `polyEncoderAt A out enc` (`out + 0 .. out + 400`) -/

theorem v7_out_96_realign (out w88 : BitVec 64) :
    ((out + 96#64) ↦₈ w88.extractLsb' 0 8) ∗
      ((out + 97#64) ↦₃₂ w88.extractLsb' 8 32) ∗
      ((out + 101#64) ↦₁₆ w88.extractLsb' 40 16) ∗
      ((out + 103#64) ↦₈ w88.extractLsb' 56 8) =
    (out + 96#64) ↦₆₄ w88 := by
  have h := (v7_pointsTo64_split_1_4_2_1 (out + 96#64) w88).symm
  have ha97 : (out + 96#64) + 1#64 = out + 97#64 := by bv_omega
  have ha101 : (out + 96#64) + 5#64 = out + 101#64 := by bv_omega
  have ha103 : (out + 96#64) + 7#64 = out + 103#64 := by bv_omega
  rw [ha97, ha101, ha103] at h
  exact h

theorem v7_out_120_realign (out w112 w120 : BitVec 64) :
    ((out + 120#64) ↦₈ loByte w112) ∗
      ((out + 121#64) ↦₆₄ unshiftWord w112 (loByte w120)) ∗
      ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 (unshiftWord w112 (loByte w120)) (w120 >>> 8))) =
    ((out + 120#64) ↦₆₄ w112) ∗ ((out + 128#64) ↦₆₄ w120) := by
  rw [v7_overlapWord7_unshift_lsr8 w112 w120]
  have h := (pair64_to_byte_word_tail7 (out + 120#64) w112 w120).symm
  have ha121 : (out + 120#64) + 1#64 = out + 121#64 := by bv_omega
  have ha129 : (out + 120#64) + 9#64 = out + 129#64 := by bv_omega
  have ha128 : (out + 120#64) + 8#64 = out + 128#64 := by bv_omega
  rw [ha121, ha129, ha128] at h
  exact h

theorem v7_out_144_realign (out w136 w144 w152 : BitVec 64) :
    ((out + 144#64) ↦₈ ((loByte w136).zeroExtend 32).setWidth 8) ∗
      ((out + 145#64) ↦₆₄ (v7_midQ128 w136 w144 w152).extractLsb' 0 64) ∗
      ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v7_midQ128 w136 w144 w152).extractLsb' 64 64)) ∗
      ((out + 160#64) ↦₆₄
        overlapWord7 ((v7_midQ128 w136 w144 w152).extractLsb' 64 64) (w152 >>> 8)) =
    ((out + 144#64) ↦₆₄ w136) ∗ ((out + 152#64) ↦₆₄ w144) ∗ ((out + 160#64) ↦₆₄ w152) := by
  rw [v7_zext32_setWidth8 (loByte w136)]
  have hlo : (v7_midQ128 w136 w144 w152).extractLsb' 0 64 = unshiftWord w136 (loByte w144) := by
    unfold v7_midQ128; bv_kernel
  have hhi : (v7_midQ128 w136 w144 w152).extractLsb' 64 64 = unshiftWord w144 (loByte w152) := by
    unfold v7_midQ128; bv_kernel
  rw [hlo, hhi, v7_overlapWord7_unshift_lsr8 w144 w152]
  have hdst := v7_byte_qword_lo7_word_eq_triple64 (out + 144#64) w136 w144 w152
  have hd145 : (out + 144#64) + 1#64 = out + 145#64 := by bv_omega
  have hd153 : (out + 144#64) + 9#64 = out + 153#64 := by bv_omega
  have hd160 : (out + 144#64) + 16#64 = out + 160#64 := by bv_omega
  have hd152 : (out + 144#64) + 8#64 = out + 152#64 := by bv_omega
  rw [hd145, hd153, hd160, hd152] at hdst
  exact hdst

theorem v7_out_8_to_392_eq_bs (out : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) :
    ((out + 8#64) ↦₆₄ v7_wordAt bs 0) ∗
      ((out + 16#64) ↦₆₄ v7_wordAt bs 8) ∗
      ((out + 24#64) ↦₆₄ v7_wordAt bs 16) ∗
      ((out + 32#64) ↦₆₄ v7_wordAt bs 24) ∗
      ((out + 40#64) ↦₆₄ v7_wordAt bs 32) ∗
      ((out + 48#64) ↦₆₄ v7_wordAt bs 40) ∗
      ((out + 56#64) ↦₆₄ v7_wordAt bs 48) ∗
      ((out + 64#64) ↦₆₄ v7_wordAt bs 56) ∗
      ((out + 72#64) ↦₆₄ v7_wordAt bs 64) ∗
      ((out + 80#64) ↦₆₄ v7_wordAt bs 72) ∗
      ((out + 88#64) ↦₆₄ v7_wordAt bs 80) ∗
      (((out + 96#64) ↦₈ (v7_wordAt bs 88).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v7_wordAt bs 88).extractLsb' 8 32) ∗
       ((out + 101#64) ↦₁₆ (v7_wordAt bs 88).extractLsb' 40 16) ∗
       ((out + 103#64) ↦₈ (v7_wordAt bs 88).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v7_wordAt bs 96) ∗
      ((out + 112#64) ↦₆₄ v7_wordAt bs 104) ∗
      (((out + 120#64) ↦₈ loByte (v7_wordAt bs 112)) ∗
       ((out + 121#64) ↦₆₄ unshiftWord (v7_wordAt bs 112) (loByte (v7_wordAt bs 120))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 (unshiftWord (v7_wordAt bs 112) (loByte (v7_wordAt bs 120)))
           (v7_wordAt bs 120 >>> 8)))) ∗
      ((out + 136#64) ↦₆₄ v7_wordAt bs 128) ∗
      (((out + 144#64) ↦₈ ((loByte (v7_wordAt bs 136)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄
         (v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄
         overlapWord7
           ((v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)).extractLsb' 64 64)
           (v7_wordAt bs 152 >>> 8))) ∗
      ((out + 168#64) ↦₁₂₈ v7_quadAt bs 160) ∗
      ((out + 184#64) ↦₁₂₈ v7_quadAt bs 176) ∗
      ((out + 200#64) ↦₁₂₈ v7_quadAt bs 192) ∗
      ((out + 216#64) ↦₁₂₈ v7_quadAt bs 208) ∗
      ((out + 232#64) ↦₁₂₈ v7_quadAt bs 224) ∗
      ((out + 248#64) ↦₁₂₈ v7_quadAt bs 240) ∗
      ((out + 264#64) ↦₁₂₈ v7_quadAt bs 256) ∗
      ((out + 280#64) ↦₁₂₈ v7_quadAt bs 272) ∗
      ((out + 296#64) ↦₁₂₈ v7_quadAt bs 288) ∗
      ((out + 312#64) ↦₁₂₈ v7_quadAt bs 304) ∗
      ((out + 328#64) ↦₁₂₈ v7_quadAt bs 320) ∗
      ((out + 344#64) ↦₁₂₈ v7_quadAt bs 336) ∗
      ((out + 360#64) ↦₁₂₈ v7_quadAt bs 352) ∗
      ((out + 376#64) ↦₁₂₈ v7_quadAt bs 368) =
    (out + 8#64) ↦ₛ bs := by
  rw [v7_out_96_realign out (v7_wordAt bs 88),
      v7_out_120_realign out (v7_wordAt bs 112) (v7_wordAt bs 120),
      v7_out_144_realign out (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152),
      v7_bs384_eq_encCells bs hbs out]
  unfold v7_encCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## 2. Reassembly of `unchunkedCt1SentAt` (`out + 400..528`) & `polyDecoderAt` (`out + 528..928`) -/

theorem v7_unchunkedCt1SentAt_400_pack (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64) (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64) :
    ((out + 400#64) ↦₆₄ c1) ∗ ((out + 408#64) ↦₆₄ p1) ∗ ((out + 416#64) ↦₆₄ l1) ∗
      ((out + 424#64) ↦₆₄ c2) ∗ ((out + 432#64) ↦₆₄ p2) ∗ ((out + 440#64) ↦₆₄ l2) ∗
      ((out + 448#64) ↦₆₄ c3) ∗ ((out + 456#64) ↦₆₄ p3) ∗ ((out + 464#64) ↦₆₄ l3) ∗
      ((out + 472#64) ↦₆₄ c4) ∗ ((out + 480#64) ↦₆₄ p4) ∗ ((out + 488#64) ↦₆₄ l4) ∗
      ((out + 496#64) ↦₆₄ c5) ∗ ((out + 504#64) ↦₆₄ p5) ∗ ((out + 512#64) ↦₆₄ l5) ∗
      ((out + 520#64) ↦₆₄ uc.epoch) ∗
      v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ⊢
    unchunkedCt1SentAt A (F := F) (out + 400#64) uc := by
  rw [← v7_ct1SentAt_eq_unchunkedCt1SentAt A (F := F) (out + 400#64) uc]
  have hpack := v7_ct1SentAt_pack A (out + 400#64) uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
  dsimp only [v7_ct1SentWordsAt] at hpack
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hpack

theorem v7_out_536_realign (out w8_dec w16_dec w24_dec : BitVec 64) :
    ((out + 536#64) ↦₈ ((loByte w8_dec).zeroExtend 32).setWidth 8) ∗
      ((out + 537#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
      ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 ((v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64) (w24_dec >>> 8))) =
    ((out + 536#64) ↦₆₄ w8_dec) ∗ ((out + 544#64) ↦₆₄ w16_dec) ∗ ((out + 552#64) ↦₆₄ w24_dec) := by
  rw [v7_zext32_setWidth8 (loByte w8_dec)]
  have hhi : (v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64 =
      unshiftWord w16_dec (loByte w24_dec) := by
    unfold v7_midQ128; bv_kernel
  rw [hhi, v7_overlapWord7_unshift_lsr8 w16_dec w24_dec]
  have h := (v7_triple64_eq_byte_q128_tail7 (out + 536#64) w8_dec w16_dec w24_dec).symm
  change _ = ((out + 536#64) ↦₆₄ w8_dec) ∗ (((out + 536#64) + 8#64) ↦₆₄ w16_dec) ∗
    (((out + 536#64) + 16#64) ↦₆₄ w24_dec) at h
  have ha537 : (out + 536#64) + 1#64 = out + 537#64 := by bv_omega
  have ha553 : (out + 536#64) + 17#64 = out + 553#64 := by bv_omega
  have ha544 : (out + 536#64) + 8#64 = out + 544#64 := by bv_omega
  have ha552 : (out + 536#64) + 16#64 = out + 552#64 := by bv_omega
  rw [ha537, ha553, ha544, ha552] at h
  exact h

theorem v7_polyDecoderAt_528_pack (A : RustAlloc)
    (out w0_dec w8_dec w16_dec w24_dec : BitVec 64)
    (bs328_dec : List (BitVec 8))
    (q328_dec q344_dec : BitVec 128) (w360_dec : BitVec 64)
    (dec : PolyDecoder) (P_dec_heap : SepProp)
    (hreloc_dec :
      ((out + 528#64) ↦₆₄ w0_dec) ∗ (((out + 528#64) + 8#64) ↦₆₄ w8_dec) ∗
        (((out + 528#64) + 16#64) ↦₆₄ w16_dec) ∗ (((out + 528#64) + 24#64) ↦₆₄ w24_dec) ∗
        (((out + 528#64) + 32#64) ↦ₛ bs328_dec) ∗
        (((out + 528#64) + 360#64) ↦₁₂₈ q328_dec) ∗
        (((out + 528#64) + 376#64) ↦₁₂₈ q344_dec) ∗
        (((out + 528#64) + 392#64) ↦₆₄ w360_dec) ∗ P_dec_heap ⊢
        polyDecoderAt A (out + 528#64) dec) :
    ((out + 528#64) ↦₆₄ w0_dec) ∗
      (((out + 536#64) ↦₈ ((loByte w8_dec).zeroExtend 32).setWidth 8) ∗
       ((out + 537#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
       ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 ((v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64) (w24_dec >>> 8))) ∗
       ((out + 560#64) ↦ₛ bs328_dec) ∗
       ((out + 888#64) ↦₁₂₈ q328_dec) ∗
       ((out + 904#64) ↦₁₂₈ q344_dec) ∗
       ((out + 920#64) ↦₆₄ w360_dec)) ∗
      P_dec_heap ⊢
    polyDecoderAt A (out + 528#64) dec := by
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hreloc_dec
  refine Entails.trans (Entails.of_eq (show _ =
    ((out + 528#64) ↦₆₄ w0_dec) ∗
    (((out + 536#64) ↦₈ ((loByte w8_dec).zeroExtend 32).setWidth 8) ∗
     ((out + 537#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
     ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7
       (overlapWord7 ((v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64) (w24_dec >>> 8)))) ∗
    ((out + 560#64) ↦ₛ bs328_dec) ∗
    ((out + 888#64) ↦₁₂₈ q328_dec) ∗
    ((out + 904#64) ↦₁₂₈ q344_dec) ∗
    ((out + 920#64) ↦₆₄ w360_dec) ∗
    P_dec_heap by ac_rfl)) ?_
  rw [v7_out_536_realign out w8_dec w16_dec w24_dec]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hreloc_dec

/-! ## 3. Epilogue Output Entailment (`v7_epilogueOutFull_entails_ct1Sampled`) -/

theorem v7_epilogueOutFull_entails_ct1Sampled (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64) (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (enc : PolyEncoder) (dec : PolyDecoder)
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (bs_enc : List (BitVec 8)) (hbs_enc : bs_enc.length = 384)
    (hi32_enc : BitVec 32) (P_enc_heap : SepProp)
    (hreloc_enc :
      (out ↦₆₄ v7_polyEncoderTag enc) ∗ ((out + 8#64) ↦ₛ bs_enc) ∗
        ((out + 392#64) ↦₆₄ (hi32_enc ++ enc.idx)) ∗ P_enc_heap ⊢
        polyEncoderAt A out enc)
    (w0_dec w8_dec w16_dec w24_dec : BitVec 64)
    (bs328_dec : List (BitVec 8))
    (q328_dec q344_dec : BitVec 128) (w360_dec : BitVec 64) (P_dec_heap : SepProp)
    (hreloc_dec :
      ((out + 528#64) ↦₆₄ w0_dec) ∗ (((out + 528#64) + 8#64) ↦₆₄ w8_dec) ∗
        (((out + 528#64) + 16#64) ↦₆₄ w16_dec) ∗ (((out + 528#64) + 24#64) ↦₆₄ w24_dec) ∗
        (((out + 528#64) + 32#64) ↦ₛ bs328_dec) ∗
        (((out + 528#64) + 360#64) ↦₁₂₈ q328_dec) ∗
        (((out + 528#64) + 376#64) ↦₁₂₈ q344_dec) ∗
        (((out + 528#64) + 392#64) ↦₆₄ w360_dec) ∗ P_dec_heap ⊢
        polyDecoderAt A (out + 528#64) dec) :
    epilogueOutFull out
      (v7_polyEncoderTag enc)
      (v7_wordAt bs_enc 0) (v7_wordAt bs_enc 8) (v7_wordAt bs_enc 16)
      (v7_wordAt bs_enc 24) (v7_wordAt bs_enc 32) (v7_wordAt bs_enc 40) (v7_wordAt bs_enc 48)
      (v7_wordAt bs_enc 56) (v7_wordAt bs_enc 64) (v7_wordAt bs_enc 72) (v7_wordAt bs_enc 80)
      ((v7_wordAt bs_enc 88).extractLsb' 0 8) ((v7_wordAt bs_enc 88).extractLsb' 8 32)
      ((v7_wordAt bs_enc 88).extractLsb' 40 16) ((v7_wordAt bs_enc 88).extractLsb' 56 8)
      (v7_wordAt bs_enc 96) (v7_wordAt bs_enc 104) (loByte (v7_wordAt bs_enc 112))
      (unshiftWord (v7_wordAt bs_enc 112) (loByte (v7_wordAt bs_enc 120)))
      (overlapWord7 (unshiftWord (v7_wordAt bs_enc 112) (loByte (v7_wordAt bs_enc 120)))
        (v7_wordAt bs_enc 120 >>> 8))
      (v7_wordAt bs_enc 128)
      (((loByte (v7_wordAt bs_enc 136)).zeroExtend 32).setWidth 8)
      (v7_midQ128 (v7_wordAt bs_enc 136) (v7_wordAt bs_enc 144) (v7_wordAt bs_enc 152))
      (overlapWord7
        ((v7_midQ128 (v7_wordAt bs_enc 136) (v7_wordAt bs_enc 144) (v7_wordAt bs_enc 152)).extractLsb' 64 64)
        (v7_wordAt bs_enc 152 >>> 8))
      (v7_quadAt bs_enc 160) (v7_quadAt bs_enc 176) (v7_quadAt bs_enc 192) (v7_quadAt bs_enc 208)
      (v7_quadAt bs_enc 224) (v7_quadAt bs_enc 240) (v7_quadAt bs_enc 256) (v7_quadAt bs_enc 272)
      (v7_quadAt bs_enc 288) (v7_quadAt bs_enc 304) (v7_quadAt bs_enc 320) (v7_quadAt bs_enc 336)
      (v7_quadAt bs_enc 352) (v7_quadAt bs_enc 368)
      (hi32_enc ++ enc.idx) c1
      p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5
      l5 uc.epoch w0_dec
      (((loByte w8_dec).zeroExtend 32).setWidth 8)
      (v7_midQ128 w8_dec w16_dec w24_dec)
      (overlapWord7 ((v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64) (w24_dec >>> 8))
      bs328_dec q328_dec q344_dec w360_dec ∗
      P_enc_heap ∗
      P_dec_heap ∗
      v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ⊢
    resultChunkedStatesAt A (F := F) out
      (.ok (.ct1Sampled ⟨uc, enc, dec⟩)) := by
  dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedCt1SampledAt]
  unfold epilogueOutFull
  have hbs_eq := v7_out_8_to_392_eq_bs out bs_enc hbs_enc
  have huc := v7_unchunkedCt1SentAt_400_pack A (F := F) out uc
    c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
  have hdec := v7_polyDecoderAt_528_pack A out w0_dec w8_dec w16_dec w24_dec
    bs328_dec q328_dec q344_dec w360_dec dec P_dec_heap hreloc_dec
  refine Entails.trans (Entails.of_eq (show _ =
    ((out ↦₆₄ v7_polyEncoderTag enc) ∗
     (((out + 8#64) ↦₆₄ v7_wordAt bs_enc 0) ∗
      ((out + 16#64) ↦₆₄ v7_wordAt bs_enc 8) ∗
      ((out + 24#64) ↦₆₄ v7_wordAt bs_enc 16) ∗
      ((out + 32#64) ↦₆₄ v7_wordAt bs_enc 24) ∗
      ((out + 40#64) ↦₆₄ v7_wordAt bs_enc 32) ∗
      ((out + 48#64) ↦₆₄ v7_wordAt bs_enc 40) ∗
      ((out + 56#64) ↦₆₄ v7_wordAt bs_enc 48) ∗
      ((out + 64#64) ↦₆₄ v7_wordAt bs_enc 56) ∗
      ((out + 72#64) ↦₆₄ v7_wordAt bs_enc 64) ∗
      ((out + 80#64) ↦₆₄ v7_wordAt bs_enc 72) ∗
      ((out + 88#64) ↦₆₄ v7_wordAt bs_enc 80) ∗
      (((out + 96#64) ↦₈ (v7_wordAt bs_enc 88).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v7_wordAt bs_enc 88).extractLsb' 8 32) ∗
       ((out + 101#64) ↦₁₆ (v7_wordAt bs_enc 88).extractLsb' 40 16) ∗
       ((out + 103#64) ↦₈ (v7_wordAt bs_enc 88).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v7_wordAt bs_enc 96) ∗
      ((out + 112#64) ↦₆₄ v7_wordAt bs_enc 104) ∗
      (((out + 120#64) ↦₈ loByte (v7_wordAt bs_enc 112)) ∗
       ((out + 121#64) ↦₆₄ unshiftWord (v7_wordAt bs_enc 112) (loByte (v7_wordAt bs_enc 120))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 (unshiftWord (v7_wordAt bs_enc 112) (loByte (v7_wordAt bs_enc 120)))
           (v7_wordAt bs_enc 120 >>> 8)))) ∗
      ((out + 136#64) ↦₆₄ v7_wordAt bs_enc 128) ∗
      (((out + 144#64) ↦₈ ((loByte (v7_wordAt bs_enc 136)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄
         (v7_midQ128 (v7_wordAt bs_enc 136) (v7_wordAt bs_enc 144) (v7_wordAt bs_enc 152)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v7_midQ128 (v7_wordAt bs_enc 136) (v7_wordAt bs_enc 144) (v7_wordAt bs_enc 152)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄
         overlapWord7
           ((v7_midQ128 (v7_wordAt bs_enc 136) (v7_wordAt bs_enc 144) (v7_wordAt bs_enc 152)).extractLsb' 64 64)
           (v7_wordAt bs_enc 152 >>> 8))) ∗
      ((out + 168#64) ↦₁₂₈ v7_quadAt bs_enc 160) ∗
      ((out + 184#64) ↦₁₂₈ v7_quadAt bs_enc 176) ∗
      ((out + 200#64) ↦₁₂₈ v7_quadAt bs_enc 192) ∗
      ((out + 216#64) ↦₁₂₈ v7_quadAt bs_enc 208) ∗
      ((out + 232#64) ↦₁₂₈ v7_quadAt bs_enc 224) ∗
      ((out + 248#64) ↦₁₂₈ v7_quadAt bs_enc 240) ∗
      ((out + 264#64) ↦₁₂₈ v7_quadAt bs_enc 256) ∗
      ((out + 280#64) ↦₁₂₈ v7_quadAt bs_enc 272) ∗
      ((out + 296#64) ↦₁₂₈ v7_quadAt bs_enc 288) ∗
      ((out + 312#64) ↦₁₂₈ v7_quadAt bs_enc 304) ∗
      ((out + 328#64) ↦₁₂₈ v7_quadAt bs_enc 320) ∗
      ((out + 344#64) ↦₁₂₈ v7_quadAt bs_enc 336) ∗
      ((out + 360#64) ↦₁₂₈ v7_quadAt bs_enc 352) ∗
      ((out + 376#64) ↦₁₂₈ v7_quadAt bs_enc 368)) ∗
     ((out + 392#64) ↦₆₄ (hi32_enc ++ enc.idx)) ∗
     P_enc_heap) ∗
    (((out + 400#64) ↦₆₄ c1) ∗ ((out + 408#64) ↦₆₄ p1) ∗ ((out + 416#64) ↦₆₄ l1) ∗
     ((out + 424#64) ↦₆₄ c2) ∗ ((out + 432#64) ↦₆₄ p2) ∗ ((out + 440#64) ↦₆₄ l2) ∗
     ((out + 448#64) ↦₆₄ c3) ∗ ((out + 456#64) ↦₆₄ p3) ∗ ((out + 464#64) ↦₆₄ l3) ∗
     ((out + 472#64) ↦₆₄ c4) ∗ ((out + 480#64) ↦₆₄ p4) ∗ ((out + 488#64) ↦₆₄ l4) ∗
     ((out + 496#64) ↦₆₄ c5) ∗ ((out + 504#64) ↦₆₄ p5) ∗ ((out + 512#64) ↦₆₄ l5) ∗
     ((out + 520#64) ↦₆₄ uc.epoch) ∗
     v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5) ∗
    (((out + 528#64) ↦₆₄ w0_dec) ∗
     (((out + 536#64) ↦₈ ((loByte w8_dec).zeroExtend 32).setWidth 8) ∗
      ((out + 537#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
      ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 ((v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64) (w24_dec >>> 8))) ∗
      ((out + 560#64) ↦ₛ bs328_dec) ∗
      ((out + 888#64) ↦₁₂₈ q328_dec) ∗
      ((out + 904#64) ↦₁₂₈ q344_dec) ∗
      ((out + 920#64) ↦₆₄ w360_dec)) ∗
     P_dec_heap) by ac_rfl)) ?_
  rw [hbs_eq]
  exact Entails.trans (sepConj_mono hreloc_enc (sepConj_mono huc hdec)) (Entails.of_eq (by ac_rfl))

/-! ## 4. Stack Splitting & Gap Packing Helpers for `+7404 -> +8180` -/

theorem v7_memRegion_0_16_split (fsp : BitVec 64) :
    memRegion fsp 16 ⊢
      memRegion fsp 8 ∗ (∃∗ w8 : BitVec 64, (fsp + 8#64) ↦₆₄ w8) := by
  exact split_top <| split_step0 (Entails.refl _) <| mem64_entails _

theorem v7_memRegion_32_168_split (fsp : BitVec 64) :
    memRegion (fsp + 32#64) 168 ⊢
      (∃∗ w32 : BitVec 64, (fsp + 32#64) ↦₆₄ w32) ∗
      (∃∗ w40 : BitVec 64, (fsp + 40#64) ↦₆₄ w40) ∗
      (∃∗ w48 : BitVec 64, (fsp + 48#64) ↦₆₄ w48) ∗
      (∃∗ w56 : BitVec 64, (fsp + 56#64) ↦₆₄ w56) ∗
      (∃∗ w64 : BitVec 64, (fsp + 64#64) ↦₆₄ w64) ∗
      (∃∗ w72 : BitVec 64, (fsp + 72#64) ↦₆₄ w72) ∗
      (∃∗ w80 : BitVec 64, (fsp + 80#64) ↦₆₄ w80) ∗
      memRegion (fsp + 88#64) 4 ∗
      (∃∗ d92 : BitVec 32, (fsp + 92#64) ↦₃₂ d92) ∗
      (∃∗ w96 : BitVec 64, (fsp + 96#64) ↦₆₄ w96) ∗
      (∃∗ w104 : BitVec 64, (fsp + 104#64) ↦₆₄ w104) ∗
      (∃∗ w112 : BitVec 64, (fsp + 112#64) ↦₆₄ w112) ∗
      (∃∗ w120 : BitVec 64, (fsp + 120#64) ↦₆₄ w120) ∗
      (∃∗ w128 : BitVec 64, (fsp + 128#64) ↦₆₄ w128) ∗
      (∃∗ w136 : BitVec 64, (fsp + 136#64) ↦₆₄ w136) ∗
      (∃∗ w144 : BitVec 64, (fsp + 144#64) ↦₆₄ w144) ∗
      (∃∗ w152 : BitVec 64, (fsp + 152#64) ↦₆₄ w152) ∗
      (∃∗ w160 : BitVec 64, (fsp + 160#64) ↦₆₄ w160) ∗
      memRegion (fsp + 168#64) 4 ∗
      (∃∗ d172 : BitVec 32, (fsp + 172#64) ↦₃₂ d172) ∗
      (∃∗ w176 : BitVec 64, (fsp + 176#64) ↦₆₄ w176) ∗
      (∃∗ w184 : BitVec 64, (fsp + 184#64) ↦₆₄ w184) ∗
      (∃∗ w192 : BitVec 64, (fsp + 192#64) ↦₆₄ w192) := by
  exact split_top <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem32_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem32_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    mem64_entails _

theorem v7_pointsTo64_entails_loBytes7_mem1 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦ₛ EncoderFromPb.loBytes7 w) ∗ memRegion (a + 7#64) 1 := by
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w]
  have hsplit : unpack64 w = EncoderFromPb.loBytes7 w ++ [w.extractLsb' 56 8] := rfl
  rw [hsplit, ProofLib.pointsToBytes_append a (EncoderFromPb.loBytes7 w) [w.extractLsb' 56 8],
      EncoderFromPb.length_loBytes7 w]
  exact sepConj_mono_right
    (ProofLib.pointsToBytes_entails_memRegion (a + 7#64) [w.extractLsb' 56 8])

theorem v7_memRegion8_entails_loBytes7_mem1 (a : BitVec 64) :
    memRegion a 8 ⊢ (∃∗ w : BitVec 64, a ↦ₛ EncoderFromPb.loBytes7 w) ∗ memRegion (a + 7#64) 1 := by
  refine Entails.trans (mem64_entails a) ?_
  apply Entails.sepExists_elim; intro w
  refine Entails.trans (v7_pointsTo64_entails_loBytes7_mem1 a w) ?_
  exact sepConj_mono_left (Entails.sepExists_right w (Entails.refl _))

theorem v7_memRegion8_loBytes7_at (fsp o1 o2 : BitVec 64)
    (ho : o1 + 7#64 = o2 := by rfl) :
    memRegion (fsp + o1) 8 ⊢
      (∃∗ w : BitVec 64, (fsp + o1) ↦ₛ EncoderFromPb.loBytes7 w) ∗ memRegion (fsp + o2) 1 := by
  have ha : (fsp + o1) + 7#64 = fsp + o2 := by rw [BitVec.add_assoc, ho]
  rw [← ha]
  exact v7_memRegion8_entails_loBytes7_mem1 (fsp + o1)

theorem v7_memRegion16_loBytes7_at (fsp o1 o2 : BitVec 64)
    (ho : o1 + 7#64 = o2 := by rfl) :
    memRegion (fsp + o1) 16 ⊢
      (∃∗ w : BitVec 64, (fsp + o1) ↦ₛ EncoderFromPb.loBytes7 w) ∗ memRegion (fsp + o2) 9 := by
  have hsplit : memRegion (fsp + o1) 16 ⊢
      memRegion (fsp + o1) 8 ∗ memRegion ((fsp + o1) + 8#64) 8 := by
    rw [ProofLib.memRegion_split (fsp + o1) 8 8 (by decide)]
    exact Entails.refl _
  refine Entails.trans hsplit ?_
  refine Entails.trans (sepConj_mono_left (v7_memRegion8_loBytes7_at fsp o1 o2 ho)) ?_
  rw [sepConj_assoc]
  refine sepConj_mono_right ?_
  have ha : (fsp + o1) + 8#64 = (fsp + o2) + 1#64 := by
    rw [← ho, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; rfl
  rw [ha, ← ProofLib.memRegion_split (fsp + o2) 1 8 (by decide)]
  exact Entails.refl _

theorem v7_memRegion_208_1056_split (fsp : BitVec 64) :
    memRegion (fsp + 208#64) 1056 ⊢
      (∃∗ w208 : BitVec 64, (fsp + 208#64) ↦₆₄ w208) ∗
      (∃∗ w216 : BitVec 64, (fsp + 216#64) ↦₆₄ w216) ∗
      (∃∗ w224 : BitVec 64, (fsp + 224#64) ↦₆₄ w224) ∗
      (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 328 ∗
      memRegion (fsp + 568#64) 8 ∗
      (∃∗ q576 : BitVec 128, (fsp + 576#64) ↦₁₂₈ q576) ∗
      ((∃∗ w592 : BitVec 64, (fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion (fsp + 599#64) 9) ∗
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
      ((∃∗ w864 : BitVec 64, (fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗ memRegion (fsp + 871#64) 9) ∗
      (∃∗ w880 : BitVec 64, (fsp + 880#64) ↦₆₄ w880) ∗
      ((∃∗ w888 : BitVec 64, (fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗ memRegion (fsp + 895#64) 1) ∗
      memRegion (fsp + 896#64) 368 := by
  exact split_top <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (Entails.refl _) <|
    split_step (mem128_entails _) <|
    split_step (v7_memRegion16_loBytes7_at fsp 592#64 599#64) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem128_entails _) <|
    split_step (v7_memRegion16_loBytes7_at fsp 864#64 871#64) <|
    split_step (mem64_entails _) <|
    split_step (v7_memRegion8_loBytes7_at fsp 888#64 895#64) <|
    Entails.refl _

theorem v7_memRegion_1888_400_split (fsp : BitVec 64) :
    memRegion (fsp + 1888#64) 400 ⊢
      (∃∗ q1888 : BitVec 128, (fsp + 1888#64) ↦₁₂₈ q1888) ∗
      (∃∗ q1904 : BitVec 128, (fsp + 1904#64) ↦₁₂₈ q1904) ∗
      (∃∗ w1920 : BitVec 64, (fsp + 1920#64) ↦₆₄ w1920) ∗
      memRegion (fsp + 1928#64) 360 := by
  exact split_top <|
    split_step (mem128_entails _) <|
    split_step (mem128_entails _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v7_epilogueStackGaps_pack (fsp w8 tag c1 w32 w40 w48 w56 w64 w72 w80 c4
    w128 w136 w144 w152 l3 l2 p1 w216 : BitVec 64)
    (bs328_dec : { l : List (BitVec 8) // l.length = 328 })
    (q328_dec q344_dec : BitVec 128) (w360_dec : BitVec 64)
    (c1' p1' l1 c2 p2 l2' c3 p3 l3' c4' p4 l4 c5 p5 l5 ep : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) (w1784 : BitVec 64) :
    memRegion fsp 8 ∗
      ((fsp + 8#64) ↦₆₄ w8) ∗ ((fsp + 16#64) ↦₆₄ tag) ∗ ((fsp + 24#64) ↦₆₄ c1) ∗
      ((fsp + 32#64) ↦₆₄ w32) ∗ ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗
      ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ ((fsp + 72#64) ↦₆₄ w72) ∗
      ((fsp + 80#64) ↦₆₄ w80) ∗ memRegion (fsp + 88#64) 4 ∗
      ((fsp + 96#64) ↦₆₄ c4) ∗
      ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
      ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
      memRegion (fsp + 168#64) 4 ∗
      ((fsp + 176#64) ↦₆₄ l3) ∗ ((fsp + 184#64) ↦₆₄ l2) ∗
      ((fsp + 200#64) ↦₆₄ p1) ∗
      ((fsp + 216#64) ↦₆₄ w216) ∗
      memRegion (fsp + 568#64) 8 ∗
      memRegion (fsp + 599#64) 9 ∗
      memRegion (fsp + 840#64) 8 ∗
      memRegion (fsp + 871#64) 9 ∗
      memRegion (fsp + 895#64) 1 ∗
      ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
      ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
      ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
      ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
      v7_ct1SentWordsAt (fsp + 1264#64) c1' p1' l1 c2 p2 l2' c3 p3 l3' c4' p4 l4 c5 p5 l5 ep ∗
      ((fsp + 1392#64) ↦₆₄ tag) ∗
      v7_encCellsAt (fsp + 1392#64) bs ∗
      ((fsp + 1784#64) ↦₆₄ w1784) ∗
      memRegion (fsp + 1792#64) 96 ∗
      memRegion (fsp + 1928#64) 360 ∗
      memRegion (fsp + 2288#64) 16 ⊢
    epilogueStackGaps fsp := by
  unfold epilogueStackGaps
  have h92 : memRegion fsp 8 ∗
      ((fsp + 8#64) ↦₆₄ w8) ∗ ((fsp + 16#64) ↦₆₄ tag) ∗ ((fsp + 24#64) ↦₆₄ c1) ∗
      ((fsp + 32#64) ↦₆₄ w32) ∗ ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗
      ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ ((fsp + 72#64) ↦₆₄ w72) ∗
      ((fsp + 80#64) ↦₆₄ w80) ∗ memRegion (fsp + 88#64) 4 ⊢
      memRegion fsp 92 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have h96 : ((fsp + 96#64) ↦₆₄ c4) ⊢ memRegion (fsp + 96#64) 8 :=
    Drop.pointsTo64_entails_memRegion _ _
  have h128 : ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
      ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152) ⊢
      memRegion (fsp + 128#64) 32 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  have h176 : ((fsp + 176#64) ↦₆₄ l3) ∗ ((fsp + 184#64) ↦₆₄ l2) ⊢ memRegion (fsp + 176#64) 16 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  have h200 : ((fsp + 200#64) ↦₆₄ p1) ⊢ memRegion (fsp + 200#64) 8 :=
    Drop.pointsTo64_entails_memRegion _ _
  have h216 : ((fsp + 216#64) ↦₆₄ w216) ⊢ memRegion (fsp + 216#64) 8 :=
    Drop.pointsTo64_entails_memRegion _ _
  have hbs328 : ((fsp + 896#64) ↦ₛ bs328_dec.val) ⊢ memRegion (fsp + 896#64) 328 := by
    simpa [bs328_dec.property] using
      ProofLib.pointsToBytes_entails_memRegion (fsp + 896#64) bs328_dec.val
  have henc384 : v7_encCellsAt (fsp + 1392#64) bs ⊢ memRegion (fsp + 1400#64) 384 := by
    rw [← v7_bs384_eq_encCells bs hbs (fsp + 1392#64)]
    have ha1400 : (fsp + 1392#64) + 8#64 = fsp + 1400#64 := by bv_omega
    rw [ha1400]
    simpa [hbs] using ProofLib.pointsToBytes_entails_memRegion (fsp + 1400#64) bs
  have h895 : memRegion (fsp + 895#64) 1 ∗
      ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
      ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
      ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
      ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
      v7_ct1SentWordsAt (fsp + 1264#64) c1' p1' l1 c2 p2 l2' c3 p3 l3' c4' p4 l4 c5 p5 l5 ep ∗
      ((fsp + 1392#64) ↦₆₄ tag) ∗
      v7_encCellsAt (fsp + 1392#64) bs ∗
      ((fsp + 1784#64) ↦₆₄ w1784) ∗
      memRegion (fsp + 1792#64) 96 ⊢
      memRegion (fsp + 895#64) 993 :=
    collapse_top <| collapse_step (Entails.refl _) <|
      collapse_step hbs328 <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (v7_ct1SentWordsAt_entails_128 (fsp + 1264#64) c1' p1' l1 c2 p2 l2' c3 p3 l3' c4' p4 l4 c5 p5 l5 ep) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step henc384 <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have h1928 : memRegion (fsp + 1928#64) 360 ∗ memRegion (fsp + 2288#64) 16 ⊢
      memRegion (fsp + 1928#64) 376 :=
    collapse_top <| collapse_step (Entails.refl _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion fsp 8 ∗
     ((fsp + 8#64) ↦₆₄ w8) ∗ ((fsp + 16#64) ↦₆₄ tag) ∗ ((fsp + 24#64) ↦₆₄ c1) ∗
     ((fsp + 32#64) ↦₆₄ w32) ∗ ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗
     ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ ((fsp + 72#64) ↦₆₄ w72) ∗
     ((fsp + 80#64) ↦₆₄ w80) ∗ memRegion (fsp + 88#64) 4) ∗
    ((fsp + 96#64) ↦₆₄ c4) ∗
    (((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
     ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152)) ∗
    memRegion (fsp + 168#64) 4 ∗
    (((fsp + 176#64) ↦₆₄ l3) ∗ ((fsp + 184#64) ↦₆₄ l2)) ∗
    ((fsp + 200#64) ↦₆₄ p1) ∗
    ((fsp + 216#64) ↦₆₄ w216) ∗
    memRegion (fsp + 568#64) 8 ∗
    memRegion (fsp + 599#64) 9 ∗
    memRegion (fsp + 840#64) 8 ∗
    memRegion (fsp + 871#64) 9 ∗
    (memRegion (fsp + 895#64) 1 ∗
     ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
     ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
     ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
     ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
     v7_ct1SentWordsAt (fsp + 1264#64) c1' p1' l1 c2 p2 l2' c3 p3 l3' c4' p4 l4 c5 p5 l5 ep ∗
     ((fsp + 1392#64) ↦₆₄ tag) ∗
     v7_encCellsAt (fsp + 1392#64) bs ∗
     ((fsp + 1784#64) ↦₆₄ w1784) ∗
     memRegion (fsp + 1792#64) 96) ∗
    (memRegion (fsp + 1928#64) 360 ∗ memRegion (fsp + 2288#64) 16) by ac_rfl)) ?_
  exact sepConj_mono h92 (sepConj_mono h96 (sepConj_mono h128 (sepConj_mono_right
    (sepConj_mono h176 (sepConj_mono h200 (sepConj_mono h216 (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono h895 h1928)))))))))))

/-! ## 5. Complete Success Return Path (`+7404 (.ok dec) -> s0.x30`) -/

end CryptoVerification.SpqrV1.States.FromPb

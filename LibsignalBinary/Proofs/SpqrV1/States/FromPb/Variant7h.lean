/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7g -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 7 (`Ct1Sampled`, `+1056`) — Part H

Covers the `<PolyEncoder>::from_pb = Ok(enc)` stack move (`+3720 -> +7260 -> +7348`),
`s.receivingEk = none` cleanup (`+7348 -> +10556 -> +4632`), and `<PolyDecoder>::from_pb` setup,
call, and error cleanup (`+7348 -> +7400 -> +7404 -> +11096 -> +4632`).
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



theorem v7_memRegion_896_56_split_24_32 (fsp : BitVec 64) :
    memRegion (fsp + 896#64) 56 ⊢
      (∃∗ d0 : BitVec 64, (fsp + 896#64) ↦₆₄ d0) ∗
      (∃∗ d8 : BitVec 64, (fsp + 904#64) ↦₆₄ d8) ∗
      (∃∗ d16 : BitVec 64, (fsp + 912#64) ↦₆₄ d16) ∗
      memRegion (fsp + 920#64) 32 := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v7_memRegion_1392_400_split_32_368 (fsp : BitVec 64) :
    memRegion (fsp + 1392#64) 400 ⊢
      (∃∗ e0 : BitVec 64, (fsp + 1392#64) ↦₆₄ e0) ∗
      (∃∗ e8 : BitVec 64, (fsp + 1400#64) ↦₆₄ e8) ∗
      (∃∗ e16 : BitVec 64, (fsp + 1408#64) ↦₆₄ e16) ∗
      (∃∗ e24 : BitVec 64, (fsp + 1416#64) ↦₆₄ e24) ∗
      memRegion (fsp + 1424#64) 368 := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v7_1888_32_368_entails_memRegion_400
    (fsp tag w8 w16 w24 : BitVec 64)
    (tail368 : { l : List (BitVec 8) // l.length = 368 }) :
    ((fsp + 1888#64) ↦₆₄ tag) ∗
    ((fsp + 1896#64) ↦₆₄ w8) ∗
    ((fsp + 1904#64) ↦₆₄ w16) ∗
    ((fsp + 1912#64) ↦₆₄ w24) ∗
    ((fsp + 1920#64) ↦ₛ tail368.val) ⊢
      memRegion (fsp + 1888#64) 400 := by
  have hm368 : ((fsp + 1920#64) ↦ₛ tail368.val) ⊢ memRegion (fsp + 1920#64) 368 := by
    have h := ProofLib.pointsToBytes_entails_memRegion (fsp + 1920#64) tail368.val
    rw [tail368.property] at h
    exact h
  exact collapse_top <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    hm368

theorem v7_896_spill_entails_memRegion_56
    (fsp u0 u1 w : BitVec 64) (b7 : BitVec 8) :
    ((fsp + 896#64) ↦₆₄ u0) ∗
    ((fsp + 904#64) ↦₆₄ u1) ∗
    (((fsp + 912#64) ↦ₛ EncoderFromPb.loBytes7 w) ∗ ((fsp + 919#64) ↦₈ b7)) ∗
    memRegion (fsp + 920#64) 32 ⊢
      memRegion (fsp + 896#64) 56 := by
  rw [← ProofLib.pointsToBytes_singleton (fsp + 919#64) b7]
  have hm8 := v7_pointsTo64_split_7_1_entails_8 (fsp + 912#64) w b7
  have ha919 : (fsp + 912#64) + 7#64 = fsp + 919#64 := by bv_omega
  rw [ha919] at hm8
  exact collapse_top <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step hm8 <|
    Entails.refl _

theorem v7_resultPolyEncoder_ok_eq (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    resultPolyEncoderFromPbAt A a (.ok enc) = polyEncoderAt A a enc := rfl

@[local simp, local arm64_norm, local wp_norm]
theorem v7_polyEncoderTag_bne_two (enc : PolyEncoder) :
    (v7_polyEncoderTag enc != 2#64) = true := by
  rcases v7_polyEncoderTag_eq enc with h | h <;> rw [h] <;> rfl

attribute [local simp, local arm64_norm, local wp_norm] v7_zext32_setWidth8

@[local simp, local arm64_norm, local wp_norm]
theorem v7_zext64_32_setWidth8 (w : BitVec 32) :
    (w.zeroExtend 64).setWidth 8 = w.setWidth 8 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v7_zext64_32_setWidth32 (w : BitVec 32) :
    (w.zeroExtend 64).setWidth 32 = w := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v7_zext64_setWidth8 (b : BitVec 8) :
    (b.zeroExtend 64).setWidth 8 = b := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v7_zext64_setWidth32_setWidth8 (b : BitVec 8) :
    ((b.zeroExtend 64).setWidth 32).setWidth 8 = b := by bv_kernel

theorem v7_stackAt_encoderFromPbStack_eq_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack =
      memRegion (fsp - 4096#64) 4096 ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ memRegion (fsp - 4096#64) 4096 at h
  rw [h, sepConj_comm]

theorem v7_polyEncoderAt_relocate_1888_to_1392 (A : RustAlloc) (fsp : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A (fsp + 1888#64) enc ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
      ∃∗ tail368 : { l : List (BitVec 8) // l.length = 368 },
      ∃∗ P_heap : SepProp,
        ⌜(((fsp + 1392#64) ↦₆₄ v7_polyEncoderTag enc) ∗
          ((fsp + 1400#64) ↦₆₄ w8) ∗ ((fsp + 1408#64) ↦₆₄ w16) ∗ ((fsp + 1416#64) ↦₆₄ w24) ∗
          ((fsp + 1424#64) ↦ₛ tail368.val) ∗ P_heap ⊢
            polyEncoderAt A (fsp + 1392#64) enc)⌝ ∗
        ((fsp + 1888#64) ↦₆₄ v7_polyEncoderTag enc) ∗
        ((fsp + 1896#64) ↦₆₄ w8) ∗
        ((fsp + 1904#64) ↦₆₄ w16) ∗
        ((fsp + 1912#64) ↦₆₄ w24) ∗
        ((fsp + 1920#64) ↦ₛ tail368.val) ∗
        P_heap := by
  have h := v7_polyEncoderAt_relocate_368 A (fsp + 1888#64) (fsp + 1392#64) enc
  have ha1400 : (fsp + 1392#64) + 8#64 = fsp + 1400#64 := by bv_omega
  have ha1408 : (fsp + 1392#64) + 16#64 = fsp + 1408#64 := by bv_omega
  have ha1416 : (fsp + 1392#64) + 24#64 = fsp + 1416#64 := by bv_omega
  have ha1424 : (fsp + 1392#64) + 32#64 = fsp + 1424#64 := by bv_omega
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  have ha1904 : (fsp + 1888#64) + 16#64 = fsp + 1904#64 := by bv_omega
  have ha1912 : (fsp + 1888#64) + 24#64 = fsp + 1912#64 := by bv_omega
  have ha1920 : (fsp + 1888#64) + 32#64 = fsp + 1920#64 := by bv_omega
  rw [ha1400, ha1408, ha1416, ha1424, ha1896, ha1904, ha1912, ha1920] at h
  exact h

theorem v7_byte_qword_lo7_word_eq_triple64 (a w8 w16 w24 : BitVec 64) :
    (a ↦₈ loByte w8) ∗
    ((a + 1#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
    ((a + 9#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
    ((a + 16#64) ↦₆₄ w24) =
    (a ↦₆₄ w8) ∗ ((a + 8#64) ↦₆₄ w16) ∗ ((a + 16#64) ↦₆₄ w24) := by
  have h1 := v7_triple64_to_byte_qword_tail7 a w8 w16 w24
  rw [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (a + 1#64)
        (unshiftWord w8 (loByte w16)) (unshiftWord w16 (loByte w24))] at h1
  have ha9 : (a + 1#64) + 8#64 = a + 9#64 := by bv_omega
  rw [ha9] at h1
  have h2 := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (a + 9#64)
    (unshiftWord w16 (loByte w24)) (w24 >>> 8)
  have ha16 : (a + 9#64) + 7#64 = a + 16#64 := by bv_omega
  have ha17 : (a + 9#64) + 8#64 = a + 17#64 := by bv_omega
  rw [ha17, ha16, ← v7_hiBytes7_eq_loBytes7_lsr8 w24,
      v7_overlapWord7_unshift_lsr8 w16 w24] at h2
  rw [h1]
  simp only [sepConj_assoc, h2]

theorem v7_1896_realign_final (fsp w8 w16 w24 : BitVec 64) :
    ((fsp + 1896#64) ↦₈ loByte w8) ∗
    ((fsp + 1897#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
    ((fsp + 1905#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
    ((fsp + 1912#64) ↦₆₄ w24) =
    ((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24) := by
  have h := v7_byte_qword_lo7_word_eq_triple64 (fsp + 1896#64) w8 w16 w24
  have ha1 : (fsp + 1896#64) + 1#64 = fsp + 1897#64 := by bv_omega
  have ha9 : (fsp + 1896#64) + 9#64 = fsp + 1905#64 := by bv_omega
  have ha8 : (fsp + 1896#64) + 8#64 = fsp + 1904#64 := by bv_omega
  have ha16 : (fsp + 1896#64) + 16#64 = fsp + 1912#64 := by bv_omega
  rw [ha1, ha9, ha8, ha16] at h
  exact h

theorem v7_1400_realign_final (fsp w8 w16 w24 : BitVec 64) :
    ((fsp + 1400#64) ↦₈ loByte w8) ∗
    ((fsp + 1401#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
    ((fsp + 1409#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
    ((fsp + 1416#64) ↦₆₄ w24) =
    ((fsp + 1400#64) ↦₆₄ w8) ∗ ((fsp + 1408#64) ↦₆₄ w16) ∗ ((fsp + 1416#64) ↦₆₄ w24) := by
  have h := v7_byte_qword_lo7_word_eq_triple64 (fsp + 1400#64) w8 w16 w24
  have ha1 : (fsp + 1400#64) + 1#64 = fsp + 1401#64 := by bv_omega
  have ha9 : (fsp + 1400#64) + 9#64 = fsp + 1409#64 := by bv_omega
  have ha8 : (fsp + 1400#64) + 8#64 = fsp + 1408#64 := by bv_omega
  have ha16 : (fsp + 1400#64) + 16#64 = fsp + 1416#64 := by bv_omega
  rw [ha1, ha9, ha8, ha16] at h
  exact h

theorem v7_1896_realign_final_rest (fsp w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1896#64) ↦₈ loByte w8) ∗
    ((fsp + 1897#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
    ((fsp + 1905#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
    ((fsp + 1912#64) ↦₆₄ w24) ∗ Rest =
    ((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24) ∗ Rest := by
  rw [← sepConj_assoc ((fsp + 1896#64) ↦₈ loByte w8),
      ← sepConj_assoc (((fsp + 1896#64) ↦₈ loByte w8) ∗ _),
      ← sepConj_assoc ((((fsp + 1896#64) ↦₈ loByte w8) ∗ _) ∗ _)]
  simp only [sepConj_assoc] at *
  have h := congrArg (· ∗ Rest) (v7_1896_realign_final fsp w8 w16 w24)
  simp only [sepConj_assoc] at h
  exact h

theorem v7_1400_realign_final_rest (fsp w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1400#64) ↦₈ loByte w8) ∗
    ((fsp + 1401#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
    ((fsp + 1409#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
    ((fsp + 1416#64) ↦₆₄ w24) ∗ Rest =
    ((fsp + 1400#64) ↦₆₄ w8) ∗ ((fsp + 1408#64) ↦₆₄ w16) ∗ ((fsp + 1416#64) ↦₆₄ w24) ∗ Rest := by
  have h := congrArg (· ∗ Rest) (v7_1400_realign_final fsp w8 w16 w24)
  simp only [sepConj_assoc] at h
  exact h

theorem v7_memRegion_1848_split_decCopy (fsp : BitVec 64) :
    memRegion (fsp + 1848#64) 40 ⊢
      (∃∗ d0 : BitVec 64, (fsp + 1848#64) ↦₆₄ d0) ∗
      (∃∗ b8 : BitVec 8, (fsp + 1856#64) ↦₈ b8) ∗
      (∃∗ q9_lo : BitVec 64, (fsp + 1857#64) ↦₆₄ q9_lo) ∗
      (∃∗ q9_hi : BitVec 64, (fsp + 1865#64) ↦₆₄ q9_hi) ∗
      memRegion (fsp + 1873#64) 7 ∗
      (∃∗ d32 : BitVec 64, (fsp + 1880#64) ↦₆₄ d32) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem8_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    mem64_entails _

theorem v7_decTailWordsAt_to_step7352
    (pbA w8 w16 w24 w32 : BitVec 64) :
    v7_decTailWordsAt (pbA + 184#64) w8 w16 w24 w32 ⊢
      ((pbA + 192#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((pbA + 193#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
      ((pbA + 201#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
      ((pbA + 209#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗
      ((pbA + 216#64) ↦₆₄ w32) := by
  unfold v7_decTailWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have htri := v7_triple64_to_byte_qword_tail7 (pbA + 192#64) w8 w16 w24
  simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at htri
  refine Entails.trans (Entails.of_eq (show _ =
    (((pbA + 192#64) ↦₆₄ w8) ∗ ((pbA + 200#64) ↦₆₄ w16) ∗ ((pbA + 208#64) ↦₆₄ w24)) ∗
    ((pbA + 216#64) ↦₆₄ w32) by ac_rfl)) ?_
  rw [htri]
  exact Entails.of_eq (by ac_rfl)

/-! ## 4. `<PolyDecoder>::from_pb = Err` Cleanup (`+7404 -> +11096 -> +4632`) -/

theorem v7_resultPolyDecoder_err_entails_tag_392 (A : RustAlloc) (fsp : BitVec 64)
    (err : PolynomialError) :
    resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err) ⊢
      ((fsp + 1888#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 1896#64) 392 := by
  dsimp only [resultPolyDecoderFromPbAt,
    resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize, noneCap]
  have hm8 : ((fsp + 1896#64) ↦₈ polynomialErrorByte err) ∗ memRegion (fsp + 1897#64) 391 ⊢
      memRegion (fsp + 1896#64) 392 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1896#64) (n := 1) (k := 391)
          (b' := fsp + 1897#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (fsp + 1896#64) (polynomialErrorByte err))
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  have ha1897 : (fsp + 1888#64) + 9#64 = fsp + 1897#64 := by bv_omega
  rw [ha1896, ha1897]
  exact sepConj_mono_right hm8

theorem v7_ct1SentAt_eq_unchunkedCt1SentAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    ct1SentAt A (F := F) a uc = unchunkedCt1SentAt A a uc := by
  rcases uc with ⟨epoch, ⟨rootKey, macKey⟩, hdr, es, ct1⟩
  rfl

end CryptoVerification.SpqrV1.States.FromPb


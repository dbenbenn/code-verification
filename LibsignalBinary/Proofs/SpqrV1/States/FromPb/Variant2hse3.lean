/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsd
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part E3

`receivingCt1` (`<PolyDecoder>::from_pb`) stage (`+9328..+9404`) and error exits to `+9228`.
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



@[local simp, local arm64_norm, local wp_norm]
theorem v2hse3_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse3_x23_add_193_sext (fsp : BitVec 64) :
    (fsp + 848#64) + (193#64).signExtend 64 = fsp + 1041#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse3_x25_add_65_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (65#64).signExtend 64 = fsp + 1857#64 := by bv_kernel

/-! ## `receivingCt1 = none` Branch (`+9328 -> +11024 -> +9228`) -/

theorem v2hse3_byte_pointsTo64_eq_pointsTo64_byte (a w : BitVec 64) (b : BitVec 8) :
    (a ↦₆₄ w) ∗ ((a + 8#64) ↦₈ b) =
      (a ↦₈ EncoderFromPb.loByte w) ∗ ((a + 1#64) ↦₆₄ EncoderFromPb.unshiftWord w b) := by
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo64_eq_pointsToBytes (a + 1#64),
      ← ProofLib.pointsToBytes_cons,
      EncoderFromPb.loByte_cons_unpack64_unshiftWord w b,
      ProofLib.pointsToBytes_append a (unpack64 w) [b], unpack64_length]
  simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]

theorem v2hse3_triple64_to_byte_qword_tail7 (a w8 w16 w24 : BitVec 64) :
    (a ↦₆₄ w8) ∗ ((a + 8#64) ↦₆₄ w16) ∗ ((a + 16#64) ↦₆₄ w24) =
      (a ↦₈ EncoderFromPb.loByte w8) ∗
      ((a + 1#64) ↦₁₂₈
        (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24) ++
         EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 w24) := by
  have hp := EncoderFromPb.pair64_to_byte_word_tail7 (a + 8#64) w16 w24
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  have ha17 : a + 8#64 + 9#64 = a + 17#64 := by bv_omega
  rw [ha16, ha9, ha17] at hp
  have hq := EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))
    (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24))
  have ha9' : a + 1#64 + 8#64 = a + 9#64 := by bv_omega
  rw [ha9'] at hq
  rw [hp, ← sepConj_assoc, ← sepConj_assoc,
      v2hse3_byte_pointsTo64_eq_pointsTo64_byte a w8 (EncoderFromPb.loByte w16),
      sepConj_assoc (a ↦₈ EncoderFromPb.loByte w8),
      sepConj_assoc (a ↦₈ EncoderFromPb.loByte w8), hq]

theorem v2hse3_byte_qword_mem7_to_triple64 (a w8 w16 w24 : BitVec 64) :
    (a ↦₈ EncoderFromPb.loByte w8) ∗
    ((a + 1#64) ↦₁₂₈
      (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24) ++
       EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))) ∗
    memRegion (a + 17#64) 7 ⊢
    ∃∗ u16 : BitVec 64,
      (a ↦₆₄ w8) ∗ ((a + 8#64) ↦₆₄ w16) ∗ ((a + 16#64) ↦₆₄ u16) := by
  have hq := EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))
    (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24))
  have ha9 : a + 1#64 + 8#64 = a + 9#64 := by bv_omega
  rw [ha9] at hq
  rw [← hq, ← sepConj_assoc, ← sepConj_assoc,
      ← v2hse3_byte_pointsTo64_eq_pointsTo64_byte a w8 (EncoderFromPb.loByte w16),
      sepConj_assoc, sepConj_assoc]
  have hjoin : ((a + 8#64) ↦₈ EncoderFromPb.loByte w16) ∗
      (((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
       memRegion (a + 17#64) 7) ⊢
      ((a + 8#64) ↦₆₄ w16) ∗ (∃∗ u16 : BitVec 64, (a + 16#64) ↦₆₄ u16) := by
    have hb : ((a + 8#64) ↦₈ EncoderFromPb.loByte w16) ∗
        ((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) =
        ((a + 8#64) ↦₆₄ w16) ∗ ((a + 16#64) ↦₈ EncoderFromPb.loByte w24) := by
      have h := (v2hse3_byte_pointsTo64_eq_pointsTo64_byte (a + 8#64) w16 (EncoderFromPb.loByte w24)).symm
      have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
      have ha9' : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
      rw [ha16, ha9'] at h
      exact h
    rw [← sepConj_assoc, hb, sepConj_assoc]
    refine sepConj_mono_right ?_
    have hm : memRegion (a + 16#64) 1 ∗ memRegion (a + 17#64) 7 = memRegion (a + 16#64) 8 := by
      rw [← ProofLib.memRegion_split' (b := a + 16#64) (n := 1) (k := 7)
        (b' := a + 17#64) rfl (by bv_omega) (by decide)]
    rw [← ProofLib.memRegion_eight (a + 16#64), ← hm]
    exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)
  refine Entails.trans (sepConj_mono_right hjoin) ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right]
  exact Entails.refl _

theorem v2hse3_memRegion_1848_split_decCopy (fsp : BitVec 64) :
    memRegion (fsp + 1848#64) 40 ⊢
      (∃∗ z0 : BitVec 64, (fsp + 1848#64) ↦₆₄ z0) ∗
      (∃∗ b8 : BitVec 8, (fsp + 1856#64) ↦₈ b8) ∗
      (∃∗ q9_lo : BitVec 64, (fsp + 1857#64) ↦₆₄ q9_lo) ∗
      (∃∗ q9_hi : BitVec 64, (fsp + 1865#64) ↦₆₄ q9_hi) ∗
      memRegion (fsp + 1873#64) 7 ∗
      (∃∗ z32 : BitVec 64, (fsp + 1880#64) ↦₆₄ z32) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem8_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    mem64_entails _

theorem v2hse3_fsp1040_to_step9332 (fsp d8 d16 d24 d32 : BitVec 64) :
    ((fsp + 1040#64) ↦₆₄ d8) ∗
    ((fsp + 1048#64) ↦₆₄ d16) ∗
    ((fsp + 1056#64) ↦₆₄ d24) ∗
    ((fsp + 1064#64) ↦₆₄ d32) ⊢
      ((fsp + 1040#64) ↦₈ EncoderFromPb.loByte d8) ∗
      ((fsp + 1041#64) ↦₆₄ EncoderFromPb.unshiftWord d8 (EncoderFromPb.loByte d16)) ∗
      ((fsp + 1049#64) ↦₆₄ EncoderFromPb.unshiftWord d16 (EncoderFromPb.loByte d24)) ∗
      ((fsp + 1057#64) ↦ₛ EncoderFromPb.hiBytes7 d24) ∗
      ((fsp + 1064#64) ↦₆₄ d32) := by
  have htri := v2hse3_triple64_to_byte_qword_tail7 (fsp + 1040#64) d8 d16 d24
  simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
    v2hse3_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc] at htri
  refine Entails.trans (Entails.of_eq (show _ =
    (((fsp + 1040#64) ↦₆₄ d8) ∗ ((fsp + 1048#64) ↦₆₄ d16) ∗ ((fsp + 1056#64) ↦₆₄ d24)) ∗
    ((fsp + 1064#64) ↦₆₄ d32) by ac_rfl)) ?_
  rw [htri]
  exact Entails.of_eq (by ac_rfl)

theorem v2hse3_resultPolyDecoder_err_entails_tag_392 (A : RustAlloc) (fsp : BitVec 64)
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

theorem v2hse3_1888_tag_392_to_memRegion_400 (fsp tag : BitVec 64) :
    ((fsp + 1888#64) ↦₆₄ tag) ∗ memRegion (fsp + 1896#64) 392 ⊢
      memRegion (fsp + 1888#64) 400 := by
  rw [ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 8) (k := 392)
        (b' := fsp + 1896#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

end CryptoVerification.SpqrV1.States.FromPb

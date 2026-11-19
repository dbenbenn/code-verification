/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 10 (`Ct2Sampled`, `+1632`) — Encoder Dispatch

Proves the `+1632 -> +1720` field loads, the `sending_ct2 = none` error branch (`+5728 -> +7212`),
the `ProtoPolynomialEncoder` copy and `<PolyEncoder>::from_pb` call (`+5728 -> +5808`), post-call
`Err` (`+5808 -> +5820`) and `Ok` (`+5808 -> +7904`) branches, and `PolyEncoder` cell-unpacking
helpers.
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

private theorem v10_add_5804_add_27192_eq (x : BitVec 64) :
    (x + 5804#64) + 27192#64 = x + 32996#64 := by bv_omega

theorem v10_cap_add_two_beq_zero_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    (cap + 2#64 == 0#64) = false :=
  Bool.eq_false_iff.mpr (cap_add_two_beq_zero_false hlt)

theorem v10_cap_add_one_beq_zero_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have h1 : cap = noneCap := by
    change cap + 1#64 = 0#64 at h
    bv_omega
  subst h1
  revert hlt; decide

@[local arm64_norm, local wp_norm]
theorem v10_reconstruct_p1 (p1 : BitVec 64) :
    ((((p1.extractLsb' 0 8).zeroExtend 32).zeroExtend 64 |||
      ((((p1.extractLsb' 8 32).zeroExtend 64 |||
        ((((p1.extractLsb' 40 16).zeroExtend 32 |||
          ((p1.extractLsb' 56 8).zeroExtend 32 <<< 16#64)).zeroExtend 64) <<< 32#64)) <<< 8#64))) : BitVec 64) = p1 := by
  bv_kernel

theorem v10_triple64_eq_byte_q128_tail7 (a w0 w8 w16 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) =
      (a ↦₈ loByte w0) ∗
      ((a + 1#64) ↦₁₂₈ (unshiftWord w8 (loByte w16) ++ unshiftWord w0 (loByte w8))) ∗
      ((a + 17#64) ↦ₛ hiBytes7 w16) := by
  have h2 := pair64_to_byte_word_tail7 (a + 8#64) w8 w16
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have ha17 : (a + 8#64) + 9#64 = a + 17#64 := by bv_omega
  rw [ha16, ha9, ha17] at h2
  have h1b :
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ loByte w8) =
        (a ↦₈ loByte w0) ∗ ((a + 1#64) ↦₆₄ unshiftWord w0 (loByte w8)) := by
    rw [pointsTo64_eq_pointsToBytes a w0, pointsTo64_eq_pointsToBytes (a + 1#64),
        ← ProofLib.pointsToBytes_cons, loByte_cons_unpack64_unshiftWord w0 (loByte w8),
        ProofLib.pointsToBytes_append a (unpack64 w0) [loByte w8], unpack64_length]
    simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]
  have hq := pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (unshiftWord w0 (loByte w8)) (unshiftWord w8 (loByte w16))
  have ha1_8 : (a + 1#64) + 8#64 = a + 9#64 := by bv_omega
  rw [ha1_8] at hq
  rw [h2, ← sepConj_assoc, ← sepConj_assoc, h1b,
      sepConj_assoc (a ↦₈ loByte w0), sepConj_assoc, hq]

theorem v10_right64_eq_unshift_hiBytes7 (p ptr len : BitVec 64) :
    (p ↦ₛ loBytes7 (unshiftWord ptr (loByte len))) ∗ ((p + 7#64) ↦₆₄ len) =
      (p ↦₆₄ unshiftWord ptr (loByte len)) ∗ ((p + 8#64) ↦ₛ hiBytes7 len) := by
  rw [pointsTo64_eq_pointsToBytes (p + 7#64) len]
  have h7 : p + BitVec.ofNat 64 (loBytes7 (unshiftWord ptr (loByte len))).length = p + 7#64 := by
    rw [length_loBytes7]
  rw [← h7, ← ProofLib.pointsToBytes_append p (loBytes7 (unshiftWord ptr (loByte len))) (unpack64 len),
      loBytes7_unshiftWord_append_unpack64 ptr len,
      ProofLib.pointsToBytes_append p (unpack64 (unshiftWord ptr (loByte len))) (hiBytes7 len),
      unpack64_length, ← pointsTo64_eq_pointsToBytes p (unshiftWord ptr (loByte len))]

theorem v10_dst24_split (a : BitVec 64) :
    memRegion a 24 ⊢
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
      (∃∗ q1 : BitVec 128, (a + 1#64) ↦₁₂₈ q1) ∗
      memRegion (a + 17#64) 7 := by
  rw [ProofLib.memRegion_split a 1 23 (by decide),
      ProofLib.memRegion_one a,
      ProofLib.memRegion_split' (b := a + 1#64) (n := 16) (k := 7)
        (b' := a + 17#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_left (memRegion_16_entails_128 (a + 1#64)))

theorem v10_dst24_realign_mid (a w0 w8 w16 : BitVec 64) :
    (a ↦₈ loByte w0) ∗
      ((a + 1#64) ↦₁₂₈ (unshiftWord w8 (loByte w16) ++ unshiftWord w0 (loByte w8))) ∗
      memRegion (a + 17#64) 7 ⊢
    (a ↦₈ loByte w0) ∗
      ((a + 1#64) ↦₆₄ unshiftWord w0 (loByte w8)) ∗
      ((a + 9#64) ↦ₛ loBytes7 (unshiftWord w8 (loByte w16))) ∗
      (∃∗ v16 : BitVec 64, (a + 16#64) ↦₆₄ v16) := by
  have hq := (pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (unshiftWord w0 (loByte w8)) (unshiftWord w8 (loByte w16))).symm
  have ha9 : (a + 1#64) + 8#64 = a + 9#64 := by bv_omega
  rw [ha9] at hq
  rw [hq, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  have hu := unshift_left64_to_right64 (a + 9#64) w8 w16
  have ha17 : (a + 9#64) + 8#64 = a + 17#64 := by bv_omega
  have ha16 : (a + 9#64) + 7#64 = a + 16#64 := by bv_omega
  rw [ha17, ha16] at hu
  exact hu

theorem v10_dst24_realign_final (a w0 w8 w16 : BitVec 64) :
    (a ↦₈ loByte w0) ∗
      ((a + 1#64) ↦₆₄ unshiftWord w0 (loByte w8)) ∗
      ((a + 9#64) ↦ₛ loBytes7 (unshiftWord w8 (loByte w16))) ∗
      ((a + 16#64) ↦₆₄ w16) =
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) := by
  have hr := v10_right64_eq_unshift_hiBytes7 (a + 9#64) w8 w16
  have ha16 : (a + 9#64) + 7#64 = a + 16#64 := by bv_omega
  have ha17 : (a + 9#64) + 8#64 = a + 17#64 := by bv_omega
  rw [ha16, ha17] at hr
  have hq := pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (unshiftWord w0 (loByte w8)) (unshiftWord w8 (loByte w16))
  have ha9 : (a + 1#64) + 8#64 = a + 9#64 := by bv_omega
  rw [ha9] at hq
  rw [hr, ← sepConj_assoc ((a + 1#64) ↦₆₄ _), hq,
      ← v10_triple64_eq_byte_q128_tail7 a w0 w8 w16]

theorem v10_pbA_16_realign_rest (pbA ptr_pts len_pts cap_polys : BitVec 64) (Rest : SepProp) :
    ((pbA + 16#64) ↦₆₄ ptr_pts) ∗ ((pbA + 24#64) ↦₆₄ len_pts) ∗
      ((pbA + 32#64) ↦₆₄ cap_polys) ∗ Rest =
    ((pbA + 16#64) ↦₈ loByte ptr_pts) ∗
      ((pbA + 17#64) ↦₆₄ unshiftWord ptr_pts (loByte len_pts)) ∗
      ((pbA + 25#64) ↦₆₄ unshiftWord len_pts (loByte cap_polys)) ∗
      ((pbA + 33#64) ↦ₛ hiBytes7 cap_polys) ∗ Rest := by
  have h := v10_triple64_eq_byte_q128_tail7 (pbA + 16#64) ptr_pts len_pts cap_polys
  unfold pointsTo128 at h
  have ha24 : (pbA + 16#64) + 8#64 = pbA + 24#64 := by bv_omega
  have ha32 : (pbA + 16#64) + 16#64 = pbA + 32#64 := by bv_omega
  have ha17 : (pbA + 16#64) + 1#64 = pbA + 17#64 := by bv_omega
  have ha25 : (pbA + 17#64) + 8#64 = pbA + 25#64 := by bv_omega
  have ha33 : (pbA + 16#64) + 17#64 = pbA + 33#64 := by bv_omega
  have hlo : (unshiftWord len_pts (loByte cap_polys) ++ unshiftWord ptr_pts (loByte len_pts)).extractLsb' 0 64 =
      unshiftWord ptr_pts (loByte len_pts) := by bv_kernel
  have hhi : (unshiftWord len_pts (loByte cap_polys) ++ unshiftWord ptr_pts (loByte len_pts)).extractLsb' 64 64 =
      unshiftWord len_pts (loByte cap_polys) := by bv_kernel
  rw [ha24, ha32, ha17, ha25, ha33, hlo, hhi] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v10_pbA_16_unrealign_rest (pbA ptr_pts len_pts cap_polys : BitVec 64) (Rest : SepProp) :
    ((pbA + 16#64) ↦₈ loByte ptr_pts) ∗
      ((pbA + 17#64) ↦₆₄ unshiftWord ptr_pts (loByte len_pts)) ∗
      ((pbA + 25#64) ↦₆₄ unshiftWord len_pts (loByte cap_polys)) ∗
      ((pbA + 33#64) ↦ₛ hiBytes7 cap_polys) ∗ Rest =
    ((pbA + 16#64) ↦₆₄ ptr_pts) ∗ ((pbA + 24#64) ↦₆₄ len_pts) ∗
      ((pbA + 32#64) ↦₆₄ cap_polys) ∗ Rest :=
  (v10_pbA_16_realign_rest pbA ptr_pts len_pts cap_polys Rest).symm

theorem v10_fsp_1409_realign_rest (fsp w9 u1417 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1409#64) ↦₆₄ w9) ∗ ((fsp + 1417#64) ↦ₛ loBytes7 u1417) ∗ Rest =
      ((fsp + 1409#64) ↦ₛ loBytes7 w9) ∗ ((fsp + 1416#64) ↦₆₄ overlapWord7 w9 u1417) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 1409#64) w9 u1417
  have ha8 : (fsp + 1409#64) + 8#64 = fsp + 1417#64 := by bv_omega
  have ha7 : (fsp + 1409#64) + 7#64 = fsp + 1416#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v10_fsp_1400_realign_rest (fsp ptr_pts len_pts cap_polys : BitVec 64) (Rest : SepProp) :
    ((fsp + 1400#64) ↦₈ loByte ptr_pts) ∗
      ((fsp + 1401#64) ↦₆₄ unshiftWord ptr_pts (loByte len_pts)) ∗
      ((fsp + 1409#64) ↦ₛ loBytes7 (unshiftWord len_pts (loByte cap_polys))) ∗
      ((fsp + 1416#64) ↦₆₄ cap_polys) ∗ Rest =
    ((fsp + 1400#64) ↦₆₄ ptr_pts) ∗
      ((fsp + 1408#64) ↦₆₄ len_pts) ∗
      ((fsp + 1416#64) ↦₆₄ cap_polys) ∗ Rest := by
  have hdst := v10_dst24_realign_final (fsp + 1400#64) ptr_pts len_pts cap_polys
  have hd1 : (fsp + 1400#64) + 1#64 = fsp + 1401#64 := by bv_omega
  have hd9 : (fsp + 1400#64) + 9#64 = fsp + 1409#64 := by bv_omega
  have hd16 : (fsp + 1400#64) + 16#64 = fsp + 1416#64 := by bv_omega
  have hd8 : (fsp + 1400#64) + 8#64 = fsp + 1408#64 := by bv_omega
  rw [hd1, hd9, hd16, hd8] at hdst
  have h' := congrArg (· ∗ Rest) hdst
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

@[local arm64_norm, local wp_norm]
theorem v10_fsp_1264_add_137 (fsp : BitVec 64) :
    (fsp + 1264#64) + 137#64 = fsp + 1401#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v10_fsp_1401_add_8 (fsp : BitVec 64) :
    (fsp + 1401#64) + 8#64 = fsp + 1409#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v10_fsp_1424_add_8 (fsp : BitVec 64) :
    (fsp + 1424#64) + 8#64 = fsp + 1432#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v10_pbA_17_add_8 (pbA : BitVec 64) :
    (pbA + 17#64) + 8#64 = pbA + 25#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v10_pbA_40_add_8 (pbA : BitVec 64) :
    (pbA + 40#64) + 8#64 = pbA + 48#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v10_extract_loByte_zext (w : BitVec 64) :
    ((loByte w).zeroExtend 32).extractLsb' 0 8 = loByte w := by
  unfold loByte
  bv_kernel

theorem v10_resultPolyEncoder_err_entails_tag_392 (A : RustAlloc) (fsp : BitVec 64)
    (err : PolynomialError) :
    resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ⊢
      ((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392 := by
  dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag,
    resultPolyEncoderErrByteOff, resultPolyEncoderErrTailSize]
  have hm8 : ((fsp + 1896#64) ↦₈ polynomialErrorByte err) ∗ memRegion (fsp + 1897#64) 391 ⊢
      memRegion (fsp + 1896#64) 392 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1896#64) (n := 1) (k := 391)
          (b' := fsp + 1897#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (fsp + 1896#64) (polynomialErrorByte err))
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  have ha1897 : (fsp + 1888#64) + 9#64 = fsp + 1897#64 := by bv_omega
  rw [ha1896, ha1897]
  exact sepConj_mono_right hm8

/-- Pack 8 bytes (little-endian) from `bs` into a `BitVec 64`. -/
@[expose] def v10_pack64 (bs : List (BitVec 8)) : BitVec 64 :=
  (bs.getD 7 0#8) ++ (bs.getD 6 0#8) ++ (bs.getD 5 0#8) ++ (bs.getD 4 0#8) ++
  (bs.getD 3 0#8) ++ (bs.getD 2 0#8) ++ (bs.getD 1 0#8) ++ (bs.getD 0 0#8)

theorem v10_unpack64_pack64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (v10_pack64 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h; done)
  change [_, _, _, _, _, _, _, _] = [b0, b1, b2, b3, b4, b5, b6, b7]
  dsimp only [v10_pack64, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v10_pointsToBytes_eq_pack64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ v10_pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, v10_unpack64_pack64 bs h]

/-- Pack 16 bytes (little-endian) from `bs` into a `BitVec 128`. -/
@[expose] def v10_pack128 (bs : List (BitVec 8)) : BitVec 128 :=
  v10_pack64 (bs.drop 8) ++ v10_pack64 (bs.take 8)

theorem v10_pointsToBytes_eq_pack128 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 16) :
    (a ↦ₛ bs) = (a ↦₁₂₈ v10_pack128 bs) := by
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : (bs.drop 8).length = 8 := by simp [h]
  nth_rw 1 [← List.take_append_drop 8 bs]
  rw [ProofLib.pointsToBytes_append a (bs.take 8) (bs.drop 8), h1]
  change (a ↦ₛ bs.take 8) ∗ ((a + 8#64) ↦ₛ bs.drop 8) = (a ↦₁₂₈ v10_pack128 bs)
  rw [v10_pointsToBytes_eq_pack64 a (bs.take 8) h1,
      v10_pointsToBytes_eq_pack64 (a + 8#64) (bs.drop 8) h2,
      pointsTo64_pair_eq_pointsTo128]
  rfl

/-- 8-byte word at byte offset `i` within `bs`. -/
@[expose] def v10_wordAt (bs : List (BitVec 8)) (i : Nat) : BitVec 64 :=
  v10_pack64 ((bs.drop i).take 8)

/-- 16-byte quadword at byte offset `i` within `bs`. -/
@[expose] def v10_quadAt (bs : List (BitVec 8)) (i : Nat) : BitVec 128 :=
  v10_pack128 ((bs.drop i).take 16)

theorem v10_bs_drop_step8 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 o2 : BitVec 64) (i : Nat) {Q : SepProp}
    (hrest : ((a + o2) ↦ₛ bs.drop (i + 8)) = Q)
    (hi : i + 8 ≤ 384 := by decide)
    (ho : o1 + 8#64 = o2 := by rfl) :
    ((a + o1) ↦ₛ bs.drop i) = ((a + o1) ↦₆₄ v10_wordAt bs i) ∗ Q := by
  have htake_len : ((bs.drop i).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hbs]; omega
  have hsplit : bs.drop i = (bs.drop i).take 8 ++ bs.drop (i + 8) := by
    rw [← List.drop_drop, List.take_append_drop]
  have ha : (a + o1) + BitVec.ofNat 64 ((bs.drop i).take 8).length = a + o2 := by
    rw [htake_len, BitVec.add_assoc, ho]
  rw [hsplit, ProofLib.pointsToBytes_append (a + o1) ((bs.drop i).take 8) (bs.drop (i + 8)),
      ha, v10_pointsToBytes_eq_pack64 (a + o1) ((bs.drop i).take 8) htake_len, hrest]
  rfl

theorem v10_bs_drop_step16 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 o2 : BitVec 64) (i : Nat) {Q : SepProp}
    (hrest : ((a + o2) ↦ₛ bs.drop (i + 16)) = Q)
    (hi : i + 16 ≤ 384 := by decide)
    (ho : o1 + 16#64 = o2 := by rfl) :
    ((a + o1) ↦ₛ bs.drop i) = ((a + o1) ↦₁₂₈ v10_quadAt bs i) ∗ Q := by
  have htake_len : ((bs.drop i).take 16).length = 16 := by
    rw [List.length_take, List.length_drop, hbs]; omega
  have hsplit : bs.drop i = (bs.drop i).take 16 ++ bs.drop (i + 16) := by
    rw [← List.drop_drop, List.take_append_drop]
  have ha : (a + o1) + BitVec.ofNat 64 ((bs.drop i).take 16).length = a + o2 := by
    rw [htake_len, BitVec.add_assoc, ho]
  rw [hsplit, ProofLib.pointsToBytes_append (a + o1) ((bs.drop i).take 16) (bs.drop (i + 16)),
      ha, v10_pointsToBytes_eq_pack128 (a + o1) ((bs.drop i).take 16) htake_len, hrest]
  rfl

theorem v10_bs_drop_end8 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 : BitVec 64) :
    ((a + o1) ↦ₛ bs.drop 376) = ((a + o1) ↦₆₄ v10_wordAt bs 376) := by
  have hlen : (bs.drop 376).length = 8 := by rw [List.length_drop, hbs]
  have htake : (bs.drop 376).take 8 = bs.drop 376 := List.take_of_length_le (by omega)
  rw [v10_pointsToBytes_eq_pack64 (a + o1) (bs.drop 376) hlen]
  unfold v10_wordAt
  rw [htake]

/-- The 384-byte `PolyEncoder` vector-headers region at `a + 8..a + 392` decomposed into
the exact 64-bit and 128-bit cells accessed at `+7904..+8176` (for `a = fsp + 1888`) and
written by `epilogueOutFull` (for `a = out + 8`). -/
@[expose] def v10_encCellsAt (a : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ((a + 8#64) ↦₆₄ v10_wordAt bs 0) ∗
  ((a + 16#64) ↦₆₄ v10_wordAt bs 8) ∗
  ((a + 24#64) ↦₆₄ v10_wordAt bs 16) ∗
  ((a + 32#64) ↦₆₄ v10_wordAt bs 24) ∗
  ((a + 40#64) ↦₆₄ v10_wordAt bs 32) ∗
  ((a + 48#64) ↦₆₄ v10_wordAt bs 40) ∗
  ((a + 56#64) ↦₆₄ v10_wordAt bs 48) ∗
  ((a + 64#64) ↦₆₄ v10_wordAt bs 56) ∗
  ((a + 72#64) ↦₆₄ v10_wordAt bs 64) ∗
  ((a + 80#64) ↦₆₄ v10_wordAt bs 72) ∗
  ((a + 88#64) ↦₆₄ v10_wordAt bs 80) ∗
  ((a + 96#64) ↦₆₄ v10_wordAt bs 88) ∗
  ((a + 104#64) ↦₆₄ v10_wordAt bs 96) ∗
  ((a + 112#64) ↦₆₄ v10_wordAt bs 104) ∗
  ((a + 120#64) ↦₆₄ v10_wordAt bs 112) ∗
  ((a + 128#64) ↦₆₄ v10_wordAt bs 120) ∗
  ((a + 136#64) ↦₆₄ v10_wordAt bs 128) ∗
  ((a + 144#64) ↦₆₄ v10_wordAt bs 136) ∗
  ((a + 152#64) ↦₆₄ v10_wordAt bs 144) ∗
  ((a + 160#64) ↦₁₂₈ v10_quadAt bs 152) ∗
  ((a + 176#64) ↦₁₂₈ v10_quadAt bs 168) ∗
  ((a + 192#64) ↦₁₂₈ v10_quadAt bs 184) ∗
  ((a + 208#64) ↦₁₂₈ v10_quadAt bs 200) ∗
  ((a + 224#64) ↦₁₂₈ v10_quadAt bs 216) ∗
  ((a + 240#64) ↦₁₂₈ v10_quadAt bs 232) ∗
  ((a + 256#64) ↦₁₂₈ v10_quadAt bs 248) ∗
  ((a + 272#64) ↦₁₂₈ v10_quadAt bs 264) ∗
  ((a + 288#64) ↦₁₂₈ v10_quadAt bs 280) ∗
  ((a + 304#64) ↦₁₂₈ v10_quadAt bs 296) ∗
  ((a + 320#64) ↦₁₂₈ v10_quadAt bs 312) ∗
  ((a + 336#64) ↦₁₂₈ v10_quadAt bs 328) ∗
  ((a + 352#64) ↦₁₂₈ v10_quadAt bs 344) ∗
  ((a + 368#64) ↦₁₂₈ v10_quadAt bs 360) ∗
  ((a + 384#64) ↦₆₄ v10_wordAt bs 376)

theorem v10_bs384_eq_encCells (bs : List (BitVec 8)) (hbs : bs.length = 384) (a : BitVec 64) :
    ((a + 8#64) ↦ₛ bs) = v10_encCellsAt a bs := by
  unfold v10_encCellsAt
  change ((a + 8#64) ↦ₛ bs.drop 0) = _
  exact
    v10_bs_drop_step8 hbs a 8#64 16#64 0 <|
    v10_bs_drop_step8 hbs a 16#64 24#64 8 <|
    v10_bs_drop_step8 hbs a 24#64 32#64 16 <|
    v10_bs_drop_step8 hbs a 32#64 40#64 24 <|
    v10_bs_drop_step8 hbs a 40#64 48#64 32 <|
    v10_bs_drop_step8 hbs a 48#64 56#64 40 <|
    v10_bs_drop_step8 hbs a 56#64 64#64 48 <|
    v10_bs_drop_step8 hbs a 64#64 72#64 56 <|
    v10_bs_drop_step8 hbs a 72#64 80#64 64 <|
    v10_bs_drop_step8 hbs a 80#64 88#64 72 <|
    v10_bs_drop_step8 hbs a 88#64 96#64 80 <|
    v10_bs_drop_step8 hbs a 96#64 104#64 88 <|
    v10_bs_drop_step8 hbs a 104#64 112#64 96 <|
    v10_bs_drop_step8 hbs a 112#64 120#64 104 <|
    v10_bs_drop_step8 hbs a 120#64 128#64 112 <|
    v10_bs_drop_step8 hbs a 128#64 136#64 120 <|
    v10_bs_drop_step8 hbs a 136#64 144#64 128 <|
    v10_bs_drop_step8 hbs a 144#64 152#64 136 <|
    v10_bs_drop_step8 hbs a 152#64 160#64 144 <|
    v10_bs_drop_step16 hbs a 160#64 176#64 152 <|
    v10_bs_drop_step16 hbs a 176#64 192#64 168 <|
    v10_bs_drop_step16 hbs a 192#64 208#64 184 <|
    v10_bs_drop_step16 hbs a 208#64 224#64 200 <|
    v10_bs_drop_step16 hbs a 224#64 240#64 216 <|
    v10_bs_drop_step16 hbs a 240#64 256#64 232 <|
    v10_bs_drop_step16 hbs a 256#64 272#64 248 <|
    v10_bs_drop_step16 hbs a 272#64 288#64 264 <|
    v10_bs_drop_step16 hbs a 288#64 304#64 280 <|
    v10_bs_drop_step16 hbs a 304#64 320#64 296 <|
    v10_bs_drop_step16 hbs a 320#64 336#64 312 <|
    v10_bs_drop_step16 hbs a 336#64 352#64 328 <|
    v10_bs_drop_step16 hbs a 352#64 368#64 344 <|
    v10_bs_drop_step16 hbs a 368#64 384#64 360 <|
    v10_bs_drop_end8 hbs a 384#64

theorem v10_pointsTo32_pair_eq_pointsTo64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes]
  change (a ↦ₛ unpack32 lo) ∗ ((a + BitVec.ofNat 64 (unpack32 lo).length) ↦ₛ unpack32 hi) = _
  rw [← ProofLib.pointsToBytes_append a (unpack32 lo) (unpack32 hi)]
  congr 1
  unfold unpack64 unpack32
  simp only [List.singleton_append, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v10_polyEncoderAt_relocate (A : RustAlloc) (a1 a2 : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a1 enc ⊢
      ∃∗ tag : BitVec 64, ∃∗ bs : { l : List (BitVec 8) // l.length = 384 },
      ∃∗ hi32 : BitVec 32, ∃∗ P_heap : SepProp,
        ⌜(tag = 0#64 ∨ tag = 1#64) ∧
          ((a2 ↦₆₄ tag) ∗ ((a2 + 8#64) ↦ₛ bs.val) ∗
           ((a2 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
            polyEncoderAt A a2 enc)⌝ ∗
        (a1 ↦₆₄ tag) ∗
        ((a1 + 8#64) ↦ₛ bs.val) ∗
        ((a1 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        P_heap := by
  unfold polyEncoderAt encoderStateAt polyEncoderPointsTag polyEncoderPolysTag
    polyEncoderVecsOff polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  rw [ProofLib.memRegion_four (a1 + 396#64)]
  cases hs : enc.s with
  | points pts =>
    dsimp only
    rw [pointListOf_eq_vecGF16ListOf A pts (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (pts.map Point.value) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; rintro ⟨hpts_len, hpts_bound⟩
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (pts.map Point.value)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (pts.map Point.value) hpins_len, List.length_map, hpts_len]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v10_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right 0#64
      (Entails.sepExists_right ⟨vecHeadersBytesOf pins (pts.map Point.value), hbs_len⟩
        (Entails.sepExists_right hi32
          (Entails.sepExists_right (vecGF16HeapList A pins (pts.map Point.value)) ?_)))
    refine Entails.pure_right ⟨Or.inl rfl, ?_⟩ (Entails.of_eq (by ac_rfl))
    rw [pointListOf_eq_vecGF16ListOf A pts (a2 + 8#64),
        ← v10_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (pts.map Point.value) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 0#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ∗
       vecGF16HeapList A pins (pts.map Point.value)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right ⟨hpts_len, hpts_bound⟩ (Entails.of_eq (by ac_rfl))
  | polys ps =>
    dsimp only
    rw [polyListOf_eq_vecGF16ListOf A ps (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (ps.map LibsignalSpqrV1.Poly.coefficients) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; intro hps_len
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients) hpins_len, List.length_map, hps_len]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v10_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right 1#64
      (Entails.sepExists_right ⟨vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients), hbs_len⟩
        (Entails.sepExists_right hi32
          (Entails.sepExists_right (vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ?_)))
    refine Entails.pure_right ⟨Or.inr rfl, ?_⟩ (Entails.of_eq (by ac_rfl))
    rw [polyListOf_eq_vecGF16ListOf A ps (a2 + 8#64),
        ← v10_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (ps.map LibsignalSpqrV1.Poly.coefficients) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 1#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
       vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right hps_len (Entails.of_eq (by ac_rfl))

end CryptoVerification.SpqrV1.States.FromPb


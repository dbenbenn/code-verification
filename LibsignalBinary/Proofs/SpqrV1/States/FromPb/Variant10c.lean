/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 10 (`Ct2Sampled`, `+1632`) — Epilogue Staging

Proves the `+7904 -> +8176` staging step (copying the decoded `PolyEncoder` into epilogue stack
slots and loading `Unchunked.Ct2Sent` fields), output reconstruction into `resultChunkedStatesAt`,
and the `+7904 -> s0.x30` return theorem.
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

/-! ## 1. Bitvector & Realignment Helpers for `+7904 -> +8176` and `epilogueOutFull` -/

/-- The 128-bit quadword loaded from `fsp + 2025` (`x11 + 137`) and stored to `fsp + 848`. -/
@[expose] def v10_midQ128 (w128 w136 w144 : BitVec 64) : BitVec 128 :=
  unshiftWord w136 (loByte w144) ++ unshiftWord w128 (loByte w136)

theorem v10_hiBytes7_eq_loBytes7_lsr8 (w : BitVec 64) :
    EncoderFromPb.hiBytes7 w = EncoderFromPb.loBytes7 (w >>> 8) := by
  change [_, _, _, _, _, _, _] = [_, _, _, _, _, _, _]
  refine congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·)
    (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (· :: []) ?_))))))
  all_goals bv_kernel

theorem v10_lsr8_lsl8 (v : BitVec 64) :
    (v >>> 8) <<< 8 = v &&& 0xffffffffffffff00#64 := by
  bv_kernel

theorem v10_unshift_lsr56 (w0 v : BitVec 64) :
    (unshiftWord w0 (loByte v)) >>> 56 = v &&& 0xff#64 := by
  unfold unshiftWord loByte
  bv_kernel

theorem v10_overlapWord7_unshift_lsr8 (w0 w8 : BitVec 64) :
    overlapWord7 (unshiftWord w0 (loByte w8)) (w8 >>> 8) = w8 := by
  unfold overlapWord7
  rw [v10_unshift_lsr56 w0 w8, v10_lsr8_lsl8 w8]
  bv_kernel

theorem v10_overlapWord7_midQ128_lsr8 (w128 w136 w144 : BitVec 64) :
    overlapWord7 ((v10_midQ128 w128 w136 w144).extractLsb' 64 64) (w144 >>> 8) = w144 := by
  have hhi : (v10_midQ128 w128 w136 w144).extractLsb' 64 64 = unshiftWord w136 (loByte w144) := by
    unfold v10_midQ128
    bv_kernel
  rw [hhi]
  exact v10_overlapWord7_unshift_lsr8 w136 w144

@[local arm64_norm, local wp_norm]
theorem v10_orr_x27_w80 (w80 : BitVec 64) :
    ((w80.extractLsb' 8 32).zeroExtend 64 |||
      ((((w80.extractLsb' 40 16).zeroExtend 32 |||
        ((w80.extractLsb' 56 8).zeroExtend 32 <<< 16#64)).zeroExtend 64) <<< 32#64)) =
      (w80.extractLsb' 8 56).zeroExtend 64 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v10_w80_d97 (w80 : BitVec 64) :
    ((w80.extractLsb' 8 56).zeroExtend 64).setWidth 32 = w80.extractLsb' 8 32 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v10_w80_h101 (w80 : BitVec 64) :
    ((((w80.extractLsb' 8 56).zeroExtend 64) >>> 32).setWidth 32).setWidth 16 =
      w80.extractLsb' 40 16 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v10_w80_b103 (w80 : BitVec 64) :
    ((((w80.extractLsb' 8 56).zeroExtend 64) >>> 48).setWidth 32).setWidth 8 =
      w80.extractLsb' 56 8 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v10_zext32_setWidth8 (b : BitVec 8) :
    (b.zeroExtend 32).setWidth 8 = b := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v10_fsp_1888_add_89 (fsp : BitVec 64) :
    (fsp + 1888#64) + 89#64 = fsp + 1977#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v10_fsp_1888_add_93 (fsp : BitVec 64) :
    (fsp + 1888#64) + 93#64 = fsp + 1981#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v10_fsp_1888_add_113 (fsp : BitVec 64) :
    (fsp + 1888#64) + 113#64 = fsp + 2001#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v10_fsp_1888_add_137 (fsp : BitVec 64) :
    (fsp + 1888#64) + 137#64 = fsp + 2025#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v10_fsp_848_add_39 (fsp : BitVec 64) :
    (fsp + 848#64) + 39#64 = fsp + 887#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v10_fsp_848_add_15 (fsp : BitVec 64) :
    (fsp + 848#64) + 15#64 = fsp + 863#64 := by bv_omega

theorem v10_fsp_1976_split_rest (fsp w80 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1976#64) ↦₆₄ w80) ∗ Rest =
      ((fsp + 1976#64) ↦₈ w80.extractLsb' 0 8) ∗
      ((fsp + 1977#64) ↦₃₂ w80.extractLsb' 8 32) ∗
      ((fsp + 1981#64) ↦₁₆ w80.extractLsb' 40 16) ∗
      ((fsp + 1983#64) ↦₈ w80.extractLsb' 56 8) ∗ Rest := by
  have h := v10_pointsTo64_split_1_4_2_1 (fsp + 1976#64) w80
  have ha1 : (fsp + 1976#64) + 1#64 = fsp + 1977#64 := by bv_omega
  have ha5 : (fsp + 1976#64) + 5#64 = fsp + 1981#64 := by bv_omega
  have ha7 : (fsp + 1976#64) + 7#64 = fsp + 1983#64 := by bv_omega
  rw [ha1, ha5, ha7] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v10_fsp_1976_unsplit_rest (fsp w80 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1976#64) ↦₈ w80.extractLsb' 0 8) ∗
      ((fsp + 1977#64) ↦₃₂ w80.extractLsb' 8 32) ∗
      ((fsp + 1981#64) ↦₁₆ w80.extractLsb' 40 16) ∗
      ((fsp + 1983#64) ↦₈ w80.extractLsb' 56 8) ∗ Rest =
      ((fsp + 1976#64) ↦₆₄ w80) ∗ Rest :=
  (v10_fsp_1976_split_rest fsp w80 Rest).symm

theorem v10_fsp_2024_realign_rest (fsp w128 w136 w144 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₆₄ w128) ∗ ((fsp + 2032#64) ↦₆₄ w136) ∗ ((fsp + 2040#64) ↦₆₄ w144) ∗ Rest =
      ((fsp + 2024#64) ↦₈ loByte w128) ∗
      ((fsp + 2025#64) ↦₆₄ (v10_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((fsp + 2033#64) ↦₆₄ (v10_midQ128 w128 w136 w144).extractLsb' 64 64) ∗
      ((fsp + 2041#64) ↦ₛ EncoderFromPb.hiBytes7 w144) ∗ Rest := by
  have h := v10_triple64_eq_byte_q128_tail7 (fsp + 2024#64) w128 w136 w144
  have ha8 : (fsp + 2024#64) + 8#64 = fsp + 2032#64 := by bv_omega
  have ha16 : (fsp + 2024#64) + 16#64 = fsp + 2040#64 := by bv_omega
  have ha1 : (fsp + 2024#64) + 1#64 = fsp + 2025#64 := by bv_omega
  have ha17 : (fsp + 2024#64) + 17#64 = fsp + 2041#64 := by bv_omega
  have ha2033 : (fsp + 2025#64) + 8#64 = fsp + 2033#64 := by bv_omega
  rw [ha8, ha16, ha1, ha17] at h
  change _ = ((fsp + 2024#64) ↦₈ loByte w128) ∗
    ((fsp + 2025#64) ↦₁₂₈ v10_midQ128 w128 w136 w144) ∗
    ((fsp + 2041#64) ↦ₛ EncoderFromPb.hiBytes7 w144) at h
  unfold pointsTo128 at h
  rw [ha2033] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v10_fsp_2024_unrealign_rest (fsp w128 w136 w144 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₈ loByte w128) ∗
      ((fsp + 2025#64) ↦₆₄ (v10_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((fsp + 2033#64) ↦₆₄ (v10_midQ128 w128 w136 w144).extractLsb' 64 64) ∗
      ((fsp + 2041#64) ↦ₛ EncoderFromPb.hiBytes7 w144) ∗ Rest =
    ((fsp + 2024#64) ↦₆₄ w128) ∗ ((fsp + 2032#64) ↦₆₄ w136) ∗ ((fsp + 2040#64) ↦₆₄ w144) ∗ Rest :=
  (v10_fsp_2024_realign_rest fsp w128 w136 w144 Rest).symm

theorem v10_fsp_2024_split_1_7_rest (fsp w128 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₆₄ w128) ∗ Rest =
      ((fsp + 2024#64) ↦₈ loByte w128) ∗
      ((fsp + 2025#64) ↦ₛ EncoderFromPb.hiBytes7 w128) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 2024#64) w128
  have ha1 : (fsp + 2024#64) + 1#64 = fsp + 2025#64 := by bv_omega
  rw [ha1] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v10_fsp_2024_unsplit_1_7_rest (fsp w128 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₈ loByte w128) ∗
      ((fsp + 2025#64) ↦ₛ EncoderFromPb.hiBytes7 w128) ∗ Rest =
      ((fsp + 2024#64) ↦₆₄ w128) ∗ Rest :=
  (v10_fsp_2024_split_1_7_rest fsp w128 Rest).symm

theorem v10_fsp_2000_realign_rest (fsp w104 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2000#64) ↦₆₄ w104) ∗ ((fsp + 2008#64) ↦₆₄ w112) ∗ Rest =
      ((fsp + 2000#64) ↦₈ loByte w104) ∗
      ((fsp + 2001#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗
      ((fsp + 2009#64) ↦ₛ EncoderFromPb.hiBytes7 w112) ∗ Rest := by
  have h := pair64_to_byte_word_tail7 (fsp + 2000#64) w104 w112
  have ha8 : (fsp + 2000#64) + 8#64 = fsp + 2008#64 := by bv_omega
  have ha1 : (fsp + 2000#64) + 1#64 = fsp + 2001#64 := by bv_omega
  have ha9 : (fsp + 2000#64) + 9#64 = fsp + 2009#64 := by bv_omega
  rw [ha8, ha1, ha9] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v10_fsp_2000_unrealign_rest (fsp w104 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2000#64) ↦₈ loByte w104) ∗
      ((fsp + 2001#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗
      ((fsp + 2009#64) ↦ₛ EncoderFromPb.hiBytes7 w112) ∗ Rest =
      ((fsp + 2000#64) ↦₆₄ w104) ∗ ((fsp + 2008#64) ↦₆₄ w112) ∗ Rest :=
  (v10_fsp_2000_realign_rest fsp w104 w112 Rest).symm

theorem v10_fsp_880_realign_rest (fsp u880 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880) ∗ ((fsp + 887#64) ↦₆₄ w112) ∗ Rest =
      ((fsp + 880#64) ↦₆₄ overlapLow7 u880 w112) ∗
      ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (w112 >>> 8)) ∗ Rest := by
  have h := loBytes7_pointsTo64_eq_overlap (fsp + 880#64) u880 w112
  have ha7 : (fsp + 880#64) + 7#64 = fsp + 887#64 := by bv_omega
  have ha8 : (fsp + 880#64) + 8#64 = fsp + 888#64 := by bv_omega
  rw [ha7, ha8, v10_hiBytes7_eq_loBytes7_lsr8 w112] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v10_fsp_856_realign_rest (fsp w856 u864 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦₆₄ w856) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗ Rest =
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 w856) ∗
      ((fsp + 863#64) ↦₆₄ overlapWord7 w856 u864) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 856#64) w856 u864
  have ha8 : (fsp + 856#64) + 8#64 = fsp + 864#64 := by bv_omega
  have ha7 : (fsp + 856#64) + 7#64 = fsp + 863#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v10_fsp_856_unrealign_midQ128_rest (fsp w128 w136 w144 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 ((v10_midQ128 w128 w136 w144).extractLsb' 64 64)) ∗
      ((fsp + 863#64) ↦₆₄ w144) ∗ Rest =
    ((fsp + 856#64) ↦₆₄ (v10_midQ128 w128 w136 w144).extractLsb' 64 64) ∗
      ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (w144 >>> 8)) ∗ Rest := by
  have h := (v10_fsp_856_realign_rest fsp ((v10_midQ128 w128 w136 w144).extractLsb' 64 64)
    (w144 >>> 8) Rest).symm
  rwa [v10_overlapWord7_midQ128_lsr8 w128 w136 w144] at h

/-! ## 2. Step `+7904 -> +8176` (`0x5bf84 -> 0x5c094`, 68 instructions) -/

/-- Active stack slots in `fsp + 160..895` written by `+7904..+8176` (before execution). -/
@[expose] def v10_stagingSlotsPre (fsp : BitVec 64)
    (u160 : BitVec 64) (d172 : BitVec 32) (u208 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u887 : BitVec 64) : SepProp :=
  ((fsp + 160#64) ↦₆₄ u160) ∗
  ((fsp + 172#64) ↦₃₂ d172) ∗
  ((fsp + 208#64) ↦₆₄ u208) ∗
  ((fsp + 232#64) ↦₆₄ u232) ∗
  ((fsp + 608#64) ↦₁₂₈ uq608) ∗ ((fsp + 624#64) ↦₁₂₈ uq624) ∗
  ((fsp + 640#64) ↦₁₂₈ uq640) ∗ ((fsp + 656#64) ↦₁₂₈ uq656) ∗
  ((fsp + 672#64) ↦₁₂₈ uq672) ∗ ((fsp + 688#64) ↦₁₂₈ uq688) ∗
  ((fsp + 704#64) ↦₁₂₈ uq704) ∗ ((fsp + 720#64) ↦₁₂₈ uq720) ∗
  ((fsp + 736#64) ↦₁₂₈ uq736) ∗ ((fsp + 752#64) ↦₁₂₈ uq752) ∗
  ((fsp + 768#64) ↦₁₂₈ uq768) ∗ ((fsp + 784#64) ↦₁₂₈ uq784) ∗
  ((fsp + 800#64) ↦₁₂₈ uq800) ∗ ((fsp + 816#64) ↦₁₂₈ uq816) ∗
  ((fsp + 832#64) ↦₆₄ u832) ∗
  ((fsp + 848#64) ↦₁₂₈ uq848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗
  ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880) ∗ ((fsp + 887#64) ↦₆₄ u887)

/-- Active stack slots in `fsp + 160..895` after `+7904..+8176` (ready for `epilogueStackSlots`). -/
@[expose] def v10_stagingSlotsPost (fsp : BitVec 64) (bs : List (BitVec 8)) (l2 : BitVec 64) : SepProp :=
  ((fsp + 160#64) ↦₆₄ l2) ∗
  ((fsp + 172#64) ↦₃₂ (loByte (v10_wordAt bs 128)).zeroExtend 32) ∗
  ((fsp + 208#64) ↦₆₄ v10_wordAt bs 0) ∗
  ((fsp + 232#64) ↦₆₄ l2) ∗
  ((fsp + 608#64) ↦₁₂₈ v10_quadAt bs 152) ∗ ((fsp + 624#64) ↦₁₂₈ v10_quadAt bs 168) ∗
  ((fsp + 640#64) ↦₁₂₈ v10_quadAt bs 184) ∗ ((fsp + 656#64) ↦₁₂₈ v10_quadAt bs 200) ∗
  ((fsp + 672#64) ↦₁₂₈ v10_quadAt bs 216) ∗ ((fsp + 688#64) ↦₁₂₈ v10_quadAt bs 232) ∗
  ((fsp + 704#64) ↦₁₂₈ v10_quadAt bs 248) ∗ ((fsp + 720#64) ↦₁₂₈ v10_quadAt bs 264) ∗
  ((fsp + 736#64) ↦₁₂₈ v10_quadAt bs 280) ∗ ((fsp + 752#64) ↦₁₂₈ v10_quadAt bs 296) ∗
  ((fsp + 768#64) ↦₁₂₈ v10_quadAt bs 312) ∗ ((fsp + 784#64) ↦₁₂₈ v10_quadAt bs 328) ∗
  ((fsp + 800#64) ↦₁₂₈ v10_quadAt bs 344) ∗ ((fsp + 816#64) ↦₁₂₈ v10_quadAt bs 360) ∗
  ((fsp + 832#64) ↦₆₄ v10_wordAt bs 376) ∗
  ((fsp + 848#64) ↦₁₂₈ v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144)) ∗
  ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v10_wordAt bs 144 >>> 8)) ∗
  ((fsp + 880#64) ↦₆₄ unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112))) ∗
  ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v10_wordAt bs 112 >>> 8))

theorem v10_out_96_realign (out w80 : BitVec 64) :
    ((out + 96#64) ↦₈ w80.extractLsb' 0 8) ∗
      ((out + 97#64) ↦₃₂ w80.extractLsb' 8 32) ∗
      ((out + 101#64) ↦₁₆ w80.extractLsb' 40 16) ∗
      ((out + 103#64) ↦₈ w80.extractLsb' 56 8) =
    (out + 96#64) ↦₆₄ w80 := by
  have h := (v10_pointsTo64_split_1_4_2_1 (out + 96#64) w80).symm
  have ha97 : (out + 96#64) + 1#64 = out + 97#64 := by bv_omega
  have ha101 : (out + 96#64) + 5#64 = out + 101#64 := by bv_omega
  have ha103 : (out + 96#64) + 7#64 = out + 103#64 := by bv_omega
  rw [ha97, ha101, ha103] at h
  exact h

theorem v10_out_120_realign (out w104 w112 : BitVec 64) :
    ((out + 120#64) ↦₈ loByte w104) ∗
      ((out + 121#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗
      ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 (unshiftWord w104 (loByte w112)) (w112 >>> 8))) =
    ((out + 120#64) ↦₆₄ w104) ∗ ((out + 128#64) ↦₆₄ w112) := by
  rw [v10_overlapWord7_unshift_lsr8 w104 w112]
  have h := (pair64_to_byte_word_tail7 (out + 120#64) w104 w112).symm
  have ha121 : (out + 120#64) + 1#64 = out + 121#64 := by bv_omega
  have ha129 : (out + 120#64) + 9#64 = out + 129#64 := by bv_omega
  have ha128 : (out + 120#64) + 8#64 = out + 128#64 := by bv_omega
  rw [ha121, ha129, ha128] at h
  exact h

theorem v10_out_144_realign (out w128 w136 w144 : BitVec 64) :
    ((out + 144#64) ↦₈ ((loByte w128).zeroExtend 32).setWidth 8) ∗
      ((out + 145#64) ↦₆₄ (v10_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v10_midQ128 w128 w136 w144).extractLsb' 64 64)) ∗
      ((out + 160#64) ↦₆₄
        overlapWord7 ((v10_midQ128 w128 w136 w144).extractLsb' 64 64) (w144 >>> 8)) =
    ((out + 144#64) ↦₆₄ w128) ∗ ((out + 152#64) ↦₆₄ w136) ∗ ((out + 160#64) ↦₆₄ w144) := by
  rw [v10_zext32_setWidth8 (loByte w128)]
  have hlo : (v10_midQ128 w128 w136 w144).extractLsb' 0 64 = unshiftWord w128 (loByte w136) := by
    unfold v10_midQ128; bv_kernel
  have hhi : (v10_midQ128 w128 w136 w144).extractLsb' 64 64 = unshiftWord w136 (loByte w144) := by
    unfold v10_midQ128; bv_kernel
  rw [hlo, hhi, v10_overlapWord7_unshift_lsr8 w136 w144]
  have hdst := v10_dst24_realign_final (out + 144#64) w128 w136 w144
  have hd145 : (out + 144#64) + 1#64 = out + 145#64 := by bv_omega
  have hd153 : (out + 144#64) + 9#64 = out + 153#64 := by bv_omega
  have hd160 : (out + 144#64) + 16#64 = out + 160#64 := by bv_omega
  have hd152 : (out + 144#64) + 8#64 = out + 152#64 := by bv_omega
  rw [hd145, hd153, hd160, hd152] at hdst
  exact hdst

theorem v10_out_16_to_400_eq_bs (out : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) :
    ((out + 16#64) ↦₆₄ v10_wordAt bs 0) ∗
      ((out + 24#64) ↦₆₄ v10_wordAt bs 8) ∗
      ((out + 32#64) ↦₆₄ v10_wordAt bs 16) ∗
      ((out + 40#64) ↦₆₄ v10_wordAt bs 24) ∗
      ((out + 48#64) ↦₆₄ v10_wordAt bs 32) ∗
      ((out + 56#64) ↦₆₄ v10_wordAt bs 40) ∗
      ((out + 64#64) ↦₆₄ v10_wordAt bs 48) ∗
      ((out + 72#64) ↦₆₄ v10_wordAt bs 56) ∗
      ((out + 80#64) ↦₆₄ v10_wordAt bs 64) ∗
      ((out + 88#64) ↦₆₄ v10_wordAt bs 72) ∗
      (((out + 96#64) ↦₈ (v10_wordAt bs 80).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v10_wordAt bs 80).extractLsb' 8 32) ∗
       ((out + 101#64) ↦₁₆ (v10_wordAt bs 80).extractLsb' 40 16) ∗
       ((out + 103#64) ↦₈ (v10_wordAt bs 80).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v10_wordAt bs 88) ∗
      ((out + 112#64) ↦₆₄ v10_wordAt bs 96) ∗
      (((out + 120#64) ↦₈ loByte (v10_wordAt bs 104)) ∗
       ((out + 121#64) ↦₆₄ unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 (unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112)))
           (v10_wordAt bs 112 >>> 8)))) ∗
      ((out + 136#64) ↦₆₄ v10_wordAt bs 120) ∗
      (((out + 144#64) ↦₈ ((loByte (v10_wordAt bs 128)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄
         (v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄
         overlapWord7
           ((v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144)).extractLsb' 64 64)
           (v10_wordAt bs 144 >>> 8))) ∗
      ((out + 168#64) ↦₁₂₈ v10_quadAt bs 152) ∗
      ((out + 184#64) ↦₁₂₈ v10_quadAt bs 168) ∗
      ((out + 200#64) ↦₁₂₈ v10_quadAt bs 184) ∗
      ((out + 216#64) ↦₁₂₈ v10_quadAt bs 200) ∗
      ((out + 232#64) ↦₁₂₈ v10_quadAt bs 216) ∗
      ((out + 248#64) ↦₁₂₈ v10_quadAt bs 232) ∗
      ((out + 264#64) ↦₁₂₈ v10_quadAt bs 248) ∗
      ((out + 280#64) ↦₁₂₈ v10_quadAt bs 264) ∗
      ((out + 296#64) ↦₁₂₈ v10_quadAt bs 280) ∗
      ((out + 312#64) ↦₁₂₈ v10_quadAt bs 296) ∗
      ((out + 328#64) ↦₁₂₈ v10_quadAt bs 312) ∗
      ((out + 344#64) ↦₁₂₈ v10_quadAt bs 328) ∗
      ((out + 360#64) ↦₁₂₈ v10_quadAt bs 344) ∗
      ((out + 376#64) ↦₁₂₈ v10_quadAt bs 360) ∗
      ((out + 392#64) ↦₆₄ v10_wordAt bs 376) =
    ((out + 8#64) + 8#64) ↦ₛ bs := by
  rw [v10_out_96_realign out (v10_wordAt bs 80),
      v10_out_120_realign out (v10_wordAt bs 104) (v10_wordAt bs 112),
      v10_out_144_realign out (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144),
      v10_bs384_eq_encCells bs hbs (out + 8#64)]
  unfold v10_encCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem v10_unchunkedCt2SentAt_408_pack (A : RustAlloc) {F : ShaCompress}
    (out l1 pa1 l2 pa2 ep : BitVec 64)
    (rootKey macKey : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length) :
    ((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗
      ((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗
      ((out + 456#64) ↦₆₄ ep) ∗
      vecU8Payload A l1 pa1 rootKey ∗
      vecU8Payload A l2 pa2 macKey ⊢
    unchunkedCt2SentAt A (F := F) (out + 408#64)
      { auth := { rootKey := rootKey, macKey := macKey }, epoch := ep } := by
  subst hl1 hl2
  dsimp only [unchunkedCt2SentAt, authenticatorAt]
  have h1 := vecU8_of_header_payload A (out + 408#64) (BitVec.ofNat 64 rootKey.length) pa1 rootKey
  have h2 := vecU8_of_header_payload A (out + 432#64) (BitVec.ofNat 64 macKey.length) pa2 macKey
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    (((out + 408#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
     ((out + 416#64) ↦₆₄ pa1) ∗
     ((out + 424#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 rootKey.length) pa1 rootKey) ∗
    (((out + 432#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
     ((out + 440#64) ↦₆₄ pa2) ∗
     ((out + 448#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 macKey.length) pa2 macKey) ∗
    ((out + 456#64) ↦₆₄ ep) by ac_rfl)) ?_
  rw [sepConj_assoc (vecU8 A (out + 408#64) rootKey)]
  exact sepConj_mono h1 (sepConj_mono_left h2)

theorem v10_epilogueOutFull_entails_ct2Sent (A : RustAlloc) {F : ShaCompress}
    (out tag l1 pa1 l2 pa2 ep : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp)
    (hreloc :
      ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
        (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
        polyEncoderAt A (out + 8#64) enc)
    (rootKey macKey : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length)
    (w464 w472 w480 w488 w496 w504 w512 w520 w528 : BitVec 64)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out
      12#64 tag (v10_wordAt bs 0) (v10_wordAt bs 8)
      (v10_wordAt bs 16) (v10_wordAt bs 24) (v10_wordAt bs 32) (v10_wordAt bs 40)
      (v10_wordAt bs 48) (v10_wordAt bs 56) (v10_wordAt bs 64) (v10_wordAt bs 72)
      ((v10_wordAt bs 80).extractLsb' 0 8) ((v10_wordAt bs 80).extractLsb' 8 32)
      ((v10_wordAt bs 80).extractLsb' 40 16) ((v10_wordAt bs 80).extractLsb' 56 8)
      (v10_wordAt bs 88) (v10_wordAt bs 96) (loByte (v10_wordAt bs 104))
      (unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112)))
      (overlapWord7 (unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112)))
        (v10_wordAt bs 112 >>> 8))
      (v10_wordAt bs 120)
      (((loByte (v10_wordAt bs 128)).zeroExtend 32).setWidth 8)
      (v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144))
      (overlapWord7
        ((v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144)).extractLsb' 64 64)
        (v10_wordAt bs 144 >>> 8))
      (v10_quadAt bs 152) (v10_quadAt bs 168) (v10_quadAt bs 184) (v10_quadAt bs 200)
      (v10_quadAt bs 216) (v10_quadAt bs 232) (v10_quadAt bs 248) (v10_quadAt bs 264)
      (v10_quadAt bs 280) (v10_quadAt bs 296) (v10_quadAt bs 312) (v10_quadAt bs 328)
      (v10_quadAt bs 344) (v10_quadAt bs 360)
      (v10_wordAt bs 376) (hi32 ++ enc.idx)
      l1 pa1 l1 l2 pa2 l2 ep
      w464 w472 w480 w488 w496 w504 w512 w520 w528
      b536 q537 w552 bs240 q888 q904 w920 ∗
      P_heap ∗
      vecU8Payload A l1 pa1 rootKey ∗
      vecU8Payload A l2 pa2 macKey ⊢
    resultChunkedStatesAt A (F := F) out
      (.ok (.ct2Sampled
        { uc := { auth := { rootKey := rootKey, macKey := macKey }, epoch := ep },
          sending_ct2 := enc })) := by
  dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedCt2SampledAt]
  have ha408 : (out + 8#64) + 400#64 = out + 408#64 := by bv_omega
  have ha400 : (out + 8#64) + 392#64 = out + 400#64 := by bv_omega
  rw [ha408, sepConj_assoc (polyEncoderAt A (out + 8#64) enc)]
  rw [ha400] at hreloc
  unfold epilogueOutFull
  have hbs_eq := v10_out_16_to_400_eq_bs out bs hbs
  have huc := v10_unchunkedCt2SentAt_408_pack A (F := F) out l1 pa1 l2 pa2 ep rootKey macKey hl1 hl2
  have htail := epilogueOut_tail_464_entails_464 out
    w464 w472 w480 w488 w496 w504 w512 w520 w528
    b536 q537 w552 bs240 hbs240 q888 q904 w920
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 12#64) ∗
    (((out + 8#64) ↦₆₄ tag) ∗
     (((out + 16#64) ↦₆₄ v10_wordAt bs 0) ∗
      ((out + 24#64) ↦₆₄ v10_wordAt bs 8) ∗
      ((out + 32#64) ↦₆₄ v10_wordAt bs 16) ∗
      ((out + 40#64) ↦₆₄ v10_wordAt bs 24) ∗
      ((out + 48#64) ↦₆₄ v10_wordAt bs 32) ∗
      ((out + 56#64) ↦₆₄ v10_wordAt bs 40) ∗
      ((out + 64#64) ↦₆₄ v10_wordAt bs 48) ∗
      ((out + 72#64) ↦₆₄ v10_wordAt bs 56) ∗
      ((out + 80#64) ↦₆₄ v10_wordAt bs 64) ∗
      ((out + 88#64) ↦₆₄ v10_wordAt bs 72) ∗
      (((out + 96#64) ↦₈ (v10_wordAt bs 80).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v10_wordAt bs 80).extractLsb' 8 32) ∗
       ((out + 101#64) ↦₁₆ (v10_wordAt bs 80).extractLsb' 40 16) ∗
       ((out + 103#64) ↦₈ (v10_wordAt bs 80).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v10_wordAt bs 88) ∗
      ((out + 112#64) ↦₆₄ v10_wordAt bs 96) ∗
      (((out + 120#64) ↦₈ loByte (v10_wordAt bs 104)) ∗
       ((out + 121#64) ↦₆₄ unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 (unshiftWord (v10_wordAt bs 104) (loByte (v10_wordAt bs 112)))
           (v10_wordAt bs 112 >>> 8)))) ∗
      ((out + 136#64) ↦₆₄ v10_wordAt bs 120) ∗
      (((out + 144#64) ↦₈ ((loByte (v10_wordAt bs 128)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄
         (v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄
         overlapWord7
           ((v10_midQ128 (v10_wordAt bs 128) (v10_wordAt bs 136) (v10_wordAt bs 144)).extractLsb' 64 64)
           (v10_wordAt bs 144 >>> 8))) ∗
      ((out + 168#64) ↦₁₂₈ v10_quadAt bs 152) ∗
      ((out + 184#64) ↦₁₂₈ v10_quadAt bs 168) ∗
      ((out + 200#64) ↦₁₂₈ v10_quadAt bs 184) ∗
      ((out + 216#64) ↦₁₂₈ v10_quadAt bs 200) ∗
      ((out + 232#64) ↦₁₂₈ v10_quadAt bs 216) ∗
      ((out + 248#64) ↦₁₂₈ v10_quadAt bs 232) ∗
      ((out + 264#64) ↦₁₂₈ v10_quadAt bs 248) ∗
      ((out + 280#64) ↦₁₂₈ v10_quadAt bs 264) ∗
      ((out + 296#64) ↦₁₂₈ v10_quadAt bs 280) ∗
      ((out + 312#64) ↦₁₂₈ v10_quadAt bs 296) ∗
      ((out + 328#64) ↦₁₂₈ v10_quadAt bs 312) ∗
      ((out + 344#64) ↦₁₂₈ v10_quadAt bs 328) ∗
      ((out + 360#64) ↦₁₂₈ v10_quadAt bs 344) ∗
      ((out + 376#64) ↦₁₂₈ v10_quadAt bs 360) ∗
      ((out + 392#64) ↦₆₄ v10_wordAt bs 376)) ∗
     ((out + 400#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
     P_heap) ∗
    (((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗
     ((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗
     ((out + 456#64) ↦₆₄ ep) ∗
     vecU8Payload A l1 pa1 rootKey ∗
     vecU8Payload A l2 pa2 macKey) ∗
    (((out + 464#64) ↦₆₄ w464) ∗ ((out + 472#64) ↦₆₄ w472) ∗ ((out + 480#64) ↦₆₄ w480) ∗
     (((out + 488#64) ↦₆₄ w488) ∗ ((out + 496#64) ↦₆₄ w496) ∗ ((out + 504#64) ↦₆₄ w504) ∗
      (((out + 512#64) ↦₆₄ w512) ∗ ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
       (((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
        ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗ ((out + 560#64) ↦ₛ bs240) ∗
        ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920))))) by ac_rfl)) ?_
  rw [hbs_eq]
  exact sepConj_mono_right (sepConj_mono hreloc (sepConj_mono huc htail))

theorem v10_fsp_1888_entails_epilogue (fsp tag w2280 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) :
    ((fsp + 1888#64) ↦₆₄ tag) ∗
      v10_encCellsAt (fsp + 1888#64) bs ∗
      ((fsp + 2280#64) ↦₆₄ w2280) ∗
      memRegion (fsp + 2288#64) 16 ⊢
    ((fsp + 1888#64) ↦₁₂₈ (v10_wordAt bs 0 ++ tag)) ∗
      ((fsp + 1904#64) ↦₁₂₈ (v10_wordAt bs 16 ++ v10_wordAt bs 8)) ∗
      ((fsp + 1920#64) ↦₆₄ v10_wordAt bs 24) ∗
      memRegion (fsp + 1928#64) 376 := by
  rw [← v10_bs384_eq_encCells bs hbs (fsp + 1888#64)]
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  rw [ha1896]
  have hbs_split : ((fsp + 1896#64) ↦ₛ bs) =
      ((fsp + 1896#64) ↦₆₄ v10_wordAt bs 0) ∗
      ((fsp + 1904#64) ↦₆₄ v10_wordAt bs 8) ∗
      ((fsp + 1912#64) ↦₆₄ v10_wordAt bs 16) ∗
      ((fsp + 1920#64) ↦₆₄ v10_wordAt bs 24) ∗
      ((fsp + 1928#64) ↦ₛ bs.drop 32) := by
    have h :=
      v10_bs_drop_step8 hbs (fsp + 1888#64) 8#64 16#64 0 <|
      v10_bs_drop_step8 hbs (fsp + 1888#64) 16#64 24#64 8 <|
      v10_bs_drop_step8 hbs (fsp + 1888#64) 24#64 32#64 16 <|
      v10_bs_drop_step8 hbs (fsp + 1888#64) 32#64 40#64 24 rfl
    change (((fsp + 1888#64) + 8#64) ↦ₛ bs) = _ at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd, sepConj_assoc] at h
    exact h
  rw [hbs_split]
  have hq1888 : ((fsp + 1888#64) ↦₆₄ tag) ∗ ((fsp + 1896#64) ↦₆₄ v10_wordAt bs 0) =
      ((fsp + 1888#64) ↦₁₂₈ (v10_wordAt bs 0 ++ tag)) := by
    rw [← ha1896, pointsTo64_pair_eq_pointsTo128]
  have hq1904 : ((fsp + 1904#64) ↦₆₄ v10_wordAt bs 8) ∗ ((fsp + 1912#64) ↦₆₄ v10_wordAt bs 16) =
      ((fsp + 1904#64) ↦₁₂₈ (v10_wordAt bs 16 ++ v10_wordAt bs 8)) := by
    have ha : (fsp + 1904#64) + 8#64 = fsp + 1912#64 := by bv_omega
    rw [← ha, pointsTo64_pair_eq_pointsTo128]
  have hlen352 : (bs.drop 32).length = 352 := by rw [List.length_drop, hbs]
  have hm352 : ((fsp + 1928#64) ↦ₛ bs.drop 32) ⊢ memRegion (fsp + 1928#64) 352 :=
    hlen352 ▸ ProofLib.pointsToBytes_entails_memRegion (fsp + 1928#64) (bs.drop 32)
  have hm376 : ((fsp + 1928#64) ↦ₛ bs.drop 32) ∗
      ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16 ⊢
      memRegion (fsp + 1928#64) 376 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1928#64) (n := 352) (k := 24)
          (b' := fsp + 2280#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 2280#64) (n := 8) (k := 16)
          (b' := fsp + 2288#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono hm352
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 2280#64) w2280))
  refine Entails.trans (Entails.of_eq (show _ =
    (((fsp + 1888#64) ↦₆₄ tag) ∗ ((fsp + 1896#64) ↦₆₄ v10_wordAt bs 0)) ∗
    (((fsp + 1904#64) ↦₆₄ v10_wordAt bs 8) ∗ ((fsp + 1912#64) ↦₆₄ v10_wordAt bs 16)) ∗
    ((fsp + 1920#64) ↦₆₄ v10_wordAt bs 24) ∗
    (((fsp + 1928#64) ↦ₛ bs.drop 32) ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16) by ac_rfl)) ?_
  rw [hq1888, hq1904]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm376))

theorem v10_fsp_128_152_entails_32 (fsp ep : BitVec 64) :
    memRegion (fsp + 128#64) 24 ∗ ((fsp + 152#64) ↦₆₄ ep) ⊢
      memRegion (fsp + 128#64) 32 := by
  rw [ProofLib.memRegion_split' (b := fsp + 128#64) (n := 24) (k := 8)
        (b' := fsp + 152#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (ProofLib.pointsTo64_entails_memRegion (fsp + 152#64) ep)

theorem v10_fsp_176_184_entails_16 (fsp pa2 : BitVec 64) :
    memRegion (fsp + 176#64) 8 ∗ ((fsp + 184#64) ↦₆₄ pa2) ⊢
      memRegion (fsp + 176#64) 16 := by
  rw [ProofLib.memRegion_split' (b := fsp + 176#64) (n := 8) (k := 8)
        (b' := fsp + 184#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (ProofLib.pointsTo64_entails_memRegion (fsp + 184#64) pa2)

theorem v10_memRegion_loBytes7_gap_at (a o1 o2 : BitVec 64) (k : Nat)
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
  exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _)

theorem v10_memRegion_entails_bs :
    ∀ (n : Nat) (a : BitVec 64), n ≤ 2 ^ 64 →
      ProofLib.memRegion a n ⊢
        ∃∗ bs : { l : List (BitVec 8) // l.length = n }, (a ↦ₛ bs.val)
  | 0, a, _ => by
    rw [ProofLib.memRegion_zero]
    refine Entails.sepExists_right ⟨[], rfl⟩ ?_
    rw [ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | n + 1, a, hn => by
    have hsplit : n + 1 = 1 + n := by omega
    rw [hsplit, ProofLib.memRegion_split a 1 n (by omega), ProofLib.memRegion_one a,
        sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro b0
    refine Entails.trans (sepConj_mono_right (v10_memRegion_entails_bs n (a + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ⟨bs, hlen⟩
    refine Entails.sepExists_right ⟨b0 :: bs, by simp [hlen]; omega⟩ ?_
    rw [ProofLib.pointsToBytes_cons]
    exact Entails.refl _

theorem v10_memRegion_328_entails_bs (a : BitVec 64) :
    ProofLib.memRegion a 328 ⊢
      ∃∗ bs : { l : List (BitVec 8) // l.length = 328 }, (a ↦ₛ bs.val) :=
  v10_memRegion_entails_bs 328 a (by decide)

theorem v10_memRegion_152_split_7904 (fsp : BitVec 64) :
    memRegion fsp 152 ⊢
      memRegion fsp 92 ∗
      (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) ∗
      memRegion (fsp + 96#64) 8 ∗
      (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗
      (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) ∗
      (∃∗ w120 : BitVec 64, ((fsp + 120#64) ↦₆₄ w120)) ∗
      memRegion (fsp + 128#64) 24 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem32_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v10_memRegion_160_24_split_7904 (fsp : BitVec 64) :
    memRegion (fsp + 160#64) 24 ⊢
      (∃∗ u160 : BitVec 64, ((fsp + 160#64) ↦₆₄ u160)) ∗
      memRegion (fsp + 168#64) 4 ∗
      (∃∗ d172 : BitVec 32, ((fsp + 172#64) ↦₃₂ d172)) ∗
      memRegion (fsp + 176#64) 8 := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem32_entails _) <|
    Entails.refl _

theorem v10_memRegion_208_16_split_7904 (fsp : BitVec 64) :
    memRegion (fsp + 208#64) 16 ⊢
      (∃∗ u208 : BitVec 64, ((fsp + 208#64) ↦₆₄ u208)) ∗
      memRegion (fsp + 216#64) 8 := by
  exact split_top <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v10_memRegion_240_1648_split_7904 (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 1648 ⊢
      (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
      memRegion (fsp + 568#64) 8 ∗
      (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗
      ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗
       memRegion (fsp + 599#64) 9) ∗
      (∃∗ uq608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ uq608)) ∗
      (∃∗ uq624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ uq624)) ∗
      (∃∗ uq640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ uq640)) ∗
      (∃∗ uq656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ uq656)) ∗
      (∃∗ uq672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ uq672)) ∗
      (∃∗ uq688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ uq688)) ∗
      (∃∗ uq704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ uq704)) ∗
      (∃∗ uq720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ uq720)) ∗
      (∃∗ uq736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ uq736)) ∗
      (∃∗ uq752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ uq752)) ∗
      (∃∗ uq768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ uq768)) ∗
      (∃∗ uq784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ uq784)) ∗
      (∃∗ uq800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ uq800)) ∗
      (∃∗ uq816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ uq816)) ∗
      (∃∗ u832 : BitVec 64, ((fsp + 832#64) ↦₆₄ u832)) ∗
      memRegion (fsp + 840#64) 8 ∗
      (∃∗ uq848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ uq848)) ∗
      ((∃∗ u864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864)) ∗
       memRegion (fsp + 871#64) 9) ∗
      ((∃∗ u880 : BitVec 64, ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880)) ∗
       (∃∗ u887 : BitVec 64, ((fsp + 887#64) ↦₆₄ u887))) ∗
      memRegion (fsp + 895#64) 993 := by
  exact split_top <|
    split_step (v10_memRegion_328_entails_bs _) <|
    split_step (Entails.refl _) <|
    split_step (mem128_entails _) <|
    split_step (v10_memRegion_loBytes7_gap_at fsp 592#64 599#64 8) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem128_entails _) <|
    split_step (v10_memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <|
    split_step (memRegion_15_entails_loBytes7_and_64_at fsp 880#64 887#64) <|
    Entails.refl _

theorem v10_fsp_split_7904_all (fsp : BitVec 64) :
    memRegion fsp 152 ∗
      memRegion (fsp + 160#64) 24 ∗
      memRegion (fsp + 192#64) 8 ∗
      memRegion (fsp + 208#64) 16 ∗
      memRegion (fsp + 240#64) 1648 ⊢
    memRegion fsp 92 ∗
      (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) ∗
      memRegion (fsp + 96#64) 8 ∗
      (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗
      (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) ∗
      (∃∗ w120 : BitVec 64, ((fsp + 120#64) ↦₆₄ w120)) ∗
      memRegion (fsp + 128#64) 24 ∗
      (∃∗ u160 : BitVec 64, ((fsp + 160#64) ↦₆₄ u160)) ∗
      memRegion (fsp + 168#64) 4 ∗
      (∃∗ d172 : BitVec 32, ((fsp + 172#64) ↦₃₂ d172)) ∗
      memRegion (fsp + 176#64) 8 ∗
      (∃∗ w192 : BitVec 64, ((fsp + 192#64) ↦₆₄ w192)) ∗
      (∃∗ u208 : BitVec 64, ((fsp + 208#64) ↦₆₄ u208)) ∗
      memRegion (fsp + 216#64) 8 ∗
      (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
      memRegion (fsp + 568#64) 8 ∗
      (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗
      ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗
       memRegion (fsp + 599#64) 9) ∗
      (∃∗ uq608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ uq608)) ∗
      (∃∗ uq624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ uq624)) ∗
      (∃∗ uq640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ uq640)) ∗
      (∃∗ uq656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ uq656)) ∗
      (∃∗ uq672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ uq672)) ∗
      (∃∗ uq688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ uq688)) ∗
      (∃∗ uq704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ uq704)) ∗
      (∃∗ uq720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ uq720)) ∗
      (∃∗ uq736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ uq736)) ∗
      (∃∗ uq752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ uq752)) ∗
      (∃∗ uq768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ uq768)) ∗
      (∃∗ uq784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ uq784)) ∗
      (∃∗ uq800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ uq800)) ∗
      (∃∗ uq816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ uq816)) ∗
      (∃∗ u832 : BitVec 64, ((fsp + 832#64) ↦₆₄ u832)) ∗
      memRegion (fsp + 840#64) 8 ∗
      (∃∗ uq848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ uq848)) ∗
      ((∃∗ u864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864)) ∗
       memRegion (fsp + 871#64) 9) ∗
      ((∃∗ u880 : BitVec 64, ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880)) ∗
       (∃∗ u887 : BitVec 64, ((fsp + 887#64) ↦₆₄ u887))) ∗
      memRegion (fsp + 895#64) 993 := by
  refine Entails.trans
    (sepConj_mono (v10_memRegion_152_split_7904 fsp)
      (sepConj_mono (v10_memRegion_160_24_split_7904 fsp)
        (sepConj_mono (mem64_entails (fsp + 192#64))
          (sepConj_mono (v10_memRegion_208_16_split_7904 fsp)
            (v10_memRegion_240_1648_split_7904 fsp))))) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2d -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 1 (`KeysSampled`, `+1104`) — Part E

**Checked by Lean.**

`<PolyEncoder>::from_pb` call (`+4096`), result dispatch (`+4100`), `Ok` staging (`+6568 -> +8180`),
and shared epilogue composition for `InnerState.keysSampled`.
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



attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x25_add_189 (fsp : BitVec 64) :
    (fsp + 1792#64) + 189#64 = fsp + 1981#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x25_add_189_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (189#64).signExtend 64 = fsp + 1981#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x25_add_233 (fsp : BitVec 64) :
    (fsp + 1792#64) + 233#64 = fsp + 2025#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x25_add_233_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (233#64).signExtend 64 = fsp + 2025#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x11_add_185 (fsp : BitVec 64) :
    (fsp + 1792#64) + 185#64 = fsp + 1977#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x11_add_185_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (185#64).signExtend 64 = fsp + 1977#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x11_add_209 (fsp : BitVec 64) :
    (fsp + 1792#64) + 209#64 = fsp + 2001#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x11_add_209_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (209#64).signExtend 64 = fsp + 2001#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x23_add_39 (fsp : BitVec 64) :
    (fsp + 848#64) + 39#64 = fsp + 887#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x23_add_39_sext (fsp : BitVec 64) :
    (fsp + 848#64) + (39#64).signExtend 64 = fsp + 887#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x23_add_15 (fsp : BitVec 64) :
    (fsp + 848#64) + 15#64 = fsp + 863#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x23_add_15_sext (fsp : BitVec 64) :
    (fsp + 848#64) + (15#64).signExtend 64 = fsp + 863#64 := by bv_kernel

theorem v1_fsp_880_realign_64_rest (fsp w880 w888 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗ Rest =
      ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
      ((fsp + 887#64) ↦₆₄ overlapWord7 w880 w888) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 880#64) w880 w888
  have ha7 : (fsp + 880#64) + 7#64 = fsp + 887#64 := by bv_omega
  have ha8 : (fsp + 880#64) + 8#64 = fsp + 888#64 := by bv_omega
  rw [ha7, ha8] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v1_onPanic_shift {s0 sm : State} (htrace : TraceCalleeSaved sm s0)
    (sf : State) {F : SepProp} :
    encoderFromPbOnPanic sm sf ∗ F ⊢
      statesFromPbOnPanic s0 sf := by
  dsimp only [encoderFromPbOnPanic, statesFromPbOnPanic]
  rw [sepConj_assoc]
  apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢
  rw [htrace.1] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

theorem v1_memRegion_72_104_split (fsp : BitVec 64) :
    memRegion (fsp + 72#64) 104 ⊢
      memRegion (fsp + 72#64) 20 ∗
      (∃∗ d92 : BitVec 32, (fsp + 92#64) ↦₃₂ d92) ∗
      memRegion (fsp + 96#64) 8 ∗
      (∃∗ w104 : BitVec 64, (fsp + 104#64) ↦₆₄ w104) ∗
      (∃∗ w112 : BitVec 64, (fsp + 112#64) ↦₆₄ w112) ∗
      (∃∗ w120 : BitVec 64, (fsp + 120#64) ↦₆₄ w120) ∗
      memRegion (fsp + 128#64) 32 ∗
      (∃∗ w160 : BitVec 64, (fsp + 160#64) ↦₆₄ w160) ∗
      memRegion (fsp + 168#64) 4 ∗
      (∃∗ d172 : BitVec 32, (fsp + 172#64) ↦₃₂ d172) := by
  exact split_top <|
    split_step (Entails.refl _) <|
    split_step (mem32_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    mem32_entails _

theorem v1_memRegion_240_1648_split (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 1648 ⊢
      (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, (fsp + 240#64) ↦ₛ bs240.val) ∗
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
      ((∃∗ w888 : BitVec 64, (fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗ memRegion (fsp + 895#64) 993) := by
  exact split_top <|
    split_step (memRegion_328_entails_bs _) <|
    split_step (Entails.refl _) <|
    split_step (mem128_entails _) <|
    split_step (memRegion_loBytes7_gap_at fsp 592#64 599#64 8) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem128_entails _) <|
    split_step (memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <|
    split_step (mem64_entails _) <|
    memRegion_loBytes7_gap_at fsp 888#64 895#64 992

theorem v1_epilogueStackGaps_pack (fsp u104 u16 pa2 pa1 u40 : BitVec 64) :
    memRegion fsp 64 ∗
      ((fsp + 64#64) ↦₆₄ u104) ∗
      memRegion (fsp + 72#64) 20 ∗
      memRegion (fsp + 96#64) 8 ∗
      memRegion (fsp + 128#64) 32 ∗
      memRegion (fsp + 168#64) 4 ∗
      ((fsp + 176#64) ↦₆₄ u16) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 200#64) ↦₆₄ pa1) ∗
      ((fsp + 216#64) ↦₆₄ u40) ∗
      memRegion (fsp + 568#64) 8 ∗
      memRegion (fsp + 599#64) 9 ∗
      memRegion (fsp + 840#64) 8 ∗
      memRegion (fsp + 871#64) 9 ∗
      memRegion (fsp + 895#64) 993 ∗
      memRegion (fsp + 1928#64) 376 ⊢
      epilogueStackGaps fsp := by
  unfold epilogueStackGaps
  have h92 : memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ u104) ∗ memRegion (fsp + 72#64) 20 ⊢
      memRegion fsp 92 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have h16 : ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ⊢ memRegion (fsp + 176#64) 16 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  have h200 : ((fsp + 200#64) ↦₆₄ pa1) ⊢ memRegion (fsp + 200#64) 8 :=
    Drop.pointsTo64_entails_memRegion _ _
  have h216 : ((fsp + 216#64) ↦₆₄ u40) ⊢ memRegion (fsp + 216#64) 8 :=
    Drop.pointsTo64_entails_memRegion _ _
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ u104) ∗ memRegion (fsp + 72#64) 20) ∗
    memRegion (fsp + 96#64) 8 ∗
    memRegion (fsp + 128#64) 32 ∗
    memRegion (fsp + 168#64) 4 ∗
    (((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2)) ∗
    ((fsp + 200#64) ↦₆₄ pa1) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗
    memRegion (fsp + 568#64) 8 ∗
    memRegion (fsp + 599#64) 9 ∗
    memRegion (fsp + 840#64) 8 ∗
    memRegion (fsp + 871#64) 9 ∗
    memRegion (fsp + 895#64) 993 ∗
    memRegion (fsp + 1928#64) 376 by ac_rfl)) ?_
  exact sepConj_mono h92 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono h16 (sepConj_mono h200 (sepConj_mono_left h216))))))

end CryptoVerification.SpqrV1.States.FromPb

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9c -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10c
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 5 (`NoHeaderReceived`, `+1344`) — Part C

Cloned-`Authenticator` error cleanup (`+6520 -> +6500`), `<PolyDecoder>::from_pb` staging
(`+6064..+6132`), and `Ok` output staging (`+6132 -> +8180`).
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



/-! ## Error Deallocation of Cloned `Authenticator` (`+6520..+6564 -> +10484 -> +6500`) -/

/-- Split `memRegion base 40` into `v5a_optProtoPolyDecoderWordsAt base`. -/
theorem v5c_memRegion_40_to_polyDecoderWordsAt (base : BitVec 64) :
    memRegion base 40 ⊢
      ∃∗ z0 : BitVec 64, ∃∗ z8 : BitVec 64, ∃∗ z16 : BitVec 64,
      ∃∗ zd24 : BitVec 32, ∃∗ zd28 : BitVec 32, ∃∗ z32 : BitVec 64,
        v5a_optProtoPolyDecoderWordsAt base z0 z8 z16 zd24 zd28 z32 := by
  have hsplit : memRegion base 40 ⊢
      (∃∗ z0 : BitVec 64, base ↦₆₄ z0) ∗
      (∃∗ z8 : BitVec 64, (base + 8#64) ↦₆₄ z8) ∗
      (∃∗ z16 : BitVec 64, (base + 16#64) ↦₆₄ z16) ∗
      (∃∗ zd24 : BitVec 32, (base + 24#64) ↦₃₂ zd24) ∗
      (∃∗ zd28 : BitVec 32, (base + 28#64) ↦₃₂ zd28) ∗
      (∃∗ z32 : BitVec 64, (base + 32#64) ↦₆₄ z32) := by
    exact split_top <|
      split_step0 (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem32_entails _) <|
      split_step (mem32_entails _) <|
      mem64_entails _
  refine Entails.trans hsplit ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro z32
  apply Entails.sepExists_elim; intro zd28
  apply Entails.sepExists_elim; intro zd24
  apply Entails.sepExists_elim; intro z16
  apply Entails.sepExists_elim; intro z8
  apply Entails.sepExists_elim; intro z0
  refine Entails.sepExists_right z0 (Entails.sepExists_right z8
    (Entails.sepExists_right z16 (Entails.sepExists_right zd24
      (Entails.sepExists_right zd28 (Entails.sepExists_right z32 ?_)))))
  unfold v5a_optProtoPolyDecoderWordsAt
  exact Entails.of_eq (by ac_rfl)

/-- The 384-byte `PolyDecoder` `pts` headers region at `a..a + 384` decomposed into the
    exact 64-bit and 128-bit cells accessed at `+6132..+6416` (`a = fsp + 1888`) and
    written by `epilogueOutFull` (`a = out + 64`). -/
@[expose] def v5c_decCellsAt (a : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (a ↦₆₄ v9_wordAt bs 0) ∗
  ((a + 8#64) ↦₆₄ v9_wordAt bs 8) ∗
  ((a + 16#64) ↦₆₄ v9_wordAt bs 16) ∗
  ((a + 24#64) ↦₆₄ v9_wordAt bs 24) ∗
  ((a + 32#64) ↦₆₄ v9_wordAt bs 32) ∗
  ((a + 40#64) ↦₆₄ v9_wordAt bs 40) ∗
  ((a + 48#64) ↦₆₄ v9_wordAt bs 48) ∗
  ((a + 56#64) ↦₆₄ v9_wordAt bs 56) ∗
  ((a + 64#64) ↦₆₄ v9_wordAt bs 64) ∗
  ((a + 72#64) ↦₆₄ v9_wordAt bs 72) ∗
  ((a + 80#64) ↦₆₄ v9_wordAt bs 80) ∗
  ((a + 88#64) ↦₆₄ v9_wordAt bs 88) ∗
  ((a + 96#64) ↦₆₄ v9_wordAt bs 96) ∗
  ((a + 104#64) ↦₁₂₈ v9_quadAt bs 104) ∗
  ((a + 120#64) ↦₁₂₈ v9_quadAt bs 120) ∗
  ((a + 136#64) ↦₁₂₈ v9_quadAt bs 136) ∗
  ((a + 152#64) ↦₁₂₈ v9_quadAt bs 152) ∗
  ((a + 168#64) ↦₁₂₈ v9_quadAt bs 168) ∗
  ((a + 184#64) ↦₁₂₈ v9_quadAt bs 184) ∗
  ((a + 200#64) ↦₁₂₈ v9_quadAt bs 200) ∗
  ((a + 216#64) ↦₁₂₈ v9_quadAt bs 216) ∗
  ((a + 232#64) ↦₁₂₈ v9_quadAt bs 232) ∗
  ((a + 248#64) ↦₁₂₈ v9_quadAt bs 248) ∗
  ((a + 264#64) ↦₁₂₈ v9_quadAt bs 264) ∗
  ((a + 280#64) ↦₁₂₈ v9_quadAt bs 280) ∗
  ((a + 296#64) ↦₁₂₈ v9_quadAt bs 296) ∗
  ((a + 312#64) ↦₁₂₈ v9_quadAt bs 312) ∗
  ((a + 328#64) ↦₆₄ v9_wordAt bs 328) ∗
  ((a + 336#64) ↦₆₄ v9_wordAt bs 336) ∗
  ((a + 344#64) ↦₆₄ v9_wordAt bs 344) ∗
  ((a + 352#64) ↦₆₄ v9_wordAt bs 352) ∗
  ((a + 360#64) ↦₆₄ v9_wordAt bs 360) ∗
  ((a + 368#64) ↦₆₄ v9_wordAt bs 368) ∗
  ((a + 376#64) ↦₆₄ v9_wordAt bs 376)

theorem v5c_bs384_eq_decCells (bs : List (BitVec 8)) (hbs : bs.length = 384) (a : BitVec 64) :
    (a ↦ₛ bs) = v5c_decCellsAt a bs := by
  unfold v5c_decCellsAt
  change (a ↦ₛ bs.drop 0) = _
  exact
    v9_bs_drop_step8_zero hbs a <| v9_bs_drop_step8 hbs a 8#64 16#64 8 <|
    v9_bs_drop_step8 hbs a 16#64 24#64 16 <| v9_bs_drop_step8 hbs a 24#64 32#64 24 <|
    v9_bs_drop_step8 hbs a 32#64 40#64 32 <| v9_bs_drop_step8 hbs a 40#64 48#64 40 <|
    v9_bs_drop_step8 hbs a 48#64 56#64 48 <| v9_bs_drop_step8 hbs a 56#64 64#64 56 <|
    v9_bs_drop_step8 hbs a 64#64 72#64 64 <| v9_bs_drop_step8 hbs a 72#64 80#64 72 <|
    v9_bs_drop_step8 hbs a 80#64 88#64 80 <| v9_bs_drop_step8 hbs a 88#64 96#64 88 <|
    v9_bs_drop_step8 hbs a 96#64 104#64 96 <|
    v9_bs_drop_step16 hbs a 104#64 120#64 104 <| v9_bs_drop_step16 hbs a 120#64 136#64 120 <|
    v9_bs_drop_step16 hbs a 136#64 152#64 136 <| v9_bs_drop_step16 hbs a 152#64 168#64 152 <|
    v9_bs_drop_step16 hbs a 168#64 184#64 168 <| v9_bs_drop_step16 hbs a 184#64 200#64 184 <|
    v9_bs_drop_step16 hbs a 200#64 216#64 200 <| v9_bs_drop_step16 hbs a 216#64 232#64 216 <|
    v9_bs_drop_step16 hbs a 232#64 248#64 232 <| v9_bs_drop_step16 hbs a 248#64 264#64 248 <|
    v9_bs_drop_step16 hbs a 264#64 280#64 264 <| v9_bs_drop_step16 hbs a 280#64 296#64 280 <|
    v9_bs_drop_step16 hbs a 296#64 312#64 296 <| v9_bs_drop_step16 hbs a 312#64 328#64 312 <|
    v9_bs_drop_step8 hbs a 328#64 336#64 328 <| v9_bs_drop_step8 hbs a 336#64 344#64 336 <|
    v9_bs_drop_step8 hbs a 344#64 352#64 344 <| v9_bs_drop_step8 hbs a 352#64 360#64 352 <|
    v9_bs_drop_step8 hbs a 360#64 368#64 360 <| v9_bs_drop_step8 hbs a 368#64 376#64 368 <|
    v9_bs_drop_end8 hbs a 376#64

@[local simp, local arm64_norm, local wp_norm]
theorem v5c_fsp_1888_add_33 (fsp : BitVec 64) :
    (fsp + 1888#64) + (33#64).signExtend 64 = fsp + 1921#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v5c_fsp_1888_add_37 (fsp : BitVec 64) :
    (fsp + 1888#64) + (37#64).signExtend 64 = fsp + 1925#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v5c_fsp_1888_add_57 (fsp : BitVec 64) :
    (fsp + 1888#64) + (57#64).signExtend 64 = fsp + 1945#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v5c_fsp_1888_add_81 (fsp : BitVec 64) :
    (fsp + 1888#64) + (81#64).signExtend 64 = fsp + 1969#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v5c_fsp_848_add_15 (fsp : BitVec 64) :
    (fsp + 848#64) + (15#64).signExtend 64 = fsp + 863#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v5c_fsp_848_add_39 (fsp : BitVec 64) :
    (fsp + 848#64) + (39#64).signExtend 64 = fsp + 887#64 := by bv_kernel

theorem v5c_fsp_1920_split_rest (fsp w32 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1920#64) ↦₆₄ w32) ∗ Rest =
      ((fsp + 1920#64) ↦₈ w32.extractLsb' 0 8) ∗
      ((fsp + 1921#64) ↦₃₂ w32.extractLsb' 8 32) ∗
      ((fsp + 1925#64) ↦₁₆ w32.extractLsb' 40 16) ∗
      ((fsp + 1927#64) ↦₈ w32.extractLsb' 56 8) ∗ Rest := by
  have h := v9_pointsTo64_split_1_4_2_1 (fsp + 1920#64) w32
  have ha1 : (fsp + 1920#64) + 1#64 = fsp + 1921#64 := by bv_omega
  have ha5 : (fsp + 1920#64) + 5#64 = fsp + 1925#64 := by bv_omega
  have ha7 : (fsp + 1920#64) + 7#64 = fsp + 1927#64 := by bv_omega
  rw [ha1, ha5, ha7] at h
  rw [← sepConj_assoc, h]
  simp only [sepConj_assoc]

theorem v5c_fsp_1920_unsplit_rest (fsp w32 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1920#64) ↦₈ w32.extractLsb' 0 8) ∗
      ((fsp + 1921#64) ↦₃₂ w32.extractLsb' 8 32) ∗
      ((fsp + 1925#64) ↦₁₆ w32.extractLsb' 40 16) ∗
      ((fsp + 1927#64) ↦₈ w32.extractLsb' 56 8) ∗ Rest =
      ((fsp + 1920#64) ↦₆₄ w32) ∗ Rest :=
  (v5c_fsp_1920_split_rest fsp w32 Rest).symm

theorem v5c_fsp_1968_realign_rest (fsp w80 w88 w96 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1968#64) ↦₆₄ w80) ∗ ((fsp + 1976#64) ↦₆₄ w88) ∗ ((fsp + 1984#64) ↦₆₄ w96) ∗ Rest =
      ((fsp + 1968#64) ↦₈ EncoderFromPb.loByte w80) ∗
      ((fsp + 1969#64) ↦₆₄ (v9_midQ128 w80 w88 w96).extractLsb' 0 64) ∗
      ((fsp + 1977#64) ↦₆₄ (v9_midQ128 w80 w88 w96).extractLsb' 64 64) ∗
      ((fsp + 1985#64) ↦ₛ EncoderFromPb.hiBytes7 w96) ∗ Rest := by
  have h := v9_triple64_eq_byte_q128_tail7 (fsp + 1968#64) w80 w88 w96
  have ha8 : (fsp + 1968#64) + 8#64 = fsp + 1976#64 := by bv_omega
  have ha16 : (fsp + 1968#64) + 16#64 = fsp + 1984#64 := by bv_omega
  have ha1 : (fsp + 1968#64) + 1#64 = fsp + 1969#64 := by bv_omega
  have ha17 : (fsp + 1968#64) + 17#64 = fsp + 1985#64 := by bv_omega
  have ha1977 : (fsp + 1969#64) + 8#64 = fsp + 1977#64 := by bv_omega
  rw [ha8, ha16, ha1, ha17] at h
  change _ = ((fsp + 1968#64) ↦₈ EncoderFromPb.loByte w80) ∗
    ((fsp + 1969#64) ↦₁₂₈ v9_midQ128 w80 w88 w96) ∗
    ((fsp + 1985#64) ↦ₛ EncoderFromPb.hiBytes7 w96) at h
  unfold pointsTo128 at h
  rw [ha1977] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v5c_fsp_1968_unrealign_rest (fsp w80 w88 w96 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1968#64) ↦₈ EncoderFromPb.loByte w80) ∗
      ((fsp + 1969#64) ↦₆₄ (v9_midQ128 w80 w88 w96).extractLsb' 0 64) ∗
      ((fsp + 1977#64) ↦₆₄ (v9_midQ128 w80 w88 w96).extractLsb' 64 64) ∗
      ((fsp + 1985#64) ↦ₛ EncoderFromPb.hiBytes7 w96) ∗ Rest =
    ((fsp + 1968#64) ↦₆₄ w80) ∗ ((fsp + 1976#64) ↦₆₄ w88) ∗ ((fsp + 1984#64) ↦₆₄ w96) ∗ Rest :=
  (v5c_fsp_1968_realign_rest fsp w80 w88 w96 Rest).symm

theorem v5c_fsp_1944_realign_rest (fsp w56 w64 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1944#64) ↦₆₄ w56) ∗ ((fsp + 1952#64) ↦₆₄ w64) ∗ Rest =
      ((fsp + 1944#64) ↦₈ EncoderFromPb.loByte w56) ∗
      ((fsp + 1945#64) ↦₆₄ EncoderFromPb.unshiftWord w56 (EncoderFromPb.loByte w64)) ∗
      ((fsp + 1953#64) ↦ₛ EncoderFromPb.hiBytes7 w64) ∗ Rest := by
  have h := pair64_to_byte_word_tail7 (fsp + 1944#64) w56 w64
  have ha8 : (fsp + 1944#64) + 8#64 = fsp + 1952#64 := by bv_omega
  have ha1 : (fsp + 1944#64) + 1#64 = fsp + 1945#64 := by bv_omega
  have ha9 : (fsp + 1944#64) + 9#64 = fsp + 1953#64 := by bv_omega
  rw [ha8, ha1, ha9] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v5c_fsp_1944_unrealign_rest (fsp w56 w64 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1944#64) ↦₈ EncoderFromPb.loByte w56) ∗
      ((fsp + 1945#64) ↦₆₄ EncoderFromPb.unshiftWord w56 (EncoderFromPb.loByte w64)) ∗
      ((fsp + 1953#64) ↦ₛ EncoderFromPb.hiBytes7 w64) ∗ Rest =
      ((fsp + 1944#64) ↦₆₄ w56) ∗ ((fsp + 1952#64) ↦₆₄ w64) ∗ Rest :=
  (v5c_fsp_1944_realign_rest fsp w56 w64 Rest).symm

theorem v5c_fsp_856_to_64_rest (fsp u856 w96 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 u856) ∗ ((fsp + 863#64) ↦₆₄ w96) ∗ Rest =
      ((fsp + 856#64) ↦₆₄ overlapLow7 u856 w96) ∗
      ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (w96 >>> 8)) ∗ Rest := by
  have h := loBytes7_pointsTo64_eq_overlap (fsp + 856#64) u856 w96
  have ha7 : (fsp + 856#64) + 7#64 = fsp + 863#64 := by bv_omega
  have ha8 : (fsp + 856#64) + 8#64 = fsp + 864#64 := by bv_omega
  rw [ha7, ha8, v9_hiBytes7_eq_loBytes7_lsr8 w96] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v5c_fsp_880_unrealign_unshift_rest (fsp w56 w64 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord w56 (EncoderFromPb.loByte w64))) ∗
      ((fsp + 887#64) ↦₆₄ w64) ∗ Rest =
    ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord w56 (EncoderFromPb.loByte w64)) ∗
      ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (w64 >>> 8)) ∗ Rest := by
  have h := v9_fsp_880_realign_rest fsp (EncoderFromPb.unshiftWord w56 (EncoderFromPb.loByte w64)) w64 Rest
  rwa [v9_overlapLow7_unshift w56 w64] at h

/-- Active stack slots in `fsp + 160..895` written by `+6132..+6416` (before execution). -/
@[expose] def v5c_stagingSlotsPre (fsp : BitVec 64)
    (u160 : BitVec 64) (d172 : BitVec 32) (u208 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u888 : BitVec 64) : SepProp :=
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
  ((fsp + 880#64) ↦₆₄ u880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 u888)

/-- Active stack slots in `fsp + 160..895` after `+6132..+6416` (ready for `epilogueStackSlots`). -/
@[expose] def v5c_stagingSlotsPost (fsp : BitVec 64) (bs : List (BitVec 8)) (p1_new w2272 : BitVec 64) : SepProp :=
  ((fsp + 160#64) ↦₆₄ w2272) ∗
  ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs 80)).zeroExtend 32) ∗
  ((fsp + 208#64) ↦₆₄ p1_new) ∗
  ((fsp + 232#64) ↦₆₄ v9_wordAt bs 368) ∗
  ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs 104) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs 120) ∗
  ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs 136) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs 152) ∗
  ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs 168) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs 184) ∗
  ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs 200) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs 216) ∗
  ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs 232) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs 248) ∗
  ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs 264) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs 280) ∗
  ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs 296) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs 312) ∗
  ((fsp + 832#64) ↦₆₄ v9_wordAt bs 328) ∗
  ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)) ∗
  ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs 96 >>> 8)) ∗
  ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord (v9_wordAt bs 56) (EncoderFromPb.loByte (v9_wordAt bs 64))) ∗
  ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs 64 >>> 8))

theorem v5c_out_64_to_448_eq_bs (out : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) :
    ((out + 64#64) ↦₆₄ v9_wordAt bs 0) ∗ ((out + 72#64) ↦₆₄ v9_wordAt bs 8) ∗
      ((out + 80#64) ↦₆₄ v9_wordAt bs 16) ∗ ((out + 88#64) ↦₆₄ v9_wordAt bs 24) ∗
      (((out + 96#64) ↦₈ (v9_wordAt bs 32).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v9_wordAt bs 32).extractLsb' 8 32) ∗
       ((out + 101#64) ↦₁₆ (v9_wordAt bs 32).extractLsb' 40 16) ∗
       ((out + 103#64) ↦₈ (v9_wordAt bs 32).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v9_wordAt bs 40) ∗ ((out + 112#64) ↦₆₄ v9_wordAt bs 48) ∗
      (((out + 120#64) ↦₈ EncoderFromPb.loByte (v9_wordAt bs 56)) ∗
       ((out + 121#64) ↦₆₄
         EncoderFromPb.unshiftWord (v9_wordAt bs 56) (EncoderFromPb.loByte (v9_wordAt bs 64))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7
           (EncoderFromPb.unshiftWord (v9_wordAt bs 56) (EncoderFromPb.loByte (v9_wordAt bs 64)))
           (v9_wordAt bs 64 >>> 8)))) ∗
      ((out + 136#64) ↦₆₄ v9_wordAt bs 72) ∗
      (((out + 144#64) ↦₈ ((EncoderFromPb.loByte (v9_wordAt bs 80)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄
         (v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄
         overlapWord7
           ((v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)).extractLsb' 64 64)
           (v9_wordAt bs 96 >>> 8))) ∗
      ((out + 168#64) ↦₁₂₈ v9_quadAt bs 104) ∗ ((out + 184#64) ↦₁₂₈ v9_quadAt bs 120) ∗
      ((out + 200#64) ↦₁₂₈ v9_quadAt bs 136) ∗ ((out + 216#64) ↦₁₂₈ v9_quadAt bs 152) ∗
      ((out + 232#64) ↦₁₂₈ v9_quadAt bs 168) ∗ ((out + 248#64) ↦₁₂₈ v9_quadAt bs 184) ∗
      ((out + 264#64) ↦₁₂₈ v9_quadAt bs 200) ∗ ((out + 280#64) ↦₁₂₈ v9_quadAt bs 216) ∗
      ((out + 296#64) ↦₁₂₈ v9_quadAt bs 232) ∗ ((out + 312#64) ↦₁₂₈ v9_quadAt bs 248) ∗
      ((out + 328#64) ↦₁₂₈ v9_quadAt bs 264) ∗ ((out + 344#64) ↦₁₂₈ v9_quadAt bs 280) ∗
      ((out + 360#64) ↦₁₂₈ v9_quadAt bs 296) ∗ ((out + 376#64) ↦₁₂₈ v9_quadAt bs 312) ∗
      ((out + 392#64) ↦₆₄ v9_wordAt bs 328) ∗ ((out + 400#64) ↦₆₄ v9_wordAt bs 336) ∗
      ((out + 408#64) ↦₆₄ v9_wordAt bs 344) ∗ ((out + 416#64) ↦₆₄ v9_wordAt bs 352) ∗
      ((out + 424#64) ↦₆₄ v9_wordAt bs 360) ∗ ((out + 432#64) ↦₆₄ v9_wordAt bs 368) ∗
      ((out + 440#64) ↦₆₄ v9_wordAt bs 376) =
    (out + 64#64) ↦ₛ bs := by
  rw [v9_out_96_realign out (v9_wordAt bs 32),
      v9_out_120_realign out (v9_wordAt bs 56) (v9_wordAt bs 64),
      v9_out_144_realign out (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96),
      v5c_bs384_eq_decCells bs hbs (out + 64#64)]
  unfold v5c_decCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem v5c_unchunkedNoHeaderReceivedAt_8_pack (A : RustAlloc) {F : ShaCompress}
    (out l1 pa1 l2 pa2 ep : BitVec 64)
    (rootKey macKey : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length) :
    ((out + 8#64) ↦₆₄ l1) ∗ ((out + 16#64) ↦₆₄ pa1) ∗ ((out + 24#64) ↦₆₄ l1) ∗
      ((out + 32#64) ↦₆₄ l2) ∗ ((out + 40#64) ↦₆₄ pa2) ∗ ((out + 48#64) ↦₆₄ l2) ∗
      ((out + 56#64) ↦₆₄ ep) ∗
      vecU8Payload A l1 pa1 rootKey ∗
      vecU8Payload A l2 pa2 macKey ⊢
    unchunkedNoHeaderReceivedAt A (F := F) (out + 8#64)
      { auth := { rootKey := rootKey, macKey := macKey }, epoch := ep } := by
  subst hl1 hl2
  dsimp only [unchunkedNoHeaderReceivedAt, authenticatorAt]
  have h1 := vecU8_of_header_payload A (out + 8#64) (BitVec.ofNat 64 rootKey.length) pa1 rootKey
  have h2 := vecU8_of_header_payload A (out + 32#64) (BitVec.ofNat 64 macKey.length) pa2 macKey
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    (((out + 8#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
     ((out + 16#64) ↦₆₄ pa1) ∗
     ((out + 24#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 rootKey.length) pa1 rootKey) ∗
    (((out + 32#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
     ((out + 40#64) ↦₆₄ pa2) ∗
     ((out + 48#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 macKey.length) pa2 macKey) ∗
    ((out + 56#64) ↦₆₄ ep) by ac_rfl)) ?_
  rw [sepConj_assoc (vecU8 A (out + 8#64) rootKey)]
  exact sepConj_mono h1 (sepConj_mono_left h2)

theorem v5c_epilogueOutFull_entails_noHeaderReceived (A : RustAlloc) {F : ShaCompress}
    (out l1 pa1 l2 pa2 ep : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (w392 : BitVec 64) (dec : PolyDecoder) (P_heap : SepProp)
    (hreloc :
      ((out + 64#64) ↦ₛ bs) ∗
        (((out + 64#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        (((out + 64#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢
        polyDecoderAt A (out + 64#64) dec)
    (rootKey macKey : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length)
    (w464 w472 w480 w488 w496 w504 w512 w520 w528 : BitVec 64)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out
      7#64 l1 pa1 l1 l2 pa2 l2 ep
      (v9_wordAt bs 0) (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)
      ((v9_wordAt bs 32).extractLsb' 0 8) ((v9_wordAt bs 32).extractLsb' 8 32)
      ((v9_wordAt bs 32).extractLsb' 40 16) ((v9_wordAt bs 32).extractLsb' 56 8)
      (v9_wordAt bs 40) (v9_wordAt bs 48)
      (EncoderFromPb.loByte (v9_wordAt bs 56))
      (EncoderFromPb.unshiftWord (v9_wordAt bs 56) (EncoderFromPb.loByte (v9_wordAt bs 64)))
      (overlapWord7
        (EncoderFromPb.unshiftWord (v9_wordAt bs 56) (EncoderFromPb.loByte (v9_wordAt bs 64)))
        (v9_wordAt bs 64 >>> 8))
      (v9_wordAt bs 72)
      (((EncoderFromPb.loByte (v9_wordAt bs 80)).zeroExtend 32).setWidth 8)
      (v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96))
      (overlapWord7
        ((v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)).extractLsb' 64 64)
        (v9_wordAt bs 96 >>> 8))
      (v9_quadAt bs 104) (v9_quadAt bs 120) (v9_quadAt bs 136) (v9_quadAt bs 152)
      (v9_quadAt bs 168) (v9_quadAt bs 184) (v9_quadAt bs 200) (v9_quadAt bs 216)
      (v9_quadAt bs 232) (v9_quadAt bs 248) (v9_quadAt bs 264) (v9_quadAt bs 280)
      (v9_quadAt bs 296) (v9_quadAt bs 312)
      (v9_wordAt bs 328) (v9_wordAt bs 336) (v9_wordAt bs 344) (v9_wordAt bs 352)
      (v9_wordAt bs 360) (v9_wordAt bs 368) (v9_wordAt bs 376)
      (BitVec.ofNat 64 dec.ptsNeeded) w392
      w464 w472 w480 w488 w496 w504 w512 w520 w528
      b536 q537 w552 bs240 q888 q904 w920 ∗
      P_heap ∗
      vecU8Payload A l1 pa1 rootKey ∗
      vecU8Payload A l2 pa2 macKey ⊢
    resultChunkedStatesAt A (F := F) out
      (.ok (.noHeaderReceived
        { uc := { auth := { rootKey := rootKey, macKey := macKey }, epoch := ep },
          receiving_hdr := dec })) := by
  dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedNoHeaderReceivedAt]
  have ha64 : (out + 8#64) + 56#64 = out + 64#64 := by bv_omega
  have ha448 : (out + 64#64) + 384#64 = out + 448#64 := by bv_omega
  have ha456 : (out + 64#64) + 392#64 = out + 456#64 := by bv_omega
  rw [ha64]
  rw [ha448, ha456] at hreloc
  unfold epilogueOutFull
  have hbs_eq := v5c_out_64_to_448_eq_bs out bs hbs
  have huc := v5c_unchunkedNoHeaderReceivedAt_8_pack A (F := F) out l1 pa1 l2 pa2 ep rootKey macKey hl1 hl2
  have htail := epilogueOut_tail_464_entails_464 out
    w464 w472 w480 w488 w496 w504 w512 w520 w528
    b536 q537 w552 bs240 hbs240 q888 q904 w920
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 7#64) ∗
    ((((out + 8#64) ↦₆₄ l1) ∗ ((out + 16#64) ↦₆₄ pa1) ∗ ((out + 24#64) ↦₆₄ l1) ∗
      ((out + 32#64) ↦₆₄ l2) ∗ ((out + 40#64) ↦₆₄ pa2) ∗ ((out + 48#64) ↦₆₄ l2) ∗
      ((out + 56#64) ↦₆₄ ep) ∗
      vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey) ∗
     ((((out + 64#64) ↦₆₄ v9_wordAt bs 0) ∗ ((out + 72#64) ↦₆₄ v9_wordAt bs 8) ∗
       ((out + 80#64) ↦₆₄ v9_wordAt bs 16) ∗ ((out + 88#64) ↦₆₄ v9_wordAt bs 24) ∗
       (((out + 96#64) ↦₈ (v9_wordAt bs 32).extractLsb' 0 8) ∗
        ((out + 97#64) ↦₃₂ (v9_wordAt bs 32).extractLsb' 8 32) ∗
        ((out + 101#64) ↦₁₆ (v9_wordAt bs 32).extractLsb' 40 16) ∗
        ((out + 103#64) ↦₈ (v9_wordAt bs 32).extractLsb' 56 8)) ∗
       ((out + 104#64) ↦₆₄ v9_wordAt bs 40) ∗ ((out + 112#64) ↦₆₄ v9_wordAt bs 48) ∗
       (((out + 120#64) ↦₈ EncoderFromPb.loByte (v9_wordAt bs 56)) ∗
        ((out + 121#64) ↦₆₄
          EncoderFromPb.unshiftWord (v9_wordAt bs 56) (EncoderFromPb.loByte (v9_wordAt bs 64))) ∗
        ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
          (overlapWord7
            (EncoderFromPb.unshiftWord (v9_wordAt bs 56) (EncoderFromPb.loByte (v9_wordAt bs 64)))
            (v9_wordAt bs 64 >>> 8)))) ∗
       ((out + 136#64) ↦₆₄ v9_wordAt bs 72) ∗
       (((out + 144#64) ↦₈ ((EncoderFromPb.loByte (v9_wordAt bs 80)).zeroExtend 32).setWidth 8) ∗
        ((out + 145#64) ↦₆₄
          (v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)).extractLsb' 0 64) ∗
        ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
          ((v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)).extractLsb' 64 64)) ∗
        ((out + 160#64) ↦₆₄
          overlapWord7
            ((v9_midQ128 (v9_wordAt bs 80) (v9_wordAt bs 88) (v9_wordAt bs 96)).extractLsb' 64 64)
            (v9_wordAt bs 96 >>> 8))) ∗
       ((out + 168#64) ↦₁₂₈ v9_quadAt bs 104) ∗ ((out + 184#64) ↦₁₂₈ v9_quadAt bs 120) ∗
       ((out + 200#64) ↦₁₂₈ v9_quadAt bs 136) ∗ ((out + 216#64) ↦₁₂₈ v9_quadAt bs 152) ∗
       ((out + 232#64) ↦₁₂₈ v9_quadAt bs 168) ∗ ((out + 248#64) ↦₁₂₈ v9_quadAt bs 184) ∗
       ((out + 264#64) ↦₁₂₈ v9_quadAt bs 200) ∗ ((out + 280#64) ↦₁₂₈ v9_quadAt bs 216) ∗
       ((out + 296#64) ↦₁₂₈ v9_quadAt bs 232) ∗ ((out + 312#64) ↦₁₂₈ v9_quadAt bs 248) ∗
       ((out + 328#64) ↦₁₂₈ v9_quadAt bs 264) ∗ ((out + 344#64) ↦₁₂₈ v9_quadAt bs 280) ∗
       ((out + 360#64) ↦₁₂₈ v9_quadAt bs 296) ∗ ((out + 376#64) ↦₁₂₈ v9_quadAt bs 312) ∗
       ((out + 392#64) ↦₆₄ v9_wordAt bs 328) ∗ ((out + 400#64) ↦₆₄ v9_wordAt bs 336) ∗
       ((out + 408#64) ↦₆₄ v9_wordAt bs 344) ∗ ((out + 416#64) ↦₆₄ v9_wordAt bs 352) ∗
       ((out + 424#64) ↦₆₄ v9_wordAt bs 360) ∗ ((out + 432#64) ↦₆₄ v9_wordAt bs 368) ∗
       ((out + 440#64) ↦₆₄ v9_wordAt bs 376)) ∗
      ((out + 448#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((out + 456#64) ↦₆₄ w392) ∗
      P_heap)) ∗
    (((out + 464#64) ↦₆₄ w464) ∗ ((out + 472#64) ↦₆₄ w472) ∗ ((out + 480#64) ↦₆₄ w480) ∗
     (((out + 488#64) ↦₆₄ w488) ∗ ((out + 496#64) ↦₆₄ w496) ∗ ((out + 504#64) ↦₆₄ w504) ∗
      (((out + 512#64) ↦₆₄ w512) ∗ ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
       (((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
        ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗ ((out + 560#64) ↦ₛ bs240) ∗
        ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920))))) by ac_rfl)) ?_
  rw [hbs_eq]
  exact sepConj_mono_right (sepConj_mono (sepConj_mono huc hreloc) htail)

theorem v5c_fsp_1888_entails_epilogue (fsp w2272 w2280 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) :
    v5c_decCellsAt (fsp + 1888#64) bs ∗
      ((fsp + 2272#64) ↦₆₄ w2272) ∗
      ((fsp + 2280#64) ↦₆₄ w2280) ∗
      memRegion (fsp + 2288#64) 16 ⊢
    ((fsp + 1888#64) ↦₁₂₈ (v9_wordAt bs 8 ++ v9_wordAt bs 0)) ∗
      ((fsp + 1904#64) ↦₁₂₈ (v9_wordAt bs 24 ++ v9_wordAt bs 16)) ∗
      ((fsp + 1920#64) ↦₆₄ v9_wordAt bs 32) ∗
      memRegion (fsp + 1928#64) 376 := by
  rw [← v5c_bs384_eq_decCells bs hbs (fsp + 1888#64),
      v9_bs384_eq_decCells bs hbs (fsp + 1888#64)]
  exact v9_fsp_1888_entails_epilogue fsp w2272 w2280 bs hbs

theorem v5c_fsp_128_entails_32 (fsp pa2 ep : BitVec 64) :
    memRegion (fsp + 128#64) 8 ∗ ((fsp + 136#64) ↦₆₄ pa2) ∗
      memRegion (fsp + 144#64) 8 ∗ ((fsp + 152#64) ↦₆₄ ep) ⊢
      memRegion (fsp + 128#64) 32 := by
  rw [ProofLib.memRegion_split' (b := fsp + 128#64) (n := 8) (k := 24)
        (b' := fsp + 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 136#64) (n := 8) (k := 16)
        (b' := fsp + 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 144#64) (n := 8) (k := 8)
        (b' := fsp + 152#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 136#64) pa2)
      (sepConj_mono_right (ProofLib.pointsTo64_entails_memRegion (fsp + 152#64) ep)))

theorem v5c_memRegion_136_split (fsp : BitVec 64) :
    memRegion fsp 136 ⊢
      memRegion fsp 92 ∗
      (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) ∗
      memRegion (fsp + 96#64) 8 ∗
      (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗
      (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) ∗
      (∃∗ w120 : BitVec 64, ((fsp + 120#64) ↦₆₄ w120)) ∗
      memRegion (fsp + 128#64) 8 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem32_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v5c_memRegion_160_48_split (fsp : BitVec 64) :
    memRegion (fsp + 160#64) 48 ⊢
      (∃∗ u160 : BitVec 64, ((fsp + 160#64) ↦₆₄ u160)) ∗
      memRegion (fsp + 168#64) 4 ∗
      (∃∗ d172 : BitVec 32, ((fsp + 172#64) ↦₃₂ d172)) ∗
      memRegion (fsp + 176#64) 16 ∗
      (∃∗ w192 : BitVec 64, ((fsp + 192#64) ↦₆₄ w192)) ∗
      memRegion (fsp + 200#64) 8 := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem32_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v5c_memRegion_240_1648_split (fsp : BitVec 64) :
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
      (∃∗ u880 : BitVec 64, ((fsp + 880#64) ↦₆₄ u880)) ∗
      ((∃∗ u888 : BitVec 64, ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 u888)) ∗
       memRegion (fsp + 895#64) 993) := by
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
    split_step (mem64_entails _) <|
    v10_memRegion_loBytes7_gap_at fsp 888#64 895#64 992

end CryptoVerification.SpqrV1.States.FromPb

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8d -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8c
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 8 (`EkReceivedCt1Sampled`, `+1764`)

Reconstructs `resultChunkedStatesAt` for `InnerState.ekReceivedCt1Sampled` from `epilogueOutFull`
and assembles the top-level variant theorem `states_from_pb_ekReceivedCt1Sampled_1764` (`+1764 -> s0.x30`).
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
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
/-! ## 1. Realignment & Output Reconstruction After Epilogue (`+8180 -> ret`) -/
theorem v8_out_96_realign (out w80 : BitVec 64) : ((out + 96#64) ↦₈ w80.extractLsb' 0 8) ∗ ((out + 97#64) ↦₃₂ w80.extractLsb' 8 32) ∗ ((out + 101#64) ↦₁₆ w80.extractLsb' 40 16) ∗
      ((out + 103#64) ↦₈ w80.extractLsb' 56 8) = (out + 96#64) ↦₆₄ w80 := by
  have h := (v10_pointsTo64_split_1_4_2_1 (out + 96#64) w80).symm
  have ha97 : (out + 96#64) + 1#64 = out + 97#64 := by bv_omega
  have ha101 : (out + 96#64) + 5#64 = out + 101#64 := by bv_omega
  have ha103 : (out + 96#64) + 7#64 = out + 103#64 := by bv_omega
  rw [ha97, ha101, ha103] at h
  exact h
theorem v8_out_120_realign (out w104 w112 : BitVec 64) : ((out + 120#64) ↦₈ loByte w104) ∗ ((out + 121#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗ ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 (unshiftWord w104 (loByte w112)) (w112 >>> 8))) = ((out + 120#64) ↦₆₄ w104) ∗ ((out + 128#64) ↦₆₄ w112) := by
  rw [v8_overlapWord7_unshift_lsr8 w104 w112]
  have h := (pair64_to_byte_word_tail7 (out + 120#64) w104 w112).symm
  have ha121 : (out + 120#64) + 1#64 = out + 121#64 := by bv_omega
  have ha129 : (out + 120#64) + 9#64 = out + 129#64 := by bv_omega
  have ha128 : (out + 120#64) + 8#64 = out + 128#64 := by bv_omega
  rw [ha121, ha129, ha128] at h
  exact h
theorem v8_out_144_realign (out w128 w136 w144 : BitVec 64) : ((out + 144#64) ↦₈ ((loByte w128).zeroExtend 32).setWidth 8) ∗ ((out + 145#64) ↦₆₄ (v8_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v8_midQ128 w128 w136 w144).extractLsb' 64 64)) ∗ ((out + 160#64) ↦₆₄ overlapWord7 ((v8_midQ128 w128 w136 w144).extractLsb' 64 64) (w144 >>> 8)) =
    ((out + 144#64) ↦₆₄ w128) ∗ ((out + 152#64) ↦₆₄ w136) ∗ ((out + 160#64) ↦₆₄ w144) := by
  rw [v8_zext32_setWidth8 (loByte w128)]
  have hlo : (v8_midQ128 w128 w136 w144).extractLsb' 0 64 = unshiftWord w128 (loByte w136) := by
    unfold v8_midQ128; bv_kernel
  have hhi : (v8_midQ128 w128 w136 w144).extractLsb' 64 64 = unshiftWord w136 (loByte w144) := by
    unfold v8_midQ128; bv_kernel
  rw [hlo, hhi, v8_overlapWord7_unshift_lsr8 w136 w144]
  have hr := loBytes7_pointsTo64_eq_overlap (out + 153#64) (unshiftWord w136 (loByte w144)) w144
  have hov : overlapLow7 (unshiftWord w136 (loByte w144)) w144 = unshiftWord w136 (loByte w144) := by
    unfold overlapLow7 unshiftWord loByte; bv_kernel
  have ha160 : (out + 153#64) + 7#64 = out + 160#64 := by bv_omega
  have ha161 : (out + 153#64) + 8#64 = out + 161#64 := by bv_omega
  rw [ha160, ha161, hov] at hr
  have hq := pointsTo64_pair_eq_pointsTo128 (out + 145#64) (unshiftWord w128 (loByte w136)) (unshiftWord w136 (loByte w144))
  have ha153 : (out + 145#64) + 8#64 = out + 153#64 := by bv_omega
  rw [ha153] at hq
  have ht := (v10_triple64_eq_byte_q128_tail7 (out + 144#64) w128 w136 w144).symm
  have hd145 : (out + 144#64) + 1#64 = out + 145#64 := by bv_omega
  have hd161 : (out + 144#64) + 17#64 = out + 161#64 := by bv_omega
  have hd152 : (out + 144#64) + 8#64 = out + 152#64 := by bv_omega
  have hd160 : (out + 144#64) + 16#64 = out + 160#64 := by bv_omega
  rw [hd145, hd161, hd152, hd160] at ht
  rw [hr, ← sepConj_assoc ((out + 145#64) ↦₆₄ _), hq, ht]
theorem v8_out_16_to_400_eq_bs (out : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) : ((out + 16#64) ↦₆₄ v8_wordAt bs 0) ∗ ((out + 24#64) ↦₆₄ v8_wordAt bs 8) ∗
      ((out + 32#64) ↦₆₄ v8_wordAt bs 16) ∗ ((out + 40#64) ↦₆₄ v8_wordAt bs 24) ∗ ((out + 48#64) ↦₆₄ v8_wordAt bs 32) ∗ ((out + 56#64) ↦₆₄ v8_wordAt bs 40) ∗
      ((out + 64#64) ↦₆₄ v8_wordAt bs 48) ∗ ((out + 72#64) ↦₆₄ v8_wordAt bs 56) ∗ ((out + 80#64) ↦₆₄ v8_wordAt bs 64) ∗ ((out + 88#64) ↦₆₄ v8_wordAt bs 72) ∗ (((out + 96#64) ↦₈ (v8_wordAt bs 80).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v8_wordAt bs 80).extractLsb' 8 32) ∗ ((out + 101#64) ↦₁₆ (v8_wordAt bs 80).extractLsb' 40 16) ∗ ((out + 103#64) ↦₈ (v8_wordAt bs 80).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v8_wordAt bs 88) ∗ ((out + 112#64) ↦₆₄ v8_wordAt bs 96) ∗ (((out + 120#64) ↦₈ loByte (v8_wordAt bs 104)) ∗ ((out + 121#64) ↦₆₄ unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 (overlapWord7 (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)))) ∗ ((out + 136#64) ↦₆₄ v8_wordAt bs 120) ∗
      (((out + 144#64) ↦₈ ((loByte (v8_wordAt bs 128)).zeroExtend 32).setWidth 8) ∗ ((out + 145#64) ↦₆₄ (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64)) ∗ ((out + 160#64) ↦₆₄ overlapWord7
           ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64) (v8_wordAt bs 144 >>> 8))) ∗ ((out + 168#64) ↦₁₂₈ v8_quadAt bs 152) ∗ ((out + 184#64) ↦₁₂₈ v8_quadAt bs 168) ∗
      ((out + 200#64) ↦₁₂₈ v8_quadAt bs 184) ∗ ((out + 216#64) ↦₁₂₈ v8_quadAt bs 200) ∗ ((out + 232#64) ↦₁₂₈ v8_quadAt bs 216) ∗ ((out + 248#64) ↦₁₂₈ v8_quadAt bs 232) ∗
      ((out + 264#64) ↦₁₂₈ v8_quadAt bs 248) ∗ ((out + 280#64) ↦₁₂₈ v8_quadAt bs 264) ∗ ((out + 296#64) ↦₁₂₈ v8_quadAt bs 280) ∗ ((out + 312#64) ↦₁₂₈ v8_quadAt bs 296) ∗
      ((out + 328#64) ↦₁₂₈ v8_quadAt bs 312) ∗ ((out + 344#64) ↦₁₂₈ v8_quadAt bs 328) ∗ ((out + 360#64) ↦₁₂₈ v8_quadAt bs 344) ∗ ((out + 376#64) ↦₁₂₈ v8_quadAt bs 360) ∗ ((out + 392#64) ↦₆₄ v8_wordAt bs 376) =
    ((out + 8#64) + 8#64) ↦ₛ bs := by
  rw [v8_out_96_realign out (v8_wordAt bs 80), v8_out_120_realign out (v8_wordAt bs 104) (v8_wordAt bs 112), v8_out_144_realign out (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144),
      v8_bs384_eq_encCells bs hbs (out + 8#64)]; unfold v8_encCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem v8_fsp_1888_entails_epilogue (fsp tag w2280 : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) : ((fsp + 1888#64) ↦₆₄ tag) ∗ v8_encCellsAt (fsp + 1888#64) bs ∗
      ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16 ⊢ ((fsp + 1888#64) ↦₁₂₈ (v8_wordAt bs 0 ++ tag)) ∗ ((fsp + 1904#64) ↦₁₂₈ (v8_wordAt bs 16 ++ v8_wordAt bs 8)) ∗
      ((fsp + 1920#64) ↦₆₄ v8_wordAt bs 24) ∗ memRegion (fsp + 1928#64) 376 := by
  rw [← v8_bs384_eq_encCells bs hbs (fsp + 1888#64)]
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  rw [ha1896]
  have hbs_split : ((fsp + 1896#64) ↦ₛ bs) = ((fsp + 1896#64) ↦₆₄ v8_wordAt bs 0) ∗ ((fsp + 1904#64) ↦₆₄ v8_wordAt bs 8) ∗ ((fsp + 1912#64) ↦₆₄ v8_wordAt bs 16) ∗ ((fsp + 1920#64) ↦₆₄ v8_wordAt bs 24) ∗
      ((fsp + 1928#64) ↦ₛ bs.drop 32) := by
    have h := v8_bs_drop_step8 hbs (fsp + 1888#64) 8#64 16#64 0 <| v8_bs_drop_step8 hbs (fsp + 1888#64) 16#64 24#64 8 <| v8_bs_drop_step8 hbs (fsp + 1888#64) 24#64 32#64 16 <|
      v8_bs_drop_step8 hbs (fsp + 1888#64) 32#64 40#64 24 rfl
    change (((fsp + 1888#64) + 8#64) ↦ₛ bs) = _ at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd, sepConj_assoc] at h
    exact h
  rw [hbs_split]
  have hq1888 : ((fsp + 1888#64) ↦₆₄ tag) ∗ ((fsp + 1896#64) ↦₆₄ v8_wordAt bs 0) = ((fsp + 1888#64) ↦₁₂₈ (v8_wordAt bs 0 ++ tag)) := by
    rw [← ha1896, pointsTo64_pair_eq_pointsTo128]
  have hq1904 : ((fsp + 1904#64) ↦₆₄ v8_wordAt bs 8) ∗ ((fsp + 1912#64) ↦₆₄ v8_wordAt bs 16) = ((fsp + 1904#64) ↦₁₂₈ (v8_wordAt bs 16 ++ v8_wordAt bs 8)) := by
    have ha : (fsp + 1904#64) + 8#64 = fsp + 1912#64 := by bv_omega
    rw [← ha, pointsTo64_pair_eq_pointsTo128]
  have hlen352 : (bs.drop 32).length = 352 := by rw [List.length_drop, hbs]
  have hm352 : ((fsp + 1928#64) ↦ₛ bs.drop 32) ⊢ memRegion (fsp + 1928#64) 352 := hlen352 ▸ ProofLib.pointsToBytes_entails_memRegion (fsp + 1928#64) (bs.drop 32)
  have hm376 : ((fsp + 1928#64) ↦ₛ bs.drop 32) ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16 ⊢ memRegion (fsp + 1928#64) 376 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1928#64) (n := 352) (k := 24) (b' := fsp + 2280#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 2280#64) (n := 8) (k := 16)
          (b' := fsp + 2288#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono hm352 (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 2280#64) w2280))
  refine Entails.trans (Entails.of_eq (show _ = (((fsp + 1888#64) ↦₆₄ tag) ∗ ((fsp + 1896#64) ↦₆₄ v8_wordAt bs 0)) ∗ (((fsp + 1904#64) ↦₆₄ v8_wordAt bs 8) ∗ ((fsp + 1912#64) ↦₆₄ v8_wordAt bs 16)) ∗
    ((fsp + 1920#64) ↦₆₄ v8_wordAt bs 24) ∗ (((fsp + 1928#64) ↦ₛ bs.drop 32) ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16) by ac_rfl)) ?_
  rw [hq1888, hq1904]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm376))
theorem v8_memRegion_loBytes7_gap_at (a o1 o2 : BitVec 64) (k : Nat) (ho : o1 + 7#64 = o2 := by rfl) (hk : 8 + k ≤ 2 ^ 64 := by decide) : ProofLib.memRegion (a + o1) (7 + (1 + k)) ⊢
      (∃∗ u0 : BitVec 64, ((a + o1) ↦ₛ EncoderFromPb.loBytes7 u0)) ∗ ProofLib.memRegion (a + o2) (1 + k) := by
  have h1 : 7 + (1 + k) = 8 + k := by omega
  rw [h1, ProofLib.memRegion_split' (b := a + o1) (n := 8) (k := k) (b' := a + o1 + 8#64) rfl rfl hk, ProofLib.memRegion_eight (a + o1), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro u0
  rw [pointsTo64_split_7_1 (a + o1) u0, sepConj_assoc, sepExists_sepConj_left]
  refine Entails.sepExists_right u0 (sepConj_mono_right ?_)
  have ha7 : a + o1 + 7#64 = a + o2 := by rw [BitVec.add_assoc, ho]
  have ha8 : a + o1 + 8#64 = a + o2 + 1#64 := by rw [← ha7]; bv_omega
  rw [ha7, ha8, ProofLib.memRegion_split' (b := a + o2) (n := 1) (k := k) (b' := a + o2 + 1#64) rfl rfl (by omega)]
  exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _)
theorem v8_memRegion_entails_bs : ∀ (n : Nat) (a : BitVec 64), n ≤ 2 ^ 64 → ProofLib.memRegion a n ⊢ ∃∗ bs : { l : List (BitVec 8) // l.length = n }, (a ↦ₛ bs.val)
  | 0, a, _ => by
    rw [ProofLib.memRegion_zero]
    refine Entails.sepExists_right ⟨[], rfl⟩ ?_
    rw [ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | n + 1, a, hn => by
    have hsplit : n + 1 = 1 + n := by omega
    rw [hsplit, ProofLib.memRegion_split a 1 n (by omega), ProofLib.memRegion_one a, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro b0
    refine Entails.trans (sepConj_mono_right (v8_memRegion_entails_bs n (a + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ⟨bs, hlen⟩
    refine Entails.sepExists_right ⟨b0 :: bs, by simp [hlen]; omega⟩ ?_
    rw [ProofLib.pointsToBytes_cons]
    exact Entails.refl _
theorem v8_memRegion_328_entails_bs (a : BitVec 64) : ProofLib.memRegion a 328 ⊢ ∃∗ bs : { l : List (BitVec 8) // l.length = 328 }, (a ↦ₛ bs.val) := v8_memRegion_entails_bs 328 a (by decide)
theorem v8_fsp_128_152_entails_32 (fsp ep : BitVec 64) : memRegion (fsp + 128#64) 24 ∗ ((fsp + 152#64) ↦₆₄ ep) ⊢ memRegion (fsp + 128#64) 32 := by
  rw [ProofLib.memRegion_split' (b := fsp + 128#64) (n := 24) (k := 8) (b' := fsp + 152#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (ProofLib.pointsTo64_entails_memRegion (fsp + 152#64) ep)
theorem v8_fsp_176_184_cells_entails_16 (fsp pa3 pa2 : BitVec 64) : ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ⊢ memRegion (fsp + 176#64) 16 := by
  rw [ProofLib.memRegion_split' (b := fsp + 176#64) (n := 8) (k := 8) (b' := fsp + 184#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 176#64) pa3) (ProofLib.pointsTo64_entails_memRegion (fsp + 184#64) pa2)
theorem v8_fsp_64_72_entails_92 (fsp ca5 : BitVec 64) : memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ ca5) ∗ memRegion (fsp + 72#64) 20 ⊢ memRegion fsp 92 := collapse_top <| collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
theorem v8_fsp_96_100_entails_8 (fsp : BitVec 64) (d96 : BitVec 32) : ((fsp + 96#64) ↦₃₂ d96) ∗ memRegion (fsp + 100#64) 4 ⊢ memRegion (fsp + 96#64) 8 := by
  rw [ProofLib.memRegion_split' (b := fsp + 96#64) (n := 4) (k := 4) (b' := fsp + 100#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (pointsTo32_entails_memRegion_4 (fsp + 96#64) d96)
theorem v8_memRegion_72_48_split_11264 (fsp : BitVec 64) : memRegion (fsp + 72#64) 48 ⊢ memRegion (fsp + 72#64) 20 ∗ (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) ∗
      (∃∗ d96 : BitVec 32, ((fsp + 96#64) ↦₃₂ d96)) ∗ memRegion (fsp + 100#64) 4 ∗ (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗ (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) := by
  exact split_top <| split_step (Entails.refl _) <| split_step (mem32_entails _) <| split_step (mem32_entails _) <| split_step (Entails.refl _) <| split_step (mem64_entails _) <| mem64_entails _
theorem v8_memRegion_160_16_split_11264 (fsp : BitVec 64) : memRegion (fsp + 160#64) 16 ⊢ (∃∗ u160 : BitVec 64, ((fsp + 160#64) ↦₆₄ u160)) ∗
      memRegion (fsp + 168#64) 4 ∗ (∃∗ d172 : BitVec 32, ((fsp + 172#64) ↦₃₂ d172)) := by
  exact split_top <| split_step (mem64_entails _) <| split_step (Entails.refl _) <| mem32_entails _
theorem v8_memRegion_240_1648_split_11264 (fsp : BitVec 64) : memRegion (fsp + 240#64) 1648 ⊢ (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
      memRegion (fsp + 568#64) 8 ∗ (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗ ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗ memRegion (fsp + 599#64) 9) ∗
      (∃∗ uq608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ uq608)) ∗ (∃∗ uq624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ uq624)) ∗ (∃∗ uq640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ uq640)) ∗
      (∃∗ uq656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ uq656)) ∗ (∃∗ uq672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ uq672)) ∗ (∃∗ uq688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ uq688)) ∗
      (∃∗ uq704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ uq704)) ∗ (∃∗ uq720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ uq720)) ∗ (∃∗ uq736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ uq736)) ∗
      (∃∗ uq752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ uq752)) ∗ (∃∗ uq768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ uq768)) ∗ (∃∗ uq784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ uq784)) ∗
      (∃∗ uq800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ uq800)) ∗ (∃∗ uq816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ uq816)) ∗ (∃∗ u832 : BitVec 64, ((fsp + 832#64) ↦₆₄ u832)) ∗ memRegion (fsp + 840#64) 8 ∗
      (∃∗ uq848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ uq848)) ∗ ((∃∗ u864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864)) ∗ memRegion (fsp + 871#64) 9) ∗
      ((∃∗ u880 : BitVec 64, ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880)) ∗ (∃∗ u887 : BitVec 64, ((fsp + 887#64) ↦₆₄ u887))) ∗ memRegion (fsp + 895#64) 993 := by
  exact split_top <| split_step (v8_memRegion_328_entails_bs _) <| split_step (Entails.refl _) <| split_step (mem128_entails _) <| split_step (v8_memRegion_loBytes7_gap_at fsp 592#64 599#64 8) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <| split_step (mem128_entails _) <|
    split_step (v8_memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <| split_step (memRegion_15_entails_loBytes7_and_64_at fsp 880#64 887#64) <| Entails.refl _
theorem v8_fsp_split_11264_all (fsp : BitVec 64) : memRegion (fsp + 72#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗ memRegion (fsp + 192#64) 8 ∗
      memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 232#64) 8 ∗ memRegion (fsp + 240#64) 1648 ⊢ memRegion (fsp + 72#64) 20 ∗ (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) ∗
      (∃∗ d96 : BitVec 32, ((fsp + 96#64) ↦₃₂ d96)) ∗ memRegion (fsp + 100#64) 4 ∗ (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗ (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) ∗
      (∃∗ u160 : BitVec 64, ((fsp + 160#64) ↦₆₄ u160)) ∗ memRegion (fsp + 168#64) 4 ∗ (∃∗ d172 : BitVec 32, ((fsp + 172#64) ↦₃₂ d172)) ∗ (∃∗ w192 : BitVec 64, ((fsp + 192#64) ↦₆₄ w192)) ∗
      (∃∗ u208 : BitVec 64, ((fsp + 208#64) ↦₆₄ u208)) ∗ (∃∗ u232 : BitVec 64, ((fsp + 232#64) ↦₆₄ u232)) ∗ (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
      memRegion (fsp + 568#64) 8 ∗ (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗ ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗ memRegion (fsp + 599#64) 9) ∗
      (∃∗ uq608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ uq608)) ∗ (∃∗ uq624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ uq624)) ∗ (∃∗ uq640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ uq640)) ∗
      (∃∗ uq656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ uq656)) ∗ (∃∗ uq672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ uq672)) ∗ (∃∗ uq688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ uq688)) ∗
      (∃∗ uq704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ uq704)) ∗ (∃∗ uq720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ uq720)) ∗ (∃∗ uq736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ uq736)) ∗
      (∃∗ uq752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ uq752)) ∗ (∃∗ uq768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ uq768)) ∗ (∃∗ uq784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ uq784)) ∗
      (∃∗ uq800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ uq800)) ∗ (∃∗ uq816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ uq816)) ∗ (∃∗ u832 : BitVec 64, ((fsp + 832#64) ↦₆₄ u832)) ∗ memRegion (fsp + 840#64) 8 ∗
      (∃∗ uq848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ uq848)) ∗ ((∃∗ u864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864)) ∗ memRegion (fsp + 871#64) 9) ∗
      ((∃∗ u880 : BitVec 64, ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880)) ∗ (∃∗ u887 : BitVec 64, ((fsp + 887#64) ↦₆₄ u887))) ∗ memRegion (fsp + 895#64) 993 := by
  refine Entails.trans (sepConj_mono (v8_memRegion_72_48_split_11264 fsp) (sepConj_mono (v8_memRegion_160_16_split_11264 fsp) (sepConj_mono (mem64_entails (fsp + 192#64)) (sepConj_mono (mem64_entails (fsp + 208#64))
            (sepConj_mono (mem64_entails (fsp + 232#64)) (v8_memRegion_240_1648_split_11264 fsp)))))) ?_
  exact Entails.of_eq (by ac_rfl)
theorem v8_vecU8_of_header_payload_cap (A : RustAlloc) (a cap ptr len : BitVec 64) (bs : List (BitVec 8)) (hlen : len = BitVec.ofNat 64 bs.length) : (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len) ∗
      vecU8Payload A cap ptr bs ⊢ vecU8 A a bs := by
  subst hlen; unfold vecU8 vecU8At vecHeader vecU8Payload
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)
theorem v8_unchunkedCt1SentEkReceivedAt_408_pack (A : RustAlloc) {F : ShaCompress} (out l1 pa1 l2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 ep : BitVec 64) (rootKey macKey es ek ct1 : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length) (hl2 : l2 = BitVec.ofNat 64 macKey.length) (hes : es.length = 2080) (hek : ek.length = 1152) (hct1 : ct1.length = 960) :
    ((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗ ((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗
      ((out + 456#64) ↦₆₄ ca3) ∗ ((out + 464#64) ↦₆₄ pa3) ∗ ((out + 472#64) ↦₆₄ 2080#64) ∗ ((out + 480#64) ↦₆₄ ca4) ∗ ((out + 488#64) ↦₆₄ pa4) ∗ ((out + 496#64) ↦₆₄ 1152#64) ∗
      ((out + 504#64) ↦₆₄ ca5) ∗ ((out + 512#64) ↦₆₄ pa5) ∗ ((out + 520#64) ↦₆₄ 960#64) ∗ ((out + 528#64) ↦₆₄ ep) ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗
      vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ⊢ unchunkedCt1SentEkReceivedAt A (F := F) (out + 408#64)
        { auth := { rootKey := rootKey, macKey := macKey }, es := es, ek := ek, ct1 := ct1, epoch := ep } := by
  dsimp only [unchunkedCt1SentEkReceivedAt, authenticatorAt]
  have h1 := v8_vecU8_of_header_payload_cap A (out + 408#64) l1 pa1 l1 rootKey hl1
  have h2 := v8_vecU8_of_header_payload_cap A (out + 432#64) l2 pa2 l2 macKey hl2
  have h3 := v8_vecU8_of_header_payload_cap A (out + 456#64) ca3 pa3 2080#64 es (by rw [hes])
  have h4 := v8_vecU8_of_header_payload_cap A (out + 480#64) ca4 pa4 1152#64 ek (by rw [hek])
  have h5 := v8_vecU8_of_header_payload_cap A (out + 504#64) ca5 pa5 960#64 ct1 (by rw [hct1])
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h1 h2 h3 h4 h5 ⊢
  refine Entails.trans (Entails.of_eq (show _ = (((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗ vecU8Payload A l1 pa1 rootKey) ∗
    (((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗ vecU8Payload A l2 pa2 macKey) ∗ (((out + 456#64) ↦₆₄ ca3) ∗ ((out + 464#64) ↦₆₄ pa3) ∗ ((out + 472#64) ↦₆₄ 2080#64) ∗
     vecU8Payload A ca3 pa3 es) ∗ (((out + 480#64) ↦₆₄ ca4) ∗ ((out + 488#64) ↦₆₄ pa4) ∗ ((out + 496#64) ↦₆₄ 1152#64) ∗ vecU8Payload A ca4 pa4 ek) ∗
    (((out + 504#64) ↦₆₄ ca5) ∗ ((out + 512#64) ↦₆₄ pa5) ∗ ((out + 520#64) ↦₆₄ 960#64) ∗ vecU8Payload A ca5 pa5 ct1) ∗ ((out + 528#64) ↦₆₄ ep) by ac_rfl)) ?_
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono_left h5))))
theorem v8_epilogueOutFull_entails_ekReceivedCt1Sampled (A : RustAlloc) {F : ShaCompress} (out tag l1 pa1 l2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 ep : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp) (hreloc : ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗ (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
        polyEncoderAt A (out + 8#64) enc) (rootKey macKey es ek ct1 : List (BitVec 8)) (hl1 : l1 = BitVec.ofNat 64 rootKey.length) (hl2 : l2 = BitVec.ofNat 64 macKey.length) (hes : es.length = 2080)
    (hek : ek.length = 1152) (hct1 : ct1.length = 960) (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64) (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328) (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out 10#64 tag (v8_wordAt bs 0) (v8_wordAt bs 8) (v8_wordAt bs 16) (v8_wordAt bs 24) (v8_wordAt bs 32) (v8_wordAt bs 40) (v8_wordAt bs 48) (v8_wordAt bs 56) (v8_wordAt bs 64) (v8_wordAt bs 72)
      ((v8_wordAt bs 80).extractLsb' 0 8) ((v8_wordAt bs 80).extractLsb' 8 32) ((v8_wordAt bs 80).extractLsb' 40 16) ((v8_wordAt bs 80).extractLsb' 56 8) (v8_wordAt bs 88) (v8_wordAt bs 96) (loByte (v8_wordAt bs 104))
      (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (overlapWord7 (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)) (v8_wordAt bs 120)
      (((loByte (v8_wordAt bs 128)).zeroExtend 32).setWidth 8) (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) (overlapWord7
        ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64) (v8_wordAt bs 144 >>> 8)) (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200)
      (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264) (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328) (v8_quadAt bs 344) (v8_quadAt bs 360)
      (v8_wordAt bs 376) (hi32 ++ enc.idx) l1 pa1 l1 l2 pa2 l2 ca3 pa3 2080#64 ca4 pa4 1152#64 ca5 pa5 960#64 ep b536 q537 w552 bs240 q888 q904 w920 ∗ P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗
      vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ⊢ resultChunkedStatesAt A (F := F) out (.ok (.ekReceivedCt1Sampled
        { uc := { auth := { rootKey := rootKey, macKey := macKey }, es := es, ek := ek, ct1 := ct1, epoch := ep }, sending_ct1 := enc })) := by
  dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedEkReceivedCt1SampledAt]
  have ha408 : (out + 8#64) + 400#64 = out + 408#64 := by bv_omega
  have ha400 : (out + 8#64) + 392#64 = out + 400#64 := by bv_omega
  rw [ha408, sepConj_assoc (polyEncoderAt A (out + 8#64) enc)]
  rw [ha400] at hreloc; unfold epilogueOutFull
  have hbs_eq := v8_out_16_to_400_eq_bs out bs hbs
  have huc := v8_unchunkedCt1SentEkReceivedAt_408_pack A (F := F) out l1 pa1 l2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 ep rootKey macKey es ek ct1 hl1 hl2 hes hek hct1
  have htail := epilogueOut_tail_536_entails_392 out b536 q537 w552 bs240 hbs240 q888 q904 w920
  refine Entails.trans (Entails.of_eq (show _ = (out ↦₆₄ 10#64) ∗ (((out + 8#64) ↦₆₄ tag) ∗ (((out + 16#64) ↦₆₄ v8_wordAt bs 0) ∗ ((out + 24#64) ↦₆₄ v8_wordAt bs 8) ∗
      ((out + 32#64) ↦₆₄ v8_wordAt bs 16) ∗ ((out + 40#64) ↦₆₄ v8_wordAt bs 24) ∗ ((out + 48#64) ↦₆₄ v8_wordAt bs 32) ∗ ((out + 56#64) ↦₆₄ v8_wordAt bs 40) ∗
      ((out + 64#64) ↦₆₄ v8_wordAt bs 48) ∗ ((out + 72#64) ↦₆₄ v8_wordAt bs 56) ∗ ((out + 80#64) ↦₆₄ v8_wordAt bs 64) ∗ ((out + 88#64) ↦₆₄ v8_wordAt bs 72) ∗ (((out + 96#64) ↦₈ (v8_wordAt bs 80).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v8_wordAt bs 80).extractLsb' 8 32) ∗ ((out + 101#64) ↦₁₆ (v8_wordAt bs 80).extractLsb' 40 16) ∗ ((out + 103#64) ↦₈ (v8_wordAt bs 80).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v8_wordAt bs 88) ∗ ((out + 112#64) ↦₆₄ v8_wordAt bs 96) ∗ (((out + 120#64) ↦₈ loByte (v8_wordAt bs 104)) ∗ ((out + 121#64) ↦₆₄ unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 (overlapWord7 (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)))) ∗ ((out + 136#64) ↦₆₄ v8_wordAt bs 120) ∗
      (((out + 144#64) ↦₈ ((loByte (v8_wordAt bs 128)).zeroExtend 32).setWidth 8) ∗ ((out + 145#64) ↦₆₄ (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64)) ∗ ((out + 160#64) ↦₆₄ overlapWord7
           ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64) (v8_wordAt bs 144 >>> 8))) ∗ ((out + 168#64) ↦₁₂₈ v8_quadAt bs 152) ∗ ((out + 184#64) ↦₁₂₈ v8_quadAt bs 168) ∗
      ((out + 200#64) ↦₁₂₈ v8_quadAt bs 184) ∗ ((out + 216#64) ↦₁₂₈ v8_quadAt bs 200) ∗ ((out + 232#64) ↦₁₂₈ v8_quadAt bs 216) ∗ ((out + 248#64) ↦₁₂₈ v8_quadAt bs 232) ∗
      ((out + 264#64) ↦₁₂₈ v8_quadAt bs 248) ∗ ((out + 280#64) ↦₁₂₈ v8_quadAt bs 264) ∗ ((out + 296#64) ↦₁₂₈ v8_quadAt bs 280) ∗ ((out + 312#64) ↦₁₂₈ v8_quadAt bs 296) ∗
      ((out + 328#64) ↦₁₂₈ v8_quadAt bs 312) ∗ ((out + 344#64) ↦₁₂₈ v8_quadAt bs 328) ∗ ((out + 360#64) ↦₁₂₈ v8_quadAt bs 344) ∗ ((out + 376#64) ↦₁₂₈ v8_quadAt bs 360) ∗ ((out + 392#64) ↦₆₄ v8_wordAt bs 376)) ∗
     ((out + 400#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap) ∗ (((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗ ((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗
     ((out + 456#64) ↦₆₄ ca3) ∗ ((out + 464#64) ↦₆₄ pa3) ∗ ((out + 472#64) ↦₆₄ 2080#64) ∗ ((out + 480#64) ↦₆₄ ca4) ∗ ((out + 488#64) ↦₆₄ pa4) ∗ ((out + 496#64) ↦₆₄ 1152#64) ∗
     ((out + 504#64) ↦₆₄ ca5) ∗ ((out + 512#64) ↦₆₄ pa5) ∗ ((out + 520#64) ↦₆₄ 960#64) ∗ ((out + 528#64) ↦₆₄ ep) ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗
     vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1) ∗ (((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
     ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗ ((out + 560#64) ↦ₛ bs240) ∗ ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920)) by ac_rfl)) ?_
  rw [hbs_eq]
  exact sepConj_mono_right (sepConj_mono hreloc (sepConj_mono huc htail))
theorem v8_fsp_collapse_240_to_1888 (fsp w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : memRegion (fsp + 240#64) 56 ∗ memRegion (fsp + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt (fsp + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (fsp + 1576#64) 312 ⊢ memRegion (fsp + 240#64) 1648 := collapse_top <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
    collapse_step (v1_optProtoPolyEncoderWordsAt_entails_56 (fsp + 1520#64) w0 w8 w16 w24 w32 w40 w48) <| Entails.refl _
theorem v8_fsp_collapse_2304 (fsp v64 v120 v176 v184 v200 v216 v224 : BitVec 64) : memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ v64) ∗ memRegion (fsp + 72#64) 48 ∗
      ((fsp + 120#64) ↦₆₄ v120) ∗ memRegion (fsp + 128#64) 32 ∗ memRegion (fsp + 160#64) 16 ∗ ((fsp + 176#64) ↦₆₄ v176) ∗ ((fsp + 184#64) ↦₆₄ v184) ∗ memRegion (fsp + 192#64) 8 ∗
      ((fsp + 200#64) ↦₆₄ v200) ∗ memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ v216) ∗ ((fsp + 224#64) ↦₆₄ v224) ∗ memRegion (fsp + 232#64) 8 ∗ memRegion (fsp + 240#64) 1648 ∗ memRegion (fsp + 1888#64) 400 ∗
      memRegion (fsp + 2288#64) 16 ⊢ memRegion fsp 2304 := collapse_top <| collapse_step0 (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <| Entails.refl _
theorem v8_fsp_896_split_1984 (fsp : BitVec 64) : memRegion fsp 896 ⊢ memRegion fsp 64 ∗ (∃∗ v64 : BitVec 64, ((fsp + 64#64) ↦₆₄ v64)) ∗ memRegion (fsp + 72#64) 48 ∗ (∃∗ v120 : BitVec 64, ((fsp + 120#64) ↦₆₄ v120)) ∗
      memRegion (fsp + 128#64) 32 ∗ memRegion (fsp + 160#64) 16 ∗ (∃∗ v176 : BitVec 64, ((fsp + 176#64) ↦₆₄ v176)) ∗ (∃∗ v184 : BitVec 64, ((fsp + 184#64) ↦₆₄ v184)) ∗
      memRegion (fsp + 192#64) 8 ∗ (∃∗ v200 : BitVec 64, ((fsp + 200#64) ↦₆₄ v200)) ∗ memRegion (fsp + 208#64) 8 ∗ (∃∗ v216 : BitVec 64, ((fsp + 216#64) ↦₆₄ v216)) ∗
      (∃∗ v224 : BitVec 64, ((fsp + 224#64) ↦₆₄ v224)) ∗ memRegion (fsp + 232#64) 8 ∗ memRegion (fsp + 240#64) 56 ∗ memRegion (fsp + 296#64) 600 := by
  exact split_top <| split_step0 (Entails.refl _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <| split_step (Entails.refl _) <| Entails.refl _
theorem v8_fsp_1576_split_728 (fsp : BitVec 64) : memRegion (fsp + 1576#64) 728 ⊢ memRegion (fsp + 1576#64) 312 ∗ memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16 := by
  exact split_top <| split_step (Entails.refl _) <| split_step (Entails.refl _) <| Entails.refl _
theorem v8_fsp_296_to_1520_collapse (fsp u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64) : memRegion (fsp + 296#64) 600 ∗
      v8_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ memRegion (fsp + 1024#64) 496 ⊢ memRegion (fsp + 296#64) 1224 := collapse_top <| collapse_step (Entails.refl _) <|
    collapse_step (v8_ucWordsAt_entails_128 (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128) <| Entails.refl _
theorem v8_sepWPp_weaken_panic {prog : Program} {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop} (R : SepProp) (h : SepWPp prog ret s P Q (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf)) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hret | ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ := h R' hm hL
  · exact ⟨sf, hsteps, Or.inl hret⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, fun hmR => Satisfies.mono (sepConj_mono_left hqp) hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩
theorem v8_sepWPp_seq {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp} {Q_mid Q Qp : State → SepProp → Prop} (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q_mid sm Pm → SepWPp prog ret sm Pm Q Qp) : SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hqm⟩ | hpan⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps2, hout⟩ := h2 sm Pm hpcm hrunm hqm R hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact ⟨sm, hsteps1, Or.inr hpan⟩
theorem v8_fsp_240_split_56 (fsp : BitVec 64) : memRegion (fsp + 240#64) 56 ⊢ (∃∗ z240 : BitVec 64, (fsp + 240#64) ↦₆₄ z240) ∗ (∃∗ z248 : BitVec 64, (fsp + 248#64) ↦₆₄ z248) ∗
      (∃∗ z256 : BitVec 64, (fsp + 256#64) ↦₆₄ z256) ∗ (∃∗ z264 : BitVec 64, (fsp + 264#64) ↦₆₄ z264) ∗ (∃∗ z272 : BitVec 64, (fsp + 272#64) ↦₆₄ z272) ∗ (∃∗ z280 : BitVec 64, (fsp + 280#64) ↦₆₄ z280) ∗
      (∃∗ z288 : BitVec 64, (fsp + 288#64) ↦₆₄ z288) := by
  exact split_top <| split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <| mem64_entails _
theorem v8_pb_uc_enc_entails_224 (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : (pbA ↦₆₄ 0x8000000000000008#64) ∗
      v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ⊢
      memRegion pbA optProtoInnerStateSize := by
  have h := v8_pb128_entails_full_224 pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
  rw [← v8_uc_and_enc_words_eq_pb128] at h
  exact Entails.trans (Entails.of_eq (by ac_rfl)) h
theorem v8_states_from_pb_sendingCt1_err_any_eq {F : ShaCompress} (u : V1State.Unchunked.Ct1SentEkReceived) (auth : ProtoAuthenticator) (pbEnc : PolynomialEncoder) (err : PolynomialError)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) = true) (hauth : u.auth = some auth)
    (henc : fromPbResult (pbToProtoPolyEncoder pbEnc) = .error err) : States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := some pbEnc }) } =
    .error (.err .stateDecode) := by
  have henc' := fromPb_eq_ok (pbToProtoPolyEncoder pbEnc)
  rw [henc] at henc'
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb, Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, hauth, ↓reduceIte,
    encoderFromPbStateDecode, spqrPolyApi, henc', StatesResult.ofPanic, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]
theorem v8_tag2_392_entails_400 (fsp : BitVec 64) : ((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392 ⊢ memRegion (fsp + 1888#64) 400 :=
  collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
theorem v8_5vecs_entails_dealloc (A : RustAlloc) (c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64) (b1 b2 b3 b4 b5 : List (BitVec 8)) : vecU8Payload A c1 p1 b1 ∗ vecU8Payload A c2 p2 b2 ∗ vecU8Payload A c3 p3 b3 ∗
      vecU8Payload A c4 p4 b4 ∗ vecU8Payload A c5 p5 b5 ⊢ vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ vecCapPtrDealloc A c3 p3 ∗ vecCapPtrDealloc A c4 p4 ∗ vecCapPtrDealloc A c5 p5 :=
  sepConj_mono (vecU8Payload_entails_dealloc A c1 p1 b1) (sepConj_mono (vecU8Payload_entails_dealloc A c2 p2 b2) (sepConj_mono (vecU8Payload_entails_dealloc A c3 p3 b3)
        (sepConj_mono (vecU8Payload_entails_dealloc A c4 p4 b4) (vecU8Payload_entails_dealloc A c5 p5 b5))))
theorem v8_ucWordsAt_896_eq (fsp u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64) : v8_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 =
      ((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗ ((fsp + 920#64) ↦₆₄ u32) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
      ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗ ((fsp + 968#64) ↦₆₄ u80) ∗ ((fsp + 976#64) ↦₆₄ u88) ∗ ((fsp + 984#64) ↦₆₄ u96) ∗
      ((fsp + 992#64) ↦₆₄ u104) ∗ ((fsp + 1000#64) ↦₆₄ u112) ∗ ((fsp + 1008#64) ↦₆₄ u120) ∗ ((fsp + 1016#64) ↦₆₄ u128) := by
  dsimp only [v8_ucWordsAt]
  simp only [v8_bv_add_add_lit, BitVec.ofNat_eq_ofNat]
theorem v8_len_ok_of_true (u : V1State.Unchunked.Ct1SentEkReceived) (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) = true) :
    u.es.length = 2080 ∧ u.ct1.length = 960 ∧ u.ek.length = 1152 := by
  dsimp only [ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE, ENCAPSULATION_KEY_SIZE] at hlen
  simp only [Bool.and_eq_true, beq_iff_eq] at hlen
  exact ⟨hlen.1.1, hlen.1.2, hlen.2⟩
theorem v8_len_err_of_false (u : V1State.Unchunked.Ct1SentEkReceived) (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) = false)
    (hes_lt : u.es.length < 2 ^ 63) (hct1_lt : u.ct1.length < 2 ^ 63) (hek_lt : u.ek.length < 2 ^ 63) : BitVec.ofNat 64 u.es.length ≠ 2080#64 ∨ BitVec.ofNat 64 u.ct1.length ≠ 960#64 ∨
    BitVec.ofNat 64 u.ek.length ≠ 1152#64 := by
  dsimp only [ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE, ENCAPSULATION_KEY_SIZE] at hlen
  by_cases h1 : u.es.length = 2080
  · by_cases h2 : u.ct1.length = 960
    · by_cases h3 : u.ek.length = 1152
      · simp [h1, h2, h3] at hlen
      · right; right; intro heq
        have hto := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
        exact h3 hto
    · right; left; intro heq
      have hto := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
      exact h2 hto
  · left; intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    exact h1 hto
theorem v8_optProtoInnerStateAt_ekReceivedCt1Sampled_eq (A : RustAlloc) (pbA : BitVec 64) (s : V1State.Chunked.EkReceivedCt1Sampled) : optProtoInnerStateAt A pbA (some (.ekReceivedCt1Sampled s)) =
      (pbA ↦₆₄ 0x8000000000000008#64) ∗ optProtoUnchunkedCt1SentEkReceivedAt A (pbA + 8#64) s.uc ∗ optProtoPolynomialEncoderAt A (pbA + 136#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗ memRegion (pbA + 192#64) 32 := by
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedEkReceivedCt1SampledAt]
  have h136 : (pbA + 8#64) + 128#64 = pbA + 136#64 := by bv_omega
  rw [h136]; ac_rfl
theorem v8_3vecs_entails_dealloc (A : RustAlloc) (c1 p1 c2 p2 c3 p3 : BitVec 64) (b1 b2 b3 : List (BitVec 8)) : vecU8Payload A c1 p1 b1 ∗ vecU8Payload A c2 p2 b2 ∗ vecU8Payload A c3 p3 b3 ⊢
    vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ vecCapPtrDealloc A c3 p3 := sepConj_mono (vecU8Payload_entails_dealloc A c1 p1 b1) (sepConj_mono (vecU8Payload_entails_dealloc A c2 p2 b2)
      (vecU8Payload_entails_dealloc A c3 p3 b3))
end CryptoVerification.SpqrV1.States.FromPb

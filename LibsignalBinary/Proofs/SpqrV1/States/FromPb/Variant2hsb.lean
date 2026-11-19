/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsa -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part B

Stack copy (`+508..+588`), `ptsNeeded == 480` check (`+592`), `Unchunked::EkSent` validation
(`+3348..+3436`), and `Authenticator::from_pb` assembly (`+3436 -> +9032`).
-/

public section

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open V1State.Chunked
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



/-! ## PB-to-Stack Copy (`+508..+588`) & `pts_needed == 480` Check (`+592..+600`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem v2hs_bv_sub_sub_lit (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

attribute [local simp, local arm64_norm, local wp_norm] v2hs_bv_add_add_lit

theorem v2hs_memRegion_2304_split_896_176_1232 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 896 ∗
      (∃∗ q0 : BitVec 128, (fsp + 896#64) ↦₁₂₈ q0) ∗
      (∃∗ q1 : BitVec 128, (fsp + 912#64) ↦₁₂₈ q1) ∗
      (∃∗ q2 : BitVec 128, (fsp + 928#64) ↦₁₂₈ q2) ∗
      (∃∗ q3 : BitVec 128, (fsp + 944#64) ↦₁₂₈ q3) ∗
      (∃∗ q4 : BitVec 128, (fsp + 960#64) ↦₁₂₈ q4) ∗
      (∃∗ q5 : BitVec 128, (fsp + 976#64) ↦₁₂₈ q5) ∗
      (∃∗ q6 : BitVec 128, (fsp + 992#64) ↦₁₂₈ q6) ∗
      (∃∗ q7 : BitVec 128, (fsp + 1008#64) ↦₁₂₈ q7) ∗
      (∃∗ q8 : BitVec 128, (fsp + 1024#64) ↦₁₂₈ q8) ∗
      (∃∗ q9 : BitVec 128, (fsp + 1040#64) ↦₁₂₈ q9) ∗
      (∃∗ q10 : BitVec 128, (fsp + 1056#64) ↦₁₂₈ q10) ∗
      memRegion (fsp + 1072#64) 1232 := by
  rw [ProofLib.memRegion_split fsp 896 1408 (by decide),
      ProofLib.memRegion_split' (b := fsp + 896#64) (n := 176) (k := 1232)
        (b' := fsp + 1072#64) rfl (by bv_omega) (by decide)]
  simpa only [arm64_norm, sepConj_assoc] using
    sepConj_mono_right (sepConj_mono_left (v2hs_memRegion_176_to_128 (fsp + 896#64)))

/-- Stack split of `memRegion fsp 896` into the 8 scratch slots used by Variant 2 (`96, 152, 176, 184, 200, 216, 224, 232`). -/
@[expose] def v2hs_stack896ScratchRest (fsp : BitVec 64) : SepProp :=
  memRegion fsp 96 ∗ memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
  memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8

theorem v2hs_memRegion_896_split_scratch (fsp : BitVec 64) :
    memRegion fsp 896 ⊢
      (∃∗ w96 : BitVec 64, (fsp + 96#64) ↦₆₄ w96) ∗
      (∃∗ w152 : BitVec 64, (fsp + 152#64) ↦₆₄ w152) ∗
      (∃∗ w176 : BitVec 64, (fsp + 176#64) ↦₆₄ w176) ∗
      (∃∗ w184 : BitVec 64, (fsp + 184#64) ↦₆₄ w184) ∗
      (∃∗ w200 : BitVec 64, (fsp + 200#64) ↦₆₄ w200) ∗
      (∃∗ w216 : BitVec 64, (fsp + 216#64) ↦₆₄ w216) ∗
      (∃∗ w224 : BitVec 64, (fsp + 224#64) ↦₆₄ w224) ∗
      (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 656 ∗
      v2hs_stack896ScratchRest fsp := by
  have h :
      memRegion fsp 896 ⊢
        memRegion fsp 96 ∗
        (∃∗ w96 : BitVec 64, (fsp + 96#64) ↦₆₄ w96) ∗
        memRegion (fsp + 104#64) 48 ∗
        (∃∗ w152 : BitVec 64, (fsp + 152#64) ↦₆₄ w152) ∗
        memRegion (fsp + 160#64) 16 ∗
        (∃∗ w176 : BitVec 64, (fsp + 176#64) ↦₆₄ w176) ∗
        (∃∗ w184 : BitVec 64, (fsp + 184#64) ↦₆₄ w184) ∗
        memRegion (fsp + 192#64) 8 ∗
        (∃∗ w200 : BitVec 64, (fsp + 200#64) ↦₆₄ w200) ∗
        memRegion (fsp + 208#64) 8 ∗
        (∃∗ w216 : BitVec 64, (fsp + 216#64) ↦₆₄ w216) ∗
        (∃∗ w224 : BitVec 64, (fsp + 224#64) ↦₆₄ w224) ∗
        (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
        memRegion (fsp + 240#64) 656 :=
    split_top <|
      split_step0 (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      Entails.refl _
  refine Entails.trans h ?_
  dsimp only [v2hs_stack896ScratchRest]
  exact Entails.of_eq (by ac_rfl)

theorem v2hs_memRegion_896_unsplit_scratch (fsp w96 w152 w216 w224 w232 : BitVec 64) :
    ((fsp + 96#64) ↦₆₄ w96) ∗
      ((fsp + 152#64) ↦₆₄ w152) ∗
      memRegion (fsp + 176#64) 8 ∗
      memRegion (fsp + 184#64) 8 ∗
      memRegion (fsp + 200#64) 8 ∗
      ((fsp + 216#64) ↦₆₄ w216) ∗
      ((fsp + 224#64) ↦₆₄ w224) ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 656 ∗
      v2hs_stack896ScratchRest fsp ⊢
      memRegion fsp 896 := by
  dsimp only [v2hs_stack896ScratchRest]
  have hcol :
      memRegion fsp 96 ∗ ((fsp + 96#64) ↦₆₄ w96) ∗ memRegion (fsp + 104#64) 48 ∗
      ((fsp + 152#64) ↦₆₄ w152) ∗ memRegion (fsp + 160#64) 16 ∗ memRegion (fsp + 176#64) 8 ∗
      memRegion (fsp + 184#64) 8 ∗ memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
      memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ⊢
      memRegion fsp 896 :=
    collapse_top <|
      collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Entails.refl _
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hcol

theorem v2hs_merge_240_656_80_736 (fsp : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) :
    memRegion (fsp + 240#64) 656 ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ⊢
      memRegion (fsp + 240#64) 736 := by
  rw [ProofLib.memRegion_split' (b := fsp + 240#64) (n := 656) (k := 80)
    (b' := fsp + 896#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (v2hs_ucWordsAt_entails_80 (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80)

theorem v2hs_pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

theorem v2hs_vecU8Payload_of_nil (A : RustAlloc) :
    emp ⊢ vecU8Payload A (BitVec.ofNat 64 ([] : List (BitVec 8)).length) 1#64 [] := by
  unfold vecU8Payload
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

theorem v2hs_vecU8Payload_pos_unpack (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8Payload A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
      (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8Payload
  apply Entails.pure_left; intro ⟨hle, hlt, hptr⟩
  have hcap : cap ≠ 0#64 := cap_ne_zero_of_pos hpos hle
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hptr, hcap⟩ (Entails.refl _)

theorem v2hs_vecU8Payload_pos_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
    vecCapPtrDealloc A cap ptr := by
  refine Entails.trans ?_ (vecU8Payload_entails_dealloc A cap ptr bs)
  unfold vecU8Payload
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

/-- Ten 64-bit words (`80` bytes) of `Unchunked.SendEk.EkSent` at `a` (`fsp + 1264#64`). -/
@[expose] def v2hs_ekSentWordsAt (a u48 pa1 u72 pa2 u8 u16 u24 u80 : BitVec 64) : SepProp :=
  (a ↦₆₄ u48) ∗ ((a + 8#64) ↦₆₄ pa1) ∗ ((a + 16#64) ↦₆₄ u48) ∗
  ((a + 24#64) ↦₆₄ u72) ∗ ((a + 32#64) ↦₆₄ pa2) ∗ ((a + 40#64) ↦₆₄ u72) ∗
  ((a + 48#64) ↦₆₄ u8) ∗ ((a + 56#64) ↦₆₄ u16) ∗ ((a + 64#64) ↦₆₄ u24) ∗
  ((a + 72#64) ↦₆₄ u80)

theorem v2hs_reconstruct_pa1 (sp0 pa1 : BitVec 64) :
    ((sp0 - 1128#64) ↦₈ BitVec.zeroExtend 8 pa1) ∗
      ((sp0 - 1127#64) ↦₃₂ BitVec.truncate 32 (pa1 >>> 8)) ∗
      ((sp0 - 1123#64) ↦₁₆ BitVec.truncate 16 (BitVec.truncate 32 (pa1 >>> 40))) ∗
      ((sp0 - 1121#64) ↦₈ BitVec.zeroExtend 8 (pa1 >>> 56)) ⊢
      ((sp0 - 1128#64) ↦₆₄ pa1) := by
  have h0 : BitVec.zeroExtend 8 pa1 = pa1.extractLsb' 0 8 := by bv_kernel
  have h1 : BitVec.truncate 32 (pa1 >>> 8) = pa1.extractLsb' 8 32 := by bv_kernel
  have h2 : BitVec.truncate 16 (BitVec.truncate 32 (pa1 >>> 40)) = pa1.extractLsb' 40 16 := by bv_kernel
  have h3 : BitVec.zeroExtend 8 (pa1 >>> 56) = pa1.extractLsb' 56 8 := by bv_kernel
  have ha1 : sp0 - 1128#64 + 1#64 = sp0 - 1127#64 := by bv_omega
  have ha5 : sp0 - 1128#64 + 5#64 = sp0 - 1123#64 := by bv_omega
  have ha7 : sp0 - 1128#64 + 7#64 = sp0 - 1121#64 := by bv_omega
  rw [h0, h1, h2, h3, ← ha1, ← ha5, ← ha7, ← v10_pointsTo64_split_1_4_2_1 (sp0 - 1128#64) pa1]
  exact Entails.refl _

theorem v2hs_memRegion_1232_split_1264 (fsp : BitVec 64) :
    memRegion (fsp + 1072#64) 1232 ⊢
      memRegion (fsp + 1072#64) 192 ∗
      (∃∗ e0 : BitVec 64, (fsp + 1264#64) ↦₆₄ e0) ∗ (∃∗ e1 : BitVec 64, (fsp + 1272#64) ↦₆₄ e1) ∗
      (∃∗ e2 : BitVec 64, (fsp + 1280#64) ↦₆₄ e2) ∗ (∃∗ e3 : BitVec 64, (fsp + 1288#64) ↦₆₄ e3) ∗
      (∃∗ e4 : BitVec 64, (fsp + 1296#64) ↦₆₄ e4) ∗ (∃∗ e5 : BitVec 64, (fsp + 1304#64) ↦₆₄ e5) ∗
      (∃∗ e6 : BitVec 64, (fsp + 1312#64) ↦₆₄ e6) ∗ (∃∗ e7 : BitVec 64, (fsp + 1320#64) ↦₆₄ e7) ∗
      (∃∗ e8 : BitVec 64, (fsp + 1328#64) ↦₆₄ e8) ∗ (∃∗ e9 : BitVec 64, (fsp + 1336#64) ↦₆₄ e9) ∗
      memRegion (fsp + 1344#64) 960 := by
  have h : ∀ b : BitVec 64, memRegion b 1232 ⊢
      memRegion b 192 ∗ (∃∗ e0 : BitVec 64, (b + 192#64) ↦₆₄ e0) ∗
      (∃∗ e1 : BitVec 64, (b + 200#64) ↦₆₄ e1) ∗ (∃∗ e2 : BitVec 64, (b + 208#64) ↦₆₄ e2) ∗
      (∃∗ e3 : BitVec 64, (b + 216#64) ↦₆₄ e3) ∗ (∃∗ e4 : BitVec 64, (b + 224#64) ↦₆₄ e4) ∗
      (∃∗ e5 : BitVec 64, (b + 232#64) ↦₆₄ e5) ∗ (∃∗ e6 : BitVec 64, (b + 240#64) ↦₆₄ e6) ∗
      (∃∗ e7 : BitVec 64, (b + 248#64) ↦₆₄ e7) ∗ (∃∗ e8 : BitVec 64, (b + 256#64) ↦₆₄ e8) ∗
      (∃∗ e9 : BitVec 64, (b + 264#64) ↦₆₄ e9) ∗ memRegion (b + 272#64) 960 := fun b =>
    split_top <|
      split_step0 (Entails.refl _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      Entails.refl _
  simpa only [v2hs_bv_add_add_lit, BitVec.ofNat_eq_ofNat, sepConj_assoc] using h (fsp + 1072#64)

end CryptoVerification.SpqrV1.States.FromPb

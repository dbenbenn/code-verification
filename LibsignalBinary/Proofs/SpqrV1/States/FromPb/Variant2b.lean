/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 1 (`KeysSampled`, `+1104`) — Part B

**Checked by Lean.**

Header unpacking, stack copy (`+1104..+1192`), validation (`+1196..+1292`), and `auth.rootKey`
cloning (`+1292 -> +8756`) for `InnerState.keysSampled`.
-/

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



@[local simp, local arm64_norm, local wp_norm]
theorem v1_bv_add_add_lit' (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_bv_sub_sub_lit' (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## Unpacking `optProtoUnchunkedHeaderSentAt` into `v1_ucWordsAt` -/

/-- Heap and pure constraints of `Option<V1State.Unchunked.HeaderSent>` associated with words `u8..u104`. -/
@[expose] def v1_optProtoUcHeap (A : RustAlloc) :
    Option V1State.Unchunked.HeaderSent →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → SepProp
  | none, u8, _, _, _, _, _, _, _, _, _, _, _, _ => ⌜u8 = noneCap⌝
  | some uc, u8, u16, u24, u32, u40, u48, u56, u64, u72, u80, u88, u96, u104 =>
    ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 uc.ek.length ∧
      u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 uc.dk.length ∧
      u104 = uc.epoch⌝ ∗
    vecU8Payload A u8 u16 uc.ek ∗
    vecU8Payload A u32 u40 uc.dk ∗
    v1_optProtoAuthHeap A uc.auth u56 u64 u72 u80 u88 u96

theorem v1_vecU8_unpack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64, ∃∗ l : BitVec 64,
        ⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 bs.length⌝ ∗
        (a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l) ∗
        vecU8Payload A c p bs := by
  unfold vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro c
  apply Entails.sepExists_elim; intro p
  unfold vecU8Payload
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜bs.length ≤ c.toNat ∧ c.toNat < 2 ^ 63 ∧ p ≠ 0#64⌝ ∗
    ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
     if c = 0#64 then emp
     else A.live p c.toNat 1 ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hle, hc_lt, hp_ne⟩
  refine Entails.sepExists_right c (Entails.sepExists_right p
    (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_))
  refine Entails.pure_right ⟨hc_lt, rfl⟩ ?_
  have hpure : bs.length ≤ c.toNat ∧ c.toNat < 2 ^ 63 ∧ p ≠ 0#64 := ⟨hle, hc_lt, hp_ne⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v1_optProtoAuthAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optAuth : Option ProtoAuthenticator) :
    optProtoAuthenticatorAt A a optAuth ⊢
      ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64, ∃∗ u72 : BitVec 64,
      ∃∗ u80 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u96 : BitVec 64,
        ((a ↦₆₄ u56) ∗ ((a + 8#64) ↦₆₄ u64) ∗ ((a + 16#64) ↦₆₄ u72) ∗
         ((a + 24#64) ↦₆₄ u80) ∗ ((a + 32#64) ↦₆₄ u88) ∗ ((a + 40#64) ↦₆₄ u96)) ∗
        v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 := by
  cases optAuth with
  | none =>
    unfold optProtoAuthenticatorAt v1_optProtoAuthHeap
    have hsplit : memRegion (a + 8#64) 40 ⊢
        (∃∗ u64 : BitVec 64, (a + 8#64) ↦₆₄ u64) ∗
        (∃∗ u72 : BitVec 64, (a + 16#64) ↦₆₄ u72) ∗
        (∃∗ u80 : BitVec 64, (a + 24#64) ↦₆₄ u80) ∗
        (∃∗ u88 : BitVec 64, (a + 32#64) ↦₆₄ u88) ∗
        (∃∗ u96 : BitVec 64, (a + 40#64) ↦₆₄ u96) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u64
    refine Entails.sepExists_right noneCap (Entails.sepExists_right u64
      (Entails.sepExists_right u72 (Entails.sepExists_right u80
        (Entails.sepExists_right u88 (Entails.sepExists_right u96 ?_)))))
    exact Entails.trans (Entails.pure_right (rfl : noneCap = noneCap) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))
  | some auth =>
    unfold optProtoAuthenticatorAt protoAuthenticatorAt v1_optProtoAuthHeap
    refine Entails.trans (sepConj_mono (v1_vecU8_unpack A a auth.rootKey)
      (v1_vecU8_unpack A (a + 24#64) auth.macKey)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u56
    apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u72
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    rw [ha32, ha40]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 auth.rootKey.length⌝ ∗
      ⌜u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
      ((a ↦₆₄ u56) ∗ ((a + 8#64) ↦₆₄ u64) ∗ ((a + 16#64) ↦₆₄ u72) ∗
       ((a + 24#64) ↦₆₄ u80) ∗ ((a + 32#64) ↦₆₄ u88) ∗ ((a + 40#64) ↦₆₄ u96) ∗
       vecU8Payload A u56 u64 auth.rootKey ∗
       vecU8Payload A u80 u88 auth.macKey) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨hu56, hu72⟩
    apply Entails.pure_left; rintro ⟨_, hu96⟩
    refine Entails.sepExists_right u56 (Entails.sepExists_right u64
      (Entails.sepExists_right u72 (Entails.sepExists_right u80
        (Entails.sepExists_right u88 (Entails.sepExists_right u96 ?_)))))
    have hpure : u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 auth.rootKey.length ∧
        u96 = BitVec.ofNat 64 auth.macKey.length := ⟨hu56, hu72, hu96⟩
    exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v1_optProtoUnchunkedHeaderSentAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optUc : Option V1State.Unchunked.HeaderSent) :
    optProtoUnchunkedHeaderSentAt A a optUc ⊢
      ∃∗ u8 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u24 : BitVec 64,
      ∃∗ u32 : BitVec 64, ∃∗ u40 : BitVec 64, ∃∗ u48 : BitVec 64,
      ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64, ∃∗ u72 : BitVec 64,
      ∃∗ u80 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u96 : BitVec 64,
      ∃∗ u104 : BitVec 64,
        v1_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoUcHeap A optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 := by
  cases optUc with
  | none =>
    unfold optProtoUnchunkedHeaderSentAt v1_optProtoUcHeap
    have hsplit : memRegion (a + 8#64) 96 ⊢
        (∃∗ u16 : BitVec 64, (a + 8#64) ↦₆₄ u16) ∗
        (∃∗ u24 : BitVec 64, (a + 16#64) ↦₆₄ u24) ∗
        (∃∗ u32 : BitVec 64, (a + 24#64) ↦₆₄ u32) ∗
        (∃∗ u40 : BitVec 64, (a + 32#64) ↦₆₄ u40) ∗
        (∃∗ u48 : BitVec 64, (a + 40#64) ↦₆₄ u48) ∗
        (∃∗ u56 : BitVec 64, (a + 48#64) ↦₆₄ u56) ∗
        (∃∗ u64 : BitVec 64, (a + 56#64) ↦₆₄ u64) ∗
        (∃∗ u72 : BitVec 64, (a + 64#64) ↦₆₄ u72) ∗
        (∃∗ u80 : BitVec 64, (a + 72#64) ↦₆₄ u80) ∗
        (∃∗ u88 : BitVec 64, (a + 80#64) ↦₆₄ u88) ∗
        (∃∗ u96 : BitVec 64, (a + 88#64) ↦₆₄ u96) ∗
        (∃∗ u104 : BitVec 64, (a + 96#64) ↦₆₄ u104) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u104
    apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u56
    apply Entails.sepExists_elim; intro u48
    apply Entails.sepExists_elim; intro u40
    apply Entails.sepExists_elim; intro u32
    apply Entails.sepExists_elim; intro u24
    apply Entails.sepExists_elim; intro u16
    refine Entails.sepExists_right noneCap (Entails.sepExists_right u16
      (Entails.sepExists_right u24 (Entails.sepExists_right u32
        (Entails.sepExists_right u40 (Entails.sepExists_right u48
          (Entails.sepExists_right u56 (Entails.sepExists_right u64
            (Entails.sepExists_right u72 (Entails.sepExists_right u80
               (Entails.sepExists_right u88 (Entails.sepExists_right u96
                (Entails.sepExists_right u104 ?_))))))))))))
    unfold v1_ucWordsAt
    exact Entails.trans (Entails.pure_right (rfl : noneCap = noneCap) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))
  | some uc =>
    unfold optProtoUnchunkedHeaderSentAt protoUnchunkedHeaderSentAt
    refine Entails.trans (sepConj_mono (v1_vecU8_unpack A a uc.ek)
      (sepConj_mono (v1_vecU8_unpack A (a + 24#64) uc.dk)
        (sepConj_mono_left (v1_optProtoAuthAt_unpack A (a + 48#64) uc.auth)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u56
    apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u32
    apply Entails.sepExists_elim; intro u40
    apply Entails.sepExists_elim; intro u48
    apply Entails.sepExists_elim; intro u8
    apply Entails.sepExists_elim; intro u16
    apply Entails.sepExists_elim; intro u24
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
    have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
    have ha72 : a + 48#64 + 24#64 = a + 72#64 := by bv_omega
    have ha80 : a + 48#64 + 32#64 = a + 80#64 := by bv_omega
    have ha88 : a + 48#64 + 40#64 = a + 88#64 := by bv_omega
    rw [ha32, ha40, ha56, ha64, ha72, ha80, ha88]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 uc.ek.length⌝ ∗
      ⌜u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 uc.dk.length⌝ ∗
      ((a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ u24) ∗
       ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ u48) ∗
       ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ u72) ∗
       ((a + 72#64) ↦₆₄ u80) ∗ ((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗
       ((a + 96#64) ↦₆₄ uc.epoch) ∗
       vecU8Payload A u8 u16 uc.ek ∗
       vecU8Payload A u32 u40 uc.dk ∗
       v1_optProtoAuthHeap A uc.auth u56 u64 u72 u80 u88 u96) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨hu8, hu24⟩
    apply Entails.pure_left; rintro ⟨hu32, hu48⟩
    refine Entails.sepExists_right u8 (Entails.sepExists_right u16
      (Entails.sepExists_right u24 (Entails.sepExists_right u32
        (Entails.sepExists_right u40 (Entails.sepExists_right u48
          (Entails.sepExists_right u56 (Entails.sepExists_right u64
            (Entails.sepExists_right u72 (Entails.sepExists_right u80
              (Entails.sepExists_right u88 (Entails.sepExists_right u96
                (Entails.sepExists_right uc.epoch ?_))))))))))))
    dsimp only [v1_optProtoUcHeap]
    refine Entails.trans (Entails.of_eq (show _ =
      v1_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 uc.epoch ∗
      (vecU8Payload A u8 u16 uc.ek ∗
       vecU8Payload A u32 u40 uc.dk ∗
       v1_optProtoAuthHeap A uc.auth u56 u64 u72 u80 u88 u96) by
      unfold v1_ucWordsAt; ac_rfl)) ?_
    exact sepConj_mono_right (Entails.pure_right ⟨hu8, hu24, hu32, hu48, rfl⟩ (Entails.refl _))

/-! ## PB-to-Stack Copy (`+1104..+1192`) -/

theorem v1_memRegion_2304_split_1392_160_752 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 1392 ∗
      (∃∗ q0 : BitVec 128, (fsp + 1392#64) ↦₁₂₈ q0) ∗
      (∃∗ q1 : BitVec 128, (fsp + 1408#64) ↦₁₂₈ q1) ∗
      (∃∗ q2 : BitVec 128, (fsp + 1424#64) ↦₁₂₈ q2) ∗
      (∃∗ q3 : BitVec 128, (fsp + 1440#64) ↦₁₂₈ q3) ∗
      (∃∗ q4 : BitVec 128, (fsp + 1456#64) ↦₁₂₈ q4) ∗
      (∃∗ q5 : BitVec 128, (fsp + 1472#64) ↦₁₂₈ q5) ∗
      (∃∗ q6 : BitVec 128, (fsp + 1488#64) ↦₁₂₈ q6) ∗
      (∃∗ q7 : BitVec 128, (fsp + 1504#64) ↦₁₂₈ q7) ∗
      (∃∗ q8 : BitVec 128, (fsp + 1520#64) ↦₁₂₈ q8) ∗
      (∃∗ q9 : BitVec 128, (fsp + 1536#64) ↦₁₂₈ q9) ∗
      memRegion (fsp + 1552#64) 752 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    Entails.refl _

theorem v1_pointsTo128_eq_pair64_1008 (sp u8 u16 : BitVec 64) :
    ((sp - 1008#64) ↦₁₂₈ (u16 ++ u8)) =
      ((sp - 1008#64) ↦₆₄ u8) ∗ ((sp - 1000#64) ↦₆₄ u16) := by
  rw [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (sp - 1008#64) u8 u16]
  have ha : sp - 1008#64 + 8#64 = sp - 1000#64 := by bv_omega
  rw [ha]

theorem v1_merge_1392_104_1496 (fsp : BitVec 64) :
    memRegion fsp 1392 ∗ memRegion (fsp + 1392#64) 104 ⊢ memRegion fsp 1496 :=
  collapse_top <| collapse_step0 (Entails.refl _) <| Entails.refl _

theorem v1_memRegion_1392_split_frame (fsp : BitVec 64) :
    memRegion fsp 1392 ⊢
      memRegion fsp 64 ∗
      (∃∗ w64 : BitVec 64, (fsp + 64#64) ↦₆₄ w64) ∗
      memRegion (fsp + 72#64) 104 ∗
      (∃∗ w176 : BitVec 64, (fsp + 176#64) ↦₆₄ w176) ∗
      (∃∗ w184 : BitVec 64, (fsp + 184#64) ↦₆₄ w184) ∗
      (∃∗ w192 : BitVec 64, (fsp + 192#64) ↦₆₄ w192) ∗
      (∃∗ w200 : BitVec 64, (fsp + 200#64) ↦₆₄ w200) ∗
      memRegion (fsp + 208#64) 8 ∗
      (∃∗ w216 : BitVec 64, (fsp + 216#64) ↦₆₄ w216) ∗
      (∃∗ w224 : BitVec 64, (fsp + 224#64) ↦₆₄ w224) ∗
      (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 1152 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v1_frame_entails_192_216_224_1496
    (fsp w64 w176 w184 w192 w200 w216 w224 w232 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    memRegion fsp 64 ∗
      ((fsp + 64#64) ↦₆₄ w64) ∗
      memRegion (fsp + 72#64) 104 ∗
      ((fsp + 176#64) ↦₆₄ w176) ∗
      ((fsp + 184#64) ↦₆₄ w184) ∗
      ((fsp + 192#64) ↦₆₄ w192) ∗
      ((fsp + 200#64) ↦₆₄ w200) ∗
      memRegion (fsp + 208#64) 8 ∗
      ((fsp + 216#64) ↦₆₄ w216) ∗
      ((fsp + 224#64) ↦₆₄ w224) ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 1152 ∗
      v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢
      memRegion fsp 192 ∗
      ((fsp + 192#64) ↦₆₄ w192) ∗
      memRegion (fsp + 200#64) 16 ∗
      ((fsp + 216#64) ↦₆₄ w216) ∗
      ((fsp + 224#64) ↦₆₄ w224) ∗
      memRegion (fsp + 232#64) 1264 := by
  have h192 : memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ memRegion (fsp + 72#64) 104 ∗
      ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ⊢ memRegion fsp 192 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  have h16 : ((fsp + 200#64) ↦₆₄ w200) ∗ memRegion (fsp + 208#64) 8 ⊢ memRegion (fsp + 200#64) 16 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have huc := v1_ucWordsAt_entails_104 (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
  have h1264 : ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 1152 ∗ memRegion (fsp + 1392#64) 104 ⊢
      memRegion (fsp + 232#64) 1264 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ memRegion (fsp + 72#64) 104 ∗
     ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184)) ∗
    ((fsp + 192#64) ↦₆₄ w192) ∗
    (((fsp + 200#64) ↦₆₄ w200) ∗ memRegion (fsp + 208#64) 8) ∗
    ((fsp + 216#64) ↦₆₄ w216) ∗
    ((fsp + 224#64) ↦₆₄ w224) ∗
    (((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 1152 ∗
     v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) by ac_rfl)) ?_
  exact sepConj_mono h192 (sepConj_mono_right (sepConj_mono h16 (sepConj_mono_right (sepConj_mono_right
    (Entails.trans (sepConj_mono_right (sepConj_mono_right huc)) h1264)))))

theorem v1_merge_240_1152_104_1256 (fsp : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    memRegion (fsp + 240#64) 1152 ∗
      v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢
      memRegion (fsp + 240#64) 1256 := by
  have huc := v1_ucWordsAt_entails_104 (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
  have hm : memRegion (fsp + 240#64) 1152 ∗ memRegion (fsp + 1392#64) 104 ⊢ memRegion (fsp + 240#64) 1256 :=
    collapse_top <| collapse_step (Entails.refl _) <| Entails.refl _
  exact Entails.trans (sepConj_mono_right huc) hm

end CryptoVerification.SpqrV1.States.FromPb

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 8 (`EkReceivedCt1Sampled`, `+1764`) — Part B

Unpacking of `Option<V1State.Unchunked.Ct1SentEkReceived>`, PB-to-stack copy (`+1764..+1872`),
`s.uc = none` error exit, and `es`/`ct1`/`ek` byte-length validation (`+1872 -> +1936 -> +2100 | +1972`).
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
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



@[local simp, local arm64_norm, local wp_norm]
theorem v8_bv_add_add_lit' (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v8_bv_sub_sub_lit' (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## 1. Unpacking `optProtoUnchunkedCt1SentEkReceivedAt` into `v8_ucWordsAt` -/

/-- Heap and pure constraints of `Option<V1State.Unchunked.Ct1SentEkReceived>` associated with words `u8..u128`. -/
@[expose] def v8_optProtoUcHeap (A : RustAlloc) :
    Option V1State.Unchunked.Ct1SentEkReceived →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, u8, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => ⌜u8 = noneCap⌝
  | some uc, u8, u16, u24, u32, u40, u48, u56, u64, u72, u80, u88, u96, u104, u112, u120, u128 =>
    ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 uc.es.length ∧
      u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 uc.ek.length ∧
      u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 uc.ct1.length ∧
      u128 = uc.epoch⌝ ∗
    vecU8Payload A u8 u16 uc.es ∗
    vecU8Payload A u32 u40 uc.ek ∗
    vecU8Payload A u56 u64 uc.ct1 ∗
    v1_optProtoAuthHeap A uc.auth u80 u88 u96 u104 u112 u120

theorem v8_vecU8_unpack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
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

theorem v8_optProtoAuthAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optAuth : Option ProtoAuthenticator) :
    optProtoAuthenticatorAt A a optAuth ⊢
      ∃∗ u80 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u96 : BitVec 64,
      ∃∗ u104 : BitVec 64, ∃∗ u112 : BitVec 64, ∃∗ u120 : BitVec 64,
        ((a ↦₆₄ u80) ∗ ((a + 8#64) ↦₆₄ u88) ∗ ((a + 16#64) ↦₆₄ u96) ∗
         ((a + 24#64) ↦₆₄ u104) ∗ ((a + 32#64) ↦₆₄ u112) ∗ ((a + 40#64) ↦₆₄ u120)) ∗
        v1_optProtoAuthHeap A optAuth u80 u88 u96 u104 u112 u120 := by
  cases optAuth with
  | none =>
    unfold optProtoAuthenticatorAt v1_optProtoAuthHeap
    have hsplit : memRegion (a + 8#64) 40 ⊢
        (∃∗ u88 : BitVec 64, (a + 8#64) ↦₆₄ u88) ∗
        (∃∗ u96 : BitVec 64, (a + 16#64) ↦₆₄ u96) ∗
        (∃∗ u104 : BitVec 64, (a + 24#64) ↦₆₄ u104) ∗
        (∃∗ u112 : BitVec 64, (a + 32#64) ↦₆₄ u112) ∗
        (∃∗ u120 : BitVec 64, (a + 40#64) ↦₆₄ u120) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u120
    apply Entails.sepExists_elim; intro u112
    apply Entails.sepExists_elim; intro u104
    apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u88
    refine Entails.sepExists_right noneCap (Entails.sepExists_right u88
      (Entails.sepExists_right u96 (Entails.sepExists_right u104
        (Entails.sepExists_right u112 (Entails.sepExists_right u120 ?_)))))
    exact Entails.trans (Entails.pure_right (rfl : noneCap = noneCap) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))
  | some auth =>
    unfold optProtoAuthenticatorAt protoAuthenticatorAt v1_optProtoAuthHeap
    refine Entails.trans (sepConj_mono (v8_vecU8_unpack A a auth.rootKey)
      (v8_vecU8_unpack A (a + 24#64) auth.macKey)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u104
    apply Entails.sepExists_elim; intro u112
    apply Entails.sepExists_elim; intro u120
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u96
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    rw [ha32, ha40]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.rootKey.length⌝ ∗
      ⌜u104.toNat < 2 ^ 63 ∧ u120 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
      ((a ↦₆₄ u80) ∗ ((a + 8#64) ↦₆₄ u88) ∗ ((a + 16#64) ↦₆₄ u96) ∗
       ((a + 24#64) ↦₆₄ u104) ∗ ((a + 32#64) ↦₆₄ u112) ∗ ((a + 40#64) ↦₆₄ u120) ∗
       vecU8Payload A u80 u88 auth.rootKey ∗
       vecU8Payload A u104 u112 auth.macKey) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨hu80, hu96⟩
    apply Entails.pure_left; rintro ⟨_, hu120⟩
    refine Entails.sepExists_right u80 (Entails.sepExists_right u88
      (Entails.sepExists_right u96 (Entails.sepExists_right u104
        (Entails.sepExists_right u112 (Entails.sepExists_right u120 ?_)))))
    have hpure : u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.rootKey.length ∧
        u120 = BitVec.ofNat 64 auth.macKey.length := ⟨hu80, hu96, hu120⟩
    exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v8_optProtoUnchunkedCt1SentEkReceivedAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1SentEkReceived) :
    optProtoUnchunkedCt1SentEkReceivedAt A a optUc ⊢
      ∃∗ u8 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u24 : BitVec 64,
      ∃∗ u32 : BitVec 64, ∃∗ u40 : BitVec 64, ∃∗ u48 : BitVec 64,
      ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64, ∃∗ u72 : BitVec 64,
      ∃∗ u80 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u96 : BitVec 64,
      ∃∗ u104 : BitVec 64, ∃∗ u112 : BitVec 64, ∃∗ u120 : BitVec 64,
      ∃∗ u128 : BitVec 64,
        v8_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        v8_optProtoUcHeap A optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 := by
  cases optUc with
  | none =>
    unfold optProtoUnchunkedCt1SentEkReceivedAt v8_optProtoUcHeap
    have hsplit : memRegion (a + 8#64) 120 ⊢
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
        (∃∗ u104 : BitVec 64, (a + 96#64) ↦₆₄ u104) ∗
        (∃∗ u112 : BitVec 64, (a + 104#64) ↦₆₄ u112) ∗
        (∃∗ u120 : BitVec 64, (a + 112#64) ↦₆₄ u120) ∗
        (∃∗ u128 : BitVec 64, (a + 120#64) ↦₆₄ u128) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u128
    apply Entails.sepExists_elim; intro u120
    apply Entails.sepExists_elim; intro u112
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
                (Entails.sepExists_right u104 (Entails.sepExists_right u112
                  (Entails.sepExists_right u120 (Entails.sepExists_right u128 ?_)))))))))))))))
    unfold v8_ucWordsAt
    exact Entails.trans (Entails.pure_right (rfl : noneCap = noneCap) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))
  | some uc =>
    unfold optProtoUnchunkedCt1SentEkReceivedAt protoUnchunkedCt1SentEkReceivedAt
    refine Entails.trans (sepConj_mono (v8_vecU8_unpack A a uc.es)
      (sepConj_mono (v8_vecU8_unpack A (a + 24#64) uc.ek)
        (sepConj_mono (v8_vecU8_unpack A (a + 48#64) uc.ct1)
          (sepConj_mono_left (v8_optProtoAuthAt_unpack A (a + 72#64) uc.auth))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u104
    apply Entails.sepExists_elim; intro u112
    apply Entails.sepExists_elim; intro u120
    apply Entails.sepExists_elim; intro u56
    apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u72
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
    have ha80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
    have ha88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
    have ha96 : a + 72#64 + 24#64 = a + 96#64 := by bv_omega
    have ha104 : a + 72#64 + 32#64 = a + 104#64 := by bv_omega
    have ha112 : a + 72#64 + 40#64 = a + 112#64 := by bv_omega
    rw [ha32, ha40, ha56, ha64, ha80, ha88, ha96, ha104, ha112]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 uc.es.length⌝ ∗
      ⌜u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 uc.ek.length⌝ ∗
      ⌜u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 uc.ct1.length⌝ ∗
      ((a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ u24) ∗
       ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ u48) ∗
       ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ u72) ∗
       ((a + 72#64) ↦₆₄ u80) ∗ ((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗
       ((a + 96#64) ↦₆₄ u104) ∗ ((a + 104#64) ↦₆₄ u112) ∗ ((a + 112#64) ↦₆₄ u120) ∗
       ((a + 120#64) ↦₆₄ uc.epoch) ∗
       vecU8Payload A u8 u16 uc.es ∗
       vecU8Payload A u32 u40 uc.ek ∗
       vecU8Payload A u56 u64 uc.ct1 ∗
       v1_optProtoAuthHeap A uc.auth u80 u88 u96 u104 u112 u120) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨hu8, hu24⟩
    apply Entails.pure_left; rintro ⟨hu32, hu48⟩
    apply Entails.pure_left; rintro ⟨hu56, hu72⟩
    refine Entails.sepExists_right u8 (Entails.sepExists_right u16
      (Entails.sepExists_right u24 (Entails.sepExists_right u32
        (Entails.sepExists_right u40 (Entails.sepExists_right u48
          (Entails.sepExists_right u56 (Entails.sepExists_right u64
            (Entails.sepExists_right u72 (Entails.sepExists_right u80
              (Entails.sepExists_right u88 (Entails.sepExists_right u96
                (Entails.sepExists_right u104 (Entails.sepExists_right u112
                  (Entails.sepExists_right u120 (Entails.sepExists_right uc.epoch ?_)))))))))))))))
    dsimp only [v8_optProtoUcHeap]
    refine Entails.trans (Entails.of_eq (show _ =
      v8_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 uc.epoch ∗
      (vecU8Payload A u8 u16 uc.es ∗
       vecU8Payload A u32 u40 uc.ek ∗
       vecU8Payload A u56 u64 uc.ct1 ∗
       v1_optProtoAuthHeap A uc.auth u80 u88 u96 u104 u112 u120) by
      unfold v8_ucWordsAt; ac_rfl)) ?_
    exact sepConj_mono_right (Entails.pure_right ⟨hu8, hu24, hu32, hu48, hu56, hu72, rfl⟩ (Entails.refl _))

/-! ## 2. PB-to-Stack Copy (`+1764..+1872`) -/

theorem v8_memRegion_2304_split_1392_184_728 (fsp : BitVec 64) :
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
      (∃∗ q10 : BitVec 128, (fsp + 1552#64) ↦₁₂₈ q10) ∗
      (∃∗ w11 : BitVec 64, (fsp + 1568#64) ↦₆₄ w11) ∗
      memRegion (fsp + 1576#64) 728 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem64_entails _) <|
    Entails.refl _

theorem v8_merge_1392_128_1520 (fsp : BitVec 64) :
    memRegion fsp 1392 ∗ memRegion (fsp + 1392#64) 128 ⊢ memRegion fsp 1520 :=
  collapse_top <| collapse_step0 (Entails.refl _) <| Entails.refl _

theorem v8_pbA_144_realign_rest (pbA w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗
      ((pbA + 160#64) ↦₆₄ w24) ∗ Rest =
    ((pbA + 144#64) ↦₈ loByte w8) ∗
      ((pbA + 145#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
      ((pbA + 153#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((pbA + 161#64) ↦ₛ hiBytes7 w24) ∗ Rest := by
  have h := v10_triple64_eq_byte_q128_tail7 (pbA + 144#64) w8 w16 w24
  unfold pointsTo128 at h
  have ha152 : (pbA + 144#64) + 8#64 = pbA + 152#64 := by bv_omega
  have ha160 : (pbA + 144#64) + 16#64 = pbA + 160#64 := by bv_omega
  have ha145 : (pbA + 144#64) + 1#64 = pbA + 145#64 := by bv_omega
  have ha153 : (pbA + 145#64) + 8#64 = pbA + 153#64 := by bv_omega
  have ha161 : (pbA + 144#64) + 17#64 = pbA + 161#64 := by bv_omega
  have hlo : (unshiftWord w16 (loByte w24) ++ unshiftWord w8 (loByte w16)).extractLsb' 0 64 =
      unshiftWord w8 (loByte w16) := by bv_kernel
  have hhi : (unshiftWord w16 (loByte w24) ++ unshiftWord w8 (loByte w16)).extractLsb' 64 64 =
      unshiftWord w16 (loByte w24) := by bv_kernel
  rw [ha152, ha160, ha145, ha153, ha161, hlo, hhi] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v8_pbA_144_unrealign_rest (pbA w8 w16 w24 : BitVec 64) (Rest : SepProp) :
    ((pbA + 144#64) ↦₈ loByte w8) ∗
      ((pbA + 145#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
      ((pbA + 153#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((pbA + 161#64) ↦ₛ hiBytes7 w24) ∗ Rest =
    ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗
      ((pbA + 160#64) ↦₆₄ w24) ∗ Rest :=
  (v8_pbA_144_realign_rest pbA w8 w16 w24 Rest).symm

theorem v8_fsp_1400_split_1_7_rest (fsp w : BitVec 64) (Rest : SepProp) :
    ((fsp + 1400#64) ↦₆₄ w) ∗ Rest =
      ((fsp + 1400#64) ↦₈ loByte w) ∗ ((fsp + 1401#64) ↦ₛ hiBytes7 w) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 1400#64) w
  have ha1 : (fsp + 1400#64) + 1#64 = fsp + 1401#64 := by bv_omega
  rw [ha1] at h
  rw [h, sepConj_assoc]

theorem v8_fsp_1400_unsplit_1_7_rest (fsp w : BitVec 64) (Rest : SepProp) :
    ((fsp + 1400#64) ↦₈ loByte w) ∗ ((fsp + 1401#64) ↦ₛ hiBytes7 w) ∗ Rest =
      ((fsp + 1400#64) ↦₆₄ w) ∗ Rest :=
  (v8_fsp_1400_split_1_7_rest fsp w Rest).symm

theorem v8_fsp_1528_split_1_7_rest (fsp w : BitVec 64) (Rest : SepProp) :
    ((fsp + 1528#64) ↦₆₄ w) ∗ Rest =
      ((fsp + 1528#64) ↦₈ loByte w) ∗ ((fsp + 1529#64) ↦ₛ hiBytes7 w) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 1528#64) w
  have ha1 : (fsp + 1528#64) + 1#64 = fsp + 1529#64 := by bv_omega
  rw [ha1] at h
  rw [h, sepConj_assoc]

theorem v8_fsp_1528_unsplit_1_7_rest (fsp w : BitVec 64) (Rest : SepProp) :
    ((fsp + 1528#64) ↦₈ loByte w) ∗ ((fsp + 1529#64) ↦ₛ hiBytes7 w) ∗ Rest =
      ((fsp + 1528#64) ↦₆₄ w) ∗ Rest :=
  (v8_fsp_1528_split_1_7_rest fsp w Rest).symm

theorem v8_fsp_913_realign_rest (fsp w9 u : BitVec 64) (Rest : SepProp) :
    ((fsp + 913#64) ↦₆₄ w9) ∗ ((fsp + 921#64) ↦ₛ loBytes7 u) ∗ Rest =
      ((fsp + 913#64) ↦ₛ loBytes7 w9) ∗ ((fsp + 920#64) ↦₆₄ overlapWord7 w9 u) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 913#64) w9 u
  have ha8 : (fsp + 913#64) + 8#64 = fsp + 921#64 := by bv_omega
  have ha7 : (fsp + 913#64) + 7#64 = fsp + 920#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v8_fsp_904_realign_rest (fsp w0 w8 w16 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦₈ loByte w0) ∗
      ((fsp + 905#64) ↦₆₄ unshiftWord w0 (loByte w8)) ∗
      ((fsp + 913#64) ↦ₛ loBytes7 (unshiftWord w8 (loByte w16))) ∗
      ((fsp + 920#64) ↦₆₄ w16) ∗ Rest =
    ((fsp + 904#64) ↦₆₄ w0) ∗ ((fsp + 912#64) ↦₆₄ w8) ∗ ((fsp + 920#64) ↦₆₄ w16) ∗ Rest := by
  have hdst := v10_dst24_realign_final (fsp + 904#64) w0 w8 w16
  have hd1 : (fsp + 904#64) + 1#64 = fsp + 905#64 := by bv_omega
  have hd9 : (fsp + 904#64) + 9#64 = fsp + 913#64 := by bv_omega
  have hd16 : (fsp + 904#64) + 16#64 = fsp + 920#64 := by bv_omega
  have hd8 : (fsp + 904#64) + 8#64 = fsp + 912#64 := by bv_omega
  rw [hd1, hd9, hd16, hd8] at hdst
  have h' := congrArg (· ∗ Rest) hdst
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v8_loBytes7_unshiftWord (w : BitVec 64) (b : BitVec 8) :
    loBytes7 (unshiftWord w b) = hiBytes7 w := by
  dsimp only [loBytes7, hiBytes7, unshiftWord, unpack64, List.take, List.drop]
  refine congrArg₂ List.cons (by bv_kernel)
    (congrArg₂ List.cons (by bv_kernel)
      (congrArg₂ List.cons (by bv_kernel)
        (congrArg₂ List.cons (by bv_kernel)
          (congrArg₂ List.cons (by bv_kernel)
            (congrArg₂ List.cons (by bv_kernel)
              (congrArg₂ List.cons (by bv_kernel) rfl))))))

theorem v8_fsp_904_realign_16_rest (fsp w0 w8 w16 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦₈ loByte w0) ∗
      ((fsp + 905#64) ↦₆₄ unshiftWord w0 (loByte w8)) ∗
      ((fsp + 913#64) ↦ₛ loBytes7 (unshiftWord w8 (loByte w16))) ∗ Rest =
    ((fsp + 904#64) ↦₆₄ w0) ∗ ((fsp + 912#64) ↦₆₄ w8) ∗ Rest := by
  rw [v8_loBytes7_unshiftWord]
  have h := (pair64_to_byte_word_tail7 (fsp + 904#64) w0 w8).symm
  have hd8 : (fsp + 904#64) + 8#64 = fsp + 912#64 := by bv_omega
  have hd1 : (fsp + 904#64) + 1#64 = fsp + 905#64 := by bv_omega
  have hd9 : (fsp + 904#64) + 9#64 = fsp + 913#64 := by bv_omega
  rw [hd8, hd1, hd9] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v8_fsp_257_realign_rest (fsp w9 u : BitVec 64) (Rest : SepProp) :
    ((fsp + 257#64) ↦₆₄ w9) ∗ ((fsp + 265#64) ↦ₛ loBytes7 u) ∗ Rest =
      ((fsp + 257#64) ↦ₛ loBytes7 w9) ∗ ((fsp + 264#64) ↦₆₄ overlapWord7 w9 u) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 257#64) w9 u
  have ha8 : (fsp + 257#64) + 8#64 = fsp + 265#64 := by bv_omega
  have ha7 : (fsp + 257#64) + 7#64 = fsp + 264#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v8_fsp_248_realign_rest (fsp w0 w8 w16 : BitVec 64) (Rest : SepProp) :
    ((fsp + 248#64) ↦₈ loByte w0) ∗
      ((fsp + 249#64) ↦₆₄ unshiftWord w0 (loByte w8)) ∗
      ((fsp + 257#64) ↦ₛ loBytes7 (unshiftWord w8 (loByte w16))) ∗
      ((fsp + 264#64) ↦₆₄ w16) ∗ Rest =
    ((fsp + 248#64) ↦₆₄ w0) ∗ ((fsp + 256#64) ↦₆₄ w8) ∗ ((fsp + 264#64) ↦₆₄ w16) ∗ Rest := by
  have hdst := v10_dst24_realign_final (fsp + 248#64) w0 w8 w16
  have hd1 : (fsp + 248#64) + 1#64 = fsp + 249#64 := by bv_omega
  have hd9 : (fsp + 248#64) + 9#64 = fsp + 257#64 := by bv_omega
  have hd16 : (fsp + 248#64) + 16#64 = fsp + 264#64 := by bv_omega
  have hd8 : (fsp + 248#64) + 8#64 = fsp + 256#64 := by bv_omega
  rw [hd1, hd9, hd16, hd8] at hdst
  have h' := congrArg (· ∗ Rest) hdst
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

@[local arm64_norm, local wp_norm]
theorem v8_pbA_17_add_8 (pbA : BitVec 64) :
    (pbA + 17#64) + 8#64 = pbA + 25#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_pbA_40_add_8 (pbA : BitVec 64) :
    (pbA + 40#64) + 8#64 = pbA + 48#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_pbA_56_add_8 (pbA : BitVec 64) :
    (pbA + 56#64) + 8#64 = pbA + 64#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_pbA_72_add_8 (pbA : BitVec 64) :
    (pbA + 72#64) + 8#64 = pbA + 80#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_pbA_88_add_8 (pbA : BitVec 64) :
    (pbA + 88#64) + 8#64 = pbA + 96#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_pbA_104_add_8 (pbA : BitVec 64) :
    (pbA + 104#64) + 8#64 = pbA + 112#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_pbA_120_add_8 (pbA : BitVec 64) :
    (pbA + 120#64) + 8#64 = pbA + 128#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_pbA_145_add_8 (pbA : BitVec 64) :
    (pbA + 145#64) + 8#64 = pbA + 153#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_pbA_168_add_8 (pbA : BitVec 64) :
    (pbA + 168#64) + 8#64 = pbA + 176#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_848_add_57 (fsp : BitVec 64) :
    (fsp + 848#64) + 57#64 = fsp + 905#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_905_add_8 (fsp : BitVec 64) :
    (fsp + 905#64) + 8#64 = fsp + 913#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_928_add_8 (fsp : BitVec 64) :
    (fsp + 928#64) + 8#64 = fsp + 936#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_944_add_8 (fsp : BitVec 64) :
    (fsp + 944#64) + 8#64 = fsp + 952#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_960_add_8 (fsp : BitVec 64) :
    (fsp + 960#64) + 8#64 = fsp + 968#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_976_add_8 (fsp : BitVec 64) :
    (fsp + 976#64) + 8#64 = fsp + 984#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_992_add_8 (fsp : BitVec 64) :
    (fsp + 992#64) + 8#64 = fsp + 1000#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_1008_add_8 (fsp : BitVec 64) :
    (fsp + 1008#64) + 8#64 = fsp + 1016#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_249_add_8 (fsp : BitVec 64) :
    (fsp + 249#64) + 8#64 = fsp + 257#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_272_add_8 (fsp : BitVec 64) :
    (fsp + 272#64) + 8#64 = fsp + 280#64 := by bv_omega

theorem v8_fsp_904_split_for_stur (fsp z904 z912 z920 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦₆₄ z904) ∗ ((fsp + 912#64) ↦₆₄ z912) ∗
      ((fsp + 920#64) ↦₆₄ z920) ∗ Rest =
    ((fsp + 904#64) ↦₈ loByte z904) ∗
      ((fsp + 905#64) ↦₆₄ unshiftWord z904 (loByte z912)) ∗
      ((fsp + 913#64) ↦₆₄ unshiftWord z912 (loByte z920)) ∗
      ((fsp + 921#64) ↦ₛ loBytes7 (unshiftWord z920 0#8)) ∗ Rest := by
  have h := v10_triple64_eq_byte_q128_tail7 (fsp + 904#64) z904 z912 z920
  unfold pointsTo128 at h
  have ha912 : (fsp + 904#64) + 8#64 = fsp + 912#64 := by bv_omega
  have ha920 : (fsp + 904#64) + 16#64 = fsp + 920#64 := by bv_omega
  have ha905 : (fsp + 904#64) + 1#64 = fsp + 905#64 := by bv_omega
  have ha913 : (fsp + 905#64) + 8#64 = fsp + 913#64 := by bv_omega
  have ha921 : (fsp + 904#64) + 17#64 = fsp + 921#64 := by bv_omega
  have hlo : (unshiftWord z912 (loByte z920) ++ unshiftWord z904 (loByte z912)).extractLsb' 0 64 =
      unshiftWord z904 (loByte z912) := by bv_kernel
  have hhi : (unshiftWord z912 (loByte z920) ++ unshiftWord z904 (loByte z912)).extractLsb' 64 64 =
      unshiftWord z912 (loByte z920) := by bv_kernel
  rw [ha912, ha920, ha905, ha913, ha921, hlo, hhi, ← v8_loBytes7_unshiftWord z920 0#8] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v8_memRegion_1392_split_896_128_368 (fsp : BitVec 64) :
    memRegion fsp 1392 ⊢
      memRegion fsp 896 ∗
      (∃∗ z896 : BitVec 64, (fsp + 896#64) ↦₆₄ z896) ∗
      (∃∗ z904 : BitVec 64, (fsp + 904#64) ↦₆₄ z904) ∗
      (∃∗ z912 : BitVec 64, (fsp + 912#64) ↦₆₄ z912) ∗
      (∃∗ z920 : BitVec 64, (fsp + 920#64) ↦₆₄ z920) ∗
      (∃∗ z928 : BitVec 64, (fsp + 928#64) ↦₆₄ z928) ∗
      (∃∗ z936 : BitVec 64, (fsp + 936#64) ↦₆₄ z936) ∗
      (∃∗ z944 : BitVec 64, (fsp + 944#64) ↦₆₄ z944) ∗
      (∃∗ z952 : BitVec 64, (fsp + 952#64) ↦₆₄ z952) ∗
      (∃∗ z960 : BitVec 64, (fsp + 960#64) ↦₆₄ z960) ∗
      (∃∗ z968 : BitVec 64, (fsp + 968#64) ↦₆₄ z968) ∗
      (∃∗ z976 : BitVec 64, (fsp + 976#64) ↦₆₄ z976) ∗
      (∃∗ z984 : BitVec 64, (fsp + 984#64) ↦₆₄ z984) ∗
      (∃∗ z992 : BitVec 64, (fsp + 992#64) ↦₆₄ z992) ∗
      (∃∗ z1000 : BitVec 64, (fsp + 1000#64) ↦₆₄ z1000) ∗
      (∃∗ z1008 : BitVec 64, (fsp + 1008#64) ↦₆₄ z1008) ∗
      (∃∗ z1016 : BitVec 64, (fsp + 1016#64) ↦₆₄ z1016) ∗
      memRegion (fsp + 1024#64) 368 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    Entails.refl _

theorem v8_merge_368_ucWords_496 (fsp : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64) :
    memRegion (fsp + 1024#64) 368 ∗
      v8_ucWordsAt (fsp + 1392#64)
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ⊢
      memRegion (fsp + 1024#64) 496 := by
  refine Entails.trans
    (sepConj_mono_right (v8_ucWordsAt_entails_128 (fsp + 1392#64)
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128)) ?_
  have h1392 : fsp + 1392#64 = (fsp + 1024#64) + 368#64 := by bv_omega
  rw [h1392]
  exact collapse_top <| collapse_step0 (Entails.refl _) <| Entails.refl _

end CryptoVerification.SpqrV1.States.FromPb


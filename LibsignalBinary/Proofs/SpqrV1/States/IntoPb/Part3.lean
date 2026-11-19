/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 3: Arm 1 (`States.keysSampled`) and `SendEk` Helpers

**Checked by Lean.**

Defines `SendEk` heap exposure and 28-word output packing helpers for `States.keysSampled` and
`States.ct1Received`, and proves `states_into_pb_keysSampled` for Arm 1 (`States.keysSampled`,
tag `3`, `+896..+1104 -> +1544`).
-/

public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_lit bv_add_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Exposure and Output Helpers for `KeysSampled` and `Ct1Received` -/

theorem unchunkedEkSentCt1Received_expose (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    unchunkedEkSentCt1ReceivedAt A a uc ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗
        ((a + 16#64) ↦₆₄ a2) ∗ ((a + 24#64) ↦₆₄ a3) ∗
        ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
        ((a + 48#64) ↦₆₄ k0) ∗ ((a + 56#64) ↦₆₄ k1) ∗ ((a + 64#64) ↦₆₄ k2) ∗
        ((a + 72#64) ↦₆₄ d0) ∗ ((a + 80#64) ↦₆₄ d1) ∗ ((a + 88#64) ↦₆₄ d2) ∗
        ((a + 96#64) ↦₆₄ uc.epoch) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 uc.auth ∗
        vecU8Heap A k0 k1 k2 uc.dk ∗
        vecU8Heap A d0 d1 d2 uc.ct1 := by
  unfold unchunkedEkSentCt1ReceivedAt
  refine Entails.trans (sepConj_mono (authenticatorAt_expose A a uc.auth)
    (sepConj_mono (vecU8_expose A (a + 48#64) uc.dk)
      (sepConj_mono (vecU8_expose A (a + 72#64) uc.ct1) (Entails.refl _)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro d0
  apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d2
  apply Entails.sepExists_elim; intro k0
  apply Entails.sepExists_elim; intro k1
  apply Entails.sepExists_elim; intro k2
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5
        (Entails.sepExists_right k0 (Entails.sepExists_right k1
          (Entails.sepExists_right k2 (Entails.sepExists_right d0
            (Entails.sepExists_right d1 (Entails.sepExists_right d2 ?_)))))))))))
  exact Entails.of_eq (by ac_rfl)

theorem chunkedCt1Received_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.ct1Received s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        (stA ↦₆₄ 5#64) ∗
        polyEncoderAt A (stA + 8#64) s.sending_ek ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
        ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
        ((stA + 504#64) ↦₆₄ s.uc.epoch) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A k0 k1 k2 s.uc.dk ∗
        vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
        memRegion (stA + 512#64) 416 := by
  dsimp only [chunkedStatesAt, chunkedCt1ReceivedAt]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right (unchunkedEkSentCt1Received_expose A (stA + 8#64 + 400#64) s.uc)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  apply Entails.sepExists_elim; intro k0
  apply Entails.sepExists_elim; intro k1
  apply Entails.sepExists_elim; intro k2
  apply Entails.sepExists_elim; intro d0
  apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d2
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5
        (Entails.sepExists_right k0 (Entails.sepExists_right k1
          (Entails.sepExists_right k2 (Entails.sepExists_right d0
            (Entails.sepExists_right d1 (Entails.sepExists_right d2 ?_)))))))))))
  exact Entails.of_eq (by ac_rfl)

theorem chunkedKeysSampled_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.keysSampled s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        (stA ↦₆₄ 3#64) ∗
        polyEncoderAt A (stA + 8#64) s.sending_hdr ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
        ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
        ((stA + 504#64) ↦₆₄ s.uc.epoch) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A k0 k1 k2 s.uc.ek ∗
        vecU8Heap A d0 d1 d2 s.uc.dk ∗
        memRegion (stA + 512#64) 416 := by
  dsimp only [chunkedStatesAt]
  rw [chunkedKeysSampledAt_eq_ct1ReceivedAt]
  dsimp only [chunkedCt1ReceivedAt, chunkedKeysSampledToCt1Received,
    unchunkedHeaderSentToEkSentCt1Received]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right (unchunkedEkSentCt1Received_expose A (stA + 8#64 + 400#64)
      { epoch := s.uc.epoch, auth := s.uc.auth, dk := s.uc.ek, ct1 := s.uc.dk })))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  apply Entails.sepExists_elim; intro k0
  apply Entails.sepExists_elim; intro k1
  apply Entails.sepExists_elim; intro k2
  apply Entails.sepExists_elim; intro d0
  apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d2
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5
        (Entails.sepExists_right k0 (Entails.sepExists_right k1
          (Entails.sepExists_right k2 (Entails.sepExists_right d0
            (Entails.sepExists_right d1 (Entails.sepExists_right d2 ?_)))))))))))
  exact Entails.of_eq (by ac_rfl)

theorem stA_sendEk_enc_entails_928 (stA tag : BitVec 64)
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 epoch : BitVec 64) :
    (stA ↦₆₄ tag) ∗
    memRegion (stA + 8#64) polyEncoderSize ∗
    ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
    ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
    ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
    ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
    ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
    ((stA + 504#64) ↦₆₄ epoch) ∗
    memRegion (stA + 512#64) 416 ⊢
    memRegion stA chunkedStatesSize := by
  have hc13 :
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
      ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
      ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
      ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
      ((stA + 504#64) ↦₆₄ epoch) ⊢
      memRegion (stA + 408#64) 104 := by
    rw [ProofLib.memRegion_cells (stA + 408#64) 13 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5
          (Entails.sepExists_right k0 (Entails.sepExists_right k1
            (Entails.sepExists_right k2 (Entails.sepExists_right d0
              (Entails.sepExists_right d1 (Entails.sepExists_right d2
                (Entails.sepExists_right epoch (Entails.refl _)))))))))))))
  have h1 : (stA ↦₆₄ tag) ⊢ memRegion stA 8 := Drop.pointsTo64_entails_memRegion stA tag
  have hsplit : memRegion stA chunkedStatesSize =
      memRegion stA 8 ∗
      memRegion (stA + 8#64) polyEncoderSize ∗
      memRegion (stA + 408#64) 104 ∗
      memRegion (stA + 512#64) 416 := by
    change memRegion stA 928 =
      memRegion stA 8 ∗ memRegion (stA + 8#64) 400 ∗
      memRegion (stA + 408#64) 104 ∗ memRegion (stA + 512#64) 416
    rw [ProofLib.memRegion_split' (b := stA) (n := 8) (k := 920)
          (b' := stA + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := stA + 8#64) (n := 400) (k := 520)
          (b' := stA + 408#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := stA + 408#64) (n := 104) (k := 416)
          (b' := stA + 512#64) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  refine Entails.trans (Entails.of_eq (show _ =
    (stA ↦₆₄ tag) ∗
    memRegion (stA + 8#64) polyEncoderSize ∗
    (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
     ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
     ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
     ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
     ((stA + 504#64) ↦₆₄ epoch)) ∗
    memRegion (stA + 512#64) 416 by ac_rfl)) ?_
  exact sepConj_mono h1 (sepConj_mono (Entails.refl _) (sepConj_mono hc13 (Entails.refl _)))

theorem outWords28_entails_ct1Received (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (k0 k1 k2 d0 d1 d2 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (w168 w176 w184 w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000003#64
      k0 k1 k2 d0 d1 d2
      a0 a1 a2 a3 a4 a5 s.uc.epoch
      e0 e1 e2 e3 e4 e5 e6
      w168 w176 w184 w192 w200 w208 w216 ∗
    protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A k0 k1 k2 s.uc.dk ∗
    vecU8Heap A d0 d1 d2 s.uc.ct1 ⊢
    optProtoInnerStateAt A out (States.ct1Received s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendEk.Ct1Received.into_pb,
    Unchunked.SendEk.EkSentCt1Received.into_pb, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedCt1ReceivedAt, optProtoUnchunkedEkSentCt1ReceivedAt,
    protoUnchunkedEkSentCt1ReceivedAt, optProtoPolynomialEncoderAt, Option.map,
    spqrPolyApi, pbToProtoPolyEncoder, protoPolyEncoderToPb,
    optProtoAuthenticatorAt_some_into_pb]
  have hk := vecU8_of_words_heap A (out + 8#64) k0 k1 k2 s.uc.dk
  have hd := vecU8_of_words_heap A (out + 32#64) d0 d1 d2 s.uc.ct1
  have hauth := authenticatorAt_of_words_heap A (out + 56#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  have henc := protoPolynomialEncoder_of_words_heap A (out + 112#64)
    e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk hd hauth henc ⊢
  have hc7 :
      ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
      ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
      ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
      ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 168#64) 56 := by
    rw [ProofLib.memRegion_cells (out + 168#64) 7 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w168 (Entails.sepExists_right w176
      (Entails.sepExists_right w184 (Entails.sepExists_right w192
        (Entails.sepExists_right w200 (Entails.sepExists_right w208
          (Entails.sepExists_right w216 (Entails.refl _)))))))
  unfold outWords28
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 0x8000000000000003#64) ∗
    (((((out + 8#64) ↦₆₄ k0) ∗ ((out + 16#64) ↦₆₄ k1) ∗ ((out + 24#64) ↦₆₄ k2) ∗
       vecU8Heap A k0 k1 k2 s.uc.dk) ∗
      (((out + 32#64) ↦₆₄ d0) ∗ ((out + 40#64) ↦₆₄ d1) ∗ ((out + 48#64) ↦₆₄ d2) ∗
       vecU8Heap A d0 d1 d2 s.uc.ct1) ∗
      (((out + 56#64) ↦₆₄ a0) ∗ ((out + 64#64) ↦₆₄ a1) ∗
       ((out + 72#64) ↦₆₄ a2) ∗ ((out + 80#64) ↦₆₄ a3) ∗
       ((out + 88#64) ↦₆₄ a4) ∗ ((out + 96#64) ↦₆₄ a5) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
      ((out + 104#64) ↦₆₄ s.uc.epoch)) ∗
     (((out + 112#64) ↦₆₄ e0) ∗ ((out + 120#64) ↦₆₄ e1) ∗
      ((out + 128#64) ↦₆₄ e2) ∗ ((out + 136#64) ↦₆₄ e3) ∗
      ((out + 144#64) ↦₆₄ e4) ∗ ((out + 152#64) ↦₆₄ e5) ∗
      ((out + 160#64) ↦₆₄ e6) ∗
      protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb)) ∗
    (((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
     ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
     ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
     ((out + 216#64) ↦₆₄ w216)) by ac_rfl)) ?_
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono
      (sepConj_mono (sepConj_mono hk (sepConj_mono hd (sepConj_mono hauth (Entails.refl _)))) henc)
      hc7)

theorem outWords28_entails_keysSampled (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (k0 k1 k2 d0 d1 d2 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (w168 w176 w184 w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000001#64
      k0 k1 k2 d0 d1 d2
      a0 a1 a2 a3 a4 a5 s.uc.epoch
      e0 e1 e2 e3 e4 e5 e6
      w168 w176 w184 w192 w200 w208 w216 ∗
    protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_hdr.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A k0 k1 k2 s.uc.ek ∗
    vecU8Heap A d0 d1 d2 s.uc.dk ⊢
    optProtoInnerStateAt A out (States.keysSampled s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendEk.KeysSampled.into_pb,
    Unchunked.SendEk.HeaderSent.into_pb, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedKeysSampledAt, optProtoUnchunkedHeaderSentAt,
    protoUnchunkedHeaderSentAt, optProtoPolynomialEncoderAt, Option.map,
    spqrPolyApi, pbToProtoPolyEncoder, protoPolyEncoderToPb,
    optProtoAuthenticatorAt_some_into_pb]
  have hk := vecU8_of_words_heap A (out + 8#64) k0 k1 k2 s.uc.ek
  have hd := vecU8_of_words_heap A (out + 32#64) d0 d1 d2 s.uc.dk
  have hauth := authenticatorAt_of_words_heap A (out + 56#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  have henc := protoPolynomialEncoder_of_words_heap A (out + 112#64)
    e0 e1 e2 e3 e4 e5 e6 s.sending_hdr.intoPb
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk hd hauth henc ⊢
  have hc7 :
      ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
      ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
      ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
      ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 168#64) 56 := by
    rw [ProofLib.memRegion_cells (out + 168#64) 7 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w168 (Entails.sepExists_right w176
      (Entails.sepExists_right w184 (Entails.sepExists_right w192
        (Entails.sepExists_right w200 (Entails.sepExists_right w208
          (Entails.sepExists_right w216 (Entails.refl _)))))))
  unfold outWords28
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 0x8000000000000001#64) ∗
    (((((out + 8#64) ↦₆₄ k0) ∗ ((out + 16#64) ↦₆₄ k1) ∗ ((out + 24#64) ↦₆₄ k2) ∗
       vecU8Heap A k0 k1 k2 s.uc.ek) ∗
      (((out + 32#64) ↦₆₄ d0) ∗ ((out + 40#64) ↦₆₄ d1) ∗ ((out + 48#64) ↦₆₄ d2) ∗
       vecU8Heap A d0 d1 d2 s.uc.dk) ∗
      (((out + 56#64) ↦₆₄ a0) ∗ ((out + 64#64) ↦₆₄ a1) ∗
       ((out + 72#64) ↦₆₄ a2) ∗ ((out + 80#64) ↦₆₄ a3) ∗
       ((out + 88#64) ↦₆₄ a4) ∗ ((out + 96#64) ↦₆₄ a5) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
      ((out + 104#64) ↦₆₄ s.uc.epoch)) ∗
     (((out + 112#64) ↦₆₄ e0) ∗ ((out + 120#64) ↦₆₄ e1) ∗
      ((out + 128#64) ↦₆₄ e2) ∗ ((out + 136#64) ↦₆₄ e3) ∗
      ((out + 144#64) ↦₆₄ e4) ∗ ((out + 152#64) ↦₆₄ e5) ∗
      ((out + 160#64) ↦₆₄ e6) ∗
      protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_hdr.intoPb)) ∗
    (((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
     ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
     ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
     ((out + 216#64) ↦₆₄ w216)) by ac_rfl)) ?_
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono
      (sepConj_mono (sepConj_mono hk (sepConj_mono hd (sepConj_mono hauth (Entails.refl _)))) henc)
      hc7)

/-! ## 2. Arm 1: `States.keysSampled` (`+0 -> +60 -> +896 -> +1000 -> +1544 -> ret`) -/

end CryptoVerification.SpqrV1.States.IntoPb

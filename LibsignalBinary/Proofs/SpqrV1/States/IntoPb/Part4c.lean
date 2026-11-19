/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 4c: Arm 4 (`States.ekSentCt1Received`)

**Checked by Lean.**

Verifies Arm 4 (`States.ekSentCt1Received`, tag `6`,
`+0 -> +60 -> +140 -> +160 -> +252 -> +1544 -> ret`).
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
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Representation Exposure & Postcondition Entailments for Arm 4 (`EkSentCt1Received`) -/

/-- Expose `chunkedStatesAt A stA (.ekSentCt1Received s)` into tag `6#64`, 12 words
    (`auth`, `dk`, `ct1`) at `stA + 8..stA + 96`, `((stA + 104#64) ↦₆₄ s.uc.epoch) ∗
    polyDecoderAt A (stA + 112#64) s.receiving_ct2`, heap predicates, and trailing padding
    `memRegion (stA + 512#64) 416`. -/
theorem chunkedEkSentCt1Received_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.ekSentCt1Received s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        (stA ↦₆₄ 6#64) ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
         ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
         ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
         ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
         ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
        (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗
         polyDecoderAt A (stA + 112#64) s.receiving_ct2) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A k0 k1 k2 s.uc.dk ∗
        vecU8Heap A d0 d1 d2 s.uc.ct1 ∗
        memRegion (stA + 512#64) 416 := by
  dsimp only [chunkedStatesAt, chunkedEkSentCt1ReceivedAt]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_left (unchunkedEkSentCt1Received_expose A (stA + 8#64) s.uc)))) ?_
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

/-- Recombine `stA` cells after Arm 4 (`ekSentCt1Received`) into `memRegion stA 928`. -/
theorem stA_ekSentCt1Received_entails_928 (stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 : BitVec 64) :
    (stA ↦₆₄ 6#64) ∗
    (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
     ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
     ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
    memRegion (stA + 104#64) 408 ∗
    memRegion (stA + 512#64) 416 ⊢
    memRegion stA chunkedStatesSize := by
  have h104 :
      (stA ↦₆₄ 6#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
       ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
       ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ⊢
      memRegion stA 104 := by
    rw [ProofLib.memRegion_cells stA 13 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right 6#64 (Entails.sepExists_right a0
      (Entails.sepExists_right a1 (Entails.sepExists_right a2
        (Entails.sepExists_right a3 (Entails.sepExists_right a4
          (Entails.sepExists_right a5 (Entails.sepExists_right k0
            (Entails.sepExists_right k1 (Entails.sepExists_right k2
              (Entails.sepExists_right d0 (Entails.sepExists_right d1
                (Entails.sepExists_right d2 ?_))))))))))))
    exact Entails.of_eq (by ac_rfl)
  change _ ⊢ memRegion stA 928
  rw [ProofLib.memRegion_split' (b := stA) (n := 104) (k := 824)
        (b' := stA + 104#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := stA + 104#64) (n := 408) (k := 416)
        (b' := stA + 512#64) rfl (by bv_omega) (by decide)]
  have hgroup :
      (stA ↦₆₄ 6#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
       ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
       ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
      memRegion (stA + 104#64) 408 ∗
      memRegion (stA + 512#64) 416 =
      ((stA ↦₆₄ 6#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
        ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
        ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2))) ∗
      (memRegion (stA + 104#64) 408 ∗ memRegion (stA + 512#64) 416) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono h104 (Entails.refl _)

/-- Assemble `outWords28` for Arm 4 (`ekSentCt1Received`, tag `0x8000000000000004`) into
    `optProtoInnerStateAt A out (States.ekSentCt1Received s).into_pb.innerState`. -/
theorem outWords28_entails_ekSentCt1Received (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (k0 k1 k2 d0 d1 d2 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (dec0 dec1 dec2 dec3 dec4 : BitVec 64)
    (w152 w160 w168 w176 w184 w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000004#64
      k0 k1 k2 d0 d1 d2
      a0 a1 a2 a3 a4 a5 s.uc.epoch
      dec0 dec1 dec2 dec3 dec4
      w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
    protoPolynomialDecoderHeap A dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A k0 k1 k2 s.uc.dk ∗
    vecU8Heap A d0 d1 d2 s.uc.ct1 ⊢
    optProtoInnerStateAt A out (States.ekSentCt1Received s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendEk.EkSentCt1Received.into_pb,
    Unchunked.SendEk.EkSentCt1Received.into_pb, spqrPolyApi, spqrAuthApi,
    optProtoInnerStateAt, protoInnerStateAt, protoChunkedEkSentCt1ReceivedAt,
    optProtoPolynomialDecoderAt, optProtoUnchunkedEkSentCt1ReceivedAt,
    protoUnchunkedEkSentCt1ReceivedAt, Option.map,
    pbToProtoPolyDecoder, protoPolyDecoderToPb,
    optProtoAuthenticatorAt_some_into_pb]
  have hk := vecU8_of_words_heap A (out + 8#64) k0 k1 k2 s.uc.dk
  have hd := vecU8_of_words_heap A (out + 32#64) d0 d1 d2 s.uc.ct1
  have hauth := authenticatorAt_of_words_heap A (out + 56#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  have hdec := protoPolynomialDecoder_of_words_heap A (out + 112#64)
    dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk hd hauth hdec ⊢
  have hpad :
      ((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗
      ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
      ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
      ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
      ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 152#64) 72 := by
    rw [ProofLib.memRegion_cells (out + 152#64) 9 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w152 (Entails.sepExists_right w160
      (Entails.sepExists_right w168 (Entails.sepExists_right w176
        (Entails.sepExists_right w184 (Entails.sepExists_right w192
          (Entails.sepExists_right w200 (Entails.sepExists_right w208
            (Entails.sepExists_right w216 (Entails.refl _)))))))))
  unfold outWords28
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 0x8000000000000004#64) ∗
    (((((out + 8#64) ↦₆₄ k0) ∗ ((out + 16#64) ↦₆₄ k1) ∗ ((out + 24#64) ↦₆₄ k2) ∗
       vecU8Heap A k0 k1 k2 s.uc.dk) ∗
      (((out + 32#64) ↦₆₄ d0) ∗ ((out + 40#64) ↦₆₄ d1) ∗ ((out + 48#64) ↦₆₄ d2) ∗
       vecU8Heap A d0 d1 d2 s.uc.ct1) ∗
      (((out + 56#64) ↦₆₄ a0) ∗ ((out + 64#64) ↦₆₄ a1) ∗
       ((out + 72#64) ↦₆₄ a2) ∗ ((out + 80#64) ↦₆₄ a3) ∗
       ((out + 88#64) ↦₆₄ a4) ∗ ((out + 96#64) ↦₆₄ a5) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
      ((out + 104#64) ↦₆₄ s.uc.epoch)) ∗
     (((out + 112#64) ↦₆₄ dec0) ∗ ((out + 120#64) ↦₆₄ dec1) ∗
      ((out + 128#64) ↦₆₄ dec2) ∗ ((out + 136#64) ↦₆₄ dec3) ∗
      ((out + 144#64) ↦₆₄ dec4) ∗
      protoPolynomialDecoderHeap A dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb)) ∗
    (((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗
     ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
     ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
     ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
     ((out + 216#64) ↦₆₄ w216)) by ac_rfl)) ?_
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono
      (sepConj_mono (sepConj_mono hk (sepConj_mono hd (sepConj_mono hauth (Entails.refl _)))) hdec)
      hpad)

/-! ## 2. Arm 4 Pre-Call and Post-Call Symbolic Execution Steps -/

theorem stack_1416_split_ekSentCt1Received (sp0 : BitVec 64) :
    memRegion (sp0 - 1512#64) 1416 =
      cells (sp0 - 1512#64) 19 ∗
      memRegion (sp0 - 1360#64) 504 ∗
      memRegion (sp0 - 856#64) 376 ∗
      cells (sp0 - 480#64) 13 ∗
      memRegion (sp0 - 376#64) protoPolynomialDecoderSize ∗
      memRegion (sp0 - 336#64) 32 ∗
      cells (sp0 - 304#64) 6 ∗
      cells (sp0 - 256#64) 18 ∗
      memRegion (sp0 - 112#64) 16 := by
  change memRegion (sp0 - 1512#64) 1416 =
    cells (sp0 - 1512#64) 19 ∗
    memRegion (sp0 - 1360#64) 504 ∗
    memRegion (sp0 - 856#64) 376 ∗
    cells (sp0 - 480#64) 13 ∗
    memRegion (sp0 - 376#64) 40 ∗
    memRegion (sp0 - 336#64) 32 ∗
    cells (sp0 - 304#64) 6 ∗
    cells (sp0 - 256#64) 18 ∗
    memRegion (sp0 - 112#64) 16
  rw [ProofLib.memRegion_split' (b := sp0 - 1512#64) (n := 152) (k := 1264)
        (b' := sp0 - 1360#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 1360#64) (n := 504) (k := 760)
        (b' := sp0 - 856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 856#64) (n := 376) (k := 384)
        (b' := sp0 - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 480#64) (n := 104) (k := 280)
        (b' := sp0 - 376#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 376#64) (n := 40) (k := 240)
        (b' := sp0 - 336#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 336#64) (n := 32) (k := 208)
        (b' := sp0 - 304#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 304#64) (n := 48) (k := 160)
        (b' := sp0 - 256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 256#64) (n := 144) (k := 16)
        (b' := sp0 - 112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp0 - 1512#64) 19 (by decide),
      ProofLib.memRegion_cells (sp0 - 480#64) 13 (by decide),
      ProofLib.memRegion_cells (sp0 - 304#64) 6 (by decide),
      ProofLib.memRegion_cells (sp0 - 256#64) 18 (by decide)]

end CryptoVerification.SpqrV1.States.IntoPb

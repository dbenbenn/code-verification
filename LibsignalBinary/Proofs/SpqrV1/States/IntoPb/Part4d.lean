/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 4d: Arm 2 (`States.headerSent`)

**Checked by Lean.**

Verifies Arm 2 (`States.headerSent`, tag `4`,
`+0 -> +60 -> +472 -> +500 -> +592 -> +604 -> +704 -> +1544 -> ret`).
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

/-! ## 1. Representation Exposure & Postcondition Entailments for Arm 2 (`HeaderSent`) -/

/-- Expose `chunkedStatesAt A stA (.headerSent s)` into tag `4#64`, `polyEncoderAt A (stA + 8#64) s.sending_ek`,
    9 words (`a0..a5, k0..k2`) at `stA + 408..stA + 480`, `((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (stA + 488#64) s.receiving_ct1`,
    `authenticatorHeap`, `vecU8Heap`, and trailing padding `memRegion (stA + 888#64) 40`. -/
theorem chunkedHeaderSent_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.headerSent s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
        (stA ↦₆₄ 4#64) ∗
        polyEncoderAt A (stA + 8#64) s.sending_ek ∗
        (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
         ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
         ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
         ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
         ((stA + 472#64) ↦₆₄ k2)) ∗
        (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗
         polyDecoderAt A (stA + 488#64) s.receiving_ct1) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A k0 k1 k2 s.uc.dk ∗
        memRegion (stA + 888#64) 40 := by
  unfold chunkedStatesAt chunkedHeaderSentAt unchunkedEkSentAt
  have ha408 : (stA + 8#64) + 400#64 = stA + 408#64 := by bv_omega
  have ha488 : (stA + 8#64) + 480#64 = stA + 488#64 := by bv_omega
  rw [ha408, ha488]
  have hauth := authenticatorAt_expose A (stA + 408#64) s.uc.auth
  have ha416 : (stA + 408#64) + 8#64 = stA + 416#64 := by bv_omega
  have ha424 : (stA + 408#64) + 16#64 = stA + 424#64 := by bv_omega
  have ha432 : (stA + 408#64) + 24#64 = stA + 432#64 := by bv_omega
  have ha440 : (stA + 408#64) + 32#64 = stA + 440#64 := by bv_omega
  have ha448 : (stA + 408#64) + 40#64 = stA + 448#64 := by bv_omega
  have ha456 : (stA + 408#64) + 48#64 = stA + 456#64 := by bv_omega
  have ha480 : (stA + 408#64) + 72#64 = stA + 480#64 := by bv_omega
  rw [ha416, ha424, ha432, ha440, ha448] at hauth
  rw [ha456, ha480]
  have hdk := vecU8_expose A (stA + 456#64) s.uc.dk
  have hk464 : (stA + 456#64) + 8#64 = stA + 464#64 := by bv_omega
  have hk472 : (stA + 456#64) + 16#64 = stA + 472#64 := by bv_omega
  rw [hk464, hk472] at hdk
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono hauth (sepConj_mono_left hdk)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
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
          (Entails.sepExists_right k2 ?_))))))))
  exact Entails.of_eq (by ac_rfl)

/-- Recombine `stA` cells after Arm 2 (`headerSent`) into `memRegion stA 928`. -/
theorem stA_headerSent_entails_928 (stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 : BitVec 64) :
    (stA ↦₆₄ 4#64) ∗
    memRegion (stA + 8#64) polyEncoderSize ∗
    (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
     ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
     ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
     ((stA + 472#64) ↦₆₄ k2)) ∗
    memRegion (stA + 480#64) 408 ∗
    memRegion (stA + 888#64) 40 ⊢
    memRegion stA chunkedStatesSize := by
  have h8 : (stA ↦₆₄ 4#64) ⊢ memRegion stA 8 := by
    rw [ProofLib.memRegion_cells stA 1 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp]
    exact Entails.sepExists_right 4#64 (Entails.refl _)
  have h72 :
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
       ((stA + 472#64) ↦₆₄ k2)) ⊢
      memRegion (stA + 408#64) 72 := by
    rw [ProofLib.memRegion_cells (stA + 408#64) 9 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5
          (Entails.sepExists_right k0 (Entails.sepExists_right k1
            (Entails.sepExists_right k2 (Entails.refl _)))))))))
  change _ ⊢ memRegion stA 928
  rw [ProofLib.memRegion_split' (b := stA) (n := 8) (k := 920)
        (b' := stA + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := stA + 8#64) (n := 400) (k := 520)
        (b' := stA + 408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := stA + 408#64) (n := 72) (k := 448)
        (b' := stA + 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := stA + 480#64) (n := 408) (k := 40)
        (b' := stA + 888#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h8 (sepConj_mono_right (sepConj_mono_left h72))

/-- Assemble `outWords28` for Arm 2 (`headerSent`, tag `0x8000000000000002`) into
    `optProtoInnerStateAt A out (States.headerSent s).into_pb.innerState`. -/
theorem outWords28_entails_headerSent (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (k0 k1 k2 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (w184 w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000002#64
      k0 k1 k2 a0 a1 a2
      a3 a4 a5 s.uc.epoch e0 e1 e2 e3
      e4 e5 e6 d0 d1 d2 d3 d4
      w184 w192 w200 w208 w216 ∗
    protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
    protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A k0 k1 k2 s.uc.dk ⊢
    optProtoInnerStateAt A out (States.headerSent s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendEk.HeaderSent.into_pb,
    Unchunked.SendEk.EkSent.into_pb, spqrPolyApi, spqrAuthApi,
    optProtoInnerStateAt, protoInnerStateAt, protoChunkedHeaderSentAt,
    optProtoUnchunkedEkSentAt, protoUnchunkedEkSentAt,
    optProtoPolynomialEncoderAt, optProtoPolynomialDecoderAt, Option.map,
    pbToProtoPolyEncoder, protoPolyEncoderToPb,
    pbToProtoPolyDecoder, protoPolyDecoderToPb,
    optProtoAuthenticatorAt_some_into_pb]
  have hdk := vecU8_of_words_heap A (out + 8#64) k0 k1 k2 s.uc.dk
  have hk16 : (out + 8#64) + 8#64 = out + 16#64 := by bv_omega
  have hk24 : (out + 8#64) + 16#64 = out + 24#64 := by bv_omega
  rw [hk16, hk24] at hdk
  have hauth := authenticatorAt_of_words_heap A (out + 32#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  have ha40 : (out + 32#64) + 8#64 = out + 40#64 := by bv_omega
  have ha48 : (out + 32#64) + 16#64 = out + 48#64 := by bv_omega
  have ha56 : (out + 32#64) + 24#64 = out + 56#64 := by bv_omega
  have ha64 : (out + 32#64) + 32#64 = out + 64#64 := by bv_omega
  have ha72 : (out + 32#64) + 40#64 = out + 72#64 := by bv_omega
  rw [ha40, ha48, ha56, ha64, ha72] at hauth
  have henc := protoPolynomialEncoder_of_words_heap A (out + 88#64)
    e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb
  have he96 : (out + 88#64) + 8#64 = out + 96#64 := by bv_omega
  have he104 : (out + 88#64) + 16#64 = out + 104#64 := by bv_omega
  have he112 : (out + 88#64) + 24#64 = out + 112#64 := by bv_omega
  have he120 : (out + 88#64) + 32#64 = out + 120#64 := by bv_omega
  have he128 : (out + 88#64) + 40#64 = out + 128#64 := by bv_omega
  have he136 : (out + 88#64) + 48#64 = out + 136#64 := by bv_omega
  rw [he96, he104, he112, he120, he128, he136] at henc
  have hdec := protoPolynomialDecoder_of_words_heap A (out + 144#64)
    d0 d1 d2 d3 d4 s.receiving_ct1.intoPb
  have hd152 : (out + 144#64) + 8#64 = out + 152#64 := by bv_omega
  have hd160 : (out + 144#64) + 16#64 = out + 160#64 := by bv_omega
  have hd168 : (out + 144#64) + 24#64 = out + 168#64 := by bv_omega
  have hd176 : (out + 144#64) + 32#64 = out + 176#64 := by bv_omega
  rw [hd152, hd160, hd168, hd176] at hdec
  have ho32 : (out + 8#64) + 24#64 = out + 32#64 := by bv_omega
  have ho80 : (out + 8#64) + 72#64 = out + 80#64 := by bv_omega
  have ho88 : (out + 8#64) + 80#64 = out + 88#64 := by bv_omega
  have ho144 : (out + 8#64) + 136#64 = out + 144#64 := by bv_omega
  rw [ho32, ho80, ho88, ho144]
  have h40 :
      ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
      ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
      ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 184#64) 40 := by
    rw [ProofLib.memRegion_cells (out + 184#64) 5 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w184 (Entails.sepExists_right w192
      (Entails.sepExists_right w200 (Entails.sepExists_right w208
        (Entails.sepExists_right w216 (Entails.refl _)))))
  unfold outWords28
  have hgroup :
      ((out ↦₆₄ 0x8000000000000002#64) ∗
       ((out + 8#64) ↦₆₄ k0) ∗ ((out + 16#64) ↦₆₄ k1) ∗
       ((out + 24#64) ↦₆₄ k2) ∗ ((out + 32#64) ↦₆₄ a0) ∗
       ((out + 40#64) ↦₆₄ a1) ∗ ((out + 48#64) ↦₆₄ a2) ∗
       ((out + 56#64) ↦₆₄ a3) ∗ ((out + 64#64) ↦₆₄ a4) ∗
       ((out + 72#64) ↦₆₄ a5) ∗ ((out + 80#64) ↦₆₄ s.uc.epoch) ∗
       ((out + 88#64) ↦₆₄ e0) ∗ ((out + 96#64) ↦₆₄ e1) ∗
       ((out + 104#64) ↦₆₄ e2) ∗ ((out + 112#64) ↦₆₄ e3) ∗
       ((out + 120#64) ↦₆₄ e4) ∗ ((out + 128#64) ↦₆₄ e5) ∗
       ((out + 136#64) ↦₆₄ e6) ∗ ((out + 144#64) ↦₆₄ d0) ∗
       ((out + 152#64) ↦₆₄ d1) ∗ ((out + 160#64) ↦₆₄ d2) ∗
       ((out + 168#64) ↦₆₄ d3) ∗ ((out + 176#64) ↦₆₄ d4) ∗
       ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
       ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
       ((out + 216#64) ↦₆₄ w216)) ∗
      protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
      protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A k0 k1 k2 s.uc.dk =
      (out ↦₆₄ 0x8000000000000002#64) ∗
      (((((out + 8#64) ↦₆₄ k0) ∗ ((out + 16#64) ↦₆₄ k1) ∗
         ((out + 24#64) ↦₆₄ k2) ∗ vecU8Heap A k0 k1 k2 s.uc.dk) ∗
        (((out + 32#64) ↦₆₄ a0) ∗ ((out + 40#64) ↦₆₄ a1) ∗
         ((out + 48#64) ↦₆₄ a2) ∗ ((out + 56#64) ↦₆₄ a3) ∗
         ((out + 64#64) ↦₆₄ a4) ∗ ((out + 72#64) ↦₆₄ a5) ∗
         authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
        ((out + 80#64) ↦₆₄ s.uc.epoch)) ∗
       (((out + 88#64) ↦₆₄ e0) ∗ ((out + 96#64) ↦₆₄ e1) ∗
        ((out + 104#64) ↦₆₄ e2) ∗ ((out + 112#64) ↦₆₄ e3) ∗
        ((out + 120#64) ↦₆₄ e4) ∗ ((out + 128#64) ↦₆₄ e5) ∗
        ((out + 136#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb) ∗
       (((out + 144#64) ↦₆₄ d0) ∗ ((out + 152#64) ↦₆₄ d1) ∗
        ((out + 160#64) ↦₆₄ d2) ∗ ((out + 168#64) ↦₆₄ d3) ∗
        ((out + 176#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb)) ∗
      (((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
       ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
       ((out + 216#64) ↦₆₄ w216)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_right
    (sepConj_mono
      (sepConj_mono
        (sepConj_mono hdk (sepConj_mono_left hauth))
        (sepConj_mono henc hdec))
      h40)

/-! ## 2. Proof of Arm 2: `States.headerSent` (`+0 -> +60 -> +472 -> +500 -> +592 -> +604 -> +1544 -> ret`) -/

/-- Stack split for Arm 2 (`headerSent`): splits `memRegion (sp0 - 1512#64) 1416` into the
    exact regions used across `memcpy`, `<PolyEncoder>::into_pb`, `<PolyDecoder>::into_pb`,
    and the epilogue. -/
theorem stack_1416_split_headerSent (sp0 : BitVec 64) :
    memRegion (sp0 - 1512#64) 1416 =
      cells (sp0 - 1512#64) 19 ∗
      memRegion (sp0 - 1360#64) 880 ∗
      cells (sp0 - 480#64) 10 ∗
      memRegion (sp0 - 400#64) protoPolynomialEncoderSize ∗
      memRegion (sp0 - 344#64) protoPolynomialDecoderSize ∗
      cells (sp0 - 304#64) 6 ∗
      cells (sp0 - 256#64) 9 ∗
      memRegion (sp0 - 184#64) 24 ∗
      cells (sp0 - 160#64) 6 ∗
      memRegion (sp0 - 112#64) 16 := by
  change memRegion (sp0 - 1512#64) 1416 =
    cells (sp0 - 1512#64) 19 ∗
    memRegion (sp0 - 1360#64) 880 ∗
    cells (sp0 - 480#64) 10 ∗
    memRegion (sp0 - 400#64) 56 ∗
    memRegion (sp0 - 344#64) 40 ∗
    cells (sp0 - 304#64) 6 ∗
    cells (sp0 - 256#64) 9 ∗
    memRegion (sp0 - 184#64) 24 ∗
    cells (sp0 - 160#64) 6 ∗
    memRegion (sp0 - 112#64) 16
  rw [ProofLib.memRegion_split' (b := sp0 - 1512#64) (n := 152) (k := 1264)
        (b' := sp0 - 1360#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 1360#64) (n := 880) (k := 384)
        (b' := sp0 - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 480#64) (n := 80) (k := 304)
        (b' := sp0 - 400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 400#64) (n := 56) (k := 248)
        (b' := sp0 - 344#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 344#64) (n := 40) (k := 208)
        (b' := sp0 - 304#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 304#64) (n := 48) (k := 160)
        (b' := sp0 - 256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 256#64) (n := 72) (k := 88)
        (b' := sp0 - 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 184#64) (n := 24) (k := 64)
        (b' := sp0 - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 160#64) (n := 48) (k := 16)
        (b' := sp0 - 112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp0 - 1512#64) 19 (by decide),
      ProofLib.memRegion_cells (sp0 - 480#64) 10 (by decide),
      ProofLib.memRegion_cells (sp0 - 304#64) 6 (by decide),
      ProofLib.memRegion_cells (sp0 - 256#64) 9 (by decide),
      ProofLib.memRegion_cells (sp0 - 160#64) 6 (by decide)]

end CryptoVerification.SpqrV1.States.IntoPb

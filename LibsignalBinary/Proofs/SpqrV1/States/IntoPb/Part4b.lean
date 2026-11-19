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
# `<spqr::v1::chunked::states::States>::into_pb` — Part 4b: Arm 6 (`States.headerReceived`)

**Checked by Lean.**

Verifies Arm 6 (`States.headerReceived`, tag `8`,
`+0 -> +60 -> +1240 -> +1344 -> +1428 -> +1544 -> ret`).
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

/-! ## 1. Representation Exposure & Postcondition Entailments for Arm 6 (`HeaderReceived`) -/

/-- Expose `chunkedStatesAt A stA (.headerReceived s)` into tag `8#64`, 9 words (`a0..a5, h0..h2`)
    at `stA + 8..stA + 80`, `((stA + 80#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (stA + 88#64) s.receiving_ek`,
    `authenticatorHeap`, `vecU8Heap`, and trailing padding `memRegion (stA + 488#64) 440`. -/
theorem chunkedHeaderReceived_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.headerReceived s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ h0 : BitVec 64, ∃∗ h1 : BitVec 64, ∃∗ h2 : BitVec 64,
        (stA ↦₆₄ 8#64) ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
         ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
         ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
         ((stA + 72#64) ↦₆₄ h2)) ∗
        (((stA + 80#64) ↦₆₄ s.uc.epoch) ∗
         polyDecoderAt A (stA + 88#64) s.receiving_ek) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A h0 h1 h2 s.uc.hdr ∗
        memRegion (stA + 488#64) 440 := by
  unfold chunkedStatesAt chunkedHeaderReceivedAt unchunkedHeaderReceivedAt
  have hauth := authenticatorAt_expose A (stA + 8#64) s.uc.auth
  have ha16 : (stA + 8#64) + 8#64 = stA + 16#64 := by bv_omega
  have ha24 : (stA + 8#64) + 16#64 = stA + 24#64 := by bv_omega
  have ha32 : (stA + 8#64) + 24#64 = stA + 32#64 := by bv_omega
  have ha40 : (stA + 8#64) + 32#64 = stA + 40#64 := by bv_omega
  have ha48 : (stA + 8#64) + 40#64 = stA + 48#64 := by bv_omega
  have ha56 : (stA + 8#64) + 48#64 = stA + 56#64 := by bv_omega
  have ha80 : (stA + 8#64) + 72#64 = stA + 80#64 := by bv_omega
  have ha88 : (stA + 8#64) + 80#64 = stA + 88#64 := by bv_omega
  rw [ha16, ha24, ha32, ha40, ha48] at hauth
  rw [ha56, ha80, ha88]
  have hhdr := vecU8_expose A (stA + 56#64) s.uc.hdr
  have hh64 : (stA + 56#64) + 8#64 = stA + 64#64 := by bv_omega
  have hh72 : (stA + 56#64) + 16#64 = stA + 72#64 := by bv_omega
  rw [hh64, hh72] at hhdr
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_left (sepConj_mono hauth (sepConj_mono_left hhdr))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro h0
  apply Entails.sepExists_elim; intro h1
  apply Entails.sepExists_elim; intro h2
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5
        (Entails.sepExists_right h0 (Entails.sepExists_right h1
          (Entails.sepExists_right h2 ?_))))))))
  exact Entails.of_eq (by ac_rfl)

/-- Recombine `stA` cells after Arm 6 (`headerReceived`) into `memRegion stA 928`. -/
theorem stA_headerReceived_entails_928 (stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 h0 h1 h2 : BitVec 64) :
    (stA ↦₆₄ 8#64) ∗
    (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
     ((stA + 72#64) ↦₆₄ h2)) ∗
    memRegion (stA + 80#64) 408 ∗
    memRegion (stA + 488#64) 440 ⊢
    memRegion stA chunkedStatesSize := by
  have h80 :
      (stA ↦₆₄ 8#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
       ((stA + 72#64) ↦₆₄ h2)) ⊢
      memRegion stA 80 := by
    rw [ProofLib.memRegion_cells stA 10 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right 8#64 (Entails.sepExists_right a0
      (Entails.sepExists_right a1 (Entails.sepExists_right a2
        (Entails.sepExists_right a3 (Entails.sepExists_right a4
          (Entails.sepExists_right a5 (Entails.sepExists_right h0
            (Entails.sepExists_right h1 (Entails.sepExists_right h2 ?_)))))))))
    exact Entails.of_eq (by ac_rfl)
  change _ ⊢ memRegion stA 928
  rw [ProofLib.memRegion_split' (b := stA) (n := 80) (k := 848)
        (b' := stA + 80#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := stA + 80#64) (n := 408) (k := 440)
        (b' := stA + 488#64) rfl (by bv_omega) (by decide)]
  have hgroup :
      (stA ↦₆₄ 8#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
       ((stA + 72#64) ↦₆₄ h2)) ∗
      memRegion (stA + 80#64) 408 ∗
      memRegion (stA + 488#64) 440 =
      ((stA ↦₆₄ 8#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
        ((stA + 72#64) ↦₆₄ h2))) ∗
      (memRegion (stA + 80#64) 408 ∗ memRegion (stA + 488#64) 440) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono h80 (Entails.refl _)

/-- Assemble `outWords28` for Arm 6 (`headerReceived`, tag `0x8000000000000006`) into
    `optProtoInnerStateAt A out (States.headerReceived s).into_pb.innerState`. -/
theorem outWords28_entails_headerReceived (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (h0 h1 h2 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000006#64
      h0 h1 h2 a0 a1 a2
      a3 a4 a5 s.uc.epoch d0 d1 d2 d3
      d4 w128 w136 w144 w152 w160 w168 w176
      w184 w192 w200 w208 w216 ∗
    protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A h0 h1 h2 s.uc.hdr ⊢
    optProtoInnerStateAt A out (States.headerReceived s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendCt.HeaderReceived.into_pb,
    Unchunked.SendCt.HeaderReceived.into_pb, spqrPolyApi, spqrAuthApi,
    optProtoInnerStateAt, protoInnerStateAt, protoChunkedHeaderReceivedAt,
    optProtoUnchunkedHeaderReceivedAt, protoUnchunkedHeaderReceivedAt,
    optProtoPolynomialDecoderAt, Option.map,
    pbToProtoPolyDecoder, protoPolyDecoderToPb,
    optProtoAuthenticatorAt_some_into_pb]
  have hhdr := vecU8_of_words_heap A (out + 8#64) h0 h1 h2 s.uc.hdr
  have hh16 : (out + 8#64) + 8#64 = out + 16#64 := by bv_omega
  have hh24 : (out + 8#64) + 16#64 = out + 24#64 := by bv_omega
  rw [hh16, hh24] at hhdr
  have hauth := authenticatorAt_of_words_heap A (out + 32#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  have ha40 : (out + 32#64) + 8#64 = out + 40#64 := by bv_omega
  have ha48 : (out + 32#64) + 16#64 = out + 48#64 := by bv_omega
  have ha56 : (out + 32#64) + 24#64 = out + 56#64 := by bv_omega
  have ha64 : (out + 32#64) + 32#64 = out + 64#64 := by bv_omega
  have ha72 : (out + 32#64) + 40#64 = out + 72#64 := by bv_omega
  rw [ha40, ha48, ha56, ha64, ha72] at hauth
  have hdec := protoPolynomialDecoder_of_words_heap A (out + 88#64) d0 d1 d2 d3 d4 s.receiving_ek.intoPb
  have hd96 : (out + 88#64) + 8#64 = out + 96#64 := by bv_omega
  have hd104 : (out + 88#64) + 16#64 = out + 104#64 := by bv_omega
  have hd112 : (out + 88#64) + 24#64 = out + 112#64 := by bv_omega
  have hd120 : (out + 88#64) + 32#64 = out + 120#64 := by bv_omega
  rw [hd96, hd104, hd112, hd120] at hdec
  have ho32 : (out + 8#64) + 24#64 = out + 32#64 := by bv_omega
  have ho80 : (out + 8#64) + 72#64 = out + 80#64 := by bv_omega
  have ho88 : (out + 8#64) + 80#64 = out + 88#64 := by bv_omega
  rw [ho32, ho80, ho88]
  have h96 :
      ((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗
      ((out + 144#64) ↦₆₄ w144) ∗ ((out + 152#64) ↦₆₄ w152) ∗
      ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗
      ((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
      ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
      ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 128#64) 96 := by
    rw [ProofLib.memRegion_cells (out + 128#64) 12 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w128 (Entails.sepExists_right w136
      (Entails.sepExists_right w144 (Entails.sepExists_right w152
        (Entails.sepExists_right w160 (Entails.sepExists_right w168
          (Entails.sepExists_right w176 (Entails.sepExists_right w184
            (Entails.sepExists_right w192 (Entails.sepExists_right w200
              (Entails.sepExists_right w208 (Entails.sepExists_right w216
                (Entails.refl _))))))))))))
  unfold outWords28
  have hgroup :
      ((out ↦₆₄ 0x8000000000000006#64) ∗
       ((out + 8#64) ↦₆₄ h0) ∗ ((out + 16#64) ↦₆₄ h1) ∗
       ((out + 24#64) ↦₆₄ h2) ∗ ((out + 32#64) ↦₆₄ a0) ∗
       ((out + 40#64) ↦₆₄ a1) ∗ ((out + 48#64) ↦₆₄ a2) ∗
       ((out + 56#64) ↦₆₄ a3) ∗ ((out + 64#64) ↦₆₄ a4) ∗
       ((out + 72#64) ↦₆₄ a5) ∗ ((out + 80#64) ↦₆₄ s.uc.epoch) ∗
       ((out + 88#64) ↦₆₄ d0) ∗ ((out + 96#64) ↦₆₄ d1) ∗
       ((out + 104#64) ↦₆₄ d2) ∗ ((out + 112#64) ↦₆₄ d3) ∗
       ((out + 120#64) ↦₆₄ d4) ∗ ((out + 128#64) ↦₆₄ w128) ∗
       ((out + 136#64) ↦₆₄ w136) ∗ ((out + 144#64) ↦₆₄ w144) ∗
       ((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗
       ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
       ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
       ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
       ((out + 216#64) ↦₆₄ w216)) ∗
      protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A h0 h1 h2 s.uc.hdr =
      (out ↦₆₄ 0x8000000000000006#64) ∗
      (((((out + 8#64) ↦₆₄ h0) ∗ ((out + 16#64) ↦₆₄ h1) ∗
         ((out + 24#64) ↦₆₄ h2) ∗ vecU8Heap A h0 h1 h2 s.uc.hdr) ∗
        (((out + 32#64) ↦₆₄ a0) ∗ ((out + 40#64) ↦₆₄ a1) ∗
         ((out + 48#64) ↦₆₄ a2) ∗ ((out + 56#64) ↦₆₄ a3) ∗
         ((out + 64#64) ↦₆₄ a4) ∗ ((out + 72#64) ↦₆₄ a5) ∗
         authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
        ((out + 80#64) ↦₆₄ s.uc.epoch)) ∗
       (((out + 88#64) ↦₆₄ d0) ∗ ((out + 96#64) ↦₆₄ d1) ∗
        ((out + 104#64) ↦₆₄ d2) ∗ ((out + 112#64) ↦₆₄ d3) ∗
        ((out + 120#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb)) ∗
      (((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗
       ((out + 144#64) ↦₆₄ w144) ∗ ((out + 152#64) ↦₆₄ w152) ∗
       ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗
       ((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
       ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
       ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_right
    (sepConj_mono
      (sepConj_mono (sepConj_mono hhdr (sepConj_mono_left hauth)) hdec)
      h96)

/-! ## 2. Proof of Arm 6: `States.headerReceived` (`+0 -> +60 -> +1240 -> +1344 -> +1428 -> +1544 -> ret`) -/

theorem stack_1416_split_headerReceived (sp0 : BitVec 64) :
    memRegion (sp0 - 1512#64) 1416 =
      cells (sp0 - 1512#64) 19 ∗
      memRegion (sp0 - 1360#64) 480 ∗
      memRegion (sp0 - 880#64) 400 ∗
      cells (sp0 - 480#64) 10 ∗
      memRegion (sp0 - 400#64) protoPolynomialDecoderSize ∗
      memRegion (sp0 - 360#64) 56 ∗
      cells (sp0 - 304#64) 6 ∗
      cells (sp0 - 256#64) 9 ∗
      memRegion (sp0 - 184#64) 24 ∗
      cells (sp0 - 160#64) 6 ∗
      memRegion (sp0 - 112#64) 16 := by
  change memRegion (sp0 - 1512#64) 1416 =
    cells (sp0 - 1512#64) 19 ∗
    memRegion (sp0 - 1360#64) 480 ∗
    memRegion (sp0 - 880#64) 400 ∗
    cells (sp0 - 480#64) 10 ∗
    memRegion (sp0 - 400#64) 40 ∗
    memRegion (sp0 - 360#64) 56 ∗
    cells (sp0 - 304#64) 6 ∗
    cells (sp0 - 256#64) 9 ∗
    memRegion (sp0 - 184#64) 24 ∗
    cells (sp0 - 160#64) 6 ∗
    memRegion (sp0 - 112#64) 16
  rw [ProofLib.memRegion_split' (b := sp0 - 1512#64) (n := 152) (k := 1264)
        (b' := sp0 - 1360#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 1360#64) (n := 480) (k := 784)
        (b' := sp0 - 880#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 880#64) (n := 400) (k := 384)
        (b' := sp0 - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 480#64) (n := 80) (k := 304)
        (b' := sp0 - 400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 400#64) (n := 40) (k := 264)
        (b' := sp0 - 360#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 360#64) (n := 56) (k := 208)
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

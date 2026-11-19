/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 2: Arm 10 (`States.ct2Sampled`)

**Checked by Lean.**

Proves `states_into_pb_ct2Sampled` for Arm 10 (`States.ct2Sampled`, tag `12`, `+1432..+1540 -> +1544`)
of `<spqr::v1::chunked::states::States>::into_pb`.
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
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

@[local arm64_norm, local wp_norm]
theorem bv_sub_sub_lit (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## 1. Arm 10: `States.ct2Sampled` (`+0 -> +60 -> +1432 -> +1544 -> ret`) -/

theorem chunkedCt2Sampled_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.ct2Sampled s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
        (stA ↦₆₄ 12#64) ∗
        polyEncoderAt A (stA + 8#64) s.sending_ct2 ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        memRegion (stA + 464#64) 464 := by
  dsimp only [chunkedStatesAt, chunkedCt2SampledAt, unchunkedCt2SentAt]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left (authenticatorAt_expose A (stA + 8#64 + 400#64) s.uc.auth))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
  exact Entails.of_eq (by ac_rfl)

theorem stA_ct2Sampled_entails_928 (stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 epoch : BitVec 64) :
    (stA ↦₆₄ 12#64) ∗
    memRegion (stA + 8#64) polyEncoderSize ∗
    ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
    ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
    ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
    ((stA + 456#64) ↦₆₄ epoch) ∗
    memRegion (stA + 464#64) 464 ⊢
    memRegion stA chunkedStatesSize := by
  have hc7 :
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
      ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
      ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ epoch) ⊢
      memRegion (stA + 408#64) 56 := by
    rw [ProofLib.memRegion_cells (stA + 408#64) 7 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5
          (Entails.sepExists_right epoch (Entails.refl _)))))))
  have h1 : (stA ↦₆₄ 12#64) ⊢ memRegion stA 8 := Drop.pointsTo64_entails_memRegion stA 12#64
  have hsplit : memRegion stA chunkedStatesSize =
      memRegion stA 8 ∗
      memRegion (stA + 8#64) polyEncoderSize ∗
      memRegion (stA + 408#64) 56 ∗
      memRegion (stA + 464#64) 464 := by
    change memRegion stA 928 =
      memRegion stA 8 ∗ memRegion (stA + 8#64) 400 ∗
      memRegion (stA + 408#64) 56 ∗ memRegion (stA + 464#64) 464
    rw [ProofLib.memRegion_split' (b := stA) (n := 8) (k := 920)
          (b' := stA + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := stA + 8#64) (n := 400) (k := 520)
          (b' := stA + 408#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := stA + 408#64) (n := 56) (k := 464)
          (b' := stA + 464#64) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  refine Entails.trans (Entails.of_eq (show _ =
    (stA ↦₆₄ 12#64) ∗
    memRegion (stA + 8#64) polyEncoderSize ∗
    (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
     ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
     ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ epoch)) ∗
    memRegion (stA + 464#64) 464 by ac_rfl)) ?_
  exact sepConj_mono h1 (sepConj_mono (Entails.refl _) (sepConj_mono hc7 (Entails.refl _)))

theorem outWords28_entails_ct2Sampled (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x800000000000000a#64
      e0 e1 e2 e3 e4 e5 e6
      a0 a1 a2 a3 a4 a5 s.uc.epoch
      w120 w128 w136 w144 w152 w160 w168 w176 w184
      w192 w200 w208 w216 ∗
    protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ⊢
    optProtoInnerStateAt A out (States.ct2Sampled s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendCt.Ct2Sampled.into_pb,
    Unchunked.SendCt.Ct2Sent.into_pb, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedCt2SampledAt, optProtoPolynomialEncoderAt, Option.map,
    spqrPolyApi, pbToProtoPolyEncoder, protoPolyEncoderToPb,
    optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt,
    optProtoAuthenticatorAt_some_into_pb]
  have henc := protoPolynomialEncoder_of_words_heap A (out + 8#64)
    e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb
  have hauth := authenticatorAt_of_words_heap A (out + 64#64)
    a0 a1 a2 a3 a4 a5 s.uc.auth
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at henc hauth ⊢
  have hc13 :
      ((out + 120#64) ↦₆₄ w120) ∗ ((out + 128#64) ↦₆₄ w128) ∗
      ((out + 136#64) ↦₆₄ w136) ∗ ((out + 144#64) ↦₆₄ w144) ∗
      ((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗
      ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
      ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
      ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
      ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 120#64) 104 := by
    rw [ProofLib.memRegion_cells (out + 120#64) 13 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w120 (Entails.sepExists_right w128
      (Entails.sepExists_right w136 (Entails.sepExists_right w144
        (Entails.sepExists_right w152 (Entails.sepExists_right w160
          (Entails.sepExists_right w168 (Entails.sepExists_right w176
            (Entails.sepExists_right w184 (Entails.sepExists_right w192
              (Entails.sepExists_right w200 (Entails.sepExists_right w208
                (Entails.sepExists_right w216 (Entails.refl _)))))))))))))
  unfold outWords28
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 0x800000000000000a#64) ∗
    ((((out + 8#64) ↦₆₄ e0) ∗ ((out + 16#64) ↦₆₄ e1) ∗
      ((out + 24#64) ↦₆₄ e2) ∗ ((out + 32#64) ↦₆₄ e3) ∗
      ((out + 40#64) ↦₆₄ e4) ∗ ((out + 48#64) ↦₆₄ e5) ∗
      ((out + 56#64) ↦₆₄ e6) ∗
      protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb) ∗
     ((((out + 64#64) ↦₆₄ a0) ∗ ((out + 72#64) ↦₆₄ a1) ∗
       ((out + 80#64) ↦₆₄ a2) ∗ ((out + 88#64) ↦₆₄ a3) ∗
       ((out + 96#64) ↦₆₄ a4) ∗ ((out + 104#64) ↦₆₄ a5) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
      ((out + 112#64) ↦₆₄ s.uc.epoch))) ∗
    (((out + 120#64) ↦₆₄ w120) ∗ ((out + 128#64) ↦₆₄ w128) ∗
     ((out + 136#64) ↦₆₄ w136) ∗ ((out + 144#64) ↦₆₄ w144) ∗
     ((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗
     ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
     ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
     ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
     ((out + 216#64) ↦₆₄ w216)) by ac_rfl)) ?_
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (sepConj_mono henc (sepConj_mono hauth (Entails.refl _))) hc13)

end CryptoVerification.SpqrV1.States.IntoPb

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5b
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5d: Arm 7 (`States.ct1Sampled`) Step Lemmas

**Checked by Lean.**

Representation exposure, output reassembly, and step lemmas for Arm 7 (`States.ct1Sampled`,
`PolyEncoder` tag `0` or `1`, jump table index `7`,
`+0 -> +60 -> +828 -> +1712 -> +2028 -> +2100 -> +2116 -> +2128 -> +1544 -> ret`).
-/

public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
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

/-! ## 1. Representation Exposure & Reassembly Helpers for Arm 7 (`Ct1Sampled`) -/

/-- The 64-bit discriminant word at `+0` of a `PolyEncoder` (`0#64` for `.points`, `1#64` for `.polys`). -/
@[expose] def polyEncoderTag (enc : PolyEncoder) : BitVec 64 :=
  match enc.s with
  | .points _ => polyEncoderPointsTag
  | .polys _ => polyEncoderPolysTag

/-- Tail of `encoderStateAt A a s` after splitting out `(a ↦₆₄ polyEncoderTag ...)`. -/
@[expose] def encoderStateTailAt (A : RustAlloc) (a : BitVec 64) : EncoderState → SepProp
  | .points pts =>
    ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
      pointListOf A (a + polyEncoderVecsOff) pts
  | .polys polys =>
    ⌜polys.length = NUM_POLYS⌝ ∗ polyListOf A (a + polyEncoderVecsOff) polys

/-- Tail of `polyEncoderAt A a enc` after splitting out `(a ↦₆₄ polyEncoderTag enc)`. -/
@[expose] def polyEncoderTailAt (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) : SepProp :=
  encoderStateTailAt A a enc.s ∗
    ((a + polyEncoderIdxOff) ↦₃₂ enc.idx) ∗
    memRegion (a + polyEncoderPadOff) polyEncoderPadSize

theorem polyEncoderAt_eq_tag_tail (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a enc =
      (a ↦₆₄ polyEncoderTag enc) ∗ polyEncoderTailAt A a enc := by
  unfold polyEncoderAt polyEncoderTailAt polyEncoderTag encoderStateAt encoderStateTailAt
  cases enc.s <;> dsimp only <;> ac_rfl

theorem polyEncoderTag_eq_zero_or_one (enc : PolyEncoder) :
    polyEncoderTag enc = 0#64 ∨ polyEncoderTag enc = 1#64 := by
  unfold polyEncoderTag polyEncoderPointsTag polyEncoderPolysTag
  cases enc.s
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Expose `chunkedStatesAt A stA (.ct1Sampled s)` for Arm 7. -/
theorem chunkedCt1Sampled_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.ct1Sampled s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ hdr0 : BitVec 64, ∃∗ hdr1 : BitVec 64, ∃∗ hdr2 : BitVec 64,
      ∃∗ es0 : BitVec 64, ∃∗ es1 : BitVec 64, ∃∗ es2 : BitVec 64,
      ∃∗ cap_ct1 : BitVec 64, ∃∗ ptr_ct1 : BitVec 64,
        ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
        (stA ↦₆₄ polyEncoderTag s.sending_ct1) ∗
        polyEncoderTailAt A stA s.sending_ct1 ∗
        ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
        ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
        ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
        ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
        ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
        ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
        polyDecoderAt A (stA + 528#64) s.receiving_ek ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
        vecU8Heap A es0 es1 es2 s.uc.es := by
  dsimp only [chunkedStatesAt, chunkedCt1SampledAt]
  rw [polyEncoderAt_eq_tag_tail A stA s.sending_ct1]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (unchunkedCt1Sent_expose_clone A (stA + 400#64) s.uc))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  apply Entails.sepExists_elim; intro hdr0
  apply Entails.sepExists_elim; intro hdr1
  apply Entails.sepExists_elim; intro hdr2
  apply Entails.sepExists_elim; intro es0
  apply Entails.sepExists_elim; intro es1
  apply Entails.sepExists_elim; intro es2
  apply Entails.sepExists_elim; intro cap_ct1
  apply Entails.sepExists_elim; intro ptr_ct1
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5
        (Entails.sepExists_right hdr0 (Entails.sepExists_right hdr1
          (Entails.sepExists_right hdr2 (Entails.sepExists_right es0
            (Entails.sepExists_right es1 (Entails.sepExists_right es2
              (Entails.sepExists_right cap_ct1 (Entails.sepExists_right ptr_ct1 ?_)))))))))))))
  exact Entails.of_eq (by ac_rfl)

/-- Recombine `stA` after Arm 7 (`ct1Sampled`) into `memRegion stA 928`. -/
theorem stA_ct1Sampled_entails_928 (stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 cap_ct1 ptr_ct1 len_ct1 epoch : BitVec 64) :
    memRegion stA polyEncoderSize ∗
    ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
    ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
    ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
    ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
    ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
    ((stA + 512#64) ↦₆₄ len_ct1) ∗ ((stA + 520#64) ↦₆₄ epoch) ∗
    memRegion (stA + 528#64) polyDecoderSize ⊢
    memRegion stA chunkedStatesSize := by
  have hc16 :
      ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
      ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
      ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
      ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
      ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 512#64) ↦₆₄ len_ct1) ∗ ((stA + 520#64) ↦₆₄ epoch) ⊢
      memRegion (stA + 400#64) 128 := by
    rw [ProofLib.memRegion_cells (stA + 400#64) 16 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5
          (Entails.sepExists_right hdr0 (Entails.sepExists_right hdr1
            (Entails.sepExists_right hdr2 (Entails.sepExists_right es0
              (Entails.sepExists_right es1 (Entails.sepExists_right es2
                (Entails.sepExists_right cap_ct1 (Entails.sepExists_right ptr_ct1
                  (Entails.sepExists_right len_ct1 (Entails.sepExists_right epoch
                    (Entails.refl _))))))))))))))))
  have hsplit : memRegion stA chunkedStatesSize =
      memRegion stA polyEncoderSize ∗
      memRegion (stA + 400#64) 128 ∗
      memRegion (stA + 528#64) polyDecoderSize := by
    change memRegion stA 928 =
      memRegion stA 400 ∗ memRegion (stA + 400#64) 128 ∗ memRegion (stA + 528#64) 400
    rw [ProofLib.memRegion_split' (b := stA) (n := 400) (k := 528)
          (b' := stA + 400#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := stA + 400#64) (n := 128) (k := 400)
          (b' := stA + 528#64) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion stA polyEncoderSize ∗
    (((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
     ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
     ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
     ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
     ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 512#64) ↦₆₄ len_ct1) ∗ ((stA + 520#64) ↦₆₄ epoch)) ∗
    memRegion (stA + 528#64) polyDecoderSize by ac_rfl)) ?_
  exact sepConj_mono (Entails.refl _) (sepConj_mono hc16 (Entails.refl _))

/-- Recombine the 5 decoder output words at `sp - 1176..1144` and `memRegion (sp - 1136#64) 656`
    with `ekReceivedScratchCells` into the 3 epilogue scratch regions. -/
theorem ct1SampledScratchCells_entails_memRegions (sp : BitVec 64)
    (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64) :
    ekReceivedScratchCells sp
      t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
      u0 u1 u2 u3 u4 u5
      v0 v1 v2 v3 v4 v5 ∗
    (((sp - 1232#64) ↦₆₄ e0) ∗ ((sp - 1224#64) ↦₆₄ e1) ∗
     ((sp - 1216#64) ↦₆₄ e2) ∗ ((sp - 1208#64) ↦₆₄ e3) ∗
     ((sp - 1200#64) ↦₆₄ e4) ∗ ((sp - 1192#64) ↦₆₄ e5) ∗
     ((sp - 1184#64) ↦₆₄ e6)) ∗
    (((sp - 1176#64) ↦₆₄ d0) ∗ ((sp - 1168#64) ↦₆₄ d1) ∗
     ((sp - 1160#64) ↦₆₄ d2) ∗ ((sp - 1152#64) ↦₆₄ d3) ∗
     ((sp - 1144#64) ↦₆₄ d4)) ∗
    memRegion (sp - 1136#64) 656 ∗
    memRegion (sp - 432#64) 128 ∗
    memRegion (sp - 208#64) 112 ⊢
    memRegion (sp - 1360#64) 880 ∗
    memRegion (sp - 480#64) 176 ∗
    memRegion (sp - 256#64) 160 := by
  have hd40 :
      (((sp - 1176#64) ↦₆₄ d0) ∗ ((sp - 1168#64) ↦₆₄ d1) ∗
       ((sp - 1160#64) ↦₆₄ d2) ∗ ((sp - 1152#64) ↦₆₄ d3) ∗
       ((sp - 1144#64) ↦₆₄ d4)) ∗
      memRegion (sp - 1136#64) 656 ⊢
      memRegion (sp - 1176#64) 696 := by
    rw [ProofLib.memRegion_split' (b := sp - 1176#64) (n := 40) (k := 656)
          (b' := sp - 1136#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (sp - 1176#64) 5 (by decide)]
    refine sepConj_mono_left ?_
    cells_unfold
    exact Entails.sepExists_right d0 (Entails.sepExists_right d1
      (Entails.sepExists_right d2 (Entails.sepExists_right d3
        (Entails.sepExists_right d4 (Entails.refl _)))))
  refine Entails.trans (Entails.of_eq (show _ =
    ekReceivedScratchCells sp
      t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
      u0 u1 u2 u3 u4 u5
      v0 v1 v2 v3 v4 v5 ∗
    (((sp - 1232#64) ↦₆₄ e0) ∗ ((sp - 1224#64) ↦₆₄ e1) ∗
     ((sp - 1216#64) ↦₆₄ e2) ∗ ((sp - 1208#64) ↦₆₄ e3) ∗
     ((sp - 1200#64) ↦₆₄ e4) ∗ ((sp - 1192#64) ↦₆₄ e5) ∗
     ((sp - 1184#64) ↦₆₄ e6)) ∗
    ((((sp - 1176#64) ↦₆₄ d0) ∗ ((sp - 1168#64) ↦₆₄ d1) ∗
      ((sp - 1160#64) ↦₆₄ d2) ∗ ((sp - 1152#64) ↦₆₄ d3) ∗
      ((sp - 1144#64) ↦₆₄ d4)) ∗
     memRegion (sp - 1136#64) 656) ∗
    memRegion (sp - 432#64) 128 ∗
    memRegion (sp - 208#64) 112 by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hd40))) ?_
  exact ekReceivedScratchCells_entails_memRegions sp
    t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    e0 e1 e2 e3 e4 e5 e6

/-- Assemble `optProtoInnerStateAt A out (States.ct1Sampled s).into_pb.innerState` from `outWords28`. -/
theorem outWords28_entails_ct1Sampled (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64)
    (c0 c1 c2 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (s : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      hdr0 hdr1 hdr2 es0 es1 es2
      c0 c1 c2
      a0 a1 a2 a3 a4 a5 s.uc.epoch
      e0 e1 e2 e3 e4 e5 e6
      d0 d1 d2 d3 d4 ∗
    protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
    protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
    vecU8Heap A es0 es1 es2 s.uc.es ∗
    vecU8Heap A c0 c1 c2 s.uc.ct1 ⊢
    optProtoInnerStateAt A out (States.ct1Sampled s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendCt.Ct1Sampled.into_pb,
    Unchunked.SendCt.Ct1Sent.into_pb,
    optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1SampledAt,
    optProtoUnchunkedCt1SentAt, protoUnchunkedCt1SentAt,
    optProtoPolynomialEncoderAt, optProtoPolynomialDecoderAt, Option.map,
    spqrPolyApi, pbToProtoPolyEncoder, protoPolyEncoderToPb,
    pbToProtoPolyDecoder, protoPolyDecoderToPb,
    optProtoAuthenticatorAt_some_into_pb]
  have hhdr := vecU8_of_words_heap A out hdr0 hdr1 hdr2 s.uc.hdr
  have hes := vecU8_of_words_heap A (out + 24#64) es0 es1 es2 s.uc.es
  have hct1 := vecU8_of_words_heap A (out + 48#64) c0 c1 c2 s.uc.ct1
  have hauth := authenticatorAt_of_words_heap A (out + 72#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  have henc := protoPolynomialEncoder_of_words_heap A (out + 128#64)
    e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb
  have hdec := protoPolynomialDecoder_of_words_heap A (out + 184#64)
    d0 d1 d2 d3 d4 s.receiving_ek.intoPb
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr hes hct1 hauth henc hdec ⊢
  unfold outWords28
  refine Entails.trans (Entails.of_eq (show _ =
    (((out ↦₆₄ hdr0) ∗ ((out + 8#64) ↦₆₄ hdr1) ∗ ((out + 16#64) ↦₆₄ hdr2) ∗
      vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr) ∗
     (((out + 24#64) ↦₆₄ es0) ∗ ((out + 32#64) ↦₆₄ es1) ∗ ((out + 40#64) ↦₆₄ es2) ∗
      vecU8Heap A es0 es1 es2 s.uc.es) ∗
     (((out + 48#64) ↦₆₄ c0) ∗ ((out + 56#64) ↦₆₄ c1) ∗ ((out + 64#64) ↦₆₄ c2) ∗
      vecU8Heap A c0 c1 c2 s.uc.ct1) ∗
     (((out + 72#64) ↦₆₄ a0) ∗ ((out + 80#64) ↦₆₄ a1) ∗ ((out + 88#64) ↦₆₄ a2) ∗
      ((out + 96#64) ↦₆₄ a3) ∗ ((out + 104#64) ↦₆₄ a4) ∗ ((out + 112#64) ↦₆₄ a5) ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
     ((out + 120#64) ↦₆₄ s.uc.epoch)) ∗
    (((out + 128#64) ↦₆₄ e0) ∗ ((out + 136#64) ↦₆₄ e1) ∗ ((out + 144#64) ↦₆₄ e2) ∗
     ((out + 152#64) ↦₆₄ e3) ∗ ((out + 160#64) ↦₆₄ e4) ∗ ((out + 168#64) ↦₆₄ e5) ∗
     ((out + 176#64) ↦₆₄ e6) ∗
     protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb) ∗
    (((out + 184#64) ↦₆₄ d0) ∗ ((out + 192#64) ↦₆₄ d1) ∗ ((out + 200#64) ↦₆₄ d2) ∗
     ((out + 208#64) ↦₆₄ d3) ∗ ((out + 216#64) ↦₆₄ d4) ∗
     protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb) by ac_rfl)) ?_
  exact sepConj_mono
    (sepConj_mono hhdr (sepConj_mono hes (sepConj_mono hct1 (sepConj_mono hauth (Entails.refl _)))))
    (sepConj_mono henc hdec)

/-! ## 2. Step Lemmas for Arm 7 (`+60 -> +1712 -> +2028 -> +2100 -> +2116 -> +2128 -> +1544`) -/

end CryptoVerification.SpqrV1.States.IntoPb

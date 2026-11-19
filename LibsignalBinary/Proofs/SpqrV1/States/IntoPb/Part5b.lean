/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5b: Arm 9 (`States.ct1Acknowledged`) Step Lemmas

**Checked by Lean.**

Representation exposure, scratch-cell layout, and step lemmas for Arm 9 (`States.ct1Acknowledged`,
tag `11`, `+0 -> +60 -> +360 -> +376 -> +424 -> +1812 -> +1884 -> +1904 -> +1544 -> ret`).
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

/-! ## 1. Representation Exposure & Scratch Helpers for Arm 9 (`Ct1Acknowledged`) -/

/-- `Relocatable 32` for 4 consecutive 64-bit words starting at `a`. -/
theorem Relocatable.words4 (w0 w1 w2 w3 : BitVec 64) :
    Relocatable 32 (fun a =>
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) := by
  have h := Relocatable.sepConj (off := 24#64) (m := 32) rfl rfl
    (Relocatable.words3 w0 w1 w2) (Relocatable.pointsTo64 w3)
  refine Relocatable.congr rfl (fun a => ?_) h
  ac_rfl

/-- `Relocatable 432` for 4 words `(w0, w1, w2, w3)` followed by `polyDecoderAt A (a + 32#64) dec`. -/
theorem Relocatable.words4_polyDecoderAt (A : RustAlloc)
    (w0 w1 w2 w3 : BitVec 64) (dec : PolyDecoder) :
    Relocatable 432 (fun a =>
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ polyDecoderAt A (a + 32#64) dec) := by
  have h := Relocatable.sepConj (off := 32#64) (m := 432) rfl rfl
    (Relocatable.words4 w0 w1 w2 w3) (Relocatable.of_polyDecoderAt A dec)
  refine Relocatable.congr rfl (fun a => ?_) h
  ac_rfl

/-- Expose `unchunkedCt1SentAt A a st` for cloning `st.ct1` while moving `st.auth`, `st.hdr`, `st.es`. -/
theorem unchunkedCt1Sent_expose_clone (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    unchunkedCt1SentAt A a st ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ hdr0 : BitVec 64, ∃∗ hdr1 : BitVec 64, ∃∗ hdr2 : BitVec 64,
      ∃∗ es0 : BitVec 64, ∃∗ es1 : BitVec 64, ∃∗ es2 : BitVec 64,
      ∃∗ cap_ct1 : BitVec 64, ∃∗ ptr_ct1 : BitVec 64,
        ⌜st.ct1.length < 2 ^ 63⌝ ∗
        (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
        ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
        ((a + 48#64) ↦₆₄ hdr0) ∗ ((a + 56#64) ↦₆₄ hdr1) ∗ ((a + 64#64) ↦₆₄ hdr2) ∗
        ((a + 72#64) ↦₆₄ es0) ∗ ((a + 80#64) ↦₆₄ es1) ∗ ((a + 88#64) ↦₆₄ es2) ∗
        ((a + 96#64) ↦₆₄ cap_ct1) ∗ ((a + 104#64) ↦₆₄ ptr_ct1) ∗
        ((a + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
        ((a + 120#64) ↦₆₄ st.epoch) ∗
        (ptr_ct1 ↦ₛ st.ct1) ∗
        vecU8CloneTail A cap_ct1 ptr_ct1 st.ct1 ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 st.auth ∗
        vecU8Heap A hdr0 hdr1 hdr2 st.hdr ∗
        vecU8Heap A es0 es1 es2 st.es :=
  unchunkedCt1SentEkReceived_expose_clone A a
    { auth := st.auth, es := st.hdr, ek := st.es, ct1 := st.ct1, epoch := st.epoch }

/-- Expose `chunkedStatesAt A stA (.ct1Acknowledged s)` into tag `11#64`,
    the 12 kept words (`auth`, `hdr`, `es`) at `stA + 8..stA + 96`,
    the 432-byte relocated block (`ct1`, `epoch`, `receiving_ek`) at `stA + 104..stA + 536`,
    and trailing padding `memRegion (stA + 536#64) 392`. -/
theorem chunkedCt1Acknowledged_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.ct1Acknowledged s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ hdr0 : BitVec 64, ∃∗ hdr1 : BitVec 64, ∃∗ hdr2 : BitVec 64,
      ∃∗ es0 : BitVec 64, ∃∗ es1 : BitVec 64, ∃∗ es2 : BitVec 64,
      ∃∗ cap_ct1 : BitVec 64, ∃∗ ptr_ct1 : BitVec 64,
        ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
        (stA ↦₆₄ 11#64) ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
         ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
         ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
        (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
         ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
         ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
         polyDecoderAt A (stA + 136#64) s.receiving_ek) ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
        vecU8Heap A es0 es1 es2 s.uc.es ∗
        memRegion (stA + 536#64) 392 := by
  dsimp only [chunkedStatesAt, chunkedCt1AcknowledgedAt]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_left (unchunkedCt1Sent_expose_clone A (stA + 8#64) s.uc)))) ?_
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

/-- Recombine `stA` after Arm 9 (`ct1Acknowledged`) into `memRegion stA 928`. -/
theorem stA_ct1Acknowledged_entails_928 (stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 : BitVec 64) :
    (stA ↦₆₄ 11#64) ∗
    (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
     ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
     ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
    memRegion (stA + 104#64) 432 ∗
    memRegion (stA + 536#64) 392 ⊢
    memRegion stA chunkedStatesSize := by
  have h104 :
      (stA ↦₆₄ 11#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
       ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ⊢
      memRegion stA 104 := by
    rw [ProofLib.memRegion_cells stA 13 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right 11#64 (Entails.sepExists_right a0
      (Entails.sepExists_right a1 (Entails.sepExists_right a2
        (Entails.sepExists_right a3 (Entails.sepExists_right a4
          (Entails.sepExists_right a5 (Entails.sepExists_right hdr0
            (Entails.sepExists_right hdr1 (Entails.sepExists_right hdr2
              (Entails.sepExists_right es0 (Entails.sepExists_right es1
                (Entails.sepExists_right es2 ?_))))))))))))
    exact Entails.of_eq (by ac_rfl)
  change _ ⊢ memRegion stA 928
  rw [ProofLib.memRegion_split' (b := stA) (n := 104) (k := 824)
        (b' := stA + 104#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := stA + 104#64) (n := 432) (k := 392)
        (b' := stA + 536#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    ((stA ↦₆₄ 11#64) ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2))) ∗
    (memRegion (stA + 104#64) 432 ∗ memRegion (stA + 536#64) 392) by ac_rfl)) ?_
  exact sepConj_mono h104 (Entails.refl _)

/-- Scratch cells in `s0.sp - 480..s0.sp - 304` and `s0.sp - 256..s0.sp - 96` used by Arm 9 (`27` words):
    - `u0..u5` (`6` words at `s0.sp - 480..s0.sp - 432`, `[sp, #0x410..#0x440)`)
    - `v0..v8` (`9` words at `s0.sp - 424..s0.sp - 352`, `[sp, #0x448..#0x490)`)
    - `w0..w5` (`6` words at `s0.sp - 256..s0.sp - 208`, `[x29, #-0xa0..#-0x70)`)
    - `y0..y5` (`6` words at `s0.sp - 160..s0.sp - 112`, `[x29, #-0x40..#-0x10)`). -/
@[expose] def ct1AcknowledgedScratchCells (sp : BitVec 64)
    (u0 u1 u2 u3 u4 u5 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 : BitVec 64) : SepProp :=
  ((sp - 480#64) ↦₆₄ u0) ∗ ((sp - 472#64) ↦₆₄ u1) ∗ ((sp - 464#64) ↦₆₄ u2) ∗
  ((sp - 456#64) ↦₆₄ u3) ∗ ((sp - 448#64) ↦₆₄ u4) ∗ ((sp - 440#64) ↦₆₄ u5) ∗
  ((sp - 424#64) ↦₆₄ v0) ∗ ((sp - 416#64) ↦₆₄ v1) ∗ ((sp - 408#64) ↦₆₄ v2) ∗
  ((sp - 400#64) ↦₆₄ v3) ∗ ((sp - 392#64) ↦₆₄ v4) ∗ ((sp - 384#64) ↦₆₄ v5) ∗
  ((sp - 376#64) ↦₆₄ v6) ∗ ((sp - 368#64) ↦₆₄ v7) ∗ ((sp - 360#64) ↦₆₄ v8) ∗
  ((sp - 256#64) ↦₆₄ w0) ∗ ((sp - 248#64) ↦₆₄ w1) ∗ ((sp - 240#64) ↦₆₄ w2) ∗
  ((sp - 232#64) ↦₆₄ w3) ∗ ((sp - 224#64) ↦₆₄ w4) ∗ ((sp - 216#64) ↦₆₄ w5) ∗
  ((sp - 160#64) ↦₆₄ y0) ∗ ((sp - 152#64) ↦₆₄ y1) ∗ ((sp - 144#64) ↦₆₄ y2) ∗
  ((sp - 136#64) ↦₆₄ y3) ∗ ((sp - 128#64) ↦₆₄ y4) ∗ ((sp - 120#64) ↦₆₄ y5)

theorem memRegion_ct1Acknowledged_scratch_split (sp : BitVec 64) :
    memRegion (sp - 1360#64) 880 ∗
    memRegion (sp - 480#64) 176 ∗
    memRegion (sp - 256#64) 160 ⊢
    ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
    ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
    ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
    ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
    ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64, ∃∗ v8 : BitVec 64,
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ∃∗ y0 : BitVec 64, ∃∗ y1 : BitVec 64, ∃∗ y2 : BitVec 64,
    ∃∗ y3 : BitVec 64, ∃∗ y4 : BitVec 64, ∃∗ y5 : BitVec 64,
      ct1AcknowledgedScratchCells sp
        u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
        w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
      memRegion (sp - 1360#64) 528 ∗
      memRegion (sp - 832#64) 352 ∗
      memRegion (sp - 432#64) 8 ∗
      memRegion (sp - 352#64) 40 ∗
      memRegion (sp - 312#64) 8 ∗
      memRegion (sp - 208#64) 48 ∗
      memRegion (sp - 112#64) 16 := by
  have h880 : memRegion (sp - 1360#64) 880 =
      memRegion (sp - 1360#64) 528 ∗ memRegion (sp - 832#64) 352 :=
    ProofLib.memRegion_split' (b := sp - 1360#64) (n := 528) (k := 352)
      (b' := sp - 832#64) rfl (by bv_omega) (by decide)
  have h176 : memRegion (sp - 480#64) 176 =
      cells (sp - 480#64) 6 ∗ memRegion (sp - 432#64) 8 ∗
      cells (sp - 424#64) 9 ∗ memRegion (sp - 352#64) 40 ∗
      memRegion (sp - 312#64) 8 := by
    rw [ProofLib.memRegion_split' (b := sp - 480#64) (n := 48) (k := 128)
          (b' := sp - 432#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 432#64) (n := 8) (k := 120)
          (b' := sp - 424#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 424#64) (n := 72) (k := 48)
          (b' := sp - 352#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 352#64) (n := 40) (k := 8)
          (b' := sp - 312#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (sp - 480#64) 6 (by decide),
        ProofLib.memRegion_cells (sp - 424#64) 9 (by decide)]
  have h160 : memRegion (sp - 256#64) 160 =
      cells (sp - 256#64) 6 ∗ memRegion (sp - 208#64) 48 ∗
      cells (sp - 160#64) 6 ∗ memRegion (sp - 112#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 256#64) (n := 48) (k := 112)
          (b' := sp - 208#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 208#64) (n := 48) (k := 64)
          (b' := sp - 160#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 160#64) (n := 48) (k := 16)
          (b' := sp - 112#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (sp - 256#64) 6 (by decide),
        ProofLib.memRegion_cells (sp - 160#64) 6 (by decide)]
  rw [h880, h176, h160]
  unfold ct1AcknowledgedScratchCells
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  apply Entails.sepExists_elim; intro y0
  apply Entails.sepExists_elim; intro y1
  apply Entails.sepExists_elim; intro y2
  apply Entails.sepExists_elim; intro y3
  apply Entails.sepExists_elim; intro y4
  apply Entails.sepExists_elim; intro y5
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro v0
  apply Entails.sepExists_elim; intro v1
  apply Entails.sepExists_elim; intro v2
  apply Entails.sepExists_elim; intro v3
  apply Entails.sepExists_elim; intro v4
  apply Entails.sepExists_elim; intro v5
  apply Entails.sepExists_elim; intro v6
  apply Entails.sepExists_elim; intro v7
  apply Entails.sepExists_elim; intro v8
  apply Entails.sepExists_elim; intro u0
  apply Entails.sepExists_elim; intro u1
  apply Entails.sepExists_elim; intro u2
  apply Entails.sepExists_elim; intro u3
  apply Entails.sepExists_elim; intro u4
  apply Entails.sepExists_elim; intro u5
  refine Entails.sepExists_right u0 (Entails.sepExists_right u1
    (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5
        (Entails.sepExists_right v0 (Entails.sepExists_right v1
          (Entails.sepExists_right v2 (Entails.sepExists_right v3
            (Entails.sepExists_right v4 (Entails.sepExists_right v5
              (Entails.sepExists_right v6 (Entails.sepExists_right v7
                (Entails.sepExists_right v8 (Entails.sepExists_right w0
                  (Entails.sepExists_right w1 (Entails.sepExists_right w2
                    (Entails.sepExists_right w3 (Entails.sepExists_right w4
                      (Entails.sepExists_right w5 (Entails.sepExists_right y0
                        (Entails.sepExists_right y1 (Entails.sepExists_right y2
                          (Entails.sepExists_right y3 (Entails.sepExists_right y4
                            (Entails.sepExists_right y5 ?_))))))))))))))))))))))))))
  exact Entails.of_eq (by ac_rfl)

theorem ct1AcknowledgedScratchCells_entails_memRegions (sp : BitVec 64)
    (u0 u1 u2 u3 u4 u5 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 : BitVec 64)
    (c0 c1 c2 c3 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64) :
    ct1AcknowledgedScratchCells sp
      u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
      w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
    (((sp - 1264#64) ↦₆₄ c0) ∗ ((sp - 1256#64) ↦₆₄ c1) ∗
     ((sp - 1248#64) ↦₆₄ c2) ∗ ((sp - 1240#64) ↦₆₄ c3)) ∗
    (((sp - 352#64) ↦₆₄ d0) ∗ ((sp - 344#64) ↦₆₄ d1) ∗
     ((sp - 336#64) ↦₆₄ d2) ∗ ((sp - 328#64) ↦₆₄ d3) ∗
     ((sp - 320#64) ↦₆₄ d4)) ∗
    memRegion (sp - 1360#64) 96 ∗
    memRegion (sp - 1232#64) 400 ∗
    memRegion (sp - 832#64) 352 ∗
    memRegion (sp - 432#64) 8 ∗
    memRegion (sp - 312#64) 8 ∗
    memRegion (sp - 208#64) 48 ∗
    memRegion (sp - 112#64) 16 ⊢
    memRegion (sp - 1360#64) 880 ∗
    memRegion (sp - 480#64) 176 ∗
    memRegion (sp - 256#64) 160 := by
  have hc4 :
      ((sp - 1264#64) ↦₆₄ c0) ∗ ((sp - 1256#64) ↦₆₄ c1) ∗
      ((sp - 1248#64) ↦₆₄ c2) ∗ ((sp - 1240#64) ↦₆₄ c3) ⊢
      memRegion (sp - 1264#64) 32 := by
    rw [ProofLib.memRegion_cells (sp - 1264#64) 4 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right c0 (Entails.sepExists_right c1
      (Entails.sepExists_right c2 (Entails.sepExists_right c3 (Entails.of_eq (by ac_rfl)))))
  have hd5 :
      ((sp - 352#64) ↦₆₄ d0) ∗ ((sp - 344#64) ↦₆₄ d1) ∗
      ((sp - 336#64) ↦₆₄ d2) ∗ ((sp - 328#64) ↦₆₄ d3) ∗
      ((sp - 320#64) ↦₆₄ d4) ⊢
      memRegion (sp - 352#64) 40 := by
    rw [ProofLib.memRegion_cells (sp - 352#64) 5 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right d0 (Entails.sepExists_right d1
      (Entails.sepExists_right d2 (Entails.sepExists_right d3
        (Entails.sepExists_right d4 (Entails.of_eq (by ac_rfl))))))
  have hu6 :
      ((sp - 480#64) ↦₆₄ u0) ∗ ((sp - 472#64) ↦₆₄ u1) ∗ ((sp - 464#64) ↦₆₄ u2) ∗
      ((sp - 456#64) ↦₆₄ u3) ∗ ((sp - 448#64) ↦₆₄ u4) ∗ ((sp - 440#64) ↦₆₄ u5) ⊢
      memRegion (sp - 480#64) 48 := by
    rw [ProofLib.memRegion_cells (sp - 480#64) 6 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right u0 (Entails.sepExists_right u1
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
        (Entails.sepExists_right u4 (Entails.sepExists_right u5 (Entails.of_eq (by ac_rfl)))))))
  have hv9 :
      ((sp - 424#64) ↦₆₄ v0) ∗ ((sp - 416#64) ↦₆₄ v1) ∗ ((sp - 408#64) ↦₆₄ v2) ∗
      ((sp - 400#64) ↦₆₄ v3) ∗ ((sp - 392#64) ↦₆₄ v4) ∗ ((sp - 384#64) ↦₆₄ v5) ∗
      ((sp - 376#64) ↦₆₄ v6) ∗ ((sp - 368#64) ↦₆₄ v7) ∗ ((sp - 360#64) ↦₆₄ v8) ⊢
      memRegion (sp - 424#64) 72 := by
    rw [ProofLib.memRegion_cells (sp - 424#64) 9 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1
      (Entails.sepExists_right v2 (Entails.sepExists_right v3
        (Entails.sepExists_right v4 (Entails.sepExists_right v5
          (Entails.sepExists_right v6 (Entails.sepExists_right v7
            (Entails.sepExists_right v8 (Entails.of_eq (by ac_rfl))))))))))
  have hw6 :
      ((sp - 256#64) ↦₆₄ w0) ∗ ((sp - 248#64) ↦₆₄ w1) ∗ ((sp - 240#64) ↦₆₄ w2) ∗
      ((sp - 232#64) ↦₆₄ w3) ∗ ((sp - 224#64) ↦₆₄ w4) ∗ ((sp - 216#64) ↦₆₄ w5) ⊢
      memRegion (sp - 256#64) 48 := by
    rw [ProofLib.memRegion_cells (sp - 256#64) 6 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
        (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.of_eq (by ac_rfl)))))))
  have hy6 :
      ((sp - 160#64) ↦₆₄ y0) ∗ ((sp - 152#64) ↦₆₄ y1) ∗ ((sp - 144#64) ↦₆₄ y2) ∗
      ((sp - 136#64) ↦₆₄ y3) ∗ ((sp - 128#64) ↦₆₄ y4) ∗ ((sp - 120#64) ↦₆₄ y5) ⊢
      memRegion (sp - 160#64) 48 := by
    rw [ProofLib.memRegion_cells (sp - 160#64) 6 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, arm64_norm]
    exact Entails.sepExists_right y0 (Entails.sepExists_right y1
      (Entails.sepExists_right y2 (Entails.sepExists_right y3
        (Entails.sepExists_right y4 (Entails.sepExists_right y5 (Entails.of_eq (by ac_rfl)))))))
  rw [ProofLib.memRegion_split' (b := sp - 1360#64) (n := 96) (k := 784)
        (b' := sp - 1264#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1264#64) (n := 32) (k := 752)
        (b' := sp - 1232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1232#64) (n := 400) (k := 352)
        (b' := sp - 832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 480#64) (n := 48) (k := 128)
        (b' := sp - 432#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 432#64) (n := 8) (k := 120)
        (b' := sp - 424#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 424#64) (n := 72) (k := 48)
        (b' := sp - 352#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 352#64) (n := 40) (k := 8)
        (b' := sp - 312#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 256#64) (n := 48) (k := 112)
        (b' := sp - 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 208#64) (n := 48) (k := 64)
        (b' := sp - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 48) (k := 16)
        (b' := sp - 112#64) rfl (by bv_omega) (by decide)]
  unfold ct1AcknowledgedScratchCells
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp - 1264#64) ↦₆₄ c0) ∗ ((sp - 1256#64) ↦₆₄ c1) ∗
     ((sp - 1248#64) ↦₆₄ c2) ∗ ((sp - 1240#64) ↦₆₄ c3)) ∗
    (((sp - 352#64) ↦₆₄ d0) ∗ ((sp - 344#64) ↦₆₄ d1) ∗
     ((sp - 336#64) ↦₆₄ d2) ∗ ((sp - 328#64) ↦₆₄ d3) ∗
     ((sp - 320#64) ↦₆₄ d4)) ∗
    (((sp - 480#64) ↦₆₄ u0) ∗ ((sp - 472#64) ↦₆₄ u1) ∗ ((sp - 464#64) ↦₆₄ u2) ∗
     ((sp - 456#64) ↦₆₄ u3) ∗ ((sp - 448#64) ↦₆₄ u4) ∗ ((sp - 440#64) ↦₆₄ u5)) ∗
    (((sp - 424#64) ↦₆₄ v0) ∗ ((sp - 416#64) ↦₆₄ v1) ∗ ((sp - 408#64) ↦₆₄ v2) ∗
     ((sp - 400#64) ↦₆₄ v3) ∗ ((sp - 392#64) ↦₆₄ v4) ∗ ((sp - 384#64) ↦₆₄ v5) ∗
     ((sp - 376#64) ↦₆₄ v6) ∗ ((sp - 368#64) ↦₆₄ v7) ∗ ((sp - 360#64) ↦₆₄ v8)) ∗
    (((sp - 256#64) ↦₆₄ w0) ∗ ((sp - 248#64) ↦₆₄ w1) ∗ ((sp - 240#64) ↦₆₄ w2) ∗
     ((sp - 232#64) ↦₆₄ w3) ∗ ((sp - 224#64) ↦₆₄ w4) ∗ ((sp - 216#64) ↦₆₄ w5)) ∗
    (((sp - 160#64) ↦₆₄ y0) ∗ ((sp - 152#64) ↦₆₄ y1) ∗ ((sp - 144#64) ↦₆₄ y2) ∗
     ((sp - 136#64) ↦₆₄ y3) ∗ ((sp - 128#64) ↦₆₄ y4) ∗ ((sp - 120#64) ↦₆₄ y5)) ∗
    (memRegion (sp - 1360#64) 96 ∗
     memRegion (sp - 1232#64) 400 ∗
     memRegion (sp - 832#64) 352 ∗
     memRegion (sp - 432#64) 8 ∗
     memRegion (sp - 312#64) 8 ∗
     memRegion (sp - 208#64) 48 ∗
     memRegion (sp - 112#64) 16) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono hc4 (sepConj_mono hd5 (sepConj_mono hu6
      (sepConj_mono hv9 (sepConj_mono hw6 (sepConj_mono hy6 (Entails.refl _))))))) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Reassemble the 28 output words of `out` for Arm 9 (`States.ct1Acknowledged`) into
    `optProtoInnerStateAt A out (States.ct1Acknowledged s).into_pb.innerState`. -/
theorem outWords28_entails_ct1Acknowledged (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (hdr0 hdr1 hdr2 es0 es1 es2 ct1_0 ct1_1 ct1_2 a0 a1 a2 a3 a4 a5 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (w176 w184 w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000009#64
      hdr0 hdr1 hdr2 es0 es1 es2 ct1_0
      ct1_1 ct1_2 a0 a1 a2 a3 a4 a5
      s.uc.epoch d0 d1 d2 d3 d4 w176 w184
      w192 w200 w208 w216 ∗
    protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr ∗
    vecU8Heap A es0 es1 es2 s.uc.es ∗
    vecU8Heap A ct1_0 ct1_1 ct1_2 s.uc.ct1 ⊢
    optProtoInnerStateAt A out (States.ct1Acknowledged s).into_pb.innerState := by
  have hdec := protoPolynomialDecoder_of_words_heap A (out + 136#64)
    d0 d1 d2 d3 d4 s.receiving_ek.intoPb
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdec
  have hauth := authenticatorAt_of_words_heap A (out + 80#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hauth
  have hhdr := vecU8_of_words_heap A (out + 8#64) hdr0 hdr1 hdr2 s.uc.hdr
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr
  have hes := vecU8_of_words_heap A (out + 32#64) es0 es1 es2 s.uc.es
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hes
  have hct1 := vecU8_of_words_heap A (out + 56#64) ct1_0 ct1_1 ct1_2 s.uc.ct1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hct1
  have h48 :
      ((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
      ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
      ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 176#64) 48 := by
    rw [ProofLib.memRegion_cells (out + 176#64) 6 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w176 (Entails.sepExists_right w184
      (Entails.sepExists_right w192 (Entails.sepExists_right w200
        (Entails.sepExists_right w208 (Entails.sepExists_right w216 (Entails.of_eq (by ac_rfl)))))))
  dsimp only [States.into_pb, Chunked.SendCt.Ct1Acknowledged.into_pb,
    Unchunked.SendCt.Ct1Sent.into_pb,
    optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1AcknowledgedAt,
    optProtoUnchunkedCt1SentAt, protoUnchunkedCt1SentAt,
    optProtoPolynomialDecoderAt, Option.map,
    spqrPolyApi, pbToProtoPolyDecoder, protoPolyDecoderToPb,
    optProtoAuthenticatorAt_some_into_pb]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  unfold outWords28
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 0x8000000000000009#64) ∗
    (((out + 8#64) ↦₆₄ hdr0) ∗ ((out + 16#64) ↦₆₄ hdr1) ∗ ((out + 24#64) ↦₆₄ hdr2) ∗
     vecU8Heap A hdr0 hdr1 hdr2 s.uc.hdr) ∗
    (((out + 32#64) ↦₆₄ es0) ∗ ((out + 40#64) ↦₆₄ es1) ∗ ((out + 48#64) ↦₆₄ es2) ∗
     vecU8Heap A es0 es1 es2 s.uc.es) ∗
    (((out + 56#64) ↦₆₄ ct1_0) ∗ ((out + 64#64) ↦₆₄ ct1_1) ∗ ((out + 72#64) ↦₆₄ ct1_2) ∗
     vecU8Heap A ct1_0 ct1_1 ct1_2 s.uc.ct1) ∗
    (((out + 80#64) ↦₆₄ a0) ∗ ((out + 88#64) ↦₆₄ a1) ∗
     ((out + 96#64) ↦₆₄ a2) ∗ ((out + 104#64) ↦₆₄ a3) ∗
     ((out + 112#64) ↦₆₄ a4) ∗ ((out + 120#64) ↦₆₄ a5) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
    ((out + 128#64) ↦₆₄ s.uc.epoch) ∗
    (((out + 136#64) ↦₆₄ d0) ∗ ((out + 144#64) ↦₆₄ d1) ∗
     ((out + 152#64) ↦₆₄ d2) ∗ ((out + 160#64) ↦₆₄ d3) ∗
     ((out + 168#64) ↦₆₄ d4) ∗
     protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb) ∗
    (((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
     ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
     ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216)) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono hhdr (sepConj_mono hes (sepConj_mono hct1
      (sepConj_mono hauth (sepConj_mono_right (sepConj_mono hdec h48))))))) ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Step Lemmas for Arm 9 (`+60 -> +360 -> +376 -> +424 -> +1812 -> +1884 -> +1904 -> +1544`) -/

end CryptoVerification.SpqrV1.States.IntoPb


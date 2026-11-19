/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedSteps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.noHeaderReceived` Arm, Part 1

**Checked by Lean.** Branch assembly lemmas (`msg.epoch > st.uc.epoch`, `msg.epoch < st.uc.epoch`,
and `msg.epoch = st.uc.epoch ∧ msg.payload ≠ .hdr _`) for `.noHeaderReceived` (`0x55ca8`,
`entry + 2132`).
-/

public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

theorem memRegion_out_960_split_4words (out : BitVec 64) :
    memRegion out v1RecvSize ⊢
      ∃∗ o0 : BitVec 64, ∃∗ o1 : BitVec 64, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
        (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗ ((out + 24#64) ↦₆₄ o3) ∗
        memRegion (out + 32#64) 928 := by
  unfold v1RecvSize
  rw [ProofLib.memRegion_split out 8 952 (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 944) (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 936) (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 928) (b' := out + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out,
      ProofLib.memRegion_eight (out + 8#64),
      ProofLib.memRegion_eight (out + 16#64),
      ProofLib.memRegion_eight (out + 24#64)]
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro o0
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro o1
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro o2
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro o3
  exact Entails.sepExists_right o0 (Entails.sepExists_right o1
    (Entails.sepExists_right o2 (Entails.sepExists_right o3 (Entails.of_eq (by ac_rfl)))))

theorem nhr_err_words_entails_memRegion_480 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      memRegion (a + 32#64) 448 ⊢
    memRegion a 480 := by
  rw [ProofLib.memRegion_split a 8 472 (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 464) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 456) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 448) (b' := a + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion a w0)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (a + 8#64) w1)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (a + 16#64) w2)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (a + 24#64) w3))))

/-! ## Branch Assembly Lemmas -/

@[expose] def writebackAt8984 (s1 : State) (sp1 : SendEkSpills) : Words63 :=
  { b0 := ⟨sp1.b1.w6, sp1.b2.w5, sp1.w61, sp1.b5.w6, sp1.b4.w6,
           sp1.b4.w5, sp1.w62, sp1.b3.w5, sp1.b5.w3, sp1.b5.w0⟩
    b1 := ⟨sp1.b4.w3, sp1.b4.w7, sp1.b4.w1, sp1.b3.w6, sp1.b5.w2,
           sp1.b1.w8, sp1.b1.w9, s1.readReg64 .x9, s1.readReg64 .x26, s1.readReg64 .x23⟩
    b2 := ⟨sp1.b4.w8, sp1.b3.w3, sp1.b4.w4, sp1.b4.w9, sp1.b5.w7,
           sp1.b3.w7, sp1.b4.w0, s1.readReg64 .x1, sp1.b3.w9, s1.readReg64 .x27⟩
    b3 := ⟨sp1.b3.w8, s1.readReg64 .x24, s1.readReg64 .x25, s1.readReg64 .x12, s1.readReg64 .x11,
           s1.readReg64 .x10, s1.readReg64 .x15, s1.readReg64 .x28, s1.readReg64 .x20, s1.readReg64 .x0⟩
    b4 := ⟨s1.readReg64 .x7, s1.readReg64 .x30, sp1.b2.w9, s1.readReg64 .x14, sp1.b5.w1,
           s1.readReg64 .x18, s1.readReg64 .x5, s1.readReg64 .x2, sp1.b2.w6, s1.readReg64 .x4⟩
    b5 := ⟨s1.readReg64 .x6, s1.readReg64 .x22, s1.readReg64 .x13, s1.readReg64 .x17, s1.readReg64 .x3,
           s1.readReg64 .x16, sp1.w60, sp1.b1.w0, sp1.b3.w0, sp1.b1.w7⟩
    q60 := sp1.q3c0
    w62 := sp1.b3.w1 }

theorem writebackWords63_at_8984 (s1 s2 : State) (sp1 : SendEkSpills)
    (h2_x0 : s2.readReg64 .x0 = s1.readReg64 .x0) (h2_x1 : s2.readReg64 .x1 = sp1.b1.w6) (h2_x2 : s2.readReg64 .x2 = sp1.b1.w0)
    (h2_x3 : s2.readReg64 .x3 = s1.readReg64 .x27) (h2_x4 : s2.readReg64 .x4 = s1.readReg64 .x4) (h2_x5 : s2.readReg64 .x5 = sp1.b2.w6)
    (h2_x6 : s2.readReg64 .x6 = s1.readReg64 .x7) (h2_x7 : s2.readReg64 .x7 = s1.readReg64 .x20) (h2_x8 : s2.readReg64 .x8 = sp1.b2.w5)
    (h2_x9 : s2.readReg64 .x9 = s1.readReg64 .x14) (h2_x10 : s2.readReg64 .x10 = s1.readReg64 .x10) (h2_x11 : s2.readReg64 .x11 = s1.readReg64 .x11)
    (h2_x12 : s2.readReg64 .x12 = s1.readReg64 .x12) (h2_x13 : s2.readReg64 .x13 = s1.readReg64 .x13) (h2_x14 : s2.readReg64 .x14 = s1.readReg64 .x17)
    (h2_x15 : s2.readReg64 .x15 = s1.readReg64 .x15) (h2_x16 : s2.readReg64 .x16 = s1.readReg64 .x16) (h2_x17 : s2.readReg64 .x17 = s1.readReg64 .x18)
    (h2_x20 : s2.readReg64 .x20 = sp1.b1.w7) (h2_x21 : s2.readReg64 .x21 = sp1.b2.w9) (h2_x22 : s2.readReg64 .x22 = s1.readReg64 .x22)
    (h2_x23 : s2.readReg64 .x23 = sp1.b1.w8) (h2_x24 : s2.readReg64 .x24 = s1.readReg64 .x24) (h2_x25 : s2.readReg64 .x25 = s1.readReg64 .x25)
    (h2_x26 : s2.readReg64 .x26 = s1.readReg64 .x2) (h2_x27 : s2.readReg64 .x27 = sp1.b1.w9)
    (h2_x28 : s2.readReg64 .x28 = s1.readReg64 .x28) (h2_x30 : s2.readReg64 .x30 = s1.readReg64 .x30) :
    writebackWords63 s2 (nhrSpills8984 s1 sp1) = writebackAt8984 s1 sp1 := by
  dsimp only [writebackWords63, nhrSpills8984, writebackAt8984]
  simp only [
    h2_x0, h2_x1, h2_x2, h2_x3, h2_x4, h2_x5, h2_x6, h2_x7, h2_x8, h2_x9,
    h2_x10, h2_x11, h2_x12, h2_x13, h2_x14, h2_x15, h2_x16, h2_x17, h2_x20,
    h2_x21, h2_x22, h2_x23, h2_x24, h2_x25, h2_x26, h2_x27, h2_x28, h2_x30]

theorem writebackAt8984_nhr_noop (s1 : State) (sp : SendEkSpills) (w : Words57)
    (hw62 : sp.w62 = w.b0.w6)
    (h1_x0 : s1.readReg64 .x0 = w.b3.w9) (h1_x1 : s1.readReg64 .x1 = w.b2.w7) (h1_x2 : s1.readReg64 .x2 = w.b4.w7)
    (h1_x3 : s1.readReg64 .x3 = w.w54) (h1_x4 : s1.readReg64 .x4 = w.b4.w9) (h1_x5 : s1.readReg64 .x5 = w.b4.w6)
    (h1_x6 : s1.readReg64 .x6 = w.w50) (h1_x7 : s1.readReg64 .x7 = w.b4.w0) (h1_x9 : s1.readReg64 .x9 = w.b1.w7)
    (h1_x10 : s1.readReg64 .x10 = w.b3.w5) (h1_x11 : s1.readReg64 .x11 = w.b3.w4) (h1_x12 : s1.readReg64 .x12 = w.b3.w3)
    (h1_x13 : s1.readReg64 .x13 = w.w52) (h1_x14 : s1.readReg64 .x14 = w.b4.w3) (h1_x15 : s1.readReg64 .x15 = w.b3.w6)
    (h1_x16 : s1.readReg64 .x16 = w.w55) (h1_x17 : s1.readReg64 .x17 = w.w53) (h1_x18 : s1.readReg64 .x18 = w.b4.w5)
    (h1_x20 : s1.readReg64 .x20 = w.b3.w8) (h1_x22 : s1.readReg64 .x22 = w.w51) (h1_x23 : s1.readReg64 .x23 = w.b1.w9)
    (h1_x24 : s1.readReg64 .x24 = w.b3.w1) (h1_x25 : s1.readReg64 .x25 = w.b3.w2) (h1_x26 : s1.readReg64 .x26 = w.b1.w8)
    (h1_x27 : s1.readReg64 .x27 = w.b2.w9) (h1_x28 : s1.readReg64 .x28 = w.b3.w7) (h1_x30 : s1.readReg64 .x30 = w.b4.w1) :
    writebackAt8984 s1 (nhrSpills8664 sp w) =
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4
        b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56,
               sp.b1.w0, sp.b3.w0, sp.b1.w7⟩
        q60 := sp.q3c0, w62 := sp.b3.w1 } := by
  dsimp only [writebackAt8984, nhrSpills8664]
  simp only [
    hw62, h1_x0, h1_x1, h1_x2, h1_x3, h1_x4, h1_x5, h1_x6, h1_x7, h1_x9, h1_x10,
    h1_x11, h1_x12, h1_x13, h1_x14, h1_x15, h1_x16, h1_x17, h1_x18, h1_x20,
    h1_x22, h1_x23, h1_x24, h1_x25, h1_x26, h1_x27, h1_x28, h1_x30]

@[expose] def mkWords60_still (w : Words57) (w58 w59 : BitVec 64) : Words60 :=
  { b0 := ⟨noneCap, w.b0.w0, w.b0.w1, w.b0.w2, w.b0.w3, w.b0.w4, w.b0.w5, w.b0.w6, w.b0.w7, w.b0.w8⟩
    b1 := ⟨w.b0.w9, w.b1.w0, w.b1.w1, w.b1.w2, w.b1.w3, w.b1.w4, w.b1.w5, w.b1.w6, w.b1.w7, w.b1.w8⟩
    b2 := ⟨w.b1.w9, w.b2.w0, w.b2.w1, w.b2.w2, w.b2.w3, w.b2.w4, w.b2.w5, w.b2.w6, w.b2.w7, w.b2.w8⟩
    b3 := ⟨w.b2.w9, w.b3.w0, w.b3.w1, w.b3.w2, w.b3.w3, w.b3.w4, w.b3.w5, w.b3.w6, w.b3.w7, w.b3.w8⟩
    b4 := ⟨w.b3.w9, w.b4.w0, w.b4.w1, w.b4.w2, w.b4.w3, w.b4.w4, w.b4.w5, w.b4.w6, w.b4.w7, w.b4.w8⟩
    b5 := ⟨w.b4.w9, w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, w58, w59⟩ }

theorem words60At_mkWords60_still (a : BitVec 64) (w : Words57) (w58 w59 : BitVec 64) :
    (a ↦₆₄ noneCap) ∗ words57At (a + 8#64) w ∗ ((a + 464#64) ↦₆₄ w58) ∗ ((a + 472#64) ↦₆₄ w59) =
      words60At a (mkWords60_still w w58 w59) := by
  dsimp only [words60At, words57At, words10At, mkWords60_still]
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]

@[expose] def writebackStillAt15296 (s1 : State) (sp1 : SendEkSpills) : Words63 :=
  { b0 := ⟨sp1.b1.w6, sp1.b2.w5, sp1.w61, sp1.b5.w6, sp1.b4.w6,
           s1.readReg64 .x20, sp1.w62, sp1.b5.w3, s1.readReg64 .x0, s1.readReg64 .x18⟩
    b1 := ⟨s1.readReg64 .x14, s1.readReg64 .x15, s1.readReg64 .x10, sp1.b5.w2, s1.readReg64 .x2,
           s1.readReg64 .x4, s1.readReg64 .x9, s1.readReg64 .x26, s1.readReg64 .x23, s1.readReg64 .x1⟩
    b2 := ⟨s1.readReg64 .x30, sp1.b3.w3, sp1.b4.w4, sp1.b4.w9, sp1.b5.w7,
           s1.readReg64 .x7, sp1.b4.w0, sp1.b3.w4, sp1.b3.w9, s1.readReg64 .x12⟩
    b3 := ⟨sp1.b3.w8, sp1.b0.w2, sp1.b0.w4, sp1.b0.w9, sp1.b0.w8,
           sp1.b0.w1, sp1.b1.w3, sp1.b1.w5, sp1.b0.w7, sp1.b1.w2⟩
    b4 := ⟨sp1.b0.w6, sp1.b0.w5, s1.readReg64 .x13, sp1.b2.w3, sp1.b5.w1,
           sp1.b2.w4, s1.readReg64 .x21, s1.readReg64 .x11, sp1.b2.w6, sp1.b2.w2⟩
    b5 := ⟨s1.readReg64 .x6, sp1.b2.w1, s1.readReg64 .x5, s1.readReg64 .x17, sp1.b5.w9,
           s1.readReg64 .x27, s1.readReg64 .x16, sp1.b1.w0, sp1.b3.w0, sp1.b1.w7⟩
    q60 := sp1.q3c0
    w62 := sp1.b3.w1 }

theorem writebackAt8984_of_still15296 (s1 s2 : State) (sp1 : SendEkSpills)
    (h2_x0 : s2.readReg64 .x0 = sp1.b1.w2) (h2_x1 : s2.readReg64 .x1 = sp1.b3.w4) (h2_x2 : s2.readReg64 .x2 = s1.readReg64 .x11)
    (h2_x3 : s2.readReg64 .x3 = sp1.b5.w9) (h2_x4 : s2.readReg64 .x4 = sp1.b2.w2) (h2_x5 : s2.readReg64 .x5 = s1.readReg64 .x21)
    (h2_x6 : s2.readReg64 .x6 = s1.readReg64 .x6) (h2_x7 : s2.readReg64 .x7 = sp1.b0.w6) (h2_x8 : s2.readReg64 .x8 = sp1.b5.w2)
    (h2_x9 : s2.readReg64 .x9 = s1.readReg64 .x26) (h2_x10 : s2.readReg64 .x10 = sp1.b0.w1) (h2_x11 : s2.readReg64 .x11 = sp1.b0.w8)
    (h2_x12 : s2.readReg64 .x12 = sp1.b0.w9) (h2_x13 : s2.readReg64 .x13 = s1.readReg64 .x5) (h2_x14 : s2.readReg64 .x14 = sp1.b2.w3)
    (h2_x15 : s2.readReg64 .x15 = sp1.b1.w3) (h2_x16 : s2.readReg64 .x16 = s1.readReg64 .x27) (h2_x17 : s2.readReg64 .x17 = s1.readReg64 .x17)
    (h2_x18 : s2.readReg64 .x18 = sp1.b2.w4) (h2_x20 : s2.readReg64 .x20 = sp1.b0.w7) (h2_x21 : s2.readReg64 .x21 = s1.readReg64 .x21)
    (h2_x22 : s2.readReg64 .x22 = sp1.b2.w1) (h2_x23 : s2.readReg64 .x23 = s1.readReg64 .x1) (h2_x24 : s2.readReg64 .x24 = sp1.b0.w2)
    (h2_x25 : s2.readReg64 .x25 = sp1.b0.w4) (h2_x26 : s2.readReg64 .x26 = s1.readReg64 .x23)
    (h2_x27 : s2.readReg64 .x27 = s1.readReg64 .x12) (h2_x28 : s2.readReg64 .x28 = sp1.b1.w5) (h2_x30 : s2.readReg64 .x30 = sp1.b0.w5) :
    writebackAt8984 s2 (nhrSpillsStill8984 s1 sp1) = writebackStillAt15296 s1 sp1 := by
  dsimp only [writebackAt8984, nhrSpillsStill8984, writebackStillAt15296]
  simp only [
    h2_x0, h2_x1, h2_x2, h2_x3, h2_x4, h2_x5, h2_x6, h2_x7, h2_x8, h2_x9,
    h2_x10, h2_x11, h2_x12, h2_x13, h2_x14, h2_x15, h2_x16, h2_x17, h2_x18,
    h2_x20, h2_x21, h2_x22, h2_x23, h2_x24, h2_x25, h2_x26, h2_x27, h2_x28, h2_x30]

theorem writebackStillAt15296_of_8616 (s1 : State) (sp : SendEkSpills) (w : Words57) (w58 w59 : BitVec 64)
    (h1_x0 : s1.readReg64 .x0 = (mkWords60_still w w58 w59).b0.w9) (h1_x1 : s1.readReg64 .x1 = (mkWords60_still w w58 w59).b2.w0)
    (h1_x2 : s1.readReg64 .x2 = (mkWords60_still w w58 w59).b1.w5) (h1_x4 : s1.readReg64 .x4 = (mkWords60_still w w58 w59).b1.w6)
    (h1_x5 : s1.readReg64 .x5 = (mkWords60_still w w58 w59).b5.w3) (h1_x6 : s1.readReg64 .x6 = (mkWords60_still w w58 w59).b5.w1)
    (h1_x7 : s1.readReg64 .x7 = (mkWords60_still w w58 w59).b2.w6) (h1_x8 : s1.readReg64 .x8 = (mkWords60_still w w58 w59).b5.w5)
    (h1_x9 : s1.readReg64 .x9 = (mkWords60_still w w58 w59).b1.w7) (h1_x10 : s1.readReg64 .x10 = (mkWords60_still w w58 w59).b1.w3)
    (h1_x11 : s1.readReg64 .x11 = (mkWords60_still w w58 w59).b4.w8) (h1_x12 : s1.readReg64 .x12 = (mkWords60_still w w58 w59).b3.w0)
    (h1_x13 : s1.readReg64 .x13 = (mkWords60_still w w58 w59).b4.w3) (h1_x14 : s1.readReg64 .x14 = (mkWords60_still w w58 w59).b1.w1)
    (h1_x15 : s1.readReg64 .x15 = (mkWords60_still w w58 w59).b1.w2) (h1_x16 : s1.readReg64 .x16 = (mkWords60_still w w58 w59).b5.w7)
    (h1_x17 : s1.readReg64 .x17 = (mkWords60_still w w58 w59).b5.w4) (h1_x18 : s1.readReg64 .x18 = (mkWords60_still w w58 w59).b1.w0)
    (h1_x20 : s1.readReg64 .x20 = (mkWords60_still w w58 w59).b0.w6) (h1_x21 : s1.readReg64 .x21 = (mkWords60_still w w58 w59).b4.w7)
    (h1_x22 : s1.readReg64 .x22 = (mkWords60_still w w58 w59).b0.w0) (h1_x23 : s1.readReg64 .x23 = (mkWords60_still w w58 w59).b1.w9)
    (h1_x26 : s1.readReg64 .x26 = (mkWords60_still w w58 w59).b1.w8) (h1_x27 : s1.readReg64 .x27 = (mkWords60_still w w58 w59).b5.w6)
    (h1_x30 : s1.readReg64 .x30 = (mkWords60_still w w58 w59).b2.w1) :
    writebackStillAt15296 s1 (nhrSpills15296 sp (mkWords60_still w w58 w59)) =
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4
        b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56,
               sp.b1.w0, sp.b3.w0, sp.b1.w7⟩
        q60 := sp.q3c0, w62 := sp.b3.w1 } := by
  dsimp only [writebackStillAt15296, nhrSpills15296, mkWords60_still] at *
  simp only [
    h1_x0, h1_x1, h1_x2, h1_x4, h1_x5, h1_x6, h1_x7, h1_x8, h1_x9, h1_x10,
    h1_x11, h1_x12, h1_x13, h1_x14, h1_x15, h1_x16, h1_x17, h1_x18, h1_x20,
    h1_x21, h1_x22, h1_x23, h1_x26, h1_x27, h1_x30]

@[expose] def writebackDoneAt15296 (s1 : State) (sp1 : SendEkSpills) (w58 w59 : BitVec 64) : Words63 :=
  { b0 := ⟨s1.readReg64 .x22, sp1.b1.w6, sp1.b2.w5, sp1.w61, sp1.b5.w6,
           sp1.b4.w6, s1.readReg64 .x20, sp1.w62, sp1.b5.w3, s1.readReg64 .x0⟩
    b1 := ⟨s1.readReg64 .x18, s1.readReg64 .x14, s1.readReg64 .x15, s1.readReg64 .x10, sp1.b5.w2,
           s1.readReg64 .x2, s1.readReg64 .x4, s1.readReg64 .x9, s1.readReg64 .x26, s1.readReg64 .x23⟩
    b2 := ⟨s1.readReg64 .x1, s1.readReg64 .x30, sp1.b3.w3, sp1.b4.w4, sp1.b4.w9,
           sp1.b5.w7, s1.readReg64 .x7, sp1.b4.w0, sp1.b3.w4, sp1.b3.w9⟩
    b3 := ⟨s1.readReg64 .x12, sp1.b3.w8, sp1.b0.w2, sp1.b0.w4, sp1.b0.w9,
           sp1.b0.w8, sp1.b0.w1, sp1.b1.w3, sp1.b1.w5, sp1.b0.w7⟩
    b4 := ⟨sp1.b1.w2, sp1.b0.w6, sp1.b0.w5, s1.readReg64 .x13, sp1.b2.w3,
           sp1.b5.w1, sp1.b2.w4, s1.readReg64 .x21, s1.readReg64 .x11, sp1.b2.w6⟩
    b5 := ⟨sp1.b2.w2, s1.readReg64 .x6, sp1.b2.w1, s1.readReg64 .x5, s1.readReg64 .x17,
           sp1.b5.w9, s1.readReg64 .x27, s1.readReg64 .x16, w58, w59⟩
    q60 := sp1.q3c0
    w62 := sp1.b3.w1 }

theorem writebackAt8984_of_done15296 (s1 s2 : State) (sp1 : SendEkSpills) (w58 w59 : BitVec 64)
    (h2_x0 : s2.readReg64 .x0 = sp1.b0.w7) (h2_x1 : s2.readReg64 .x1 = sp1.b4.w0) (h2_x2 : s2.readReg64 .x2 = s1.readReg64 .x21)
    (h2_x3 : s2.readReg64 .x3 = s1.readReg64 .x17) (h2_x4 : s2.readReg64 .x4 = sp1.b2.w6) (h2_x5 : s2.readReg64 .x5 = sp1.b2.w4)
    (h2_x6 : s2.readReg64 .x6 = sp1.b2.w2) (h2_x7 : s2.readReg64 .x7 = sp1.b1.w2) (h2_x8 : s2.readReg64 .x8 = 8#64)
    (h2_x9 : s2.readReg64 .x9 = s1.readReg64 .x9) (h2_x10 : s2.readReg64 .x10 = sp1.b0.w8) (h2_x11 : s2.readReg64 .x11 = sp1.b0.w9)
    (h2_x12 : s2.readReg64 .x12 = sp1.b0.w4) (h2_x13 : s2.readReg64 .x13 = sp1.b2.w1) (h2_x14 : s2.readReg64 .x14 = s1.readReg64 .x13)
    (h2_x15 : s2.readReg64 .x15 = sp1.b0.w1) (h2_x16 : s2.readReg64 .x16 = sp1.b5.w9) (h2_x17 : s2.readReg64 .x17 = s1.readReg64 .x5)
    (h2_x18 : s2.readReg64 .x18 = sp1.b5.w1) (h2_x20 : s2.readReg64 .x20 = sp1.b1.w5) (h2_x21 : s2.readReg64 .x21 = s1.readReg64 .x22)
    (h2_x22 : s2.readReg64 .x22 = s1.readReg64 .x6) (h2_x23 : s2.readReg64 .x23 = s1.readReg64 .x23) (h2_x24 : s2.readReg64 .x24 = sp1.b3.w8)
    (h2_x25 : s2.readReg64 .x25 = sp1.b0.w2) (h2_x26 : s2.readReg64 .x26 = s1.readReg64 .x26)
    (h2_x27 : s2.readReg64 .x27 = sp1.b3.w9) (h2_x28 : s2.readReg64 .x28 = sp1.b1.w3) (h2_x30 : s2.readReg64 .x30 = sp1.b0.w6) :
    writebackAt8984 s2 (nhrSpillsDone8984 s1 sp1 w58 w59) = writebackDoneAt15296 s1 sp1 w58 w59 := by
  dsimp only [writebackAt8984, nhrSpillsDone8984, writebackDoneAt15296]
  simp only [
    h2_x0, h2_x1, h2_x2, h2_x3, h2_x4, h2_x5, h2_x6, h2_x7, h2_x8, h2_x9,
    h2_x10, h2_x11, h2_x12, h2_x13, h2_x14, h2_x15, h2_x16, h2_x17, h2_x18,
    h2_x20, h2_x21, h2_x22, h2_x23, h2_x24, h2_x25, h2_x26, h2_x27, h2_x28, h2_x30]

theorem writebackDoneAt15296_of_8616 (s1 : State) (sp : SendEkSpills) (w : Words60)
    (h1_x0 : s1.readReg64 .x0 = w.b0.w9) (h1_x1 : s1.readReg64 .x1 = w.b2.w0) (h1_x2 : s1.readReg64 .x2 = w.b1.w5)
    (h1_x4 : s1.readReg64 .x4 = w.b1.w6) (h1_x5 : s1.readReg64 .x5 = w.b5.w3) (h1_x6 : s1.readReg64 .x6 = w.b5.w1)
    (h1_x7 : s1.readReg64 .x7 = w.b2.w6) (h1_x8 : s1.readReg64 .x8 = w.b5.w5) (h1_x9 : s1.readReg64 .x9 = w.b1.w7)
    (h1_x10 : s1.readReg64 .x10 = w.b1.w3) (h1_x11 : s1.readReg64 .x11 = w.b4.w8) (h1_x12 : s1.readReg64 .x12 = w.b3.w0)
    (h1_x13 : s1.readReg64 .x13 = w.b4.w3) (h1_x14 : s1.readReg64 .x14 = w.b1.w1) (h1_x15 : s1.readReg64 .x15 = w.b1.w2)
    (h1_x16 : s1.readReg64 .x16 = w.b5.w7) (h1_x17 : s1.readReg64 .x17 = w.b5.w4) (h1_x18 : s1.readReg64 .x18 = w.b1.w0)
    (h1_x20 : s1.readReg64 .x20 = w.b0.w6) (h1_x21 : s1.readReg64 .x21 = w.b4.w7) (h1_x22 : s1.readReg64 .x22 = w.b0.w0)
    (h1_x23 : s1.readReg64 .x23 = w.b1.w9) (h1_x26 : s1.readReg64 .x26 = w.b1.w8)
    (h1_x27 : s1.readReg64 .x27 = w.b5.w6) (h1_x30 : s1.readReg64 .x30 = w.b2.w1) :
    writebackDoneAt15296 s1 (nhrSpills15296 sp w) w.b5.w8 w.b5.w9 =
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
        q60 := sp.q3c0, w62 := sp.b3.w1 } := by
  dsimp only [writebackDoneAt15296, nhrSpills15296]
  simp only [
    h1_x0, h1_x1, h1_x2, h1_x4, h1_x5, h1_x6, h1_x7, h1_x8, h1_x9, h1_x10,
    h1_x11, h1_x12, h1_x13, h1_x14, h1_x15, h1_x16, h1_x17, h1_x18, h1_x20,
    h1_x21, h1_x22, h1_x23, h1_x26, h1_x27, h1_x30]

theorem words60At_1856_400_entails_memRegion_880 (fsp : BitVec 64) (w : Words60) :
    words60At (fsp + 1856#64) w ∗ memRegion (fsp + 2336#64) 400 ⊢
      memRegion (fsp + 1856#64) 880 := by
  rw [ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 480) (k := 400)
        (b' := fsp + 2336#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (words60At_entails_memRegion (fsp + 1856#64) w)

@[expose] def words8At (a : BitVec 64) (w : Words10) : SepProp :=
  (a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3) ∗
  ((a + 32#64) ↦₆₄ w.w4) ∗ ((a + 40#64) ↦₆₄ w.w5) ∗ ((a + 48#64) ↦₆₄ w.w6) ∗ ((a + 56#64) ↦₆₄ w.w7)

theorem words10At_eq_words8At (a : BitVec 64) (w : Words10) :
    words10At a w = words8At a w ∗ ((a + 64#64) ↦₆₄ w.w8) ∗ ((a + 72#64) ↦₆₄ w.w9) := by
  dsimp only [words10At, words8At]
  simp only [sepConj_assoc]

@[expose] def nhrRest1856At (fsp : BitVec 64) (w : Words60) : SepProp :=
  words10At (fsp + 1856#64) w.b0 ∗
  words10At (fsp + 1936#64) w.b1 ∗
  words10At (fsp + 2016#64) w.b2 ∗
  words10At (fsp + 2096#64) w.b3 ∗
  words10At (fsp + 2176#64) w.b4 ∗
  words8At (fsp + 2256#64) w.b5 ∗
  memRegion (fsp + 2336#64) 400

theorem words60At_1856_400_split (fsp : BitVec 64) (w : Words60) :
    words60At (fsp + 1856#64) w ∗ memRegion (fsp + 2336#64) 400 ⊢
      ((fsp + 2320#64) ↦₆₄ w.b5.w8) ∗ ((fsp + 2328#64) ↦₆₄ w.b5.w9) ∗ nhrRest1856At fsp w := by
  dsimp only [words60At, nhrRest1856At]
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]
  rw [words10At_eq_words8At (fsp + 2256#64) w.b5]
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem nhrRest1856At_rejoin_880 (fsp : BitVec 64) (w : Words60) :
    ((fsp + 2320#64) ↦₆₄ w.b5.w8) ∗ ((fsp + 2328#64) ↦₆₄ w.b5.w9) ∗ nhrRest1856At fsp w ⊢
      memRegion (fsp + 1856#64) 880 := by
  refine Entails.trans (Entails.of_eq (show _ = words60At (fsp + 1856#64) w ∗ memRegion (fsp + 2336#64) 400 by
    dsimp only [words60At, nhrRest1856At]
    simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]
    rw [words10At_eq_words8At (fsp + 2256#64) w.b5]
    simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]
    ac_rfl)) (words60At_1856_400_entails_memRegion_880 fsp w)

theorem byte_memRegion7_extract_word (a : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64,
        ⌜∃ bs : List (BitVec 8), bs.length = 7 ∧ b0 :: bs = unpack64 w⌝ ∗ (a ↦₆₄ w) := by
  rw [memRegion_eq_exists_bytes (a + 1#64) 7 (by decide), sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [← sepConj_assoc, sepConj_comm (a ↦₈ b0), sepConj_assoc]
  apply Entails.pure_left; intro hbs
  obtain ⟨w, hw⟩ := exists_word_of_length_8 (b0 :: bs) (by simp [hbs])
  refine Entails.sepExists_right w (Entails.pure_right ⟨bs, hbs, hw⟩ ?_)
  rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_cons, sepConj_comm]
  exact Entails.refl _

theorem byte_memRegion7_recompose_word (dst : BitVec 64) (b0 : BitVec 8) (w : BitVec 64)
    (hw : ∃ bs : List (BitVec 8), bs.length = 7 ∧ b0 :: bs = unpack64 w) :
    (dst ↦₆₄ w) ⊢ (dst ↦₈ b0) ∗ memRegion (dst + 1#64) 7 := by
  rcases hw with ⟨bs, hbs, hw⟩
  rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_cons, ← hbs]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion (dst + 1#64) bs)

theorem nhr_err_1856_split {A : RustAlloc} {F : ShaCompress} (fsp : BitVec 64) (err : Error) :
    noHeaderReceivedRecvChunkResultAt A (F := F) (fsp + 1856#64) (.error (.err err)) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ⌜∃ bs : List (BitVec 8), bs.length = 7 ∧ spqrErrorByte err :: bs = unpack64 w1⌝ ∗
        ((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
        ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗ memRegion (fsp + 1888#64) 448 := by
  dsimp only [noHeaderReceivedRecvChunkResultAt, none2Cap]
  rw [ProofLib.memRegion_split' (b := (fsp + 1856#64) + 9#64) (n := 7) (k := 464)
        (b' := fsp + 1872#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1872#64) (n := 8) (k := 456)
        (b' := fsp + 1880#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1880#64) (n := 8) (k := 448)
        (b' := fsp + 1888#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 1872#64), ProofLib.memRegion_eight (fsp + 1880#64)]
  have h1864 : (fsp + 1856#64) + 8#64 = fsp + 1864#64 := by bv_omega
  have h1865 : (fsp + 1856#64) + 9#64 = (fsp + 1864#64) + 1#64 := by bv_omega
  rw [h1864, h1865]
  refine Entails.trans (Entails.of_eq (show _ =
    (((fsp + 1864#64) ↦₈ spqrErrorByte err) ∗ memRegion ((fsp + 1864#64) + 1#64) 7) ∗
    ((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
    (∃∗ w2 : BitVec 64, ((fsp + 1872#64) ↦₆₄ w2)) ∗
    (∃∗ w3 : BitVec 64, ((fsp + 1880#64) ↦₆₄ w3)) ∗ memRegion (fsp + 1888#64) 448 by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (byte_memRegion7_extract_word (fsp + 1864#64) (spqrErrorByte err))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3; apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w1
  exact Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.of_eq (by ac_rfl))))

theorem nhr_err_out_recompose (A : RustAlloc) {F : ShaCompress} (outA : BitVec 64) (err : Error)
    (w1 w2 w3 : BitVec 64)
    (hw1 : ∃ bs : List (BitVec 8), bs.length = 7 ∧ spqrErrorByte err :: bs = unpack64 w1) :
    (outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₆₄ w1) ∗ ((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3) ∗
      memRegion (outA + 32#64) 928 ⊢
    resultV1RecvAt A (F := F) outA (.error (.err err)) := by
  dsimp only [resultV1RecvAt]
  have h1 : ((outA + 8#64) ↦₆₄ w1) ⊢ ((outA + 8#64) ↦₈ spqrErrorByte err) ∗ memRegion (outA + 9#64) 7 := by
    have h9 : (outA + 8#64) + 1#64 = outA + 9#64 := by bv_omega
    rw [← h9]; exact byte_memRegion7_recompose_word (outA + 8#64) (spqrErrorByte err) w1 hw1
  have h2 : memRegion (outA + 9#64) 7 ∗ ((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3) ∗
      memRegion (outA + 32#64) 928 ⊢ memRegion (outA + 9#64) 951 := by
    rw [ProofLib.memRegion_split' (b := outA + 9#64) (n := 7) (k := 944) (b' := outA + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 16#64) (n := 8) (k := 936) (b' := outA + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 24#64) (n := 8) (k := 928) (b' := outA + 32#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (outA + 16#64) w2)
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (outA + 24#64) w3)))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h1)) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ spqrErrorByte err) ∗
    (memRegion (outA + 9#64) 7 ∗ ((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3) ∗
     memRegion (outA + 32#64) 928) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right h2)

@[expose] def sendEkSpillsRestAt (fsp : BitVec 64) (sp : SendEkSpills) : SepProp :=
  words10At (fsp + 8#64) sp.b0 ∗ words10At (fsp + 88#64) sp.b1 ∗ words10At (fsp + 168#64) sp.b2 ∗
  words10At (fsp + 248#64) sp.b3 ∗ words10At (fsp + 328#64) sp.b4 ∗ words10At (fsp + 408#64) sp.b5 ∗
  ((fsp + 488#64) ↦₆₄ sp.w60) ∗ ((fsp + 504#64) ↦₆₄ sp.w62) ∗
  ((fsp + 512#64) ↦₁₂₈ sp.q200) ∗ ((fsp + 528#64) ↦₁₂₈ sp.q210) ∗
  ((fsp + 544#64) ↦₁₂₈ sp.q220) ∗ ((fsp + 560#64) ↦₆₄ sp.w230) ∗ ((fsp + 960#64) ↦₁₂₈ sp.q3c0)

theorem sendEkSpillsAt_split_w61 (fsp : BitVec 64) (sp : SendEkSpills) :
    sendEkSpillsAt fsp sp = ((fsp + 496#64) ↦₆₄ sp.w61) ∗ sendEkSpillsRestAt fsp sp := by
  dsimp only [sendEkSpillsAt, sendEkSpillsRestAt]; ac_rfl

theorem sendEkSpillsAt_rejoin_w61 (fsp : BitVec 64) (sp : SendEkSpills) (w3 : BitVec 64) :
    ((fsp + 496#64) ↦₆₄ w3) ∗ sendEkSpillsRestAt fsp sp = sendEkSpillsAt fsp { sp with w61 := w3 } := by
  dsimp only [sendEkSpillsAt, sendEkSpillsRestAt]; ac_rfl

theorem nhr_err_1856_rejoin_880 (fsp w0 w1 w2 w3 : BitVec 64) :
    ((fsp + 1856#64) ↦₆₄ w0) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
      ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗
      memRegion (fsp + 1888#64) 448 ∗ memRegion (fsp + 2336#64) 400 ⊢
      memRegion (fsp + 1856#64) 880 := by
  rw [ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 480) (k := 400) (b' := fsp + 2336#64) rfl (by bv_omega) (by decide)]
  have h480 := nhr_err_words_entails_memRegion_480 (fsp + 1856#64) w0 w1 w2 w3
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd] at h480
  refine Entails.trans (Entails.of_eq (show _ =
    (((fsp + 1856#64) ↦₆₄ w0) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
     ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗
     memRegion (fsp + 1888#64) 448) ∗ memRegion (fsp + 2336#64) 400 by ac_rfl)) ?_
  exact sepConj_mono_left h480

end CryptoVerification.SpqrV1.States.Recv


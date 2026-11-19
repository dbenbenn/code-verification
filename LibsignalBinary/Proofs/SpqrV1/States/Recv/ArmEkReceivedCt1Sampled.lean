/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledSteps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ekReceivedCt1Sampled` Arm

Verifies the `.ekReceivedCt1Sampled` match arm (`entry + 3392`, tag `10#64`) of `<States>::recv`,
parameterized by `EkRecvMode` (`states_recv_ekReceivedCt1Sampled_sepWPp_gen` and `_ok_ext`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16 CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize CryptoVerification.SpqrV1.States.Leaves

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

/-! ## Top-Level Proof of `.ekReceivedCt1Sampled` (Tag `10#64`) -/

theorem writebackWords63_ek_noop (s1 s2 s3 : State) (sp : SendEkSpills) (w : Words66)
    (h1_x3 : s1.readReg64 .x3 = w.b0.w3) (h1_x4 : s1.readReg64 .x4 = w.b1.w5) (h1_x5 : s1.readReg64 .x5 = w.b4.w4)
    (h1_x6 : s1.readReg64 .x6 = w.b4.w0) (h1_x7 : s1.readReg64 .x7 = w.b3.w1) (h1_x10 : s1.readReg64 .x10 = w.b2.w5)
    (h1_x11 : s1.readReg64 .x11 = w.b4.w1) (h1_x12 : s1.readReg64 .x12 = w.b1.w8) (h1_x13 : s1.readReg64 .x13 = w.b4.w3)
    (h1_x14 : s1.readReg64 .x14 = w.b3.w9) (h1_x15 : s1.readReg64 .x15 = w.b3.w5) (h1_x17 : s1.readReg64 .x17 = w.b1.w3)
    (h1_x18 : s1.readReg64 .x18 = w.b2.w7) (h1_x20 : s1.readReg64 .x20 = w.b1.w6) (h1_x21 : s1.readReg64 .x21 = w.b0.w7)
    (h1_x22 : s1.readReg64 .x22 = w.b0.w4) (h1_x23 : s1.readReg64 .x23 = w.b5.w2) (h1_x26 : s1.readReg64 .x26 = w.b1.w0)
    (h1_x27 : s1.readReg64 .x27 = w.b1.w2) (h1_x30 : s1.readReg64 .x30 = w.b2.w3)
    (h2_x0 : s2.readReg64 .x0 = s1.readReg64 .x14) (h2_x1 : s2.readReg64 .x1 = (ekLoadSpills sp w).b0.w7)
    (h2_x2 : s2.readReg64 .x2 = (ekLoadSpills sp w).b5.w8) (h2_x3 : s2.readReg64 .x3 = (ekLoadSpills sp w).b1.w1)
    (h2_x4 : s2.readReg64 .x4 = (ekLoadSpills sp w).b2.w2) (h2_x6 : s2.readReg64 .x6 = s1.readReg64 .x6)
    (h2_x7 : s2.readReg64 .x7 = (ekLoadSpills sp w).b0.w7) (h2_x9 : s2.readReg64 .x9 = (ekLoadSpills sp w).b5.w4)
    (h2_x10 : s2.readReg64 .x10 = s1.readReg64 .x15) (h2_x12 : s2.readReg64 .x12 = (ekLoadSpills sp w).b0.w9)
    (h2_x13 : s2.readReg64 .x13 = (ekLoadSpills sp w).w60) (h2_x16 : s2.readReg64 .x16 = s1.readReg64 .x11)
    (h2_x17 : s2.readReg64 .x17 = (ekLoadSpills sp w).b1.w4) (h2_x20 : s2.readReg64 .x20 = (ekLoadSpills sp w).b5.w9)
    (h2_x23 : s2.readReg64 .x23 = s1.readReg64 .x23) (h2_x25 : s2.readReg64 .x25 = (ekLoadSpills sp w).b0.w4)
    (h2_x26 : s2.readReg64 .x26 = (ekLoadSpills sp w).b2.w0) (h2_x27 : s2.readReg64 .x27 = (ekLoadSpills sp w).b1.w0)
    (h2_x30 : s2.readReg64 .x30 = (ekLoadSpills sp w).b0.w8)
    (h3_x0 : s3.readReg64 .x0 = s2.readReg64 .x0) (h3_x1 : s3.readReg64 .x1 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w6)
    (h3_x2 : s3.readReg64 .x2 = s2.readReg64 .x27) (h3_x3 : s3.readReg64 .x3 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b0.w3)
    (h3_x4 : s3.readReg64 .x4 = s2.readReg64 .x4) (h3_x5 : s3.readReg64 .x5 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w6)
    (h3_x6 : s3.readReg64 .x6 = s2.readReg64 .x6) (h3_x7 : s3.readReg64 .x7 = s2.readReg64 .x7)
    (h3_x8 : s3.readReg64 .x8 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w5)
    (h3_x9 : s3.readReg64 .x9 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w3)
    (h3_x10 : s3.readReg64 .x10 = s2.readReg64 .x10) (h3_x11 : s3.readReg64 .x11 = s2.readReg64 .x30)
    (h3_x12 : s3.readReg64 .x12 = s2.readReg64 .x12) (h3_x13 : s3.readReg64 .x13 = s2.readReg64 .x23)
    (h3_x14 : s3.readReg64 .x14 = s2.readReg64 .x17) (h3_x15 : s3.readReg64 .x15 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w3)
    (h3_x16 : s3.readReg64 .x16 = s2.readReg64 .x3) (h3_x17 : s3.readReg64 .x17 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w4)
    (h3_x20 : s3.readReg64 .x20 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w7)
    (h3_x21 : s3.readReg64 .x21 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w9)
    (h3_x22 : s3.readReg64 .x22 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w1)
    (h3_x23 : s3.readReg64 .x23 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w8)
    (h3_x24 : s3.readReg64 .x24 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b0.w2)
    (h3_x25 : s3.readReg64 .x25 = s2.readReg64 .x25) (h3_x26 : s3.readReg64 .x26 = s2.readReg64 .x26)
    (h3_x27 : s3.readReg64 .x27 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w9)
    (h3_x28 : s3.readReg64 .x28 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w5)
    (h3_x30 : s3.readReg64 .x30 = s2.readReg64 .x16) :
    writebackWords63 s3 (ekSpills10276 s2 (ekSpills10136 s1 (ekLoadSpills sp w) w.q60)) =
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5, q60 := w.q60, w62 := w.w62 } := by
  dsimp only [writebackWords63, ekSpills10276, ekSpills10136, ekLoadSpills]
  simp only [h3_x0, h3_x1, h3_x2, h3_x3, h3_x4, h3_x5, h3_x6, h3_x7, h3_x8, h3_x9, h3_x10, h3_x11, h3_x12, h3_x13,
    h3_x14, h3_x15, h3_x16, h3_x17, h3_x20, h3_x21, h3_x22, h3_x23, h3_x24, h3_x25, h3_x26, h3_x27, h3_x28, h3_x30,
    h2_x0, h2_x1, h2_x2, h2_x3, h2_x4, h2_x6, h2_x7, h2_x9, h2_x10, h2_x12, h2_x13, h2_x16, h2_x17, h2_x20, h2_x23,
    h2_x25, h2_x26, h2_x27, h2_x30, ekSpills10136, ekLoadSpills, h1_x3, h1_x4, h1_x5, h1_x6, h1_x7, h1_x10, h1_x11,
    h1_x12, h1_x13, h1_x14, h1_x15, h1_x17, h1_x18, h1_x20, h1_x21, h1_x22, h1_x23, h1_x26, h1_x27, h1_x30]

theorem writebackWords63_ek_ack (s2 s3 : State) (sp : SendEkSpills) (w : Words57)
    (h2_x0 : s2.readReg64 .x0 = w.b3.w9) (h2_x2 : s2.readReg64 .x2 = w.b4.w6) (h2_x3 : s2.readReg64 .x3 = w.w55)
    (h2_x4 : s2.readReg64 .x4 = w.b4.w9) (h2_x6 : s2.readReg64 .x6 = w.b4.w0) (h2_x7 : s2.readReg64 .x7 = w.b3.w8)
    (h2_x9 : s2.readReg64 .x9 = w.b1.w7) (h2_x10 : s2.readReg64 .x10 = w.b3.w5) (h2_x12 : s2.readReg64 .x12 = w.b3.w3)
    (h2_x13 : s2.readReg64 .x13 = w.w56) (h2_x16 : s2.readReg64 .x16 = w.b4.w1) (h2_x17 : s2.readReg64 .x17 = w.w53)
    (h2_x20 : s2.readReg64 .x20 = w.w54) (h2_x23 : s2.readReg64 .x23 = w.w52) (h2_x25 : s2.readReg64 .x25 = w.b3.w2)
    (h2_x26 : s2.readReg64 .x26 = w.b4.w7) (h2_x30 : s2.readReg64 .x30 = w.b3.w4)
    (h3_x0 : s3.readReg64 .x0 = s2.readReg64 .x0) (h3_x1 : s3.readReg64 .x1 = (ekSpills9788 sp w).b1.w6)
    (h3_x2 : s3.readReg64 .x2 = s2.readReg64 .x27) (h3_x3 : s3.readReg64 .x3 = (ekSpills9788 sp w).b0.w3)
    (h3_x4 : s3.readReg64 .x4 = s2.readReg64 .x4) (h3_x5 : s3.readReg64 .x5 = (ekSpills9788 sp w).b2.w6)
    (h3_x6 : s3.readReg64 .x6 = s2.readReg64 .x6) (h3_x7 : s3.readReg64 .x7 = s2.readReg64 .x7)
    (h3_x8 : s3.readReg64 .x8 = (ekSpills9788 sp w).b2.w5) (h3_x9 : s3.readReg64 .x9 = (ekSpills9788 sp w).b2.w3)
    (h3_x10 : s3.readReg64 .x10 = s2.readReg64 .x10) (h3_x11 : s3.readReg64 .x11 = s2.readReg64 .x30)
    (h3_x12 : s3.readReg64 .x12 = s2.readReg64 .x12) (h3_x13 : s3.readReg64 .x13 = s2.readReg64 .x23)
    (h3_x14 : s3.readReg64 .x14 = s2.readReg64 .x17) (h3_x15 : s3.readReg64 .x15 = (ekSpills9788 sp w).b1.w3)
    (h3_x16 : s3.readReg64 .x16 = s2.readReg64 .x3) (h3_x17 : s3.readReg64 .x17 = (ekSpills9788 sp w).b2.w4)
    (h3_x20 : s3.readReg64 .x20 = (ekSpills9788 sp w).b1.w7) (h3_x21 : s3.readReg64 .x21 = (ekSpills9788 sp w).b2.w9)
    (h3_x22 : s3.readReg64 .x22 = (ekSpills9788 sp w).b2.w1) (h3_x23 : s3.readReg64 .x23 = (ekSpills9788 sp w).b1.w8)
    (h3_x24 : s3.readReg64 .x24 = (ekSpills9788 sp w).b0.w2) (h3_x25 : s3.readReg64 .x25 = s2.readReg64 .x25)
    (h3_x26 : s3.readReg64 .x26 = s2.readReg64 .x26) (h3_x27 : s3.readReg64 .x27 = (ekSpills9788 sp w).b1.w9)
    (h3_x28 : s3.readReg64 .x28 = (ekSpills9788 sp w).b1.w5) (h3_x30 : s3.readReg64 .x30 = s2.readReg64 .x16) :
    writebackWords63 s3 (ekSpills10276 s2 (ekSpills9788 sp w)) =
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4
        b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, s2.readReg64 .x27, sp.b3.w0, sp.b1.w7⟩
        q60 := sp.q3c0, w62 := sp.b3.w1 } := by
  dsimp only [writebackWords63, ekSpills10276, ekSpills9788]
  simp only [h3_x0, h3_x1, h3_x2, h3_x3, h3_x4, h3_x5, h3_x6, h3_x7, h3_x8, h3_x9, h3_x10, h3_x11, h3_x12, h3_x13,
    h3_x14, h3_x15, h3_x16, h3_x17, h3_x20, h3_x21, h3_x22, h3_x23, h3_x24, h3_x25, h3_x26, h3_x27, h3_x28, h3_x30,
    ekSpills9788, h2_x0, h2_x2, h2_x3, h2_x4, h2_x6, h2_x7, h2_x9, h2_x10, h2_x12, h2_x13, h2_x16, h2_x17, h2_x20,
    h2_x23, h2_x25, h2_x26, h2_x30]

theorem memRegion_1856_880_entails_words66 (fsp : BitVec 64) :
    memRegion (fsp + 1856#64) 880 ⊢
      ∃∗ u740 : Words66, words66At (fsp + 1856#64) u740 ∗ memRegion (fsp + 2384#64) 352 := by
  rw [memRegion_880_split_528_352 fsp]
  refine Entails.trans (sepConj_mono_left (memRegion_528_entails_words66At (fsp + 1856#64))) ?_
  rw [sepExists_sepConj_left]; exact Entails.refl _

theorem sepWPp_intro_ex {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {Q Q_panic : State → SepProp → Prop} (hrun : s.status = .Running)
    (h : ∀ x, SepWPp prog target_pc s (P x) Q Q_panic) :
    SepWPp prog target_pc s (∃∗ x, P x) Q Q_panic := by
  apply SepWPp.of_sepWP
  rw [← emp_sepConj (∃∗ x, P x), sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left
  intro x; rw [emp_sepConj]
  exact SepWP.done rfl hrun (h x)

end CryptoVerification.SpqrV1.States.Recv


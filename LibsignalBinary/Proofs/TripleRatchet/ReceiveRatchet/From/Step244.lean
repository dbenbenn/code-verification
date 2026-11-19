/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Frame -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees -- proof-setup: allow-public-import
import ProofLib
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

namespace ReceiveRatchetFrom
open FromFetches

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

theorem sc_pack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
       ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
       ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
       ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
       ((a + 96#64) ↦₆₄ w12))) :
    (((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1) ∗ ((sp - 416#64) ↦₆₄ w2) ∗
     ((sp - 408#64) ↦₆₄ w3) ∗ ((sp - 400#64) ↦₆₄ w4) ∗ ((sp - 392#64) ↦₆₄ w5) ∗
     ((sp - 384#64) ↦₆₄ w6) ∗ ((sp - 376#64) ↦₆₄ w7) ∗ ((sp - 368#64) ↦₆₄ w8) ∗
     ((sp - 360#64) ↦₆₄ w9) ∗ ((sp - 352#64) ↦₆₄ w10) ∗ ((sp - 344#64) ↦₆₄ w11) ∗
     ((sp - 336#64) ↦₆₄ w12)) ⊢
      ((sp - 432#64) ↦ₛ bs) := by
  rw [h (sp - 432#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
  exact Entails.refl _

theorem sc_pack_ret (r : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
       ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
       ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
       ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
       ((a + 96#64) ↦₆₄ w12))) :
    (((r + 24#64) ↦₆₄ w0) ∗ ((r + 32#64) ↦₆₄ w1) ∗ ((r + 40#64) ↦₆₄ w2) ∗
     ((r + 48#64) ↦₆₄ w3) ∗ ((r + 56#64) ↦₆₄ w4) ∗ ((r + 64#64) ↦₆₄ w5) ∗
     ((r + 72#64) ↦₆₄ w6) ∗ ((r + 80#64) ↦₆₄ w7) ∗ ((r + 88#64) ↦₆₄ w8) ∗
     ((r + 96#64) ↦₆₄ w9) ∗ ((r + 104#64) ↦₆₄ w10) ∗ ((r + 112#64) ↦₆₄ w11) ∗
     ((r + 120#64) ↦₆₄ w12)) ⊢
      ((r + 24#64) ↦ₛ bs) := by
  rw [h (r + 24#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem rk_pack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    (((sp - 328#64) ↦₆₄ w0) ∗ ((sp - 320#64) ↦₆₄ w1) ∗
     ((sp - 312#64) ↦₆₄ w2) ∗ ((sp - 304#64) ↦₆₄ w3)) ⊢
      ((sp - 328#64) ↦ₛ bs) := by
  rw [h (sp - 328#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
  exact Entails.refl _

theorem rk_pack_ret (r : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    (((r + 128#64) ↦₆₄ w0) ∗ ((r + 136#64) ↦₆₄ w1) ∗
     ((r + 144#64) ↦₆₄ w2) ∗ ((r + 152#64) ↦₆₄ w3)) ⊢
      ((r + 128#64) ↦ₛ bs) := by
  rw [h (r + 128#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem lik_pack_ret (r : BitVec 64) {bs : List (BitVec 8)}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
       ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
       ((a + 6#64) ↦₈ b6) ∗
       ((a + 7#64) ↦₆₄ (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7)) ∗
       ((a + 15#64) ↦₆₄ w15) ∗
       ((a + 23#64) ↦₆₄ w23) ∗
       ((a + 31#64) ↦₈ b31))) :
    (((r + 200#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((r + 204#64) ↦₁₆ (b5 ++ b4)) ∗
     ((r + 206#64) ↦₈ b6) ∗
     ((r + 207#64) ↦₆₄ (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7)) ∗
     ((r + 215#64) ↦₆₄ w15) ∗
     ((r + 223#64) ↦₆₄ w23) ∗
     ((r + 231#64) ↦₈ b31)) ⊢
      ((r + 200#64) ↦ₛ bs) := by
  rw [h (r + 200#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem rem_pack_ret (r : BitVec 64) {bs : List (BitVec 8)}
    {d0 : BitVec 32} {h4 : BitVec 16} {w6 w14 w22 : BitVec 64} {h30 : BitVec 16}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
       ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₆₄ w22) ∗ ((a + 30#64) ↦₁₆ h30))) :
    (((r + 232#64) ↦₃₂ d0) ∗ ((r + 236#64) ↦₁₆ h4) ∗ ((r + 238#64) ↦₆₄ w6) ∗
     ((r + 246#64) ↦₆₄ w14) ∗ ((r + 254#64) ↦₆₄ w22) ∗ ((r + 262#64) ↦₁₆ h30)) ⊢
      ((r + 232#64) ↦ₛ bs) := by
  rw [h (r + 232#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem err22_pack_stack (sp p w16 : BitVec 64)
    {d0 : BitVec 32} {h4 : BitVec 16} {w6 w14 : BitVec 64} {h22 : BitVec 16}
    (h : ∀ a : BitVec 64, ((a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ 27#64) ∗ ((a + 16#64) ↦₆₄ w16)) =
      ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
       ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₁₆ h22))) :
    (((sp - 152#64) ↦₃₂ d0) ∗ ((sp - 148#64) ↦₁₆ h4) ∗ ((sp - 146#64) ↦₆₄ w6) ∗
     ((sp - 138#64) ↦₆₄ w14) ∗ ((sp - 130#64) ↦₁₆ h22)) ⊢
      (((sp - 152#64) ↦₆₄ p) ∗ ((sp - 144#64) ↦₆₄ 27#64) ∗ ((sp - 136#64) ↦₆₄ w16)) := by
  have h1 := h (sp - 152#64)
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg] at h1 ⊢
  rw [h1]
  exact Entails.refl _

theorem err22_pack_ret (r p : BitVec 64)
    {d0 : BitVec 32} {h4 : BitVec 16} {w6 w14 : BitVec 64}
    (h : ∀ a : BitVec 64, ∀ r22 : BitVec 16,
      ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
       ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₁₆ r22)) ⊢
        ((a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ 27#64) ∗ memRegion (a + 16#64) 8))
    (r38 : BitVec 16) :
    (((r + 16#64) ↦₃₂ d0) ∗ ((r + 20#64) ↦₁₆ h4) ∗ ((r + 22#64) ↦₆₄ w6) ∗
     ((r + 30#64) ↦₆₄ w14) ∗ ((r + 38#64) ↦₁₆ r38) ∗ memRegion (r + 40#64) 16) ⊢
      (((r + 16#64) ↦₆₄ p) ∗ ((r + 24#64) ↦₆₄ 27#64) ∗ memRegion (r + 32#64) 24) := by
  have h1 := h (r + 16#64) r38
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  rw [mr_cut_add r 32 8 16 (by decide)]
  have h2 := sepConj_mono h1 (Entails.refl (memRegion (r + 40#64) 16))
  simpa only [sepConj_assoc] using h2

theorem lik_unpack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    (h : ∀ a : BitVec 64,
      (a ↦ₛ bs) =
        ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
         ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
         ((a + 6#64) ↦₈ b6) ∗
         ((a + 7#64) ↦₈ b7) ∗
         ((a + 8#64) ↦₈ b8) ∗
         ((a + 9#64) ↦₃₂ (b12 ++ b11 ++ b10 ++ b9)) ∗
         ((a + 13#64) ↦₁₆ (b14 ++ b13)) ∗
         ((a + 15#64) ↦₆₄ w15) ∗
         ((a + 23#64) ↦₆₄ w23) ∗
         ((a + 31#64) ↦₈ b31))) :
    ((sp - 159#64) ↦ₛ bs) =
      (((sp - 159#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
       ((sp - 155#64) ↦₁₆ (b5 ++ b4)) ∗
       ((sp - 153#64) ↦₈ b6) ∗
       ((sp - 152#64) ↦₈ b7) ∗
       ((sp - 151#64) ↦₈ b8) ∗
       ((sp - 150#64) ↦₃₂ (b12 ++ b11 ++ b10 ++ b9)) ∗
       ((sp - 146#64) ↦₁₆ (b14 ++ b13)) ∗
       ((sp - 144#64) ↦₆₄ w15) ∗
       ((sp - 136#64) ↦₆₄ w23) ∗
       ((sp - 128#64) ↦₈ b31)) := by
  rw [h (sp - 159#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]

theorem rem_unpack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {d0 : BitVec 32} {h4 : BitVec 16} {w6 w14 w22 : BitVec 64} {h30 : BitVec 16}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
       ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₆₄ w22) ∗ ((a + 30#64) ↦₁₆ h30))) :
    ((sp - 158#64) ↦ₛ bs) =
      (((sp - 158#64) ↦₃₂ d0) ∗ ((sp - 154#64) ↦₁₆ h4) ∗ ((sp - 152#64) ↦₆₄ w6) ∗
       ((sp - 144#64) ↦₆₄ w14) ∗ ((sp - 136#64) ↦₆₄ w22) ∗ ((sp - 128#64) ↦₁₆ h30)) := by
  rw [h (sp - 158#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]

theorem pointsTo64_sp_160 (sp : BitVec 64) (b0 b1 : BitVec 8) (d2 : BitVec 32) (h6 : BitVec 16) :
    (((sp - 160#64) ↦₈ b0) ∗ ((sp - 159#64) ↦₈ b1) ∗
     ((sp - 158#64) ↦₃₂ d2) ∗ ((sp - 154#64) ↦₁₆ h6)) =
      ((sp - 160#64) ↦₆₄ (h6 ++ d2 ++ b1 ++ b0)) := by
  have h := pointsTo64_of_8_8_32_16 (sp - 160#64) b0 b1 d2 h6
  simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg] using h

theorem SepWP.mono_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (hP : P ⊢ P') (h : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  SepWP.weaken_pre hP h

@[arm64_norm, wp_norm]
theorem bv_lik_w9 (b4 b5 b6 : BitVec 8) :
    BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 (b5 ++ b4) |||
          BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b6 <<< 16))) =
      (0#8 ++ b6 ++ b5 ++ b4 : BitVec 32).zeroExtend 64 := by
  have h1 : (0#8 ++ b6 ++ b5 ++ b4 : BitVec 32) = 0#8 ++ b6 ++ (b5 ++ b4) := by bv_kernel
  rw [h1]; clear h1
  generalize b5 ++ b4 = x
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv_lik_x8 (b9 b10 b11 b12 b13 b14 : BitVec 8) :
    (0#16 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 : BitVec 64) |||
      (BitVec.zeroExtend 64 (b14 ++ b13) <<< 48) =
      b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 := by
  have h1 : (0#16 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 : BitVec 64) =
      0#16 ++ (b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8) := by bv_kernel
  have h2 : (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 : BitVec 64) =
      (b14 ++ b13) ++ (b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8) := by bv_kernel
  rw [h1, h2]; clear h1 h2
  generalize b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 = x
  generalize b14 ++ b13 = y
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv_lik_x24 (b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8) :
    (0#48 ++ b8 ++ b7 : BitVec 64) |||
      (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 : BitVec 64) =
      b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 := by
  have h1 : (0#48 ++ b8 ++ b7 : BitVec 64) = 0#48 ++ (b8 ++ b7) := by bv_kernel
  have h2 : (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ 0#8 ++ 0#8 : BitVec 64) =
      (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9) ++ 0#16 := by bv_kernel
  have h3 : (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 : BitVec 64) =
      (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9) ++ (b8 ++ b7) := by bv_kernel
  rw [h1, h2, h3]; clear h1 h2 h3
  generalize b8 ++ b7 = x
  generalize b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 = y
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv16_eta_bytes (w : BitVec 16) :
    w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv32_eta_bytes (w : BitVec 32) :
    w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w := by
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_eta_bytes (w : BitVec 64) :
    w.extractLsb' 56 8 ++ w.extractLsb' 48 8 ++ w.extractLsb' 40 8 ++ w.extractLsb' 32 8 ++
      w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w := by
  bv_kernel

@[arm64_norm, wp_norm]
theorem zext32_bv16_zext64 (w : BitVec 16) :
    (w.zeroExtend 32).zeroExtend 64 = w.zeroExtend 64 := by bv_kernel

@[arm64_norm, wp_norm]
theorem zext_bv8_and_ff (b : BitVec 8) :
    (b.zeroExtend 32 &&& 0xff#32) = b.zeroExtend 32 := by bv_kernel

@[arm64_norm, wp_norm]
theorem zext64_bv8_setWidth_32 (b : BitVec 8) :
    (b.zeroExtend 64).setWidth 32 = b.zeroExtend 32 := by bv_kernel

@[arm64_norm, wp_norm]
theorem zext64_bv8_setWidth_8 (b : BitVec 8) :
    (b.zeroExtend 64).setWidth 8 = b := by bv_kernel

@[arm64_norm, wp_norm]
theorem zext32_bv8_zext64 (b : BitVec 8) :
    (b.zeroExtend 32).zeroExtend 64 = b.zeroExtend 64 := by bv_kernel

theorem sc_unpack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
       ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
       ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
       ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
       ((a + 96#64) ↦₆₄ w12))) :
    ((sp - 432#64) ↦ₛ bs) =
      (((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1) ∗ ((sp - 416#64) ↦₆₄ w2) ∗
       ((sp - 408#64) ↦₆₄ w3) ∗ ((sp - 400#64) ↦₆₄ w4) ∗ ((sp - 392#64) ↦₆₄ w5) ∗
       ((sp - 384#64) ↦₆₄ w6) ∗ ((sp - 376#64) ↦₆₄ w7) ∗ ((sp - 368#64) ↦₆₄ w8) ∗
       ((sp - 360#64) ↦₆₄ w9) ∗ ((sp - 352#64) ↦₆₄ w10) ∗ ((sp - 344#64) ↦₆₄ w11) ∗
       ((sp - 336#64) ↦₆₄ w12)) := by
  rw [h (sp - 432#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]

theorem rk_unpack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    ((sp - 328#64) ↦ₛ bs) =
      (((sp - 328#64) ↦₆₄ w0) ∗ ((sp - 320#64) ↦₆₄ w1) ∗
       ((sp - 312#64) ↦₆₄ w2) ∗ ((sp - 304#64) ↦₆₄ w3)) := by
  rw [h (sp - 328#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]

theorem err22_unpack_stack (sp p w16 : BitVec 64)
    {d0 : BitVec 32} {h4 : BitVec 16} {w6 w14 : BitVec 64} {h22 : BitVec 16}
    (h : ∀ a : BitVec 64, ((a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ 27#64) ∗ ((a + 16#64) ↦₆₄ w16)) =
      ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
       ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₁₆ h22))) :
    (((sp - 152#64) ↦₆₄ p) ∗ ((sp - 144#64) ↦₆₄ 27#64) ∗ ((sp - 136#64) ↦₆₄ w16)) ⊢
      (((sp - 152#64) ↦₃₂ d0) ∗ ((sp - 148#64) ↦₁₆ h4) ∗ ((sp - 146#64) ↦₆₄ w6) ∗
       ((sp - 138#64) ↦₆₄ w14) ∗ ((sp - 130#64) ↦₁₆ h22)) := by
  have h1 := h (sp - 152#64)
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg] at h1 ⊢
  rw [h1]
  exact Entails.refl _

theorem sp_288_combine_prev (sp : BitVec 64) (prev u_284 : BitVec 32) :
    (((sp - 288#64) ↦₃₂ prev) ∗ ((sp - 284#64) ↦₃₂ u_284)) =
      ((sp - 288#64) ↦₆₄ (u_284 ++ prev)) := by
  have h := (pointsTo64_eq_pointsTo32 (sp - 288#64) prev u_284).symm
  simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg] using h

theorem ret_168_split_prev (r : BitVec 64) (prev u_284 : BitVec 32) :
    ((r + 168#64) ↦₆₄ (u_284 ++ prev)) ⊢
      ((r + 168#64) ↦₃₂ prev) ∗ memRegion (r + 172#64) 4 := by
  rw [pointsTo64_eq_pointsTo32 (r + 168#64) prev u_284]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (Entails.refl _) (pointsTo32_entails_memRegion _ _)

theorem ret_200_split_lik (r : BitVec 64) :
    memRegion (r + 200#64) 32 =
      (∃∗ l0 : BitVec 32, (r + 200#64) ↦₃₂ l0) ∗
      (∃∗ l4 : BitVec 16, (r + 204#64) ↦₁₆ l4) ∗
      (∃∗ l6 : BitVec 8, (r + 206#64) ↦₈ l6) ∗
      (∃∗ l7 : BitVec 64, (r + 207#64) ↦₆₄ l7) ∗
      (∃∗ l15 : BitVec 64, (r + 215#64) ↦₆₄ l15) ∗
      (∃∗ l23 : BitVec 64, (r + 223#64) ↦₆₄ l23) ∗
      (∃∗ l31 : BitVec 8, (r + 231#64) ↦₈ l31) := by
  rw [mr_cut_add r 200 4 28 (by decide)]
  rw [mr_cut_add r 204 2 26 (by decide)]
  rw [mr_cut_add r 206 1 25 (by decide)]
  rw [mr_cut_add r 207 8 17 (by decide)]
  rw [mr_cut_add r 215 8 9 (by decide)]
  rw [mr_cut_add r 223 8 1 (by decide)]
  simp only [memRegion_eight, memRegion_four, memRegion_two, memRegion_one]

theorem ret_232_split_rem (r : BitVec 64) :
    memRegion (r + 232#64) 32 =
      (∃∗ m0 : BitVec 32, (r + 232#64) ↦₃₂ m0) ∗
      (∃∗ m4 : BitVec 16, (r + 236#64) ↦₁₆ m4) ∗
      (∃∗ m6 : BitVec 64, (r + 238#64) ↦₆₄ m6) ∗
      (∃∗ m14 : BitVec 64, (r + 246#64) ↦₆₄ m14) ∗
      (∃∗ m22 : BitVec 64, (r + 254#64) ↦₆₄ m22) ∗
      (∃∗ m30 : BitVec 16, (r + 262#64) ↦₁₆ m30) := by
  rw [mr_cut_add r 232 4 28 (by decide)]
  rw [mr_cut_add r 236 2 26 (by decide)]
  rw [mr_cut_add r 238 8 18 (by decide)]
  rw [mr_cut_add r 246 8 10 (by decide)]
  rw [mr_cut_add r 254 8 2 (by decide)]
  simp only [memRegion_eight, memRegion_four, memRegion_two]

theorem vecU8Buf_zero_entails_emp (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (h : cap = 0) :
    vecU8Buf A cap ptr bs ⊢ emp := by
  subst h
  unfold vecU8Buf
  simp only [↓reduceIte]
  exact Entails.pure_left (fun _ => Entails.refl _)

theorem vecU8Buf_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (h : cap ≠ 0) :
    vecU8Buf A cap ptr bs ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold vecU8Buf
  rw [ite_eq_right_iff.mpr (fun hc => (h hc).elim)]
  apply Entails.pure_left
  rintro ⟨hle, _, _⟩
  refine sepConj_mono (Entails.refl _) ?_
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) :=
    memRegion_split' (by omega) rfl (by omega)
  rw [hsplit]
  exact sepConj_mono (pointsToBytes_entails_memRegion ptr bs) (Entails.refl _)

end ReceiveRatchetFrom
end CryptoVerification.LibsignalTripleRatchet


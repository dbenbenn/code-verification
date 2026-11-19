/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<Ct1SentEkReceived>::send_ct2`: Libcrux Issue-1275 Loops

**Checked by Lean.**

Verifies the `swapAdjacentPairs` byte-swap loop and `issue1275NeedsFlip` halfword scan loop
inlined into `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`.
-/

public section

namespace CryptoVerification.SpqrV1.Layout.L29b

open Lean Elab Tactic Arm64 ProofLib

end CryptoVerification.SpqrV1.Layout.L29b

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L29b
open DoReserveNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Registers preserved across the `swapAdjacentPairs` loop (`0x5e604..0x5e628`). -/
structure SwapLoopSaved (s0 s : State) : Prop where
  x19 : s.readReg64 .x19 = s0.readReg64 .x19
  x20 : s.readReg64 .x20 = s0.readReg64 .x20
  x22 : s.readReg64 .x22 = s0.readReg64 .x22
  x23 : s.readReg64 .x23 = s0.readReg64 .x23
  x24 : s.readReg64 .x24 = s0.readReg64 .x24
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28
  x29 : s.readReg64 .x29 = s0.readReg64 .x29
  x30 : s.readReg64 .x30 = s0.readReg64 .x30
  sp : s.sp = s0.sp
  trace : s.trace = s0.trace
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0

theorem SwapLoopSaved.refl (s : State) : SwapLoopSaved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SwapLoopSaved.trans {s0 s1 s2 : State}
    (h01 : SwapLoopSaved s0 s1) (h12 : SwapLoopSaved s1 s2) : SwapLoopSaved s0 s2 :=
  ⟨h12.x19.trans h01.x19, h12.x20.trans h01.x20, h12.x22.trans h01.x22,
   h12.x23.trans h01.x23, h12.x24.trans h01.x24, h12.x25.trans h01.x25,
   h12.x26.trans h01.x26, h12.x27.trans h01.x27, h12.x28.trans h01.x28,
   h12.x29.trans h01.x29, h12.x30.trans h01.x30, h12.sp.trans h01.sp,
   h12.trace.trans h01.trace, h12.vregs.trans h01.vregs⟩

theorem pointsToBytes_pair_split (p : BitVec 64) (b0 b1 : BitVec 8) (rest : Bytes) :
    (p ↦ₛ (b0 :: b1 :: rest)) =
      (p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦ₛ rest) := by
  rw [pointsToBytes_cons, pointsToBytes_cons]
  have h2 : (p + 1#64) + 1#64 = p + 2#64 := by bv_omega
  rw [h2]

/-- Registers preserved across the `issue1275NeedsFlip` scan loop (`0x5e478..0x5e588`). -/
structure ScanLoopSaved (s0 s : State) : Prop where
  x19 : s.readReg64 .x19 = s0.readReg64 .x19
  x20 : s.readReg64 .x20 = s0.readReg64 .x20
  x23 : s.readReg64 .x23 = s0.readReg64 .x23
  x24 : s.readReg64 .x24 = s0.readReg64 .x24
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28
  x29 : s.readReg64 .x29 = s0.readReg64 .x29
  x30 : s.readReg64 .x30 = s0.readReg64 .x30
  sp : s.sp = s0.sp
  trace : s.trace = s0.trace
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0

theorem ScanLoopSaved.refl (s : State) : ScanLoopSaved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ScanLoopSaved.trans {s0 s1 s2 : State}
    (h01 : ScanLoopSaved s0 s1) (h12 : ScanLoopSaved s1 s2) : ScanLoopSaved s0 s2 :=
  ⟨h12.x19.trans h01.x19, h12.x20.trans h01.x20,
   h12.x23.trans h01.x23, h12.x24.trans h01.x24, h12.x25.trans h01.x25,
   h12.x26.trans h01.x26, h12.x27.trans h01.x27, h12.x28.trans h01.x28,
   h12.x29.trans h01.x29, h12.x30.trans h01.x30, h12.sp.trans h01.sp,
   h12.trace.trans h01.trace, h12.vregs.trans h01.vregs⟩

theorem issue1275_word_eq (b0 b1 : BitVec 8) :
    ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = b1 ++ b0 := by
  bv_kernel

theorem pointsToBytes_pair_pointsTo16 (a : BitVec 64) (b0 b1 : BitVec 8) (rest : Bytes) :
    (a ↦ₛ (b0 :: b1 :: rest)) = (a ↦₁₆ (b1 ++ b0)) ∗ ((a + 2#64) ↦ₛ rest) := by
  rw [pointsToBytes_pair_split a b0 b1 rest, ← pointsTo8_pair a b0 b1]
  ac_rfl

theorem issue1275NeedsFlip_cons_cont (b0 b1 : BitVec 8) (rest : Bytes)
    (hw : ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0000#16 ∨
          ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0xFFFF#16) :
    issue1275NeedsFlip (b0 :: b1 :: rest) = issue1275NeedsFlip rest := by
  dsimp only [issue1275NeedsFlip]
  rcases hw with h | h <;> simp [h]

theorem issue1275NeedsFlip_cons_false_not_be (b0 b1 : BitVec 8) (rest : Bytes)
    (hflip : issue1275NeedsFlip (b0 :: b1 :: rest) = false) :
    ¬(((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0100#16 ∨
      ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0200#16 ∨
      ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0xFEFF#16) := by
  dsimp only [issue1275NeedsFlip] at hflip
  rintro (h | h | h) <;> simp [h] at hflip

theorem issue1275NeedsFlip_cons_true_be (b0 b1 : BitVec 8) (rest : Bytes)
    (hflip : issue1275NeedsFlip (b0 :: b1 :: rest) = true)
    (hnot_cont : ¬(((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0000#16 ∨
                   ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0xFFFF#16)) :
    ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0100#16 ∨
    ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0200#16 ∨
    ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0xFEFF#16 := by
  dsimp only [issue1275NeedsFlip] at hflip
  generalize ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = w at hflip hnot_cont ⊢
  push Not at hnot_cont
  rcases hnot_cont with ⟨hw0, hwffff⟩
  have hc0 : (w == 0x0000#16 || w == 0xFFFF#16) = false := by
    revert hw0 hwffff; bv_kernel
  rw [hc0] at hflip
  by_cases hc1 : (w == 0x0001#16 || w == 0x0002#16 || w == 0xFFFE#16) = true
  · rw [hc1] at hflip; contradiction
  · rw [Bool.not_eq_true] at hc1
    rw [hc1] at hflip
    by_cases hc2 : (w == 0x0100#16 || w == 0x0200#16 || w == 0xFEFF#16) = true
    · simp only [Bool.or_eq_true, beq_iff_eq] at hc2
      rcases hc2 with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rw [Bool.not_eq_true] at hc2
      rw [hc2] at hflip; contradiction

end CryptoVerification.SpqrV1.Unchunked

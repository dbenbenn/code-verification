/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockEnc
import ProofLib.BV
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Stack Frame Layout & Cell Representations (`CbcEnc.Layout`)

`0x1120`-byte (`4384`-byte) stack frame partition, `CbcKeyState` (`b == 1#8` ARMv8 round keys vs
`b != 1#8` `fixslice64` keys), and cell-representation bridges for `aes_256_cbc_encrypt`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open CryptoVerification.RustHeap (vecHeader vecU8 vecU8At allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open VerifiedLibraries.RustStd (allocCallPreserved_trans)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved OomPreserved AllocCallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (aes256KeyScheduleFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj fsKeys256At fsKeys256At_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (bytesToU128LE armv8ExpandKey roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (roundKeys15At_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockEnc (pointsToBytes16_eq_pointsTo128)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon

/-! ## 1. `CbcPreserved` & Stack Frame Partition (`4384` B + `4096` B + `7904` B = `16384` B) -/

@[expose] def CbcPreserved (s0 sf : State) : Prop :=
  AllocCallPreserved s0 sf ∧ VmPreserved s0 sf

theorem CbcPreserved.refl (s : State) : CbcPreserved s s :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, VmPreserved.refl s⟩

theorem CbcPreserved.trans {s0 s1 s2 : State}
    (h1 : CbcPreserved s0 s1) (h2 : CbcPreserved s1 s2) : CbcPreserved s0 s2 :=
  ⟨allocCallPreserved_trans h1.1 h2.1, h1.2.trans h2.2⟩

theorem CbcPreserved.of_pure {s0 sf : State} (h : PureStepPreserved s0 sf) :
    CbcPreserved s0 sf := ⟨h.allocCallPreserved, h.vmPreserved⟩

theorem CbcPreserved.of_proj_perm {s0 sf : State}
    (hp : pureStepProj sf = pureStepProj s0) (hm : sf.mem.perm = s0.mem.perm) :
    CbcPreserved s0 sf := CbcPreserved.of_pure (PureStepPreserved.of_proj_perm hp hm)

theorem CbcPreserved.pool_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s0 sf : State} (h : CbcPreserved s0 sf) :
    A.pool lim st sf = A.pool lim st s0 := A.pool_of_vmPreserved h.2

theorem CbcPreserved.toOomPreserved {s0 sf : State} (h : CbcPreserved s0 sf) :
    OomPreserved s0 sf := h.1.toOomPreserved

theorem sp_sub96_and_15 {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 96#64) &&& 15#64 = 0#64 := by revert h; bv_bits

theorem sp_sub4192_and_15 {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 96#64 - 4096#64) &&& 15#64 = 0#64 := by revert h; bv_bits

theorem sp_sub4384_and_15 {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 4384#64) &&& 15#64 = 0#64 := by revert h; bv_bits

theorem spAligned_of_eq {s : State} {sp_local : BitVec 64}
    (hsp : s.sp = sp_local) (hsp_loc : sp_local &&& 15#64 = 0#64) : s.spAligned = true := by
  simp [State.spAligned, hsp, hsp_loc]

theorem extHookStack_split_4384 (sp0 : BitVec 64) :
    stackAt sp0 extHookStack =
      stackFrameAt sp0 4384 ∗
        (stackAt (sp0 - 4384#64) allocHookStack ∗
          stackFrameAt (sp0 - 4384#64 - 4096#64) 7904) := by
  unfold stackAt extHookStack allocHookStack
  change memRegion (sp0 - 16384#64) 16384 = _
  rw [← stackFrameAt_eq_memRegion sp0 16384 (by decide),
      ← stackFrameAt_eq_memRegion (sp0 - 4384#64) 4096 (by decide),
      show (16384 : Nat) = 4384 + 12000 from rfl,
      stackFrameAt_split sp0 4384 12000 (by decide),
      show (12000 : Nat) = 4096 + 7904 from rfl,
      stackFrameAt_split (sp0 - 4384#64) 4096 7904 (by decide)]

theorem allocHookStack_split_1120 (sp : BitVec 64) :
    stackAt sp allocHookStack = stackFrameAt sp 1120 ∗ stackFrameAt (sp - 1120#64) 2976 := by
  unfold stackAt allocHookStack
  rw [← stackFrameAt_eq_memRegion sp 4096 (by decide),
      show (4096 : Nat) = 1120 + 2976 from rfl, stackFrameAt_split sp 1120 2976 (by decide)]

theorem allocHookStack_split_256 (sp : BitVec 64) :
    stackAt sp allocHookStack = stackFrameAt sp 0x100 ∗ stackFrameAt (sp - 0x100#64) 3840 := by
  unfold stackAt allocHookStack
  rw [← stackFrameAt_eq_memRegion sp 4096 (by decide),
      show (4096 : Nat) = 256 + 3840 from rfl, stackFrameAt_split sp 256 3840 (by decide)]

theorem allocHookStack_split_208 (sp : BitVec 64) :
    stackAt sp allocHookStack = stackFrameAt sp 208 ∗ stackFrameAt (sp - 208#64) 3888 := by
  unfold stackAt allocHookStack
  rw [← stackFrameAt_eq_memRegion sp 4096 (by decide),
      show (4096 : Nat) = 208 + 3888 from rfl, stackFrameAt_split sp 208 3888 (by decide)]

theorem allocHookStack_split_16 (sp : BitVec 64) :
    stackAt sp allocHookStack = stackFrameAt sp 0x10 ∗ stackFrameAt (sp - 0x10#64) 4080 := by
  unfold stackAt allocHookStack
  rw [← stackFrameAt_eq_memRegion sp 4096 (by decide),
      show (4096 : Nat) = 16 + 4080 from rfl, stackFrameAt_split sp 16 4080 (by decide)]

theorem stackFrameAt_4384_eq (sp0 : BitVec 64) :
    let sp := sp0 - 4384#64
    stackFrameAt sp0 4384 =
      stackFrameAt sp0 96 ∗
      memRegion sp 64 ∗
      memRegion (sp + 0x040#64) 976 ∗
      memRegion (sp + 0x410#64) 960 ∗
      memRegion (sp + 0x7d0#64) 240 ∗
      memRegion (sp + 0x8c0#64) 960 ∗
      memRegion (sp + 0xc80#64) 16 ∗
      memRegion (sp + 0xc90#64) 960 ∗
      memRegion (sp + 0x1050#64) 16 ∗
      memRegion (sp + 0x1060#64) 12 ∗
      memRegion (sp + 0x106c#64) 64 ∗
      memRegion (sp + 0x10ac#64) 20 := by
  intro sp
  have htop : stackFrameAt sp0 4384 = stackFrameAt sp0 96 ∗ memRegion sp 4288 := by
    rw [show (4384 : Nat) = 96 + 4288 from rfl,
        stackFrameAt_split sp0 96 4288 (by decide),
        stackFrameAt_eq_memRegion (sp0 - 96#64) 4288 (by decide),
        show (sp0 - 96#64) - 4288#64 = sp by dsimp [sp]; bv_omega]
  rw [htop,
      show (4288 : Nat) = 64 + (976 + (960 + (240 + (960 + (16 + (960 + (16 + (12 + (64 + 20))))))))) from rfl,
      memRegion_split sp 64 _ (by decide), memRegion_split _ 976 _ (by decide),
      memRegion_split _ 960 _ (by decide), memRegion_split _ 240 _ (by decide),
      memRegion_split _ 960 _ (by decide), memRegion_split _ 16 _ (by decide),
      memRegion_split _ 960 _ (by decide), memRegion_split _ 16 _ (by decide),
      memRegion_split _ 12 _ (by decide), memRegion_split _ 64 20 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_976_split_probe (sp : BitVec 64) :
    memRegion (sp + 0x040#64) 976 =
      memRegion (sp + 0x040#64) 128 ∗
      (∃∗ w : BitVec 64, (sp + 0x0c0#64) ↦₆₄ w) ∗
      memRegion (sp + 0x0c8#64) 840 := by
  rw [show (976 : Nat) = 128 + (8 + 840) from rfl,
      memRegion_split (sp + 0x040#64) 128 848 (by decide),
      memRegion_split _ 8 840 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, memRegion_eight]

theorem memRegion_976_fold_probe (sp w : BitVec 64) :
    memRegion (sp + 0x040#64) 128 ∗ ((sp + 0x0c0#64) ↦₆₄ w) ∗ memRegion (sp + 0x0c8#64) 840 ⊢
      memRegion (sp + 0x040#64) 976 := by
  rw [memRegion_976_split_probe sp]
  exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right w (Entails.refl _)))

/-! ## 2. Saved Registers, Spill Slots, Byte Cells & `CbcKeyState` -/

@[expose] def cbcSavedCells (sp0 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ v0) ∗ ((sp0 - 88#64) ↦₆₄ v1) ∗
  ((sp0 - 80#64) ↦₆₄ v2) ∗ ((sp0 - 72#64) ↦₆₄ v3) ∗
  ((sp0 - 64#64) ↦₆₄ v4) ∗ ((sp0 - 56#64) ↦₆₄ v5) ∗
  ((sp0 - 48#64) ↦₆₄ v6) ∗ ((sp0 - 40#64) ↦₆₄ v7) ∗
  ((sp0 - 32#64) ↦₆₄ v8) ∗ ((sp0 - 24#64) ↦₆₄ v9) ∗
  ((sp0 - 16#64) ↦₆₄ v10) ∗ ((sp0 - 8#64) ↦₆₄ v11)

@[expose] def cbcSavedRegs (s0 : State) : SepProp :=
  cbcSavedCells s0.sp
    (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
    (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
    (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
    (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
    (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
    (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))

theorem stackFrameAt_96_cells (sp0 : BitVec 64) :
    stackFrameAt sp0 96 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       cbcSavedCells sp0 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont, cbcSavedCells]

theorem cbcSavedRegs_entails_stackFrameAt_96 (s0 : State) :
    cbcSavedRegs s0 ⊢ stackFrameAt s0.sp 96 := by
  rw [stackFrameAt_96_cells]; unfold cbcSavedRegs
  iterate 12 apply Entails.sepExists_right
  exact Entails.refl _

@[expose] def spill16Words (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 32) : SepProp :=
  (sp ↦₃₂ w0) ∗ ((sp + 4#64) ↦₃₂ w1) ∗
  ((sp + 8#64) ↦₃₂ w2) ∗ ((sp + 12#64) ↦₃₂ w3) ∗
  ((sp + 16#64) ↦₃₂ w4) ∗ ((sp + 20#64) ↦₃₂ w5) ∗
  ((sp + 24#64) ↦₃₂ w6) ∗ ((sp + 28#64) ↦₃₂ w7) ∗
  ((sp + 32#64) ↦₃₂ w8) ∗ ((sp + 36#64) ↦₃₂ w9) ∗
  ((sp + 40#64) ↦₃₂ w10) ∗ ((sp + 44#64) ↦₃₂ w11) ∗
  ((sp + 48#64) ↦₃₂ w12) ∗ ((sp + 52#64) ↦₃₂ w13) ∗
  ((sp + 56#64) ↦₃₂ w14) ∗ ((sp + 60#64) ↦₃₂ w15)

@[expose] def spill16At (sp : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  spill16Words sp
    ((bs.getD 0 0#8).zeroExtend 32) ((bs.getD 1 0#8).zeroExtend 32)
    ((bs.getD 2 0#8).zeroExtend 32) ((bs.getD 3 0#8).zeroExtend 32)
    ((bs.getD 4 0#8).zeroExtend 32) ((bs.getD 5 0#8).zeroExtend 32)
    ((bs.getD 6 0#8).zeroExtend 32) ((bs.getD 7 0#8).zeroExtend 32)
    ((bs.getD 8 0#8).zeroExtend 32) ((bs.getD 9 0#8).zeroExtend 32)
    ((bs.getD 10 0#8).zeroExtend 32) ((bs.getD 11 0#8).zeroExtend 32)
    ((bs.getD 12 0#8).zeroExtend 32) ((bs.getD 13 0#8).zeroExtend 32)
    ((bs.getD 14 0#8).zeroExtend 32) ((bs.getD 15 0#8).zeroExtend 32)

theorem memRegion_64_eq_pts32 (sp : BitVec 64) :
    memRegion sp 64 =
      (∃∗ w : BitVec 32, sp ↦₃₂ w) ∗ (∃∗ w : BitVec 32, (sp + 4#64) ↦₃₂ w) ∗
      (∃∗ w : BitVec 32, (sp + 8#64) ↦₃₂ w) ∗ (∃∗ w : BitVec 32, (sp + 12#64) ↦₃₂ w) ∗
      (∃∗ w : BitVec 32, (sp + 16#64) ↦₃₂ w) ∗ (∃∗ w : BitVec 32, (sp + 20#64) ↦₃₂ w) ∗
      (∃∗ w : BitVec 32, (sp + 24#64) ↦₃₂ w) ∗ (∃∗ w : BitVec 32, (sp + 28#64) ↦₃₂ w) ∗
      (∃∗ w : BitVec 32, (sp + 32#64) ↦₃₂ w) ∗ (∃∗ w : BitVec 32, (sp + 36#64) ↦₃₂ w) ∗
      (∃∗ w : BitVec 32, (sp + 40#64) ↦₃₂ w) ∗ (∃∗ w : BitVec 32, (sp + 44#64) ↦₃₂ w) ∗
      (∃∗ w : BitVec 32, (sp + 48#64) ↦₃₂ w) ∗ (∃∗ w : BitVec 32, (sp + 52#64) ↦₃₂ w) ∗
      (∃∗ w : BitVec 32, (sp + 56#64) ↦₃₂ w) ∗ (∃∗ w : BitVec 32, (sp + 60#64) ↦₃₂ w) := by
  change memRegion sp (4 + (4 + (4 + (4 + (4 + (4 + (4 + (4 + (4 + (4 + (4 + (4 + (4 + (4 + (4 + 4))))))))))))))) = _
  iterate 15 rw [memRegion_split _ 4 _ (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, memRegion_four]

theorem spill16Words_entails_memRegion_64 (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 32) :
    spill16Words sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ⊢ memRegion sp 64 := by
  rw [memRegion_64_eq_pts32]; unfold spill16Words
  repeat refine sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) ?_
  exact Entails.sepExists_right _ (Entails.refl _)

@[expose] def byte16Cells16 (p : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : SepProp :=
  (p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗ ((p + 3#64) ↦₈ b3) ∗
  ((p + 4#64) ↦₈ b4) ∗ ((p + 5#64) ↦₈ b5) ∗ ((p + 6#64) ↦₈ b6) ∗ ((p + 7#64) ↦₈ b7) ∗
  ((p + 8#64) ↦₈ b8) ∗ ((p + 9#64) ↦₈ b9) ∗ ((p + 10#64) ↦₈ b10) ∗ ((p + 11#64) ↦₈ b11) ∗
  ((p + 12#64) ↦₈ b12) ∗ ((p + 13#64) ↦₈ b13) ∗ ((p + 14#64) ↦₈ b14) ∗ ((p + 15#64) ↦₈ b15)

@[expose] def byte16At (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  byte16Cells16 p
    (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)
    (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8)
    (bs.getD 8 0#8) (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8)
    (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8) (bs.getD 15 0#8)

theorem pointsToBytes_16_list_eq_cells (p : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (p ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) =
      byte16Cells16 p b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, byte16Cells16]

theorem pointsToBytes_16_eq_byte16At (p : BitVec 64) {bs : List (BitVec 8)}
    (hbs : bs.length = 16) : (p ↦ₛ bs) = byte16At p bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hbs)
  exact pointsToBytes_16_list_eq_cells p b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15

theorem byte16At_eq_pointsTo128 (p : BitVec 64) {bs : List (BitVec 8)}
    (hbs : bs.length = 16) : byte16At p bs = (p ↦₁₂₈ bytesToU128LE bs) := by
  rw [← pointsToBytes_16_eq_byte16At p hbs, pointsToBytes16_eq_pointsTo128 hbs]

theorem byte16Cells16_entails_memRegion_16 (p : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    byte16Cells16 p b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 ⊢ memRegion p 16 := by
  rw [← pointsToBytes_16_list_eq_cells]; exact pointsToBytes_entails_memRegion p _

theorem byte16At_entails_memRegion_16 (p : BitVec 64) (bs : List (BitVec 8)) :
    byte16At p bs ⊢ memRegion p 16 := byte16Cells16_entails_memRegion_16 p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem memRegion_16_eq_pts8 (p : BitVec 64) :
    memRegion p 16 =
      (∃∗ b : BitVec 8, p ↦₈ b) ∗ (∃∗ b : BitVec 8, (p + 1#64) ↦₈ b) ∗
      (∃∗ b : BitVec 8, (p + 2#64) ↦₈ b) ∗ (∃∗ b : BitVec 8, (p + 3#64) ↦₈ b) ∗
      (∃∗ b : BitVec 8, (p + 4#64) ↦₈ b) ∗ (∃∗ b : BitVec 8, (p + 5#64) ↦₈ b) ∗
      (∃∗ b : BitVec 8, (p + 6#64) ↦₈ b) ∗ (∃∗ b : BitVec 8, (p + 7#64) ↦₈ b) ∗
      (∃∗ b : BitVec 8, (p + 8#64) ↦₈ b) ∗ (∃∗ b : BitVec 8, (p + 9#64) ↦₈ b) ∗
      (∃∗ b : BitVec 8, (p + 10#64) ↦₈ b) ∗ (∃∗ b : BitVec 8, (p + 11#64) ↦₈ b) ∗
      (∃∗ b : BitVec 8, (p + 12#64) ↦₈ b) ∗ (∃∗ b : BitVec 8, (p + 13#64) ↦₈ b) ∗
      (∃∗ b : BitVec 8, (p + 14#64) ↦₈ b) ∗ (∃∗ b : BitVec 8, (p + 15#64) ↦₈ b) := by
  change memRegion p (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))))))))) = _
  iterate 15 rw [memRegion_split _ 1 _ (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, memRegion_one]

@[expose] def CbcKeyState (sp : BitVec 64) (b : BitVec 8) (key : List (BitVec 8)) : SepProp :=
  if b == 1#8 then
    roundKeys15At (sp + 0xc90#64) (armv8ExpandKey key) ∗ memRegion (sp + 0xd80#64) 720
  else
    fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs key)

theorem cbcKeyState_entails_memRegion_960 (sp : BitVec 64) (b : BitVec 8) (key : List (BitVec 8)) :
    CbcKeyState sp b key ⊢ memRegion (sp + 0xc90#64) 960 := by
  unfold CbcKeyState
  by_cases hb : (b == 1#8) = true
  · simp only [hb, ↓reduceIte]
    rw [show (960 : Nat) = 240 + 720 from rfl,
        memRegion_split (sp + 0xc90#64) 240 720 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (roundKeys15At_entails_memRegion _ _)
  · simp only [Bool.not_eq_true _ ▸ hb, Bool.false_eq_true, ↓reduceIte]
    exact fsKeys256At_entails_memRegion _ _

@[expose] def inPad6Cells (inPtr u0 u1 u2 u3 u4 u5 : BitVec 64) : SepProp :=
  ((inPtr + 16#64) ↦₆₄ u0) ∗ ((inPtr + 24#64) ↦₆₄ u1) ∗
  ((inPtr + 32#64) ↦₆₄ u2) ∗ ((inPtr + 40#64) ↦₆₄ u3) ∗
  ((inPtr + 48#64) ↦₆₄ u4) ∗ ((inPtr + 56#64) ↦₆₄ u5)

theorem memRegion_48_eq_pts64 (inPtr : BitVec 64) :
    memRegion (inPtr + 16#64) 48 =
      (∃∗ u : BitVec 64, (inPtr + 16#64) ↦₆₄ u) ∗ (∃∗ u : BitVec 64, (inPtr + 24#64) ↦₆₄ u) ∗
      (∃∗ u : BitVec 64, (inPtr + 32#64) ↦₆₄ u) ∗ (∃∗ u : BitVec 64, (inPtr + 40#64) ↦₆₄ u) ∗
      (∃∗ u : BitVec 64, (inPtr + 48#64) ↦₆₄ u) ∗ (∃∗ u : BitVec 64, (inPtr + 56#64) ↦₆₄ u) := by
  change memRegion (inPtr + 16#64) (8 + (8 + (8 + (8 + (8 + 8))))) = _
  iterate 5 rw [memRegion_split _ 8 _ (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, memRegion_eight]

theorem inPad6_entails_memRegion_48 (inPtr u0 u1 u2 u3 u4 u5 : BitVec 64) :
    inPad6Cells inPtr u0 u1 u2 u3 u4 u5 ⊢ memRegion (inPtr + 16#64) 48 := by
  rw [memRegion_48_eq_pts64]; unfold inPad6Cells
  repeat refine sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) ?_
  exact Entails.sepExists_right _ (Entails.refl _)

theorem inPad6_zero_eq_pointsToBytes (inPtr : BitVec 64) :
    inPad6Cells inPtr 0#64 0#64 0#64 0#64 0#64 0#64 =
      ((inPtr + 16#64) ↦ₛ (List.replicate 16 0#8 ++ List.replicate 16 0#8 ++ List.replicate 16 0#8)) := by
  have hz8 : unpack64 0#64 = List.replicate 8 0#8 := by decide
  have hz48 : List.replicate 16 (0#8) ++ List.replicate 16 (0#8) ++ List.replicate 16 (0#8) =
      unpack64 0#64 ++ unpack64 0#64 ++ unpack64 0#64 ++
      unpack64 0#64 ++ unpack64 0#64 ++ unpack64 0#64 := by rw [hz8]; decide
  rw [hz48]; unfold inPad6Cells
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]

theorem pointsTo64_entails_memRegion_8 (a u : BitVec 64) :
    (a ↦₆₄ u) ⊢ memRegion a 8 := by
  rw [memRegion_eight]; exact Entails.sepExists_right u (Entails.refl _)

theorem vecU8_nonempty_pack {M : AllocCostModel} (A : RustCliAllocBudget M)
    (ret newPtr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt63 : bs.length < 2 ^ 63) (hne0 : newPtr ≠ 0#64) :
    let lenBv := BitVec.ofNat 64 bs.length
    (((ret ↦₆₄ lenBv) ∗ ((ret + 8#64) ↦₆₄ newPtr) ∗ ((ret + 16#64) ↦₆₄ lenBv)) ∗
      A.live newPtr bs.length 1 ∗ (newPtr ↦ₛ bs)) ⊢ vecU8 A.repAlloc ret bs := by
  intro lenBv
  have hlenNat : lenBv.toNat = bs.length := by
    dsimp only [lenBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcapNe : lenBv ≠ 0 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hlenNat] at this; change bs.length = 0 at this; omega
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right lenBv (Entails.sepExists_right newPtr ?_)
  simp only [hcapNe, ↓reduceIte, hlenNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  have hLiveEq : A.repAlloc.live newPtr bs.length 1 = A.live newPtr bs.length 1 := rfl
  rw [hLiveEq]
  refine Entails.trans (Entails.pure_right (φ := bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ newPtr ≠ 0)
    ⟨Nat.le_refl _, hlt63, hne0⟩ (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

theorem memRegion24_eq_pts (p : BitVec 64) :
    memRegion p 24 =
      (∃∗ r0 : BitVec 64, p ↦₆₄ r0) ∗ (∃∗ r1 : BitVec 64, (p + 8#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (p + 16#64) ↦₆₄ r2) := by
  change memRegion p (8 + (8 + 8)) = _
  rw [memRegion_split p 8 16 (by decide), memRegion_split (p + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, memRegion_eight]

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout

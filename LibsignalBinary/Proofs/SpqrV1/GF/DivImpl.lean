/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Verification of `<spqr::encoding::gf::GF16>::div_impl`

Proves fixed-offset (`0x552d0`) and relocatable `[LibsignalPlacement]` (Block `331`) subroutine
contracts for `<spqr::encoding::gf::GF16>::div_impl` against `GF16.divImpl`.
-/

public section

namespace CryptoVerification.SpqrV1.GF.DivImpl

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.AcceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

abbrev divImplName : String := "<spqr::encoding::gf::GF16>::div_impl"

/-- Total stack budget of `div_impl`: `0x30` (`48` bytes own frame) + `0x100` (`mul2U16Stack`). -/
abbrev divImplStack : Nat := 0x130

theorem stackAt_divImpl_split (sp : BitVec 64) :
    stackAt sp divImplStack =
      stackAt (sp - 48#64) mul2U16Stack ∗
      (∃∗ v0 : BitVec 64, (sp - 48#64) ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, (sp - 40#64) ↦₆₄ v1) ∗
      (∃∗ s29 : BitVec 64, (sp - 32#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 24#64) ↦₆₄ s30) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  have hbot : sp - BitVec.ofNat 64 (0x30 + mul2U16Stack) =
      sp - 48#64 - BitVec.ofNat 64 mul2U16Stack := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  show stackAt sp (0x30 + mul2U16Stack) = _
  rw [ProofLib.stackAt_split_bottom sp 0x30 mul2U16Stack (by decide), hbot]
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x30 = 48#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32)
        (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 48#64), memRegion_eight (sp - 40#64),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
      memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]

theorem stackAt_divImpl_merge (sp sp' v0 v1 s29 s30 s20 s19 : BitVec 64)
    (hsp : sp' = sp - 48#64) :
    stackAt sp' mul2U16Stack ∗
      ((sp - 48#64) ↦₆₄ v0) ∗
      ((sp - 40#64) ↦₆₄ v1) ∗
      ((sp - 32#64) ↦₆₄ s29) ∗
      ((sp - 24#64) ↦₆₄ s30) ∗
      ((sp - 16#64) ↦₆₄ s20) ∗
      ((sp - 8#64) ↦₆₄ s19) ⊢
      stackAt sp divImplStack := by
  subst hsp
  rw [stackAt_divImpl_split sp]
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_intro v0) ?_
  refine sepConj_mono (Entails.sepExists_intro v1) ?_
  refine sepConj_mono (Entails.sepExists_intro s29) ?_
  refine sepConj_mono (Entails.sepExists_intro s30) ?_
  refine sepConj_mono (Entails.sepExists_intro s20) ?_
  exact Entails.sepExists_intro s19

private theorem stackAt_mul2_split_once (sp : BitVec 64) :
    stackAt sp mul2U16Stack =
      memRegion (sp - 256#64) 96 ∗ stackAt sp 0xa0 := by
  show stackAt sp (0xa0 + 96) = _
  rw [ProofLib.stackAt_split_bottom sp 0xa0 96 (by decide)]

private theorem stackAt_mul2_merge_once (sp : BitVec 64) :
    memRegion (sp - 304#64) 96 ∗ stackAt (sp - 48#64) 0xa0 ⊢
      stackAt (sp - 48#64) mul2U16Stack := by
  rw [stackAt_mul2_split_once (sp - 48#64),
      show sp - 48#64 - 256#64 = sp - 304#64 by bv_arith]
  exact Entails.refl _

private def vmCore (s : State) :=
  (s.brkStart, s.brk, s.tpidrEl0, s.physMemAvail,
    fun fd : { fd : Nat // 3 ≤ fd ∧ fd < 2 ^ 31 } => s.fs.fds (BitVec.ofNat 64 fd.1))

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmPreserved_iff_vmCore (s s' : State) :
    LibsignalBinary.Heap.VmPreserved s s' ↔ (vmCore s' = vmCore s ∧ s'.mem.perm = s.mem.perm) := by
  unfold vmCore LibsignalBinary.Heap.VmPreserved LibsignalBinary.Heap.PoolPreserved
    LibsignalBinary.Heap.FdsHiFrame
  simp only [Prod.mk.injEq, funext_iff, Subtype.forall, and_imp]
  exact ⟨fun ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ => ⟨⟨h1, h2, h3, h4, h6⟩, h5⟩,
         fun ⟨⟨h1, h2, h3, h4, h6⟩, h5⟩ => ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩⟩

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_setPC (s : State) (pc : BitVec 64) : vmCore (s.setPC pc) = vmCore s := by
  unfold vmCore; cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_advancePC (s : State) : vmCore s.advancePC = vmCore s := by
  unfold vmCore; cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_setPState (s : State) (ps : PState) : vmCore (s.setPState ps) = vmCore s := by
  unfold vmCore; cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_setMem (s : State) (m : Memory) : vmCore (s.setMem m) = vmCore s := by
  unfold vmCore; cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    vmCore (s.writeReg64 r v) = vmCore s := by
  unfold vmCore; cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    vmCore (s.writeReg32 r v) = vmCore s := vmCore_writeReg64 s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_writeReg (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    vmCore (s.writeReg w r v) = vmCore s := by cases w <;> exact vmCore_writeReg64 s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    vmCore (applyWriteback s wb) = vmCore s := by
  cases wb with
  | none => rfl
  | some p => exact vmCore_writeReg64 s p.1 p.2

attribute [local irreducible] vmCore

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_setMem_loc (s : State) (m : Memory) : (s.setMem m).mem = m := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_setPC_loc (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_advancePC_loc (s : State) : s.advancePC.mem = s.mem := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_setPState_loc (s : State) (ps : PState) : (s.setPState ps).mem = s.mem := by
  cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_writeReg64_loc (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_writeReg32_loc (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).mem = s.mem := mem_writeReg64_loc s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_writeReg_loc (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).mem = s.mem := by cases w <;> exact mem_writeReg64_loc s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_applyWriteback_loc (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).mem = s.mem := by
  cases wb with
  | none => rfl
  | some p => exact mem_writeReg64_loc s p.1 p.2

private theorem mem_perm_setMem_of_nsp {s s' : State} {m : Memory}
    (h : ProofLib.NonSyscallPreserved s (s'.setMem m)) :
    m.perm = s.mem.perm :=
  h.2.1

attribute [local wp_norm] zeroExtend_16_truncate_32_64
attribute [local arm64_norm, local wp_norm]
  polyReduce_setWidth16_eq polyReduce_setWidth16_comm_eq mul2UnreducedWord_truncate32

@[local arm64_norm, local wp_norm]
private theorem polyReduce_asm_eq_trunc_div (a b_arg : BitVec 16) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
          (reduce.reduceByteEntry
            (BitVec.truncate 8
              ((unaccelerated.polyMul a b_arg ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<< 8) >>> 16))) ^^^
        (unaccelerated.polyMul a b_arg ^^^
          BitVec.zeroExtend 32
              (reduce.reduceByteEntry
                (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<< 8).zeroExtend 64) =
      unaccelerated.mul a b_arg := by
  rw [← zeroExtend_16_truncate_32_64]
  exact polyReduce_asm_eq a b_arg

@[local arm64_norm, local wp_norm]
private theorem zext64_trunc32_shr32_mul2Unreduced_div (a b1 b2 : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 32)) =
      (unaccelerated.polyMul a b1).zeroExtend 64 := by
  rw [mul2UnreducedWord_shr32]; bv_bits

@[local arm64_norm, local wp_norm]
private theorem trunc32_shr32_mul2Unreduced_div (a b1 b2 : BitVec 16) :
    BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 32) =
      unaccelerated.polyMul a b1 := by
  rw [mul2UnreducedWord_shr32]; bv_bits

/-- State `(square, out)` after `k` iterations of the `GF16::div_impl` loop.
Keeping this folded during symbolic execution prevents exponential term duplication
across the 15 unrolled `mul2_u16` calls. -/
private def divStep (other self : BitVec 16) : Nat → BitVec 16 × BitVec 16
  | 0 => (unaccelerated.mul other other, self)
  | k + 1 =>
    let p := divStep other self k
    mul2U16 p.1 p.1 p.2

@[local wp_norm]
private theorem divStep_one (other self : BitVec 16) :
    mul2U16 (unaccelerated.mul other other) (unaccelerated.mul other other) self =
      divStep other self 1 := rfl

@[local wp_norm]
private theorem divStep_succ (other self : BitVec 16) (k : Nat) :
    mul2U16 (divStep other self k).1 (divStep other self k).1 (divStep other self k).2 =
      divStep other self (k + 1) := rfl

@[local wp_norm]
private theorem divStep_15_snd (self other : GF16) :
    (divStep other.value self.value 15).2 = (GF16.divImpl self other).value := rfl

/-- Probed-postcondition variant of `divImplPlacedSpec` (post guarantees `tokenProbedPlacedAt`). -/
@[expose] def divImplPlacedProbedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × BitVec 64 × GF16 × GF16) where
  pre := fun (p_self, p_other, self, other) s =>
    ⌜s.readReg64 .x0 = p_self ∧
      s.readReg64 .x1 = p_other⌝ ∗
      (p_self ↦₁₆ self.value) ∗
      (p_other ↦₁₆ other.value) ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s.sp divImplStack
  post := fun (p_self, p_other, self, other) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (GF16.divImpl self other).value ∧
      sf.trace = s0.trace⌝ ∗
      (p_self ↦₁₆ self.value) ∗
      (p_other ↦₁₆ other.value) ∗
      tokenProbedPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s0.sp divImplStack

/-- Relocatable specification of `<spqr::encoding::gf::GF16>::div_impl` (Block `331`)
under `[LibsignalPlacement]`. -/
@[expose] def divImplPlacedSpec [LibsignalPlacement] : Spec (BitVec 64 × BitVec 64 × GF16 × GF16) where
  pre := fun (p_self, p_other, self, other) s =>
    ⌜s.readReg64 .x0 = p_self ∧
      s.readReg64 .x1 = p_other⌝ ∗
      (p_self ↦₁₆ self.value) ∗
      (p_other ↦₁₆ other.value) ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s.sp divImplStack
  post := fun (p_self, p_other, self, other) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (GF16.divImpl self other).value ∧
      sf.trace = s0.trace⌝ ∗
      (p_self ↦₁₆ self.value) ∗
      (p_other ↦₁₆ other.value) ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s0.sp divImplStack

set_option maxHeartbeats 1600000 in
private theorem divImpl_tail_64 [LibsignalPlacement]
    (H : String → Option (State → State))
    (hmul : subroutine_ok ((blkPC_331).rebase (blkPl_331).base H) (lsmpl.base 383)
      (withLsCl lsmpl (addVmPreservedAcc acceleratedMul2UnreducedPlacedSpec)))
    (hmul2 : subroutine_ok ((blkPC_331).rebase (blkPl_331).base H) (lsmpl.base 381)
      (withLsCl lsmpl (addVmPreserved mul2U16PlacedSpec)))
    (hmul2_probed : subroutine_ok ((blkPC_331).rebase (blkPl_331).base H) (lsmpl.base 381)
      (withLsCl lsmpl (addVmPreserved mul2U16PlacedProbedSpec)))
    (p_self p_other : BitVec 64) (self other : GF16) (s0 s1 : State)
    (v0 v1 : BitVec 64)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_331).base + 64#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 48#64)
    (hsp0_al : (s0.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hvm1 : LibsignalBinary.Heap.VmPreserved s0 s1)
    (hcs_v1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hx21_1 : s1.readReg64 .x21 = s0.readReg64 .x21)
    (hx22_1 : s1.readReg64 .x22 = s0.readReg64 .x22)
    (hx23_1 : s1.readReg64 .x23 = s0.readReg64 .x23)
    (hx24_1 : s1.readReg64 .x24 = s0.readReg64 .x24)
    (hx25_1 : s1.readReg64 .x25 = s0.readReg64 .x25)
    (hx26_1 : s1.readReg64 .x26 = s0.readReg64 .x26)
    (hx27_1 : s1.readReg64 .x27 = s0.readReg64 .x27)
    (hx28_1 : s1.readReg64 .x28 = s0.readReg64 .x28)
    (hx0_1 : BitVec.truncate 16 (s1.readReg64 .x0) = other.value)
    (hx1_1 : BitVec.truncate 16 (s1.readReg64 .x1) = other.value)
    (hx19_1 : s1.readReg64 .x19 = p_self)
    {post : State → SepProp → Prop}
    (hpost : ∀ sf Q,
      (Q ⊢ ⌜LibsignalBinary.Heap.VmPreserved s0 sf⌝ ∗
        ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (GF16.divImpl self other).value ∧
          sf.trace = s0.trace⌝ ∗
        (p_self ↦₁₆ self.value) ∗
        (p_other ↦₁₆ other.value) ∗
        tokenProbedPlacedAt ∗
        reduceTablePlacedAt ∗
        stackAt s0.sp divImplStack) →
      sf.sp = s0.sp → CallingConventionPreserved s0 sf → post sf Q) :
    SepWP ((blkPC_331).rebase (blkPl_331).base H) (s0.readReg64 .lr) s1
      ((p_self ↦₁₆ self.value) ∗
        (p_other ↦₁₆ other.value) ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        stackAt (s0.sp - 48#64) mul2U16Stack ∗
        ((s0.sp - 48#64) ↦₆₄ v0) ∗
        ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      post := by
  simp only [withLsCl, acceleratedMul2UnreducedPlacedSpec, mul2U16PlacedSpec,
    mul2U16PlacedProbedSpec] at hmul hmul2 hmul2_probed
  have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by
    rw [hsp1]; revert hsp0_al; bv_bits
  wp_steps 1
  wp_call hmul (other.value, other.value, 0#16)
  wp_steps 4
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16
          (BitVec.truncate 8 (unaccelerated.polyMul other.value other.value >>> 24)),
        uxtx1_hi_idx1_nomask_eq other.value other.value 0#16]
  wp_steps 1
  wp_conv_pre =>
    rw [← uxtx1_hi_idx1_nomask_eq other.value other.value 0#16,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8 (unaccelerated.polyMul other.value other.value >>> 24))]
  wp_steps 2
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul other.value other.value ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry
                      (BitVec.truncate 8 (unaccelerated.polyMul other.value other.value >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 1
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul other.value other.value ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry
                      (BitVec.truncate 8 (unaccelerated.polyMul other.value other.value >>> 24))) <<<
                  8) >>>
              16))]
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2_probed
  wp_steps
  refine SepWP.fold
    (stackAt_divImpl_merge s0.sp _ v0 v1
      (s0.readReg64 (Reg.gpr 29#5))
      (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 20#5))
      (s0.readReg64 (Reg.gpr 19#5))
      ?_)
    (by sep_focus)
    ?_
  · wp_norm_lhs
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  refine hpost _ _ ?_ (by wp_norm_lhs) ?_
  · refine Entails.pure_right (by simp_all [vmPreserved_iff_vmCore]) ?_
    refine Entails.pure_right (by simp_all [wp_norm]) ?_
    exact Entails.of_eq (by ac_rfl)
  · simp_all [CallingConventionPreserved, CalleeSavedPreserved, wp_norm]

set_option maxHeartbeats 1600000 in
/-- Relocatable `<spqr::encoding::gf::GF16>::div_impl` (Block `331`) meets
`withLsCodeLoaded lsmpl (addVmPreserved divImplPlacedProbedSpec)` under `[LibsignalPlacement]`. -/
theorem divImpl_vm_probed_placed_ok [LibsignalPlacement] (H : String → Option (State → State))
    (hOnce : OnceCallHookOk H) :
    subroutine_ok ((blkPC_331).rebase (blkPl_331).base H) (blkPl_331).base
      (withLsCodeLoaded lsmpl (addVmPreserved divImplPlacedProbedSpec)) := by
  have hmul0 : subroutine_ok ((blkPC_383).rebase (blkPl_383).base H) (lsmpl.base 383)
      (addVmPreservedAcc acceleratedMul2UnreducedPlacedSpec) :=
    acceleratedMul2Unreduced_vm_placed_ok H
  have hmul := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_331).rebase (blkPl_331).base H) hmul0
  have hmul20 : subroutine_ok ((blkPC_381).rebase (blkPl_381).base H) (lsmpl.base 381)
      (withLsCodeLoaded lsmpl (addVmPreserved mul2U16PlacedSpec)) :=
    mul2U16_vm_placed_ok H hOnce
  have hmul2 := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_331).rebase (blkPl_331).base H) hmul20
  have hmul2p0 : subroutine_ok ((blkPC_381).rebase (blkPl_381).base H) (lsmpl.base 381)
      (withLsCodeLoaded lsmpl (addVmPreserved mul2U16PlacedProbedSpec)) :=
    mul2U16_vm_probed_placed_ok H hOnce
  have hmul2p := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_331).rebase (blkPl_331).base H) hmul2p0
  have honce : subroutine_ok ((blkPC_331).rebase (blkPl_331).base H)
      (lsρ spqrOnceCallSym) spqrOnceCallGhostSpec :=
    spqr_onceCall_ok hOnce
  simp only [withLsCodeLoaded, divImplPlacedProbedSpec]
  wp_init args s0
  have halign := aligned_tokenOnce_placed
  wp_simp_pre [stackAt_divImpl_split, tokenInitPlacedAt]
  wp_pull_exists
  rename_i probed
  cases probed
  · -- Unprobed slow path (`probed = false`)
    wp_simp_pre [tokenUnprobedPlacedAt, stackAt_mul2_split_once]
    apply sepWP_seq_lscl h (mid := (blkPl_331).base + 64#64)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_331).rebase (blkPl_331).base (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H))
      blkLib_eq_331 (mid := (blkPl_331).base + 156#64)
    intro _m_strip
    wp_steps 7
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 13
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hperm0 := mem_perm_setMem_of_nsp _hnsp
    wp_call honce
    wp_steps
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl1
    apply SepWP.fold (stackAt_mul2_merge_once s0.sp) (by sep_focus)
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    refine SepWP.weaken_pre (by sep_focus)
      (divImpl_tail_64 H hmul hmul2 hmul2p args.1 args.2.1 args.2.2.1 args.2.2.2 s0 _ _ _ hcl1
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) hsp_align (by simp_all [wp_norm])
        (by simp_all [vmPreserved_iff_vmCore]) (by simp_all [wp_norm])
        (by simp_all [wp_norm]) (by simp_all [wp_norm]) (by simp_all [wp_norm])
        (by simp_all [wp_norm]) (by simp_all [wp_norm]) (by simp_all [wp_norm])
        (by simp_all [wp_norm]) (by simp_all [wp_norm])
        (by simp_all [wp_norm]) (by simp_all [wp_norm]) (by simp_all [wp_norm])
        (fun sf Q hent hsp_f hcc_f =>
          ⟨fun hm => Satisfies.of_entails hm
            (Entails.trans (sepConj_mono_left hent) (Entails.of_eq (by simp only [sepConj_assoc]))),
           hsp_f, hcc_f.2⟩))
  · -- Probed fast path (`probed = true`)
    wp_simp_pre [tokenProbedPlacedAt]
    apply sepWP_seq_lscl h (mid := (blkPl_331).base + 64#64)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_331).rebase (blkPl_331).base (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H))
      blkLib_eq_331 (mid := (blkPl_331).base + 64#64)
    intro _m_strip
    wp_steps 7
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign
    · wp_sep_access
    · wp_norm_lhs
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hperm0 := mem_perm_setMem_of_nsp _hnsp
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl1
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    refine SepWP.weaken_pre (by sep_focus)
      (divImpl_tail_64 H hmul hmul2 hmul2p args.1 args.2.1 args.2.2.1 args.2.2.2 s0 _ _ _ hcl1
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
        (by simp [vmPreserved_iff_vmCore, hperm0]) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp_all [wp_norm]) (by simp_all [wp_norm]) (by simp_all [wp_norm])
        (fun sf Q hent hsp_f hcc_f =>
          ⟨fun hm => Satisfies.of_entails hm
            (Entails.trans (sepConj_mono_left hent) (Entails.of_eq (by simp only [sepConj_assoc]))),
           hsp_f, hcc_f.2⟩))

/-- Relocatable `<spqr::encoding::gf::GF16>::div_impl` (Block `331`) meets
`withLsCodeLoaded lsmpl (addVmPreserved divImplPlacedSpec)` under `[LibsignalPlacement]`. -/
theorem divImpl_vm_placed_ok [LibsignalPlacement] (H : String → Option (State → State))
    (hOnce : OnceCallHookOk H) :
    subroutine_ok ((blkPC_331).rebase (blkPl_331).base H) (blkPl_331).base
      (withLsCodeLoaded lsmpl (addVmPreserved divImplPlacedSpec)) := by
  refine subroutine_ok_mono (divImpl_vm_probed_placed_ok H hOnce)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeLoaded, addVmPreserved, divImplPlacedProbedSpec, divImplPlacedSpec] at hq ⊢
  exact Satisfies.of_entails hq (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left tokenProbedPlacedAt_entails_init))))))

/-- Relocatable `<spqr::encoding::gf::GF16>::div_impl` (Block `331`) meets
`withLsCodeLoaded lsmpl divImplPlacedSpec` under `[LibsignalPlacement]`. -/
theorem divImpl_placed_ok [LibsignalPlacement] (H : String → Option (State → State))
    (hOnce : OnceCallHookOk H) :
    subroutine_ok ((blkPC_331).rebase (blkPl_331).base H) (blkPl_331).base
      (withLsCodeLoaded lsmpl divImplPlacedSpec) :=
  subroutine_ok_drop_vmPreserved (divImpl_vm_placed_ok H hOnce)

end CryptoVerification.SpqrV1.GF.DivImpl

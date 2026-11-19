/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.SpqrV1.GF.AcceleratedMul
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<Poly>::lagrange_interpolate_complete`: Binary Verification

Verifies `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete` (`0x61ec4`,
Block `373`) against `lagrangeCompleteSpec` and `lagrangeCompletePlacedSpec`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.LagrangeComplete

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.AcceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.DivImpl
open CryptoVerification.SpqrV1.Poly

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

attribute [local wp_norm] zeroExtend_16_truncate_32_64

@[local arm64_norm, local wp_norm]
private theorem ptr_sub_two_step_norm (ptr : BitVec 64) (rem : Nat) :
    ptr + BitVec.ofNat 64 (2 * (rem + 1)) + 0xfffffffffffffffe#64 =
      ptr + BitVec.ofNat 64 (2 * rem) :=
  ptr_sub_two_step ptr rem

@[local arm64_norm, local wp_norm]
private theorem ptr_sub_two_step_norm' (ptr : BitVec 64) (rem : Nat) :
    ptr + BitVec.ofNat 64 (2 * (rem + 1)) - 2#64 =
      ptr + BitVec.ofNat 64 (2 * rem) := by
  have h1 : BitVec.ofNat 64 (2 * (rem + 1)) = BitVec.ofNat 64 (2 * rem) + 2#64 := by
    rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add]
    congr 1
  rw [h1, ← BitVec.add_assoc, BitVec.add_sub_cancel]

@[local arm64_norm, local wp_norm]
private theorem truncate16_eor_zext32 (u : BitVec 16) (v : BitVec 64) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
        (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ^^^
         BitVec.zeroExtend 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 v)))) =
      u ^^^ BitVec.truncate 16 v := by
  ext i hi
  simp

@[local arm64_norm, local wp_norm]
private theorem truncate16_eor_zext_truncate32 (u : BitVec 16) (v : BitVec 64) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
        (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ^^^
         BitVec.zeroExtend 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 v)))) =
      u ^^^ BitVec.truncate 16 v := by
  ext i hi
  simp

@[local arm64_norm, local wp_norm]
private theorem truncate16_eor_zext64_truncate32 (u : BitVec 16) (v : BitVec 64) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 u ^^^ BitVec.zeroExtend 64 (BitVec.truncate 32 v)) =
      u ^^^ BitVec.truncate 16 v := by
  ext i hi
  simp

private theorem ule_of_lt_pts {i n : Nat} (hi : i < n) (hn : 4 * n < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 n) (BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

private theorem perm_to_denom (C P T R F : SepProp) :
    C ∗ P ∗ T ∗ R ∗ F = P ∗ T ∗ R ∗ C ∗ F := by
  rw [← sepConj_assoc C, sepConj_comm C P, sepConj_assoc P,
      ← sepConj_assoc C, sepConj_comm C T, sepConj_assoc T,
      ← sepConj_assoc C, sepConj_comm C R, sepConj_assoc R]

@[local arm64_norm, local wp_norm]
private theorem lsl_two_eq_four_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 2#64 = BitVec.ofNat 64 (4 * n) := lsl_two_eq_four_mul n

@[local arm64_norm, local wp_norm]
private theorem lsl_two_nat_eq_four_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 2 = BitVec.ofNat 64 (4 * n) := lsl_two_eq_four_mul n

@[local arm64_norm, local wp_norm]
private theorem lsl_one_eq_two_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 1#64 = BitVec.ofNat 64 (2 * n) := lsl_one_eq_two_mul n

@[local arm64_norm, local wp_norm]
private theorem lsl_one_nat_eq_two_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 1 = BitVec.ofNat 64 (2 * n) := lsl_one_eq_two_mul n

private theorem perm_to_div (S1 S2 T R St P C F : SepProp) :
    S1 ∗ S2 ∗ T ∗ R ∗ St ∗ P ∗ C ∗ F =
      C ∗ T ∗ R ∗ S1 ∗ S2 ∗ St ∗ P ∗ F := by
  rw [← sepConj_assoc P C F, sepConj_comm P C, sepConj_assoc C P F,
      ← sepConj_assoc St C, sepConj_comm St C, sepConj_assoc C St,
      ← sepConj_assoc R C, sepConj_comm R C, sepConj_assoc C R,
      ← sepConj_assoc T C, sepConj_comm T C, sepConj_assoc C T,
      ← sepConj_assoc S2 C, sepConj_comm S2 C, sepConj_assoc C S2,
      ← sepConj_assoc S1 C, sepConj_comm S1 C, sepConj_assoc C S1,
      ← sepConj_assoc S2 T, sepConj_comm S2 T, sepConj_assoc T S2,
      ← sepConj_assoc S1 T, sepConj_comm S1 T, sepConj_assoc T S1,
      ← sepConj_assoc S2 R, sepConj_comm S2 R, sepConj_assoc R S2,
      ← sepConj_assoc S1 R, sepConj_comm S1 R, sepConj_assoc R S1]

@[local arm64_norm, local wp_norm]
private theorem truncate16_zext64_truncate32 (v : BitVec 64) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 (BitVec.truncate 32 v)) =
      BitVec.truncate 16 v := by
  ext i hi; simp

attribute [local wp_norm] zeroExtend_16_truncate_32_64
attribute [local arm64_norm, local wp_norm]
  truncate16_zext64 Arm64.Obj.pageOf_add_lo12Of
  polyReduce_setWidth16_eq polyReduce_setWidth16_comm_eq mul2UnreducedWord_truncate32

@[local arm64_norm, local wp_norm]
private theorem zext64_trunc32_shr32_mul2Unreduced_lc (a b1 b2 : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 32)) =
      (unaccelerated.polyMul a b1).zeroExtend 64 := by
  rw [mul2UnreducedWord_shr32]; bv_bits

@[local arm64_norm, local wp_norm]
private theorem trunc32_shr32_mul2Unreduced_lc (a b1 b2 : BitVec 16) :
    BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 32) =
      unaccelerated.polyMul a b1 := by
  rw [mul2UnreducedWord_shr32]; bv_bits

@[local arm64_norm, local wp_norm]
private theorem polyReduce_asm_eq_trunc_lc (a b_arg : BitVec 16) :
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

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_local (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_local (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_local (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_local (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases s <;> cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_local (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

private theorem mem_perm_setMem_of_nsp {s s' : State} {m : Memory}
    (h : ProofLib.NonSyscallPreserved s (s'.setMem m)) :
    m.perm = s.mem.perm :=
  h.2.1

private theorem divImplStack_split_once (sp : BitVec 64) :
    stackAt sp divImplStack =
      memRegion (sp - 304#64) 144 ∗ stackAt sp 0xa0 := by
  show stackAt sp (0xa0 + 144) = _
  rw [ProofLib.stackAt_split_bottom sp 0xa0 144 (by decide)]

private theorem divImplStack_merge_once (sp : BitVec 64) :
    memRegion (sp - 304#64) 144 ∗ stackAt sp 0xa0 ⊢
      stackAt sp divImplStack := by
  rw [divImplStack_split_once sp]
  exact Entails.refl _

private theorem denomScratch_split (sp : BitVec 64) :
    memRegion sp 32 =
      memRegion sp 12 ∗
      (∃∗ v0 : BitVec 32, (sp + 12#64) ↦₃₂ v0) ∗
      (∃∗ v1 : BitVec 64, (sp + 16#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, (sp + 24#64) ↦₆₄ v2) := by
  rw [ProofLib.memRegion_split' (b := sp) (n := 12) (k := 20) (b' := sp + 12#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := sp + 12#64) (n := 4) (k := 16) (b' := sp + 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp + 16#64) (n := 8) (k := 8) (b' := sp + 24#64) rfl (by bv_arith) (by decide),
      memRegion_four (sp + 12#64), memRegion_eight (sp + 16#64), memRegion_eight (sp + 24#64)]

private theorem denomScratch_merge (sp : BitVec 64) (v0 : BitVec 32) (v1 v2 : BitVec 64) :
    memRegion sp 12 ∗
      ((sp + 12#64) ↦₃₂ v0) ∗
      ((sp + 16#64) ↦₆₄ v1) ∗
      ((sp + 24#64) ↦₆₄ v2) ⊢
      memRegion sp 32 := by
  rw [denomScratch_split sp]
  refine sepConj_mono_right (sepConj_mono (Entails.sepExists_intro v0) ?_)
  exact sepConj_mono (Entails.sepExists_intro v1) (Entails.sepExists_intro v2)

private theorem denomScratch_frame_eq (sp : BitVec 64) :
    memRegion (sp - 128#64) 32 =
      memRegion (sp - 128#64) 16 ∗
      (∃∗ s112 : BitVec 16, (sp - 112#64) ↦₁₆ s112) ∗ memRegion (sp - 110#64) 6 ∗
      (∃∗ s104 : BitVec 16, (sp - 104#64) ↦₁₆ s104) ∗ memRegion (sp - 102#64) 6 := by
  rw [ProofLib.memRegion_split' (b := sp - 128#64) (n := 16) (k := 16) (b' := sp - 112#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 112#64) (n := 2) (k := 14) (b' := sp - 110#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 110#64) (n := 6) (k := 8) (b' := sp - 104#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 104#64) (n := 2) (k := 6) (b' := sp - 102#64) rfl (by bv_arith) (by decide),
      memRegion_two (sp - 112#64), memRegion_two (sp - 104#64)]

private theorem denomScratch_of_frame (sp : BitVec 64) (s112 s104 : BitVec 16) :
    memRegion (sp - 128#64) 16 ∗
      ((sp - 112#64) ↦₁₆ s112) ∗ memRegion (sp - 110#64) 6 ∗
      ((sp - 104#64) ↦₁₆ s104) ∗ memRegion (sp - 102#64) 6 ⊢
      memRegion (sp - 128#64) 32 := by
  rw [denomScratch_frame_eq sp]
  refine sepConj_mono_right (sepConj_mono (Entails.sepExists_intro s112) ?_)
  exact sepConj_mono_right (sepConj_mono (Entails.sepExists_intro s104) (Entails.refl _))

set_option maxHeartbeats 1600000 in
private theorem denomLoop_vm_placed_sepWP [LibsignalPlacement] (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (ptsPtr : BitVec 64) (pts : List Pt) (hpts_len : 4 * pts.length < 2 ^ 64)
    (i : Nat) (hi : i < pts.length) (fsp : BitVec 64)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) (s0 : State) :
    ∀ (rem j : Nat) (_hrem : j + rem = pts.length) (acc : GF16)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_373).base + 84#64 →
      s.status = .Running →
      s.sp = fsp →
      (fsp &&& 15#64 == 0#64) = true →
      s.readReg64 .x29 = fsp + 32#64 →
      BitVec.truncate 16 (s.readReg64 .x0) = acc.value →
      s.readReg64 .x19 = ptsPtr + BitVec.ofNat 64 (4 * j) →
      s.readReg64 .x24 = lsρ tokenName + 8#64 →
      s.readReg64 .x25 = lsρ reduceTableSym →
      s.readReg64 .x26 = ptsPtr + BitVec.ofNat 64 (4 * i) →
      s.readReg64 .x27 = Obj.pageOf (lsρ tokenStorageName) →
      s.readReg64 .x28 = ptsPtr + BitVec.ofNat 64 (4 * pts.length) →
      vmCore s = vmCore s0 →
      s.mem.perm = s0.mem.perm →
      (∀ (sf : State),
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.pc = (blkPl_373).base + 256#64 →
        sf.status = .Running →
        sf.sp = fsp →
        sf.trace = s.trace →
        BitVec.truncate 16 (sf.readReg64 .x0) =
          ((pts.drop j).foldl (denomStep (pts[i]'hi).x) acc).value →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x22 = s.readReg64 .x22 →
        sf.readReg64 .x24 = lsρ tokenName + 8#64 →
        sf.readReg64 .x25 = s.readReg64 .x25 →
        sf.readReg64 .x26 = ptsPtr + BitVec.ofNat 64 (4 * i) →
        sf.readReg64 .x27 = Obj.pageOf (lsρ tokenStorageName) →
        sf.readReg64 .x28 = ptsPtr + BitVec.ofNat 64 (4 * pts.length) →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        vmCore sf = vmCore s0 →
        sf.mem.perm = s0.mem.perm →
        SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc sf
          (ptSliceAt ptsPtr pts ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
           stackAt fsp divImplStack ∗ memRegion fsp 32 ∗ F) Q) →
      SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc s
        (ptSliceAt ptsPtr pts ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
         stackAt fsp divImplStack ∗ memRegion fsp 32 ∗ F) Q := by
  intro rem
  induction rem with
  | zero =>
    intro j hrem acc s F hcl hpc hrun hsp hsp_align hx29 hx0 hx19 hx24 hx25 hx26 hx27 hx28 hvmc hvmp hnext
    have hj_eq : j = pts.length := by omega
    subst hj_eq
    wp_steps 2
    simp only [List.drop_length, List.foldl_nil] at hnext
    exact hnext _ hcl (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, hsp]) (by wp_norm_lhs)
      (by simpa [arm64_norm] using hx0) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm] using hx24) (by simp only [arm64_norm, wp_norm, hx25])
      (by simpa [arm64_norm] using hx26) (by simpa [arm64_norm] using hx27)
      (by simpa [arm64_norm] using hx28) (by simp only [arm64_norm, wp_norm]) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, hvmc]) (by simp only [arm64_norm, wp_norm, hvmp])
  | succ rem' ih =>
    intro j hrem acc s F hcl hpc hrun hsp hsp_align hx29 hx0 hx19 hx24 hx25 hx26 hx27 hx28 hvmc hvmp hnext
    have hj : j < pts.length := by omega
    have hdrop : pts.drop j = (pts[j]'hj) :: pts.drop (j + 1) := List.drop_eq_getElem_cons hj
    have halign_bd8 := aligned_tokenOnce_placed
    rcases ptr_sub_four_mul_ne_zero ptsPtr hj hpts_len with ⟨hne, hne'⟩
    wp_steps 2
    wp_simp_pre [ptSliceAt_focus_x hj ptsPtr]
    wp_steps 1
    wp_conv_pre =>
      rw [← sepConj_assoc, ← ptSliceAt_focus_x hj ptsPtr, ptSliceAt_focus_x hi ptsPtr, sepConj_assoc]
    wp_steps 1
    wp_conv_pre => rw [← sepConj_assoc, ← ptSliceAt_focus_x hi ptsPtr]
    wp_steps 1
    cases hpx : ((pts[i]'hi).x == (pts[j]'hj).x) with
    | false =>
      have hval_ne : (pts[i]'hi).x.value ≠ (pts[j]'hj).x.value := by
        intro heq
        have htrue : ((pts[i]'hi).x == (pts[j]'hj).x) = true := by rw [gf16_beq_iff, beq_iff_eq]; exact heq
        rw [hpx] at htrue; contradiction
      rcases cmp32_zext16_ne_zero _ _ hval_ne with ⟨hcmp1, hcmp2, hcmp3, hcmp4⟩
      have hmul := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
        (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl
      simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul
      have honce : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
          (lsρ spqrOnceCallSym) spqrOnceCallGhostSpec :=
        spqr_onceCall_ok hOnce
      let diff16 := (GF16.sub (pts[i]'hi).x (pts[j]'hj).x).value
      have heor :
          BitVec.truncate 16 (BitVec.zeroExtend 64 (pts[j]'hj).x.value ^^^ BitVec.zeroExtend 64 (pts[i]'hi).x.value) =
            diff16 := by
        change BitVec.truncate 16 (BitVec.zeroExtend 64 (pts[j]'hj).x.value ^^^ BitVec.zeroExtend 64 (pts[i]'hi).x.value) =
          (pts[i]'hi).x.value ^^^ (pts[j]'hj).x.value
        ext k hk; simp [Bool.xor_comm]
      apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_373).base + 84#64)
      wp_steps 1
      wp_simp_pre [tokenInitPlacedAt]
      wp_pull_exists
      rename_i probed
      cases probed
      · -- Unprobed slow path (`probed = false`)
        wp_simp_pre [tokenUnprobedPlacedAt, divImplStack_split_once, denomScratch_split]
        wp_pull_exists
        apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_373).base + 132#64)
        apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
          (Q := (blkPC_373).rebase (blkPl_373).base
            (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
          blkLib_eq_373 (mid := (blkPl_373).base + 224#64)
        intro _m_strip
        apply step_ldar32
        · wp_norm_lhs
        · wp_norm_lhs
        · wp_norm_lhs
        · wp_norm_lhs
        · wp_norm_lhs
        · exact halign_bd8
        · wp_sep_access
        · wp_norm_lhs
        wp_steps 14
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
        have hperm_once0 := (mem_perm_setMem_of_nsp _hnsp).trans hvmp
        wp_call honce
        wp_steps 6
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        intro hcl_once
        apply SepWP.fold (divImplStack_merge_once fsp) (by sep_focus)
        apply SepWP.fold (denomScratch_merge fsp _ _ _) (by sep_focus)
        apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
        have hmul_after := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
          (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl_once
        simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul_after
        wp_steps 1
        wp_call hmul_after (acc.value, diff16, 0#16)
        have _hx25_mul : sf_1.readReg64 .x25 = lsρ reduceTableSym := by simp only [arm64_norm, wp_norm, *]
        wp_steps 2
        wp_conv_pre =>
          rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul acc.value diff16 >>> 24)),
              uxtx1_hi_idx1_nomask_eq acc.value diff16 0#16]
        wp_steps 1
        wp_conv_pre =>
          rw [← uxtx1_hi_idx1_nomask_eq acc.value diff16 0#16,
              ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul acc.value diff16 >>> 24))]
        wp_steps 2
        wp_conv_pre =>
          rw [reduceTablePlacedAt_focus16
                (BitVec.truncate 8
                  ((unaccelerated.polyMul acc.value diff16 ^^^
                      BitVec.zeroExtend 32
                          (reduce.reduceByteEntry
                            (BitVec.truncate 8 (unaccelerated.polyMul acc.value diff16 >>> 24))) <<<
                        8) >>>
                    16)),
              uxtw1_idx2_eq]
        wp_steps 1
        wp_conv_pre =>
          rw [← uxtw1_idx2_eq,
              ← reduceTablePlacedAt_focus16
                (BitVec.truncate 8
                  ((unaccelerated.polyMul acc.value diff16 ^^^
                      BitVec.zeroExtend 32
                          (reduce.reduceByteEntry
                            (BitVec.truncate 8 (unaccelerated.polyMul acc.value diff16 >>> 24))) <<<
                        8) >>>
                    16))]
        wp_steps 1
        wp_step
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        intro hcl_next
        refine SepWP.weaken_pre (Entails.of_eq (show _ =
          ptSliceAt ptsPtr pts ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt fsp divImplStack ∗ memRegion fsp 32 ∗ F by ac_rfl)) ?_
        apply ih (j + 1) (by omega) (GF16.mul acc (GF16.sub (pts[i]'hi).x (pts[j]'hj).x)) _ F (by exact hcl_next)
        · wp_norm_lhs
        · wp_norm_lhs
        · simp only [arm64_norm, wp_norm, *]
        · exact hsp_align
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]; rfl
        · simp only [arm64_norm, wp_norm, *]; exact ptr_add_four_step ptsPtr j
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · intro sf' hcl_f hpc_f hrun_f hsp_f htr_f hx0_f hx20_f hx22_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregs_f hvmc_f hvmp_f
          refine hnext sf' hcl_f hpc_f hrun_f hsp_f ?_ ?_ ?_ ?_ hx24_f ?_ hx26_f hx27_f hx28_f ?_ ?_ hvmc_f hvmp_f
          · simp only [arm64_norm, wp_norm, *]
          · rw [hdrop, List.foldl_cons, denomStep]; simp only [hpx, Bool.false_eq_true, ↓reduceIte]; exact hx0_f
          · simp only [arm64_norm, wp_norm, *]
          · simp only [arm64_norm, wp_norm, *]
          · simp only [arm64_norm, wp_norm, *]
          · simp only [arm64_norm, wp_norm, *]
          · simp only [arm64_norm, wp_norm, *]
      · -- Probed fast path (`probed = true`)
        wp_simp_pre [tokenProbedPlacedAt]
        apply step_ldar32
        · wp_norm_lhs
        · wp_norm_lhs
        · exact blkPC_373_rebase_fetch_0x6c (blkPl_373).base (Rust.withPanics ext)
        · wp_norm_lhs
        · wp_norm_lhs
        · exact halign_bd8
        · wp_sep_access
        · wp_norm_lhs
        wp_steps 6
        apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
        wp_call hmul (acc.value, diff16, 0#16)
        have _hx25_mul : sf.readReg64 .x25 = lsρ reduceTableSym := by simp only [arm64_norm, wp_norm, *]
        wp_steps 2
        wp_conv_pre =>
          rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul acc.value diff16 >>> 24)),
              uxtx1_hi_idx1_nomask_eq acc.value diff16 0#16]
        wp_steps 1
        wp_conv_pre =>
          rw [← uxtx1_hi_idx1_nomask_eq acc.value diff16 0#16,
              ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul acc.value diff16 >>> 24))]
        wp_steps 2
        wp_conv_pre =>
          rw [reduceTablePlacedAt_focus16
                (BitVec.truncate 8
                  ((unaccelerated.polyMul acc.value diff16 ^^^
                      BitVec.zeroExtend 32
                          (reduce.reduceByteEntry
                            (BitVec.truncate 8 (unaccelerated.polyMul acc.value diff16 >>> 24))) <<<
                        8) >>>
                    16)),
              uxtw1_idx2_eq]
        wp_steps 1
        wp_conv_pre =>
          rw [← uxtw1_idx2_eq,
              ← reduceTablePlacedAt_focus16
                (BitVec.truncate 8
                  ((unaccelerated.polyMul acc.value diff16 ^^^
                      BitVec.zeroExtend 32
                          (reduce.reduceByteEntry
                            (BitVec.truncate 8 (unaccelerated.polyMul acc.value diff16 >>> 24))) <<<
                        8) >>>
                    16))]
        wp_steps 1
        wp_step
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        intro hcl_next
        refine SepWP.weaken_pre (Entails.of_eq (show _ =
          ptSliceAt ptsPtr pts ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt fsp divImplStack ∗ memRegion fsp 32 ∗ F by ac_rfl)) ?_
        apply ih (j + 1) (by omega) (GF16.mul acc (GF16.sub (pts[i]'hi).x (pts[j]'hj).x)) _ F (by exact hcl_next)
        · wp_norm_lhs
        · wp_norm_lhs
        · simp only [arm64_norm, wp_norm, *]
        · exact hsp_align
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]; rfl
        · simp only [arm64_norm, wp_norm, *]; exact ptr_add_four_step ptsPtr j
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · simp only [arm64_norm, wp_norm, *]
        · intro sf' hcl_f hpc_f hrun_f hsp_f htr_f hx0_f hx20_f hx22_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregs_f hvmc_f hvmp_f
          refine hnext sf' hcl_f hpc_f hrun_f hsp_f ?_ ?_ ?_ ?_ hx24_f ?_ hx26_f hx27_f hx28_f ?_ ?_ hvmc_f hvmp_f
          · simp only [arm64_norm, wp_norm, *]
          · rw [hdrop, List.foldl_cons, denomStep]; simp only [hpx, Bool.false_eq_true, ↓reduceIte]; exact hx0_f
          · simp only [arm64_norm, wp_norm, *]
          · simp only [arm64_norm, wp_norm, *]
          · simp only [arm64_norm, wp_norm, *]
          · simp only [arm64_norm, wp_norm, *]
          · simp only [arm64_norm, wp_norm, *]
    | true =>
      have hval_eq : (pts[i]'hi).x.value = (pts[j]'hj).x.value := by rw [gf16_beq_iff, beq_iff_eq] at hpx; exact hpx
      rcases cmp32_zext16_eq_zero _ _ hval_eq with ⟨hcmp1, hcmp2, hcmp3, hcmp4⟩
      wp_steps 1
      apply ih (j + 1) (by omega) acc _ F (by exact hcl)
      · wp_norm_lhs
      · wp_norm_lhs
      · simpa [arm64_norm, wp_norm] using hsp
      · exact hsp_align
      · simpa [arm64_norm, wp_norm] using hx29
      · simpa [arm64_norm, wp_norm] using hx0
      · simp only [arm64_norm, wp_norm]; exact ptr_add_four_step ptsPtr j
      · simpa [arm64_norm, wp_norm] using hx24
      · simpa [arm64_norm, wp_norm] using hx25
      · simpa [arm64_norm, wp_norm] using hx26
      · simpa [arm64_norm, wp_norm] using hx27
      · simpa [arm64_norm, wp_norm] using hx28
      · simp only [arm64_norm, wp_norm, hvmc]
      · simp only [arm64_norm, wp_norm, hvmp]
      · intro sf' hcl_f hpc_f hrun_f hsp_f htr_f hx0_f hx20_f hx22_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregs_f hvmc_f hvmp_f
        refine hnext sf' hcl_f hpc_f hrun_f hsp_f ?_ ?_ ?_ ?_ hx24_f ?_ hx26_f hx27_f hx28_f ?_ ?_ hvmc_f hvmp_f
        · simpa [arm64_norm, wp_norm] using htr_f
        · rw [hdrop, List.foldl_cons, denomStep]; simp only [hpx, ↓reduceIte]; exact hx0_f
        · simpa [arm64_norm, wp_norm] using hx20_f
        · simpa [arm64_norm, wp_norm] using hx22_f
        · simpa [arm64_norm, wp_norm] using hx25_f
        · simpa [arm64_norm, wp_norm] using hx29_f
        · simpa [arm64_norm, wp_norm] using hvregs_f

set_option maxHeartbeats 1600000 in
private theorem divLoop_vm_placed_sepWP [LibsignalPlacement] (ext : String → Option (State → State))
    (coeffsPtr : BitVec 64) (pix scale : GF16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) (s0 : State) :
    ∀ (rem : Nat) (cs : List GF16) (_hrem : rem + 1 < cs.length) (_hlen : 2 * cs.length < 2 ^ 64)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_373).base + 352#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      BitVec.truncate 16 (s.readReg64 .x19) = scale.value →
      BitVec.truncate 16 (s.readReg64 .x20) = pix.value →
      s.readReg64 .x21 = coeffsPtr + BitVec.ofNat 64 (2 * (rem + 1)) →
      s.readReg64 .x22 = BitVec.ofNat 64 (rem + 1) →
      s.readReg64 .x24 = lsρ tokenName + 8#64 →
      s.readReg64 .x25 = lsρ reduceTableSym →
      s.readReg64 .x27 = Obj.pageOf (lsρ tokenStorageName) →
      vmCore s = vmCore s0 →
      s.mem.perm = s0.mem.perm →
      (∀ (sf : State),
        sf.pc = (blkPl_373).base + 656#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        sf.trace = s.trace →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        vmCore sf = vmCore s0 →
        sf.mem.perm = s0.mem.perm →
        SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt coeffsPtr (divLoopPure pix scale (rem + 1) cs) ∗
           tokenProbedPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt coeffsPtr cs ∗ tokenProbedPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  intro rem
  induction rem with
  | zero =>
    intro cs hrem hlen s F hcl hpc hrun hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hvmc hvmp hnext
    have hrem1 : 1 < cs.length := hrem
    have halign_bd8 := aligned_tokenOnce_placed
    have hmul := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl
    simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul
    let cIdx := (cs[1]'hrem1).value
    apply sepWP_seq_lscl hcl (mid := (blkPl_373).base + 496#64)
    wp_simp_pre [gf16SliceAt_focus hrem1 coeffsPtr, tokenProbedPlacedAt]
    wp_steps 1
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 6
    apply SepWP.fold tokenProbedPlacedAt_fold (by sep_focus)
    wp_call hmul (cIdx, pix.value, 0#16)
    have _hx25_mul0 : sf.readReg64 .x25 = lsρ reduceTableSym := by simp only [arm64_norm, wp_norm, *]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul cIdx pix.value >>> 24)),
          uxtx1_hi_idx1_nomask_eq cIdx pix.value 0#16]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtx1_hi_idx1_nomask_eq cIdx pix.value 0#16,
          ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul cIdx pix.value >>> 24))]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul cIdx pix.value ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cIdx pix.value >>> 24))) <<<
                    8) >>>
                16)),
          uxtw1_idx2_eq]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtw1_idx2_eq,
          ← reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul cIdx pix.value ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cIdx pix.value >>> 24))) <<<
                    8) >>>
                16))]
    wp_steps 2
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl1
    have hmul1 := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl1
    simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul1
    wp_simp_pre [tokenProbedPlacedAt]
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 7
    apply SepWP.fold tokenProbedPlacedAt_fold (by sep_focus)
    wp_call hmul1 (cIdx, scale.value, 0#16)
    have _hx25_mul1 : sf_1.readReg64 .x25 = lsρ reduceTableSym := by simp only [arm64_norm, wp_norm, *]
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_373).rebase (blkPl_373).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_373 (mid := (blkPl_373).base + 656#64)
    intro _m_strip
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul cIdx scale.value >>> 24)),
          uxtx1_hi_idx1_nomask_eq cIdx scale.value 0#16]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtx1_hi_idx1_nomask_eq cIdx scale.value 0#16,
          ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul cIdx scale.value >>> 24))]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul cIdx scale.value ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cIdx scale.value >>> 24))) <<<
                    8) >>>
                16)),
          uxtw1_idx2_eq]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtw1_idx2_eq,
          ← reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul cIdx scale.value ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cIdx scale.value >>> 24))) <<<
                    8) >>>
                16))]
    wp_steps 2
    have hrem0 : 0 < (cs.set 1 ⟨unaccelerated.mul (cs[1]'hrem1).value scale.value⟩).length := by
      simp [List.length_set]; omega
    wp_conv_pre => rw [gf16SliceAt_update_one_assoc hrem1 coeffsPtr, gf16SliceAt_focus_assoc hrem0 coeffsPtr]
    wp_steps 6
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hperm_seg := mem_perm_setMem_of_nsp _hnsp
    have hlist :
        (cs.set 1 ⟨unaccelerated.mul (cs[1]'hrem1).value scale.value⟩).set 0
          ⟨((cs.set 1 ⟨unaccelerated.mul (cs[1]'hrem1).value scale.value⟩)[0]'hrem0).value ^^^
            unaccelerated.mul (cs[1]'hrem1).value pix.value⟩ =
        divLoopPure pix scale (0 + 1) cs := by
      simpa [divLoopPure] using divLoop_step_eq pix scale 0 cs hrem
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem0 coeffsPtr, hlist]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      gf16SliceAt coeffsPtr (divLoopPure pix scale (0 + 1) cs) ∗
      tokenProbedPlacedAt ∗ reduceTablePlacedAt ∗ F by ac_rfl)) ?_
    exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
  | succ rem' ih =>
    intro cs hrem hlen s F hcl hpc hrun hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hvmc hvmp hnext
    have halign_bd8 := aligned_tokenOnce_placed
    rcases bv_sub_one_succ rem' (by omega) with ⟨hsub1, hsub2, hsub3⟩
    have hmul := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl
    simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul
    let cIdx := (cs[rem' + 1 + 1]'hrem).value
    apply sepWP_seq_lscl hcl (mid := (blkPl_373).base + 496#64)
    wp_simp_pre [gf16SliceAt_focus hrem coeffsPtr, tokenProbedPlacedAt]
    wp_steps 1
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 6
    apply SepWP.fold tokenProbedPlacedAt_fold (by sep_focus)
    wp_call hmul (cIdx, pix.value, 0#16)
    have _hx25_mul0 : sf.readReg64 .x25 = lsρ reduceTableSym := by simp only [arm64_norm, wp_norm, *]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul cIdx pix.value >>> 24)),
          uxtx1_hi_idx1_nomask_eq cIdx pix.value 0#16]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtx1_hi_idx1_nomask_eq cIdx pix.value 0#16,
          ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul cIdx pix.value >>> 24))]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul cIdx pix.value ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cIdx pix.value >>> 24))) <<<
                    8) >>>
                16)),
          uxtw1_idx2_eq]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtw1_idx2_eq,
          ← reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul cIdx pix.value ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cIdx pix.value >>> 24))) <<<
                    8) >>>
                16))]
    wp_steps 2
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl1
    have hmul1 := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl1
    simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul1
    apply sepWP_seq_lscl hcl1 (mid := (blkPl_373).base + 352#64)
    wp_simp_pre [tokenProbedPlacedAt]
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 7
    apply SepWP.fold tokenProbedPlacedAt_fold (by sep_focus)
    wp_call hmul1 (cIdx, scale.value, 0#16)
    have _hx25_mul1 : sf_1.readReg64 .x25 = lsρ reduceTableSym := by simp only [arm64_norm, wp_norm, *]
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_373).rebase (blkPl_373).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_373 (mid := (blkPl_373).base + 352#64)
    intro _m_strip
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul cIdx scale.value >>> 24)),
          uxtx1_hi_idx1_nomask_eq cIdx scale.value 0#16]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtx1_hi_idx1_nomask_eq cIdx scale.value 0#16,
          ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul cIdx scale.value >>> 24))]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul cIdx scale.value ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cIdx scale.value >>> 24))) <<<
                    8) >>>
                16)),
          uxtw1_idx2_eq]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtw1_idx2_eq,
          ← reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul cIdx scale.value ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cIdx scale.value >>> 24))) <<<
                    8) >>>
                16))]
    wp_steps 2
    have hrem1 : rem' + 1 < (cs.set (rem' + 1 + 1) ⟨unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩).length := by
      simp [List.length_set]; omega
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem coeffsPtr, gf16SliceAt_focus_assoc hrem1 coeffsPtr]
    wp_steps 6
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hperm_seg := mem_perm_setMem_of_nsp _hnsp
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl2 => ?_
    let cs_next :=
      let cIdx := cs[rem' + 1 + 1]?.getD GF16.ZERO
      let cPrev := cs[rem' + 1]?.getD GF16.ZERO
      let negativeDelta := GF16.mul cIdx pix
      let coeffs1 := cs.set (rem' + 1 + 1) (GF16.mul cIdx scale)
      coeffs1.set (rem' + 1) (GF16.add cPrev negativeDelta)
    have hlist :
        (cs.set (rem' + 1 + 1) ⟨unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩).set (rem' + 1)
          ⟨((cs.set (rem' + 1 + 1) ⟨unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩)[rem' + 1]'hrem1).value ^^^
            unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value pix.value⟩ =
        cs_next := divLoop_step_eq pix scale (rem' + 1) cs hrem
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem1 coeffsPtr, hlist]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      gf16SliceAt coeffsPtr cs_next ∗
      tokenProbedPlacedAt ∗ reduceTablePlacedAt ∗ F by ac_rfl)) ?_
    apply ih cs_next (by simp [cs_next, List.length_set]; omega) (by simp [cs_next, List.length_set]; omega) _ F hcl2
    · wp_norm_lhs
    · wp_norm_lhs
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · wp_norm_lhs
    · simp [arm64_norm, wp_norm]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · intro sf' hpc_f hrun_f hsp_f htr_f hvregs_f hvmc_f hvmp_f
      exact hnext sf' hpc_f hrun_f
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        hvmc_f hvmp_f

set_option maxHeartbeats 1600000 in
/-- Relocatable `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete` (Block `373`)
meets `withLsCodeLoaded lsmpl (addVmPreserved lagrangeCompletePlacedSpec)` under
`[LibsignalPlacement]`. -/
theorem lagrangeComplete_vm_placed_ok [LibsignalPlacement] (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (addVmPreserved lagrangeCompletePlacedSpec)) := by
  simp only [withLsCodeLoaded, lagrangeCompletePlacedSpec]
  wp_init x s0
  have hule_i : BitVec.ule (BitVec.ofNat 64 x.pts.length) (BitVec.ofNat 64 x.i) = false :=
    ule_of_lt_pts h_7 h_1
  wp_simp_pre [stackAt_lagrangeComplete_split]
  wp_pull_exists
  apply sepWP_seq_lscl h (mid := (blkPl_373).base + 84#64)
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_373).rebase (blkPl_373).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    blkLib_eq_373 (mid := (blkPl_373).base + 84#64)
  intro _m_strip
  wp_steps 21
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hperm0 := mem_perm_setMem_of_nsp _hnsp
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl0 => ?_
  apply SepWP.fold (denomScratch_of_frame s0.sp _ _) (by sep_focus)
  apply SepWP.fold (Entails.refl (ptSliceAt x.ptsPtr x.pts ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
    stackAt (s0.sp - 128#64) divImplStack ∗ memRegion (s0.sp - 128#64) 32)) (by sep_focus)
  wp_conv_pre => simp only [sepConj_assoc]
  apply denomLoop_vm_placed_sepWP ext hOnce x.ptsPtr x.pts h_1 x.i h_7 (s0.sp - 128#64) (s0.readReg64 .lr) _ s0
    x.pts.length 0 (by omega) GF16.ONE _ _ hcl0
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp_align
  · simp [arm64_norm, wp_norm]
  · rfl
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp only [arm64_norm, wp_norm]
  · simp only [arm64_norm, wp_norm, *]
  · intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hx0_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1 hvmc1 hvmp1
    simp only [arm64_norm, wp_norm] at hsp1 htr1 hx20_1 hx22_1 hx25_1 hx29_1 hvregs1
    simp only [List.drop_zero, ← lagrangeDenominator_eq_foldl] at hx0_1
    wp_simp_pre [denomScratch_frame_eq]
    wp_pull_exists
    apply sepWP_seq_lscl hcl1 (mid := (blkPl_373).base + 280#64)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_373).rebase (blkPl_373).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_373 (mid := (blkPl_373).base + 280#64)
    intro _m_strip_mid
    wp_simp_pre [ptSliceAt_focus_y h_7 x.ptsPtr]
    wp_steps 7
    wp_conv_pre =>
      rw [← sepConj_assoc ((x.ptsPtr + BitVec.ofNat 64 (4 * x.i) + 2#64) ↦₁₆ _),
          ← ptSliceAt_focus_y h_7 x.ptsPtr]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real_mid _hnsp_mid => ?_
    have hperm_mid := (mem_perm_setMem_of_nsp _hnsp_mid).trans hvmp1
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_div => ?_
    have hdiv_call := lscall_blk_cl (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (divImpl_vm_probed_placed_ok (Rust.withPanics ext) hOnce) hcl_div
    simp only [withMemEq, divImplPlacedProbedSpec] at hdiv_call
    apply sepWP_seq_lscl hcl_div (mid := (blkPl_373).base + 284#64)
    wp_call hdiv_call
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl2
    wp_steps 2
    by_cases hlen2 : x.self.coefficients.length < 2
    · have hult2 : (BitVec.ofNat 64 x.self.coefficients.length).ult 2#64 = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : x.self.coefficients.length < 2 ^ 64), decide_eq_true_eq]
        omega
      have hpure_eq : (lagrangeCompletePure x.self x.pts x.i).coefficients = x.self.coefficients := by
        have hsub0 : x.self.coefficients.length - 1 = 0 := by omega
        simp [lagrangeCompletePure, List.getElem?_eq_getElem h_7, hsub0, divLoopPure]
      wp_conv_pre => rw [hsp1]
      wp_steps
      apply SepWP.fold tokenProbedPlacedAt_entails_init (by sep_focus)
      refine SepWP.fold
        (stackAt_lagrangeComplete_merge s0.sp (s0.sp - 128#64) (x.pts[x.i]'h_7).y.value
          (Poly.lagrangeDenominator (x.pts[x.i]'h_7).x x.pts).value
          (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
          (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
          (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
          (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
          (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
          (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)) rfl)
        (by sep_focus) ?_
      rw [hpure_eq]; wp_done
    · have hult2 : (BitVec.ofNat 64 x.self.coefficients.length).ult 2#64 = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : x.self.coefficients.length < 2 ^ 64), decide_eq_false_iff_not]
        omega
      wp_conv_pre => rw [ptSliceAt_focus_x h_7 x.ptsPtr]
      wp_steps 8
      wp_conv_pre => rw [← ptSliceAt_focus_x h_7 x.ptsPtr]
      apply SepWP.fold (Entails.refl (gf16SliceAt x.coeffsPtr x.self.coefficients ∗
        tokenProbedPlacedAt ∗ reduceTablePlacedAt)) (by sep_focus)
      wp_conv_pre => simp only [sepConj_assoc]
      let rem := x.self.coefficients.length - 2
      have hrem_eq : rem + 1 + 1 = x.self.coefficients.length := by omega
      let pix := (x.pts[x.i]'h_7).x
      let scale := (x.pts[x.i]'h_7).y.divImpl (Poly.lagrangeDenominator pix x.pts)
      apply divLoop_vm_placed_sepWP ext x.coeffsPtr pix scale (s0.readReg64 .lr) _ s0
        rem x.self.coefficients (by omega) h_8 _ _ (by exact hcl2)
      · wp_norm_lhs
      · wp_norm_lhs
      · simp only [arm64_norm, wp_norm, *]
      · simp only [arm64_norm, wp_norm, truncate16_zext64_truncate32, *]; rfl
      · simp only [arm64_norm, wp_norm, truncate16_zext64]; rfl
      · simp only [arm64_norm, wp_norm, ← hrem_eq, ptr_sub_two_step_norm']
      · simp only [arm64_norm, wp_norm, ← hrem_eq]
        rw [show (rem + 1 + 1 : Nat) = (rem + 1) + 1 from rfl,
            BitVec.ofNat_add, show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.add_sub_cancel]
      · simp only [arm64_norm, wp_norm, *]
      · simp only [arm64_norm, wp_norm, *]
      · simp only [arm64_norm, wp_norm, *]
      · simp only [arm64_norm, wp_norm, *]
      · simp only [arm64_norm, wp_norm, *]
      · intro s2 hpc2 hrun2 hsp2 htr2 hvregs2 hvmc2 hvmp2
        have hpure_eq :
            divLoopPure pix scale (rem + 1) x.self.coefficients =
              (lagrangeCompletePure x.self x.pts x.i).coefficients := by
          have hsub1 : rem + 1 = x.self.coefficients.length - 1 := by omega
          have hnotle1 : ¬ x.self.coefficients.length ≤ 1 := by omega
          simp [lagrangeCompletePure, List.getElem?_eq_getElem h_7, hsub1, hnotle1, GF16.div, pix, scale]
        have hsp2' : s2.sp = s0.sp - 128#64 := by simp only [arm64_norm, wp_norm, *]
        have htr2' : s2.trace = s0.trace := by simp only [arm64_norm, wp_norm, *]
        have hvregs2' : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
          simp only [arm64_norm, wp_norm, *]
        clear hsp2 htr2 hvregs2
        wp_conv_pre => rw [hsp1, hpure_eq]
        wp_steps
        apply SepWP.fold tokenProbedPlacedAt_entails_init (by sep_focus)
        refine SepWP.fold
          (stackAt_lagrangeComplete_merge s0.sp (s0.sp - 128#64) (x.pts[x.i]'h_7).y.value
            (Poly.lagrangeDenominator (x.pts[x.i]'h_7).x x.pts).value
            (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
            (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
            (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
            (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
            (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
            (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)) rfl)
          (by sep_focus) ?_
        wp_done

theorem lagrangeComplete_placed_ok [LibsignalPlacement] (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl lagrangeCompletePlacedSpec) :=
  subroutine_ok_drop_vmPreserved (lagrangeComplete_vm_placed_ok ext hOnce)

end CryptoVerification.SpqrV1.Poly.LagrangeComplete

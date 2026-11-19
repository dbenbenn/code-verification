/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.GF.GfCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.SpqrV1.GF.IsNonZero

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout

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

abbrev isNonZeroName : String := "spqr::util::is_non_zero"

theorem stackAt_16_split_byte12 (sp : BitVec 64) :
    stackAt sp 0x10 =
      memRegion (sp - 16#64) 12 ∗
      (∃∗ b0 : BitVec 8, (sp - 4#64) ↦₈ b0) ∗
      memRegion (sp - 3#64) 3 := by
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x10 = 16#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 12) (k := 4)
        (b' := sp - 4#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 4#64) (n := 1) (k := 3)
        (b' := sp - 3#64) rfl (by bv_arith) (by decide),
      memRegion_one (sp - 4#64)]

theorem stackAt_16_merge_byte12 (sp : BitVec 64) (b0 : BitVec 8) :
    memRegion (sp - 16#64) 12 ∗ ((sp - 4#64) ↦₈ b0) ∗ memRegion (sp - 3#64) 3 ⊢
      stackAt sp 0x10 := by
  rw [stackAt_16_split_byte12 sp]
  refine sepConj_mono_right (sepConj_mono_left ?_)
  exact Entails.sepExists_intro b0

/-- Bridge from the AArch64 instruction sequence (`sub w8, wzr, w0, uxtb; lsr w8, w8, #31`)
to the model `isNonZero v`. -/
@[local arm64_norm, local wp_norm]
theorem isNonZero_asm_eq (v : BitVec 8) :
    BitVec.zeroExtend 64
      (BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (0#32 - BitVec.zeroExtend 32 v) >>> 31)) =
    BitVec.zeroExtend 64 (isNonZero v) := by
  revert v
  decide +kernel

/-- Specification of `spqr::util::is_non_zero` (`0x639e8`).
Accepts any 64-bit register `.x0` whose low byte is `v`, and returns `(isNonZero v).zeroExtend 64`
in `.x0` (so `.w0 = (isNonZero v).zeroExtend 32`). -/
@[expose] def isNonZeroSpec : Spec (BitVec 8) where
  pre := fun v s =>
    ⌜BitVec.truncate 8 (s.readReg64 .x0) = v⌝ ∗ stackAt s.sp 0x10
  post := fun v s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.zeroExtend 64 (isNonZero v) ∧ sf.trace = s0.trace⌝ ∗
      stackAt s0.sp 0x10

/-- Relocatable `spqr::util::is_non_zero` (Block `380`) meets `isNonZeroSpec` under `[LibsignalPlacement]`. -/
theorem isNonZero_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_380).rebase (blkPl_380).base H) (blkPl_380).base isNonZeroSpec := by
  simp only [isNonZeroSpec]
  wp_init v s0
  wp_simp_pre [stackAt_16_split_byte12]
  wp_pull_exists
  wp_steps
  apply SepWP.fold
    (stackAt_16_merge_byte12 s0.sp
      (BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (0#32 - BitVec.zeroExtend 32 v) >>> 31)))
    (by sep_focus)
  wp_done

end CryptoVerification.SpqrV1.GF.IsNonZero

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.From
import ProofLib.SepLogic.WPp

/-!
# Verification of `prost::encoding::varint::decode_varint_slow`

Verifies the 10-byte slow-path LEB128 varint decoder `decode_varint_slow::<&mut &[u8]>` against
`decodeVarintSlowSpec`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre' (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre' (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre' (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre' (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre' (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre' (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre' (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre' (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre' (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_pre' (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := rfl

theorem allocFailedIn_trans {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  simpa only [allocFailedIn, htr] using h

theorem memRegion_48_split (a : BitVec 64) :
    memRegion a 48 = (∃∗ v : BitVec 64, a ↦₆₄ v) ∗ memRegion (a + 8#64) 40 := by
  rw [← memRegion_eight, ← memRegion_split a 8 40 (by decide)]

theorem stackAt_varintSlow (sp : BitVec 64) :
    stackAt sp varintSlowStack =
      stackAt (sp - 64#64) decodeErrorHookStack ∗
        memRegion (sp - 56#64) 40 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v8 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v8) ∗ ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := stackAt_split_cells sp decodeErrorHookStack 8 (by decide)
  rw [← memRegion_cells (sp - BitVec.ofNat 64 (8 * 8)) 8 (by decide)] at h0
  change stackAt sp varintSlowStack =
    stackAt (sp - 64#64) decodeErrorHookStack ∗ memRegion (sp - 64#64) 64 at h0
  have s1 := memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s1
  have s2 := memRegion_split (sp - 56#64) 40 16 (by decide)
  rw [bv_sub_add_lit sp 56 40] at s2
  have s3 := memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s3
  rw [h0, s1, s2, s3,
    memRegion_eight (sp - 64#64), memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem toNat_le_0x7f_iff (b : BitVec 8) : b.toNat ≤ 0x7f ↔ b ≤ 0x7f#8 := Iff.rfl

theorem two_le_toNat_iff (b : BitVec 8) : 2 ≤ b.toNat ↔ 2#8 ≤ b := Iff.rfl

theorem getLsbD_7_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    b.getLsbD 7 = false := by revert h; revert b; decide +kernel

theorem getLsbD_7_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    b.getLsbD 7 = true := by revert h; revert b; decide +kernel

theorem getLsbD_7_beq_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    (b.getLsbD 7 == true) = false := by
  rw [getLsbD_7_of_le h]; rfl

theorem getLsbD_7_beq_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    (b.getLsbD 7 == true) = true := by
  rw [getLsbD_7_of_gt h]; rfl

theorem signExtend32_getLsbD_31_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    (b.signExtend 32).getLsbD 31 = false := by revert h; revert b; decide +kernel

theorem signExtend32_getLsbD_31_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    (b.signExtend 32).getLsbD 31 = true := by revert h; revert b; decide +kernel

theorem signExtend32_getLsbD_31_beq_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    ((b.signExtend 32).getLsbD 31 == true) = false := by
  rw [signExtend32_getLsbD_31_of_le h]; rfl

theorem signExtend32_getLsbD_31_beq_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    ((b.signExtend 32).getLsbD 31 == true) = true := by
  rw [signExtend32_getLsbD_31_of_gt h]; rfl

theorem signExtend64_getLsbD_63_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    (b.signExtend 64).getLsbD 63 = false := by revert h; revert b; decide +kernel

theorem signExtend64_getLsbD_63_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    (b.signExtend 64).getLsbD 63 = true := by revert h; revert b; decide +kernel

theorem signExtend64_getLsbD_63_beq_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    ((b.signExtend 64).getLsbD 63 == true) = false := by
  rw [signExtend64_getLsbD_63_of_le h]; rfl

theorem signExtend64_getLsbD_63_beq_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    ((b.signExtend 64).getLsbD 63 == true) = true := by
  rw [signExtend64_getLsbD_63_of_gt h]; rfl

theorem byte9_hi_of_ge {b9 : BitVec 8} (hb9 : 2#8 ≤ b9) :
    (1#32).ult (BitVec.truncate 32 (BitVec.signExtend 64 b9)) = true := by
  revert hb9; revert b9; decide +kernel

theorem byte9_hi_of_lt {b9 : BitVec 8} (_hb9 : b9 ≤ 0x7f#8) (hb9_lt : ¬ 2#8 ≤ b9) :
    (1#32).ult (BitVec.truncate 32 (BitVec.signExtend 64 b9)) = false := by
  revert hb9_lt _hb9; revert b9; decide +kernel

theorem ofNat_ne_ofNat {n k : Nat} (hne : n ≠ k) (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ BitVec.ofNat 64 k := by
  rw [ne_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change n % 2 ^ 64 ≠ k % 2 ^ 64
  omega

abbrev vAcc1 (b0 : BitVec 8) : BitVec 64 :=
  0#64 ||| ((b0 &&& 0x7f#8).zeroExtend 64 <<< 0)
abbrev vAcc2 (b0 b1 : BitVec 8) : BitVec 64 :=
  vAcc1 b0 ||| ((b1 &&& 0x7f#8).zeroExtend 64 <<< 7)
abbrev vAcc3 (b0 b1 b2 : BitVec 8) : BitVec 64 :=
  vAcc2 b0 b1 ||| ((b2 &&& 0x7f#8).zeroExtend 64 <<< 14)
abbrev vAcc4 (b0 b1 b2 b3 : BitVec 8) : BitVec 64 :=
  vAcc3 b0 b1 b2 ||| ((b3 &&& 0x7f#8).zeroExtend 64 <<< 21)
abbrev vAcc5 (b0 b1 b2 b3 b4 : BitVec 8) : BitVec 64 :=
  vAcc4 b0 b1 b2 b3 ||| ((b4 &&& 0x7f#8).zeroExtend 64 <<< 28)
abbrev vAcc6 (b0 b1 b2 b3 b4 b5 : BitVec 8) : BitVec 64 :=
  vAcc5 b0 b1 b2 b3 b4 ||| ((b5 &&& 0x7f#8).zeroExtend 64 <<< 35)
abbrev vAcc7 (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) : BitVec 64 :=
  vAcc6 b0 b1 b2 b3 b4 b5 ||| ((b6 &&& 0x7f#8).zeroExtend 64 <<< 42)
abbrev vAcc8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  vAcc7 b0 b1 b2 b3 b4 b5 b6 ||| ((b7 &&& 0x7f#8).zeroExtend 64 <<< 49)
abbrev vAcc9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) : BitVec 64 :=
  vAcc8 b0 b1 b2 b3 b4 b5 b6 b7 ||| ((b8 &&& 0x7f#8).zeroExtend 64 <<< 56)
abbrev vAcc10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) : BitVec 64 :=
  vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8 ||| ((b9 &&& 0x7f#8).zeroExtend 64 <<< 63)

theorem zeroExtend64_and_127 (b : BitVec 8) :
    (b &&& 0x7f#8).zeroExtend 64 = b.zeroExtend 64 &&& 127#64 := by revert b; decide +kernel

theorem vAcc1_eq (b0 : BitVec 8) :
    b0.zeroExtend 64 &&& 127#64 = vAcc1 b0 := by revert b0; decide +kernel

theorem signExtend64_shiftLeft_63 (b9 : BitVec 8) :
    b9.signExtend 64 <<< 63 = (b9.zeroExtend 64 &&& 127#64) <<< 63 := by revert b9; decide +kernel

theorem varintSlow_1 (b0 : BitVec 8) (rest : List (BitVec 8)) (hb0 : b0 ≤ 0x7f#8) :
    varintSlow (b0 :: rest) = some (vAcc1 b0, 1) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, vAcc1]

theorem varintSlow_2 (b0 b1 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : b1 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: rest) = some (vAcc2 b0 b1, 2) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, vAcc2, vAcc1]

theorem varintSlow_3 (b0 b1 b2 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : b2 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: rest) = some (vAcc3 b0 b1 b2, 3) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, vAcc3, vAcc2, vAcc1]

theorem varintSlow_4 (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8) (hb3 : b3 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: rest) = some (vAcc4 b0 b1 b2 b3, 4) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_5 (b0 b1 b2 b3 b4 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : b4 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: rest) = some (vAcc5 b0 b1 b2 b3 b4, 5) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4,
    vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_6 (b0 b1 b2 b3 b4 b5 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : b5 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest) = some (vAcc6 b0 b1 b2 b3 b4 b5, 6) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5,
    vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_7 (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8) (hb6 : b6 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest) =
      some (vAcc7 b0 b1 b2 b3 b4 b5 b6, 7) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
    vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : b7 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) =
      some (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7, 8) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
    vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : b8 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest) =
      some (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8, 9) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8,
    vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : ¬ b8 ≤ 0x7f#8)
    (hb9 : b9 ≤ 0x7f#8) (hb9_lt : ¬ 2#8 ≤ b9) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) =
      some (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9, 10) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4,
    hb5, hb6, hb7, hb8, hb9, hb9_lt, vAcc10, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3,
    vAcc2, vAcc1]

theorem varintSlow_none_1 (b0 : BitVec 8) (hb0 : ¬ b0 ≤ 0x7f#8) :
    varintSlow [b0] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0]

theorem varintSlow_none_2 (b0 b1 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) :
    varintSlow [b0, b1] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1]

theorem varintSlow_none_3 (b0 b1 b2 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2]

theorem varintSlow_none_4 (b0 b1 b2 b3 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8) (hb3 : ¬ b3 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3]

theorem varintSlow_none_5 (b0 b1 b2 b3 b4 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3, b4] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4]

theorem varintSlow_none_6 (b0 b1 b2 b3 b4 b5 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3, b4, b5] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5]

theorem varintSlow_none_7 (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8) (hb6 : ¬ b6 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3, b4, b5, b6] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6]

theorem varintSlow_none_8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3, b4, b5, b6, b7] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]

theorem varintSlow_none_9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : ¬ b8 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3, b4, b5, b6, b7, b8] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8]

theorem varintSlow_none_10_gt (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : ¬ b8 ≤ 0x7f#8)
    (hb9 : ¬ b9 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
    hb8, hb9]

theorem varintSlow_none_10_ovf (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : ¬ b8 ≤ 0x7f#8)
    (hb9 : b9 ≤ 0x7f#8) (hb9_ge : 2#8 ≤ b9) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4,
    hb5, hb6, hb7, hb8, hb9, hb9_ge]

@[expose] def CalleeSaved19_28 (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5) ∧
  s.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5) ∧
  s.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) ∧
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

@[expose] def StateAt (s0 s : State) (pc : BitVec 64) : Prop :=
  s.pc = pc ∧ s.status = .Running ∧ s.sp = s0.sp - 64#64 ∧
    s.trace = s0.trace ∧ CalleeSaved19_28 s0 s

theorem ofNat_sub_ofNat_of_le {n k : Nat} (h : k ≤ n) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : n % 2 ^ 64 = n := Nat.mod_eq_of_lt hlt
  have : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  have : (n - k) % 2 ^ 64 = n - k := Nat.mod_eq_of_lt (by omega)
  omega

theorem pointsToBytes_extract_at (ptr : BitVec 64) (bs pre rest : List (BitVec 8)) (b : BitVec 8)
    (k : Nat) (h : pre ++ b :: rest = bs) (hk : pre.length = k) :
    (ptr ↦ₛ bs) =
      (ptr ↦ₛ pre) ∗ ((ptr + BitVec.ofNat 64 k) ↦₈ b) ∗
        ((ptr + BitVec.ofNat 64 k + 1#64) ↦ₛ rest) := by
  subst h hk
  rw [pointsToBytes_append, pointsToBytes_cons]

attribute [local irreducible] Program.fnOff

end CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeVarintSlowX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false

/-!
# Handshake `decode_varint [local#5]` Verification

Verifies the 145-instruction (`580` B) handshake `prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]`
subroutine against `decodeVarint2SpecX` (`LibsignalProtoCodec.decodeVarint`) on `tripleRatchetProgAtExt`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]` (145 instructions, `580B`). -/
abbrev decodeVarint5Name : String :=
  "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]"

/-- Stack budget for `decode_varint::<&mut &[u8]>`:
own frame `0x40` bytes (`+0x000: sub sp, sp, #64`) plus `decodeVarintSlowStack`. -/
abbrev decodeVarint2Stack : Nat := 0x40 + decodeVarintSlowStack

/-- Stack budget for `decode_varint::<&mut &[u8]>` under `Stage2ContractsX`. -/
abbrev decodeVarint2StackX : Nat := 0x40 + decodeVarintSlowStackX

/-- Contract of `prost::encoding::varint::decode_varint::<&mut &[u8]>`
in terms of `LibsignalProtoCodec.decodeVarint`. -/
@[expose] def decodeVarint2Spec (A : RustAlloc) : Spec DecodeVarintSlowGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp decodeVarint2Stack
  post := fun x s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp decodeVarint2Stack ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract of `prost::encoding::varint::decode_varint::<&mut &[u8]>`
under `Stage2ContractsX` (`decodeVarint2StackX`). -/
@[expose] def decodeVarint2SpecX (A : RustAlloc) : Spec DecodeVarintSlowGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp decodeVarint2StackX
  post := fun x s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp decodeVarint2StackX ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[local simp, local arm64_norm]
theorem signExtend32_and_255 (b : BitVec 8) :
    BitVec.truncate 32 (BitVec.signExtend 64 b) &&& 255#32 = BitVec.zeroExtend 32 b := by
  bv_bits

@[local simp, local arm64_norm]
theorem zeroExtend64_zeroExtend32 (b : BitVec 8) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b) = BitVec.zeroExtend 64 b := by
  bv_bits

@[local simp, local arm64_norm]
theorem signExtend32_and_127 (b : BitVec 8) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b) &&& 127#32) =
      BitVec.zeroExtend 64 b &&& 127#64 := by
  bv_bits

@[local simp, local arm64_norm]
theorem getLsbD_31_signExtend (b : BitVec 8) :
    (BitVec.truncate 32 (BitVec.signExtend 64 b)).getLsbD 31 = b.getLsbD 7 := by
  bv_bits

theorem byte9_ult1_of_ge {b9 : BitVec 8} (hb9 : 2#8 ≤ b9) :
    (1#64).ult (b9.zeroExtend 64) = true := by bv_bits

theorem byte9_ult1_of_lt {b9 : BitVec 8} (hb9 : ¬ 2#8 ≤ b9) :
    (1#64).ult (b9.zeroExtend 64) = false := by bv_bits

theorem stackAt_decodeVarint2 (sp : BitVec 64) :
    stackAt sp decodeVarint2Stack =
      stackAt (sp - 64#64) decodeVarintSlowStack ∗
        memRegion (sp - 56#64) 40 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v8 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v8) ∗ ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := ProofLib.stackAt_split_cells sp decodeVarintSlowStack 8 (by decide)
  rw [← ProofLib.memRegion_cells (sp - BitVec.ofNat 64 (8 * 8)) 8 (by decide)] at h0
  change stackAt sp decodeVarint2Stack =
    stackAt (sp - 64#64) decodeVarintSlowStack ∗ memRegion (sp - 64#64) 64 at h0
  have s1 := ProofLib.memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 64 8] at s1
  have s2 := ProofLib.memRegion_split (sp - 56#64) 40 16 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 56 40] at s2
  have s3 := ProofLib.memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 16 8] at s3
  rw [h0, s1, s2, s3,
    ProofLib.memRegion_eight (sp - 64#64), ProofLib.memRegion_eight (sp - 16#64),
    ProofLib.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem stackAt_decodeVarint2X (sp : BitVec 64) :
    stackAt sp decodeVarint2StackX =
      stackAt (sp - 64#64) decodeVarintSlowStackX ∗
        memRegion (sp - 56#64) 40 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v8 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v8) ∗ ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := ProofLib.stackAt_split_cells sp decodeVarintSlowStackX 8 (by decide)
  rw [← ProofLib.memRegion_cells (sp - BitVec.ofNat 64 (8 * 8)) 8 (by decide)] at h0
  change stackAt sp decodeVarint2StackX =
    stackAt (sp - 64#64) decodeVarintSlowStackX ∗ memRegion (sp - 64#64) 64 at h0
  have s1 := ProofLib.memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 64 8] at s1
  have s2 := ProofLib.memRegion_split (sp - 56#64) 40 16 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 56 40] at s2
  have s3 := ProofLib.memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 16 8] at s3
  rw [h0, s1, s2, s3,
    ProofLib.memRegion_eight (sp - 64#64), ProofLib.memRegion_eight (sp - 16#64),
    ProofLib.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem stackAt_slow_eq_errorHook (sp : BitVec 64) :
    stackAt sp decodeVarintSlowStack =
      memRegion (sp - BitVec.ofNat 64 decodeVarintSlowStack) 64 ∗
        stackAt sp decodeErrorHookStack :=
  ProofLib.stackAt_split_bottom sp decodeErrorHookStack 64 (by decide)

theorem stackAt_errorHook_entails_slow (sp : BitVec 64) :
    memRegion (sp - 8320#64) 64 ∗ stackAt (sp - 64#64) decodeErrorHookStack ⊢
      stackAt (sp - 64#64) decodeVarintSlowStack := by
  have h := stackAt_slow_eq_errorHook (sp - 64#64)
  have hsub : sp - 64#64 - BitVec.ofNat 64 decodeVarintSlowStack = sp - 8320#64 := by
    dsimp [decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]; bv_omega
  rw [hsub] at h
  exact Entails.of_eq h.symm

theorem stackAt_slowX_eq_errorHookX (sp : BitVec 64) :
    stackAt sp decodeVarintSlowStackX =
      memRegion (sp - BitVec.ofNat 64 decodeVarintSlowStackX) 64 ∗
        stackAt sp decodeErrorHookStackX :=
  ProofLib.stackAt_split_bottom sp decodeErrorHookStackX 64 (by decide)

theorem stackAt_errorHookX_entails_slowX (sp : BitVec 64) :
    memRegion (sp - 32896#64) 64 ∗ stackAt (sp - 64#64) decodeErrorHookStackX ⊢
      stackAt (sp - 64#64) decodeVarintSlowStackX := by
  have h := stackAt_slowX_eq_errorHookX (sp - 64#64)
  have hsub : sp - 64#64 - BitVec.ofNat 64 decodeVarintSlowStackX = sp - 32896#64 := by
    dsimp [decodeVarintSlowStackX, decodeErrorHookStackX, extHookStack]; bv_omega
  rw [hsub] at h
  exact Entails.of_eq h.symm

/-! ## `decodeVarint` 1..10-byte unfolding and hardware value equality lemmas -/

theorem decodeVarint_1 {b0 : BitVec 8} (rest : List (BitVec 8)) (hb0 : b0 ≤ 0x7f#8) :
    decodeVarint (b0 :: rest) = some (BitVec.signExtend 64 b0, rest) := by
  have hdec : decodeVarint (b0 :: rest) = some (vAcc1 b0, rest) := by
    rw [decodeVarint, decodeVarintAux]; simp [toNat_le_0x7f_iff, hb0, vAcc1]
  have hv : vAcc1 b0 = BitVec.signExtend 64 b0 := by
    rw [vAcc1_eq]; revert hb0; bv_bits
  rw [hdec, hv]

theorem decodeVarint_2 {b0 b1 : BitVec 8} (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : b1 ≤ 0x7f#8) :
    decodeVarint (b0 :: b1 :: rest) =
      some (BitVec.zeroExtend 64 (part0_2 b0 b1), rest) := by
  have hdec : decodeVarint (b0 :: b1 :: rest) = some (vAcc2 b0 b1, rest) := by
    rw [decodeVarint]; iterate 2 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, vAcc2, vAcc1]
  have hv : vAcc2 b0 b1 = BitVec.zeroExtend 64 (part0_2 b0 b1) := by
    simp only [vAcc2_eq, vAcc1_eq, part0_2]
    revert hb0 hb1; bv_bits
  rw [hdec, hv]

theorem decodeVarint_3 {b0 b1 b2 : BitVec 8} (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : b2 ≤ 0x7f#8) :
    decodeVarint (b0 :: b1 :: b2 :: rest) =
      some (BitVec.zeroExtend 64 (part0_3 b0 b1 b2), rest) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: rest) = some (vAcc3 b0 b1 b2, rest) := by
    rw [decodeVarint]; iterate 3 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, vAcc3, vAcc2, vAcc1]
  have hv : vAcc3 b0 b1 b2 = BitVec.zeroExtend 64 (part0_3 b0 b1 b2) := by
    simp only [vAcc3_eq, vAcc2_eq, vAcc1_eq, part0_3, part0_2]
    revert hb0 hb1 hb2; bv_bits
  rw [hdec, hv]

theorem decodeVarint_4 {b0 b1 b2 b3 : BitVec 8} (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8) (hb3 : b3 ≤ 0x7f#8) :
    decodeVarint (b0 :: b1 :: b2 :: b3 :: rest) =
      some (BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3), rest) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: rest) = some (vAcc4 b0 b1 b2 b3, rest) := by
    rw [decodeVarint]; iterate 4 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, vAcc4, vAcc3, vAcc2, vAcc1]
  have hv : vAcc4 b0 b1 b2 b3 = BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3) := by
    simp only [vAcc4_eq, vAcc3_eq, vAcc2_eq, vAcc1_eq, part0_4, part0_3, part0_2]
    revert hb0 hb1 hb2 hb3; bv_bits
  rw [hdec, hv]

theorem decodeVarint_5 {b0 b1 b2 b3 b4 : BitVec 8} (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : b4 ≤ 0x7f#8) :
    decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: rest) =
      some (BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) +
        BitVec.zeroExtend 64 b4 <<< 28, rest) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: rest) =
      some (vAcc5 b0 b1 b2 b3 b4, rest) := by
    rw [decodeVarint]; iterate 5 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  have hp1 : ((b4 &&& 0x7F#8).zeroExtend 64 <<< 28) = BitVec.zeroExtend 64 b4 <<< 28 := by
    clear hb0 hb1 hb2 hb3; revert hb4; bv_bits
  rw [hdec, vAcc5_eq, ← hw_part0_eq hb0 hb1 hb2 hb3, hp1]

theorem decodeVarint_6 {b0 b1 b2 b3 b4 b5 : BitVec 8} (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : b5 ≤ 0x7f#8) :
    decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest) =
      some (BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) +
        BitVec.zeroExtend 64 (part1_2 b4 b5) <<< 28, rest) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest) =
      some (vAcc6 b0 b1 b2 b3 b4 b5, rest) := by
    rw [decodeVarint]; iterate 6 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  have hp1 : ((b4 &&& 0x7F#8).zeroExtend 64 <<< 28) + ((b5 &&& 0x7F#8).zeroExtend 64 <<< 35) =
      BitVec.zeroExtend 64 (part1_2 b4 b5) <<< 28 := by
    clear hb0 hb1 hb2 hb3; simp only [part1_2]; revert hb4 hb5; bv_bits
  rw [hdec, vAcc6_eq, vAcc5_eq, ← hw_part0_eq hb0 hb1 hb2 hb3, BitVec.add_assoc, hp1]

theorem decodeVarint_7 {b0 b1 b2 b3 b4 b5 b6 : BitVec 8} (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8) (hb6 : b6 ≤ 0x7f#8) :
    decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest) =
      some (BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) +
        BitVec.zeroExtend 64 (part1_3 b4 b5 b6) <<< 28, rest) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest) =
      some (vAcc7 b0 b1 b2 b3 b4 b5 b6, rest) := by
    rw [decodeVarint]; iterate 7 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
      vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  have hp1 : ((b4 &&& 0x7F#8).zeroExtend 64 <<< 28) +
      (((b5 &&& 0x7F#8).zeroExtend 64 <<< 35) + ((b6 &&& 0x7F#8).zeroExtend 64 <<< 42)) =
      BitVec.zeroExtend 64 (part1_3 b4 b5 b6) <<< 28 := by
    clear hb0 hb1 hb2 hb3; simp only [part1_3, part1_2]; revert hb4 hb5 hb6; bv_bits
  rw [hdec, vAcc7_eq, vAcc6_eq, vAcc5_eq, ← hw_part0_eq hb0 hb1 hb2 hb3,
    BitVec.add_assoc, BitVec.add_assoc, hp1]

theorem decodeVarint_8 {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8} (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : b7 ≤ 0x7f#8) :
    decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) =
      some (BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) +
        BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7) <<< 28, rest) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) =
      some (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7, rest) := by
    rw [decodeVarint]; iterate 8 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
      vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  have hp1 : ((b4 &&& 0x7F#8).zeroExtend 64 <<< 28) +
      (((b5 &&& 0x7F#8).zeroExtend 64 <<< 35) +
      (((b6 &&& 0x7F#8).zeroExtend 64 <<< 42) + ((b7 &&& 0x7F#8).zeroExtend 64 <<< 49))) =
      BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7) <<< 28 := by
    clear hb0 hb1 hb2 hb3; simp only [part1_4, part1_3, part1_2]; revert hb4 hb5 hb6 hb7; bv_bits
  rw [hdec, vAcc8_eq, vAcc7_eq, vAcc6_eq, vAcc5_eq, ← hw_part0_eq hb0 hb1 hb2 hb3,
    BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, hp1]

theorem decodeVarint_9 {b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8} (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : b8 ≤ 0x7f#8) :
    decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest) =
      some (BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) +
        BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7 + 4026531840#32) <<< 28 +
        BitVec.signExtend 64 b8 <<< 56, rest) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest) =
      some (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8, rest) := by
    rw [decodeVarint]; iterate 9 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8,
      vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  have hp8 : ((b8 &&& 0x7F#8).zeroExtend 64 <<< 56) = BitVec.signExtend 64 b8 <<< 56 := by
    clear hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7; revert hb8; bv_bits
  rw [hdec, vAcc9_eq, ← hw_part01_eq hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7, hp8]

theorem decodeVarint_10 {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8} (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : ¬ b8 ≤ 0x7f#8)
    (hb9 : ¬ 2#8 ≤ b9) :
    decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) =
      some ((BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) +
        BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7 + 4026531840#32) <<< 28 +
        (BitVec.zeroExtend 64 b8 &&& 127#64) <<< 56) |||
        BitVec.zeroExtend 64 b9 <<< 63, rest) := by
  have hb9' : b9 ≤ 0x7f#8 := by revert hb9; bv_bits
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) =
      some (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9, rest) := by
    rw [decodeVarint]; iterate 10 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9', hb9,
      vAcc10, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  have hp8 : ((b8 &&& 0x7F#8).zeroExtend 64 <<< 56) = (BitVec.zeroExtend 64 b8 &&& 127#64) <<< 56 := by
    clear hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb9'; bv_bits
  have hp9 : ((b9 &&& 0x7F#8).zeroExtend 64 <<< 63) = BitVec.zeroExtend 64 b9 <<< 63 := by
    clear hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9'; revert hb9; bv_bits
  rw [hdec, vAcc10, vAcc9_eq, ← hw_part01_eq hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7, hp8, hp9]

theorem sliceCursorAfter_of_eq {slot ptr : BitVec 64} {bs rest : List (BitVec 8)} {k : Nat}
    (hlen : bs.length = rest.length + k) :
    sliceCursorAfter slot ptr bs rest =
      (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
        ((slot + 8#64) ↦₆₄ (BitVec.ofNat 64 bs.length - BitVec.ofNat 64 k)) ∗ (ptr ↦ₛ bs) := by
  have hsub : bs.length - rest.length = k := by omega
  have hbv : BitVec.ofNat 64 rest.length = BitVec.ofNat 64 bs.length - BitVec.ofNat 64 k := by
    rw [hlen, BitVec.ofNat_add, BitVec.add_sub_cancel]
  simp only [sliceCursorAfter, hsub, hbv]

/-! ## Relative callee offsets -/

private abbrev dv5JoinState (s0 : State) (slot ptr : BitVec 64)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8)) (entry : BitVec 64) (m : Memory) : State :=
  ((((((((s0.writeReg64 Reg.sp (s0.sp - 64#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
      (Reg.gpr 8#5) slot).writeReg64 (Reg.gpr 9#5)
      (BitVec.ofNat 64 (b0 :: b1 :: bs2).length)).writeReg64 (Reg.gpr 10#5) ptr).writeReg64
      (Reg.gpr 1#5) (BitVec.signExtend 64 b0)).writeReg64
      (Reg.gpr 11#5) (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b1)))).setPState
      (subsPState64 (BitVec.ofNat 64 (b0 :: b1 :: bs2).length) 10#64)
    |>.setPC (entry + bv% (88)) |>.setMem m)

private abbrev dv5JoinPre (A : RustAlloc) (s0 : State) (bufRef slot ptr v_stk_2 : BitVec 64)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8)) : SepProp :=
  bufRef ↦₆₄ slot ∗ slot ↦₆₄ ptr ∗
    (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (b0 :: b1 :: bs2).length ∗
    (ptr ↦₈ b0 ∗ ((ptr + 1#64) ↦₈ b1 ∗ (ptr + 1#64 + 1#64) ↦ₛ bs2)) ∗ A.pool ∗
    stackAt (s0.sp - 64#64) decodeVarintSlowStackX ∗ memRegion (s0.sp - 56#64) 40 ∗
    (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
    (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)

private abbrev dv5JoinPost (A : RustAlloc) (s0 : State) (bufRef slot ptr : BitVec 64)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8)) (R : SepProp) :
    State → SepProp → Prop := fun sf P_f =>
  (sf.mem ⊨ P_f ∗ R →
      sf.mem ⊨
        (∃∗ x, ∃∗ x_1, ∃∗ x_2,
          (match decodeVarint (b0 :: b1 :: bs2) with
            | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
            | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
            ⌜sf.trace = s0.trace⌝ ∗ bufRef ↦₆₄ slot ∗ A.pool ∗
            (stackAt (s0.sp - 64#64) decodeVarintSlowStackX ∗
              memRegion (s0.sp - 56#64) 40 ∗
              (s0.sp - 64#64) ↦₆₄ x_2 ∗ (s0.sp - 16#64) ↦₆₄ x_1 ∗
              (s0.sp - 8#64) ↦₆₄ x) ∗
            match decodeVarint (b0 :: b1 :: bs2) with
            | some (_, rest) =>
              sliceCursorAfter slot ptr (b0 :: b1 :: bs2) rest
            | none =>
              ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
                decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
                memRegion slot 16 ∗ ptr ↦ₛ (b0 :: b1 :: bs2)) ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev dv5JoinPanic (s0 : State) (R : SepProp) :
    State → SepProp → Prop := fun sf P_f =>
  sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

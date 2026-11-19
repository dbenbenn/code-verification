/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.GF.UnacceleratedMul -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.IfaceBudget
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Verification of `spqr::encoding::gf::accelerated::mul2_unreduced` (Block `383`)

Proves the algebraic equivalence between ARMv8 `PMULL` (`Arm64.evalPmull false true` /
`Arm64.polyMul`) and `CryptoVerification.LibsignalSpqrV1.unaccelerated.polyMul`, verifies the
relocatable `[LibsignalPlacement]` subroutine contracts for Block `383`
(`spqr::encoding::gf::accelerated::mul2_unreduced`), and provides shared normalization helpers
for inline `REDUCE_BYTES` polynomial reduction at accelerated call sites.
-/

public section

namespace CryptoVerification.SpqrV1.GF.AcceleratedMul

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev acceleratedMul2UnreducedName : String :=
  "spqr::encoding::gf::accelerated::mul2_unreduced"

/-! ## 1. Pure Algebraic Equivalence: `Arm64.polyMul` vs `unaccelerated.polyMul` -/

private theorem truncate32_xor_128 (x y : BitVec 128) :
    (x ^^^ y).truncate 32 = x.truncate 32 ^^^ y.truncate 32 := by
  bv_slice

private theorem truncate32_ite_128 (c : Bool) (x y : BitVec 128) :
    (if c then x else y).truncate 32 = if c then x.truncate 32 else y.truncate 32 := by
  cases c <;> rfl

private theorem truncate32_zext128_zext64_shl (a : BitVec 16) (i : Nat) :
    (((a.zeroExtend 64).zeroExtend 128) <<< i).truncate 32 = (a.zeroExtend 32) <<< i := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj128 : j < 128 := by omega
  have hsub128 : j - i < 128 := by omega
  have hsub64 : j - i < 64 := by omega
  have hsub32 : j - i < 32 := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    hj, hj128, hsub128, hsub64, hsub32, decide_true, Bool.true_and]

private theorem one_getLsbD {w : Nat} (hw : 0 < w) (j : Nat) :
    (1#w).getLsbD j = decide (j = 0) := by
  cases j with
  | zero => rw [BitVec.getLsbD_ofNat]; simp [hw]
  | succ n => simp

private theorem test_bit16_eq_getLsbD_gen (b : BitVec 16) {i : Nat} (hi : i < 16) :
    (0#16 != (b &&& (1#16 <<< i))) = b.getLsbD i := by
  cases hb : b.getLsbD i
  · rw [bne_eq_false_iff_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_zero, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hk,
      decide_true, Bool.true_and, one_getLsbD (by decide : 0 < 16)]
    by_cases hki : k < i
    · simp [hki]
    · by_cases heq : k = i
      · subst heq; simp [hb]
      · have hne0 : k - i ≠ 0 := by omega
        simp [hki, hne0]
  · rw [bne_iff_ne]
    intro heq
    have hk := congrArg (fun x => x.getLsbD i) heq
    rw [BitVec.getLsbD_zero, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      one_getLsbD (by decide : 0 < 16)] at hk
    simp only [hi, hb, Nat.lt_irrefl, Nat.sub_self, decide_true, decide_false, Bool.not_false,
      Bool.true_and, Bool.false_eq_true] at hk

private theorem polyMulLoop_eq_arm64_polyMul_aux (a b : BitVec 16) :
    ∀ k, k ≤ 16 →
      unaccelerated.polyMulLoop (a.zeroExtend 32) b k (16 - k)
        ((Arm64.polyMul (16 - k) (b.zeroExtend 64) (a.zeroExtend 64)).truncate 32) =
      (Arm64.polyMul 16 (b.zeroExtend 64) (a.zeroExtend 64)).truncate 32
  | 0, _ => by rfl
  | m + 1, hm => by
    have hs_lt : 16 - (m + 1) < 16 := by omega
    have hs_lt64 : 16 - (m + 1) < 64 := by omega
    have hs_succ : 16 - (m + 1) + 1 = 16 - m := by omega
    dsimp only [unaccelerated.polyMulLoop]
    rw [test_bit16_eq_getLsbD_gen b hs_lt]
    have hstep :
        (if b.getLsbD (16 - (m + 1)) = true then
            (Arm64.polyMul (16 - (m + 1)) (b.zeroExtend 64) (a.zeroExtend 64)).truncate 32 ^^^
              a.zeroExtend 32 <<< (16 - (m + 1))
          else (Arm64.polyMul (16 - (m + 1)) (b.zeroExtend 64) (a.zeroExtend 64)).truncate 32) =
          (Arm64.polyMul (16 - m) (b.zeroExtend 64) (a.zeroExtend 64)).truncate 32 := by
      rw [← hs_succ, Arm64.polyMul_succ, truncate32_ite_128]
      have hlsb : (b.zeroExtend 64).getLsbD (16 - (m + 1)) = b.getLsbD (16 - (m + 1)) := by
        simp only [BitVec.getLsbD_setWidth, hs_lt64, decide_true, Bool.true_and]
      rw [hlsb]
      cases b.getLsbD (16 - (m + 1))
      · rfl
      · simp only [↓reduceIte, truncate32_xor_128, truncate32_zext128_zext64_shl]
    rw [hstep, hs_succ]
    exact polyMulLoop_eq_arm64_polyMul_aux a b m (by omega)

theorem arm64_polyMul_16_eq_unaccelerated_swap (a b : BitVec 16) :
    (Arm64.polyMul 16 (b.zeroExtend 64) (a.zeroExtend 64)).truncate 32 =
      unaccelerated.polyMul a b :=
  (polyMulLoop_eq_arm64_polyMul_aux a b 16 (by decide)).symm

private theorem polyMul_one_right_getLsbD (x : BitVec 64) :
    ∀ n, n ≤ 64 → ∀ k, k < 128 →
      (Arm64.polyMul n x 1#64).getLsbD k = (decide (k < n) && x.getLsbD k)
  | 0, _, k, _ => by simp [Arm64.polyMul_zero]
  | m + 1, hm, k, hk => by
    rw [Arm64.polyMul_succ]
    have ihm := polyMul_one_right_getLsbD x m (by omega) k hk
    have hz1 : (1#64 : BitVec 64).zeroExtend 128 = 1#128 := by decide
    cases hxm : x.getLsbD m
    · simp only [Bool.false_eq_true, ↓reduceIte, ihm]
      by_cases hkm : k = m
      · subst hkm; simp [hxm]
      · have hiff : (k < m) ↔ (k < m + 1) := by omega
        simp [hiff]
    · simp only [↓reduceIte, BitVec.getLsbD_xor, ihm, hz1, BitVec.getLsbD_shiftLeft,
        hk, decide_true, Bool.true_and, one_getLsbD (by decide : 0 < 128)]
      by_cases hkl : k < m
      · have hlt2 : k < m + 1 := by omega
        simp [hkl, hlt2]
      · by_cases hkeq : k = m
        · subst hkeq; simp [hxm]
        · have hnot1 : ¬(k < m + 1) := by omega
          have hne0 : k - m ≠ 0 := by omega
          simp [hkl, hnot1, hne0]

private theorem polyMul_16_one_right (b : BitVec 16) :
    Arm64.polyMul 16 (b.zeroExtend 64) 1#64 = b.zeroExtend 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [polyMul_one_right_getLsbD (b.zeroExtend 64) 16 (by decide) k hk]
  simp only [BitVec.getLsbD_setWidth, hk, decide_true, Bool.true_and]
  by_cases hk16 : k < 16
  · have hk64 : k < 64 := by omega
    simp [hk16, hk64]
  · simp [hk16, BitVec.getLsbD_of_ge b k (by omega)]

private theorem polyMul_16_shift_one_right (b : BitVec 16) {s : Nat} (hs : s < 16) :
    Arm64.polyMul 16 (b.zeroExtend 64) (1#64 <<< s) = (b.zeroExtend 128) <<< s := by
  rw [Arm64.polyMul_shiftLeft_right 16 s (b.zeroExtend 64) 1#64, polyMul_16_one_right]
  intro i hlo _hhi
  have hne0 : i ≠ 0 := by omega
  rw [one_getLsbD (by decide : 0 < 64)]
  simp [hne0]

private def prefixBits64 (x : BitVec 64) : Nat → BitVec 64
  | 0 => 0#64
  | n + 1 => if x.getLsbD n then prefixBits64 x n ^^^ (1#64 <<< n) else prefixBits64 x n

private theorem prefixBits64_getLsbD (x : BitVec 64) :
    ∀ n, n ≤ 64 → ∀ k, k < 64 →
      (prefixBits64 x n).getLsbD k = (decide (k < n) && x.getLsbD k)
  | 0, _, k, _ => by simp [prefixBits64]
  | m + 1, hm, k, hk => by
    have ihm := prefixBits64_getLsbD x m (by omega) k hk
    dsimp only [prefixBits64]
    cases hxm : x.getLsbD m
    · simp only [Bool.false_eq_true, ↓reduceIte, ihm]
      by_cases hkm : k = m
      · subst hkm; simp [hxm]
      · have hiff : (k < m) ↔ (k < m + 1) := by omega
        simp [hiff]
    · simp only [↓reduceIte, BitVec.getLsbD_xor, ihm, BitVec.getLsbD_shiftLeft,
        hk, decide_true, Bool.true_and, one_getLsbD (by decide : 0 < 64)]
      by_cases hkl : k < m
      · have hlt2 : k < m + 1 := by omega
        simp [hkl, hlt2]
      · by_cases hkeq : k = m
        · subst hkeq; simp [hxm]
        · have hnot1 : ¬(k < m + 1) := by omega
          have hne0 : k - m ≠ 0 := by omega
          simp [hkl, hnot1, hne0]

private theorem prefixBits64_16_zext (a : BitVec 16) :
    prefixBits64 (a.zeroExtend 64) 16 = a.zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [prefixBits64_getLsbD (a.zeroExtend 64) 16 (by decide) k hk]
  simp only [BitVec.getLsbD_setWidth, hk, decide_true, Bool.true_and]
  by_cases hk16 : k < 16
  · simp [hk16]
  · simp [hk16, BitVec.getLsbD_of_ge a k (by omega)]

private theorem polyMul_prefix_comm_aux (a b : BitVec 16) :
    ∀ n, n ≤ 16 →
      Arm64.polyMul n (a.zeroExtend 64) (b.zeroExtend 64) =
        Arm64.polyMul 16 (b.zeroExtend 64) (prefixBits64 (a.zeroExtend 64) n)
  | 0, _ => by simp [prefixBits64, Arm64.polyMul_zero, Arm64.polyMul_zero_right]
  | m + 1, hm => by
    rw [Arm64.polyMul_succ, polyMul_prefix_comm_aux a b m (by omega)]
    dsimp only [prefixBits64]
    cases (a.zeroExtend 64).getLsbD m
    · rfl
    · simp only [↓reduceIte, Arm64.polyMul_xor_right,
        polyMul_16_shift_one_right b (by omega : m < 16)]
      have hzext : ((b.zeroExtend 64).zeroExtend 128) = b.zeroExtend 128 := by
        apply BitVec.eq_of_getLsbD_eq
        intro k hk
        simp only [BitVec.getLsbD_setWidth, hk, decide_true, Bool.true_and]
        by_cases hk64 : k < 64
        · simp [hk64]
        · simp [hk64, BitVec.getLsbD_of_ge b k (by omega)]
      rw [hzext]

theorem arm64_polyMul_16_comm (a b : BitVec 16) :
    Arm64.polyMul 16 (a.zeroExtend 64) (b.zeroExtend 64) =
      Arm64.polyMul 16 (b.zeroExtend 64) (a.zeroExtend 64) := by
  rw [polyMul_prefix_comm_aux a b 16 (by decide), prefixBits64_16_zext]

/-- Pure algebraic equivalence between 16-bit `Arm64.polyMul` and `unaccelerated.polyMul`. -/
theorem arm64_polyMul_16_eq_unaccelerated (a b : BitVec 16) :
    (Arm64.polyMul 16 (a.zeroExtend 64) (b.zeroExtend 64)).truncate 32 =
      unaccelerated.polyMul a b := by
  rw [arm64_polyMul_16_comm, arm64_polyMul_16_eq_unaccelerated_swap]

/-! ## 2. Packed 64-Bit `mul2_unreduced` Output Word & Reduction Normalizers -/

/-- Packed 64-bit unreduced polynomial product returned in `x0` by
`spqr::encoding::gf::accelerated::mul2_unreduced(a, b1, b2)`:
`unaccelerated.polyMul a b2` in bits `[31:0]` and `unaccelerated.polyMul a b1` in bits `[63:32]`. -/
@[expose] def mul2UnreducedWord (a b1 b2 : BitVec 16) : BitVec 64 :=
  (unaccelerated.polyMul a b2).zeroExtend 64 |||
    ((unaccelerated.polyMul a b1).zeroExtend 64 <<< 32)

/-- Equivalence between `Arm64.evalPmull false true` on packed `(a, (b1, b2))` and
`mul2UnreducedWord a b1 b2` (low 64 bits) with `0#64` (high 64 bits). -/
theorem evalPmull_pack32_u16_lo64 (a b1 b2 : BitVec 16) :
    (Arm64.evalPmull false true
      ((a.zeroExtend 64).zeroExtend 128)
      (((b2.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 32)).zeroExtend 128)).truncate 64 =
    mul2UnreducedWord a b1 b2 := by
  have ht1 : (((a.zeroExtend 64).zeroExtend 128) : BitVec 128).truncate 64 = a.zeroExtend 64 := by
    bv_bits
  have ht2 :
      ((((b2.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 32)).zeroExtend 128) : BitVec 128).truncate 64 =
        (b2.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 32) := by
    bv_bits
  rw [Arm64.evalPmull_false_true, ht1, ht2, Arm64.polyMul_64_pack32_u16_truncate64,
      arm64_polyMul_16_eq_unaccelerated, arm64_polyMul_16_eq_unaccelerated,
      mul2UnreducedWord, BitVec.or_comm]

theorem evalPmull_pack32_u16_hi64 (a b1 b2 : BitVec 16) :
    (Arm64.evalPmull false true
      ((a.zeroExtend 64).zeroExtend 128)
      (((b2.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 32)).zeroExtend 128)).extractLsb' 64 64 =
    0#64 := by
  have ht1 : (((a.zeroExtend 64).zeroExtend 128) : BitVec 128).truncate 64 = a.zeroExtend 64 := by
    bv_bits
  have ht2 :
      ((((b2.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 32)).zeroExtend 128) : BitVec 128).truncate 64 =
        (b2.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 32) := by
    bv_bits
  rw [Arm64.evalPmull_false_true, ht1, ht2]
  exact Arm64.polyMul_64_pack32_u16_hi64 a b1 b2

theorem mul2UnreducedWord_shr32 (a b1 b2 : BitVec 16) :
    mul2UnreducedWord a b1 b2 >>> 32 = (unaccelerated.polyMul a b1).zeroExtend 64 := by
  unfold mul2UnreducedWord; bv_bits

theorem mul2UnreducedWord_shr32_and_u32 (a b1 b2 : BitVec 16) :
    mul2UnreducedWord a b1 b2 >>> 32 &&& 4294967295#64 =
      (unaccelerated.polyMul a b1).zeroExtend 64 := by
  unfold mul2UnreducedWord; bv_bits

theorem mul2UnreducedWord_truncate32 (a b1 b2 : BitVec 16) :
    BitVec.truncate 32 (mul2UnreducedWord a b1 b2) = unaccelerated.polyMul a b2 := by
  unfold mul2UnreducedWord; bv_bits

theorem mul2UnreducedWord_shr56 (a b1 b2 : BitVec 16) :
    mul2UnreducedWord a b1 b2 >>> 56 = (unaccelerated.polyMul a b1 >>> 24).zeroExtend 64 := by
  unfold mul2UnreducedWord; bv_bits

theorem mul2UnreducedWord_shr56_and255 (a b1 b2 : BitVec 16) :
    mul2UnreducedWord a b1 b2 >>> 56 &&& 255#64 =
      (BitVec.truncate 8 (unaccelerated.polyMul a b1 >>> 24)).zeroExtend 64 := by
  unfold mul2UnreducedWord; bv_bits

theorem uxtx1_hi_idx1_eq (a b1 b2 : BitVec 16) :
    BitVec.ofNat 64 (2 * (BitVec.truncate 8 (unaccelerated.polyMul a b1 >>> 24)).toNat) =
      (mul2UnreducedWord a b1 b2 >>> 56 &&& 255#64) <<< 1 := by
  rw [ofNat_mul2_eq_shl1, mul2UnreducedWord_shr56_and255]

theorem uxtx1_hi_idx1_nomask_eq (a b1 b2 : BitVec 16) :
    BitVec.ofNat 64 (2 * (BitVec.truncate 8 (unaccelerated.polyMul a b1 >>> 24)).toNat) =
      (mul2UnreducedWord a b1 b2 >>> 56) <<< 1 := by
  rw [ofNat_mul2_eq_shl1, mul2UnreducedWord_shr56]; bv_bits

theorem uxtw1_hi_idx1_eq (a b1 b2 : BitVec 16) :
    BitVec.ofNat 64 (2 * (BitVec.truncate 8 (unaccelerated.polyMul a b1 >>> 24)).toNat) =
      BitVec.zeroExtend 64 (BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 56 &&& 255#64)) <<< 1 := by
  rw [ofNat_mul2_eq_shl1, mul2UnreducedWord_shr56_and255]; bv_bits

theorem uxtw1_hi_idx1_noshift_mask_eq (a b1 b2 : BitVec 16) :
    BitVec.ofNat 64 (2 * (BitVec.truncate 8 (unaccelerated.polyMul a b1 >>> 24)).toNat) =
      BitVec.zeroExtend 64 (BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 56)) <<< 1 := by
  rw [ofNat_mul2_eq_shl1, mul2UnreducedWord_shr56]; bv_bits

theorem uxtw1_lo_idx1_eq (a b1 b2 : BitVec 16) :
    BitVec.ofNat 64 (2 * (BitVec.truncate 8 (unaccelerated.polyMul a b2 >>> 24)).toNat) =
      BitVec.zeroExtend 64
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (mul2UnreducedWord a b1 b2)) >>> 24 &&& 255#64)) <<< 1 := by
  rw [mul2UnreducedWord_truncate32, ofNat_mul2_eq_shl1]; bv_bits

theorem uxtw1_lo_idx1_nomask_eq (a b1 b2 : BitVec 16) :
    BitVec.ofNat 64 (2 * (BitVec.truncate 8 (unaccelerated.polyMul a b2 >>> 24)).toNat) =
      BitVec.zeroExtend 64
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (mul2UnreducedWord a b1 b2)) >>> 24)) <<< 1 := by
  rw [mul2UnreducedWord_truncate32, uxtw1_idx1_eq]

theorem polyReduce_eor_comm_asm_eq (a b_arg : BitVec 16) :
    BitVec.zeroExtend 16
      (BitVec.truncate 32
        (BitVec.zeroExtend 64
            (unaccelerated.polyMul a b_arg ^^^
              BitVec.zeroExtend 32
                  (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<<
                8) ^^^
          BitVec.zeroExtend 64
            (reduce.reduceByteEntry
              (BitVec.truncate 8
                ((unaccelerated.polyMul a b_arg ^^^
                    BitVec.zeroExtend 32
                        (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<<
                      8) >>>
                  16))))) =
    unaccelerated.mul a b_arg := by
  rw [BitVec.xor_comm (BitVec.zeroExtend 64 (unaccelerated.polyMul a b_arg ^^^ _))]
  exact polyReduce_asm_eq a b_arg

theorem polyReduce_eor_comm_trunc16_eq (a b_arg : BitVec 16) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
          (unaccelerated.polyMul a b_arg ^^^
            BitVec.zeroExtend 32
                (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<<
              8) ^^^
        BitVec.zeroExtend 64
          (reduce.reduceByteEntry
            (BitVec.truncate 8
              ((unaccelerated.polyMul a b_arg ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<<
                    8) >>>
                16)))) =
    unaccelerated.mul a b_arg := by
  have hz : ∀ x : BitVec 64, BitVec.truncate 16 x = BitVec.zeroExtend 16 (BitVec.truncate 32 x) := by
    intro x; bv_bits
  rw [hz]
  exact polyReduce_eor_comm_asm_eq a b_arg

/-! ## 3. Subroutine Specification & Verification of Block `383` -/

private def vmCoreAcc (s : State) :=
  (s.brkStart, s.brk, s.tpidrEl0, s.physMemAvail,
    fun fd : { fd : Nat // 3 ≤ fd ∧ fd < 2 ^ 31 } => s.fs.fds (BitVec.ofNat 64 fd.1))

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmPreserved_iff_vmCoreAcc (s s' : State) :
    LibsignalBinary.Heap.VmPreserved s s' ↔ (vmCoreAcc s' = vmCoreAcc s ∧ s'.mem.perm = s.mem.perm) := by
  unfold vmCoreAcc LibsignalBinary.Heap.VmPreserved LibsignalBinary.Heap.PoolPreserved
    LibsignalBinary.Heap.FdsHiFrame
  simp only [Prod.mk.injEq, funext_iff, Subtype.forall, and_imp]
  exact ⟨fun ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ => ⟨⟨h1, h2, h3, h4, h6⟩, h5⟩,
         fun ⟨⟨h1, h2, h3, h4, h6⟩, h5⟩ => ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩⟩

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCoreAcc_setPC (s : State) (pc : BitVec 64) : vmCoreAcc (s.setPC pc) = vmCoreAcc s := by
  unfold vmCoreAcc; cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCoreAcc_advancePC (s : State) : vmCoreAcc s.advancePC = vmCoreAcc s := by
  unfold vmCoreAcc; cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCoreAcc_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    vmCoreAcc (s.writeReg64 r v) = vmCoreAcc s := by
  unfold vmCoreAcc; cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCoreAcc_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    vmCoreAcc (s.writeReg32 r v) = vmCoreAcc s := vmCoreAcc_writeReg64 s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCoreAcc_writeReg (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    vmCoreAcc (s.writeReg w r v) = vmCoreAcc s := by cases w <;> exact vmCoreAcc_writeReg64 s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCoreAcc_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    vmCoreAcc (s.writeVReg128 r v) = vmCoreAcc s := by
  unfold vmCoreAcc; cases s; rfl

attribute [local irreducible] vmCoreAcc

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_setPC_acc (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_advancePC_acc (s : State) : s.advancePC.mem = s.mem := by
  cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_writeReg64_acc (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_writeReg32_acc (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).mem = s.mem := mem_writeReg64_acc s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_writeReg_acc (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).mem = s.mem := by cases w <;> exact mem_writeReg64_acc s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_writeVReg128_acc (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).mem = s.mem := by cases s; rfl

private theorem mask16_64_eq_zext (x : BitVec 64) :
    x &&& 0xffff#64 = (x.truncate 16).zeroExtend 64 := by bv_bits

private theorem zext16_trunc32_eq_trunc16 (x : BitVec 64) :
    BitVec.zeroExtend 16 (BitVec.truncate 32 x) = BitVec.truncate 16 x := by bv_bits

private theorem trunc64_shr64_eq_extractLsb64 (v : BitVec 128) :
    BitVec.truncate 64 (v >>> 64) = v.extractLsb' 64 64 := by bv_bits

/-- Conjoin `⌜VmPreserved s0 sf⌝` onto `spec.post`. -/
abbrev addVmPreservedAcc {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜LibsignalBinary.Heap.VmPreserved s0 sf⌝ ∗ spec.post x s0 sf }

/-- Relocatable specification of `spqr::encoding::gf::accelerated::mul2_unreduced` (Block `383`). -/
@[expose] def acceleratedMul2UnreducedPlacedSpec [LibsignalPlacement] :
    Spec (BitVec 16 × BitVec 16 × BitVec 16) where
  pre := fun (a, b1, b2) s =>
    ⌜BitVec.truncate 16 (s.readReg64 .x0) = a ∧
      BitVec.truncate 16 (s.readReg64 .x1) = b1 ∧
      BitVec.truncate 16 (s.readReg64 .x2) = b2⌝
  post := fun (a, b1, b2) s0 sf =>
    ⌜sf.readReg64 .x0 = mul2UnreducedWord a b1 b2 ∧
      sf.readReg64 .x1 = 0#64 ∧
      sf.trace = s0.trace⌝

/-- Relocatable `spqr::encoding::gf::accelerated::mul2_unreduced` (Block `383`) meets
`addVmPreservedAcc acceleratedMul2UnreducedPlacedSpec` under `[LibsignalPlacement]`. -/
theorem acceleratedMul2Unreduced_vm_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_383).rebase (blkPl_383).base H) (blkPl_383).base
      (addVmPreservedAcc acceleratedMul2UnreducedPlacedSpec) := by
  simp only [addVmPreservedAcc, acceleratedMul2UnreducedPlacedSpec]
  wp_init args s0
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_), ?_, ?_⟩
  · refine Entails.pure_right (by simp [vmPreserved_iff_vmCoreAcc]) ?_
    rw [← sepConj_emp ⌜_⌝]
    refine Entails.pure_right ?_ (Entails.refl emp)
    simp only [wp_norm, arm64_norm, Arm64.truncate_64_and_mask64, mask16_64_eq_zext,
      zext16_trunc32_eq_trunc16, trunc64_shr64_eq_extractLsb64]
    refine ⟨?_, Arm64.polyMul_64_pack32_u16_hi64 _ _ _⟩
    rw [Arm64.polyMul_64_pack32_u16_truncate64,
        arm64_polyMul_16_eq_unaccelerated, arm64_polyMul_16_eq_unaccelerated,
        mul2UnreducedWord, BitVec.or_comm]
    simp_all
  · wp_norm_lhs
  · simp [CalleeSavedPreserved, wp_norm, arm64_norm]

/-- Relocatable `spqr::encoding::gf::accelerated::mul2_unreduced` (Block `383`) meets
`acceleratedMul2UnreducedPlacedSpec` under `[LibsignalPlacement]`. -/
theorem acceleratedMul2Unreduced_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_383).rebase (blkPl_383).base H) (blkPl_383).base
      acceleratedMul2UnreducedPlacedSpec := by
  refine subroutine_ok_mono (acceleratedMul2Unreduced_vm_placed_ok H)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [addVmPreservedAcc] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

end CryptoVerification.SpqrV1.GF.AcceleratedMul

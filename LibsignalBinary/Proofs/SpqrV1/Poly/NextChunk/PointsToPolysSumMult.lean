/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMult1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Inlined `gf::parallel_mult`

**Checked by Lean.**

Verifies the pair loop, register reload, and full inlined `spqr::encoding::gf::parallel_mult`
(`0x6ae34..0x6b24c`, `+2736 -> +3784`).
-/

public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre
  truncate32_zext64_sm truncate32_zext64_16_sm truncate32_shl_zext64_32_sm
  truncate16_zext64_16_sm zext16_trunc32_zext64_16_sm
  truncate32_xor_zext64_sm truncate32_and_zext64_sm
  truncate64_sxth32_16_sm sbfx_bit0_sxth32_sm
  pmTerm_bit0_sm pmTerm_bit0_zext64_sm truncate16_truncate32_64_sm
  sxth32_shl30_asr31 sxth32_shl29_asr31 sxth32_shl28_asr31 sxth32_shl27_asr31
  sxth32_shl26_asr31 sxth32_shl25_asr31 sxth32_shl24_asr31 sxth32_shl23_asr31
  sxth32_shl22_asr31 sxth32_shl21_asr31 sxth32_shl20_asr31 sxth32_shl19_asr31
  sxth32_shl18_asr31 sxth32_shl17_asr31
  pmTerm_mid_sm csel_gt_cmn1_sxth32_sm csel_gt_cmn1_sxth32_zext_sm
  polyMul_pair_c1_eq polyMul_pair_c2_eq

/-! ## 1. Single Iteration of the Pair Loop (`+3384`) -/

private theorem zext64_and_mask32 (w : BitVec 32) (b : Bool) :
    BitVec.zeroExtend 64 w &&& (if b = true then 4294967295#64 else 0#64) =
      BitVec.zeroExtend 64 (w &&& (if b = true then 0xffff_ffff#32 else 0#32)) := by
  cases b <;> bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem pmTerm_bit0_64 (yv x : BitVec 16) :
    (if x.getLsbD 0 = true then 4294967295#64 else 0#64) &&& BitVec.zeroExtend 64 yv =
      BitVec.zeroExtend 64 (pmTerm_sm yv x 0) := by
  have h : pmTerm_sm yv x 0 =
      (BitVec.zeroExtend 32 yv <<< 0) &&& (if x.getLsbD 0 = true then 0xffff_ffff#32 else 0#32) := by
    unfold pmTerm_sm; rfl
  rw [h]; generalize x.getLsbD 0 = b; cases b <;> bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem pmTerm_mid_64 (yv x : BitVec 16) (i : Nat) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 yv <<< i) &&&
      (if x.getLsbD i = true then 4294967295#64 else 0#64) =
      BitVec.zeroExtend 64 (pmTerm_sm yv x i) := by
  have h : pmTerm_sm yv x i =
      (BitVec.zeroExtend 32 yv <<< i) &&& (if x.getLsbD i = true then 0xffff_ffff#32 else 0#32) := by
    unfold pmTerm_sm; rfl
  rw [h]; exact zext64_and_mask32 _ _

@[local arm64_norm, local wp_norm]
theorem sub2_ofNat_pair (k : Nat) :
    BitVec.ofNat 64 (2 * (k + 1)) - 2#64 = BitVec.ofNat 64 (2 * k) := by
  have h2 : BitVec.ofNat 64 (2 * (k + 1)) = BitVec.ofNat 64 (2 * k) + 2#64 := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, BitVec.ofNat_add]
  rw [h2]; bv_omega

@[local arm64_norm, local wp_norm]
theorem sub2_ofNat_pair_add (k : Nat) :
    BitVec.ofNat 64 (2 * (k + 1)) + 18446744073709551614#64 = BitVec.ofNat 64 (2 * k) := by
  have h1 : (18446744073709551614#64 : BitVec 64) = -2#64 := rfl
  have h2 : BitVec.ofNat 64 (2 * (k + 1)) = BitVec.ofNat 64 (2 * k) + 2#64 := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, BitVec.ofNat_add]
  rw [h1, h2]; bv_omega

@[local arm64_norm, local wp_norm]
theorem add2_ofNat_pair (k : Nat) :
    BitVec.ofNat 64 (2 * (k + 1)) + 2#64 = BitVec.ofNat 64 (2 * (k + 2)) := by
  rw [show 2 * (k + 2) = 2 * (k + 1) + 2 by omega, BitVec.ofNat_add]

theorem ule_n_2k {k n : Nat} (hk : 2 * (k + 1) ≤ n) (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2 * k)) = false := by
  rw [Bool.eq_false_iff, Ne, BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem ult_2k_n {k n : Nat} (hk : 2 * (k + 1) ≤ n) (hn : n ≤ 0x0555555555555555) :
    (!((BitVec.ofNat 64 (2 * k)).ult (BitVec.ofNat 64 n))) = false := by
  rw [Bool.not_eq_false', BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem ult_n_2k2 {k n : Nat} (hn : n ≤ 0x0555555555555555) (hk : 2 * (k + 1) ≤ n) :
    (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 (2 * (k + 2))) = decide (n < 2 * (k + 2)) := by
  by_cases h : n < 2 * (k + 2)
  · rw [decide_eq_true_iff.mpr h, BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [decide_eq_false_iff_not.mpr h, Bool.eq_false_iff, Ne, BitVec.ult_iff_toNat_lt,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem hi_2k2_n {k n : Nat} (hn : n ≤ 0x0555555555555555) (hk : 2 * (k + 1) ≤ n) :
    ((!((BitVec.ofNat 64 (2 * (k + 2))).ult (BitVec.ofNat 64 n))) &&
     !(BitVec.ofNat 64 (2 * (k + 2)) == BitVec.ofNat 64 n)) = decide (n < 2 * (k + 2)) := by
  have h1 : (BitVec.ofNat 64 (2 * (k + 2))).toNat = 2 * (k + 2) := Nat.mod_eq_of_lt (by omega)
  have h2 : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt (by omega)
  by_cases hlt : n < 2 * (k + 2)
  · have hult : (BitVec.ofNat 64 (2 * (k + 2))).ult (BitVec.ofNat 64 n) = false := by
      rw [Bool.eq_false_iff, Ne, BitVec.ult_iff_toNat_lt, h1, h2]; omega
    have hbeq : (BitVec.ofNat 64 (2 * (k + 2)) == BitVec.ofNat 64 n) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have hto := congrArg BitVec.toNat heq; rw [h1, h2] at hto; omega
    simp [hlt, hult, hbeq]
  · by_cases heq : 2 * (k + 2) = n
    · subst heq; simp
    · have hult : (BitVec.ofNat 64 (2 * (k + 2))).ult (BitVec.ofNat 64 n) = true := by
        rw [BitVec.ult_iff_toNat_lt, h1, h2]; omega
      simp [hlt, hult]

/-- Action of the pair loop (`0x6b0bc..0x6b0ec -> 0x6aec4..0x6b0b8`) on a `List GF16`:
    multiplies all complete pairs by `yv` and leaves a trailing odd element unchanged. -/
@[expose] def parallelMultPairs (yv : BitVec 16) : List GF16 → List GF16
  | [] => []
  | [last] => [last]
  | c1 :: c2 :: rest =>
    ⟨unaccelerated.mul yv c1.value⟩ ::
    ⟨unaccelerated.mul yv c2.value⟩ ::
    parallelMultPairs yv rest

@[simp]
theorem parallelMultPairs_nil (yv : BitVec 16) :
    parallelMultPairs yv [] = [] := rfl

@[simp]
theorem parallelMultPairs_singleton (yv : BitVec 16) (last : GF16) :
    parallelMultPairs yv [last] = [last] := rfl

@[simp]
theorem parallelMultPairs_pair_cons (yv : BitVec 16) (c1 c2 : GF16) (rest : List GF16) :
    parallelMultPairs yv (c1 :: c2 :: rest) =
      ⟨unaccelerated.mul yv c1.value⟩ ::
      ⟨unaccelerated.mul yv c2.value⟩ ::
      parallelMultPairs yv rest := rfl

theorem parallelMultPairs_even_eq (yv : BitVec 16) :
    ∀ cs : List GF16, cs.length % 2 = 0 →
      parallelMultPairs yv cs = parallelMult ⟨yv⟩ cs
  | [], _ => rfl
  | [_], h => by simp at h
  | c1 :: c2 :: rest, h => by
    have h' : rest.length % 2 = 0 := by simp at h; omega
    simp [parallelMultPairs_pair_cons, parallelMult_pair_cons, parallelMultPairs_even_eq yv rest h']

theorem gf16SliceAt_pair_cons (ptr : BitVec 64) (c1 c2 : GF16) (rest : List GF16) :
    gf16SliceAt ptr (c1 :: c2 :: rest) =
      (gf16At c1 ptr ∗ gf16At c2 (ptr + 2#64) ∗ gf16SliceAt (ptr + 4#64) rest) := by
  simp only [gf16SliceAt, arrayAt, gf16Stride, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [show (ptr + 2#64) + 2#64 = ptr + 4#64 by bv_omega]

theorem gf16SliceAt_parallelMultPairs_odd (yv : BitVec 16) :
    ∀ (cs : List GF16) (ptr : BitVec 64),
      cs.length % 2 = 1 →
      ∃ (last : GF16) (Rest : SepProp),
        gf16SliceAt ptr (parallelMultPairs yv cs) =
          (gf16At last (ptr + BitVec.ofNat 64 (2 * (2 * (cs.length / 2)))) ∗ Rest) ∧
        (gf16At ⟨unaccelerated.mul last.value yv⟩
           (ptr + BitVec.ofNat 64 (2 * (2 * (cs.length / 2)))) ∗ Rest) =
          gf16SliceAt ptr (parallelMult ⟨yv⟩ cs)
  | [], _, h => by simp at h
  | [last], ptr, _ => by
    have h0 : ptr + BitVec.ofNat 64 (2 * (2 * (1 / 2))) = ptr := by bv_omega
    refine ⟨last, emp, ?_, ?_⟩ <;>
      simp only [List.length_singleton, parallelMultPairs_singleton, parallelMult_singleton,
        gf16SliceAt, arrayAt, h0]
  | c1 :: c2 :: rest, ptr, h => by
    have h' : rest.length % 2 = 1 := by simp at h; omega
    obtain ⟨last, Rest', hpre, hpost⟩ := gf16SliceAt_parallelMultPairs_odd yv rest (ptr + 4#64) h'
    have haddr : (ptr + 4#64) + BitVec.ofNat 64 (2 * (2 * (rest.length / 2))) =
        ptr + BitVec.ofNat 64 (2 * (2 * ((c1 :: c2 :: rest).length / 2))) := by
      have hdiv : (c1 :: c2 :: rest).length / 2 = rest.length / 2 + 1 := by simp; omega
      rw [hdiv, show 2 * (2 * (rest.length / 2 + 1)) = 4 + 2 * (2 * (rest.length / 2)) by omega,
          BitVec.ofNat_add]; bv_omega
    refine ⟨last,
      gf16At ⟨unaccelerated.mul yv c1.value⟩ ptr ∗
        gf16At ⟨unaccelerated.mul yv c2.value⟩ (ptr + 2#64) ∗ Rest',
      ?_, ?_⟩
    · rw [parallelMultPairs_pair_cons, gf16SliceAt_pair_cons, hpre, ← haddr]; ac_rfl
    · rw [parallelMult_pair_cons, gf16SliceAt_pair_cons, ← hpost, ← haddr]; dsimp only; ac_rfl

theorem ule_n_even {n : Nat} (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (2 * (n / 2))) = decide (n % 2 = 0) := by
  by_cases h : n % 2 = 0
  · rw [decide_eq_true_iff.mpr h, BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [decide_eq_false_iff_not.mpr h, Bool.eq_false_iff, Ne, BitVec.ule_iff_toNat_le,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem not_ult_even {n : Nat} (hn : n ≤ 0x0555555555555555) :
    (!((BitVec.ofNat 64 (2 * (n / 2))).ult (BitVec.ofNat 64 n))) = decide (n % 2 = 0) := by
  by_cases h : n % 2 = 0
  · rw [decide_eq_true_iff.mpr h, Bool.not_eq_true', Bool.eq_false_iff, Ne, BitVec.ult_iff_toNat_lt,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [decide_eq_false_iff_not.mpr h, Bool.not_eq_false', BitVec.ult_iff_toNat_lt,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

end CryptoVerification.SpqrV1.Poly.NextChunk

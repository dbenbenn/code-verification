/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Defs
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-!
# 4K-Stack `RawVec<GF16>::grow_one` Support for `<Poly>::compute_at`

Lifts `finish_grow [local#7]`, `grow_one_gf16_bs_ok_ext`, `grow_one_gf16_full_ok_ext`,
`grow_one_gf16_zero_ok_at`, and `grow_one_gf16_one_ok_at` to `AllocContracts4K`.
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap (RustAlloc allocHookStack allocFailedIn LayoutOk)
open CryptoVerification.SpqrV1.Alloc.GrowOneNorm (
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre)
open CryptoVerification.SpqrV1.Poly.ComputeAt (computeAtName
  growOneGF16ZeroSpec growOneGF16OneSpec)

namespace LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.GrowOneExt

open CryptoVerification.SpqrV1.Alloc (finishGrowSpecWithStack growOneStack stackAt_doReserve_gen)

open CryptoVerification.LibsignalTripleRatchet (FinishGrowCall finishGrowStack)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Private 4K `finish_grow [local#7]` Support -/

private theorem umulh_stride_eq_zero_4k {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3,
    Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]
  rfl

private theorem mul_stride_toNat_4k {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat_4k {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat_4k h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem beq_mul_stride_zero_eq_false_4k {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat_4k h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem hi_stride_eq_false_4k {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]; change align.toNat ≤ 2 ^ 63; omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat_4k (by omega)]
  omega

private def finishGrow8AllocSpecG_4k (A : RustAlloc) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A allocHookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧ x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (allocHookStack + 48) }

private def finishGrow8ReallocSpecG_4k (A : RustAlloc) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A allocHookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (allocHookStack + 48) }

private theorem stackAt_growOne_4k (sp : BitVec 64) :
    stackAt sp growOneStack = stackAt (sp - 64#64) finishGrowStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗ ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) :=
  stackAt_doReserve_gen sp (by decide)

private theorem grow_new_cap_eq_4k {cap : BitVec 64} (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have h2 : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  have hsh : cap <<< 1 = BitVec.ofNat 64 (2 * cap.toNat) :=
    BitVec.eq_of_toNat_eq (by rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  by_cases hlt : 4 < 2 * cap.toNat
  · have hult : (4#64).ult (cap <<< 1) = true := by
      rw [BitVec.ult_eq_decide, decide_eq_true_iff, h2]; exact hlt
    rw [hult]; simp only [↓reduceIte, hsh, (by omega : max (2 * cap.toNat) 4 = 2 * cap.toNat)]
  · have hult : (4#64).ult (cap <<< 1) = false := by
      rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, h2]; exact hlt
    rw [hult]; simp only [Bool.false_eq_true, ↓reduceIte, (by omega : max (2 * cap.toNat) 4 = 4)]

private theorem memRegion8_split_16_16_4_4k (p' : BitVec 64) :
    memRegion p' 8 =
      (∃∗ w1 : BitVec 16, ∃∗ w0 : BitVec 16,
        (p' ↦₁₆ w0) ∗ ((p' + 2#64) ↦₁₆ w1) ∗ memRegion (p' + 4#64) 4) := by
  rw [show (8 : Nat) = 2 + (2 + 4) by rfl,
      memRegion_split p' 2 (2 + 4) (by decide),
      memRegion_split (p' + 2#64) 2 4 (by decide),
      ProofLib.memRegion_two p', ProofLib.memRegion_two (p' + 2#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem pointsTo16_one_eq_bytes_4k (a : BitVec 64) :
    (a ↦₁₆ 1#16) = (a ↦ₛ [1#8, 0#8]) := by
  simp only [pointsTo16, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_zero]
  rfl

private theorem memRegion6_split_16_4_4k (p' : BitVec 64) :
    memRegion (p' + 2#64) 6 =
      (∃∗ w1 : BitVec 16, ((p' + 2#64) ↦₁₆ w1) ∗ memRegion (p' + 4#64) 4) := by
  rw [show (6 : Nat) = 2 + 4 by rfl,
      memRegion_split (p' + 2#64) 2 4 (by decide),
      ProofLib.memRegion_two (p' + 2#64)]
  simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd]

end LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.GrowOneExt

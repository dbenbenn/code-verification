/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.GrowOneSpecs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOne -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrow -- proof-setup: allow-public-import

/-!
# Sysroot `RawVec::{grow_one, finish_grow}` on `tripleRatchetProgAtExt`

Verifies `finish_grow [liballoc]`, `RawVec<u8>::grow_one`, `finish_grow [libstd]`, and
`RawVec<Vec<u8>>::grow_one` (blocks 619..622) on `tripleRatchetProgAtExt` under
`AllocContracts`, `AllocContracts4K`, and `AllocContractsX`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.CodeLayout
open DoReserveNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev finishGrowLiballocName : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [liballoc]"

abbrev finishGrowLibstdName : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]"

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : stride.toNat * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]; rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
  BitVec.eq_of_toNat_eq (by rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h])

private theorem mul_stride_ne_zero {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq; have ht := congrArg BitVec.toNat heq; rw [mul_stride_toNat h] at ht
  change new.toNat * stride.toNat = 0 at ht; omega

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; exact mul_stride_ne_zero h0 h

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]; · simp
    · rw [BitVec.le_def]; change align.toNat ≤ 2 ^ 63; omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat (by omega)]; omega

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]; exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht; omega

private theorem stackAt_finishGrow_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 48) = stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hhook

private theorem stackAt_finishGrow32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 32) = stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp hookStack 4 hhook

private theorem grow_new_cap_eq_local {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change 4 < 2 * cap.toNat at hc; omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change ¬ 4 < 2 * cap.toNat at hc
    change 4 = max (2 * cap.toNat) 4; omega

private theorem grow_new_cap_u8_eq_local {cap : BitVec 64}
    (h : max (2 * cap.toNat) 8 < 2 ^ 63) :
    (if (8#64).ult (cap <<< 1) = true then cap <<< 1 else 8#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 8) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (8#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change 8 < 2 * cap.toNat at hc; omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change ¬ 8 < 2 * cap.toNat at hc
    change 8 = max (2 * cap.toNat) 8; omega

/-! ## `finish_grow [libstd]` (Generic `stride` and `align`) -/

private def finishGrow8AllocSpecG_sys (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 48) }

private def finishGrow8ReallocSpecG_sys (A : RustAlloc) (hookStack : Nat) : Spec FinishGrowCall :=
  { finishGrowSpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 48) }

private def finishGrow1AllocSpecG_sys (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 32) }

private def finishGrow1ReallocSpecG_sys (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 32) }

/-- Prefix-preserving contract (`bs.length ≤ cap.toNat`) for `RawVec<u8>::grow_one` parameterized by `hookStack`. -/
@[expose] def growOneU8BsSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 8 < 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
    A.pool ∗ stackAt s.sp ((hookStack + 32) + 64)
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗
      (v ↦₆₄ newCapU8 cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 8) 1 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 8 - bs.length)) ∗
    A.pool ∗ stackAt s0.sp ((hookStack + 32) + 64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem growOneU8_ok_of_bs {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (hbs : subroutine_ok P addr (growOneU8BsSpecWithStack A allocHookStack)) :
    subroutine_ok P addr (growOneU8Spec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let Frame : SepProp := memRegion (s0.sp - 16384#64) 12192
  have hstack : stackAt s0.sp extHookStack =
      Frame ∗ stackAt s0.sp ((allocHookStack + 32) + 64) :=
    ProofLib.stackAt_split_bottom s0.sp ((allocHookStack + 32) + 64) 12192 (by decide)
  simp only [growOneU8Spec, BitVec.ofNat_eq_ofNat, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (growOneU8BsSpecWithStack A allocHookStack).pre (x.v, x.cap, x.ptr, x.bs) s0 ∗
        (Frame ∗ R) := by
    simp only [growOneU8BsSpecWithStack, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨⟨hx0, Nat.le_of_eq hlen, hptr, hbound⟩, ?_⟩
    rw [hstack] at hmem
    by_cases hcap0 : x.cap = 0#64
    · simp only [hcap0, ite_true] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    · simp only [hcap0, ite_false, ← hlen, Nat.sub_self, memRegion_zero, sepConj_emp,
        sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  refine hbs.mono_outcome (x.v, x.cap, x.ptr, x.bs) (Frame ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [growOneU8BsSpecWithStack, growOneU8Spec] at hq ⊢
    rw [hstack]
    simp only [hlen, BitVec.ofNat_eq_ofNat] at hq ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
  · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
    dsimp only [growOneU8BsSpecWithStack, growOneU8Spec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact False.elim (allowPanic_not_exited hq)
  · exact False.elim (allowPanic_not_exited hq)

/-- Prefix-preserving contract (`bs.length ≤ cap.toNat * 24`) for `RawVec<Vec<u8>>::grow_one` parameterized by `hookStack`. -/
@[expose] def growOneVecU8BsSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat * 24 ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 24) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 24 - bs.length)) ∗
    A.pool ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 24) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * 24 - bs.length)) ∗
    A.pool ∗ stackAt s0.sp ((hookStack + 48) + 64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem growOneVecU8_ok_of_full {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (hfull : subroutine_ok P addr (growOneStrideFullSpec A 24 8)) :
    subroutine_ok P addr (growOneVecU8Spec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let Frame : SepProp := memRegion (s0.sp - 16384#64) 12176
  have hstack : stackAt s0.sp extHookStack = Frame ∗ stackAt s0.sp growOneStack :=
    ProofLib.stackAt_split_bottom s0.sp growOneStack 12176 (by decide)
  simp only [growOneVecU8Spec, BitVec.ofNat_eq_ofNat, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (growOneStrideFullSpec A 24 8).pre (x.v, x.cap, x.ptr, x.bs) s0 ∗ (Frame ∗ R) := by
    simp only [growOneStrideFullSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen, hptr, hbound⟩, ?_⟩
    rw [hstack] at hmem
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  refine hfull.mono_outcome (x.v, x.cap, x.ptr, x.bs) (Frame ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [growOneStrideFullSpec, growOneVecU8Spec, newCapVecU8] at hq ⊢
    rw [hstack]
    simp only [BitVec.ofNat_eq_ofNat] at hq ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
  · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
    dsimp only [growOneStrideFullSpec, growOneVecU8Spec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact False.elim (allowPanic_not_exited hq)
  · exact False.elim (allowPanic_not_exited hq)

/-- `growOneVecU8Spec A` lifted to a 32 KiB caller stack (`serializeSubStackX`). -/
@[expose] def growOneVecU8Stack32kSpec (A : RustAlloc) : Spec GrowOneCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat * 24 ∧ x.ptr ≠ 0 ∧
      max (2 * x.cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length 8 ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool ∗ stackAt s.sp 32768
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ (p' : BitVec 64),
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (x.v ↦₆₄ newCapVecU8 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * x.cap.toNat) 4 * 24) 8 ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) ((max (2 * x.cap.toNat) 4 - x.cap.toNat) * 24)) ∗
      A.pool ∗ stackAt s0.sp 32768
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.SpqrV1.Alloc

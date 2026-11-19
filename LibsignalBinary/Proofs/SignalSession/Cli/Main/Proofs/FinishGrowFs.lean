/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.Layout -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `finish_grow [local#12]` Preserving `fs` (`Spec.keepsFs`)

Proves `<alloc::raw_vec::RawVecInner>::finish_grow [local#12]` satisfies
`(finishGrowSpecX A).keepsFs.inImage img` under `AllocContractsFs img A ext`, together with
`SpecRefines` cell-form corollaries for zero and nonzero capacities.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm]
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

private theorem subroutine_ok_of_keepsFs {α : Type} {P : Program} {e : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P e spec.keepsFs) :
    subroutine_ok P e spec := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (h.to_outcome x R s0 hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.keepsFs] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

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
  rw [hdiv]
  rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem mul_stride_ne_zero {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_stride_ne_zero h0 h

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]
      change align.toNat ≤ 2 ^ 63
      omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat (by omega)]
  omega

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_finishGrowX (sp : BitVec 64) :
    stackAt sp finishGrowStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 16384 6 (by decide)

private def finishGrowZeroFsSpec2X (A : RustAlloc) : Spec FinishGrowCall :=
  ({ finishGrowSpecX A with
      pre := fun x s =>
        ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
          s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
          x.cap = 0#64 ∧ x.bs = [] ∧
          x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
          LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
        memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp finishGrowStackX } : Spec FinishGrowCall).keepsFs

private def finishGrowNeFsSpec2X (A : RustAlloc) : Spec FinishGrowCall :=
  ({ finishGrowSpecX A with
      pre := fun x s =>
        ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
          s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
          x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
          x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
          LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
        memRegion x.out 24 ∗
        A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
        memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
          (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
        A.pool ∗ stackAt s.sp finishGrowStackX } : Spec FinishGrowCall).keepsFs

/-- Spec-level refinement witness that simultaneously lifts both `subroutine_ok` and `Spec.keepsFs`. -/
@[expose] def SpecRefines {α β : Type} (spec1 : Spec α) (spec2 : Spec β) : Prop :=
  ∀ (y : β) (R : SepProp) (s0 : State),
    s0.mem ⊨ spec2.pre y s0 ∗ R →
    ∃ (x : α) (F : SepProp),
      s0.mem ⊨ spec1.pre x s0 ∗ F ∧
      (∀ sf, sf.mem ⊨ spec1.post x s0 sf ∗ F → sf.mem ⊨ spec2.post y s0 sf ∗ R) ∧
      (∀ sf, sf.mem ⊨ spec1.onPanic x s0 sf ∗ F → sf.mem ⊨ spec2.onPanic y s0 sf ∗ R) ∧
      (∀ c sf, sf.mem ⊨ spec1.onExit x c s0 sf ∗ F → sf.mem ⊨ spec2.onExit y c s0 sf ∗ R) ∧
      (∀ sf, sf.mem ⊨ spec1.onOom x s0 sf ∗ F → sf.mem ⊨ spec2.onOom y s0 sf ∗ R)

theorem SpecRefines.apply_ok {α β : Type} {P : Program} {e : BitVec 64}
    {spec1 : Spec α} {spec2 : Spec β}
    (href : SpecRefines spec1 spec2) (h1 : subroutine_ok P e spec1) :
    subroutine_ok P e spec2 := by
  apply subroutine_ok_outcome_intro
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨x, F, hpre1, hpost, hpan, hex, hoom⟩ := href y R s0 hpre
  refine (h1.to_outcome x F s0 hpc hrun hpre1 hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp, hq⟩ | ⟨c, he, hq⟩ | ⟨ho, hq⟩
  · exact Or.inl ⟨hret, hcc, hpost sf hq⟩
  · exact Or.inr (Or.inl ⟨hp, hpan sf hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hex c sf hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom sf hq⟩))

theorem SpecRefines.apply_keepsFs {α β : Type} {P : Program} {e : BitVec 64}
    {spec1 : Spec α} {spec2 : Spec β}
    (href : SpecRefines spec1 spec2) (h1 : subroutine_ok P e spec1.keepsFs) :
    subroutine_ok P e spec2.keepsFs := by
  apply subroutine_ok_outcome_intro
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨x, F, hpre1, hpost, hpan, hex, hoom⟩ := href y R s0 hpre
  refine (h1.to_outcome x F s0 hpc hrun hpre1 hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp, hq⟩ | ⟨c, he, hq⟩ | ⟨ho, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.keepsFs] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨hq.1, hpost sf hq.2⟩
  · exact Or.inr (Or.inl ⟨hp, hpan sf hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hex c sf hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom sf hq⟩))

private theorem pull_fg0_err (O1 O2 O3 P A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ P ∗ A ∗ S) ∗ R = P ∗ ((A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg0_ok (O1 O2 O3 P L M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg1_post (O1 O2 O3 P L B M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ B ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ B ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

end CryptoVerification.SignalSession.Cli.MainHops

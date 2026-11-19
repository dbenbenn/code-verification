/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Disproof.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FinishGrowFs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `do_reserve_and_handle [local#11]` Contracts and Unbounded-Capacity Counterexample

Verifies `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle [local#11]`:
- `reserve11_raw_ok` and `reserve11_raw_fs_ok`: general `(stride, align)` contract `doReserveStrideRawSpecX`
  and its `.keepsFs` strengthening via `finish_grow [local#12]`.
- `reserve1_ok`, `cliDoReserve_ok`, `reserve16Cap_ok` (`16 * cap < 2 ^ 62`), `reserve16Eq_ok`
  (`cap = len`), and `reserve16_ok`.
- `not_subroutine_ok_reserve16Spec`: binary counterexample refuting `reserve16SpecR2` (which omits
  `16 * cap < 2 ^ 62`) at `cap = 2 ^ 58, bs = []`, where `finish_grow` panics on capacity overflow
  without invoking the allocator.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace Reserve11Norm

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

theorem repack_stack_bound (C0 C1 C2 Buf Pool Stack R : SepProp) :
    C0 ∗ C1 ∗ C2 ∗ Buf ∗ Pool ∗ Stack ∗ R =
      Stack ∗ (C0 ∗ (C1 ∗ C2 ∗ Buf ∗ Pool ∗ R)) := by ac_rfl

theorem repack_raw_pre (C0 C1 C2 Buf Pool Extra SubStack R : SepProp) :
    C0 ∗ C1 ∗ C2 ∗ Buf ∗ Pool ∗ (Extra ∗ SubStack) ∗ R =
      C0 ∗ C1 ∗ Buf ∗ Pool ∗ SubStack ∗ (C2 ∗ Extra ∗ R) := by ac_rfl

theorem repack_raw_post (C0' C1' C2 Live' Bs' Tail' Pool Extra SubStack R : SepProp) :
    (C0' ∗ C1' ∗ Live' ∗ Bs' ∗ Tail') ∗ (Pool ∗ SubStack) ∗ (C2 ∗ Extra ∗ R) =
      (C0' ∗ C1' ∗ C2 ∗ Live' ∗ Bs' ∗ Tail') ∗ (Pool ∗ Extra ∗ SubStack) ∗ R := by ac_rfl

theorem repack_anyHeap (F1 F2 R : SepProp) :
    anyHeap ∗ (F1 ∗ F2 ∗ R) = (anyHeap ∗ F1 ∗ F2) ∗ R := by ac_rfl

end Reserve11Norm

open Reserve11Norm

attribute [local wp_norm]
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

/-! ## 1. Decodes & arithmetic helpers for `do_reserve_and_handle [local#11]` -/

private theorem adds_cs_eq_false {x2 x1 : BitVec 64}
    (h : x2.toNat + x1.toNat < 2 ^ 64) :
    (x2 + x1).ult x2 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

private theorem reserve_new_cap_stride_eq {stride cap x1 x2 : BitVec 64} {len additional : Nat}
    (hx1 : x1.toNat = len) (hx2 : x2.toNat = additional)
    (h : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63) :
    (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
          (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = true then
      if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1
     else if (stride == 1#64) = true then 8#64 else 4#64) =
      BitVec.ofNat 64 (SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional) := by
  have hmin_ge : 4 ≤ SpqrV1.Alloc.reserveMinCap stride.toNat := by
    unfold SpqrV1.Alloc.reserveMinCap; split <;> omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (SpqrV1.Alloc.reserveMinCap stride.toNat) < 2 ^ 63 := h
  have hadd : (x2 + x1).toNat = len + additional := by
    rw [BitVec.toNat_add, hx2, hx1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm0 : (if (stride == 1#64) = true then 8#64 else 4#64).toNat =
      SpqrV1.Alloc.reserveMinCap stride.toNat := by
    by_cases hs : (stride == 1#64) = true
    · have hs' : stride = 1#64 := beq_iff_eq.mp hs
      subst hs'
      rfl
    · have hs' : stride.toNat ≠ 1 := by
        intro h1
        apply hs
        exact beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h1)
      simp only [hs, Bool.false_eq_true, ite_false, SpqrV1.Alloc.reserveMinCap, hs']
      rfl
  have hm1 : (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1).toNat =
      max (len + additional) (2 * cap.toNat) := by
    by_cases hc : (cap <<< 1).ult (x2 + x1) = true
    · simp only [hc, ite_true, hadd]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
    · simp only [hc, Bool.false_eq_true, ite_false, hsh]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
  apply BitVec.eq_of_toNat_eq
  dsimp only [SpqrV1.Alloc.reserveCapStride]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize (if (stride == 1#64) = true then 8#64 else 4#64) = m0 at hm0 ⊢
  generalize (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = m1 at hm1 ⊢
  by_cases hc2 : m0.ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false, hm0]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2
    omega

/-! ## 2. General `(stride, align)` raw contract (`reserve11_raw_ok`) -/

/-- General raw `(stride, align)` contract of `do_reserve_and_handle [local#11]` (`reserve11Name`)
at stack budget `doReserveStackX`. -/
@[expose] def doReserveStrideRawSpecX (A : RustAlloc) : Spec SpqrV1.Alloc.DoReserveStrideCall where
  pre := fun x s =>
    let newCap := SpqrV1.Alloc.reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.len ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = x.align ∧
      s.readReg64 .x4 = x.stride ∧
      x.len ≤ x.cap.toNat ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.ptr ≠ 0#64 ∧ 0 < x.stride.toNat ∧ LayoutOk (newCap * x.stride.toNat) x.align.toNat⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
         (x.cap.toNat * x.stride.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp doReserveStackX
  post := fun x s0 sf =>
    let newCap := SpqrV1.Alloc.reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0⌝ ∗
      (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' (newCap * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length)
        (newCap * x.stride.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp doReserveStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

private theorem vec16At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vec16At A v cap ptr bs =
      ⌜bs.length % 16 = 0 ∧ bs.length ≤ 16 * cap.toNat ∧ 16 * cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length / 16)) ∗
      (if cap = 0#64 then emp
       else A.live ptr (16 * cap.toNat) 8 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (16 * cap.toNat - bs.length)) := by
  simp only [vec16At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

/-- Capacity-bounded `reserve16Spec` requiring `16 * x.cap.toNat < 2 ^ 62` so
`newCap = max (max (len + 1) (2 * cap)) 4` satisfies `LayoutOk (newCap * 16) 8`. -/
@[expose] def reserve16CapSpec (A : RustAlloc) (resStack : Nat) : Spec Reserve16Call where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.v ∧ s0.readReg64 .x1 = BitVec.ofNat 64 (x.bs.length / 16) ∧
      s0.readReg64 .x2 = 1#64 ∧ s0.readReg64 .x3 = 8#64 ∧ s0.readReg64 .x4 = 16#64 ∧
      16 * (x.bs.length / 16 + 1) < 2 ^ 62 ∧ 16 * x.cap.toNat < 2 ^ 62⌝ ∗
      vec16At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp resStack
  post := (reserve16Spec A resStack).post
  onPanic := (reserve16Spec A resStack).onPanic

/-- Equality-guarded `reserve16Spec` for `Vec::push` growth (`x.cap = BitVec.ofNat 64 (x.bs.length / 16)`),
preserving `sf.trace = s0.trace ∧ sf.fs = s0.fs` and `allocFailedIn s0 sf` on panic. -/
@[expose] def reserve16EqSpec (A : RustAlloc) (resStack : Nat) : Spec Reserve16Call where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.v ∧ s0.readReg64 .x1 = BitVec.ofNat 64 (x.bs.length / 16) ∧
      s0.readReg64 .x2 = 1#64 ∧ s0.readReg64 .x3 = 8#64 ∧ s0.readReg64 .x4 = 16#64 ∧
      16 * (x.bs.length / 16 + 1) < 2 ^ 62 ∧
      x.cap = BitVec.ofNat 64 (x.bs.length / 16)⌝ ∗
      vec16At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp resStack
  post := (reserve16Spec A resStack).post
  onPanic := (reserve16Spec A resStack).onPanic

private theorem pull_live_bound (C0 C1 C2 Live Rest : SepProp) :
    C0 ∗ C1 ∗ C2 ∗ Live ∗ Rest = Live ∗ (C0 ∗ C1 ∗ C2 ∗ Rest) := by ac_rfl

/-- Unbounded-capacity variant of `reserve16Spec` omitting `16 * x.cap.toNat < 2 ^ 62`,
refuted by `not_subroutine_ok_reserve16Spec` below. -/
@[expose] def reserve16SpecR2 (A : RustAlloc) (resStack : Nat) : Spec Reserve16Call where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.v ∧ s0.readReg64 .x1 = BitVec.ofNat 64 (x.bs.length / 16) ∧
      s0.readReg64 .x2 = 1#64 ∧ s0.readReg64 .x3 = 8#64 ∧ s0.readReg64 .x4 = 16#64 ∧
      16 * (x.bs.length / 16 + 1) < 2 ^ 62⌝ ∗
      vec16At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp resStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜x.bs.length / 16 + 1 ≤ cap'.toNat⌝ ∗ vec16At A x.v cap' p' x.bs) ∗
      A.pool ∗ stackAt s0.sp resStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap

/-- Pure side conditions of `reserve16SpecR2.pre` and `vec16At` hold simultaneously at
`cap = BitVec.ofNat 64 (2 ^ 58)`, `bs = []` (`16 * cap.toNat = 2 ^ 62 < 2 ^ 63`). -/
theorem reserve16_overflow_call_valid :
    let cap : BitVec 64 := BitVec.ofNat 64 (2 ^ 58)
    let bs : List (BitVec 8) := []
    16 * (bs.length / 16 + 1) < 2 ^ 62 ∧
      bs.length % 16 = 0 ∧ bs.length ≤ 16 * cap.toNat ∧ 16 * cap.toNat < 2 ^ 63 := by
  decide

private def finishGrowOverflowSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (out, cap, ptr, v1, v2) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 (2 ^ 59) ∧
      s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 16#64⌝ ∗
    (out ↦₆₄ v1) ∗ ((out + 8#64) ↦₆₄ v2) ∗ stackAt s.sp finishGrowStackX
  post := fun (out, _, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (out ↦₆₄ 1#64) ∗ ((out + 8#64) ↦₆₄ 0#64) ∗ stackAt s0.sp finishGrowStackX

private theorem stackAt_finishGrowX (sp : BitVec 64) :
    stackAt sp finishGrowStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 16384 6 (by decide)

end CryptoVerification.SignalSession.Cli.MainHops

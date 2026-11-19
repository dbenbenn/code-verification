/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WPp
meta import ProofLib.SepLogic.WPp -- shake: keep

/-!
# Budget-Threaded `AllocContracts4K` Contracts for `finish_grow` and `do_reserve_and_handle`

Re-exports `finish_grow_{8,2,4}_ok_ext_4k` from `DoReserveExtBudgetAux` and proves
`do_reserve_{7,2,4}_*ok_ext_4k` under `Hooks4KBudget.AllocContracts4K b A lim ext`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget

open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX extHookStack finishGrowStack finishGrowStackX reserveCap)

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8At)
open CryptoVerification.SpqrV1.Alloc (
  DoReserveStrideCall adds_cs_eq_false
  doReserve2Name doReserve4Name doReserve7Name
  finishGrow2Name finishGrow4Name finishGrow8Name
  reserveCapStride reserveCapStride_one reserveMinCap
  reserve_new_cap_eq reserve_new_cap_stride_eq
  stackAt_doReserve32_gen stackAt_doReserve_gen
)
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents finishGrowSpec finishGrowSpecWithStack fitsEnv_doReserve_iff
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (
  finishGrow1Spec finishGrow1SpecWithStack
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (
  DoReserveStrideEnv doReserve1Raw32Spec doReserve1Raw32SpecWithStack
  doReserve1RawSpec doReserve1RawSpecWithStack
  doReserveRawSpec doReserveRawSpecWithStack
  doReserveSpec doReserveSpecWithStack doReserveSpecX
  doReserveStrideEvents doReserveStrideRawSpec doReserveStrideRawSpecWithStack
  finish_grow_24_ne_cells_of_spec finish_grow_24_zero_cells_of_spec
  finish_grow_8_ne_cells_of_spec finish_grow_8_zero_cells_of_spec
  fitsEnv_doReserveStride_iff
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Re-Exported `finish_grow` Contracts -/

private theorem do_reserve_7_raw_of_stride {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hs : subroutine_ok P addr (doReserveStrideRawSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (doReserveRawSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveRawSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfits⟩, hmem⟩
  let xs : DoReserveStrideCall := ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hrlay : RustLayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 :=
    ⟨⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hfits' : FitsEnv M lim st (DoReserveStrideEnv xs) := by
    rw [fitsEnv_doReserve_iff] at hfits
    rw [fitsEnv_doReserveStride_iff]
    by_cases hc : x.cap = 0#64
    · simpa only [doReserveStrideEvents, doReserveEvents, xs, hc, BitVec.toNat_zero,
        BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, ↓reduceIte] using hfits
    · have hc_nat : x.cap.toNat ≠ 0 :=
        Nat.ne_of_gt (Nat.pos_of_ne_zero (fun h0 => hc (BitVec.eq_of_toNat_eq h0)))
      simpa only [doReserveStrideEvents, doReserveEvents, xs, hc, hc_nat,
        BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, ↓reduceIte] using hfits
  have hpre' : s0.mem ⊨ (doReserveStrideRawSpecWithStack M A lim hookStack).pre (xs, st) s0 ∗ R := by
    simp only [doReserveStrideRawSpecWithStack, xs, BitVec.toNat_ofNat, Nat.one_mod,
      reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hrlay, hfits'⟩, hmem⟩
  refine hs.mono_outcome (xs, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hevs : doReserveStrideEvents xs = doReserveEvents x := by
      by_cases hc : x.cap = 0#64
      · simp [doReserveStrideEvents, doReserveEvents, xs, hc, reserveCapStride_one]
      · simp [doReserveStrideEvents, doReserveEvents, xs, hc, reserveCapStride_one]
    simpa only [doReserveStrideRawSpecWithStack, doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      xs, hevs, BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, Nat.mod_one,
      and_true] using hq
  · exact Or.inr hfail

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  sep_ac_rfl

private theorem do_reserve_vec_of_raw {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hraw : subroutine_ok P addr (doReserveRawSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (doReserveSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm, sepConj_assoc, satisfies_pure_sepConj]
    at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfits⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (doReserveRawSpecWithStack M A lim hookStack).pre (x, st) s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfits⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine hraw.mono_outcome (x, st) (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R)
    s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63 at hbound
    simp only [doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.reserveCap,
      vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem_f⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem_f
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem stackAt_doReserve_eq_32 (sp : BitVec 64) {hookStack : Nat}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 48) + 64) =
      stackAt sp ((hookStack + 32) + 64) ∗
        memRegion (sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16 := by
  have hsplit := ProofLib.stackAt_split_bottom sp ((hookStack + 32) + 64) 16
    (by omega : ((hookStack + 32) + 64) + 16 ≤ 2 ^ 64)
  rw [sepConj_comm]
  simpa only [show ((hookStack + 32) + 64) + 16 = (hookStack + 48) + 64 by omega] using hsplit

private theorem do_reserve_raw1_of_raw32 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64)
    (h32 : subroutine_ok P addr (doReserve1Raw32SpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (doReserve1RawSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserve1RawSpecWithStack, stackAt_doReserve_eq_32 _ hhook, sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16
  have hpre' : s0.mem ⊨
      (doReserve1Raw32SpecWithStack M A lim hookStack).pre (x, st) s0 ∗ (btm ∗ R) := by
    simp only [doReserve1Raw32SpecWithStack, btm, sepConj_assoc]
    exact hpre
  refine h32.mono_outcome (x, st) (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [doReserve1Raw32SpecWithStack, doReserve1RawSpecWithStack,
      stackAt_doReserve_eq_32 _ hhook, btm, sepConj_assoc] using hq
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem do_reserve_raw_of_raw1 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h1 : subroutine_ok P addr (doReserve1RawSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (doReserveRawSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveRawSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, _, _, hlen, hptr, hbound, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨ (doReserve1RawSpecWithStack M A lim hookStack).pre (x, st) s0 ∗ R := by
    simp only [doReserve1RawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound, hfits⟩, hmem⟩
  exact h1.mono_outcome (x, st) R s0 hpc hrun hpre' hsp fun _ hout => hout

private theorem doReserveSpecX_of_doReserveSpec_budget {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (h4k : subroutine_ok P addr (doReserveSpec M A lim)) :
    subroutine_ok P addr (doReserveSpecX M A lim) := by
  have hstk : ∀ sp : BitVec 64,
      stackAt sp ((extHookStack + 48) + 64) =
        stackAt sp ((allocHookStack + 48) + 64) ∗
          memRegion (sp - BitVec.ofNat 64 ((extHookStack + 48) + 64))
            (((extHookStack + 48) + 64) - ((allocHookStack + 48) + 64)) := by
    intro sp
    have hsplit := ProofLib.stackAt_split_bottom sp ((allocHookStack + 48) + 64)
      (((extHookStack + 48) + 64) - ((allocHookStack + 48) + 64)) (by decide)
    rw [sepConj_comm]
    simpa only [show ((allocHookStack + 48) + 64) +
        (((extHookStack + 48) + 64) - ((allocHookStack + 48) + 64)) =
      (extHookStack + 48) + 64 by decide] using hsplit
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [doReserveSpecX,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecX,
    doReserveSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    doReserveStackX, finishGrowStackX] at hpre
  rw [hstk s0.sp] at hpre
  simp only [sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - BitVec.ofNat 64 ((extHookStack + 48) + 64))
    (((extHookStack + 48) + 64) - ((allocHookStack + 48) + 64))
  have hpre' : s0.mem ⊨ (doReserveSpec M A lim).pre (x, st) s0 ∗ (btm ∗ R) := by
    dsimp only [doReserveSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
      doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      doReserveStack, finishGrowStack, btm]
    simpa only [sepConj_assoc] using hpre
  refine h4k.mono_outcome (x, st) (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [doReserveSpec, doReserveSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecX,
      doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      doReserveStack, doReserveStackX, finishGrowStack, finishGrowStackX, btm] at hq ⊢
    rw [hstk s0.sp]
    simpa only [sepConj_assoc] using hq
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

end LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget

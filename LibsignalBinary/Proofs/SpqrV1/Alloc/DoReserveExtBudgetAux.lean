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
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches

/-!
# Budget-Threaded `AllocContracts4K` Contracts for `finish_grow` (`[local#2, 4, 8]`)

Proves `finish_grow_{8,2,4}_ok_ext_4k` on `tripleRatchetProgAtExt b ext` under
`Hooks4KBudget.AllocContracts4K b A lim ext` (`allocHookStack = 4096`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (
  finishGrow2Name finishGrow4Name finishGrow8Name
)
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustReallocEvents
  subroutine_ok_allocNoOom_of_budgetBase subroutine_ok_reallocNoOom_of_budgetBase
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStackBase rustCliReallocNoOomExternSpecWithStackBase
  subroutine_ok_rustCliAllocNoOom_externWithStackBase
  subroutine_ok_rustCliReallocNoOom_externWithStackBase
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  FinishGrowEnv finishGrowEvents finishGrowSpec finishGrowSpecWithStack
  fitsEnv_finishGrow_iff noAllocShimSpec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (
  FinishGrow1Env
  finishGrow1AllocSpecG finishGrow1Events finishGrow1ReallocSpecG
  finishGrow1Spec finishGrow1SpecWithStack
  finishGrow8AllocSpecG finishGrow8ReallocSpecG
  fitsEnv_finishGrow1_iff memRegion_24 session2ShimSpecWithStack
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem fetch_withSvc (P : Program) (svc : State → State) (a : BitVec 64) :
    P.fetch a = (P.withSvc svc).fetch a := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Arithmetic and Stack Helpers -/

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) =
      0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hs : stride.toNat < 2 ^ 128 := lt_trans stride.isLt (by decide)
  have hn : new.toNat < 2 ^ 128 := lt_trans new.isLt (by decide)
  rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hn]
  have hprod : stride.toNat * new.toNat < 2 ^ 64 := by rw [Nat.mul_comm]; exact h
  rw [Nat.mod_eq_of_lt (lt_trans hprod (by decide)), Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt hprod]
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

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (hlt : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat hlt] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hlt : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hal : align.toNat ≤ 2 ^ 63 := by omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, not_lt]
  rw [mul_stride_toNat hlt, BitVec.toNat_sub_of_le]
  · change new.toNat * stride.toNat ≤ 2 ^ 63 - align.toNat
    omega
  · rw [BitVec.le_def]
    exact hal

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht
  omega

private theorem stackAt_finishGrow_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hhook

private theorem stackAt_finishGrow32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 32) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp hookStack 4 hhook

theorem sepWP_seg_rebase_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) target_pc sm Pm post oom))) :
    SepWP (P.rebase b Hk) target_pc s Pre post oom := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hPm, hvm, hcont⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc (sepWP_rebase_vmPreserved hwp) hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc (hcont hvm) hPm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem sepWPp_seg_rebase_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → SepWPp (P.rebase b Hk) ret sm Pm Q Qp oom))) :
    SepWPp (P.rebase b Hk) ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hPm, hvm, hcont⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc (sepWP_rebase_vmPreserved hwp) hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ := hcont hvm R hPm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

macro "wp_steps_rebase_pool " mid:term : tactic => `(tactic| (
  first
    | apply LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux.sepWP_seg_rebase_vm (mid := $mid)
    | apply LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux.sepWPp_seg_rebase_vm (mid := $mid)
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    ⟨by simp only [wp_norm, arm64_norm], fun _hvm_seg => ?_⟩
  first
    | refine ProofLib.SepWP.transport_budgetPool _hvm_seg (hnext := ?_)
    | refine ProofLib.SepWPp.transport_budgetPool _hvm_seg (hnext := ?_)
  try simp only [Arm64.State.setMem_setMem]
))

/-! ## `AllocContracts4K` Hook Adapters -/

private theorem finish_grow_1_of_zero_ne {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hz : subroutine_ok P addr (finishGrow1AllocSpecG M A lim hookStack))
    (hne : subroutine_ok P addr (finishGrow1ReallocSpecG M A lim hookStack)) :
    subroutine_ok P addr (finishGrow1SpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1AllocSpecG,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf, hcap0, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay, hfits⟩, hmem⟩
  · refine hne.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1ReallocSpecG,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf, hcap0, ite_false, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay, hfits⟩, hmem⟩

end LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux

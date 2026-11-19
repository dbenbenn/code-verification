/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import ProofLib.SepLogic.WP.StateNorm

/-!
# Budget-Threaded 4 KiB Stack Allocator and Memory Contract Bundle

Provides `VmPreserved`-strengthened `sessionMemcpyROSpec4K` and the budget-threaded
`AllocContracts4K` bundle (`allocHookStack = 4096`) on `tripleRatchetProgAtExt b ext`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget

open CryptoVerification.LibsignalTripleRatchet (withStack)

open Arm64 ProofLib
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpecBase
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Read-only `memcpy(dst, src, len)` region contract (`src ↦ᵣ bs`) with trace and VM preservation. -/
@[expose] def sessionMemcpyROSpec4K : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K

theorem hookMemcpy_sessionMemcpyROSpec4K_ok : HookOk hookMemcpy sessionMemcpyROSpec4K := by
  intro x R s0 hrun hpre hsp
  rcases CryptoVerification.SpqrV1.Alloc.hookMemcpy_sessionMemcpyROSpec4K_ok x R s0 hrun hpre hsp
    with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemcpyROSpec4K, withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨?_, hpost⟩
    dsimp only [hookMemcpy, retHook]
    simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]
  · exact Or.inr hrest

theorem libcMemcpyRO_of_sessionMemcpyRO4K {prog : Program} {addr : BitVec 64} {stk : Nat}
    (h : subroutine_ok prog addr (withStack sessionMemcpyROSpec4K stk)) :
    subroutine_ok prog addr (withVmPreserved (libcMemcpyROSpec stk)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  refine ⟨(dst, src, bs), R, ?_, ?_⟩
  · dsimp only [withVmPreserved, libcMemcpyROSpec, withStack, sessionMemcpyROSpec4K,
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    have hle : bs.length ≤ 2 ^ 64 := by rw [← hx2]; exact Nat.le_of_lt (s0.readReg64 .x2).isLt
    exact ⟨⟨hx0, hx1, hx2, hle⟩, hm⟩
  · intro sf hpost
    dsimp only [withVmPreserved, libcMemcpyROSpec, withStack, sessionMemcpyROSpec4K,
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1.1, hpost.2.2⟩

namespace AllocContracts4K

variable {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
  {ext : String → Option (State → State)}

end AllocContracts4K

end LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget

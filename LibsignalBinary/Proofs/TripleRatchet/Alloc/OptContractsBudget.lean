/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.InImageLift -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
public meta import Lean.Elab.Tactic -- shake: keep
public meta import Lean
public meta import ProofLib.SepLogic.WP

/-!
# Stack- and Optional-Image-Parameterized Budget Allocator Contracts

Provides `VmPreserved`-strengthened `shimSpecWithStack` and `memcpySpecWithStack`, re-exports the
`*SpecWithStack` allocator contracts from `Alloc.DefsBudget` and `Heap.IfaceBudgetLemmas`, supplies
hook adapters for `AllocContractsBudget{,X}` and placed `HookSat` assumptions, and defines
`sepWP_optImage_rebase_vm` / `wp_steps_opt_sync_pool` for synchronizing `A.pool lim st` across
fixed-base `SepWP` instruction segments.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget

open CryptoVerification.LibsignalTripleRatchet (subroutine_ok_withStack_of_subroutine_ok withStack)

open CryptoVerification (LibsignalPlacement)

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits NullAllowed RustCliAllocBudget VmPreserved
  not_nullAllowed_of_fitsAllocEvents not_nullAllowed_of_fitsReallocEvents
  rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetExternSpecWithStack rustCliAllocBudgetSpecWithStack
  rustCliAllocNoOomExternSpecWithStack rustCliAllocNoOomSpecWithStack
  rustCliDeallocBudgetExternSpecWithStack rustCliDeallocBudgetSpecWithStack
  rustCliDeallocNoOomExternSpecWithStack rustCliDeallocNoOomSpecWithStack
  rustCliReallocBudgetExternSpecWithStack rustCliReallocBudgetSpecWithStack
  rustCliReallocNoOomExternSpecWithStack rustCliReallocNoOomSpecWithStack
  subroutine_ok_rustCliAllocBudget_externWithStack subroutine_ok_rustCliAllocBudget_withStack
  subroutine_ok_rustCliAllocNoOom_externWithStack subroutine_ok_rustCliAllocNoOom_withStack
  subroutine_ok_rustCliDeallocBudget_externWithStack
  subroutine_ok_rustCliReallocBudget_externWithStack
  subroutine_ok_rustCliReallocNoOom_externWithStack subroutine_ok_rustCliReallocNoOom_withStack

  rustCliAllocBudgetExternSpecWithStackBase rustCliAllocBudgetSpecWithStackBase
  rustCliAllocNoOomExternSpecWithStackBase rustCliAllocNoOomSpecWithStackBase
  rustCliDeallocBudgetExternSpecWithStackBase rustCliDeallocBudgetSpecWithStackBase
  rustCliDeallocNoOomExternSpecWithStackBase rustCliDeallocNoOomSpecWithStackBase
  rustCliReallocBudgetExternSpecWithStackBase rustCliReallocBudgetSpecWithStackBase
  rustCliReallocNoOomExternSpecWithStackBase rustCliReallocNoOomSpecWithStackBase
  subroutine_ok_rustCliAllocBudget_externWithStackBase subroutine_ok_rustCliAllocBudget_withStackBase
  subroutine_ok_rustCliAllocNoOom_externWithStackBase subroutine_ok_rustCliAllocNoOom_withStackBase
  subroutine_ok_rustCliDeallocBudget_externWithStackBase
  subroutine_ok_rustCliReallocBudget_externWithStackBase
  subroutine_ok_rustCliReallocNoOom_externWithStackBase subroutine_ok_rustCliReallocNoOom_withStackBase
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  sepWP_rebase_vmPreserved trapHooks
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec
)

/-! ## 1. `VmPreserved` Shim & `memcpy` Stack Contracts & Spec Re-Exports -/

/-- Stack-equipped `VmPreserved` no-op shim spec at `hookStack`
(`= session2ShimBudgetSpecX` at `extHookStack` by `rfl`). -/
@[expose] def shimSpecWithStack (hookStack : Nat) : Spec Unit where
  pre := fun _ s => stackAt s.sp hookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp hookStack

abbrev shimBudgetSpecWithStack := shimSpecWithStack

/-- Stack-equipped `VmPreserved` `memcpy` spec at `hookStack`
(`= session2MemcpyBudgetSpecX` at `extHookStack` by `rfl`). -/
@[expose] def memcpySpecWithStack (hookStack : Nat) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ (dst ↦ₛ bs) ∗
      (src ↦ₛ bs) ∗ stackAt s0.sp hookStack

abbrev memcpyBudgetSpecWithStack := memcpySpecWithStack

abbrev finishGrowSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack
abbrev finishGrowBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowBudgetSpecWithStack
abbrev doReserveRawSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack
abbrev doReserveRawBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawBudgetSpecWithStack
abbrev doReserveSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack
abbrev doReserveBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveBudgetSpecWithStack
abbrev intoBoxedSliceSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.intoBoxedSliceSpecWithStack
abbrev intoBoxedSliceBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.intoBoxedSliceBudgetSpecWithStack
abbrev tryCloneFromRefSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefSpecWithStack
abbrev tryCloneFromRefBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefBudgetSpecWithStack
abbrev chainKeyToPbSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.chainKeyToPbSpecWithStack
abbrev chainKeyToPbBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.chainKeyToPbBudgetSpecWithStack
abbrev publicKeySerializeSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeSpecWithStack
abbrev publicKeySerializeBudgetSpecWithStack :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeBudgetSpecWithStack

abbrev rustAllocSpecWithStack [inst : LibsignalPlacement] := @rustCliAllocBudgetSpecWithStack inst
abbrev rustAllocExternSpecWithStack [inst : LibsignalPlacement] := @rustCliAllocBudgetExternSpecWithStack inst
abbrev rustDeallocSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocBudgetSpecWithStack inst
abbrev rustDeallocExternSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocBudgetExternSpecWithStack inst
abbrev rustReallocSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocBudgetSpecWithStack inst
abbrev rustReallocExternSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocBudgetExternSpecWithStack inst

abbrev rustAllocNoOomSpecWithStack [inst : LibsignalPlacement] := @rustCliAllocNoOomSpecWithStack inst
abbrev rustAllocNoOomExternSpecWithStack [inst : LibsignalPlacement] := @rustCliAllocNoOomExternSpecWithStack inst
abbrev rustDeallocNoOomSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocNoOomSpecWithStack inst
abbrev rustDeallocNoOomExternSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocNoOomExternSpecWithStack inst
abbrev rustReallocNoOomSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocNoOomSpecWithStack inst
abbrev rustReallocNoOomExternSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocNoOomExternSpecWithStack inst

abbrev rustDeallocExternSpecWithStackBase := @rustCliDeallocBudgetExternSpecWithStackBase
abbrev rustAllocNoOomExternSpecWithStackBase := @rustCliAllocNoOomExternSpecWithStackBase
abbrev rustReallocNoOomExternSpecWithStackBase := @rustCliReallocNoOomExternSpecWithStackBase

/-! ## 2. Placed `noAllocShim` / `framelessMemcpy` Stack Adapters -/

theorem shimWithStack_of_noAllocShim {P : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok P addr noAllocShimBudgetSpec) :
    subroutine_ok P addr (shimSpecWithStack hookStack) := by
  have hw := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_mono hw (fun _ R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withStack, noAllocShimBudgetSpec, shimSpecWithStack] at hpre ⊢
  simpa only [emp_sepConj, sepConj_assoc] using hpre

theorem shimWithStack_of_hookSat {hooks : String → Option (State → State)} {hname : String}
    {prog : Program} {entry : BitVec 64} (hookStack : Nat)
    (hsat : HookSat hooks hname noAllocShimBudgetSpec)
    (hext : prog.externAt? entry = hooks hname) :
    subroutine_ok prog entry (shimSpecWithStack hookStack) := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact shimWithStack_of_noAllocShim hookStack (subroutine_ok_of_hookOk (hext.trans hf) hok)

theorem memcpyWithStack_of_framelessMemcpy {P : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok P addr framelessMemcpyBudgetSpec) :
    subroutine_ok P addr (memcpySpecWithStack hookStack) := by
  have hw := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_mono hw (fun _ R s0 hpre => ?_) (fun _ R s0 sf hpost => ?_)
  · dsimp only [withStack, framelessMemcpyBudgetSpec, memcpySpecWithStack] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  · dsimp only [withStack, framelessMemcpyBudgetSpec, memcpySpecWithStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

theorem memcpyWithStack_of_hookSat {hooks : String → Option (State → State)} {hname : String}
    {prog : Program} {entry : BitVec 64} (hookStack : Nat)
    (hsat : HookSat hooks hname framelessMemcpyBudgetSpec)
    (hext : prog.externAt? entry = hooks hname) :
    subroutine_ok prog entry (memcpySpecWithStack hookStack) := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact memcpyWithStack_of_framelessMemcpy hookStack (subroutine_ok_of_hookOk (hext.trans hf) hok)

/-! ## 3. `.inImage` `Budget → NoOom` Lifts for `AllocContractsXBudget` -/

/-- `(P.rebase b trapHooks).fnAddr name` agrees with `(P.rebase b Hk).fnAddr name` without
requiring callers with `local irreducible Program.fetch` to unfold `fnOff`. -/
theorem rebase_trapHooks_fnAddr (P : Program) (b : BitVec 64)
    (Hk : String → Option (State → State)) (name : String) :
    (P.rebase b trapHooks).fnAddr name = (P.rebase b Hk).fnAddr name :=
  rfl

end LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget

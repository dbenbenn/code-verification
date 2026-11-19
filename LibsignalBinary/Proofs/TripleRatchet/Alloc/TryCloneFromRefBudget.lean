/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRef
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.CodeLayout
public import ProofLib.SepLogic.WPp
public import Arm64.Trusted.Object.Labels
public import ProofLib.BV
public import ProofLib.BV.MaskLemmas
public import ProofLib.BV.PolyMul
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.Hoare.SubroutineHook
public import ProofLib.MallocngBridge
public import ProofLib.Placed
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.SharedCode
public import ProofLib.Process.FsLemmas
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.Strlen
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Spec.Cost
public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Musl.Spec.Top
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Spec.AllocFormatInner
public import VerifiedLibraries.RustStd.Spec.AllocFormatInnerBudget
public import VerifiedLibraries.RustStd.Spec.AllocStringClone
public import VerifiedLibraries.RustStd.Spec.CoreFmtDisplay
public import VerifiedLibraries.RustStd.Spec.CoreFmtWrite
public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import VerifiedLibraries.RustStd.Spec.CoreMemrchr
public import VerifiedLibraries.RustStd.Spec.FsRead
public import VerifiedLibraries.RustStd.Spec.FsWrite
public import VerifiedLibraries.RustStd.Spec.Stdio
public import VerifiedLibraries.RustStd.Spec.TimeAdd
public import VerifiedLibraries.RustStd.Spec.TimeDurationSince
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded Contract for `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (Block `23`)

Verifies `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` against
`tryCloneFromRefSpec M A lim` on `tripleRatchetProgAt{,Ext}` and under `[LibsignalPlacement]`
(Block `23`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRefBudget

open CryptoVerification.LibsignalTripleRatchet (boxU8Buf extHookStack)

open CryptoVerification (
  LibsignalPlacement blkPC_23 blkPl_23 lsMemcpySym lsRustAllocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem lsρ
)

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk VmPreserved
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (subroutine_ok_rustCliAllocNoOom_externWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  fitsEnv_tryCloneFromRef_iff
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec tryCloneFromRefEvents
  tryCloneFromRefSpec tryCloneFromRefSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (
  memcpySpecWithStack
  memcpyWithStack_of_framelessMemcpy
  rustAllocNoOomExternSpecWithStack
  shimSpecWithStack shimWithStack_of_noAllocShim
  tryCloneFromRefSpecWithStack
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_tryCloneFromRef_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp hookStack 6 hstack

private theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

private theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

section FixedBaseSteps

attribute [local irreducible] Program.fnOff

end FixedBaseSteps

theorem try_clone_from_ref_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_23).rebase (blkPl_23).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_23).rebase (blkPl_23).base H)
      (lsρ lsRustAllocSym) (rustAllocNoOomExternSpecWithStack M A lim false hookStack))
    (hmemcpy : subroutine_ok ((blkPC_23).rebase (blkPl_23).base H)
      (lsρ lsMemcpySym) (memcpySpecWithStack hookStack)) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpecWithStack M A lim hookStack) := by
  unfold tryCloneFromRefSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefSpecWithStack
  simp only [fitsEnv_tryCloneFromRef_iff, tryCloneFromRefEvents,
    boxU8Buf, stackAt_tryCloneFromRef_opt hstack]
  cells_unfold
  dsimp only [shimSpecWithStack] at hshim
  dsimp only [memcpySpecWithStack] at hmemcpy
  dsimp only [rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    RustLayoutOk, LayoutOk, ↓reduceIte] at halloc
  wp_init g s0
  rcases g with ⟨⟨src, bs⟩, st⟩
  dsimp only at *
  have hx1_eq : (s0.readReg64 Reg.x1).toNat = bs.length := by assumption
  have hx1_bv : s0.readReg64 Reg.x1 = BitVec.ofNat 64 bs.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hbs : bs = []
  · subst hbs
    simp only [List.length_nil, ite_true, sepConj_emp] at hx1_bv ⊢
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_lt63 : bs.length < 2 ^ 63 := by omega
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpos (by omega)
    have hlen_beq0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
    have hbound : bs.length + 1 ≤ 2 ^ 63 := by omega
    have hlay : LayoutOk bs.length 1 := ⟨hpos, hpow2, hbound⟩
    simp only [hbs, ite_false] at *
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs.length, 1, st)
    have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
    have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
    wp_steps_sync_pool (lsρ lsMemcpySym)
    simp only [State.setMem_setMem]
    wp_call hmemcpy (sf_1.readReg64 Reg.x0, src, bs)
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

/-- Relocatable `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (Block `23`) meets
`tryCloneFromRefSpec M A lim`. -/
theorem try_clone_from_ref_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpec M A lim) :=
  try_clone_from_ref_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))
    (memcpyWithStack_of_framelessMemcpy allocHookStack (ls_hook_ok_of_mem hmemcpy))

theorem try_clone_from_ref_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpecX M A lim) :=
  try_clone_from_ref_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))
    (memcpyWithStack_of_framelessMemcpy extHookStack (ls_hook_ok_of_mem hmemcpy))

theorem try_clone_from_ref_placed_ok_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpec M A lim) :=
  try_clone_from_ref_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem halloc))
    (memcpyWithStack_of_framelessMemcpy allocHookStack (ls_hook_ok_of_mem hmemcpy))

theorem try_clone_from_ref_placed_ok_x_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpecX M A lim) :=
  try_clone_from_ref_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem halloc))
    (memcpyWithStack_of_framelessMemcpy extHookStack (ls_hook_ok_of_mem hmemcpy))

end LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRefBudget

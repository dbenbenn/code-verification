/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
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

/-!
# Budget-Threaded Contract for `<libsignal_core::curve::PublicKey>::serialize` (Block `205`)

Verifies `<libsignal_core::curve::PublicKey>::serialize` against `publicKeySerializeSpec M A lim`
on `tripleRatchetProgAt{,Ext}` and under `[LibsignalPlacement]` (Block `205`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget

open CryptoVerification.LibsignalTripleRatchet (boxU8Buf extHookStack)

open CryptoVerification (
  LibsignalPlacement blkPC_205 blkPl_205 lsRustAllocSym lsRustNoAllocShimSym ls_hook_ok_of_mem lsρ
)

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey djbType)
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (subroutine_ok_rustCliAllocNoOom_externWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  fitsEnv_publicKeySerialize_iff noAllocShimBudgetSpec
  publicKeySerializeEvents publicKeySerializeSpec publicKeySerializeSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (
  publicKeySerializeSpecWithStack rustAllocNoOomExternSpecWithStack
  shimSpecWithStack shimWithStack_of_noAllocShim
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_publicKeySerialize_opt {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 32) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  stackAt_split_cells sp hookStack 4 hstack

private theorem memRegion_33_cells (a : BitVec 64) :
    memRegion a 33 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ b0 : BitVec 8,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ u3) ∗ ((a + 9#64) ↦₆₄ u2) ∗
        ((a + 17#64) ↦₆₄ u1) ∗ ((a + 25#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 1 32 (by decide),
    memRegion_split (a + 1#64) 8 24 (by decide),
    memRegion_split (a + 1#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64) 8 8 (by decide),
    memRegion_one, memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

section FixedBaseSteps

attribute [local irreducible] Program.fnOff

end FixedBaseSteps

theorem public_key_serialize_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustAllocSym) (rustAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (publicKeySerializeSpecWithStack M A lim hookStack) := by
  unfold publicKeySerializeSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeSpecWithStack
  simp only [fitsEnv_publicKeySerialize_iff, publicKeySerializeEvents, PublicKey.serialize,
    boxU8Buf, stackAt_publicKeySerialize_opt hstack]
  cells_unfold
  dsimp only [shimSpecWithStack] at hshim
  dsimp only [rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    RustLayoutOk, LayoutOk, ↓reduceIte] at halloc
  wp_init g s0
  rcases g with ⟨⟨self, pk⟩, st⟩
  dsimp only at *
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length pk.bytes)
  rw [hpk_cells self]
  have hfe_raw : FitsEvents M lim st [.alloc 33] := by
    simpa [rustAllocEvents] using ‹FitsEvents M lim st (rustAllocEvents 33 1)›
  rcases hfe_raw with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos : 0 < (33 : Nat) := by decide
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (33, 1, st)
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  simp only [memRegion_33_cells, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 =>
    SepWP.exists_elim fun b0 => ?_
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem, List.length_cons, List.Vector.toList_length,
    List.cons_ne_nil, ite_false, djbType,
    pointsToBytes_cons, hpk_cells,
    BitVec.add_assoc, BitVec.reduceAdd]
  wp_done

/-- Relocatable `<libsignal_core::curve::PublicKey>::serialize` (Block `205`) meets
`publicKeySerializeSpec M A lim`. -/
theorem public_key_serialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (publicKeySerializeSpec M A lim) :=
  public_key_serialize_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

theorem public_key_serialize_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (publicKeySerializeSpecX M A lim) :=
  public_key_serialize_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

theorem public_key_serialize_placed_ok_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (publicKeySerializeSpec M A lim) :=
  public_key_serialize_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem halloc))

theorem public_key_serialize_placed_ok_x_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (publicKeySerializeSpecX M A lim) :=
  public_key_serialize_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (ls_hook_ok_of_mem halloc))

end LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget

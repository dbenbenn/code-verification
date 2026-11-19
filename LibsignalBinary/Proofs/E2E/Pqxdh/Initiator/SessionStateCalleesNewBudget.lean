/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudgetBase
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPFrozen
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.CodeLayout

/-!
# Budget-Threaded Relocatable Contract for `<SessionState>::new` (Block `37`)
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  lsRustAllocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem ls_subroutine_ok_cl_of_plain
  lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open CryptoVerification.E2E.Pqxdh.Initiator (
  SessionStateNewGhost blkLib_eq_37 blkPC_37 blkPl_37
  bv_sub_add_lit' bytesToBv8 encodeEC
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre stackAt_split_top
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEvent FitsEvents RustCliAllocBudget VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomExternSpecWithStack
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  subroutine_ok_rustCliAllocNoOom_externWithStack
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff FitsEvent
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local simp, local wp_norm, local arm64_norm] bytesToBv8_length

local macro "wp_clean_setMem" : tactic =>
  `(tactic| (
    try (conv => arg 3; simp only [State.setMem_setMem])
    try (conv => arg 4; simp only [State.setMem_setMem])))

private theorem stackAt_sessionStateNew_entry (sp : BitVec 64) :
    memRegion (sp - 4224#64) 128 ∗ stackAt sp allocHookStack =
      (memRegion (sp - 96#64 - 4128#64) 32 ∗ stackAt (sp - 96#64) allocHookStack) ∗
      cells (sp - 96#64) 12 := by
  have h1 := stackAt_split_top sp 128 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (32 + allocHookStack) 12 (by decide)
  have h3 := stackAt_split_top (sp - 96#64) 32 allocHookStack (by decide)
  have h4 : (128 + allocHookStack : Nat) = (32 + allocHookStack) + 8 * 12 := by decide
  have h5 : BitVec.ofNat 64 (128 + allocHookStack) = 4224#64 := rfl
  have h6 : BitVec.ofNat 64 (8 * 12) = 96#64 := rfl
  have h7 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  rw [h5] at h1
  rw [h6] at h2
  rw [h7] at h3
  rw [← h1, h4, h2, ← h3]

private theorem memRegion_344_sessionStateNew_split (outPtr : BitVec 64) :
    memRegion outPtr 344 =
      cells outPtr 19 ∗ memRegion (outPtr + 0x98#64) 96 ∗
      (∃∗ u_f8 : BitVec 64, (outPtr + 0xf8#64) ↦₆₄ u_f8) ∗
      memRegion (outPtr + 0x100#64) 40 ∗
      (∃∗ u_128 : BitVec 64, (outPtr + 0x128#64) ↦₆₄ u_128) ∗
      memRegion (outPtr + 0x130#64) 24 ∗
      (∃∗ u_148 : BitVec 32, (outPtr + 0x148#64) ↦₃₂ u_148) ∗
      (∃∗ u_14c : BitVec 64, (outPtr + 0x14c#64) ↦₆₄ u_14c) ∗
      (∃∗ u_154 : BitVec 32, (outPtr + 0x154#64) ↦₃₂ u_154) := by
  rw [memRegion_split outPtr 152 192 (by decide), memRegion_cells outPtr 19 (by decide),
    memRegion_split (outPtr + 152#64) 96 96 (by decide),
    memRegion_split (outPtr + 152#64 + 96#64) 8 88 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64) 8 40 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64 + 8#64 + 40#64),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 16 (by decide),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64) 4 12 (by decide),
    memRegion_four (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64) 8 4 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64),
    memRegion_four (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

@[expose] def sessionStateNewEvents : List AllocEvent :=
  rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 32 1 ++ rustAllocEvents 33 1

@[expose] def SessionStateNewEnv (evs : List AllocEvent) : Prop :=
  evs = sessionStateNewEvents

@[expose] def sessionStateNewPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SessionStateNewGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg32 .x0 = g.version ∧ s.readReg64 .x1 = g.localIkPtr ∧
      s.readReg64 .x2 = g.remoteIkPtr ∧ s.readReg64 .x3 = g.rootKeyPtr ∧
      s.readReg64 .x4 = g.baseKeyPtr ∧ s.readReg64 .x5 = g.spqrVecPtr ∧
      g.localIk32.length = 32 ∧ g.remoteIk32.length = 32 ∧
      g.rootKey32.length = 32 ∧ g.baseKey32.length = 32 ∧
      FitsEvents M lim st sessionStateNewEvents⌝ ∗
      (g.localIkPtr ↦ₛ bytesToBv8 g.localIk32) ∗ (g.remoteIkPtr ↦ₛ bytesToBv8 g.remoteIk32) ∗
      (g.rootKeyPtr ↦ₛ bytesToBv8 g.rootKey32) ∗ (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKey32) ∗
      (g.spqrVecPtr ↦₆₄ g.spqrCap) ∗ ((g.spqrVecPtr + 0x08#64) ↦₆₄ g.spqrBufPtr) ∗
      ((g.spqrVecPtr + 0x10#64) ↦₆₄ g.spqrLen) ∗ memRegion g.outPtr 344 ∗
      (memRegion (s.sp - 4224#64) 128 ∗ stackAt s.sp allocHookStack) ∗ A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ localIkBoxPtr : BitVec 64, ∃∗ remoteIkBoxPtr : BitVec 64,
    ∃∗ rootKeyBoxPtr : BitVec 64, ∃∗ baseKeyBoxPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ localIkBoxPtr ≠ 0 ∧ remoteIkBoxPtr ≠ 0 ∧
        rootKeyBoxPtr ≠ 0 ∧ baseKeyBoxPtr ≠ 0⌝ ∗
      (g.localIkPtr ↦ₛ bytesToBv8 g.localIk32) ∗ (g.remoteIkPtr ↦ₛ bytesToBv8 g.remoteIk32) ∗
      (g.rootKeyPtr ↦ₛ bytesToBv8 g.rootKey32) ∗ (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKey32) ∗
      (g.spqrVecPtr ↦₆₄ g.spqrCap) ∗ ((g.spqrVecPtr + 0x08#64) ↦₆₄ g.spqrBufPtr) ∗
      ((g.spqrVecPtr + 0x10#64) ↦₆₄ g.spqrLen) ∗
      (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC g.localIk32)) ∗ A.live localIkBoxPtr 33 1 ∗
      (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC g.remoteIk32)) ∗ A.live remoteIkBoxPtr 33 1 ∗
      (rootKeyBoxPtr ↦ₛ bytesToBv8 g.rootKey32) ∗ A.live rootKeyBoxPtr 32 1 ∗
      (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC g.baseKey32)) ∗ A.live baseKeyBoxPtr 33 1 ∗
      (g.outPtr ↦₆₄ 33#64) ∗ ((g.outPtr + 0x08#64) ↦₆₄ localIkBoxPtr) ∗
      ((g.outPtr + 0x10#64) ↦₆₄ 33#64) ∗ ((g.outPtr + 0x18#64) ↦₆₄ 33#64) ∗
      ((g.outPtr + 0x20#64) ↦₆₄ remoteIkBoxPtr) ∗ ((g.outPtr + 0x28#64) ↦₆₄ 33#64) ∗
      ((g.outPtr + 0x30#64) ↦₆₄ 32#64) ∗ ((g.outPtr + 0x38#64) ↦₆₄ rootKeyBoxPtr) ∗
      ((g.outPtr + 0x40#64) ↦₆₄ 32#64) ∗ ((g.outPtr + 0x48#64) ↦₆₄ 0#64) ∗
      ((g.outPtr + 0x50#64) ↦₆₄ 8#64) ∗ ((g.outPtr + 0x58#64) ↦₆₄ 0#64) ∗
      ((g.outPtr + 0x60#64) ↦₆₄ 33#64) ∗ ((g.outPtr + 0x68#64) ↦₆₄ baseKeyBoxPtr) ∗
      ((g.outPtr + 0x70#64) ↦₆₄ 33#64) ∗ ((g.outPtr + 0x78#64) ↦₆₄ g.spqrCap) ∗
      ((g.outPtr + 0x80#64) ↦₆₄ g.spqrBufPtr) ∗ ((g.outPtr + 0x88#64) ↦₆₄ g.spqrLen) ∗
      ((g.outPtr + 0x90#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.outPtr + 0x98#64) 96 ∗
      ((g.outPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.outPtr + 0x100#64) 40 ∗
      ((g.outPtr + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.outPtr + 0x130#64) 24 ∗
      ((g.outPtr + 0x148#64) ↦₃₂ (BitVec.ofNat 32 (g.version.toNat % 256))) ∗
      ((g.outPtr + 0x14c#64) ↦₆₄ 0#64) ∗ ((g.outPtr + 0x154#64) ↦₃₂ 0#32) ∗
      (memRegion (s0.sp - 4224#64) 128 ∗ stackAt s0.sp allocHookStack) ∗
      A.pool lim (M.stepEvents sessionStateNewEvents st) sf

set_option maxHeartbeats 4000000 in
theorem sessionStateNew_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_37).rebase (blkPl_37).base H) (blkPl_37).base
      (withLsCodeLoaded lsmpl (sessionStateNewPlacedSpec M A lim)) := by
  unfold withLsCodeLoaded sessionStateNewPlacedSpec sessionStateNewEvents
  simp only [stackAt_sessionStateNew_entry, memRegion_344_sessionStateNew_split]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_37).rebase (blkPl_37).base H)
    (ecPubKeySerialize_alloc_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 205)
    (withLsCl lsmpl (ecPubKeySerializeAllocPlacedSpec M A lim)) at hser
  simp only [withLsCl, ecPubKeySerializeAllocPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hshim' : subroutine_ok ((blkPC_37).rebase (blkPl_37).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_37).rebase (blkPl_37).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_37).rebase (blkPl_37).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  wp_init x s0
  rcases x with ⟨⟨outPtr, version, localIkPtr, localIk32, remoteIkPtr, remoteIk32,
    rootKeyPtr, rootKey32, baseKeyPtr, baseKey32, spqrVecPtr, spqrCap, spqrBufPtr, spqrLen⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr version localIkPtr remoteIkPtr rootKeyPtr baseKeyPtr spqrVecPtr
  have hfe_all : FitsEvents M lim st [.alloc 33, .alloc 33, .alloc 32, .alloc 33] := by
    simpa [rustAllocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
        rustAllocEvents 32 1 ++ rustAllocEvents 33 1)›
  rcases hfe_all with ⟨hfe1, hfe2, hfe3, hfe4, -⟩
  let st1 := M.stepEvents (rustAllocEvents 33 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  let st3 := M.stepEvents (rustAllocEvents 32 1) st2
  have hlen_rk : (bytesToBv8 rootKey32).length = 32 := by
    simp [bytesToBv8, ‹rootKey32.length = 32›]
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ := exists_unpack64_of_length_32 hlen_rk
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  wp_clean_setMem
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 1#5), localIk32), st)
  have hcl2 : LibsignalCodeLoaded lsmpl sf.mem := by assumption
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  wp_clean_setMem
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  wp_call hser ((s0.readReg64 (.gpr 2#5), remoteIk32), st1)
  have hcl4 : LibsignalCodeLoaded lsmpl sf_1.mem := by assumption
  apply sepWP_seq_lscl hcl4 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_clean_setMem
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_clean_setMem
  wp_call halloc' (32, 1, st2)
  have hne_rk : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq_rk : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne_rk
  have hm32 : memRegion (sf_3.readReg64 (Reg.gpr 0#5)) 32 =
      cells (sf_3.readReg64 (Reg.gpr 0#5)) 4 :=
    memRegion_cells (sf_3.readReg64 (Reg.gpr 0#5)) 4 (by decide)
  conv => arg 4; simp only [hm32, cells, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  rw [hrk_cells (s0.readReg64 (.gpr 3#5))]
  wp_steps_sync_pool (lsmpl.base 205)
  wp_clean_setMem
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl5
  wp_call hser ((s0.readReg64 (.gpr 4#5), baseKey32), st3)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  wp_clean_setMem
  simp only [hrk_cells, sepConj_assoc]
  wp_done

theorem sessionStateNew_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_37).rebase (blkPl_37).base H) (blkPl_37).base
      (withLsCodeLoaded lsmpl (sessionStateNewPlacedSpec M A lim)) :=
  sessionStateNew_placed_ok_of_session (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudgetBase
meta import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudgetBase
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
# Budget-Threaded Relocatable Contract for `<SessionState>::with_receiver_chain` (Block `30`)
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain
  lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  WithReceiverChainGhost blkLib_eq_30 blkLib_eq_43 blkPC_30 blkPl_30
  bv_sub_add_lit' bytesToBv8 encodeEC
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  receiverChainElemAt receiverChainVecBytes24 receiverChainVecBytes24_length
  receiverChainVecFieldsAt sp_setMem_setPC_pre sp_setPC_pre stackAt_split_top
  withReceiverChain_pack344 withReceiverChain_pack344_unfolded
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEvent FitsEvents RustCliAllocBudget VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomExternSpecWithStack
  rustCliDeallocBudgetSpec rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  subroutine_ok_rustCliAllocNoOom_externWithStack
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  allocMemcpyVmSpec rustAllocShimVmSpec
)

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

private theorem stackAt_withReceiverChain_entry (sp : BitVec 64) :
    memRegion (sp - 4576#64) 480 ∗ stackAt sp allocHookStack =
      memRegion (sp - 368#64 - 4208#64) 80 ∗
        (memRegion (sp - 368#64 - 4128#64) 32 ∗ stackAt (sp - 368#64) allocHookStack) ∗
        memRegion (sp - 368#64) 272 ∗ cells (sp - 96#64) 12 := by
  have h1 := stackAt_split_top sp 480 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (112 + allocHookStack) 46 (by decide)
  have h3 := stackAt_split_top (sp - 368#64) 112 allocHookStack (by decide)
  have h4 := memRegion_split (sp - 368#64 - 4208#64) 80 32 (by decide)
  have h5 : (480 + allocHookStack : Nat) = (112 + allocHookStack) + 8 * 46 := by decide
  have h6 : BitVec.ofNat 64 (480 + allocHookStack) = 4576#64 := rfl
  have h7 : BitVec.ofNat 64 (8 * 46) = 368#64 := rfl
  have h8 : BitVec.ofNat 64 (112 + allocHookStack) = 4208#64 := rfl
  have h9 : sp - 368#64 - 4208#64 + BitVec.ofNat 64 80 = sp - 368#64 - 4128#64 := by bv_omega
  have hcells46 : cells (sp - 368#64) 46 = memRegion (sp - 368#64) 272 ∗ cells (sp - 96#64) 12 := by
    rw [← memRegion_cells (sp - 368#64) 46 (by decide),
      memRegion_split (sp - 368#64) 272 96 (by decide),
      show sp - 368#64 + BitVec.ofNat 64 272 = sp - 96#64 by bv_omega,
      memRegion_cells (sp - 96#64) 12 (by decide)]
  rw [h6] at h1; rw [h7] at h2; rw [h8] at h3; rw [h9] at h4
  rw [← h1, h5, h2, h3, h4, hcells46]
  simp only [sepConj_assoc]

private theorem memRegion_416_receiverChain_split (ptr : BitVec 64) :
    memRegion ptr 416 =
      cells ptr 12 ∗ (∃∗ v : BitVec 32, (ptr + 0x60#64) ↦₃₂ v) ∗ memRegion (ptr + 0x64#64) 316 := by
  have h1 := memRegion_split ptr 96 320 (by decide)
  have h2 := memRegion_split (ptr + BitVec.ofNat 64 96) 4 316 (by decide)
  have h3 : ptr + BitVec.ofNat 64 96 = ptr + 0x60#64 := by bv_omega
  have h4 : ptr + 0x60#64 + BitVec.ofNat 64 4 = ptr + 0x64#64 := by bv_omega
  rw [h1, memRegion_cells ptr 12 (by decide), h3]
  rw [h3, h4] at h2
  rw [h2, ProofLib.memRegion_four (ptr + 0x60#64)]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subs_0_0 : ConditionHolds CondCode.EQ (subsPState64 0#64 0#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_0_5 : ConditionHolds CondCode.LT (subsPState64 0#64 5#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem madd_zero_104 (ptr : BitVec 64) : ptr + 0#64 * 104#64 = ptr := by simp

@[expose] def withReceiverChainEmptyEvents : List AllocEvent :=
  rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
    rustDeallocEvents 33 1 ++ growOneChainZeroEvents

@[expose] def WithReceiverChainEmptyEnv (evs : List AllocEvent) : Prop :=
  evs = withReceiverChainEmptyEvents

@[expose] def withReceiverChainEmptyPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (WithReceiverChainGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.inPtr ∧
      s.readReg64 .x1 = g.senderRatchetPubPtr ∧ s.readReg64 .x2 = g.receiverChainKeyPtr ∧
      g.senderRatchetPub32.length = 32 ∧ g.receiverChainKey32.length = 32 ∧
      g.pre72.length = 72 ∧ g.post248.length = 248 ∧
      FitsEvents M lim st withReceiverChainEmptyEvents⌝ ∗
      (g.senderRatchetPubPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
      (g.receiverChainKeyPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗
      ((g.receiverChainKeyPtr + 32#64) ↦₃₂ g.receiverChainIdx) ∗
      (g.inPtr ↦ₛ g.pre72) ∗ ((g.inPtr + 0x48#64) ↦₆₄ 0#64) ∗
      ((g.inPtr + 0x50#64) ↦₆₄ g.oldVecPtr) ∗ ((g.inPtr + 0x58#64) ↦₆₄ 0#64) ∗
      ((g.inPtr + 0x60#64) ↦ₛ g.post248) ∗ memRegion g.outPtr 344 ∗
      (memRegion (s.sp - 4576#64) 480 ∗ stackAt s.sp allocHookStack) ∗ A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ receiverRatchetPubBoxPtr : BitVec 64, ∃∗ receiverChainKeyBoxPtr : BitVec 64,
    ∃∗ chainBufPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ receiverRatchetPubBoxPtr ≠ 0 ∧ receiverChainKeyBoxPtr ≠ 0 ∧
        chainBufPtr ≠ 0⌝ ∗
      (g.senderRatchetPubPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
      (g.receiverChainKeyPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗
      ((g.receiverChainKeyPtr + 32#64) ↦₃₂ g.receiverChainIdx) ∗
      (receiverRatchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC g.senderRatchetPub32)) ∗
      A.live receiverRatchetPubBoxPtr 33 1 ∗
      (receiverChainKeyBoxPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗
      A.live receiverChainKeyBoxPtr 32 1 ∗ A.live chainBufPtr 416 8 ∗
      receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
        g.receiverChainIdx ∗
      memRegion (chainBufPtr + 0x64#64) 316 ∗
      (g.outPtr ↦ₛ g.pre72) ∗ receiverChainVecFieldsAt g.outPtr chainBufPtr ∗
      ((g.outPtr + 0x60#64) ↦ₛ g.post248) ∗
      (g.inPtr ↦ₛ g.pre72) ∗ receiverChainVecFieldsAt g.inPtr chainBufPtr ∗
      ((g.inPtr + 0x60#64) ↦ₛ g.post248) ∗
      (memRegion (s0.sp - 4576#64) 480 ∗ stackAt s0.sp allocHookStack) ∗
      A.pool lim (M.stepEvents withReceiverChainEmptyEvents st) sf

set_option maxHeartbeats 4000000 in
theorem withReceiverChain_empty_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_30).rebase (blkPl_30).base H) (blkPl_30).base
      (withLsCodeLoaded lsmpl (withReceiverChainEmptyPlacedSpec M A lim)) := by
  unfold withLsCodeLoaded withReceiverChainEmptyPlacedSpec withReceiverChainEmptyEvents
  simp only [stackAt_withReceiverChain_entry]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_30).rebase (blkPl_30).base H)
    (ecPubKeySerialize_alloc_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 205)
    (withLsCl lsmpl (ecPubKeySerializeAllocPlacedSpec M A lim)) at hser
  dsimp only [withLsCl, ecPubKeySerializeAllocPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hgrow := ls_subroutine_ok_cl_of_block (callerProg := (blkPC_30).rebase (blkPl_30).base H)
    (growOneChain_zero_region_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 43)
    (withLsCl lsmpl (growOneChainZeroRegionPlacedSpec M A lim)) at hgrow
  dsimp only [withLsCl, growOneChainZeroRegionPlacedSpec, growOneChainZeroEvents] at hgrow
  have hshim' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hdealloc' := dealloc_bytes_placed_ok (prog := (blkPC_30).rebase (blkPl_30).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec := ls_hook_ok_of_mem hmemcpy
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  dsimp only [rustDeallocBytesSpec] at hdealloc'
  dsimp only [sessionMemcpyRegionBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy'
  wp_init x s0
  rcases x with ⟨⟨outPtr, inPtr, senderRatchetPubPtr, senderRatchetPub32,
    receiverChainKeyPtr, receiverChainKey32, receiverChainIdx, oldVecPtr, pre72, post248⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr inPtr senderRatchetPubPtr receiverChainKeyPtr
  have hfe_all : FitsEvents M lim st
      [.alloc 32, .alloc 33, .alloc 33, .free 1 33, .alloc 416] := by
    simpa [growOneChainZeroEvents, rustAllocEvents, rustDeallocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++
        rustAllocEvents 33 1 ++ rustDeallocEvents 33 1 ++ growOneChainZeroEvents)›
  rcases hfe_all with ⟨hfe1, hfe2, hfe3, -, hfe4, -⟩
  let st1 := M.stepEvents (rustAllocEvents 32 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  let st3 := M.stepEvents (rustAllocEvents 33 1) st2
  let st4 := M.stepEvents (rustDeallocEvents 33 1) st3
  have hlen_ck : (bytesToBv8 receiverChainKey32).length = 32 := by
    simp [bytesToBv8, ‹receiverChainKey32.length = 32›]
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ := exists_unpack64_of_length_32 hlen_ck
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hpos33 : 0 < (33 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  have hsum33 : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_clean_setMem
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_clean_setMem
  wp_call halloc' (32, 1, st)
  have hne1 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq1 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne1
  have hm32_1 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
      cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
    memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
  conv => arg 4; simp only [hm32_1, cells, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  rw [hck_cells (s0.readReg64 (.gpr 2#5))]
  wp_steps_sync_pool (lsmpl.base 205)
  wp_clean_setMem
  simp only [hck_cells, sepConj_assoc]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 1#5), senderRatchetPub32), st1)
  have hcl2 : LibsignalCodeLoaded lsmpl sf_2.mem := by assumption
  have henc33 : (encodeEC senderRatchetPub32).length = 33 := by
    change (0x05 :: senderRatchetPub32).length = 33; simp [‹senderRatchetPub32.length = 32›]
  have hlen_pub33 : (bytesToBv8 (encodeEC senderRatchetPub32)).length = 33 := by
    simp [bytesToBv8, henc33]
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 43)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_clean_setMem
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_clean_setMem
  wp_call halloc' (33, 1, st2)
  have hne2 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq2 : (sf_4.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne2
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_clean_setMem
  rw [← hlen_pub33]
  wp_call hmemcpy' (sf_4.readReg64 (Reg.gpr 0#5), _, bytesToBv8 (encodeEC senderRatchetPub32))
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_5› (hnext := ?_)
  conv => arg 4; simp only [hlen_pub33, henc33]
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  wp_clean_setMem
  wp_call hdealloc' ((_, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1), st3)
  wp_steps_sync_pool (lsmpl.base 43)
  wp_clean_setMem
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  wp_call hgrow ((s0.readReg64 (.gpr 0#5) + 0x48#64, oldVecPtr), st4)
  conv => arg 4; simp only [memRegion_416_receiverChain_split w_1, cells, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_clean_setMem
  have hpack_in := withReceiverChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
    w_1 pre72 post248 ‹pre72.length = 72›
  have hlen_full : (pre72 ++ (receiverChainVecBytes24 w_1 ++ post248)).length = 344 := by
    simp [‹pre72.length = 72›, ‹post248.length = 248›]
  refine sepWP_focus (T :=
    (s0.readReg64 (.gpr 0#5) ↦ₛ pre72) ∗ ((s0.readReg64 (.gpr 0#5) + 0x48#64) ↦₆₄ 4#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x50#64) ↦₆₄ w_1) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x58#64) ↦₆₄ 1#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x60#64) ↦ₛ post248)) (by sep_frame_ac_rfl) ?_
  rw [hpack_in, ← hlen_full]
  wp_call hmemcpy' (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5),
    pre72 ++ (receiverChainVecBytes24 w_1 ++ post248))
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_8› (hnext := ?_)
  conv => arg 4; simp only [← withReceiverChain_pack344 _ _ _ _ ‹pre72.length = 72›]
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  wp_clean_setMem
  unfold receiverChainElemAt receiverChainVecFieldsAt
  simp only [sepConj_assoc]
  wp_done

theorem withReceiverChain_empty_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_30).rebase (blkPl_30).base H) (blkPl_30).base
      (withLsCodeLoaded lsmpl (withReceiverChainEmptyPlacedSpec M A lim)) :=
  withReceiverChain_empty_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc hdealloc
    (hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm hmemcpy)

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget

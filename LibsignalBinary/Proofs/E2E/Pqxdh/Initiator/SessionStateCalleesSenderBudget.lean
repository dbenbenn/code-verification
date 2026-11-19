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
# Budget-Threaded Relocatable Contract for `<SessionState>::with_sender_chain` (Block `27`)
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
  ls_hook_ok_of_mem ls_subroutine_ok_cl_of_plain
  lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  WithSenderChainGhost blkLib_eq_27 blkPC_27 blkPl_27
  bv_sub_add_lit' bytesToBv8 encodeEC
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  senderChainBytes100 senderChainBytes100_length senderChainFieldsAt
  sp_setMem_setPC_pre sp_setPC_pre stackAt_split_top
  withSenderChain_pack344 withSenderChain_pack344_unfolded
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

private theorem stackAt_withSenderChain_entry (sp : BitVec 64) :
    memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack =
      (memRegion (sp - 128#64 - 4128#64) 32 ∗ stackAt (sp - 128#64) allocHookStack) ∗
        cells (sp - 128#64) 16 := by
  have h1 := stackAt_split_top sp 160 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (32 + allocHookStack) 16 (by decide)
  have h3 := stackAt_split_top (sp - 128#64) 32 allocHookStack (by decide)
  have h4 : (160 + allocHookStack : Nat) = (32 + allocHookStack) + 8 * 16 := by decide
  have h5 : BitVec.ofNat 64 (160 + allocHookStack) = 4256#64 := rfl
  have h6 : BitVec.ofNat 64 (8 * 16) = 128#64 := rfl
  have h7 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  rw [h5] at h1; rw [h6] at h2; rw [h7] at h3
  rw [← h1, h4, h2, ← h3]

private theorem memRegion_92_senderChain_split (ptr : BitVec 64) :
    memRegion (ptr + 0x98#64) 92 =
      cells (ptr + 0x98#64) 11 ∗ (∃∗ v : BitVec 32, (ptr + 0xf0#64) ↦₃₂ v) := by
  have hsplit := memRegion_split (ptr + 0x98#64) 88 4 (by decide)
  have haddr : ptr + 0x98#64 + BitVec.ofNat 64 88 = ptr + 0xf0#64 := by bv_omega
  rw [hsplit, memRegion_cells (ptr + 0x98#64) 11 (by decide), haddr, ProofLib.memRegion_four]

private theorem cells_three_entails (sp v0 v1 v2 : BitVec 64) :
    ((sp - 120#64) ↦₆₄ v0 ∗ (sp - 112#64) ↦₆₄ v1 ∗ (sp - 104#64) ↦₆₄ v2) ⊢
      cells (sp - 120#64) 3 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.refl _)))

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_adds_neg1_1 :
    ConditionHolds CondCode.EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[expose] def withSenderChainNoneEvents : List AllocEvent :=
  rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
    rustAllocEvents 32 1 ++ rustAllocEvents 32 1 ++
    rustDeallocEvents 32 1 ++ rustDeallocEvents 33 1

@[expose] def WithSenderChainNoneEnv (evs : List AllocEvent) : Prop :=
  evs = withSenderChainNoneEvents

@[expose] def withSenderChainNonePlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (WithSenderChainGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.inPtr ∧
      s.readReg64 .x1 = g.senderKeyPairPtr ∧ s.readReg64 .x2 = g.senderChainKeyPtr ∧
      g.senderRatchetPub32.length = 32 ∧ g.senderRatchetPriv32.length = 32 ∧
      g.senderChainKey32.length = 32 ∧ g.pre144.length = 144 ∧ g.post100.length = 100 ∧
      FitsEvents M lim st withSenderChainNoneEvents⌝ ∗
      (g.senderKeyPairPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
      ((g.senderKeyPairPtr + 32#64) ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
      (g.senderChainKeyPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗
      ((g.senderChainKeyPtr + 32#64) ↦₃₂ g.senderChainIdx) ∗
      (g.inPtr ↦ₛ g.pre144) ∗ ((g.inPtr + 0x90#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.inPtr + 0x98#64) 92 ∗ ((g.inPtr + 0xf4#64) ↦ₛ g.post100) ∗
      memRegion g.outPtr 344 ∗ (memRegion (s.sp - 4256#64) 160 ∗ stackAt s.sp allocHookStack) ∗
      A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ senderRatchetPubBoxPtr : BitVec 64, ∃∗ senderRatchetPrivBoxPtr : BitVec 64,
    ∃∗ senderChainKeyBoxPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ senderRatchetPubBoxPtr ≠ 0 ∧ senderRatchetPrivBoxPtr ≠ 0 ∧
        senderChainKeyBoxPtr ≠ 0⌝ ∗
      (g.senderKeyPairPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
      ((g.senderKeyPairPtr + 32#64) ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
      (g.senderChainKeyPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗
      ((g.senderChainKeyPtr + 32#64) ↦₃₂ g.senderChainIdx) ∗
      (senderRatchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC g.senderRatchetPub32)) ∗
      A.live senderRatchetPubBoxPtr 33 1 ∗
      (senderRatchetPrivBoxPtr ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
      A.live senderRatchetPrivBoxPtr 32 1 ∗
      (senderChainKeyBoxPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗ A.live senderChainKeyBoxPtr 32 1 ∗
      (g.outPtr ↦ₛ g.pre144) ∗
      senderChainFieldsAt g.outPtr senderRatchetPubBoxPtr senderRatchetPrivBoxPtr
        senderChainKeyBoxPtr g.senderChainIdx ∗ ((g.outPtr + 0xf4#64) ↦ₛ g.post100) ∗
      (g.inPtr ↦ₛ g.pre144) ∗
      senderChainFieldsAt g.inPtr senderRatchetPubBoxPtr senderRatchetPrivBoxPtr
        senderChainKeyBoxPtr g.senderChainIdx ∗ ((g.inPtr + 0xf4#64) ↦ₛ g.post100) ∗
      (memRegion (s0.sp - 4256#64) 160 ∗ stackAt s0.sp allocHookStack) ∗
      A.pool lim (M.stepEvents withSenderChainNoneEvents st) sf

set_option maxHeartbeats 4000000 in
theorem withSenderChain_none_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_27).rebase (blkPl_27).base H) (blkPl_27).base
      (withLsCodeLoaded lsmpl (withSenderChainNonePlacedSpec M A lim)) := by
  unfold withLsCodeLoaded withSenderChainNonePlacedSpec withSenderChainNoneEvents
  simp only [stackAt_withSenderChain_entry, memRegion_92_senderChain_split]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_27).rebase (blkPl_27).base H)
    (ecPubKeySerialize_alloc_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 205)
    (withLsCl lsmpl (ecPubKeySerializeAllocPlacedSpec M A lim)) at hser
  dsimp only [withLsCl, ecPubKeySerializeAllocPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hpser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_27).rebase (blkPl_27).base H)
    (privKeySerialize_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 208)
    (withLsCl lsmpl (privKeySerializePlacedSpec M A lim)) at hpser
  dsimp only [withLsCl, privKeySerializePlacedSpec, privKeySerializePlacedEvents] at hpser
  have hshim' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hdealloc' := dealloc_bytes_placed_ok (prog := (blkPC_27).rebase (blkPl_27).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
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
  rcases x with ⟨⟨outPtr, inPtr, senderKeyPairPtr, senderRatchetPub32,
    senderRatchetPriv32, senderChainKeyPtr, senderChainKey32, senderChainIdx, pre144, post100⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr inPtr senderKeyPairPtr senderChainKeyPtr
  have hfe_all : FitsEvents M lim st
      [.alloc 32, .alloc 33, .alloc 33, .alloc 32, .alloc 32, .free 1 32, .free 1 33] := by
    simpa [rustAllocEvents, rustDeallocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
        rustAllocEvents 32 1 ++ rustAllocEvents 32 1 ++
        rustDeallocEvents 32 1 ++ rustDeallocEvents 33 1)›
  rcases hfe_all with ⟨hfe1, hfe2, hfe3, hfe4, hfe5, -, -, -⟩
  let st1 := M.stepEvents (rustAllocEvents 32 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  let st3 := M.stepEvents (rustAllocEvents 33 1) st2
  let st4 := M.stepEvents (rustAllocEvents 32 1) st3
  let st5 := M.stepEvents (rustAllocEvents 32 1) st4
  let st6 := M.stepEvents (rustDeallocEvents 32 1) st5
  have hlen_ck : (bytesToBv8 senderChainKey32).length = 32 := by
    simp [bytesToBv8, ‹senderChainKey32.length = 32›]
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
  have hlen_priv32 : (bytesToBv8 senderRatchetPriv32).length = 32 := by
    simp [bytesToBv8, ‹senderRatchetPriv32.length = 32›]
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 208)
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
  wp_steps_sync_pool (lsmpl.base 208)
  wp_clean_setMem
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  apply SepWP.replace_pre (by sep_frame_ac_rfl) (cells_three_entails s0.sp _ _ _)
  wp_call hpser ((s0.readReg64 (.gpr 1#5) + 32#64, bytesToBv8 senderRatchetPriv32, s0.sp - 120#64), st3)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_clean_setMem
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_7› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_clean_setMem
  wp_call halloc' (32, 1, st4)
  have hne3 : sf_8.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq3 : (sf_8.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne3
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_clean_setMem
  rw [← hlen_priv32]
  wp_call hmemcpy' (sf_8.readReg64 (Reg.gpr 0#5), _, bytesToBv8 senderRatchetPriv32)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_9› (hnext := ?_)
  conv => arg 4; simp only [hlen_priv32, ‹senderRatchetPriv32.length = 32›]
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  wp_clean_setMem
  wp_call hdealloc' ((_, bytesToBv8 senderRatchetPriv32, 32, 1), st5)
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  wp_clean_setMem
  wp_call hdealloc' ((_, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1), st6)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_clean_setMem
  have hpack_in := withSenderChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
    (sf_4.readReg64 (.gpr 0#5)) (sf_8.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5))
    senderChainIdx pre144 post100 ‹pre144.length = 144›
  have hlen_full : (pre144 ++ (senderChainBytes100 (sf_4.readReg64 (.gpr 0#5))
      (sf_8.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++
      post100)).length = 344 := by
    simp [‹pre144.length = 144›, ‹post100.length = 100›]
  refine sepWP_focus (T :=
    (s0.readReg64 (.gpr 0#5) ↦ₛ pre144) ∗ ((s0.readReg64 (.gpr 0#5) + 0x90#64) ↦₆₄ 33#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x98#64) ↦₆₄ sf_4.readReg64 (.gpr 0#5)) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xa0#64) ↦₆₄ 33#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xa8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xb0#64) ↦₆₄ sf_8.readReg64 (.gpr 0#5)) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xb8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xc0#64) ↦₆₄ 0#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xc8#64) ↦₆₄ 8#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xd0#64) ↦₆₄ 0#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xd8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xe0#64) ↦₆₄ sf_1.readReg64 (.gpr 0#5)) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xe8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xf0#64) ↦₃₂ senderChainIdx) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xf4#64) ↦ₛ post100)) (by sep_frame_ac_rfl) ?_
  rw [hpack_in, ← hlen_full]
  wp_call hmemcpy' (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pre144 ++
    (senderChainBytes100 (sf_4.readReg64 (.gpr 0#5))
      (sf_8.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++ post100))
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_12› (hnext := ?_)
  simp only [← withSenderChain_pack344 _ _ _ _ _ _ _ ‹pre144.length = 144›, sepConj_assoc]
  wp_done

theorem withSenderChain_none_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_27).rebase (blkPl_27).base H) (blkPl_27).base
      (withLsCodeLoaded lsmpl (withSenderChainNonePlacedSpec M A lim)) :=
  withSenderChain_none_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc hdealloc
    (hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm hmemcpy)

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget

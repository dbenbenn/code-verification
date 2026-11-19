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
# Budget-Threaded Relocatable Contract for `<SessionState>::set_unacknowledged_pre_key_message` (Block `33`)
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
  Bytes CryptoLeafCall blkLib_eq_33 blkPC_33 blkPl_33
  bv_sub_add_lit' bytesToBv8 cryptoLeafStubSpec encodeEC fitBv8
  lsSystemTimeDurationSinceSym
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre stackAt_split_top vecU8
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
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff FitsEvent
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local simp, local wp_norm, local arm64_norm] bytesToBv8_length

local macro "cells_pre_unfold_fast" : tactic =>
  `(tactic| (
    conv => arg 4; simp (config := { maxSteps := 1000000 }) only [
      cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.reduceSub]))

local macro "wp_clean_setMem" : tactic =>
  `(tactic| (
    try (conv => arg 3; simp only [State.setMem_setMem])
    try (conv => arg 4; simp only [State.setMem_setMem])))

abbrev cryptoLeafStubBudgetSpec (fn : Bytes → Bytes) (inLen outLen : Nat) : Spec CryptoLeafCall :=
  withVmPreserved (cryptoLeafStubSpec fn inLen outLen)

private def twoWordsToBytes (w0 w1 : BitVec 64) : Bytes :=
  (unpack64 w0 ++ unpack64 w1).map fun b => UInt8.ofNat b.toNat

private theorem twoWordsToBytes_length (w0 w1 : BitVec 64) :
    (twoWordsToBytes w0 w1).length = 16 := by
  simp [twoWordsToBytes, unpack64]

private theorem bytesToBv8_twoWordsToBytes (w0 w1 : BitVec 64) :
    bytesToBv8 (twoWordsToBytes w0 w1) = unpack64 w0 ++ unpack64 w1 := by
  simp only [twoWordsToBytes, bytesToBv8, List.map_map]
  have h_id : ((fun b : UInt8 => BitVec.ofNat 8 b.toNat) ∘ fun b : BitVec 8 =>
      UInt8.ofNat b.toNat) = id := by
    funext x
    apply BitVec.eq_of_toNat_eq
    have hx : x.toNat < 256 := x.isLt
    change (x.toNat % 256) % 256 = x.toNat
    omega
  rw [h_id, List.map_id]

private theorem pointsTo64_pair_eq_twoWords (a w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦ₛ bytesToBv8 (twoWordsToBytes w0 w1)) := by
  rw [bytesToBv8_twoWordsToBytes, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]

private theorem fitBv8_16_twoWords (w0 w1 : BitVec 64) :
    fitBv8 16 (id (twoWordsToBytes w0 w1)) = bytesToBv8 (twoWordsToBytes w0 w1) := by
  have hlen : (bytesToBv8 (twoWordsToBytes w0 w1)).length = 16 := by
    simp [bytesToBv8, twoWordsToBytes_length]
  simp [fitBv8, hlen, List.take_of_length_le (Nat.le_of_eq hlen)]

private theorem pointsTo64_pair_entails_memRegion16 (a u3 u4 : BitVec 64) :
    ((a ↦₆₄ u3) ∗ ((a + 8#64) ↦₆₄ u4)) ⊢ memRegion a 16 := by
  rw [show (16 : Nat) = 8 + 8 by decide, memRegion_split a 8 8 (by decide),
    memRegion_eight, memRegion_eight]
  exact sepConj_mono (Entails.sepExists_intro u3) (Entails.sepExists_intro u4)

private theorem memRegion_40_unack_split (statePtr : BitVec 64) :
    memRegion (statePtr + 0x100#64) 40 =
      (∃∗ w100 : BitVec 64, (statePtr + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (statePtr + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 32, (statePtr + 0x110#64) ↦₃₂ w110) ∗
      (∃∗ w114 : BitVec 32, (statePtr + 0x114#64) ↦₃₂ w114) ∗
      (∃∗ w118 : BitVec 64, (statePtr + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (statePtr + 0x120#64) ↦₃₂ w120) ∗
      memRegion (statePtr + 0x124#64) 4 := by
  rw [memRegion_split (statePtr + 0x100#64) 8 32 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64) 8 24 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64) 4 20 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64) 4 16 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 8 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 4 4 (by decide),
    memRegion_eight, memRegion_eight, ProofLib.memRegion_four, ProofLib.memRegion_four,
    memRegion_eight, ProofLib.memRegion_four]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem unack_tail24_entails_memRegion (statePtr : BitVec 64)
    (v110 v114 v120 : BitVec 32) (v118 : BitVec 64) :
    ((statePtr + 0x110#64) ↦₃₂ v110) ∗ ((statePtr + 0x114#64) ↦₃₂ v114) ∗
      ((statePtr + 0x118#64) ↦₆₄ v118) ∗ ((statePtr + 0x120#64) ↦₃₂ v120) ∗
      memRegion (statePtr + 0x124#64) 4 ⊢ memRegion (statePtr + 0x110#64) 24 := by
  refine Entails.trans
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo32_entails_memRegion _ _))))) ?_
  rw [memRegion_split (statePtr + 0x110#64) 4 20 (by decide),
    memRegion_split (statePtr + 0x110#64 + 4#64) 4 16 (by decide),
    memRegion_split (statePtr + 0x110#64 + 4#64 + 4#64) 8 8 (by decide),
    memRegion_split (statePtr + 0x110#64 + 4#64 + 4#64 + 8#64) 4 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

private theorem stackAt_setUnack_call (sp : BitVec 64) :
    stackAt (sp - 144#64) (allocHookStack + 32) =
      stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 := by
  have h1 := stackAt_split_cells (sp - 144#64) allocHookStack 4 (by decide)
  have h2 : sp - 144#64 - BitVec.ofNat 64 (8 * 4) = sp - 176#64 := by bv_arith
  rw [h2] at h1
  exact h1

private theorem stackAt_setUnack_hooks (sp : BitVec 64) :
    stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 =
      memRegion (sp - 4272#64) 32 ∗ stackAt (sp - 144#64) allocHookStack := by
  rw [← stackAt_setUnack_call sp]
  have h1 := stackAt_split_top (sp - 144#64) 32 allocHookStack (by decide)
  have h2 : (32 + allocHookStack : Nat) = allocHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have h4 : sp - 144#64 - 4128#64 = sp - 4272#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_neg1_1_true :
    ConditionHolds CondCode.LT (subsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[expose] def setUnackPreKeyMsgEvents : List AllocEvent :=
  rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustDeallocEvents 33 1

@[expose] def SetUnackPreKeyMsgEnv (evs : List AllocEvent) : Prop :=
  evs = setUnackPreKeyMsgEvents

@[expose] def setUnackPreKeyMsgPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec ((BitVec 64 × BitVec 64 × Bytes) × M.σ) where
  pre := fun ((statePtr, baseKeyPtr, baseKeyBytes), st) s =>
    ⌜s.readReg64 .x0 = statePtr ∧ s.readReg64 .x4 = baseKeyPtr ∧ baseKeyBytes.length = 32 ∧
      FitsEvents M lim st setUnackPreKeyMsgEvents⌝ ∗
    (baseKeyPtr ↦ₛ bytesToBv8 baseKeyBytes) ∗ ((statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (statePtr + 0x100#64) 40 ∗ stackAt (s.sp - 144#64) (allocHookStack + 32) ∗
    cells (s.sp - 144#64) 18 ∗ A.pool lim st s
  post := fun ((statePtr, baseKeyPtr, baseKeyBytes), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (baseKeyPtr ↦ₛ bytesToBv8 baseKeyBytes) ∗
    vecU8 A.repAlloc (statePtr + 0xf8#64) (bytesToBv8 (encodeEC baseKeyBytes)) ∗
    memRegion (statePtr + 0x110#64) 24 ∗
    stackAt (s0.sp - 144#64) (allocHookStack + 32) ∗
    cells (s0.sp - 144#64) 18 ∗
    A.pool lim (M.stepEvents setUnackPreKeyMsgEvents st) sf

set_option maxHeartbeats 4000000 in
theorem setUnackPreKeyMsg_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hTime : HookSat H lsSystemTimeDurationSinceSym (cryptoLeafStubBudgetSpec id 16 16)) :
    subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (withLsCodeLoaded lsmpl (setUnackPreKeyMsgPlacedSpec M A lim)) := by
  unfold withLsCodeLoaded setUnackPreKeyMsgPlacedSpec setUnackPreKeyMsgEvents
  have hser : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (lsmpl.base 205)
      (withLsCl lsmpl (ecPubKeySerializeRawPlacedSpec M A lim)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_33).rebase (blkPl_33).base H)
      (ecPubKeySerializeRaw_placed_ok_of_session hshim halloc)
  dsimp only [withLsCl, ecPubKeySerializeRawPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hshim' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hdealloc' := dealloc_bytes_placed_ok (prog := (blkPC_33).rebase (blkPl_33).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec := ls_hook_ok_of_mem hmemcpy
  have htime' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsSystemTimeDurationSinceSym) (cryptoLeafStubBudgetSpec id 16 16) :=
    ls_hook_ok_of_mem hTime
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  dsimp only [rustDeallocBytesSpec] at hdealloc'
  dsimp only [sessionMemcpyRegionBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy'
  dsimp only [cryptoLeafStubBudgetSpec, withVmPreserved, cryptoLeafStubSpec] at htime'
  wp_init x s0
  rcases x with ⟨⟨statePtr, baseKeyPtr, baseKeyBytes⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst statePtr baseKeyPtr
  have hfe_all : FitsEvents M lim st [.alloc 33, .alloc 33, .free 1 33] := by
    simpa [rustAllocEvents, rustDeallocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustDeallocEvents 33 1)›
  rcases hfe_all with ⟨hfe1, hfe2, -, -⟩
  let st1 := M.stepEvents (rustAllocEvents 33 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  have henc33 : (encodeEC baseKeyBytes).length = 33 := by
    change (0x05 :: baseKeyBytes).length = 33; simp [‹baseKeyBytes.length = 32›]
  have hlen_enc : (bytesToBv8 (encodeEC baseKeyBytes)).length = 33 := by
    simp [bytesToBv8, henc33]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos33 : 0 < (33 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum33 : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  rw [memRegion_40_unack_split (s0.readReg64 (.gpr 0#5))]
  cells_pre_unfold_fast
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun c0 => SepWP.exists_elim fun c1 => SepWP.exists_elim fun c2 => ?_
  repeat (refine SepWP.exists_elim fun _ => ?_)
  rw (occs := .pos [1]) [stackAt_setUnack_call s0.sp]
  rw [pointsTo64_split32' (s0.sp - 128#64)]
  conv => arg 4; simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  wp_clean_setMem
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 4#5), baseKeyBytes), st)
  apply SepWP.replace_pre (by sep_frame_ac_rfl) (Entails.of_eq (stackAt_setUnack_hooks s0.sp))
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_clean_setMem
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_clean_setMem
  wp_call halloc' (33, 1, st1)
  have hne : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_clean_setMem
  rw [← hlen_enc]
  wp_call hmemcpy' (sf_2.readReg64 (Reg.gpr 0#5), _, bytesToBv8 (encodeEC baseKeyBytes))
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  conv => arg 4; simp only [hlen_enc, henc33]
  wp_steps_sync_pool (lsρ lsSystemTimeDurationSinceSym)
  wp_clean_setMem
  have h128_eq : s0.sp - 128#64 + 4#64 = s0.sp - 124#64 := by bv_arith
  have h136_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_arith
  have h120_eq : s0.sp - 120#64 + 8#64 = s0.sp - 112#64 := by bv_arith
  apply SepWP.replace_pre (by sep_frame_ac_rfl)
    (Entails.of_eq (h128_eq ▸ pointsTo32_pair (s0.sp - 128#64) _ _))
  apply SepWP.replace_pre (by sep_frame_ac_rfl)
    (Entails.of_eq (h136_eq ▸ pointsTo64_pair_eq_twoWords (s0.sp - 136#64) _ _))
  apply SepWP.replace_pre (by sep_frame_ac_rfl)
    (h120_eq ▸ pointsTo64_pair_entails_memRegion16 (s0.sp - 120#64) _ _)
  have hlen_tw := twoWordsToBytes_length (s0.readReg64 (.gpr 5#5))
    (BitVec.extractLsb' 32 32 c2 ++ BitVec.truncate 32 (s0.readReg64 (.gpr 6#5)))
  wp_call htime' ⟨s0.sp - 136#64, twoWordsToBytes (s0.readReg64 (.gpr 5#5))
    (BitVec.extractLsb' 32 32 c2 ++ BitVec.truncate 32 (s0.readReg64 (.gpr 6#5))), s0.sp - 120#64⟩
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_4› (hnext := ?_)
  rw [fitBv8_16_twoWords, ← pointsTo64_pair_eq_twoWords (s0.sp - 136#64),
    ← pointsTo64_pair_eq_twoWords (s0.sp - 120#64), h136_eq, h120_eq]
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  rw [show sf_3.sp = sf_4.sp by simp only [*, arm64_norm]]
  wp_clean_setMem
  wp_call hdealloc' ((_, bytesToBv8 (encodeEC baseKeyBytes), 33, 1), st2)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  wp_clean_setMem
  apply SepWP.replace_pre (by sep_frame_ac_rfl)
    (unack_tail24_entails_memRegion (s0.readReg64 (.gpr 0#5)) _ _ _ _)
  conv => arg 4; simp only [*]
  apply SepWP.replace_pre (by sep_frame_ac_rfl)
    (Entails.of_eq ((stackAt_setUnack_call s0.sp).trans (stackAt_setUnack_hooks s0.sp)).symm)
  dsimp only [st2, st1]
  conv => arg 5; intro sf_f P_f; simp only [vecU8, A.repAlloc_live, AllocCostModel.stepEvents_append]
  cells_unfold
  wp_done

theorem setUnackPreKeyMsg_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (hTime : HookSat H lsSystemTimeDurationSinceSym (cryptoLeafStubBudgetSpec id 16 16)) :
    subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (withLsCodeLoaded lsmpl (setUnackPreKeyMsgPlacedSpec M A lim)) :=
  setUnackPreKeyMsg_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc hdealloc
    (hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm hmemcpy) hTime

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget

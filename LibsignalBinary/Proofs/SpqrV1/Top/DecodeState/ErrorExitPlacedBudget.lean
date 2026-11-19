/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.SepFocusAc
meta import LibsignalBinary.Proofs.TripleRatchet.SepFocusAc -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DefsPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Stack Frame & Error Exits for `spqr::decode_state` (Block `325`)

Proves the budget-threaded relocatable shared epilogue (`+2500..+2528`), `DecodeError`
drop/unwind tail (`+2392..+2528`), and top-level `DecodeError::push` error-exit blocks.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalTripleRatchet (KindNoHeap decodeErrorAtStackLen sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchet.Prost (box72_entails_memRegion kindNoHeap_branch_false shl5_toNat)
open CryptoVerification.LibsignalSpqrV1 (spqrDecodeState)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost DropProtoPqRatchetStateGhost TraceVRegs V1InnerHeapPred decodeErrorWith_unfold decodeStatePlacedEntry decodeStatePlacedProg decodeStateResultAt decodeStateSavedAt decodeStateStackX decodeState_stack_restore_1296 dropOptProtoInnerStateStack fold_decodeStateResultAt_err frame_4chunks_to_1296 memRegion_352_err_split protoPqRatchetStateAt protoPqRatchetState_of_memcpy protoPqRatchetState_to_memcpy scratch_688_fold_48 sp_sub_1392_aligned stackAt_of_callee stackAt_to_callee)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux (deallocFreeOnlySpec freeOnlyEvs_rustDeallocEvents subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitBudget (SepWPp.call_decodeErrorFrom_gen SepWPp.call_decodeErrorPush_gen)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced decodeStatePlacedSpecX dropProtoPqRatchetStatePlacedSpec spqrDecodeStatePlacedSpec spqrDecodeStatePlacedSpecOfEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Relocatable Budget-Threaded Postcondition & Envelope Helpers -/

abbrev decodeStatePostPlacedOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (spqrDecodeStatePlacedSpecOfEnv H_inner A lim PreEnv PostEnv).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev decodeStatePanicPostPlacedOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (spqrDecodeStatePlacedSpecOfEnv H_inner A lim PreEnv PostEnv).onPanic x s0 sf ∗ R)

abbrev decodeStatePostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStatePlacedSpecX H_inner A lim).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev decodeStatePanicPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStatePlacedSpecX H_inner A lim).onPanic x s0 sf ∗ R)

theorem pool_fold_postEnv {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {x : DecodeStateGhost} {st0 st : M.σ} {s0 sf : State}
    (htr : sf.trace = s0.trace)
    (henv : ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = st) :
    A.pool lim st sf ⊢
      (∃∗ evs : List AllocEvent,
        ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st0) sf) := by
  rcases henv with ⟨evs, hpostEnv, hst⟩
  rw [← hst]
  exact Arm64.Entails.trans
    (Entails.pure_right ⟨htr, hpostEnv⟩ (Entails.of_eq rfl))
    (@Entails.sepExists_intro (List AllocEvent)
      (fun evs' => ⌜sf.trace = s0.trace ∧ PostEnv x evs'⌝ ∗
        A.pool lim (M.stepEvents evs' st0) sf) evs)

theorem sepWP_done_postEnv [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {prog : Program} {s0 sf : State} {P F R : SepProp}
    {x : DecodeStateGhost} {st0 st : M.σ}
    (hpc : sf.pc = s0.readReg64 .x30)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s0.sp)
    (hcs : CalleeSavedPreserved s0 sf)
    (htr : sf.trace = s0.trace)
    (henv : ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = st)
    (hf : P = A.pool lim st sf ∗ F)
    (hF : F = v1StateJumpTablesPlacedAt ∗ x.st.at A.repAlloc ∗
        decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) ∗
        stackAt s0.sp decodeStateStackX) :
    SepWP prog (s0.readReg64 .x30) sf P
      (decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  apply SepWP.done hpc hrun
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [spqrDecodeStatePlacedSpecOfEnv]
  rw [hf, hF] at hm
  exact Satisfies.mono (sepConj_mono_left (sepConj_mono_left (pool_fold_postEnv htr henv))) hm

theorem decodeStateEnv_of_loop {M : AllocCostModel} {x : DecodeStateGhost}
    {st0 st : M.σ} {f : Nat} {evs_acc : List AllocEvent}
    (hf : f ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = st :=
  ⟨evs_acc, hloop.mono_fuel hf, hst⟩

theorem decodeStateEnv_of_loop_free {M : AllocCostModel} {x : DecodeStateGhost}
    {st0 st : M.σ} {f : Nat} {evs_acc : List AllocEvent}
    (hf : f + 1 ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∀ evs_f, FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_f st := by
  intro evs_f hfree
  refine ⟨evs_acc ++ evs_f,
    (hloop.append (DecodeStateLoopEnv.single (fuel := 0) (.deallocs hfree))).mono_fuel hf, ?_⟩
  rw [M.stepEvents_append, hst]

/-! ## 2. Shared Epilogue `0x53e60..0x53e7c` and Error Tail `0x53df4..0x53e5c` -/

/-- Envelope-parameterized shared epilogue `0x53e60..0x53e7c` (`+2500..+2528`, 8 instructions):
restores `sp := sp + 0x510`, pops `x20, x19, ..., x29, x30`, `sp := sp + 0x60`, and returns. -/
theorem decodeState_epilogue_53e60_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ) (s0 s : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (henv : ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = st)
    (hpc : s.pc = decodeStatePlacedEntry + 2500#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 1296 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP hpost
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  unfold decodeStateSavedAt
  wp_steps_sync_pool (s0.readReg64 .x30)
  simp only [State.setMem_setMem]
  refine SepWP.fold (decodeState_stack_restore_1296 s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
    unfold decodeStateSavedAt
    sep_focus_ac) ?_
  exact sepWP_done_postEnv
    (by simp only [wp_norm, arm64_norm, Reg.x30])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm])
    (by unfold CalleeSavedPreserved; simp only [wp_norm, arm64_norm, hvregs, and_self])
    (by simp only [wp_norm, arm64_norm, htr])
    henv
    (by sep_focus_ac)
    (by sep_ac_rfl)

theorem decodeState_epilogue_53e60_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ) (s0 s : State) (P R : SepProp)
    (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (henv : ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = st)
    (hpc : s.pc = decodeStatePlacedEntry + 2500#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (htr : TraceVRegs s s0)
    (hP : P =
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) ∗
      A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
      memRegion (s0.sp - 1392#64) 1296 ∗
      decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post :=
  decodeState_epilogue_53e60_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    x st0 st s0 s P R post hpost henv hpc hrun hsp hs0A htr hP

/-! ## 3. Panic-Aware Call Helpers (`DecodeError::push`, `DecodeError::from`) & `0x53cdc..0x53df0` -/

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget

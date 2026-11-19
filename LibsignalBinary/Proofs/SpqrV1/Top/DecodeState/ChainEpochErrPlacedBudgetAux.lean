/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErr
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainEpochPB` Drop Helpers

Budget-threaded relocatable `[LibsignalPlacement]` `ChainEpochPB` error frames, drop blocks
(`+1976`, `+1924`, `+1908`, `+2936`), and shared `DecodeError::from` block (`+1900`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalSpqrV1 (ChainEpochPB EpochDirectionPB PqRatchetState spqrDecodeState)
open CryptoVerification.SpqrV1.ProtoRepr (chainEpochPBAt epochDirectionPBAt optEpochDirectionPBAt rustBytesVecAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg decodeStateSavedAt epochDirection_recv_none_to_56 epochDirection_recv_raw_to_56 epochDirection_send_raw_to_48 epoch_regions_to_err_frame optEpochDirectionPBAt_none optEpochDirectionPBAt_some protoPqRatchetStateAt rustBytesVecAt_unfold_drop sp_sub_1392_aligned stackAt_of_callee stackAt_to_callee)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux (deallocFreeOnlySpec freeOnlyEvs_rustDeallocEvents subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv DecodeStateLoopEnv FitsEnv.decodeStateLoop_tail)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux (decodeStateIterEnv_of_decodeErrorFrom fitsEnv_decodeErrorPush_of_loop)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Budget-Threaded `ChainEpochPB` Error Frames & `DecodeStateLoopEnv` Helpers -/

/-- Common stack/heap frame during `ChainEpochPB` error drop under `[LibsignalPlacement]`. -/
abbrev decodeStateEpochErrTailFramePlaced [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 s : State) : SepProp :=
  v1StateJumpTablesPlacedAt ∗
  x.st.at A.repAlloc ∗
  memRegion x.outPtr 352 ∗
  A.pool lim st s ∗
  stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
  memRegion (s0.sp - 1392#64) 352 ∗
  protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
  memRegion (s0.sp - 576#64) 240 ∗
  memRegion (s0.sp - 336#64) 240 ∗
  decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

/-- Complete `ChainEpochPB` error frame under `[LibsignalPlacement]`. -/
abbrev decodeStateEpochErrFramePlaced [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 s : State) : SepProp :=
  chainEpochPBAt A.repAlloc (s0.sp - 688#64) curEpoch ∗
  decodeStateEpochErrTailFramePlaced H_inner A lim st x curSt s0 s

theorem fitsEnv_epochDrop_push1_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound n : Nat} (hn : n ≤ 4) (hrem : 2 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    ∀ evs_d, FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d st) (DecodeErrorPushEnv n) := by
  intro evs_d hd
  have h1 : FitsEnv M lim st (DecodeStateLoopEnv ((rem - 1) + 1) maxLen polyCapBound) :=
    fun evs hevs => hFit evs (hevs.mono_fuel (by omega))
  exact fitsEnv_decodeErrorPush_of_loop hn (by omega)
    (FitsEnv.decodeStateLoop_tail (.deallocs hd) h1)

theorem fitsEnv_epochDrop_push2_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound n : Nat} (hn : n + 1 ≤ 4) (hrem : 3 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    ∀ evs_d evs_p1, FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d st))
        (DecodeErrorPushEnv (n + 1)) := by
  intro evs_d evs_p1 hd hp1
  have h1 : FitsEnv M lim st (DecodeStateLoopEnv ((rem - 1) + 1) maxLen polyCapBound) :=
    fun evs hevs => hFit evs (hevs.mono_fuel (by omega))
  have h2 : FitsEnv M lim (M.stepEvents evs_d st)
      (DecodeStateLoopEnv ((rem - 2) + 1) maxLen polyCapBound) :=
    fun evs hevs =>
      FitsEnv.decodeStateLoop_tail (.deallocs hd) h1 evs (hevs.mono_fuel (by omega))
  exact fitsEnv_decodeErrorPush_of_loop hn (by omega)
    (FitsEnv.decodeStateLoop_tail (.pushErr (by omega) hp1) h2)

theorem decodeStateEnv_of_loop_epochDrop_push2_free {M : AllocCostModel} {x : DecodeStateGhost}
    {st0 st : M.σ} {f n : Nat} {evs_acc : List AllocEvent}
    (hn : n + 1 ≤ 4)
    (hf : f + 4 ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∀ evs_d evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d st))) := by
  intro evs_d evs_p1 evs_p2 evs_f hd hp1 hp2 hfree
  have h1 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_d :=
    DecodeStateLoopEnv.single (fuel := 0) (.deallocs hd)
  have h2 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p1 :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr (by omega) hp1)
  have h3 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p2 :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr hn hp2)
  have h4 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_f :=
    DecodeStateLoopEnv.single (fuel := 0) (.deallocs hfree)
  refine ⟨(((evs_acc ++ evs_d) ++ evs_p1) ++ evs_p2) ++ evs_f,
    ((((hloop.append h1).append h2).append h3).append h4).mono_fuel hf, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, hst]

theorem decodeStateEnv_of_loop_from_epochDrop_push2_free {M : AllocCostModel}
    {x : DecodeStateGhost} {st0 st : M.σ} {f : Nat} {evs_acc : List AllocEvent}
    (hf : f + 5 ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∀ evs_fr evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))) := by
  intro evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree
  have h0 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_fr :=
    DecodeStateLoopEnv.single (fuel := 0) (decodeStateIterEnv_of_decodeErrorFrom hfr)
  have h1 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_d :=
    DecodeStateLoopEnv.single (fuel := 0) (.deallocs hd)
  have h2 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p1 :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr (by decide) hp1)
  have h3 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p2 :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr (by decide) hp2)
  have h4 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_f :=
    DecodeStateLoopEnv.single (fuel := 0) (.deallocs hfree)
  refine ⟨((((evs_acc ++ evs_fr) ++ evs_d) ++ evs_p1) ++ evs_p2) ++ evs_f,
    (((((hloop.append h0).append h1).append h2).append h3).append h4).mono_fuel hf, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append,
    M.stepEvents_append, hst]

theorem decodeStateEnv_of_loop_push_epochDrop_push2_free {M : AllocCostModel}
    {x : DecodeStateGhost} {st0 st : M.σ} {f n : Nat} {evs_acc : List AllocEvent}
    (hn : n + 2 ≤ 4)
    (hf : f + 5 ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∀ evs_p0 evs_d evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))) := by
  intro evs_p0 evs_d evs_p1 evs_p2 evs_f hp0 hd hp1 hp2 hfree
  have h0 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p0 :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr (by omega) hp0)
  have h1 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_d :=
    DecodeStateLoopEnv.single (fuel := 0) (.deallocs hd)
  have h2 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p1 :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr (by omega) hp1)
  have h3 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p2 :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr hn hp2)
  have h4 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_f :=
    DecodeStateLoopEnv.single (fuel := 0) (.deallocs hfree)
  refine ⟨((((evs_acc ++ evs_p0) ++ evs_d) ++ evs_p1) ++ evs_p2) ++ evs_f,
    (((((hloop.append h0).append h1).append h2).append h3).append h4).mono_fuel hf, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append,
    M.stepEvents_append, hst]

private theorem shift_hfits1 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {n : Nat}
    {evs_s : List AllocEvent} (hs : FreeOnlyEvs evs_s)
    (hfits1 : ∀ evs_d, FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d st) (DecodeErrorPushEnv n)) :
    ∀ evs_r, FreeOnlyEvs evs_r →
      FitsEnv M lim (M.stepEvents evs_r (M.stepEvents evs_s st)) (DecodeErrorPushEnv n) := by
  intro evs_r hr
  rw [← M.stepEvents_append evs_s evs_r st]
  exact hfits1 (evs_s ++ evs_r) (hs.append hr)

private theorem shift_hfits2 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {n : Nat}
    {evs_s : List AllocEvent} (hs : FreeOnlyEvs evs_s)
    (hfits2 : ∀ evs_d evs_p1, FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d st)) (DecodeErrorPushEnv (n + 1))) :
    ∀ evs_r evs_p1, FreeOnlyEvs evs_r → DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_r (M.stepEvents evs_s st)))
        (DecodeErrorPushEnv (n + 1)) := by
  intro evs_r evs_p1 hr hp1
  rw [← M.stepEvents_append evs_s evs_r st]
  exact hfits2 (evs_s ++ evs_r) evs_p1 (hs.append hr) hp1

private theorem shift_henv {M : AllocCostModel} {PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {x : DecodeStateGhost} {st0 st : M.σ} {n : Nat}
    {evs_s : List AllocEvent} (hs : FreeOnlyEvs evs_s)
    (henv : ∀ evs_d evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_d → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d st)))) :
    ∀ evs_r evs_p1 evs_p2 evs_f,
      FreeOnlyEvs evs_r → DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1 (M.stepEvents evs_r (M.stepEvents evs_s st)))) := by
  intro evs_r evs_p1 evs_p2 evs_f hr hp1 hp2 hfree
  rw [← M.stepEvents_append evs_s evs_r st]
  exact henv (evs_s ++ evs_r) evs_p1 evs_p2 evs_f (hs.append hr) hp1 hp2 hfree

/-! ## `ChainEpochPB` Inlined Drop & Push Paths (`0x53c5c`, `0x53c28`, `0x53c18`, `0x54014`) -/

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux

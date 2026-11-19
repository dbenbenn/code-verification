/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux2
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainEpochPB` Dispatch & Loop Body

Budget-threaded relocatable `[LibsignalPlacement]` framing, `ChainEpochPB` tag dispatch (`+1036`),
and single loop iteration (`+996`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join suffix_trans)
open CryptoVerification.SpqrV1.Prost.MessageMerge (mergeLoopBin protoPrefixStep_chainEpochPB_mergeField)
open CryptoVerification.LibsignalSpqrV1 (ChainEpochPB PqRatchetState spqrDecodeState)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred chainEpochPBCapOkAt chainEpochPBCapOkAt_entails_chainEpochPBAt chainEpochPBCapOkAt_mono chainEpochPB_mergeField_other chainEpochPB_mergeField_tag1 chainEpochPB_mergeField_tag2 codecWireTypeToProto decodeStatePlacedEntry decodeStatePlacedProg key_and7_of_wt_none key_and7_of_wt_some key_lsr32_eq_zero_of_lt key_lsr32_ne_zero_of_ge key_lsr3_32_eq mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge mergeLoopBin_of_key_ok mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_mono sp_sub_1392_aligned tag_cbz32_false tag_cbz64_false tag_cmp32_of_gt tag_lt_pow29_of_key_lt tag_setWidth32_ofNat tag_zeroExtend64_ofNat32 truncate32_zeroExtend64_lsr3 wt_setWidth8 wt_ult6)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (DecodeVarintSliceEnv decodeVarintSliceEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv FitsEnv.decodeStateLoop_head FitsEnv.decodeStateLoop_mono FitsEnv.decodeStateLoop_split FitsEnv.decodeStateLoop_tail)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux (decodeStateIterEnv_of_decodeErrorFrom fitsEnv_decodeErrorFrom_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget (decodeStateEpochErrFramePlaced decodeStateEpochErrTailFramePlaced decodeStateEnv_of_loop_epochDrop_push2_free decodeStateEnv_of_loop_from_epochDrop_push2_free decodeStateEnv_of_loop_push_epochDrop_push2_free fitsEnv_epochDrop_push1_of_loop fitsEnv_epochDrop_push2_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced SepWPpIPlaced.call_decodeVarint2 decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget (decodeStateLoopEnv_of_epochDirectionMergePost_err decodeStateLoopEnv_of_epochDirectionMergePost_ok decodeStateLoopEnv_of_skipField3 epochLoop_calleeErr_to_epochErrFrame_placed epochLoop_cursor_to_epochErrFrame_placed epochRecvMergeGhost epochSendMergeGhost fitsEnv_epochDirectionMerge_of_loop fitsEnv_epochMergeErr_push0_of_loop fitsEnv_epochMergeErr_push1_of_loop fitsEnv_epochMergeErr_push2_of_loop fitsEnv_skipField3_of_loop)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] truncate32_zeroExtend64_lsr3

local macro "pool_reg_norm" : tactic =>
  `(tactic| try simp only [RustCliAllocBudget.pool_setPC_norm,
    RustCliAllocBudget.pool_advancePC_norm, RustCliAllocBudget.pool_setPState_norm,
    RustCliAllocBudget.pool_writeReg64_norm, RustCliAllocBudget.pool_writeReg32_norm,
    RustCliAllocBudget.pool_writeReg_norm, RustCliAllocBudget.pool_writeVReg128_norm,
    RustCliAllocBudget.pool_writeVReg64_norm])

/-! ## Envelope & Framing Helpers After `decode_varint` Inside `ChainEpochPB` Loop -/

theorem lift_postEnv {M : AllocCostModel} {x : DecodeStateGhost} {st0 st' : M.σ}
    {PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (h : ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = st') :
    ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = st' :=
  let ⟨evs, hd, heq⟩ := h
  ⟨evs, hpost_env evs hd, heq⟩

theorem stepEvents_nil_of_acc {M : AllocCostModel} {evs_acc : List AllocEvent} {st0 st : M.σ}
    (hst : M.stepEvents evs_acc st0 = st) :
    M.stepEvents [] st = st := by
  have h1 := M.stepEvents_append evs_acc [] st0
  rw [List.append_nil, hst] at h1
  exact h1.symm

theorem decodeVarint2Env_eq_nil_of_some {bs rest : List (BitVec 8)} {v : BitVec 64}
    {evs : List AllocEvent}
    (hdv : decodeVarint bs = some (v, rest)) (hevs : DecodeVarint2Env bs evs) :
    evs = [] := by
  simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents] at hevs
  rw [hdv] at hevs
  exact hevs

theorem fitsEnv_decodeVarint2_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound : Nat} {bs : List (BitVec 8)}
    (hrem : 1 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    FitsEnv M lim st (DecodeVarint2Env bs) :=
  FitsEnv.decodeStateLoop_head (fuel := rem - 1)
    (fun _ h => DecodeStateIterEnv.of_decodeVarint2 h)
    (fun evs hevs => hFit evs (hevs.mono_fuel (by omega)))

theorem fitsEnv_from_epochDrop_push1_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound : Nat}
    (hrem : 3 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    ∀ evs_fr evs_d, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 0) := by
  intro evs_fr evs_d hfr hd
  exact fitsEnv_epochDrop_push1_of_loop (by decide : 0 ≤ 4) (by decide : 2 ≤ 2)
    (FitsEnv.decodeStateLoop_tail (decodeStateIterEnv_of_decodeErrorFrom hfr)
      (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit))
    evs_d hd

theorem fitsEnv_from_epochDrop_push2_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound : Nat}
    (hrem : 4 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    ∀ evs_fr evs_d evs_p1,
      DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_fr st)))
        (DecodeErrorPushEnv 1) := by
  intro evs_fr evs_d evs_p1 hfr hd hp1
  exact fitsEnv_epochDrop_push2_of_loop (by decide : 0 + 1 ≤ 4) (by decide : 3 ≤ 3)
    (FitsEnv.decodeStateLoop_tail (decodeStateIterEnv_of_decodeErrorFrom hfr)
      (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit))
    evs_d evs_p1 hd hp1

theorem after_decodeVarint2_to_epochErrFrame_placed [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) {cur rest1 : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hle1 : rest1.length ≤ cur.length)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 s : State) :
    sliceCursorAfter (s0.sp - 1056#64)
        (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1 ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s ⊢
      decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s := by
  have hj := sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr) hcur_le hcur_suf hle1
  have hreord :
      sliceCursorAfter (s0.sp - 1056#64)
          (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1 ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s =
      ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        sliceCursorAfter (s0.sp - 1056#64)
          (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s := by sep_ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left hj) ?_
  exact epochLoop_cursor_to_epochErrFrame_placed H_inner A lim st x rest1 cur.length cur.length
    curSt curEpoch s0 s

theorem after_decodeVarint2_err_to_epochErrFrame_placed [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) {cur : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 s : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s ⊢
      decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s := by
  have hep := chainEpochPBCapOkAt_entails_chainEpochPBAt A.repAlloc (s0.sp - 688#64) cur.length
    curEpoch
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hep))))) ?_
  exact epochLoop_calleeErr_to_epochErrFrame_placed H_inner A lim st x hcur_le hcur_suf cur.length
    curSt curEpoch s0 s

/-! ## Tag Dispatch and Single Loop Iteration of `ChainEpochPB::merge` -/

private theorem prost_codecWireTypeToProto_eq (iwt : WireType) :
    CryptoVerification.SpqrV1.Prost.MessageMerge.codecWireTypeToProto iwt =
      codecWireTypeToProto iwt := by
  cases iwt <;> rfl

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationPlacedBudgetAux
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable `VersionNegotiationPB` Dispatch & Body (Block `325`)

Proves envelope/callee-contract bridges along with budget-threaded relocatable
`VersionNegotiationPB` tag dispatch (`+1304`) and single field-key decode iteration (`+1264`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarintAux skipField)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeCapOk BytesMergeGhost IsDropSuffix SkipFieldGhost sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join suffix_trans)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_mergeBytes_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto mergeLoopBin protoPrefixStep_versionNegotiationPB_mergeField protoWireTypeToCodec_codecWireTypeToProto)
open CryptoVerification.LibsignalSpqrV1 (ChainPB ChainParamsPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeBytes)
open CryptoVerification.SpqrV1.Top.DecodeState (ChainParamsMergeGhost DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg errFrame_parts_fold key_and7_of_wt_none key_and7_of_wt_some key_lsr3_32_eq key_lsr32_eq_zero_of_lt key_lsr32_ne_zero_of_ge mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge mergeLoopBin_of_key_ok mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt protoPqRatchetStateCapOkAt_mono sp_sub_1392_aligned tag_cbz32_false tag_cbz64_false tag_cmp32_of_gt tag_lt_pow29_of_key_lt tag_setWidth32_ofNat tag_zeroExtend64_ofNat32 truncate32_zeroExtend64_lsr3 versionNegotiationPB_mergeField_other versionNegotiationPB_mergeField_tag1 versionNegotiationPB_mergeField_tag2 versionNegotiationPB_mergeField_tag3 versionNegotiationPB_mergeField_tag4 wt_setWidth8 wt_ult6)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SkipField3Env bytesMerge3RawBudgetSpec skipField3EventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (DecodeVarintSliceEnv decodeVarintSliceEvents)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (ChainParamsMergeEnv ChainParamsMergePostEnv DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced bytesMerge3DetBudgetSpec bytesMerge3RawBudgetSpecOfEnv decodeStateLoopCommonPlaced loopCommon_cursor_to_errFrame_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero truncate32_zeroExtend64_lsr3
attribute [local simp] truncate32_zeroExtend64_lsr3

theorem decodeState_codecWireTypeToProto_eq (wt : WireType) :
    CryptoVerification.SpqrV1.Top.DecodeState.codecWireTypeToProto wt =
      codecWireTypeToProto wt := by
  cases wt <;> rfl

/-! ## 1. Envelope & Callee-Contract Bridge Helpers -/

private theorem decodeVarintAux_length_lt (i : Nat) (acc : BitVec 64)
    (bs rest0 : List (BitVec 8)) (len : BitVec 64)
    (h : decodeVarintAux i acc bs = some (len, rest0)) :
    rest0.length < bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b bs' ih =>
    unfold decodeVarintAux at h
    dsimp only at h
    split at h
    · split at h
      · contradiction
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp
    · split at h
      · contradiction
      · have hlt := ih _ _ h
        simp; omega

private theorem mergeBytes_length_sum {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : CryptoVerification.LibsignalProtoCodec.mergeBytes wt bs = some (v, rest)) :
    1 + v.length + rest.length ≤ bs.length := by
  cases wt <;> try simp [CryptoVerification.LibsignalProtoCodec.mergeBytes] at h
  cases hvar : decodeVarint bs with
  | none => simp [hvar] at h
  | some p =>
    rcases p with ⟨len, rest0⟩
    rw [hvar] at h
    dsimp only at h
    split at h
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 : rest0.length < bs.length := decodeVarintAux_length_lt 0 0 bs rest0 len hvar
      have h2 : (rest0.take len.toNat).length + (rest0.drop len.toNat).length = rest0.length := by
        rw [← List.length_append, List.take_append_drop]
      omega

private theorem proto_mergeBytes_length_sum {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : (mergeBytes (codecWireTypeToProto wt) bs).toOption = some (v, rest)) :
    1 + v.length + rest.length ≤ bs.length := by
  have heq : CryptoVerification.LibsignalProtoCodec.mergeBytes wt bs =
      (mergeBytes (codecWireTypeToProto wt) bs).toOption := by
    have h0 := proto_mergeBytes_toOption (codecWireTypeToProto wt) bs
    rw [protoWireTypeToCodec_codecWireTypeToProto] at h0
    exact h0.symm
  exact mergeBytes_length_sum (heq.trans h)

private theorem decodeVarint2Env_eq_nil_of_some {bs rest : List (BitVec 8)} {v : BitVec 64}
    {evs : List AllocEvent}
    (hdv : decodeVarint bs = some (v, rest)) (hevs : DecodeVarint2Env bs evs) :
    evs = [] := by
  simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] at hevs
  exact hevs

private theorem skipField3Env_eq_nil_of_some {x : SkipFieldGhost} {rest : List (BitVec 8)}
    {evs : List AllocEvent}
    (hsf : skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs = some rest)
    (hevs : SkipField3Env x evs) :
    evs = [] := by
  simp only [SkipField3Env, skipField3EventsCore, hsf] at hevs
  exact hevs

private theorem decodeErrorFromEnv_iter {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) :
    DecodeStateIterEnv maxLen polyCapBound evs := by
  rw [h]
  exact .of_decodeErrorFrom

theorem err3_fits1 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {E1 : List AllocEvent → Prop}
    (hf : 3 ≤ fuel)
    (h1 : ∀ evs, E1 evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv fuel maxLen polyCapBound)) :
    FitsEnv M lim st E1 :=
  SpecsBudget.FitsEnv.decodeStateLoop_head (fuel := 2) h1
    (SpecsBudget.FitsEnv.decodeStateLoop_mono (f₁ := 3) hf (Nat.le_refl _) (Nat.le_refl _) hFit)

theorem err3_fits2 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {E1 : List AllocEvent → Prop}
    (hf : 3 ≤ fuel)
    (h1 : ∀ evs, E1 evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv fuel maxLen polyCapBound)) :
    ∀ evs1, E1 evs1 → FitsEnv M lim (M.stepEvents evs1 st) (DecodeErrorPushEnv 0) :=
  fun evs1 he1 =>
    SpecsBudget.FitsEnv.decodeStateLoop_head (fuel := 1)
      (fun _ hp => .of_decodeErrorPush (by decide) hp)
      (SpecsBudget.FitsEnv.decodeStateLoop_tail (fuel := 2) (h1 evs1 he1)
        (SpecsBudget.FitsEnv.decodeStateLoop_mono (f₁ := 3) hf (Nat.le_refl _) (Nat.le_refl _)
          hFit))

theorem err3_env {M : AllocCostModel} {PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {x : DecodeStateGhost} {st0 st : M.σ} {fuel maxLen polyCapBound : Nat}
    {E1 : List AllocEvent → Prop}
    (hf : 3 ≤ fuel)
    (h1 : ∀ evs, E1 evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (henv : ∀ evs_err, DecodeStateLoopEnv fuel maxLen polyCapBound evs_err →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st) :
    ∀ evs1 evs_p evs_f, E1 evs1 → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 = M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs1 st)) := by
  intro evs1 evs_p evs_f he1 hp hfree
  have hloop3 : DecodeStateLoopEnv 3 maxLen polyCapBound (evs1 ++ (evs_p ++ evs_f)) :=
    DecodeStateLoopEnv.step (h1 evs1 he1)
      (DecodeStateLoopEnv.step (.of_decodeErrorPush (by decide) hp)
        (DecodeStateLoopEnv.single (.of_freeOnly hfree)))
  obtain ⟨evs, hpost, hstep⟩ := henv _ (hloop3.mono_fuel hf)
  exact ⟨evs, hpost, by rw [hstep, M.stepEvents_append, M.stepEvents_append]⟩

private theorem err4_fits1 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {E1 : List AllocEvent → Prop}
    (hf : 4 ≤ fuel)
    (h1 : ∀ evs, E1 evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv fuel maxLen polyCapBound)) :
    FitsEnv M lim st E1 :=
  SpecsBudget.FitsEnv.decodeStateLoop_head (fuel := 3) h1
    (SpecsBudget.FitsEnv.decodeStateLoop_mono (f₁ := 4) hf (Nat.le_refl _) (Nat.le_refl _) hFit)

private theorem err4_fits2 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {E1 : List AllocEvent → Prop} {evs1 : List AllocEvent}
    (hf : 4 ≤ fuel)
    (h1 : ∀ evs, E1 evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv fuel maxLen polyCapBound))
    (he1 : E1 evs1) :
    FitsEnv M lim (M.stepEvents evs1 st) (DecodeErrorPushEnv 0) :=
  SpecsBudget.FitsEnv.decodeStateLoop_head (fuel := 2)
    (fun _ hp => .of_decodeErrorPush (by decide) hp)
    (SpecsBudget.FitsEnv.decodeStateLoop_tail (fuel := 3) (h1 evs1 he1)
      (SpecsBudget.FitsEnv.decodeStateLoop_mono (f₁ := 4) hf (Nat.le_refl _) (Nat.le_refl _) hFit))

private theorem err4_fits3 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {E1 : List AllocEvent → Prop}
    {evs1 evs_p1 : List AllocEvent}
    (hf : 4 ≤ fuel)
    (h1 : ∀ evs, E1 evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv fuel maxLen polyCapBound))
    (he1 : E1 evs1) (hp1 : DecodeErrorPushEnv 0 evs_p1) :
    FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs1 st)) (DecodeErrorPushEnv 1) :=
  SpecsBudget.FitsEnv.decodeStateLoop_head (fuel := 1)
    (fun _ hp2 => .of_decodeErrorPush (by decide) hp2)
    (SpecsBudget.FitsEnv.decodeStateLoop_tail (fuel := 2) (.of_decodeErrorPush (by decide) hp1)
      (SpecsBudget.FitsEnv.decodeStateLoop_tail (fuel := 3) (h1 evs1 he1)
        (SpecsBudget.FitsEnv.decodeStateLoop_mono (f₁ := 4) hf (Nat.le_refl _) (Nat.le_refl _)
          hFit)))

private theorem err4_env {M : AllocCostModel} {PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {x : DecodeStateGhost} {st0 st : M.σ} {fuel maxLen polyCapBound : Nat}
    {E1 : List AllocEvent → Prop} {evs1 evs_p1 evs_p2 evs_f : List AllocEvent}
    (hf : 4 ≤ fuel)
    (h1 : ∀ evs, E1 evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (henv : ∀ evs_err, DecodeStateLoopEnv fuel maxLen polyCapBound evs_err →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st)
    (he1 : E1 evs1) (hp1 : DecodeErrorPushEnv 0 evs_p1)
    (hp2 : DecodeErrorPushEnv 1 evs_p2) (hfree : FreeOnlyEvs evs_f) :
    ∃ evs, PostEnv x evs ∧
      M.stepEvents evs st0 =
        M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs1 st))) := by
  have hloop4 : DecodeStateLoopEnv 4 maxLen polyCapBound (evs1 ++ (evs_p1 ++ (evs_p2 ++ evs_f))) :=
    DecodeStateLoopEnv.step (h1 evs1 he1)
      (DecodeStateLoopEnv.step (.of_decodeErrorPush (by decide) hp1)
        (DecodeStateLoopEnv.step (.of_decodeErrorPush (by decide) hp2)
          (DecodeStateLoopEnv.single (.of_freeOnly hfree))))
  obtain ⟨evs, hpost, hstep⟩ := henv _ (hloop4.mono_fuel hf)
  exact ⟨evs, hpost,
    by rw [hstep, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]⟩

/-- Fold post-`decodeVarint2` cursor + `protoPqRatchetStateCapOkAt` + `decodeStateLoopCommonPlaced`
into `decodeStateErrFramePlaced` under `RustCliAllocBudget M`. -/
theorem after_decodeVarint2_to_errFrame_placed [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) {cur rest1 : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hle1 : rest1.length ≤ cur.length) (curSt : PqRatchetState) (s0 s : State) :
    sliceCursorAfter (s0.sp - 1056#64)
        (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1 ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s ⊢
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s := by
  have hj := sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr) hcur_le hcur_suf hle1
  have hreord :
      sliceCursorAfter (s0.sp - 1056#64)
          (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1 ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s =
      ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        sliceCursorAfter (s0.sp - 1056#64)
          (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s := by sep_ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left hj) ?_
  exact loopCommon_cursor_to_errFrame_placed H_inner A lim st x rest1 cur.length curSt s0 s

/-! ## 2. Tag Dispatch (`+1304`) & Field-Key Body (`+1264`) -/

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux

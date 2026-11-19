/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudgetAux1
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudgetAux2
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainPB` Dispatch & Loop Body

Budget-threaded relocatable `[LibsignalPlacement]` accumulator bridges, `ChainPB` tag dispatch (`+560`),
and single loop iteration (`+520`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarintAux skipField)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeGhost IsDropSuffix SkipFieldGhost sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join suffix_trans)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_mergeBytes_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto mergeLoopBin protoPrefixStep_chainPB_mergeField protoWireTypeToCodec_codecWireTypeToProto)
open CryptoVerification.LibsignalSpqrV1 (ChainPB ChainParamsPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeBytes)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred chainPB_mergeField_other chainPB_mergeField_tag1 chainPB_mergeField_tag2 chainPB_mergeField_tag4 chainPB_mergeField_tag5 chainPB_mergeField_tag6 decodeStatePlacedEntry decodeStatePlacedProg errFrame_parts_fold key_and7_of_wt_none key_and7_of_wt_some key_lsr3_32_eq key_lsr32_eq_zero_of_lt key_lsr32_ne_zero_of_ge mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge mergeLoopBin_of_key_ok mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt protoPqRatchetStateCapOkAt_mono sp_sub_1392_aligned tag_cbz32_false tag_cbz64_false tag_cmp32_of_gt tag_lt_pow29_of_key_lt tag_setWidth32_ofNat tag_zeroExtend64_ofNat32 truncate32_zeroExtend64_lsr3 wt_setWidth8 wt_ult6)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SkipField3Env skipField3EventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (DecodeVarintSliceEnv decodeVarintSliceEvents)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (ChainParamsMergeEnv ChainParamsMergePostEnv DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux (after_decodeVarint2_to_errFrame_placed decodeState_codecWireTypeToProto_eq err3_env err3_fits1 err3_fits2)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero truncate32_zeroExtend64_lsr3
attribute [local simp] truncate32_zeroExtend64_lsr3

/-! ## Envelope & Accumulator Helpers -/

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

theorem decodeVarint2Env_eq_nil_of_some {bs rest : List (BitVec 8)} {v : BitVec 64}
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

theorem decodeErrorFromEnv_iter {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) :
    DecodeStateIterEnv maxLen polyCapBound evs := by
  rw [h]
  exact .of_decodeErrorFrom

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

theorem acc_henv_err {M : AllocCostModel}
    {PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {x : DecodeStateGhost} {st0 st : M.σ} {evs_acc : List AllocEvent} {f k : Nat}
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hf : f + k ≤ 16 * x.st.bytes.length + 32)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs) :
    ∀ evs_err,
      DecodeStateLoopEnv k x.st.bytes.length (2 * x.st.bytes.length + 16) evs_err →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st := by
  intro evs_err herr
  refine ⟨evs_acc ++ evs_err, hpost_env _ ((hacc.append herr).mono_fuel hf), ?_⟩
  rw [M.stepEvents_append, hst]

private theorem acc_fits_split {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {rem d maxLen polyCapBound : Nat} {evs_step : List AllocEvent}
    (hd : d ≤ rem)
    (hstep : DecodeStateLoopEnv d maxLen polyCapBound evs_step)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs_step st)
      (DecodeStateLoopEnv (rem - d) maxLen polyCapBound) :=
  SpecsBudget.FitsEnv.decodeStateLoop_split hstep
    (SpecsBudget.FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)

/-! ## `ChainPB` Tag Dispatch (`+560`) -/

/-! ## Single Loop Iteration of `ChainPB::merge` (`+520`) -/

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudgetAux

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
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainEpochPB` Merge Helpers

Budget-threaded relocatable `[LibsignalPlacement]` proofs of `ChainEpochPB` tag 2 (`recv`, `+1052`)
and `skip_field(depth=98)` (`+964`), re-exporting tag 1 (`send`) and framing helpers.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (WireType skipField)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix SkipFieldGhost sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.LibsignalSpqrV1 (ChainEpochPB EpochDirectionPB PqRatchetState spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred cap_add_one_beq_zero_false chainEpochPBCapOkAt chainEpochPBCapOkAt_entails_chainEpochPBAt chainEpochPBCapOkAt_mono decodeStatePlacedEntry decodeStatePlacedProg epochDirectionPBCapOkAt_default_init protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_mono sp_sub_1392_aligned)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv DecodeStateLoopEnv EpochDirectionMergeEnv EpochDirectionMergePostEnv FitsEnv.decodeStateLoop_mono FitsEnv.decodeStateLoop_split)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget (decodeStateEpochErrFramePlaced decodeStateEpochErrTailFramePlaced decodeStateEnv_of_loop_epochDrop_push2_free decodeStateEnv_of_loop_push_epochDrop_push2_free fitsEnv_epochDrop_push1_of_loop fitsEnv_epochDrop_push2_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux2 (epochRecvMergeGhost)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux (optEpochDirectionPB_none_split48 optEpochDirectionPBCapOkAt_some optEpochDirectionPBCapOkAt_none optEpochDirectionPBAt_some_eq epochDirectionPBCapOkRestAt)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux (epochDirectionPBCapOkAt_expose_cap epochDirectionPBCapOkAt_fold_cap chainEpochPBCapOkAt_eq chainEpochPBAt_eq epochLoop_cursor_to_epochErrFrame_placed)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux (epochLoop_calleeErr_to_epochErrFrame_placed fitsEnv_epochDirectionMerge_of_loop decodeStateLoopEnv_of_epochDirectionMergePost_ok decodeStateLoopEnv_of_epochDirectionMergePost_err fitsEnv_epochMergeErr_push0_of_loop)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux (fitsEnv_epochMergeErr_push1_of_loop fitsEnv_epochMergeErr_push2_of_loop fitsEnv_skipField3_of_loop decodeStateLoopEnv_of_skipField3 fitsEnv_growOneChainEpoch_of_loop)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux (decodeStateLoopEnv_of_growOneChainEpoch)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux2 (epochSendMergeGhost epochRecvMergeGhost)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local irreducible] skipField
  CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
  CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "pool_reg_norm" : tactic =>
  `(tactic| try simp only [RustCliAllocBudget.pool_setPC_norm,
    RustCliAllocBudget.pool_advancePC_norm, RustCliAllocBudget.pool_setPState_norm,
    RustCliAllocBudget.pool_writeReg64_norm, RustCliAllocBudget.pool_writeReg32_norm,
    RustCliAllocBudget.pool_writeReg_norm, RustCliAllocBudget.pool_writeVReg128_norm,
    RustCliAllocBudget.pool_writeVReg64_norm])

/-- `SkipFieldGhost` at depth `98` inside `ChainEpochPB::merge` of `spqr::decode_state`. -/
abbrev epochSkipGhost (x : DecodeStateGhost) (rest1 : List (BitVec 8)) (tag : Nat) (iwt : WireType)
    (s0 : State) : SkipFieldGhost :=
  ⟨iwt, tag, 98, s0.sp - 336#64, s0.sp - 1056#64,
    x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩

/-! ## `ChainEpochPB` Tag Body Helpers (`recv`, `skip_field`) -/

abbrev SepWPpIPlaced.call_epochDirectionMerge_ofEnv :=
  @LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux.SepWPpIPlaced.call_epochDirectionMerge_ofEnv
abbrev SepWPpIPlaced.call_epochDirectionMerge :=
  @LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux.SepWPpIPlaced.call_epochDirectionMerge
abbrev SepWPpIPlaced.call_growOneChainEpoch :=
  @LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux.SepWPpIPlaced.call_growOneChainEpoch

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget

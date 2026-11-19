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
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainEpochPB` `send` & `recv` Call Helpers

Budget-threaded relocatable `[LibsignalPlacement]` proofs of `ChainEpochPB` tag 1 (`send`, `+1108`)
and the tag 2 (`recv`) call helper (`+1088`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux2

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (WireType skipField)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.LibsignalSpqrV1 (ChainEpochPB EpochDirectionPB PqRatchetState spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost EpochDirectionMergeGhost TraceVRegs V1InnerHeapPred cap_add_one_beq_zero_false chainEpochPBCapOkAt decodeStatePlacedEntry decodeStatePlacedProg epochDirectionPBCapOkAt_default_init optEpochDirectionPBCapOkAt optEpochDirectionPBCapOkAt_entails_optEpochDirectionPBAt optEpochDirectionPBCapOkAt_mono protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_mono sp_sub_1392_aligned)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv DecodeStateLoopEnv EpochDirectionMergeEnv EpochDirectionMergePostEnv FitsEnv.decodeStateLoop_mono FitsEnv.decodeStateLoop_split)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget (decodeStateEpochErrFramePlaced decodeStateEpochErrTailFramePlaced decodeStateEnv_of_loop_push_epochDrop_push2_free)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux (SepWPpIPlaced.call_epochDirectionMerge chainEpochPBAt_eq chainEpochPBCapOkAt_eq decodeStateLoopEnv_of_epochDirectionMergePost_err decodeStateLoopEnv_of_epochDirectionMergePost_ok epochDirectionPBCapOkAt_expose_cap epochDirectionPBCapOkAt_fold_cap epochLoop_calleeErr_to_epochErrFrame_placed fitsEnv_epochDirectionMerge_of_loop fitsEnv_epochMergeErr_push0_of_loop fitsEnv_epochMergeErr_push1_of_loop fitsEnv_epochMergeErr_push2_of_loop optEpochDirectionPBAt_some_eq optEpochDirectionPBCapOkAt_none optEpochDirectionPBCapOkAt_some optEpochDirectionPB_none_split48)

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

/-- `EpochDirectionMergeGhost` at `s0.sp - 688#64` (`curEpoch.send`) inside `spqr::decode_state`. -/
abbrev epochSendMergeGhost (x : DecodeStateGhost) (d : EpochDirectionPB)
    (rest1 : List (BitVec 8)) (iwt : WireType) (s0 : State) : EpochDirectionMergeGhost :=
  ⟨iwt, s0.sp - 688#64, d, s0.sp - 336#64, s0.sp - 1056#64,
    x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩

/-- `EpochDirectionMergeGhost` at `s0.sp - 632#64` (`curEpoch.recv`) inside `spqr::decode_state`. -/
abbrev epochRecvMergeGhost (x : DecodeStateGhost) (d : EpochDirectionPB)
    (rest1 : List (BitVec 8)) (iwt : WireType) (s0 : State) : EpochDirectionMergeGhost :=
  ⟨iwt, s0.sp - 632#64, d, s0.sp - 336#64, s0.sp - 1056#64,
    x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩

/-! ## `ChainEpochPB` Tag 1 (`send`) & Tag 2 (`recv`) Call Helpers -/

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux2

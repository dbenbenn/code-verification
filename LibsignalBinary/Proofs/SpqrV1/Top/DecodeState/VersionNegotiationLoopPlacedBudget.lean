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
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable `VersionNegotiationPB` Merge Loop & Tag-1 Entry (Block `325`)

Re-exports dispatch and body helpers from `VersionNegotiationLoopPlacedBudgetAux` and proves
budget-threaded relocatable merge-loop induction (`+1252`), delimited entry (`+216`), and outer
Tag-1 handling (`+184`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (decodeVarint)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join suffix_trans)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto mergeLoopBin protoPrefixStep_versionNegotiationPB_mergeField)
open CryptoVerification.LibsignalSpqrV1 (ChainPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred bv_len_sub_limit cap_add_one_beq_zero_false cmp_len_limit_bne_of_lt cmp_len_limit_of_eq cmp_len_limit_of_gt cmp_len_limit_of_lt decodeStatePlacedEntry decodeStatePlacedProg errFrame_parts_fold len_ult_of_ge len_ult_of_lt mergeLoopBin_eq_limit mergeLoopBin_lt_limit mergeMessage_toOption_of_decodeVarint_none mergeMessage_toOption_of_ge mergeMessage_toOption_of_lt mergeMessage_toOption_of_ne_lengthDelimited optVersionNegotiationPBCapOkAt optVersionNegotiationPB_none_split40 protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt protoPqRatchetStateCapOkAt_mono protoPqRatchetStateCapOkAt_some_vn_eq sp_sub_1392_aligned suffix_eq_drop_of_len_eq truncate32_zeroExtend64_lsr3 vecU8At_eq_header_heap vecU8At_header_fold vecU8CapOkAt vecU8Heap_cap_lt versionNegotiationPBCapOkAt_default_init wt64_ne_two_of_ne_lengthDelimited)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (DecodeVarintSliceEnv decodeVarintSliceEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced bytesMerge3DetBudgetSpec decodeStateLoopCommonPlaced loopCommon_cursor_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux (after_decodeVarint2_to_errFrame_placed decodeState_codecWireTypeToProto_eq err3_env err3_fits1 err3_fits2)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux (after_decodeVarint2_to_errFrame_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero truncate32_zeroExtend64_lsr3
attribute [local simp] truncate32_zeroExtend64_lsr3

private theorem decodeErrorFromEnv_iter {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) :
    DecodeStateIterEnv maxLen polyCapBound evs := by
  rw [h]
  exact .of_decodeErrorFrom

private theorem decodeVarint2Env_eq_nil_of_some {bs rest : List (BitVec 8)} {v : BitVec 64}
    {evs : List AllocEvent}
    (hdv : decodeVarint bs = some (v, rest)) (hevs : DecodeVarint2Env bs evs) :
    evs = [] := by
  simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] at hevs
  exact hevs

/-! ## 1. Inlined `VersionNegotiationPB` Merge Loop (`+1252`) -/

/-! ## 2. Delimited `VersionNegotiationPB::merge` (`+216`) & Outer Tag-1 Entry (`+184`) -/

attribute [local irreducible]
  mergeMessage mergeLoopBin CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudget

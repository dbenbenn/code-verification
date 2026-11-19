/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudgetAux1
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget

/-!
# Budget-Threaded Relocatable `ChainPB` Tag 4 & Tag 5 Handlers for `spqr::decode_state` (Block `325`)

Proves budget-threaded relocatable `ChainPB` handlers for Tag 4 (`next_root: Vec<u8>`,
`+824..+844`) and Tag 5 (`send_epoch: u64`, `+904..+932`, `+1180..+1188`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudgetAux2

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeCapOk BytesMergeGhost IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.LibsignalSpqrV1 (ChainPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg errFrame_parts_fold optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt optProtoPqRatchetInnerCapOkAt_mono optVersionNegotiationPBCapOkAt_entails_optVersionNegotiationPBAt optVersionNegotiationPBCapOkAt_mono protoPqRatchetStateCapOkAt sp_sub_1392_aligned vecU8CapOkAt_entails_rustBytesVecAt vecU8CapOkAt_mono wireType_ofNat64_ne_zero_of_ne_varint)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced bytesMerge3DetBudgetSpec bytesMerge3RawBudgetSpecOfEnv decodeStateLoopCommonPlaced loopCommon_cursor_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudgetAux1 (chainLinks_bound_drop chainLinks_bound_mono protoPqRatchetStateAt_some_ch_eq protoPqRatchetStateCapOkAt_some_ch_eq)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `ChainPB` Field Merge Handlers — Tags 4 & 5 -/

private theorem _keep_module : True := trivial

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudgetAux2

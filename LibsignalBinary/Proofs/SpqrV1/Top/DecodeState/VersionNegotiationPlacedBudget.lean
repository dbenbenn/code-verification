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
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudgetAux
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable `VersionNegotiationPB` Tag Body Helpers (Block `325`)

Re-exports Tag 1..3 helpers from `VersionNegotiationPlacedBudgetAux` and proves budget-threaded
relocatable Tag 4 (`chain_params`, `+1228`, `+1372`) and `skip_field` (`+1392`) body lemmas.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.LibsignalSpqrV1 (ChainPB ChainParamsPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg errFrame_parts_fold optChainPBCapOkAt_entails_optChainPBAt optChainPBCapOkAt_mono optChainParamsPBAt_none_to_init optChainParamsPBAt_some_default_init optChainParamsPBAt_some_eq optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt optProtoPqRatchetInnerCapOkAt_mono protoPqRatchetStateAt_some_vn_eq protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt protoPqRatchetStateCapOkAt_mono protoPqRatchetStateCapOkAt_some_vn_eq sp_sub_1392_aligned vecU8CapOkAt_entails_rustBytesVecAt vecU8CapOkAt_mono)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (ChainParamsMergeEnv ChainParamsMergePostEnv DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced decodeStateLoopCommonPlaced)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem _keep_module : True := trivial

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationPlacedBudget

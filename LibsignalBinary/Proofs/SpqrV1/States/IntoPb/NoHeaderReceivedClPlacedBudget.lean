/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersX
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget

/-!
# Budget-Threaded `<States>::into_pb` (Block `334`) — Arm 5 (`States.noHeaderReceived`) with `withLsCodeLoaded`

Re-exports `NoHeaderReceivedEnv` and `withLsCodeLoaded` relocatable contracts for Arm 5
(`States.noHeaderReceived`, tag `7`) from `Part4aPlacedBudget`, and lifts them to `withLsCl`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalPlacement lsmpl lsρ withLsCl withLsCodeLoaded
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  subroutine_ok_withLsCl_of_withLsCodeLoaded
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  subroutine_ok_withLsCodeLoaded_of_withLsCl
)
open CryptoVerification.LibsignalSpqrV1 (spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (NoHeaderReceived)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget (
  statesIntoPbVariantPlacedSpecOfEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget (
  NoHeaderReceivedEnv statesIntoPbNoHeaderReceivedPlacedSpec
  statesIntoPb_seq_sepWP_cl_vm call_memcpy_keep_relocate_cl_placed
  states_into_pb_noHeaderReceived_of_env_cl_placed
  states_into_pb_noHeaderReceived_env_cl_placed
  states_into_pb_noHeaderReceived_cl_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

/-! ## 1. Re-Exports from `Part4aPlacedBudget` -/

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget (
  NoHeaderReceivedEnv statesIntoPbNoHeaderReceivedPlacedSpec
  statesIntoPb_seq_sepWP_cl_vm call_memcpy_keep_relocate_cl_placed
)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget (
  states_into_pb_noHeaderReceived_of_env_cl_placed
  states_into_pb_noHeaderReceived_env_cl_placed
  states_into_pb_noHeaderReceived_cl_placed
)

/-! ## 2. `withLsCl` Relocatable Arm 5 Contracts -/

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlacedBudget

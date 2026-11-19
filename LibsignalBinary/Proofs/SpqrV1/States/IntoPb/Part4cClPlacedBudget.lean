/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersX
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Arm 4 (`States.ekSentCt1Received`) with `withLsCodeLoaded`

Re-exports `EkSentCt1ReceivedEnv` and the `withLsCodeLoaded` Block `334` contracts for Arm 4
(`States.ekSentCt1Received`, tag `6`) from `Part4cPlacedBudget`, and lifts them to `withLsCl`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cClPlacedBudget

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
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (EkSentCt1Received)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget (
  statesIntoPbVariantPlacedSpecOfEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlacedBudget (
  EkSentCt1ReceivedEnv statesIntoPbEkSentCt1ReceivedPlacedSpec
  states_into_pb_ekSentCt1Received_of_env_cl_placed
  states_into_pb_ekSentCt1Received_env_cl_placed
  states_into_pb_ekSentCt1Received_cl_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

/-! ## 1. Re-Exports from `Part4cPlacedBudget` -/

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlacedBudget (
  EkSentCt1ReceivedEnv statesIntoPbEkSentCt1ReceivedPlacedSpec
)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlacedBudget (
  states_into_pb_ekSentCt1Received_of_env_cl_placed
  states_into_pb_ekSentCt1Received_env_cl_placed
  states_into_pb_ekSentCt1Received_cl_placed
)

/-! ## 2. `withLsCl` Relocatable Arm 4 Wrappers -/

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cClPlacedBudget

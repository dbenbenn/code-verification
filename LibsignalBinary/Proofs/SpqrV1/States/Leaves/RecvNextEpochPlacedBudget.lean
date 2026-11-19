/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlaced
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.PlacedCallSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Drop.Poly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `<Ct2Sampled>::recv_next_epoch` (Budget-Threaded Relocatable, Block `355`)

Re-exports the Block `355` budget-threaded contracts from `RecvNextEpochBudget` and provides
envelope-parametric `[LibsignalPlacement]` lifts `ct2_sampled_recv_next_epoch_placed_{ok,cl}_ext_ofEnv`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPl_355 extract_withLsCodeLoaded lsProg_355 lsmpl withLsCodeLoaded)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct2SampledRecvNextEpochGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
  (dropGluePoly16Spec)

/-! ## 1. Re-Exports from `RecvNextEpochBudget` & `DefsPlacedBudget` -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochBudget
  (Ct2SampledRecvNextEpochEnv ct2SampledRecvNextEpochEnv_nonempty
   ct2SampledRecvNextEpochSpec ct2SampledRecvNextEpochSpecOfEnv
   subroutine_ok_ct2SampledRecvNextEpochSpecOfEnv_freeOnly)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochBudget
  (Ct2SampledRecvNextEpochPlacedOkX Ct2SampledRecvNextEpochPlacedOkXOfEnv
   call_dropGluePoly16_cl call_dropGluePoly16_budget)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochBudget
  (ct2_sampled_recv_next_epoch_placed_ok_ext
   ct2_sampled_recv_next_epoch_placed_cl_ext
   ct2_sampled_recv_next_epoch_placed_ok_x
   ct2_sampled_recv_next_epoch_placed_ok_x_ofEnv)

/-! ## 2. Envelope-Parametric `[LibsignalPlacement]` Lifts for Block `355` -/

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlacedBudget

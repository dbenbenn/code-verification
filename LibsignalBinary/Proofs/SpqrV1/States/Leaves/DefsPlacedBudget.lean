/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# SPQR V1 Send-Leaf Transitions: Relocatable `RustCliAllocBudget` Bridges & `SepWPp` Helpers

Re-exports relocatable `withLsCodeRoLoaded` / `withLsCallInv` bridges and `DefsBudget` send-leaf
envelopes and specifications, and provides `SepWP` → `SepWPp` call helpers
`call_polyNextChunk_placed_sepWPp{,_ofEnv}` for `PolyEncoder::next_chunk` (Block `416`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget

open Arm64 ProofLib
open CryptoVerification
  (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (Chunk PolyEncoder)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt chunkSize polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (PolyNextChunkGhost polyNextChunkStack)
open CryptoVerification.SpqrV1.States.Leaves
  (Regs19To27Eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
  (polyNextChunkPlacedSpec polyNextChunkPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (PolyEncoderNextChunkEnv call_polyNextChunk_placed_ofEnv)

/-! ## 1. Re-Exports of Allocator-Free `withLsCodeRoLoaded` / `withLsCallInv` & Sequencing Bridges -/

export CryptoVerification.SpqrV1.States.Leaves
  (lsCallInv_iff_codeRoLoaded subroutine_ok_withLsCodeLoaded_of_left
   subroutine_ok_withLsCodeRoLoaded_of_left
   subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
   subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv)

export CryptoVerification.SpqrV1.States.Leaves
  (subroutine_ok_withLsCodeRoLoaded_of_plain
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   ls_subroutine_ok_to_blockProgram sepWP_seq_lscl of_sepWP_lscl)

export CryptoVerification.SpqrV1.States.Leaves
  (of_sepWP_lscro)

/-! ## 2. Re-Exports of Relocatable Envelopes, Specifications, Contracts & Call Helpers -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (Ct2SampledRecvNextEpochEnv ct2SampledRecvNextEpochEnv_nonempty
   PolyEncoderNextChunkEnv polyNextChunkEnv_eq_polyEncoderNextChunkEnv
   polyEncoderNextChunkEnv_nonempty)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (EkReceivedCt1SampledSendCt1ChunkEnv ekReceivedCt1SampledSendCt1ChunkEnv_nonempty
   Ct2SampledSendCt2ChunkEnv ct2SampledSendCt2ChunkEnv_nonempty
   HeaderSentSendEkChunkEnv)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (headerSentSendEkChunkEnv_nonempty Ct1ReceivedSendEkChunkEnv
   ct1ReceivedSendEkChunkEnv_nonempty Ct1SampledSendCt1ChunkEnv
   ct1SampledSendCt1ChunkEnv_nonempty)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (ct2SampledRecvNextEpochSpec ct2SampledRecvNextEpochSpecOfEnv
   subroutine_ok_ct2SampledRecvNextEpochSpecOfEnv_freeOnly
   ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv
   ekReceivedCt1SampledSendCt1ChunkPlacedSpec)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (ct2SampledSendCt2ChunkPlacedSpecOfEnv ct2SampledSendCt2ChunkPlacedSpec
   headerSentSendEkChunkPlacedSpecOfEnv headerSentSendEkChunkPlacedSpec
   ct1ReceivedSendEkChunkPlacedSpecOfEnv)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (ct1ReceivedSendEkChunkPlacedSpec ct1SampledSendCt1ChunkPlacedSpecOfEnv
   ct1SampledSendCt1ChunkPlacedSpec Ct2SampledRecvNextEpochPlacedOkX
   Ct2SampledRecvNextEpochPlacedOkXOfEnv)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (HeaderSentSendEkChunkPlacedOkXOfEnv HeaderSentSendEkChunkPlacedOkX
   Ct1ReceivedSendEkChunkPlacedOkXOfEnv Ct1ReceivedSendEkChunkPlacedOkX
   Ct1SampledSendCt1ChunkPlacedOkXOfEnv)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (Ct1SampledSendCt1ChunkPlacedOkX
   EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv
   EkReceivedCt1SampledSendCt1ChunkPlacedOkX
   Ct2SampledSendCt2ChunkPlacedOkXOfEnv Ct2SampledSendCt2ChunkPlacedOkX)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (sepWP_seq_lscro call_memcpy_relocate_vm call_memcpy_relocate_pool
   call_dropGluePoly16_cl call_polyNextChunk_placed_ofEnv)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (call_polyNextChunk_placed)

/-! ## 3. `SepWP` → `SepWPp` Relocatable `PolyEncoder::next_chunk` Call Helpers -/

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget

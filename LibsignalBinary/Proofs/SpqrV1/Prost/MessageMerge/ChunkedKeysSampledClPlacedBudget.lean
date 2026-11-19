/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudgetSteps
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledUcClPlacedBudget
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBase
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Code-Loaded Placed Budget Wrapper for `Chunked.KeysSampled::merge` (Block `304`)

Re-exports the `withLsCodeRoLoaded lsmpl` budget-threaded inner and outer step, loop, and top-level
contracts for `Chunked.KeysSampled::merge` on Block `304`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledClPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledUcClPlacedBudget
  (chunkedKeysSampled_push_ret_exit_cl_placed
   chunkedKeysSampled_uc_decode_key_step_cl_placed
   chunkedKeysSampled_uc_loop_ok_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudgetAux
  (chunkedKeysSampled_decode_key_step_cl_placed
   chunkedKeysSampled_loop_le_exit_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudgetSteps
  (chunkedKeysSampled_skip_step_cl_placed
   chunkedKeysSampled_tag1_step_cl_placed
   chunkedKeysSampled_tag2_step_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudget
  (chunkedKeysSampled_loop_ok_cl_placed
   chunked_keys_sampled_merge_cl_placed_ok_of_contracts)

alias chunkedKeysSampled_merge_cl_placed_ok_of_contracts :=
  chunked_keys_sampled_merge_cl_placed_ok_of_contracts

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledClPlacedBudget

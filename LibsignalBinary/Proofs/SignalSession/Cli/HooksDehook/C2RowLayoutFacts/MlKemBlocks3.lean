/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable -- proof-setup: allow-public-import
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `mlkemMultiLib` RX Block-Walk Shard 3 (Blocks 10..19)

`rfl_kernel` word-walk checks for `mlkemMultiLib` blocks `10..19`
(`from_seed`, `EncapsState::to_bytes`, `constant_time_ops::*`, and `encapsulate1`, 3,044 B total).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks3

open ProofLib.Placed.Split (rLen)
open ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (checkMultiBlockWalk checkProgCodeSubslice_of_multiBlockWalk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2MlkemMpl)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3TrialRxProg f3TrialRxWordTree)

@[expose] def mlkemShard3 : List Nat := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19]

set_option maxRecDepth 4000000 in
private theorem c2_mlkem_shard3a_walk_ok :
    (([10, 11, 12, 13, 14] : List Nat).all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes (rLen f3TrialRxWordTree.toBytes)
        mlkemMultiLib c2MlkemMpl j) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_mlkem_shard3b_walk_ok :
    (([15, 16, 17, 18, 19] : List Nat).all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes (rLen f3TrialRxWordTree.toBytes)
        mlkemMultiLib c2MlkemMpl j) = true := by
  rfl_kernel

private theorem c2_mlkem_shard3_walk_ok :
    (mlkemShard3.all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes (rLen f3TrialRxWordTree.toBytes)
        mlkemMultiLib c2MlkemMpl j) = true := by
  change (([10, 11, 12, 13, 14] ++ [15, 16, 17, 18, 19]).all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes (rLen f3TrialRxWordTree.toBytes)
        mlkemMultiLib c2MlkemMpl j) = true
  rw [List.all_append]
  exact Bool.and_eq_true_iff.mpr ⟨c2_mlkem_shard3a_walk_ok, c2_mlkem_shard3b_walk_ok⟩

theorem c2_mlkem_rx_blocks_3 :
    ∀ j ∈ mlkemShard3,
      checkProgCodeSubslice f3TrialRxProg (mlkemMultiLib.blockProgram c2MlkemMpl j) = true :=
  fun j hj =>
    checkProgCodeSubslice_of_multiBlockWalk rfl rfl rfl
      (List.all_eq_true.mp c2_mlkem_shard3_walk_ok j hj)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks3

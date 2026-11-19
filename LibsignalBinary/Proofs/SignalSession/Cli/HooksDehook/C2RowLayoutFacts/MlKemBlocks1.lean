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
# `mlkemMultiLib` RX Block-Walk Shard 1 (Blocks 5..6)

`rfl_kernel` word-walk checks for `mlkemMultiLib` blocks `5..6`
(`generate_keypair_compressed` and `kyber_decapsulate`, 84,364 B total).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks1

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

@[expose] def mlkemShard1 : List Nat := [5, 6]

set_option maxRecDepth 8000000 in
private theorem c2_mlkem_shard1_walk_ok :
    (mlkemShard1.all fun j =>
      checkMultiBlockWalk f3TrialRxWordTree.toBytes (rLen f3TrialRxWordTree.toBytes)
        mlkemMultiLib c2MlkemMpl j) = true := by
  rfl_kernel

theorem c2_mlkem_rx_blocks_1 :
    ∀ j ∈ mlkemShard1,
      checkProgCodeSubslice f3TrialRxProg (mlkemMultiLib.blockProgram c2MlkemMpl j) = true :=
  fun j hj =>
    checkProgCodeSubslice_of_multiBlockWalk rfl rfl rfl
      (List.all_eq_true.mp c2_mlkem_shard1_walk_ok j hj)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks1

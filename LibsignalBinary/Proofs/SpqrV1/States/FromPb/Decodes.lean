/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import ProofLib.SepLogic
import ProofLib.SepLogic.WPp
public meta import Lean
public meta import ProofLib.GenDecodes
public meta import ProofLib.ProgramReflection
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
public import ProofLib.GenDecodes
public import ProofLib.VCGen

/-!
# Decode Tree & Symbol Offsets for `<spqr::v1::chunked::states::States>::from_pb`

**Checked by Lean.**

Provides the `gen_decodes` binary search tree `statesFromPbBin` for the 2,911 instructions
(`11,644` bytes) of `<spqr::v1::chunked::states::States>::from_pb`, together with symbol offsets,
`.rodata` jump-table definitions, and range-fetch tactic macros.
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Symbol name of `<spqr::v1::chunked::states::States>::from_pb` (2,911 instructions). -/
abbrev statesFromPbName : String :=
  "<spqr::v1::chunked::states::States>::from_pb"

/-- The 22-byte (11-halfword) jump table for
    `<spqr::v1::chunked::states::States>::from_pb` (base `entry + 156`, scaled by `<< 2`). -/
@[expose] def statesFromPbJumpTableBytes : List (BitVec 8) :=
  [0#8, 0#8, 237#8, 0#8, 88#8, 0#8, 134#8, 0#8, 23#8, 0#8,
   41#8, 1#8, 71#8, 1#8, 225#8, 0#8, 146#8, 1#8, 72#8, 0#8, 113#8, 1#8]

end CryptoVerification.SpqrV1.States.FromPb

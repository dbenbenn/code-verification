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
# Decode Tree & Symbol Offsets for `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20..0x5d7bc`)

**Checked by Lean.**

Instruction decode tree `statesIntoPbBin` for the 615 instructions (`2,460` bytes) of
`<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20..0x5d7bc`), together with symbol offsets,
the 22-byte `.rodata` jump table at `0x82444` (`533572`), and range-fetch tactic macros.
-/

public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Symbol name of `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20`, 615 instructions). -/
abbrev statesIntoPbName : String :=
  "<spqr::v1::chunked::states::States>::into_pb"

/-- The 22-byte (11-halfword) jump table at `0x82444` (`533572`) for
    `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20`, base `entry + 100`, scaled by `<< 2`). -/
@[expose] def statesIntoPbJumpTableBytes : List (BitVec 8) :=
  [0#8, 0#8, 199#8, 0#8, 93#8, 0#8, 152#8, 0#8, 10#8, 0#8,
   252#8, 0#8, 29#8, 1#8, 182#8, 0#8, 130#8, 1#8, 65#8, 0#8, 77#8, 1#8]

end CryptoVerification.SpqrV1.States.IntoPb

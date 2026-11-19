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
public import ProofLib.GenDecodes
public import ProofLib.VCGen

/-!
# Symbol Name & Jump-Table Definitions for `<States>::recv`

**Checked by Lean.** Symbol name and `.rodata` jump-table definitions for
`<spqr::v1::chunked::states::States>::recv`.
-/

public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Symbol name of `<spqr::v1::chunked::states::States>::recv`. -/
abbrev statesRecvName : String :=
  "<spqr::v1::chunked::states::States>::recv"

@[simp, arm64_norm]
theorem statesRecv_fnOff :
    statesRecvName = "<spqr::v1::chunked::states::States>::recv" := rfl

/-! ## `.rodata` Jump Table for `States::recv` -/

/-- The 22-byte (11-halfword) jump table for
    `<spqr::v1::chunked::states::States>::recv`. -/
@[expose] def statesRecvJumpTableBytes : List (BitVec 8) :=
  [0#8, 0#8, 169#8, 1#8, 171#8, 0#8, 21#8, 1#8, 33#8, 0#8,
   253#8, 1#8, 31#8, 2#8, 102#8, 1#8, 56#8, 3#8, 123#8, 0#8, 63#8, 2#8]

/-- Synthetic `.rodata` offset of the 22-byte jump table. -/
abbrev statesRecvJumpTableOff : Nat := 596064

/-- Read-only separation-logic assertion for the 22-byte jump table. -/
@[expose] def statesRecvJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% statesRecvJumpTableOff) ↦ᵣ statesRecvJumpTableBytes

end CryptoVerification.SpqrV1.States.Recv

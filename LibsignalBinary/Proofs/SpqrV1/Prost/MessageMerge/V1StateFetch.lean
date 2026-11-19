/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import ProofLib.GenDecodes

/-!
# Instruction Decode Tree for `V1State::merge` (`0x4e7e8..0x4f544`, 855 insns)

**Checked by Lean.** Isolated into `V1StateFetch.lean` so `gen_decodes` is cached across
`V1StateDefs.lean` and proof edits.
-/

public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

abbrev v1StateMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::V1State, &mut &[u8]>"

/-- The 11-byte jump table at `0x8240c` for `V1State::merge` (`0x4e7e8`, base `entry + 300`,
    scaled by `<< 2`, indexed by `tag - 1` for tags `1..11`). -/
@[expose] def v1StateMergeJumpTableBytes : List (BitVec 8) :=
  [0#8, 66#8, 32#8, 44#8, 9#8, 76#8, 88#8, 54#8, 112#8, 20#8, 100#8]

abbrev v1StateMergeJumpTableSym : String :=
  "spqr:.rodata.prost::encoding::message::merge::<spqr::proto::pq_ratchet::V1State, &mut &[u8]>"

/-- Read-only separation-logic assertion for the 11-byte jump table at `lsmpl.ρ v1StateMergeJumpTableSym`. -/
@[expose] def v1StateMergeJumpTablePlacedAt [LibsignalPlacement] : SepProp :=
  (lsmpl.ρ v1StateMergeJumpTableSym) ↦ᵣ v1StateMergeJumpTableBytes

end CryptoVerification.SpqrV1.Prost.MessageMerge

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import GeneratedLean.LibsignalSessionPlacedObj

/-!
# Kernel-Checked Equivalence Invariants for Sharded `LibsignalSessionPlacedObj`

Verifies that the 32-shard `placed_shards = 32` emission of `libsignalSessionBlocks` concatenates
`libsignalSessionBlocksShard0` .. `libsignalSessionBlocksShard31` and preserves the exact block
count (`624`), total machine-code byte length (`386,852`), total relocation count (`11,393`),
read-only/data symbol count (`1,248`), and exported entrypoints of the monolithic emission.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.Placed.PlacedShardsCheck

open CryptoVerification (
  libsignalSessionBlocks
  libsignalSessionBlocksShard0 libsignalSessionBlocksShard1
  libsignalSessionBlocksShard2 libsignalSessionBlocksShard3
  libsignalSessionBlocksShard4 libsignalSessionBlocksShard5
  libsignalSessionBlocksShard6 libsignalSessionBlocksShard7
  libsignalSessionBlocksShard8 libsignalSessionBlocksShard9
  libsignalSessionBlocksShard10 libsignalSessionBlocksShard11
  libsignalSessionBlocksShard12 libsignalSessionBlocksShard13
  libsignalSessionBlocksShard14 libsignalSessionBlocksShard15
  libsignalSessionBlocksShard16 libsignalSessionBlocksShard17
  libsignalSessionBlocksShard18 libsignalSessionBlocksShard19
  libsignalSessionBlocksShard20 libsignalSessionBlocksShard21
  libsignalSessionBlocksShard22 libsignalSessionBlocksShard23
  libsignalSessionBlocksShard24 libsignalSessionBlocksShard25
  libsignalSessionBlocksShard26 libsignalSessionBlocksShard27
  libsignalSessionBlocksShard28 libsignalSessionBlocksShard29
  libsignalSessionBlocksShard30 libsignalSessionBlocksShard31
  libsignalSessionData libsignalSessionLib libsignalSessionMultiLib
)

private theorem sharded_blocks_eq_flatten :
    libsignalSessionBlocks =
      [libsignalSessionBlocksShard0, libsignalSessionBlocksShard1,
       libsignalSessionBlocksShard2, libsignalSessionBlocksShard3,
       libsignalSessionBlocksShard4, libsignalSessionBlocksShard5,
       libsignalSessionBlocksShard6, libsignalSessionBlocksShard7,
       libsignalSessionBlocksShard8, libsignalSessionBlocksShard9,
       libsignalSessionBlocksShard10, libsignalSessionBlocksShard11,
       libsignalSessionBlocksShard12, libsignalSessionBlocksShard13,
       libsignalSessionBlocksShard14, libsignalSessionBlocksShard15,
       libsignalSessionBlocksShard16, libsignalSessionBlocksShard17,
       libsignalSessionBlocksShard18, libsignalSessionBlocksShard19,
       libsignalSessionBlocksShard20, libsignalSessionBlocksShard21,
       libsignalSessionBlocksShard22, libsignalSessionBlocksShard23,
       libsignalSessionBlocksShard24, libsignalSessionBlocksShard25,
       libsignalSessionBlocksShard26, libsignalSessionBlocksShard27,
       libsignalSessionBlocksShard28, libsignalSessionBlocksShard29,
       libsignalSessionBlocksShard30, libsignalSessionBlocksShard31].flatten := by
  simp [List.flatten]
  rfl

private theorem sharded_blocks_count : libsignalSessionLib.blocks.length = 624 := rfl

private theorem sharded_data_count : libsignalSessionData.length = 1248 := rfl

private theorem sharded_exports_eq :
    libsignalSessionMultiLib.exports =
      ["main", "session_message_encrypt", "session_message_decrypt_signal",
       "session_signal_message_parse"] := rfl

set_option maxHeartbeats 4000000 in
private theorem sharded_total_code_bytes :
    (libsignalSessionBlocks.map (fun b => b.code.length)).sum = 386852 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem sharded_total_relocs :
    (libsignalSessionBlocks.map (fun b => b.relocs.length)).sum = 11393 := by
  decide +kernel

end LibsignalBinary.Proofs.Placed.PlacedShardsCheck

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code -- proof-setup: allow-public-import
meta import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code

/-!
# Placed Fetch and Relaxation Pair Lemmas for `sha2::sha256::compress256`

Generates `compress256PC_rebase_fetch_0x<off>` and `compress256PC_pairStep_0xd0` across
`[0x0 → 0x1dd0]` (`1,909` words) for any `Compress256Placement` (both `--no-relax` `ADRP`+`ADD`
and `stock-lld` `NOP`+`ADR`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Fetch

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
  (Compress256Placement compress256PC compress256Lib compress256Tree
   compress256_code_eq compress256_tree_size)

section
set_option linter.literalFetch false
set_option maxRecDepth 4000000 in
gen_placed_fetches compress256PC compress256Lib compress256Tree compress256_code_eq
  compress256_tree_size via_placement Compress256Placement.pl Compress256Placement.placeable
  [0x0 → 0x1dd0]
end

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Fetch

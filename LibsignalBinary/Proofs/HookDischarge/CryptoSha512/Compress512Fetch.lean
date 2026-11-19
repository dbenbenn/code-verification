/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
meta import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code

/-!
# Placed fetch and relaxation pair lemmas for `sha2::sha512::compress512`

Generates `compress512PC_rebase_fetch_0x<off>` and `compress512PC_pairStep_0x48` across
`[0x0 → 0x25b0]` (`2,413` words), valid for every `Compress512Placement` (both `--no-relax`
`ADRP`+`ADD` and `stock-lld` `NOP`+`ADR`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Fetch

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
  (Compress512Placement compress512PC compress512Lib compress512Tree
   compress512_code_eq compress512_tree_size)

section
set_option linter.literalFetch false
set_option maxRecDepth 6000000 in
gen_placed_fetches compress512PC compress512Lib compress512Tree compress512_code_eq
  compress512_tree_size via_placement Compress512Placement.pl Compress512Placement.placeable
  [0x0 → 0x25b0]
end

end LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Fetch

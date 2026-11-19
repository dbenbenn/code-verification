/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlock -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.GenLsBlock -- proof-setup: allow-public-import
public meta import Lean

/-!
# Tree-Accelerated Per-Block Fetch & Relocation Generator for Block `427`

Provides `gen_ls_blk_427_ultra`, delegating directly to `elabGenLsBlkImpl` (with `rel_<idx>`
relocation tags and `FastDecode.elabFastPlacedFetchesForBlock`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.SpqrV1.Top.Send.UltraGen

open Lean Elab Command CryptoVerification

syntax (name := genLsBlk427UltraStx) "gen_ls_blk_427_ultra " num : command

@[command_elab genLsBlk427UltraStx]
meta def elabGenLsBlk427Ultra : CommandElab := fun stx => do
  match stx with
  | `(command| gen_ls_blk_427_ultra $idxStx:num) =>
    elabGenLsBlkImpl idxStx true s!"rel_{idxStx.getNat}" true
  | _ => throwUnsupportedSyntax

end CryptoVerification.Cli.SpqrV1.Top.Send.UltraGen

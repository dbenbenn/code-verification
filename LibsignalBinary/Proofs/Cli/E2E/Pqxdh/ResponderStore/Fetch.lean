/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import
public meta import Lean -- shake: keep
public meta import ProofLib.GenDecodes
public meta import ProofLib.ProgramReflection
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
public import ProofLib.GenDecodes
public import ProofLib.VCGen

/-!
# Instruction Fetch Elaborators for CLI Responder Store Callees

Metaprogramming helpers and fetch-decode macros for CLI PQXDH responder store subroutines.
-/

public section

/-- Resolves `<P>Cli_decode_…` in the current scope when present, falling back to `<P>_decode_…`. -/
private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

namespace CryptoVerification.E2E.Pqxdh.ResponderStore

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 0

end Fetch

end CryptoVerification.E2E.Pqxdh.ResponderStore

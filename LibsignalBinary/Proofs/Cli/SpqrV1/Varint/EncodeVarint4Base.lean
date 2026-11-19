/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Aesop.BuiltinRules
public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.Simps
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.SepLogic.WPp
import VCVio.Prelude.Core
public meta import Lean -- shake: keep

/-!
# Range Instruction-Fetch Tactic for CLI `SpqrV1.Varint`

Defines the `spqrProgAt_fetches_range_cli` tactic elaborator for discharging instruction-fetch
hypotheses across contiguous byte ranges in `CryptoVerification.SpqrV1.Varint`.
-/

public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

namespace CryptoVerification.SpqrV1.Layout.L35

open Lean Elab Command ProofLib.ProgramReflection CryptoVerification.CodeLayout

end CryptoVerification.SpqrV1.Layout.L35

namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib

open CryptoVerification.CodeLayout

open CryptoVerification.SpqrV1.Layout.L35

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end CryptoVerification.SpqrV1.Varint

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.GenPlacedOddSites
public import ProofLib.Hoare.OracleHook
public import ProofLib.Abi.Rust.Heap
public import ProofLib.GlobalAlloc
public import ProofLib.StdStartup.Top

/-!
# Transitive Import Closure Check for Placed `ProofLib`

Verifies at elaboration time that `ProofLib` and the Placed proof spine do not transitively import
`Arm64.Legacy`, `ProofLib.ObjectLoad`, `ProofLib.Library`, `ProofLib.Legacy.*`, or
`ProofLib.SepLogic.ImageData*`.
-/

namespace ProofLib.Testing.NoLegacyClosure

open Lean

private meta def isForbiddenImport (m : Name) : Bool :=
  Name.isPrefixOf `Arm64.Legacy m ||
  Name.isPrefixOf `ProofLib.ObjectLoad m ||
  Name.isPrefixOf `ProofLib.Library m ||
  Name.isPrefixOf `ProofLib.Legacy m ||
  Name.isPrefixOf `ProofLib.SepLogic.ImageData m ||
  Name.isPrefixOf `ProofLib.SepLogic.ImageDataAny m

-- Positive check: zero forbidden legacy modules in the transitive import closure of `ProofLib`.
#guard_msgs in
run_cmd do
  let env ← getEnv
  let bad := env.header.moduleNames.filter isForbiddenImport
  unless bad.isEmpty do
    throwError m!"ProofLib transitive closure unexpectedly contains legacy modules: {bad.toList}"

-- Negative check: `isForbiddenImport` rejects every legacy module prefix.
/--
error: detected forbidden legacy modules: [Arm64.Legacy,
 Arm64.Legacy.Object.LinkedImage,
 ProofLib.ObjectLoad,
 ProofLib.Library.Calls,
 ProofLib.Legacy.WPFrozen,
 ProofLib.SepLogic.ImageData]
-/
#guard_msgs in
run_cmd do
  let sample : Array Name := #[
    `Arm64,
    `ProofLib.PlacedHelpers,
    `ProofLib.SepLogic.WPFrozen,
    `Arm64.Legacy,
    `Arm64.Legacy.Object.LinkedImage,
    `ProofLib.ObjectLoad,
    `ProofLib.Library.Calls,
    `ProofLib.Legacy.WPFrozen,
    `ProofLib.SepLogic.ImageData
  ]
  let bad := sample.filter isForbiddenImport
  unless bad.isEmpty do
    throwError m!"detected forbidden legacy modules: {bad.toList}"

end ProofLib.Testing.NoLegacyClosure

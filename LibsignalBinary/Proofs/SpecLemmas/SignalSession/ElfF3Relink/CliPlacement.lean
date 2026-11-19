/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.Placed
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars

/-!
# `mallocngLib` Placement Witnesses on `f3TrialElf`

**Checked by Lean.** Proves `Placeable`, `InElf`, `DataDisjoint`, `CodeLoaded`, `CodeBlocksPermRX`,
and `dataInit` for `VerifiedLibraries.mallocngLib` on `f3TrialElf` at `f3MallocngMpl`, together
with segment-disjoint byte-patch preservation helpers for `patchElfTokensPlaced`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.CliPlacement

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open VerifiedLibraries.Mallocng.Proofs (
  mallocngMultiL mallocngMultiL_names mallocngMultiL_toMultiPlacedLib
)
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.SignalSession (
  patchRegionByte patchElfByte patchElfTokensPlaced wellFormed_patchElfByte
)
open LibsignalBinary.Heap.Fine (f3MallocngMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  CodeBlocksPermRX codeBlocksPermRX_of_codeLoaded
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture (
  f3TrialElf f3TrialElfSyms_eq
)

set_option maxRecDepth 200000

/-! ## `mallocngLib` Placement and Load Witnesses -/

set_option maxHeartbeats 2000000 in
/-- `Placeable ∧ InElf f3TrialElf ∧ DataDisjoint` for `VerifiedLibraries.mallocngLib` at
`f3MallocngMpl`. -/
theorem mallocngLib_in_f3TrialElf :
    VerifiedLibraries.mallocngLib.Placeable f3MallocngMpl ∧
    VerifiedLibraries.mallocngLib.InElf f3TrialElf f3MallocngMpl ∧
    VerifiedLibraries.mallocngLib.DataDisjoint f3MallocngMpl := by
  rw [← mallocngMultiL_toMultiPlacedLib]
  exact Obj.Interned.checkMultiDisjoint_spec mallocngMultiL_names f3TrialElfSyms_eq
    (by decide +kernel)

/-! ## Segment-Disjoint `patchElfByte` Preservation -/

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.CliPlacement

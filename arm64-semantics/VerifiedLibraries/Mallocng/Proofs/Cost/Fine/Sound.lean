/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Footprint
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Entries

/-!
# Soundness of the Per-Size-Class Fine Cost Model (`…Proofs.Cost.Fine.Sound`)

- **Layer & Role**: `Role::Proof` (untrusted). A plain (non-`module`) file because it imports the
  non-`module` `Cost/Fine/Entries.lean`.
- **Contents**: Proves `mallocngFineSound : MallocngCostModelSound mallocngFineCostModel
  mallocngFineIface`, combining startup/footprint facts from `Footprint.lean`, block token facts
  from `Inv.lean`, and all six placed entry contracts from `Entries.lean`.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 Arm64.Obj ProofLib VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-- Target soundness statement for the per-size-class `mallocngFineCostModel`. -/
def MallocngFineSoundStmt : Prop :=
  MallocngCostModelSound mallocngFineCostModel mallocngFineIface

/-- End-to-end soundness of `mallocngFineCostModel` with `mallocngFineIface` for the compiled
    `mallocngLib` binary. -/
theorem mallocngFineSound : MallocngCostModelSound mallocngFineCostModel mallocngFineIface where
  init := finePlacedInit_ok
  init_resources := fineHeap_init_resources
  heap_split_runtime := fineHeap_split_runtime
  block_nonnull γ p n a := fineBlock_wf γ p n a
  block_exclusive γ p₁ n₁ a₁ p₂ n₂ a₂ := fineBlock_exclusive γ p₁ n₁ a₁ p₂ n₂ a₂
  heap_footprint_bound := fineHeap_footprint_bound
  entries_ok := mallocngFinePlacedEntries

/-- End-to-end soundness of `mallocngFineCostModel` with `mallocngFineRoIface` (duplicable `.ro`
    `auxv`) for the compiled `mallocngLib` binary. -/
theorem mallocngFineRoSound : MallocngCostModelSound mallocngFineCostModel mallocngFineRoIface where
  init := finePlacedRoInit_ok
  init_resources := fineHeapRo_init_resources
  heap_split_runtime := fineHeapRo_split_runtime
  block_nonnull γ p n a := fineBlock_wf γ p n a
  block_exclusive γ p₁ n₁ a₁ p₂ n₂ a₂ := fineBlock_exclusive γ p₁ n₁ a₁ p₂ n₂ a₂
  heap_footprint_bound := fineHeapRo_footprint_bound
  entries_ok := mallocngFineRoPlacedEntries

/-- Alias for `mallocngFineRoSound`. -/
theorem mallocngFineRoTop_ok : MallocngCostModelSound mallocngFineCostModel mallocngFineRoIface :=
  mallocngFineRoSound

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine

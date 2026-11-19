/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Tables
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Model
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Inv
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Envelope
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Footprint
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Entries
import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Sound

/-!
# Per-Size-Class `mallocng` Cost Model Umbrella (`VerifiedLibraries.Mallocng.Proofs.Cost.Fine`)

- **Layer & Role**: `Role::Proof` (untrusted). Re-exports the per-size-class cost model
  (`mallocngFineCostModel`, `FineBudget`, `fineLawful`), stride-sum envelope lemmas
  (`fine_footprint_le_of_nomStrideSum`), representation (`mallocngFineIface`, `fineInitCore_tracked`,
  `fineCore_teardown_auxv`), placed entry contracts (`mallocngFinePlacedEntries`), and end-to-end
  soundness theorem (`mallocngFineSound : MallocngCostModelSound mallocngFineCostModel
  mallocngFineIface`).
-/

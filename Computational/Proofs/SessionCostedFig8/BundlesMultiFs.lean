/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBounded -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFBounded -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsSim -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFSim -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsQueries -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFQueries -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsShort -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFShort -- proof-setup: allow-public-import

/-!
# Multi-session atomic FS-AEAD compiler facade (`BundlesMultiFs`)

Re-exports `BundlesMultiFsBase` and the eight `N07`/`N08` proof shards.-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BundlesMultiFs

public section

export Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase (
  compileFsMultiAtomic compileFsMultiDFAtomic fsMultiQueryC fsMultiQueryS fsMultiQueryS_apply
)
export Computational.Proofs.SessionCostedFig8.BundlesMultiFsBounded (
  compileFsMultiAtomic_gRedBounded
)
export Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFBounded (
  compileFsMultiDFAtomic_gRedBounded
)
export Computational.Proofs.SessionCostedFig8.BundlesMultiFsSim (
  compileFsMultiAtomic_coinSimEquiv compileFsMultiAtomic_routerAdvCompat
)
export Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFSim (
  compileFsMultiDFAtomic_coinSimEquiv compileFsMultiDFAtomic_routerAdvCompat
)
export Computational.Proofs.SessionCostedFig8.BundlesMultiFsQueries (
  compileFsMultiAtomic_isQueryBoundP compileFsMultiAtomic_makesAtMostQueries
)
export Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFQueries (
  compileFsMultiDFAtomic_isQueryBoundP compileFsMultiDFAtomic_makesAtMostQueries
)
export Computational.Proofs.SessionCostedFig8.BundlesMultiFsShort (
  compileFsMultiAtomic_encMsgsOk compileFsMultiAtomic_guardedFSInjectShort
)
export Computational.Proofs.SessionCostedFig8.BundlesMultiFsDFShort (
  compileFsMultiDFAtomic_encMsgsOk compileFsMultiDFAtomic_guardedFSInjectShort
)

end

end Computational.Proofs.SessionCostedFig8.BundlesMultiFs

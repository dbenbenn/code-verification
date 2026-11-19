/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.AuthDefs
import Computational.Proofs.SignalPqxdh.Delta.KeyInd.CorrAt
import VCVio.EvalDist.Monad.Basic

/-!
# PQXDH δ Authentication: Per-Index KEM Correctness Reduction

**Checked by Lean.** Proves `authCorrAt` (`AuthCorrAtStmt`, DEV-PQ21) by instantiating
`badKemCorrProbGenericAt_le_kemCorr` with `shcrChoosePkAuthAt`.
-/

public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

end Proofs.SignalPqxdh.Security.PqxdhDelta

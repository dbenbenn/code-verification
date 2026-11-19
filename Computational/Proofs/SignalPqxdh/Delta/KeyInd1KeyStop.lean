/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyDefs
import Computational.Proofs.SignalPqxdh.Delta.KeyInd.Stop

/-!
# One-Key PQXDH δ Key Indistinguishability: Stop Disjunction and Store Invariance

**Checked by Lean.** Proves `KI1KeyStopStmt` (DEV-CLI16, DEV-PQ21) from `kiStop` and shows that
single-scalar `.initPrin` in `pqxdhKeyIndImpl1KeyRo` preserves `ValidKeyStores`.
-/

public section

set_option autoImplicit false

open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.RoKem
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

theorem ki1KeyStop (S : Setup) : KI1KeyStopStmt S :=
  kiStop S

end Proofs.SignalPqxdh.Security.PqxdhDelta

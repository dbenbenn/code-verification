/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhEvalEq
public import Computational.Proofs.SignalPqxdh.CostedTablesCompat -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsBase

/-!
# Cost and Query Bounds for the `ReductionDsl` `KeyInd` `GapDH` Adversary

Packages `fgKeyIndGapDhProg` as a bounded `GapDhAdv` (`fgKeyIndGapDhAdv4GenAdv`) and proves its
`GapDH` advantage equals that of the shallow reduction `fgKeyIndGapDhAdv4`.
-/

public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd

/-- The `ReductionDsl` `KeyInd` `GapDH` adversary with semantic DDH and primitive query budgets. -/
@[expose] def fgKeyIndGapDhAdv4GenAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhAdv where
  run U V := (fgKeyIndGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)
  q_ddh := gdhQueryBudget S b
  q_prim := primQueryBudget S b

theorem fgKeyIndGapDhAdv4GenAdv_q_ddh_le (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (fgKeyIndGapDhAdv4GenAdv S b A).q_ddh ≤ gdhQueryBudget S b :=
  le_rfl

end SignalPqxdh.Security.ReductionDsl.KeyIndGapDh

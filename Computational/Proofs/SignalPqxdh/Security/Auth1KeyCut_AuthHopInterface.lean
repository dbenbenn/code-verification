/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthPrf
import Computational.Proofs.SignalPqxdh.Security.CollisionsA
import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
public import VCVio.CryptoFoundations.SecExp.Measure
public import VCVio.EvalDist.Monad.Basic
import Computational.Proofs.SignalPqxdh.Security.AuthHopInterface
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-Key `Auth` KOSK Stage Advantage

Real-valued boolean bias advantage `authKoskAdvAtStage1Key` at a one-key `Auth` hybrid stage and
its equality with `authFixedAdvAtStage1Key` when `stage.idealMsgKeys = false`.
-/

public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

@[expose] noncomputable def authKoskAdvAtStage1Key (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ℝ :=
  (𝒟[authKoskExpAtStage1Key stage S P A].boolBias).toReal

theorem authFixedAdvAtStage_eq_authKoskAdvAtStage1Key (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (A : AuthAdversary S)
    (hStage : stage.idealMsgKeys = false := by rfl) :
    authFixedAdvAtStage1Key stage S P A = authKoskAdvAtStage1Key stage S P A := by
  unfold authFixedAdvAtStage1Key authKoskAdvAtStage1Key
  rw [authFixedExpAtStage_eq_authKoskExpAtStage1Key stage S P A hStage]

end SignalPqxdh.Security

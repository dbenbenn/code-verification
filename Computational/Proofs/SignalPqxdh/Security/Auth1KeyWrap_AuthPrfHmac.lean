/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHA2
import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHB
import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHC
import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHD
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1
import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmac
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthPrfHmacHA2
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B2
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5C1
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M1
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs
import Computational.Proofs.GameHop.Advantage
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
import Computational.Proofs.SignalPqxdh.Security.FgGapDhA
import Computational.Proofs.SignalPqxdh.Security.FgGapDhB
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import Computational.Proofs.SignalPqxdh.Security.RoKemHopA

/-!
# One-Key Multi-Key INT-CTXT to PRF-HMAC Bound

Bounds the multi-key AEAD INT-CTXT advantage of `aeadMuIntReductionAuth1Key` by `PrfHmacReal`
over the single-identity-key `Auth` oracle `pqxdhAuthImpl1KeyG`.
-/

public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

theorem aeadMuIntCtxt_le_prfHmac_of_pow8BaseLen1Key (S : Setup) (P : Primitives)
    (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    AeadMuIntCtxt P (aeadMuIntReductionAuth1Key S b A) ≤
      (S.N_sess_tot : ℝ) * PrfHmacReal P (prfHmacReductionAuth1Key S b A) +
        (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 64 :=
  aeadMuIntCtxt_le_prfHmacOfMu_of_disciplined' P hP _ (aeadMuIntReductionAuth_bounded1Key S b A)
    goodFirstMsgAD macAdGood_goodFirstMsgAD (fun _ h => h)
    (aeadMuIntReductionAuth_disciplined1Key S P hP hLaw b A)

/-- Multi-key AEAD INT-CTXT advantage bound via `PrfHmacReal` for the one-key `Auth` reduction. -/
theorem aeadMuIntCtxt_le_prfHmac1Key (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    AeadMuIntCtxt P (aeadMuIntReductionAuth1Key S b A) ≤
      2 * (S.N_sess_tot : ℝ) * PrfHmacReal P (prfHmacReductionAuth1Key S b A) +
        (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 64 := by
  have hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32 := hP.pow8_base_len
  have h := aeadMuIntCtxt_le_prfHmac_of_pow8BaseLen1Key S P hP.toWellFormedPrimitivesδ hLaw b A
  have h0 : 0 ≤ PrfHmacReal P (prfHmacReductionAuth1Key S b A) := ENNReal.toReal_nonneg
  have hN : (0 : ℝ) ≤ S.N_sess_tot := Nat.cast_nonneg _
  nlinarith [mul_nonneg hN h0]

end SignalPqxdh.Security

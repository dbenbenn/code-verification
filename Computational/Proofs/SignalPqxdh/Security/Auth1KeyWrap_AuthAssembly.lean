/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M3d
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5D
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC5
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6b
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1
import Computational.Proofs.SignalPqxdh.Security.Reductions
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c5
import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmac
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import Computational.Proofs.SignalPqxdh.Security.AuthAssembly
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHop
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopA
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopB1
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopB2
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopB3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthPrfHmac
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthPrfHmacHA2
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3B
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3D
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3E
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3F
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3G
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3G2
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3G3
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H1
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H2
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3H3
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B2
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B3
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5C
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5D -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M1 -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M2
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M3a
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M3d -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_ReductionsAuthHandshake
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims -- proof-setup: allow-public-import

/-!
# One-Key `Auth` `G3.8 → G5` Bundle

Assembles `AuthSubHops4to5Bundle1Key` over `pqxdhAuthImpl1KeyG` from the multi-key AEAD ciphertext
integrity reduction `aeadMuIntReductionAuth1Key` and `auth_hop_G3_8_split_g5_boolBias_le_mu1Key`.
-/

public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.AuthSubHops1to3
open OracleSpec OracleComp
open scoped ENNReal

namespace Proofs.SignalPqxdh.Security

@[expose] def authSubHops4to5Bundle1Key (S : Setup) : AuthSubHops4to5Bundle1Key S :=
  authSubHops4to5Bundle_of_int1Key S
    (aeadMuIntReductionAuth1Key S)
    (aeadMuIntReductionAuth_queries1Key S)
    (aeadMuIntReductionAuth_enc_queries1Key S)
    (aeadMuIntReductionAuth_prim_queries1Key S)
    (auth_hop_G3_8_split_g5_boolBias_le_mu1Key S)

end Proofs.SignalPqxdh.Security

namespace SignalPqxdh.Security

end SignalPqxdh.Security

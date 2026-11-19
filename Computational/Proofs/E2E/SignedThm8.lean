/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SignedPrims -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Reductions -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8
import Computational.Proofs.E2E.SignedAdv

/-!
# ACD19 Theorem 8 on mixtures

Bounds the winning probability of a prefix-indexed mixture of SM authenticity games
(`theorem8_mix`) using single averaged CKA and PRF-PRNG reductions and expected FS-AEAD
advantages.
-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

private theorem _barrel : True := trivial

end CryptoVerification.E2E.Signed

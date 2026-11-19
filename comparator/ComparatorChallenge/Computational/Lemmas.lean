/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Composition.StatementModel
public import Computational.Specifications.LibsignalCli.Kyber1024Delta

/-!
# Comparator challenge: Lemmas 1–3 and Kyber-1024 `δ_kem` (`Computational/Theorems/Lemmas.lean`)

**Trusted: the statements.** Each theorem below (`headlineδ`, `session_secure`,
`model_secure_costed`, and `kyber1024_kem_delta_correct`, paired with
`Computational/Theorems/Lemmas.lean` and `comparator/computational.json`) has the exact target
statement with `sorry` as its proof. It imports only specification modules (no proof module).
`leanprover/comparator` (`comparator/README.md`) checks that the solution's theorems have these
exact statements (and that every constant they use is the same), that their proofs use only the
permitted axioms, and replays the solution in the Lean kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

theorem headlineδ : PqxdhCorrectAndSecureδ :=
  sorry

end SignalPqxdh.Security

namespace CryptoVerification.E2E

theorem session_secure {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) : SessionSecure (Pt := Pt) ℓ :=
  sorry

theorem model_secure_costed {Pt : Type}
    (S : SignalPqxdh.Setup) (ℓ : ℕ) : ModelSecure (Pt := Pt) S ℓ :=
  sorry

theorem kyber1024_kem_delta_correct : Kyber1024KemDeltaCorrect :=
  sorry

end CryptoVerification.E2E

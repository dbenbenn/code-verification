/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthStatements -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.SignalPqxdh.Assumptions -- proof-setup: allow-public-import
public import Computational.Specifications.Pqxdh.Bound

public section

set_option autoImplicit false

/-!
# Exact-correctness PQXDH headline definitions and assembly

**Checked by Lean.** Auxiliary exact-correctness (`δ = 0`) PQXDH key-indistinguishability and
authentication propositions, costed reduction bundles, and assembly helper accompanying
`Computational/Specifications/Pqxdh/Security/Headline.lean`.
-/

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.ReductionDsl (Ty CostedReduction TwoStageCostedReduction Mid)
open SignalPqxdh.Costed

abbrev KeyIndCostedReductionFamily.toSimulators {S : Setup} (R : KeyIndCostedReductionFamily S) : KeyIndReductionFamily S :=
  R.eval

abbrev KeyInd2KeyCostedReductionFamily.toSimulators {S : Setup} (R : KeyInd2KeyCostedReductionFamily S) : KeyInd2KeyReductionFamily S :=
  R.eval

abbrev AuthCostedReductionFamily.toSimulators {S : Setup} (R : AuthCostedReductionFamily S) : AuthReductionFamily S :=
  R.eval

/-- Two-key PQXDH key-indistinguishability advantage bound for reduction family `R`. -/
@[expose] def PqxdhKeyIndStatementWith (S : Setup) (R : KeyInd2KeyReductionFamily S) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitives P →
    ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      KeyIndAdvantage S P A.1 ≤
        pqxdhKeyIndBoundReal S
          (SigEufCma P (R.sig b A))
          (KemShCrReal P (R.shcr b A))
          (GapDH P P.isValidDhTriple P.pow8 (R.gdh b A))

/-- PQXDH authentication and first-message privacy advantage bound for reduction family `R`. -/
@[expose] def PqxdhAuthStatementWith (S : Setup) (R : AuthReductionFamily S) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitives P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      AuthAdvantageReal S P A.1 ≤
        pqxdhAuthBoundReal S b.q_roRoot
          (SigEufCma P (R.sig b A))
          (KemShCrReal P (R.shcr b A))
          (GapDH P P.isValidDhTriple P.pow8 (R.gdh b A))
          (PrfChainKeyReal P (R.ck b A))
          (PrfMsgKeysReal P (R.mk b A))
          (AeadIndCpaReal P (R.cpa b A))
          (PrfHmacReal P (R.int b A))

/-- Existence of a costed 2-key key-indistinguishability reduction family at setup `S`. -/
@[expose] def PqxdhKeyIndStatement (S : Setup) : Prop :=
  ∃ R : KeyInd2KeyCostedReductionFamily S,
    KeyInd2KeyCostedReductionBounds S R ∧
    KeyInd2KeyReductionQueryBounds S R.eval ∧
    PqxdhKeyIndStatementWith S R.eval

/-- Existence of a costed authentication reduction family at setup `S`. -/
@[expose] def PqxdhAuthStatement (S : Setup) : Prop :=
  ∃ R : AuthCostedReductionFamily S,
    AuthCostedReductionBounds S R ∧
    AuthReductionQueryBounds S R.eval ∧
    PqxdhAuthStatementWith S R.eval

/-- Two-key key indistinguishability and authentication at setup `S`. -/
@[expose] def PqxdhSecurityStatement (S : Setup) : Prop :=
  PqxdhKeyIndStatement S ∧
  PqxdhAuthStatement S

def PqxdhSecurity : Prop :=
  ∀ (S : Setup), PqxdhSecurityStatement S

/-- Combined costed reduction bundle for 2-key `KeyInd` and `Auth` at setup `S`. -/
structure PqxdhReds (S : Setup) where
  keyInd : KeyInd2KeyCostedReductionFamily S
  auth   : AuthCostedReductionFamily S

/-- Cost, block-size, and semantic query bounds for `PqxdhReds S`. -/
structure PqxdhBounds (S : Setup) (R : PqxdhReds S) : Prop where
  keyInd_costed : KeyInd2KeyCostedReductionBounds S R.keyInd
  keyInd_sim    : KeyInd2KeyReductionQueryBounds S R.keyInd.eval
  auth_costed   : AuthCostedReductionBounds S R.auth
  auth_sim      : AuthReductionQueryBounds S R.auth.eval

/-- Combined PQXDH protocol correctness and costed computational security across all setups. -/
@[expose] def SignalPqxdhSecurityCosted : Prop :=
  (∀ (P : Primitives), WellFormedPrimitives P → PqxdhCorrect P) ∧
  ∀ (S : Setup), ∃ R : PqxdhReds S,
    PqxdhBounds S R ∧
    PqxdhKeyIndStatementWith S R.keyInd.eval ∧
    PqxdhAuthStatementWith S R.auth.eval

/-- Exact-correctness PQXDH correctness and computational security across all primitives and setups. -/
@[expose] def Headline : Prop :=
  ∀ (P : Primitives) (S : Setup),
    (WellFormedPrimitives P → PqxdhCorrect P) ∧
    PqxdhSecurityStatement S

theorem headline_of_security (hSec : ∀ (S : Setup), PqxdhSecurityStatement S) :
    Headline :=
  fun P S => ⟨wellFormed_pqxdhCorrect P, hSec S⟩

end SignalPqxdh.Security

namespace SignalPqxdh

export Security (
  PqxdhKeyIndStatementWith PqxdhAuthStatementWith PqxdhKeyIndStatement PqxdhAuthStatement
  PqxdhSecurityStatement PqxdhSecurity PqxdhReds PqxdhBounds SignalPqxdhSecurityCosted
  headline_of_security
)

end SignalPqxdh

namespace SignalPqxdh.Costed

export SignalPqxdh.Security (
  PqxdhKeyIndStatementWith PqxdhKeyIndStatement PqxdhAuthStatementWith PqxdhAuthStatement
  PqxdhSecurityStatement PqxdhSecurity PqxdhReds PqxdhBounds SignalPqxdhSecurityCosted Headline
  headline_of_security
)

end SignalPqxdh.Costed

namespace SignalPqxdh.Security.Costed

export SignalPqxdh.Security (
  PqxdhKeyIndStatementWith PqxdhKeyIndStatement PqxdhAuthStatementWith PqxdhAuthStatement
  PqxdhSecurityStatement PqxdhSecurity PqxdhReds PqxdhBounds SignalPqxdhSecurityCosted Headline
  headline_of_security
)

end SignalPqxdh.Security.Costed

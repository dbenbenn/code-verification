/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ExternInterpretationProofDefs

/-!
# CLI extern-contract satisfiability predicates

Defines `CompExternsSatisfiableCli` and `RealAes256ContractsSatisfiable`, asserting the joint
satisfiability of `ExternInterpretationTotalOnUsedSymbols`, `ExternContractsHoldCli`, and
`HooksMatchInterpretation` / `HooksMatchPlaced` (with `W.C.E = aes256Enc` and `W.C.D = aes256Dec`).
-/

public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SignalSession (CliHooks)

/-- Joint satisfiability of extern totality, CLI extern contracts, and hook agreement. -/
@[expose] def CompExternsSatisfiableCli : Prop :=
  ∃ (interp : ExternInterpretation) (W : CliHooks),
    ExternInterpretationTotalOnUsedSymbols interp ∧ ExternContractsHoldCli interp ∧ HooksMatchInterpretation interp W

/-- Joint satisfiability of extern totality, CLI extern contracts, and placed hook agreement
(`HooksMatchPlaced`, pinning `W.C.E = CryptoGames.AES256.aes256Enc` and
`W.C.D = CryptoGames.AES256.aes256Dec`), witnessing that the universal `(interp, W)` hypotheses of
`CompRefinesCliBinary` and `SignalSessionSecure` are non-vacuous. -/
@[expose] def RealAes256ContractsSatisfiable : Prop :=
  ∃ (interp : ExternInterpretation) (W : CliHooks),
    ExternInterpretationTotalOnUsedSymbols interp ∧ ExternContractsHoldCli interp ∧ HooksMatchPlaced interp W

end DY.Libsignal.Composed.Refinement.Cli

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ElfBindingProofDefs
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ExternWitness

/-!
# Satisfiability of the Cryptographic Extern Contracts

Witnesses `CompExternsSatisfiableCli` and `RealAes256ContractsSatisfiable`: there exist an extern
interpretation `interp` and CLI hooks `W` satisfying `ExternInterpretationTotalOnUsedSymbols`,
`ExternContractsHoldCli`, and `HooksMatchPlaced` (`HooksMatchInterpretation` with
`W.C.E = CryptoGames.AES256.aes256Enc` and `W.C.D = CryptoGames.AES256.aes256Dec`), showing that
the universal `(interp, W)` hypotheses of `comp_refines_cli_placed` and `signal_session_secure_placed`
are non-vacuous.
-/

@[expose] public section

set_option autoImplicit false

namespace Proven.ExternWitness

open DY.Libsignal.Composed.Refinement.Cli (CompExternsSatisfiableCli RealAes256ContractsSatisfiable)

/-- Joint satisfiability of `ExternInterpretationTotalOnUsedSymbols`, `ExternContractsHoldCli`,
and `HooksMatchInterpretation`. -/
theorem comp_externsSatisfiable_cli : CompExternsSatisfiableCli :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.comp_externsSatisfiable_cli_proof

/-- Joint satisfiability of `ExternInterpretationTotalOnUsedSymbols`, `ExternContractsHoldCli`,
and `HooksMatchPlaced` (`W.C.E = aes256Enc`, `W.C.D = aes256Dec`). -/
theorem realAes256ContractsSatisfiable_cli : RealAes256ContractsSatisfiable :=
  Symbolic.Proofs.TopLevelHelpers.Composed.Cli.realAes256ContractsSatisfiable_cli_proof

end Proven.ExternWitness

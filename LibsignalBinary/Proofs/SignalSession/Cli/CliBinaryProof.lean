/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryTokenPatch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfFrozen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.Support.ImageWitness -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.MuslHarnessOk

public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Whole-Binary CLI Stack Budget Bound

Proves that `cliMainStk` fits within musl startup's `cliStackBudget`.
-/

namespace CryptoVerification.SignalSession

open CryptoVerification.SignalSession.InitStack CryptoVerification.SignalSession.MuslElf

/-- `cliMainStk` fits within musl startup's `cliStackBudget` (`8,371,792 ≤ 8,371,792`). -/
theorem cliMainStk_le_stackBudget : Cli.MainHops.cliMainStk ≤ cliStackBudget := by
  have := cliStackSize_eq; unfold Cli.MainHops.cliMainStk cliStackBudget cliArgBudget; omega

end CryptoVerification.SignalSession

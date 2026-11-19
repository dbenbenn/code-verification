/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Entries
public import ProofLib.SpecAudit

/-!
# SPQR V1: spec audit of store and extern-stub contracts

**Checked by Lean; not trusted, imported by nothing.** Runs `#spec_nonvacuous!` and `#spec_lint!`
(`ProofLib.SpecAudit`) on `loadSessionSpecPqStateLengthBound` (`Entries.lean`) and on each
extern-stub contract in `SpqrHooks` (`Hooks.lean`).
-/

@[expose] public section

namespace CryptoVerification.SpecAudit.SpqrV1

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1

/-! ## Store contract (`Entries.lean`) -/

#spec_nonvacuous! loadSessionSpecPqStateLengthBound
#spec_lint! loadSessionSpecPqStateLengthBound

/-! ## Extern-stub contracts (`SpqrHooks`) -/

#spec_nonvacuous! mlkemFromSeedSpec
#spec_nonvacuous! mlkemPk1Spec
#spec_nonvacuous! mlkemPk2Spec
#spec_nonvacuous! mlkemEncaps1Spec
#spec_nonvacuous! mlkemEncaps2Spec
#spec_nonvacuous! mlkemDecapsSpec
#spec_nonvacuous! mlkemValidatePkSpec
#spec_nonvacuous! libcruxHmacSpec

#spec_lint! mlkemFromSeedSpec
#spec_lint! mlkemPk1Spec
#spec_lint! mlkemPk2Spec
#spec_lint! mlkemEncaps1Spec
#spec_lint! mlkemEncaps2Spec
#spec_lint! mlkemDecapsSpec
#spec_lint! mlkemValidatePkSpec
#spec_lint! libcruxHmacSpec

end CryptoVerification.SpecAudit.SpqrV1

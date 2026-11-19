/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1CommonExtCallees -- shake: keep

/-!
# Contract-Backed 4-Byte RNG Bridge and Initiator Callee Re-Exports (`tripleRatchetProgAtExt`)

Proves `sp2Rng4_ok_at_ext` on `tripleRatchetProgAtExt` and re-exports
`InitializeAliceStage1CommonExtA`, `InitializeAliceStage1CommonExtB`, and
`InitializeAliceStage1CommonExtCallees`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.E2E.Pqxdh.Initiator
open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (rngFillAfter0Spec)
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.ResponderCore

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
end CryptoVerification.E2E.Pqxdh.Initiator

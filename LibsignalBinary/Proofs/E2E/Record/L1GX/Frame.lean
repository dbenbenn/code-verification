/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import LibsignalBinary.Proofs.CodeLayout

/-!
# Framing `DeserializeGeneral` `merge_field` leaves into PQXDH scope

Lifts `DeserializeGeneral` `merge_field` contracts (`mergeFieldGenSpec`) to `.base` fields in
`mergeFieldXSpec` when the PQXDH extension fields are at their empty defaults, together with
predicate-weakening and disjunction combinators for `MergeFieldXOk`.
-/

public section

namespace CryptoVerification.E2E.Record.L1GX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

/-- Projects `MergeFieldXGhost` to `MergeFieldGenGhost` on its base `SSG` state. -/
def MergeFieldXGhost.toGen (x : MergeFieldXGhost) (f : GenField) : MergeFieldGenGhost :=
  ⟨x.ss, x.v.base, f, x.bufRef, x.slot, x.ptr, x.tail⟩

end CryptoVerification.E2E.Record.L1GX

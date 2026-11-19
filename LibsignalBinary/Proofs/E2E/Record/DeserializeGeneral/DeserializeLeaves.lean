/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserLoopEntryG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserLoopExitG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserReprG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ProstSSGAtMove
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ProstSSGRepr

/-!
# Segment and Representation Leaf Theorems for General `SessionRecord::deserialize`

Exports the loop-entry, loop-iteration, loop-exit, 344-byte `SessionStructure` relocation, and
representation conversion theorems composed in `Root.lean`.
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)

/-- Relocates `prostSSGAt A src v` across a 344-byte `memcpy` to `dst`, establishing that word `0`
(`lik` capacity) avoids the `None` niche. -/
theorem prostSSGAt_move (A : RustAlloc) (a : BitVec 64) (v : SSG) :
    prostSSGAt A a v ⊢
      ∃∗ w0 : BitVec 64, ∃∗ rest : List (BitVec 8), ∃∗ H : SepProp,
        ⌜w0 ≠ noneCap ∧ rest.length = 336 ∧
          ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢ prostSSGAt A b v⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ rest) ∗ H := by
  exact Leaf.ProstSSGAtMove.prostSSGAt_move A a v

/-- Converts `prostSSGAt A ss (ssgOf s)` for an in-scope session `s` into `sessionStateReprAt` with
a canonical ghost (`CanonSession`). -/
theorem prostSSG_repr (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) (ss : BitVec 64) :
    prostSSGAt A0 ss (ssgOf s) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G s⌝ ∗ sessionStateReprAt A0 ss G s := by
  exact Leaf.ProstSSGRepr.prostSSG_repr_impl r hr s hs ss

/-- Converts the raw `deserOutRecordG` layout at `out` into `sessionRecordAt` holding `r` with
`CanonRecord`. -/
theorem deserReprG_ok (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r) (out : BitVec 64) :
    deserOutRecordG out r ⊢
      ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r := by
  exact Leaf.DeserReprG.deserReprG_ok r hr out (prostSSG_repr r hr)

end CryptoVerification.E2E.Record.DeserializeGeneral

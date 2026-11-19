/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.RecordJoin
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.RecordSplit
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegDispatch
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegErrTeardown
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegLoad
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegPostNone
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegPostSome
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegRegionNone
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegRegionSome
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSave
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegStore
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegTrust
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegWrite
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

/-!
# `MessageDecrypt` Segment Proofs and Bundles

Exports the twelve store-kit-parameterized segment proofs (`segLoadV_ok` through `segWriteV_ok`),
the `recordSplit_ok` and `recordJoin_ok` separation-logic bridges, and the relocatable
`[LibsignalPlacement]` segment bundle `DecSegsVPlaced` (`decSegsV_placed_ok`).
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

/-- Pure separation-logic bridge splitting a loaded `SessionRecord` with a current session into its `previous_sessions` header and `sessionStateAt`. -/
theorem recordSplit_ok : RecordSplit := by
  exact Pf.RecordSplit.recordSplit_ok

/-- Pure separation-logic bridge reassembling `sessionRecordAt` after `AfterRecordDecrypt G G'` with cleared pending pre-key fields. -/
theorem recordJoin_ok : RecordJoin := by
  exact Pf.RecordJoin.recordJoin_ok

/-! ## Relocatable `[LibsignalPlacement]` Segments & Bundle -/

section Placed

open CryptoVerification CryptoVerification.LibsignalPublicApi.Placed

theorem recordSplit_placed_ok [LibsignalPlacement] : RecordSplit :=
  Pf.RecordSplit.recordSplit_placed_ok

theorem recordJoin_placed_ok [LibsignalPlacement] : RecordJoin :=
  Pf.RecordJoin.recordJoin_placed_ok

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt

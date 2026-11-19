/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefs
import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegLoad
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegPostNone
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegRegionSome
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegWrite
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# Ext-Generic `MessageDecrypt` Segments: `SegLoad`, `SegPostNone`, `SegRegionSome`, and `SegWrite`

Proves `segLoadVX_ok_ext` (`+0x0 → +0x8c`), `segPostNoneVX_ok_ext` (`+0x1f50 → +0x22a8`),
`segRegionSomeV_ok_ext` (`+0x1a8 → +0x1f50`), and `segWriteVX_ok_ext` (`+0x24d4 → ret`) over
`tripleRatchetProgAtExt img.base ext`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Monotonicity in `Extra` and shared panic helpers -/

section SegLoadExt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad

end SegLoadExt

/-! ## `segPostNoneVX_ok_ext` (`+0x1f50 → +0x22a8`) -/

section SegPostNoneExt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone

end SegPostNoneExt

/-! ## `segRegionSomeV_ok_ext` (`+0x1a8 → +0x1f50`) -/

section SegRegionSomeExt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome

end SegRegionSomeExt

/-! ## `segWriteVX_ok_ext` (`+0x24d4 → ret`) -/

section SegWriteExt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegWrite

end SegWriteExt

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

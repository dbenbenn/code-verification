/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShims.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.CallSpecs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

public section

set_option autoImplicit false

/-!
# PQ `IdentityFiles` Shims and Future-Drop Stub

Proves the `futDrop` 1-instruction stub and the 16-byte boxed future shims for
`get_identity_key_pair` and `get_local_registration_id` on `initProg img W`.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Store.PkShims.Helpers

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `futDrop` at `initProg img W` (`1`-instruction `ret`) -/

theorem memRegion_16_ownBox (p : BitVec 64) :
    memRegion p 16 =
      (∃∗ b0 : BitVec 8, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₈ b0) ∗ memRegion (p + 9#64) 7) := by
  rw [memRegion_split p 8 8 (by decide),
    memRegion_split (p + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInner -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Inner Store-Kit Contract Instantiation for `encrypt`

Discharges the inner `withStoresEncSpecVT_cli` obligation of `cliEncrypt_slot_of_inner` by
combining `withStores_okVT_fs_cli`, the session and identity store-kit contracts, and the
`scopeIn` / `scopeKit` record invariants to establish `cliEncrypt_slot`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

private theorem spqrV1_eq_spqrV1W (W : CliHooks) :
    CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K = pqxdhSpqrModel ⟨W.C, W.Q⟩ :=
  rfl

end CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas

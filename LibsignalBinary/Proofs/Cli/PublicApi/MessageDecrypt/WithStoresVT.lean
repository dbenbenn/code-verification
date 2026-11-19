/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.Core -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOk -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOk -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCli
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Tight-Panic Token-Framed CLI `decrypt_signal` (`WithStoresVT`)

Specializes `WithStoresVT.Core` (`withStoresDecSpecVTP` and `withStoresDecSpecVT`, framing
`TokenInit img` under `RecordInScopeP` and `IdOrDistinctSid`) to `trTrapProgAt`, concrete CLI
externs (`cliExterns W`), and parametric contract-backed externs (`cliExternsWith ext`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib ProofLib.Variant CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (ScopePq decryptRecord)

open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

/-- Lifts an unconditional `region_ok` proof to `spec.restrictPre (fun _ => True)`. -/
theorem region_ok_restrictPre_true {α : Type} {P : Program} {entry exit : BitVec 64}
    {spec : Spec α} (h : region_ok P entry exit spec) :
    region_ok P entry exit (spec.restrictPre (fun _ => True)) := by
  intro x R s0 hpc hrun hpre hL
  dsimp only [Spec.restrictPre] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h x R s0 hpc hrun hpre.2 hL

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt

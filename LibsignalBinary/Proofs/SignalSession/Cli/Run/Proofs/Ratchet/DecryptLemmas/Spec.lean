/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Coins.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Encrypt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Inner Store-Kit Specification Helpers for `decrypt_signal`

Defines the stack budget helper `decNeedAux`, the functional model helpers `decKeyAux` and
`decDefAux`, and the concrete CLI session and identity store kits `decSessKit` and `decIdKit`
for `signal_session_ratchet::decrypt_signal`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

abbrev decNeedAux (B : RunBudgets) : Nat :=
  2 ^ 20 + B.readFile

@[expose] noncomputable def decKeyAux (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (msg : SignalMessage) (coins : List (BitVec 8)) :
    Option IdentityKey :=
  match Slots.loadRec Scope F peer with
  | .ok (some r) =>
    match LibsignalSessionApi.SessionRecord.tryDecryptFromRecord W.C (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse) peer me) msg
        (LibsignalTripleRatchetRepr.coinsOf coins) r with
    | .ok (_, r') => r'.currentSession.bind (·.state.remoteIdentity)
    | .error _ => none
  | _ => none

@[expose] noncomputable def decDefAux (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (msg : SignalMessage) (coins : List (BitVec 8)) :
    SlotAns (List (BitVec 8)) :=
  match LibsignalSessionApi.messageDecryptSignal W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F peer (decKeyAux W Scope F peer me msg coins)) msg peer me
      (LibsignalTripleRatchetRepr.coinsOf coins) with
  | (.ok pt, calls) => some (some (cliFinal F calls, pt))
  | (.error .panic, _) => none
  | (.error _, _) => some none

theorem decDefAux_eq_model (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (x : CryptoVerification.LibsignalPublicApi.DecryptGhost) :
    decDefAux W Scope F x.rem.val x.loc.val x.msg x.rest =
      match x.model W.C (pqxdhSpqrModel W) uuidTryParse
          (cliAnswers Scope F x.rem.val (decKeyAux W Scope F x.rem.val x.loc.val x.msg x.rest)) with
      | (.ok pt, calls) => some (some (cliFinal F calls, pt))
      | (.error .panic, _) => none
      | (.error _, _) => some none :=
  rfl

set_option linter.unusedVariables false in
abbrev decSessKit (img : Unit) (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    SessionStoreSpec E2E.HooksE.A0 0#64 :=
  cliSessionStoreSpec E2E.HooksE.A0 0#64 cliIo.rd F0 cliWrOk Slots.scopeKit peer
    SessKit.loadShimNeed (SessKit.loadPollNeed B.readFile)
    SessKit.storeShimNeed SessKit.storePollNeedX

set_option linter.unusedVariables false in
abbrev decIdKit (img : Unit) (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    IdentityStoreSpec E2E.HooksE.A0 0#64 :=
  cliIdentityStoreSpec E2E.HooksE.A0 0#64 cliIo.rd F0 cliWrOk peer
    IdKit.trustShimNeed (IdKit.trustPollNeed B.readFile)
    IdKit.saveShimNeed (IdKit.savePollNeed B.readFile)

theorem decNeedAux_extHookStack_eq :
    decNeedAux ⟨extHookStack⟩ = 2 ^ 20 + 16384 := rfl

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.Core -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.Spec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.PqDecrypt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.SmDecrypt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.Top
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `signal_session_ratchet::decrypt_signal` Slot Specification and Model Agreement

Defines the functional model `decSigDef` (and remote identity lookup key `decSigKey`) for
`signal_session_ratchet::decrypt_signal`, proves the `decSigSlotSpec` binary contract, and
establishes agreement with the PQXDH and Signal-Message receive transitions.

`decSigDef` evaluates `LibsignalSessionApi.messageDecryptSignal` against the CLI store answers
(`cliAnswers`), committing `cliFinal` on success, mapping panics (including a decrypted session
lacking a remote identity) to `none`, and mapping all other errors to rejection. Because
`decSigSlotSpec`'s `onPanic` clause allows only genuine model panics or allocation failure, the
binary proof uses the tight record-decryption contract rather than the looser `recvPanics`
over-approximation.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes

/-! ## Functional model of `decrypt_signal` -/

/-- Remote identity key queried via `is_trusted_identity` during `message_decrypt_signal`: the
remote identity of the current session returned by `try_decrypt_from_record` (`none` if loading or
decryption fails or if no remote identity is present). -/
@[expose] noncomputable def decSigKey (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
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

/-- Functional model of `decrypt_signal` at the V1 SPQR model of `W`, CLI address serializer,
`cliAnswers`, and `coinsOf coins`: maps model panics to `none`, `.ok pt` to acceptance with
`cliFinal`, and other errors to rejection. -/
@[expose] noncomputable def decSigDef (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (msg : SignalMessage) (coins : List (BitVec 8)) :
    SlotAns (List (BitVec 8)) :=
  match LibsignalSessionApi.messageDecryptSignal W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F peer (decSigKey W Scope F peer me msg coins)) msg peer me
      (LibsignalTripleRatchetRepr.coinsOf coins) with
  | (.ok pt, calls) => some (some (cliFinal F calls, pt))
  | (.error .panic, _) => none
  | (.error _, _) => some none

/-- Identifies `decSigDef` on a `DecryptGhost` input with `DecryptGhost.model` evaluated at `cliAnswers`. -/
theorem decSigDef_eq_model (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (x : CryptoVerification.LibsignalPublicApi.DecryptGhost) :
    decSigDef W Scope F x.rem.val x.loc.val x.msg x.rest =
      match x.model W.C (pqxdhSpqrModel W) uuidTryParse
          (cliAnswers Scope F x.rem.val (decSigKey W Scope F x.rem.val x.loc.val x.msg x.rest)) with
      | (.ok pt, calls) => some (some (cliFinal F calls, pt))
      | (.error .panic, _) => none
      | (.error _, _) => some none := by
  rfl

/-! ## Binary `decSigSlotSpec` contract -/

/-- Stack budget `2^20 + B.readFile` for `signal_session_ratchet::decrypt_signal`. -/
abbrev cliDecryptSignalNeed (B : RunBudgets) : Nat :=
  2 ^ 20 + B.readFile

/-- `PqDecryptSignalAgrees` for `S.decryptSignal = decSigDef W Scope`. -/
theorem pqDecryptSignalAgrees_decSigDef (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.decryptSignal = decSigDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversPq W Scope) :
    RunRefine.PqDecryptSignalAgrees S W := by
  exact Agree.pqDecryptSignalAgrees_decSigDef_aux S W Scope hS hinj hcov

/-- `SmDecryptSignalAgrees` for `S.decryptSignal = decSigDef W Scope`. -/
theorem smDecryptSignalAgrees_decSigDef (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.decryptSignal = decSigDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversSm W.C Scope) :
    RunRefine.SmDecryptSignalAgrees S W.C := by
  exact Agree.smDecryptSignalAgrees_decSigDef_aux S W Scope hS hinj hcov

/-! ## Allocator- and extern-parametric generalization -/

theorem cliDecryptSignalNeed_extHookStack_eq :
    cliDecryptSignalNeed ⟨extHookStack⟩ = 2 ^ 20 + 16384 := rfl

end CryptoVerification.SignalSession.Cli.RunProofs

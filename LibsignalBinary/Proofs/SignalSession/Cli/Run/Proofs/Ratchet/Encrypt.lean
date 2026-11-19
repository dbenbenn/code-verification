/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInner -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.CliExternsWitness
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.PqEncrypt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.SmEncrypt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInst
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `signal_session_ratchet::encrypt` Slot Specification and Model Agreement

Defines the CLI store-answer evaluation (`cliAnswers`, `cliStep`, `cliFinal`) and functional model
`encDef` (with identity lookup key `encKey`) for `signal_session_ratchet::encrypt`, proves the
`encSlotSpec` binary contract, and establishes agreement with the PQXDH and Signal-Message send
transitions.

`encDef` evaluates `LibsignalSessionApi.messageEncrypt` at `UNIX_EPOCH` against `cliAnswers`,
mapping model panics (including `EncryptGhost.sendPanics`) to `none`, `.ok m` to acceptance with
`cliFinal`, and other errors to rejection. Session records at the start of a run lie in
`Scope ⊆ Slots.scopeIn`, while the session store kit operates on `Slots.scopeKit` (which is closed
under a single SPQR step from `scopeIn`).
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

/-! ## CLI store answers and final state -/

/-- CLI store answers on `F` for `peer` and queried identity key `k`: loads via
`Slots.loadRec Scope F peer`, evaluates `IdGhost.trusted` and `saveAns` on the freshly opened
identity store, and returns `.ok ()` on `store_session`. -/
@[expose] noncomputable def cliAnswers (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer : AddrVal) (k : Option IdentityKey) : StoreAnswers (List (BitVec 8)) Unit where
  loadSession := Slots.loadRec Scope F peer
  isTrustedIdentity := match k with
    | some k => StoresGhost.opened.identity.trusted cliIo.rd F peer k
    | none => .ok false
  saveIdentity := match k with
    | some k => StoresGhost.opened.identity.saveAns cliIo.rd F peer k
    | none => .ok .newOrUnchanged
  storeSession := .ok ()

/-- Single-call transition on `StoresGhost`: `save_identity` pins the key and `store_session`
writes the serialized record, while loads and trust queries leave stores unchanged. -/
@[expose] def cliStep (F : FsFiles) (g : StoresGhost) : StoreCall AddrVal (List (BitVec 8)) → StoresGhost
  | .saveIdentity rem k => { g with identity := g.identity.saveUpd cliIo.rd F rem k }
  | .storeSession rem r =>
    { g with sessions := g.sessions.put (Cli.addressText rem) (E2E.Record.encodeRecord r) }
  | _ => g

/-- Final `StoresGhost` obtained by replaying `calls` from `StoresGhost.opened`. -/
@[expose] def cliFinal (F : FsFiles) (calls : List (StoreCall AddrVal (List (BitVec 8)))) : StoresGhost :=
  calls.foldl (cliStep F) StoresGhost.opened

/-! ## Functional model of `encrypt` -/

/-- Remote identity key queried via `is_trusted_identity` during `message_encrypt`: the remote
identity of `from_session_state` on the loaded current session (`none` if missing). -/
@[expose] noncomputable def encKey (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer : AddrVal) : Option IdentityKey :=
  match Slots.loadRec Scope F peer with
  | .ok (some r) =>
    match r.currentSession with
    | some s =>
      match execOk OutgoingTripleRatchet.fromSessionState s.state with
      | .ok (_, taken) => taken.remoteIdentity
      | .error _ => none
    | none => none
  | _ => none

/-- Functional model of `encrypt` at the V1 SPQR model of `W`, CLI address serializer,
`UNIX_EPOCH`, and `cliAnswers`: maps panics to `none`, `.ok m` to acceptance with `cliFinal`, and
other errors to rejection. -/
@[expose] noncomputable def encDef (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (ptext coins : List (BitVec 8)) :
    SlotAns CiphertextMessage :=
  match LibsignalSessionApi.messageEncrypt W.C protoSignalCodec (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse)) (cliAnswers Scope F peer (encKey Scope F peer))
      ptext peer me unixEpoch coins with
  | (.ok m, calls) => some (some (cliFinal F calls, m))
  | (.error .panic, _) => none
  | (.error _, _) => some none

/-- Identifies `encDef` on an `EncryptGhost` input at `now = unixEpoch` with `EncryptGhost.model`
evaluated at `cliAnswers`. -/
theorem encDef_eq_model (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (x : CryptoVerification.LibsignalPublicApi.EncryptGhost)
    (hnow : x.now = unixEpoch) :
    encDef W Scope F x.rem.val x.loc.val x.ptext x.rest =
      match x.model W.C (pqxdhSpqrModel W) uuidTryParse
          (cliAnswers Scope F x.rem.val (encKey Scope F x.rem.val)) with
      | (.ok m, calls) => some (some (cliFinal F calls, m))
      | (.error .panic, _) => none
      | (.error _, _) => some none := by
  simp only [encDef, CryptoVerification.LibsignalPublicApi.EncryptGhost.model, hnow]

/-! ## Binary `encSlotSpec` contract -/

/-- Stack budget `2^20 + B.readFile` for `signal_session_ratchet::encrypt`. -/
abbrev cliEncryptNeed (B : RunBudgets) : Nat :=
  2 ^ 20 + B.readFile

/-- Every PQXDH domain session record lies in `Scope`. -/
@[expose] def RatchetScopeCoversPq (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ (st : PqParty) x g, PqxdhPartyInSpecDomain W st → st.session = some (x, g) →
    Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g)

/-- Every reachable Signal-Message session record lies in `Scope`. -/
@[expose] def RatchetScopeCoversSm (C : Crypto) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ g : GhostState (List (BitVec 8)), Reach (spqrOffSessionParams C) g →
    Scope (E2E.Record.toRecord E2E.Record.extrasM g)

/-- `PqEncryptAgrees` for `S.encrypt = encDef W Scope`. -/
theorem pqEncryptAgrees_encDef (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.encrypt = encDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversPq W Scope) :
    RunRefine.PqEncryptAgrees S W := by
  exact Agree.pqEncryptAgrees_encDef_aux S W Scope hS hinj hcov

/-- `SmEncryptAgrees` for `S.encrypt = encDef W Scope`. -/
theorem smEncryptAgrees_encDef (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.encrypt = encDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversSm W.C Scope) :
    RunRefine.SmEncryptAgrees S W.C := by
  exact Agree.smEncryptAgrees_encDef_aux S W Scope hS hinj hcov

/-! ## Allocator- and extern-parametric generalization -/

private theorem encDef_eq_w1EncDef (P : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    encDef P Scope = EncryptLemmas.w1EncDef P Scope := by
  have hFinal : ∀ F calls, cliFinal F calls = EncryptLemmas.w1CliFinal F calls := by
    intro F calls
    unfold cliFinal EncryptLemmas.w1CliFinal
    have hStep : cliStep F = EncryptLemmas.w1CliStep F := by
      funext g c; cases c <;> rfl
    rw [hStep]
  have hAns : ∀ F peer,
      cliAnswers Scope F peer (encKey Scope F peer) =
        EncryptLemmas.w1CliAnswers Scope F peer (EncryptLemmas.w1EncKey Scope F peer) := by
    intro F peer
    have hKey : encKey Scope F peer = EncryptLemmas.w1EncKey Scope F peer := by
      unfold encKey EncryptLemmas.w1EncKey
      rcases Slots.loadRec Scope F peer with _ | (_ | r) <;> rfl
    rw [hKey]
    unfold cliAnswers EncryptLemmas.w1CliAnswers
    rcases EncryptLemmas.w1EncKey Scope F peer with _ | _ <;> rfl
  funext F peer me ptext coins
  unfold encDef EncryptLemmas.w1EncDef
  rw [hAns F peer]
  generalize LibsignalSessionApi.messageEncrypt P.C protoSignalCodec
    (pqxdhSpqrModel P).spqr (serializeAddrVals (serviceIdParse uuidTryParse))
    (EncryptLemmas.w1CliAnswers Scope F peer (EncryptLemmas.w1EncKey Scope F peer))
    ptext peer me unixEpoch coins = rc
  rcases rc with ⟨err | m, calls⟩
  · cases err <;> rfl
  · simp only [hFinal F calls]

end CryptoVerification.SignalSession.Cli.RunProofs

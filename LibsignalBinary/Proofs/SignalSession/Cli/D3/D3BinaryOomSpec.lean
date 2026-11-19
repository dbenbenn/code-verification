/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessOom -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Whole-Process ELF Interface Bundle for Extended Pre-Key and Initiate Clauses

Packages the `OutcomeOrExcusedAbort` whole-process propositions and `MuslElf` structural
witness for a `signal-session` ELF image across baseline, extended pre-key `recv`, and
flat-bundle `init` execution paths.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.MuslElf CryptoVerification.SignalSession.ElfFrozen
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Reconstructs the `Session` stored on disk for a PQXDH domain session `(x, g)`. -/
@[expose] def d3PqSessionOf (x : RecordExtras) (g : GhostState (List (BitVec 8))) :
    Session (List (BitVec 8)) where
  state := g.session
  pendingPreKey := if g.session.pendingPreKey then some x.pending else none
  pendingKyberPreKey := if g.session.pendingPreKey then x.kyber else none
  localRegistrationId := x.localRegistrationId
  remoteRegistrationId := x.remoteRegistrationId
  aliceBaseKey := x.aliceBaseKey

/-- Pure Path-B matching-session pre-key `recv` model on arbitrary wire `PreKeySignalMessage`. -/
@[expose] def d3PqRecvMatchingModel (W : PEParams) (st : PqParty)
    (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (pm : PreKeySignalMessage) (rc : BitVec 256) :
    Option (Option (PqParty × List (BitVec 8))) :=
  let idA := pm.identityKey
  if !st.trusts idA then some none
  else if g.session.remoteIdentity ≠ some idA then some none
  else
    match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).expectedAddrs g.party) pm.message .preKey rc g.session with
    | (.ok pt, s') =>
      some (some ({ st with
        peerId := some idA
        session := some (x, { g with session := s' }) }, pt))
    | (.error .panic, _) => none
    | (.error _, _) => some none

/-- Exact `SessionRecord` wire encoding written when an incoming pre-key message creates `(x', g')`
over a non-matching session `(x, g)`. -/
@[expose] def d3NoMatchRecordBytes (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (x' : RecordExtras) (g' : GhostState (List (BitVec 8))) : List (BitVec 8) :=
  encodeRecordUnderExtras (fun _ => x') g' ++
    E2E.Record.lenField 2 (encStateUnderExtras x { g.session with pendingPreKey := false })

/-- Session-file content specification on an accepted non-matching pre-key `recv` over `(x, g)`. -/
@[expose] def D3NoMatchSessionFile (X : UnreachedPqxdhPrimitives) (P : PEParams) (st : PqParty) (x : RecordExtras)
    (g : GhostState (List (BitVec 8))) (m : PreKeyMessageFields) (rc : BitVec 256) (o : Outcome) : Prop :=
  ∀ st' out x' g', pqRecvPrekeyModel X P { st with session := none } m rc = some (some (st', out)) →
    st'.session = some (x', g') →
    ∀ code out' fs, o = .exited code out' fs →
      fs (sessionFile (partyAddress st.party.other)) = some (d3NoMatchRecordBytes x g x' g')

end LibsignalBinary.Proofs.SignalSession.Cli.D3

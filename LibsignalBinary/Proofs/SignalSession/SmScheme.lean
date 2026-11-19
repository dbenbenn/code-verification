/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.SmDir

/-!
# The `libsignal-cli` CLI as an ACD19 SM scheme: `cliSchemeFromInitKeys`

**Checked by Lean.** Instantiates an ACD19 Def. 6 secure-messaging scheme (`SMSchemeR`) over
`BinState` in which each `send` and `receive` executes `run : CliRun` on the party's directory
(`dirOfE`, `SmDir.lean`; see `Computational/docs/TRUSTED_BASE.md`):
* **Init**: `binStateOf` of `spqrOffSessionParams C`'s initial states (no CLI run).
* **Send** (`cliSendE`): `send <peer>` with empty `coins`, extracting the inner `SignalMessage` via
  `sentCiphertext` (DEV-CLI1).
* **Receive** (`cliRecvE`): `recv <peer>` on `2 ‖ c` (DEV-CLI2) with 32-byte `coins`, computing the
  ACD19 `(epoch, index)` in Lean from `c`'s header (DEV-M2).

**DEV-M9 (libsignal): no pre-key layer and no libsignal session initialisation.** Init writes
the session model's records directly (`binStateOf`, `encodeRecord`) with placeholder pending
pre-keys, `send` extracts the inner `SignalMessage` (DEV-CLI1), and `receive` accepts `2 ‖ c` only
(DEV-CLI2); PQXDH and the pre-key layer are covered instead by `PqStatement.lean`. Effect: out of
scope.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-! ## The ciphertext of a `send` -/

/-! ## One call in the state's directory -/

/-- **The inputs of one call** by the party of `s` with command `cmd`: the directory `dirOfE` with
`s`'s record, the `coins` file `coins`, stdin `stdin`. At `binStateOf g` this is `smInputs g`
(`SmDir.lean`) by definition. -/
@[expose] def binInputs (s : BinState) (cmd : Cmd) (coins stdin : List (BitVec 8)) : Inputs :=
  { argv := cmd.argv
    dirs := partyDirs
    files := dirOfE s.party s.bytes ++ [(coinsFile, coins)]
    stdin := stdin }

/-- **The record a call left** in the files `fs` of its outcome, for the party `P`: the contents of
`sessions/<peer>` (empty if the file is missing). -/
@[expose] def recordAfter (P : Party) (fs : String → Option (List (BitVec 8))) : List (BitVec 8) :=
  (fs (sessionFile (partyAddress P.other))).getD []

/-- **CLI receive** by the party of `s` of ciphertext `c` with receive coins `rc` (`recv <peer>` of
`2 ‖ c`, the 32 bytes of `rc` in `coins`): on exit `0` the new state (the record the CLI wrote),
the epoch and index of the message and the plaintext (stdout); `none` on any other outcome.

**DEV-M2 (machine model): the receive's epoch and index are computed in Lean.** The CLI does
not output ACD19 Def. 7's `(t, i)`. They are computed here from the header of `c`
(`SignalMessage.tryFrom`) and the epoch bookkeeping: index = counter + 1; a ciphertext whose header
does not parse in Lean but which the CLI accepts is reported with the current epoch and index 0
(never an honest index), so the game sees it. They decide what counts as a trivial forgery, so this
code is trusted. Effect: none. -/
@[expose] def cliRecvE (run : CliRun) (s : BinState) (c : List (BitVec 8)) (rc : BitVec 256) :
    Option (BinState × ℕ × ℕ × List (BitVec 8)) :=
  match run (binInputs s (.recv (partyAddress s.party.other)) (HMAC.keyToBytes32 rc)
      (msgTypeWhisper :: c)), SignalMessage.tryFrom protoSignalCodec c with
  | some (.exited 0 pt fs), .ok msg =>
    let (t, e) := s.epochs.recv msg.senderRatchetKey
    some (⟨s.party, recordAfter s.party fs, e⟩, t, msg.counter.toNat + 1, pt)
  | some (.exited 0 pt fs), .error _ =>
    some (⟨s.party, recordAfter s.party fs, s.epochs⟩, s.epochs.epoch, 0, pt)
  | _, _ => none

/-! ## The scheme -/

end CryptoVerification.SignalSession

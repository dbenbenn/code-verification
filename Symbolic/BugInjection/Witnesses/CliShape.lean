/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Split
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Specifications.Security.Binary

/-!
# CLI Refinement Base Shape and Setup Helpers

Defines witness setup records and byte-decoding helpers (`PQXDHSpqrSetup`, `CompKyberCorrectOn`,
`SetupMatches`, `natBytes`, `hexBytes`, `CliSetupMatches`) and the base `RefinementShape` `cliCompShape`
whose specification half (`cliCompShape.SpecHalf`) is shared across CLI witnesses and equipped with
relocatable ELF traces in `Symbolic/BugInjection/Witnesses/CliShapePlaced.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli

/-- Initial key material, registration IDs, Kyber ciphertexts, and torsion shifts of a CLI witness. -/
structure PQXDHSpqrSetup where
  /-- Alice's identity secret (`secretBytes r 0`). -/
  aliceId : HwBytes
  /-- Bob's identity secret (`secretBytes r 1`). -/
  bobId : HwBytes
  /-- Bob's signed-prekey secret (`secretBytes r 2`). -/
  spk : HwBytes
  /-- Signature on Bob's signed prekey (`setupPublic r 5`). -/
  spkSig : HwBytes
  /-- Bob's Kyber public key without type byte (`setupPublic r 6`). -/
  kyberPk : HwBytes
  /-- Signature on Bob's Kyber public key (`setupPublic r 7`). -/
  kyberPkSig : HwBytes
  /-- Bob's Kyber secret key including its type byte. -/
  kyberSec : HwBytes
  regIdA : BitVec 32
  regIdB : BitVec 32
  spkId : BitVec 32
  kpkId : BitVec 32
  /-- Kyber ciphertexts (without type byte) from prekey messages received by Bob. -/
  kyberCts : List HwBytes
  /-- Attacker-applied X25519 8-torsion shifts as `(point, point + T)` byte pairs with `8 • T = 0`. -/
  torsionShifts : List (HwBytes × HwBytes) := []
  /-- Whether Bob provisioned a one-time prekey (`r.withOpk`). Defaults to `false`. -/
  withOpk : Bool := false
  /-- Bob's one-time prekey ID (`r.opkId`), meaningful when `withOpk = true`. -/
  opkId : BitVec 32 := 0
  /-- Bob's one-time prekey secret (`secretBytes r 6`), meaningful when `withOpk = true`. -/
  opk : HwBytes := []

/-- Every ciphertext in `cts` produced by `kyberEncapsBytes` decapsulates to the same shared secret
under `kyberDecapsBytes`. -/
def CompKyberCorrectOn (i : ExternInterpretation) (r : ProtocolSetup) (cts : List HwBytes) : Prop :=
  ∀ ct ∈ cts, ∀ e ss, e.length = 32 → kyberEncapsBytes i r e = some (ct, ss) →
    kyberDecapsBytes i r ct = some ss

/-- Binds `ProtocolSetup` `r` to witness setup `w` (with optional one-time prekey) and requires
`ExternCryptoLawsHold`, `X25519PubCanonical`, and `CompKyberCorrectOn` under `i`. -/
def SetupMatches (w : PQXDHSpqrSetup) (i : ExternInterpretation) (r : ProtocolSetup) : Prop :=
  ProtocolSetupWF r ∧
    (match w.withOpk with
     | false => r.withOpk = false
     | true => r.withOpk = true ∧ r.opkId = w.opkId ∧ secretBytes r 6 = w.opk) ∧
    r.regIdA = w.regIdA ∧ r.regIdB = w.regIdB ∧
    r.spkId = w.spkId ∧ r.kpkId = w.kpkId ∧ secretBytes r 0 = w.aliceId ∧
    secretBytes r 1 = w.bobId ∧ secretBytes r 2 = w.spk ∧
    r.opaqueBytes (setupPublic r 5) = w.spkSig ∧ r.opaqueBytes (setupPublic r 6) = w.kyberPk ∧
    r.opaqueBytes (setupPublic r 7) = w.kyberPkSig ∧ r.kyberSecB = w.kyberSec ∧
    DY.Libsignal.Refinement.ExternCryptoLawsHold i ∧ X25519PubCanonical i ∧
    CompKyberCorrectOn i r w.kyberCts

/-- Little-endian `len`-byte encoding of `n`. -/
def natBytes (len n : Nat) : HwBytes := leBytes len n

/-- Decodes a hexadecimal string into bytes (`"0a1b"` ↦ `[0x0a, 0x1b]`). -/
def hexBytes (s : String) : HwBytes :=
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
  let rec go : List Char → List (BitVec 8)
    | a :: b :: rest => BitVec.ofNat 8 (16 * digit a + digit b) :: go rest
    | _ => []
  go s.toList

/-- Base CLI `RefinementShape` fixing the interpretation, setup records, contracts, and explanation
predicate (`Explains` or `CollisionAfterExplainedPrefix`); `CliShapePlaced.cliCompShapePlaced`
overrides `traces` with `elfRelPlaced mpl mmpl elf`. -/
def cliCompShape : RefinementShape where
  Setup := Arm64.Process.ElfImage
  Interp := ExternInterpretation × CryptoVerification.SignalSession.CliHooks
  Rec := DY.Libsignal.Composed.Refinement.ProtocolSetup
  Ghost := DY.Libsignal.Composed.Refinement.OpaqueSymbolSemantics
  Event := CliEvent
  contracts := fun iw _ => ExternContractsHoldCli iw.1 ∧ HooksMatchInterpretation iw.1 iw.2
  wf := DY.Libsignal.Composed.Refinement.ProtocolSetupWF
  ghostOk := fun _ _ _ => True
  traces := fun _ _ _ _ => False
  explained := fun iw r S evs =>
    (∃ g ss vis, Explains iw.1 r S g ss vis evs) ∨ CollisionAfterExplainedPrefix iw.1 r S evs

/-- Combines `SetupMatches w iw.1 r` with `ExternContractsHoldCli` and `HooksMatchInterpretation`. -/
def CliSetupMatches (w : PQXDHSpqrSetup)
    (iw : ExternInterpretation × CryptoVerification.SignalSession.CliHooks)
    (r : DY.Libsignal.Composed.Refinement.ProtocolSetup) : Prop :=
  SetupMatches w iw.1 r ∧ ExternContractsHoldCli iw.1 ∧ HooksMatchInterpretation iw.1 iw.2

end Symbolic.BugInjection

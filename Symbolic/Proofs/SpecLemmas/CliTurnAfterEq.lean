/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession

/-!
# Equivalence of Constructive `CliTurn.after` and Its Classical Formulation

Proves kernel equality (`CliTurn_after_eq_classical`) between `CliTurn.after` in
`Symbolic/Specifications/Refinement/Statement.lean` and the classical `Classical.propDecidable`
formulation `CliTurn.afterClassical`, together with kernel evaluation checks (`decide +kernel` and
`rfl`) exercising `decodeRecordBytes?` and `EligibleForSessionPromotion` on non-empty session
records.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.SpecLemmas.CliTurnAfterEq

open DY.Libsignal (HwBytes)
open DY.Libsignal.Rust (ChainRec SessionRec RecordRec EligibleForSessionPromotion recordBytes
  decodeRecordBytes?)
open DY.Libsignal.Rust.DecodeRecord (normPending)
open DY.Libsignal.PQXDH.Refinement (preKeyWire)
open DY.Libsignal.Composed.Refinement (ProtocolSetup sentBody)
open DY.Libsignal.Composed.Refinement.Cli (CliTurn CliCall DirectorySnapshot PreKeyNoMatch scrub
  aliceUuid)

/-- Classical `noncomputable` formulation of `CliTurn.after`. Matches the exact elaborated term of
`open Classical in ... decide (code = 0 ∧ PreKeyNoMatch r t c)` (`@instDecidableAnd` over
`instDecidableEqNat code 0` and `Classical.propDecidable (PreKeyNoMatch r t c)`), written out
explicitly because `instDecidablePreKeyNoMatch` would otherwise win typeclass resolution. -/
noncomputable def CliTurn.afterClassical (t : CliTurn) (r : ProtocolSetup) (c : CliCall)
    (code : Nat) (out : HwBytes) (files : DirectorySnapshot) : CliTurn :=
  { dirs := fun q => if q = c.party then scrub files else t.dirs q
    sent := t.sent ++ (match code, c.cmd with
      | 0, .send _ => (sentBody out).toList
      | _, _ => [])
    bobOff := t.bobOff || @decide (code = 0 ∧ PreKeyNoMatch r t c)
      (@instDecidableAnd _ _ (instDecidableEqNat code 0)
        (Classical.propDecidable (PreKeyNoMatch r t c))) }

/-- `CliTurn.after` agrees pointwise with the `Classical.propDecidable` definition `CliTurn.afterClassical`. -/
theorem CliTurn_after_eq_classical :
    DY.Libsignal.Composed.Refinement.Cli.CliTurn.after = CliTurn.afterClassical := by
  funext t r c code out files
  unfold DY.Libsignal.Composed.Refinement.Cli.CliTurn.after CliTurn.afterClassical
  congr 1
  exact congrArg (t.bobOff || ·)
    (congrArg (@decide (code = 0 ∧ PreKeyNoMatch r t c)) (Subsingleton.elim _ _))

/-! ## Kernel Evaluation Checks Exercising the Session-Record Decoder -/

private def sampleEk : HwBytes := List.replicate 32 7#8
private def sampleEkBad : HwBytes := List.replicate 32 8#8
private def sampleIk : HwBytes := 0x05#8 :: List.replicate 32 9#8
private def sampleRk : CryptoGames.LibsignalSession.PublicKey := ⟨List.Vector.replicate 32 1#8⟩

private def sampleInnerMsg : HwBytes :=
  CryptoGames.LibsignalSession.serializeContent CryptoVerification.LibsignalProtoCodec.protoSignalCodec
    4#8 sampleRk 0 0 [1#8, 2#8, 3#8] [] none ++ List.replicate 8 0#8

private def sampleWire : HwBytes :=
  preKeyWire (some 1) 1 1 1 sampleIk sampleEk [4#8, 5#8] sampleInnerMsg

private def sampleChain : ChainRec :=
  { senderRatchetKey := [5#8, 6#8]
    senderRatchetKeyPrivate := [7#8]
    chainKey := some (3, [9#8, 9#8])
    messageKeys := [(1, [1#8]), (200, [2#8, 2#8])] }

private def sampleSession (abk : HwBytes) : SessionRec :=
  { sessionVersion := 4
    localIdentityPublic := [1#8]
    remoteIdentityPublic := [2#8]
    rootKey := List.replicate 32 3#8
    previousCounter := 300
    senderChain := some sampleChain
    receiverChains := [sampleChain]
    pendingPreKey := some ([1#8], [2#8, 3#8])
    pendingKyberPreKey := none
    remoteRegistrationId := 77
    localRegistrationId := 0
    aliceBaseKey := abk
    pqRatchetState := [0xAA#8] }

private def recOk : RecordRec := { current := sampleSession (0x05#8 :: sampleEk), previous := [] }
private def recBadKey : RecordRec := { current := sampleSession (0x05#8 :: sampleEkBad), previous := [] }

private def sampleSetup : ProtocolSetup :=
  { alice := "alice"
    bob := "bob"
    withOpk := false
    regIdA := 1
    regIdB := 2
    spkId := 1
    kpkId := 1
    opkId := 1
    kyberSecB := []
    fresh := fun _ _ => []
    opaqueBytes := fun _ => [] }

private def emptySnap : DirectorySnapshot := fun _ => none

private def turnWith (rr : RecordRec) : CliTurn :=
  CliTurn.init (fun p _ => if p = "bob" then some (recordBytes rr) else none)

private def recvCall : CliCall :=
  { party := "bob"
    cmd := .recv ⟨aliceUuid, 1⟩
    bundle := []
    stdin := sampleWire
    coins := [] }

set_option maxRecDepth 100000 in
example : decodeRecordBytes? (recordBytes recOk) = some (normPending recOk) := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
example : EligibleForSessionPromotion (recordBytes recOk) sampleWire := by
  decide +kernel

set_option maxRecDepth 100000 in
example : ¬ EligibleForSessionPromotion (recordBytes recBadKey) sampleWire := by
  decide +kernel

set_option maxRecDepth 100000 in
example : ¬ EligibleForSessionPromotion (recordBytes recOk ++ [0#8]) sampleWire := by
  decide +kernel

set_option maxRecDepth 100000 in
example : ((turnWith recBadKey).after sampleSetup recvCall 0 [] emptySnap).bobOff = true := by
  decide +kernel

set_option maxRecDepth 100000 in
example : ((turnWith recOk).after sampleSetup recvCall 0 [] emptySnap).bobOff = false := by
  decide +kernel

end Symbolic.Proofs.SpecLemmas.CliTurnAfterEq

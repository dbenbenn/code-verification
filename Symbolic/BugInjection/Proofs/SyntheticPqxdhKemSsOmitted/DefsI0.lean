/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.DefsShaRows
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Synthetic.Witnesses.PqxdhKemSsOmittedCli

/-!
# Concrete Witness Interpretation `pqxdhI0` and Pinned `fits` Predicate

Defines the table-driven `ExternInterpretation` `pqxdhI0`, matching CLI hooks `pqxdhHooks0`,
setup records `pqxdhRecordsI0`, and proof-layer pinned predicate `cliCompFitsPinned` for
`PqxdhKemSsOmittedCli`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.DefsI0

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (x25519PublicKeySymbol x25519AgreementSymbol x25519TorsionSymbol
   aesCbcEncryptSymbol aesCbcDecryptSymbol sha256CompressSymbol sha256CompressFunction)
open DY.Libsignal.PQXDH.Refinement
  (kyberEncapsSymbol kyberDecapsSymbol
   libcruxHmacSymbol X25519TorsionShiftsRejected)
open DY.Libsignal.Composed.Refinement (ProtocolSetup OpaqueSymbolSemantics gamma leBytes secretBytes)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli HooksMatchInterpretation)
open CryptoVerification.SignalSession (CliHooks)
open Symbolic.BugInjection (PQXDHSpqrSetup TorsionShiftsRecorded SetupMatches cliCompShape fillFresh)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (bytesToNat compDefaultSha256 compDefaultHmac compDefaultKyberCt compDefaultKyberSs
   compLookupPub compLookupDh compKyberEncaps compKyberDecaps
   compHmac compOtherExtern compMlkem768FromSeed compSha512)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (bytesToSha512StateLE)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (compMlKem0 compLookupPub_length compLookupDh_length
   compKyberEncaps_length compKyberDecaps_length)
open Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.DefsShaRows (pqxdhSha256)
open Symbolic.Swarm.CREF (compSemOf)

def pqxdhAesPt0 : HwBytes := leBytes 19 0x65646172676e776f642d6d656b2d6864787170
def pqxdhAesK0 : HwBytes := leBytes 32 0x2caf6a8039f611f7bbc78c3363b654c72818ec202459e3395b2a613be17e6078
def pqxdhAesIv0 : HwBytes := leBytes 16 0x20224c976fcbd22ff29aceb0051d1c23
def pqxdhAesC00 : HwBytes := leBytes 16 0x3fc159894bbf847c9584974f8c017dd6
def pqxdhAesC01 : HwBytes := leBytes 16 0xd755a8c596b4ce014848f7f0d97bd692
def pqxdhAesPadded0 : HwBytes :=
  ByteSpecs.pkcs7Bytes (⟨pqxdhAesPt0, by decide⟩ : List.Vector (BitVec 8) 19)
def pqxdhAesA00 : CryptoGames.CBC.Block :=
  ByteSpecs.bytesToBlock (pqxdhAesPadded0.take 16) ^^^ CryptoGames.CBC.bytesToBlock pqxdhAesIv0
def pqxdhAesB00 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock pqxdhAesC00
def pqxdhAesA01 : CryptoGames.CBC.Block :=
  ByteSpecs.bytesToBlock (pqxdhAesPadded0.drop 16) ^^^ CryptoGames.CBC.bytesToBlock pqxdhAesC00
def pqxdhAesB01 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock pqxdhAesC01

/-- Two-pair involutive swap on `CryptoGames.CBC.Block` when `{a0, b0} ∩ {a1, b1} = ∅`. -/
def swap2 (a0 b0 a1 b1 x : CryptoGames.CBC.Block) : CryptoGames.CBC.Block :=
  if x == a0 then b0
  else if x == b0 then a0
  else if x == a1 then b1
  else if x == b1 then a1
  else x

def pqxdhAesBlock (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) : CryptoGames.CBC.Block :=
  if k == CryptoGames.HKDF.bytesToKey32 pqxdhAesK0 then
    swap2 pqxdhAesA00 pqxdhAesB00 pqxdhAesA01 pqxdhAesB01 b
  else b

def pqxdhAesPerm (k iv text : HwBytes) : HwBytes :=
  CryptoGames.LibsignalSession.aesCbcEncrypt pqxdhAesBlock
    (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) text

def pqxdhAesDec (k iv ct : HwBytes) : Option HwBytes :=
  CryptoGames.LibsignalSession.aesCbcDecrypt pqxdhAesBlock
    (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) ct

/-- Recorded `libcruxHmacSymbol` table adding the 1 SPQR header HMAC call of `PqxdhKemSsOmittedCli`. -/
def pqxdhHmac (k d : HwBytes) : HwBytes :=
  if k.length == 32 && d.length == 105 &&
     bytesToNat k == 0x6513997b65b30f1b72ed7de9e4d0d9b20b56abbd5a63eeb3cdd65a3698432b58 && bytesToNat d == 0x5ac2f4ce6d5b71c22b23d97cc15fd3dfd708a3bd1e6fbddc7d7cbb0b08bac6000b8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a501000000000000007265646165686b653a3836374d454b4c4d5f31565f414b4351505f6c616e676953 then
    leBytes 32 0x93f4f4316f624269d0787fe27a54d56507fcff58289e653955e1b051888a3278
  else
    compHmac k d

/-- Witness `ExternInterpretation` for `PqxdhKemSsOmittedCli`. -/
def pqxdhI0 : ExternInterpretation :=
  fun s args =>
    if s = x25519PublicKeySymbol then
      match args with | [sk] => some (compLookupPub sk) | _ => none
    else if s = x25519AgreementSymbol then
      match args with | [sk, pk] => some (compLookupDh sk pk) | _ => none
    else if s = x25519TorsionSymbol then
      none
    else if s = aesCbcEncryptSymbol then
      match args with | [text, k, iv] => some (pqxdhAesPerm k iv text) | _ => none
    else if s = aesCbcDecryptSymbol then
      match args with | [ct, k, iv] => pqxdhAesDec k iv ct | _ => none
    else if s = kyberEncapsSymbol then
      match args with | [_, rand] => some (compKyberEncaps rand) | _ => some (compDefaultKyberCt ++ compDefaultKyberSs)
    else if s = kyberDecapsSymbol then
      match args with | [_, ct] => some (compKyberDecaps ct) | _ => some compDefaultKyberSs
    else if s = libcruxHmacSymbol then
      match args with | [k, d] => some (pqxdhHmac k d) | _ => some (compDefaultHmac [] [])
    else if s = sha256CompressSymbol then
      match args with | [st, blk] => some (pqxdhSha256 st blk) | _ => some (compDefaultSha256 [] [])
    else
      compOtherExtern s args

/-- Recorded ML-KEM-768 primitives for `pqxdhHooks0`. -/
def pqxdhExecMlKem0 : CryptoVerification.LibsignalSpqrV1.MlKem :=
  { compMlKem0 with
    keyPair := fun seed => CryptoVerification.E2E.fitVec 2400 (compMlkem768FromSeed seed.toList) }

/-- Concrete CLI hooks agreeing with `pqxdhI0`. -/
def pqxdhHooks0 : CliHooks where
  C :=
    { F := sha256CompressFunction pqxdhI0
      E := pqxdhAesBlock
      D := pqxdhAesBlock
      X := fun a b => ⟨compLookupDh a.toList b.toList, compLookupDh_length a.toList b.toList⟩
      pubKey := fun a => ⟨compLookupPub a.toList, compLookupPub_length a.toList⟩ }
  Q :=
    { F512 := fun st blk =>
        bytesToSha512StateLE (compSha512 (CryptoVerification.E2E.sha512StateBytesLE st) blk)
      encaps := fun _ rand =>
        (⟨(compKyberEncaps rand.toList).take 1568, by
            rw [List.length_take, compKyberEncaps_length]; rfl⟩,
         ⟨(compKyberEncaps rand.toList).drop 1568, by
            rw [List.length_drop, compKyberEncaps_length]⟩)
      decaps := fun _ ct => ⟨compKyberDecaps ct.toList, compKyberDecaps_length ct.toList⟩
      K := pqxdhExecMlKem0 }

/-- Concrete `ProtocolSetup` of a witness setup `w` evaluated under `pqxdhI0`. -/
def pqxdhRecordsI0 (w : PQXDHSpqrSetup) : ProtocolSetup :=
  { alice := "alice", bob := "bob", withOpk := false, regIdA := w.regIdA, regIdB := w.regIdB,
    spkId := w.spkId, kpkId := w.kpkId, opkId := 0, kyberSecB := w.kyberSec, fresh := w.fresh,
    opaqueBytes := gamma pqxdhI0 w.compSem w.compGhost }

/-- Pinned `fits` predicate for `PqxdhKemSsOmittedCli` (proof layer). -/
def cliCompFitsPinned (iw : cliCompShape.Interp) (r : ProtocolSetup) : Prop :=
  (SetupMatches Symbolic.BugInjection.Synthetic.Witnesses.PqxdhKemSsOmittedCli.setup iw.1 r ∧
    iw.1 = pqxdhI0 ∧
    (secretBytes r 3 = fillFresh 11 64 ∧ secretBytes r 4 = fillFresh 16 64 ∧
      secretBytes r 5 = fillFresh 17 64) ∧
    (r.alice = "alice" ∧ r.bob = "bob") ∧
    X25519TorsionShiftsRejected iw.1 ∧
    TorsionShiftsRecorded iw.1
      Symbolic.BugInjection.Synthetic.Witnesses.PqxdhKemSsOmittedCli.setup.torsionShifts) ∧
  ExternContractsHoldCli iw.1 ∧
  HooksMatchInterpretation iw.1 iw.2

end Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.DefsI0

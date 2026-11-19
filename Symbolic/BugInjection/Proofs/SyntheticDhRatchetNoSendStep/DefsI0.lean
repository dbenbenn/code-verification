/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsShaRows
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli

/-!
# Concrete Witness Interpretation `dhRatchetI0` and Pinned `fits` Predicate

Defines the table-driven `ExternInterpretation` `dhRatchetI0`, matching CLI hooks `dhRatchetHooks0`,
setup records `dhRatchetRecordsI0`, and proof-layer pinned predicate `cliCompFitsPinned` for
`DhRatchetNoSendStepCli`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0

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
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsShaRows (dhRatchetSha256)

def dhAesPt0 : HwBytes := leBytes 19 0x6f6c6c65682d6c616974696e692d6563696c61
def dhAesK0 : HwBytes := leBytes 32 0x675cd8931fad91165aab9f19384fad036b91292bc99dd88b42fda26566aeaa51
def dhAesIv0 : HwBytes := leBytes 16 0xb7ca7a35cbdbee763f0a1a89736fc326
def dhAesC00 : HwBytes := leBytes 16 0x761bdc96f03ff507deb278ea5657291a
def dhAesC01 : HwBytes := leBytes 16 0xdbc5fd668244bee2b702b903547bc7e9
def dhAesPadded0 : HwBytes :=
  ByteSpecs.pkcs7Bytes (⟨dhAesPt0, by decide⟩ : List.Vector (BitVec 8) 19)
def dhAesA00 : CryptoGames.CBC.Block :=
  ByteSpecs.bytesToBlock (dhAesPadded0.take 16) ^^^ CryptoGames.CBC.bytesToBlock dhAesIv0
def dhAesB00 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock dhAesC00
def dhAesA01 : CryptoGames.CBC.Block :=
  ByteSpecs.bytesToBlock (dhAesPadded0.drop 16) ^^^ CryptoGames.CBC.bytesToBlock dhAesC00
def dhAesB01 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock dhAesC01

def dhAesPt1 : HwBytes := leBytes 21 0x796c7065722d6465746568637461726e752d626f62
def dhAesK1 : HwBytes := leBytes 32 0xa21004fc2492413c6de1d340a1e6128f41d1a4c6a5aa11581cee5ad13aeff371
def dhAesIv1 : HwBytes := leBytes 16 0xacaa675c2625e62693b7c0636b3dd776
def dhAesC10 : HwBytes := leBytes 16 0xc387082bd97e3a0efb86c108bfb90a98
def dhAesC11 : HwBytes := leBytes 16 0x504bb84259e0794d9931b632053c423e
def dhAesPadded1 : HwBytes :=
  ByteSpecs.pkcs7Bytes (⟨dhAesPt1, by decide⟩ : List.Vector (BitVec 8) 21)
def dhAesA10 : CryptoGames.CBC.Block :=
  ByteSpecs.bytesToBlock (dhAesPadded1.take 16) ^^^ CryptoGames.CBC.bytesToBlock dhAesIv1
def dhAesB10 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock dhAesC10
def dhAesA11 : CryptoGames.CBC.Block :=
  ByteSpecs.bytesToBlock (dhAesPadded1.drop 16) ^^^ CryptoGames.CBC.bytesToBlock dhAesC10
def dhAesB11 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock dhAesC11

/-- Two-pair involutive swap on `CryptoGames.CBC.Block` when `{a0, b0} ∩ {a1, b1} = ∅`. -/
def swap2 (a0 b0 a1 b1 x : CryptoGames.CBC.Block) : CryptoGames.CBC.Block :=
  if x == a0 then b0
  else if x == b0 then a0
  else if x == a1 then b1
  else if x == b1 then a1
  else x

def dhRatchetAesBlock (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) : CryptoGames.CBC.Block :=
  if k == CryptoGames.HKDF.bytesToKey32 dhAesK0 then
    swap2 dhAesA00 dhAesB00 dhAesA01 dhAesB01 b
  else if k == CryptoGames.HKDF.bytesToKey32 dhAesK1 then
    swap2 dhAesA10 dhAesB10 dhAesA11 dhAesB11 b
  else b

def dhRatchetAesPerm (k iv text : HwBytes) : HwBytes :=
  CryptoGames.LibsignalSession.aesCbcEncrypt dhRatchetAesBlock
    (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) text

def dhRatchetAesDec (k iv ct : HwBytes) : Option HwBytes :=
  CryptoGames.LibsignalSession.aesCbcDecrypt dhRatchetAesBlock
    (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) ct

/-- Recorded `libcruxHmacSymbol` table for `DhRatchetNoSendStepCli`. -/
def dhRatchetHmac (k d : HwBytes) : HwBytes :=
  if k.length == 32 && d.length == 105 &&
     bytesToNat k == 0x5ecb152e05ff5834fe3b23b9a714982f10c6d29af74f8ebc65dc41e85248b1cd &&
     bytesToNat d == 0x5ac2f4ce6d5b71c22b23d97cc15fd3dfd708a3bd1e6fbddc7d7cbb0b08bac6000b8cdd0fe997174ce780528bf9ecc13020f000fc44144b1638e063bc8c1218a501000000000000007265646165686b653a3836374d454b4c4d5f31565f414b4351505f6c616e676953 then
    leBytes 32 0xce849e0a450f61afb64592dc66986e1aee6c76148888a8a1efd5398f9e8f1d38
  else
    compHmac k d

/-- Witness `ExternInterpretation` for `DhRatchetNoSendStepCli`. -/
def dhRatchetI0 : ExternInterpretation :=
  fun s args =>
    if s = x25519PublicKeySymbol then
      match args with | [sk] => some (compLookupPub sk) | _ => none
    else if s = x25519AgreementSymbol then
      match args with | [sk, pk] => some (compLookupDh sk pk) | _ => none
    else if s = x25519TorsionSymbol then
      none
    else if s = aesCbcEncryptSymbol then
      match args with | [text, k, iv] => some (dhRatchetAesPerm k iv text) | _ => none
    else if s = aesCbcDecryptSymbol then
      match args with | [ct, k, iv] => dhRatchetAesDec k iv ct | _ => none
    else if s = kyberEncapsSymbol then
      match args with | [_, rand] => some (compKyberEncaps rand) | _ => some (compDefaultKyberCt ++ compDefaultKyberSs)
    else if s = kyberDecapsSymbol then
      match args with | [_, ct] => some (compKyberDecaps ct) | _ => some compDefaultKyberSs
    else if s = libcruxHmacSymbol then
      match args with | [k, d] => some (dhRatchetHmac k d) | _ => some (compDefaultHmac [] [])
    else if s = sha256CompressSymbol then
      match args with | [st, blk] => some (dhRatchetSha256 st blk) | _ => some (compDefaultSha256 [] [])
    else
      compOtherExtern s args

/-- Recorded ML-KEM-768 primitives for `dhRatchetHooks0`. -/
def dhRatchetExecMlKem0 : CryptoVerification.LibsignalSpqrV1.MlKem :=
  { compMlKem0 with
    keyPair := fun seed => CryptoVerification.E2E.fitVec 2400 (compMlkem768FromSeed seed.toList) }

/-- Concrete CLI hooks agreeing with `dhRatchetI0`. -/
def dhRatchetHooks0 : CliHooks where
  C :=
    { F := sha256CompressFunction dhRatchetI0
      E := dhRatchetAesBlock
      D := dhRatchetAesBlock
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
      K := dhRatchetExecMlKem0 }

/-- Concrete `ProtocolSetup` of a witness setup `w` evaluated under `dhRatchetI0`. -/
def dhRatchetRecordsI0 (w : PQXDHSpqrSetup) : ProtocolSetup :=
  { alice := "alice", bob := "bob", withOpk := false, regIdA := w.regIdA, regIdB := w.regIdB,
    spkId := w.spkId, kpkId := w.kpkId, opkId := 0, kyberSecB := w.kyberSec, fresh := w.fresh,
    opaqueBytes := gamma dhRatchetI0 w.compSem w.compGhost }

/-- Pinned `fits` predicate for `DhRatchetNoSendStepCli` (proof layer). -/
def cliCompFitsPinned (iw : cliCompShape.Interp) (r : ProtocolSetup) : Prop :=
  (SetupMatches Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup iw.1 r ∧
    iw.1 = dhRatchetI0 ∧
    (secretBytes r 3 = fillFresh 11 64 ∧ secretBytes r 4 = fillFresh 16 64 ∧
      secretBytes r 5 = fillFresh 17 64) ∧
    (r.alice = "alice" ∧ r.bob = "bob") ∧
    X25519TorsionShiftsRejected iw.1 ∧
    TorsionShiftsRecorded iw.1
      Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup.torsionShifts) ∧
  ExternContractsHoldCli iw.1 ∧
  HooksMatchInterpretation iw.1 iw.2

end Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0

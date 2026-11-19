/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDir
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose
public import Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli

/-!
# Concrete `PqParty` States for `Cheval26SmallSubgroupHighBitCli`

Kernel-reducible concrete `PqParty` states (`hbAlice0`, `hbAlice1`, `hbBob0`) and
`PreKeyBundleFields` (`hbBundleFields`) for the 3-call small-subgroup CLI witness (`hbInp0`,
`hbInp1`, `hbInp2`), shared by `ValidCall0Files` and `ShaGuard`.
-/

namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.PartyStates

open CryptoGames (Party)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (GhostState IdentityKey initializeInitiatorSession)
open CryptoGames.Ratchet (clampScalar)
open CryptoVerification.E2E (
  LocalIdentity PEParams PreKeyBundleFields RecordExtras UnreachedPqxdhPrimitives
  blockLevelPrims djbKey encodeRecordUnderExtras fitVec initiateInput initiateTapeLen
  initiatorRecordExtras keyPairOf ofU8 partyAddressName pqxdhSpqrSession u8Vec
)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.RecordCodecs (IdentityKeyPairStructure)
open CryptoVerification.SignalSession (
  PqKyberKey PqParty PqSignedKey addressFile baseKeysBytes identityFile identityKeyPairFile
  kyberRecordBytes le32 oneTimeRecordBytes registrationIdFile signedRecordBytes
)
open DY.Libsignal (HwBytes)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed.Interp0 (compLookupPub)
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose (cliCoins0Fast)
open Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli (setup)

public section

set_option autoImplicit false

@[expose] def compP0 : PEParams := ⟨compHooks0.C, compHooks0.Q⟩

@[expose] def compP0Real : PEParams := ⟨{ compHooks0.C with F := sha256Compress }, compHooks0.Q⟩

@[expose] def hbPubVec (sk : HwBytes) : List.Vector (BitVec 8) 32 :=
  fitVec 32 (compLookupPub (clampScalar (fitVec 32 sk)).toList)

@[expose] def hbBundleFields : PreKeyBundleFields where
  regId := setup.regIdB
  opk := none
  spkId := setup.spkId
  spkPub := hbPubVec setup.spk
  spkSig := fitVec 64 setup.spkSig
  kpkId := setup.kpkId
  kpkPub := fitVec 1568 setup.kyberPk
  kpkSig := fitVec 64 setup.kyberPkSig
  idPub := hbPubVec setup.bobId

@[expose] def hbAlice0 : PqParty where
  party := .A
  me := { idPriv := fitVec 32 setup.aliceId, regId := setup.regIdA }
  peerId := some ⟨⟨hbPubVec setup.bobId⟩⟩
  session := none
  signed := []
  oneTime := []
  kyberOneTime := []
  kyberLastResort := []

@[expose] def hbBob0 : PqParty where
  party := .B
  me := { idPriv := fitVec 32 setup.bobId, regId := setup.regIdB }
  peerId := some ⟨⟨hbPubVec setup.aliceId⟩⟩
  session := none
  signed := [(setup.spkId, { priv := fitVec 32 setup.spk, sig := fitVec 64 setup.spkSig, timestamp := 0#64 })]
  oneTime := []
  kyberOneTime := []
  kyberLastResort :=
    [(setup.kpkId,
      { pub := fitVec 1568 setup.kyberPk
        sec := fitVec 3168 (setup.kyberSec.drop 1)
        sig := fitVec 64 setup.kyberPkSig
        timestamp := 0#64 },
      [])]

@[expose] def hbTape0 : List.Vector (BitVec 8) initiateTapeLen :=
  fitVec initiateTapeLen cliCoins0Fast

@[expose] def hbDummyX : UnreachedPqxdhPrimitives :=
  { sigPkGen := fun _ => [], sigSign := fun _ _ _ => [], scalarMul := fun _ _ => [],
    scalarAdd := fun _ _ => [], kemKeyGen := fun _ => ([], []), pow8 := fun _ => [],
    isValidDhTriple := fun _ _ _ => false }

@[expose] def u8StrFast (s : String) : SignalPqxdh.Bytes := s.toList.flatMap String.utf8EncodeChar

@[expose] def modelPrimsFast (X : UnreachedPqxdhPrimitives) (W : PEParams) : SignalPqxdh.Primitives :=
  let B := blockLevelPrims X W
  let B1 : SignalPqxdh.Primitives := { B with sha512 := SignalPqxdh.sha512Ref B }
  { B1 with
    sigVerify := SignalPqxdh.xeddsaVerifyRef B1,
    isCanonical := SignalPqxdh.isCanonicalRef B1,
    hkdfDerive96 := fun sec => SignalPqxdh.hkdfExpand96Ref B1
      (SignalPqxdh.hkdfExtractRef B1 none sec)
      (u8StrFast "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"),
    rootCreateChain := SignalPqxdh.rootCreateChainRef B1,
    chainKdfSeed := SignalPqxdh.chainKdfSeedRef B1,
    chainKdfNext := SignalPqxdh.chainKdfNextRef B1,
    deriveMsgKeys := SignalPqxdh.deriveMsgKeysRef B1,
    aeadEnc := SignalPqxdh.aes256CbcHmacEncRef B1,
    aeadDec := SignalPqxdh.aes256CbcHmacDecRef B1 }

@[expose] def hbAlice1 : PqParty :=
  match SignalPqxdh.Model.initiateKeys (modelPrimsFast hbDummyX compP0)
      (initiateInput compP0 hbAlice0.me hbBundleFields hbTape0) with
  | some (dk, hdr) =>
    let idA := keyPairOf compP0.C hbAlice0.me.idPriv
    match initializeInitiatorSession compP0.C (pqxdhSpqrSession compP0)
        ⟨idA.publicKey⟩ ⟨⟨hbBundleFields.idPub⟩⟩ ⟨hbBundleFields.spkPub⟩
        (bytesToKey32 (ofU8 dk.rootKey)) (bytesToKey32 (ofU8 dk.chainKey))
        (bytesToKey32 (ofU8 dk.pqrKey)) (bytesToKey32 ((hbTape0.toList.drop 160).take 32)) with
    | .ok s =>
      { hbAlice0 with
        peerId := some ⟨⟨hbBundleFields.idPub⟩⟩,
        session := some (initiatorRecordExtras hbAlice0.me hbBundleFields
          ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt),
          ⟨.A, s.setUnacknowledgedPreKeyMessage, 0, [0]⟩) }
    | .error _ => hbAlice0
  | none => hbAlice0

@[expose] def textBytesFast (s : String) : HwBytes :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

@[expose] def idStrFast (i : BitVec 32) : String :=
  if i = 7#32 then "7" else if i = 9#32 then "9" else toString i.toNat

@[expose] def partyTextFast : Party → String
  | .A => "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"
  | .B => "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"

@[expose] def encodeDirFast (W : PEParams) (st : PqParty) : List (String × HwBytes) :=
  [(addressFile, textBytesFast (partyTextFast st.party)),
   (identityKeyPairFile, IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩),
   (registrationIdFile, le32 st.me.regId)] ++
  (match st.peerId with
   | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
   | none => []) ++
  (match st.session with
   | some (x, g) => [("sessions/" ++ partyTextFast st.party.other,
       encodeRecordUnderExtras (fun _ => x) g)]
   | none => []) ++
  st.signed.map (fun (i, k) => ("signed-pre-keys/" ++ idStrFast i, signedRecordBytes W.C i k)) ++
  st.oneTime.map (fun (i, k) =>
    ("one-time-pre-keys/" ++ idStrFast i,
     match k with | some sk => oneTimeRecordBytes W.C i sk | none => [])) ++
  st.kyberOneTime.map (fun (i, k) =>
    ("one-time-kyber-pre-keys/" ++ idStrFast i,
     match k with | some k => kyberRecordBytes i k | none => [])) ++
  (st.kyberLastResort.map fun (i, k, seen) =>
    [("last-resort-kyber-pre-keys/" ++ idStrFast i, kyberRecordBytes i k),
     ("last-resort-kyber-pre-keys/" ++ idStrFast i ++ ".base-keys", baseKeysBytes seen)]).flatten

@[expose] def hbAlice1Files : List (String × HwBytes) :=
  encodeDirFast compP0 hbAlice1

end

end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.PartyStates

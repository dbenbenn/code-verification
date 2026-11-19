/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Witness -- proof-setup: allow-public-import
import all Init.Data.Repr
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards

/-!
# Concrete 3-Call CLI Model Steps for Handshake Non-Vacuity

Evaluates the 3-call CLI execution (`init` on Alice, `send` on Alice, `recv` on Bob) against
`CliSpecPqxdh` for every `X : UnreachedPqxdhPrimitives` and both `withOpk = false` and
`withOpk = true`, together with `PqxdhPartyInSpecDomain` well-formedness witnesses.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.HandshakeModel

set_option maxRecDepth 200000

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (setupPublic pubBytes)
open CryptoGames.LibsignalSession
  (GhostState SessionState SignalMessage initializeInitiatorSession initializeRecipientSession)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.RecordCodecs
  (IdentityKeyPairStructure SignedPreKeyRecordStructure PreKeyRecordStructure)
open CryptoVerification.E2E
  (UnreachedPqxdhPrimitives PEParams LocalIdentity ResponderPreKeySecrets
   PreKeyBundleFields PreKeyMessageFields RecordExtras Bytes
   initiateTapeLen initiateInput acceptInput initiateState recvPrekeyState
   initiatorRecordExtras responderRecordExtras
   ReachablePqxdhSession keyPairOf djbKey wirePrekey wireWhisper encodeRecordUnderExtras
   pqxdhSpqrSession pqxdhSessionParams modelPrims blockLevelPrims
   ofU8 toU8 vecU8 u8Vec)
open CryptoVerification.SignalSession
  (PqParty pqInitModel pqSendModel pqRecvPrekeyModel pqRecvWhisperModel
   preKeysNamedBy markKyberUsed removeOpk encodeDir PqxdhPartyInSpecDomain
   signedRecordBytes kyberRecordBytes oneTimeRecordBytes baseKeysBytes
   sessionFile partyAddress le32)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myParams myInterp mySigBytes mySigVec freshBytes pt0 pt1 ptReply0 pt2
   myKyberPubBytes myKyberSecField mkRecords mkRecords_wf)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers (nvX u8Vec_vecU8 vecU8_length)
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)

@[expose] def tsEk (withOpk : Bool) : Nat := if withOpk then 26 else 22

@[expose] def tsEnt (withOpk : Bool) : Nat := if withOpk then 27 else 23

@[expose] def tsDhsA (withOpk : Bool) : Nat := if withOpk then 28 else 24

@[expose] def tsM0 (withOpk : Bool) : Nat := if withOpk then 35 else 31

@[expose] def tsC0 (withOpk : Bool) : Nat := if withOpk then 36 else 32

@[expose] def tsDhsB (withOpk : Bool) : Nat := if withOpk then 42 else 38

@[expose] def entByte (withOpk : Bool) : BitVec 8 := BitVec.ofNat 8 (tsEnt withOpk + 1)

/-- 192-byte `init` random tape: `ek (32B) ++ replicate 128 entByte ++ dhsA (32B)`. -/
@[expose] def tapeInitBytes (withOpk : Bool) : HwBytes :=
  freshBytes (tsEk withOpk) 32 ++
  List.replicate 128 (entByte withOpk) ++
  freshBytes (tsDhsA withOpk) 32

@[expose] def tapeInit (withOpk : Bool) : List.Vector (BitVec 8) initiateTapeLen :=
  if withOpk then ⟨tapeInitBytes true, rfl⟩ else ⟨tapeInitBytes false, rfl⟩

/-- 64-byte `send` coins (`0x31 = 49 ≤ 96`, disjoint from `'m' = 109`). -/
@[expose] def cSend0 : HwBytes := List.replicate 64 0x31#8
@[expose] def cSend0Vec : List.Vector (BitVec 8) 64 := ⟨cSend0, rfl⟩

@[expose] def rcBytes (withOpk : Bool) : HwBytes := freshBytes (tsDhsB withOpk) 32
@[expose] def rcVal (withOpk : Bool) : BitVec 256 := CryptoGames.HKDF.bytesToKey32 (rcBytes withOpk)

theorem keyToBytes32_rcVal (withOpk : Bool) :
    CryptoGames.HMAC.keyToBytes32 (rcVal withOpk) = rcBytes withOpk := by
  cases withOpk <;> decide

/-! ## Universal `UnreachedPqxdhPrimitives` Independence -/

section ExtrasCongr

private theorem hm_upd9_sigVerify_fn (B1 : SignalPqxdh.Primitives)
    (sv ic h96 rcc cks ckn dmk ae ad) :
    ({ B1 with
        sigVerify := sv
        isCanonical := ic
        hkdfDerive96 := h96
        rootCreateChain := rcc
        chainKdfSeed := cks
        chainKdfNext := ckn
        deriveMsgKeys := dmk
        aeadEnc := ae
        aeadDec := ad } : SignalPqxdh.Primitives).sigVerify = sv := rfl

private theorem hm_upd9_isCanonical_fn (B1 : SignalPqxdh.Primitives)
    (sv ic h96 rcc cks ckn dmk ae ad) :
    ({ B1 with
        sigVerify := sv
        isCanonical := ic
        hkdfDerive96 := h96
        rootCreateChain := rcc
        chainKdfSeed := cks
        chainKdfNext := ckn
        deriveMsgKeys := dmk
        aeadEnc := ae
        aeadDec := ad } : SignalPqxdh.Primitives).isCanonical = ic := rfl

private theorem hm_sha512Step_congr {B C : SignalPqxdh.Primitives}
    (h : B.sha512Compress = C.sha512Compress) :
    SignalPqxdh.sha512Step B = SignalPqxdh.sha512Step C := by
  funext s b
  unfold SignalPqxdh.sha512Step
  rw [h]

private theorem hm_sha512Ref_congr {B C : SignalPqxdh.Primitives}
    (h : B.sha512Compress = C.sha512Compress) :
    SignalPqxdh.sha512Ref B = SignalPqxdh.sha512Ref C := by
  funext msg
  unfold SignalPqxdh.sha512Ref
  rw [hm_sha512Step_congr h]

private theorem hm_xeddsaVerifyRef_congr {B C : SignalPqxdh.Primitives}
    (h1 : B.montToEd = C.montToEd) (h2 : B.compress = C.compress)
    (h3 : B.edNeg = C.edNeg) (h4 : B.scalarFromWide = C.scalarFromWide)
    (h5 : B.sha512 = C.sha512) (h6 : B.scalarFromBytesModOrder = C.scalarFromBytesModOrder)
    (h7 : B.doubleScalarMulBasepoint = C.doubleScalarMulBasepoint) :
    SignalPqxdh.xeddsaVerifyRef B = SignalPqxdh.xeddsaVerifyRef C := by
  funext pk m sig
  unfold SignalPqxdh.xeddsaVerifyRef
  rw [h1, h2, h3, h4, h5, h6, h7]

private theorem hm_isCanonicalRef_congr {B C : SignalPqxdh.Primitives}
    (h1 : B.montToEd = C.montToEd) (h2 : B.isTorsionFree = C.isTorsionFree) :
    SignalPqxdh.isCanonicalRef B = SignalPqxdh.isCanonicalRef C := by
  funext pk
  unfold SignalPqxdh.isCanonicalRef
  rw [h1, h2]

private theorem hm_upd1_montToEd (B : SignalPqxdh.Primitives) (s512) :
    ({ B with sha512 := s512 } : SignalPqxdh.Primitives).montToEd = B.montToEd := rfl

private theorem hm_upd1_compress (B : SignalPqxdh.Primitives) (s512) :
    ({ B with sha512 := s512 } : SignalPqxdh.Primitives).compress = B.compress := rfl

private theorem hm_upd1_edNeg (B : SignalPqxdh.Primitives) (s512) :
    ({ B with sha512 := s512 } : SignalPqxdh.Primitives).edNeg = B.edNeg := rfl

private theorem hm_upd1_scalarFromWide (B : SignalPqxdh.Primitives) (s512) :
    ({ B with sha512 := s512 } : SignalPqxdh.Primitives).scalarFromWide = B.scalarFromWide := rfl

private theorem hm_upd1_sha512 (B : SignalPqxdh.Primitives) (s512) :
    ({ B with sha512 := s512 } : SignalPqxdh.Primitives).sha512 = s512 := rfl

private theorem hm_upd1_scalarFromBytesModOrder (B : SignalPqxdh.Primitives) (s512) :
    ({ B with sha512 := s512 } : SignalPqxdh.Primitives).scalarFromBytesModOrder =
      B.scalarFromBytesModOrder := rfl

private theorem hm_upd1_doubleScalarMulBasepoint (B : SignalPqxdh.Primitives) (s512) :
    ({ B with sha512 := s512 } : SignalPqxdh.Primitives).doubleScalarMulBasepoint =
      B.doubleScalarMulBasepoint := rfl

private theorem hm_upd1_isTorsionFree (B : SignalPqxdh.Primitives) (s512) :
    ({ B with sha512 := s512 } : SignalPqxdh.Primitives).isTorsionFree = B.isTorsionFree := rfl

private theorem hm_block_montToEd_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (blockLevelPrims X W).montToEd = (blockLevelPrims Y W).montToEd := rfl

private theorem hm_block_compress_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (blockLevelPrims X W).compress = (blockLevelPrims Y W).compress := rfl

private theorem hm_block_edNeg_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (blockLevelPrims X W).edNeg = (blockLevelPrims Y W).edNeg := rfl

private theorem hm_block_scalarFromWide_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (blockLevelPrims X W).scalarFromWide = (blockLevelPrims Y W).scalarFromWide := rfl

private theorem hm_block_sha512Compress_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (blockLevelPrims X W).sha512Compress = (blockLevelPrims Y W).sha512Compress := rfl

private theorem hm_block_scalarFromBytesModOrder_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (blockLevelPrims X W).scalarFromBytesModOrder = (blockLevelPrims Y W).scalarFromBytesModOrder := rfl

private theorem hm_block_doubleScalarMulBasepoint_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (blockLevelPrims X W).doubleScalarMulBasepoint = (blockLevelPrims Y W).doubleScalarMulBasepoint := rfl

private theorem hm_block_isTorsionFree_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (blockLevelPrims X W).isTorsionFree = (blockLevelPrims Y W).isTorsionFree := rfl

private theorem hm_modelPrims_x25519_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (modelPrims X W).x25519 = (modelPrims Y W).x25519 := rfl

private theorem hm_modelPrims_x25519Base_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (modelPrims X W).x25519Base = (modelPrims Y W).x25519Base := rfl

private theorem hm_modelPrims_kemEncaps_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (modelPrims X W).kemEncaps = (modelPrims Y W).kemEncaps := rfl

private theorem hm_modelPrims_kemDecaps_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (modelPrims X W).kemDecaps = (modelPrims Y W).kemDecaps := rfl

private theorem hm_modelPrims_hkdfDerive96_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (modelPrims X W).hkdfDerive96 = (modelPrims Y W).hkdfDerive96 := rfl

private theorem hm_modelPrims_sigVerify_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (modelPrims X W).sigVerify = (modelPrims Y W).sigVerify :=
  (hm_upd9_sigVerify_fn _ _ _ _ _ _ _ _ _ _).trans
    ((hm_xeddsaVerifyRef_congr
      ((hm_upd1_montToEd _ _).trans ((hm_block_montToEd_congr X Y W).trans (hm_upd1_montToEd _ _).symm))
      ((hm_upd1_compress _ _).trans ((hm_block_compress_congr X Y W).trans (hm_upd1_compress _ _).symm))
      ((hm_upd1_edNeg _ _).trans ((hm_block_edNeg_congr X Y W).trans (hm_upd1_edNeg _ _).symm))
      ((hm_upd1_scalarFromWide _ _).trans ((hm_block_scalarFromWide_congr X Y W).trans (hm_upd1_scalarFromWide _ _).symm))
      ((hm_upd1_sha512 _ _).trans ((hm_sha512Ref_congr (hm_block_sha512Compress_congr X Y W)).trans (hm_upd1_sha512 _ _).symm))
      ((hm_upd1_scalarFromBytesModOrder _ _).trans ((hm_block_scalarFromBytesModOrder_congr X Y W).trans (hm_upd1_scalarFromBytesModOrder _ _).symm))
      ((hm_upd1_doubleScalarMulBasepoint _ _).trans ((hm_block_doubleScalarMulBasepoint_congr X Y W).trans (hm_upd1_doubleScalarMulBasepoint _ _).symm))).trans
      (hm_upd9_sigVerify_fn _ _ _ _ _ _ _ _ _ _).symm)

private theorem hm_modelPrims_isCanonical_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams) :
    (modelPrims X W).isCanonical = (modelPrims Y W).isCanonical :=
  (hm_upd9_isCanonical_fn _ _ _ _ _ _ _ _ _ _).trans
    ((hm_isCanonicalRef_congr
      ((hm_upd1_montToEd _ _).trans ((hm_block_montToEd_congr X Y W).trans (hm_upd1_montToEd _ _).symm))
      ((hm_upd1_isTorsionFree _ _).trans ((hm_block_isTorsionFree_congr X Y W).trans (hm_upd1_isTorsionFree _ _).symm))).trans
      (hm_upd9_isCanonical_fn _ _ _ _ _ _ _ _ _ _).symm)

private theorem hm_initiateKeys_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams)
    (inp : SignalPqxdh.InitiateKeysInput) :
    SignalPqxdh.Model.initiateKeys (modelPrims X W) inp =
      SignalPqxdh.Model.initiateKeys (modelPrims Y W) inp := by
  unfold SignalPqxdh.Model.initiateKeys
  rw [hm_modelPrims_sigVerify_congr X Y W, hm_modelPrims_kemEncaps_congr X Y W,
    hm_modelPrims_x25519Base_congr X Y W, hm_modelPrims_x25519_congr X Y W,
    hm_modelPrims_hkdfDerive96_congr X Y W]

private theorem hm_acceptKeys_congr (X Y : UnreachedPqxdhPrimitives) (W : PEParams)
    (inp : SignalPqxdh.AcceptKeysInput) :
    SignalPqxdh.Model.acceptKeys (modelPrims X W) inp =
      SignalPqxdh.Model.acceptKeys (modelPrims Y W) inp := by
  unfold SignalPqxdh.Model.acceptKeys
  rw [hm_modelPrims_isCanonical_congr X Y W, hm_modelPrims_x25519_congr X Y W,
    hm_modelPrims_kemDecaps_congr X Y W, hm_modelPrims_hkdfDerive96_congr X Y W]

theorem pqInitModel_congr_extras (X Y : UnreachedPqxdhPrimitives) (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    pqInitModel X W st b t = pqInitModel Y W st b t := by
  unfold pqInitModel initiateState
  rw [hm_initiateKeys_congr X Y W]

theorem pqRecvPrekeyModel_congr_extras (X Y : UnreachedPqxdhPrimitives) (W : PEParams) (st : PqParty)
    (m : PreKeyMessageFields) (rc : BitVec 256) :
    pqRecvPrekeyModel X W st m rc = pqRecvPrekeyModel Y W st m rc := by
  have hrecv : ∀ k, recvPrekeyState X W st.party st.me k m rc =
      recvPrekeyState Y W st.party st.me k m rc := fun k => by
    unfold recvPrekeyState
    simp only [hm_acceptKeys_congr X Y W]
  unfold pqRecvPrekeyModel
  simp only [hrecv]

end ExtrasCongr

/-! ## Computable Initial States and Bundle (`stA0_cli`, `stB0_cli`, `bE_cli`) -/

@[expose] def idPubA_vec : List.Vector (BitVec 8) 32 :=
  ⟨[11#8] ++ List.replicate 24 1#8 ++ List.replicate 7 0#8, rfl⟩

@[expose] def idPubB_vec : List.Vector (BitVec 8) 32 :=
  ⟨[19#8] ++ List.replicate 24 9#8 ++ List.replicate 7 0#8, rfl⟩

@[expose] def spkPubB_vec : List.Vector (BitVec 8) 32 :=
  ⟨[19#8] ++ List.replicate 24 11#8 ++ List.replicate 7 0#8, rfl⟩

@[expose] def opkPubB_vec : List.Vector (BitVec 8) 32 :=
  ⟨[27#8] ++ List.replicate 24 23#8 ++ List.replicate 7 0#8, rfl⟩

@[expose] def basePubA_vec (withOpk : Bool) : List.Vector (BitVec 8) 32 :=
  if withOpk then ⟨[99#8] ++ List.replicate 24 94#8 ++ List.replicate 7 0#8, rfl⟩
  else ⟨[27#8] ++ List.replicate 24 23#8 ++ List.replicate 7 0#8, rfl⟩

@[expose] def ephPubA_vec (withOpk : Bool) : List.Vector (BitVec 8) 32 :=
  if withOpk then ⟨[35#8] ++ List.replicate 24 29#8 ++ List.replicate 7 0#8, rfl⟩
  else ⟨[35#8] ++ List.replicate 24 25#8 ++ List.replicate 7 0#8, rfl⟩

@[expose] def ephPrivA_vec (withOpk : Bool) : List.Vector (BitVec 8) 32 :=
  if withOpk then ⟨[24#8] ++ List.replicate 30 29#8 ++ [93#8], rfl⟩
  else ⟨[24#8] ++ List.replicate 30 25#8 ++ [89#8], rfl⟩

@[expose] def ephPubB_vec (withOpk : Bool) : List.Vector (BitVec 8) 32 :=
  if withOpk then ⟨[51#8] ++ List.replicate 24 43#8 ++ List.replicate 7 0#8, rfl⟩
  else ⟨[43#8] ++ List.replicate 24 39#8 ++ List.replicate 7 0#8, rfl⟩

@[expose] def ephPrivB_vec (withOpk : Bool) : List.Vector (BitVec 8) 32 :=
  if withOpk then ⟨[40#8] ++ List.replicate 30 43#8 ++ [107#8], rfl⟩
  else ⟨[32#8] ++ List.replicate 30 39#8 ++ [103#8], rfl⟩

@[expose] def myKyberPub1568 : List.Vector (BitVec 8) 1568 :=
  bytesToVec 1568 myKyberPubBytes

@[expose] def myKyberSec3168 : List.Vector (BitVec 8) 3168 :=
  bytesToVec 3168 (myKyberSecField.drop 1)

@[expose] def stA0_cli (_withOpk : Bool) : PqParty where
  party := .A
  me := ⟨bytesToVec 32 (List.replicate 32 1#8), 10#32⟩
  peerId := some ⟨⟨idPubB_vec⟩⟩
  session := none
  signed := []
  oneTime := []
  kyberOneTime := []
  kyberLastResort := []

@[expose] def stB0_cli (withOpk : Bool) : PqParty where
  party := .B
  me := ⟨bytesToVec 32 (List.replicate 32 9#8), 20#32⟩
  peerId := some ⟨⟨idPubA_vec⟩⟩
  session := none
  signed := [(1#32, ⟨bytesToVec 32 (List.replicate 32 11#8), mySigVec, 0⟩)]
  oneTime :=
    if withOpk then [(3#32, some (bytesToVec 32 (List.replicate 32 23#8)))]
    else []
  kyberOneTime := []
  kyberLastResort :=
    [(2#32, ⟨myKyberPub1568, myKyberSec3168, mySigVec, 0⟩, [])]

@[expose] def bE_cli (withOpk : Bool) : PreKeyBundleFields where
  regId := 20#32
  spkId := 1#32
  spkPub := spkPubB_vec
  spkSig := mySigVec
  kpkId := 2#32
  kpkPub := myKyberPub1568
  kpkSig := mySigVec
  idPub := idPubB_vec
  opk := if withOpk then some (3#32, opkPubB_vec) else none

theorem bytesToVec_toList_of_len {n : Nat} {bs : HwBytes} (hlen : bs.length = n) :
    (bytesToVec n bs).toList = bs :=
  List.take_left' hlen

theorem mkRecords_opaque5 (withOpk : Bool) :
    (mkRecords withOpk).opaqueBytes (setupPublic (mkRecords withOpk) 5) =
      mySigBytes := by
  have h5 := (mkRecords_wf withOpk).2.2.2.1
  dsimp only [mkRecords, DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm] at h5 ⊢
  split_ifs at h5 ⊢
  · rw [myKyberPubBytes, List.length_replicate] at h5; cases h5
  · rfl

theorem mkRecords_opaque7 (withOpk : Bool) :
    (mkRecords withOpk).opaqueBytes (setupPublic (mkRecords withOpk) 7) =
      mySigBytes := by
  have h7 := (mkRecords_wf withOpk).2.2.2.2.2.1
  dsimp only [mkRecords, DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm] at h7 ⊢
  split_ifs at h7 ⊢
  · rw [myKyberPubBytes, List.length_replicate] at h7; cases h7
  · rfl

theorem keyPair_idA :
    (keyPairOf myParams.C (bytesToVec 32 (List.replicate 32 1#8))).publicKey.bytes = idPubA_vec :=
  Subtype.ext (by decide)

theorem keyPair_idB :
    (keyPairOf myParams.C (bytesToVec 32 (List.replicate 32 9#8))).publicKey.bytes = idPubB_vec :=
  Subtype.ext (by decide)

theorem keyPair_spkB :
    (keyPairOf myParams.C (bytesToVec 32 (List.replicate 32 11#8))).publicKey.bytes = spkPubB_vec :=
  Subtype.ext (by decide)

theorem keyPair_opkB :
    (keyPairOf myParams.C (bytesToVec 32 (List.replicate 32 23#8))).publicKey.bytes = opkPubB_vec :=
  Subtype.ext (by decide)

theorem pubBytes_idA :
    pubBytes myInterp (List.replicate 32 1#8) = idPubA_vec.toList := by decide

theorem pubBytes_idB :
    pubBytes myInterp (List.replicate 32 9#8) = idPubB_vec.toList := by decide

theorem pubBytes_spkB :
    pubBytes myInterp (List.replicate 32 11#8) = spkPubB_vec.toList := by decide

theorem pubBytes_opkB :
    pubBytes myInterp (List.replicate 32 23#8) = opkPubB_vec.toList := by decide

/-! ## Fast Curve25519 / XEdDSA Short-Circuit Bridge -/

section FastCurveBridge

open VerifiedLibraries.Common (
  edOrderL fpInv recoverXEven leBytesToNat
  EdPoint edZero edBasepoint edOnCurve edAdd edNeg edSub edSmul encodeEd
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (montToEdwards)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge (
  montLiftEd montLiftEd_some_onCurve
  signalMontLiftEd_eq xeddsaVerifyRef_blockLevelPrims_eq
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge (
  montLiftEd_eq_some_of_witness edSmul_edOrderL_eq_edZero_of_extLoop
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  edOnCurve_edZero edOnCurve_edBasepoint edAdd_edZero edNeg_edZero edSmul_eq_edNatSmul
)

attribute [local irreducible] fpInv recoverXEven montLiftEd montToEdwards edSmul

private def idPubB_ed : EdPoint :=
  ⟨12893379769937409070885078791022480091371600713997733562655374796140365054228,
   36986324700564178333755582630076033137746665216206247752428381271191542462764⟩

private def basePubA_false_ed : EdPoint :=
  ⟨894876293613336184566816227755714946995729436247532007424569491225980213466,
   5939010571823288455604064213266007737308572192818143217675549303121767558536⟩

private def basePubA_true_ed : EdPoint :=
  ⟨9925413356699933603403806410407956843182943490071438606480536933878847155632,
   21791398587281720237891747852681656448169713247134360314039759257844630496033⟩

private def mySigU8 : List UInt8 := (1 : UInt8) :: List.replicate 63 0

private theorem hm_ite_true {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

private theorem idPubB_montLiftEd :
    montLiftEd idPubB_vec 0#8 = some idPubB_ed :=
  (montLiftEd_eq_some_of_witness
    (uNat := 56715460385611421489716309141452797736077752721745629481235)
    (inv1my := 28357730192805710744858154570726398868038876360872814740618)
    (P := idPubB_ed)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
    idPubB_vec 0#8 (by decide) (by decide)

private theorem basePubA_false_montLiftEd :
    montLiftEd (basePubA_vec false) 0#8 = some basePubA_false_ed :=
  (montLiftEd_eq_some_of_witness
    (uNat := 144939509874340299362608345583712705325532034733349942007579)
    (inv1my := 72469754937170149681304172791856352662766017366674971003790)
    (P := basePubA_false_ed)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (basePubA_vec false) 0#8 (by decide) (by decide)

private theorem basePubA_true_montLiftEd :
    montLiftEd (basePubA_vec true) 0#8 = some basePubA_true_ed :=
  (montLiftEd_eq_some_of_witness
    (uNat := 592361475138608180003703673255173665243478750649343241248355)
    (inv1my := 296180737569304090001851836627586832621739375324671620624178)
    (P := basePubA_true_ed)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (basePubA_vec true) 0#8 (by decide) (by decide)

private theorem hm_sha512Pad_len_ge_128 (msg : List UInt8) :
    128 ≤ (SignalPqxdh.sha512Pad msg).length := by
  unfold SignalPqxdh.sha512Pad SignalPqxdh.encodeBitLen128BE SignalPqxdh.encodeBitLen64BE
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  by_cases h0 : (msg.length + 17) % 128 = 0
  · have hb : ((msg.length + 17) % 128 == 0) = true := beq_iff_eq.mpr h0
    simp only [hb, ↓reduceIte]; omega
  · have hb : ((msg.length + 17) % 128 == 0) = false := beq_eq_false_iff_ne.mpr h0
    simp only [hb, Bool.false_eq_true, ↓reduceIte]; omega

private theorem hm_foldl_const_aux {α β : Type} (f : α → β → α) (z : α)
    (hf : ∀ s x, f s x = z) :
    ∀ (l : List β), l.foldl f z = z
  | [] => rfl
  | _ :: rest => by simp only [List.foldl_cons, hf]; exact hm_foldl_const_aux f z hf rest

private theorem hm_foldl_const {α β : Type} (f : α → β → α) (z : α)
    (hf : ∀ s x, f s x = z) :
    ∀ (l : List β) (init : α), l ≠ [] → l.foldl f init = z
  | [], _, hne => absurd rfl hne
  | _ :: rest, _, _ => by
    simp only [List.foldl_cons, hf]
    exact hm_foldl_const_aux f z hf rest

private theorem hm_sha512_zero (msg : List UInt8) :
    SignalPqxdh.sha512Ref (blockLevelPrims nvX myParams) msg = List.replicate 64 0 := by
  unfold SignalPqxdh.sha512Ref SignalPqxdh.chunkBlocks
  dsimp only []
  have hdiv : 1 ≤ (SignalPqxdh.sha512Pad msg).length / 128 :=
    Nat.div_pos (hm_sha512Pad_len_ge_128 msg) (by decide)
  have hne : ((List.range ((SignalPqxdh.sha512Pad msg).length / 128)).map
      (fun i => ((SignalPqxdh.sha512Pad msg).drop (i * 128)).take 128)) ≠ [] := by
    intro heq
    have hl := congrArg List.length heq
    simp at hl
    omega
  have hstep : ∀ s b, SignalPqxdh.sha512Step (blockLevelPrims nvX myParams) s b = List.replicate 64 0 := by
    intro s b
    unfold SignalPqxdh.sha512Step
    dsimp only [blockLevelPrims, myParams, Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase.myParams,
      Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase.myHooks]
    decide
  rw [hm_foldl_const _ (List.replicate 64 0) hstep _ _ hne]
  decide

theorem sigVerify_myParams_idPubB (msg : List UInt8) :
    (modelPrims nvX myParams).sigVerify (vecU8 idPubB_vec) msg (vecU8 mySigVec) = true := by
  have hsig : vecU8 mySigVec = mySigU8 := by decide
  rw [hsig]
  have hmont := idPubB_montLiftEd
  have hP_on : edOnCurve idPubB_ed = true := montLiftEd_some_onCurve hmont
  change SignalPqxdh.xeddsaVerifyRef
    ({ blockLevelPrims nvX myParams with sha512 := SignalPqxdh.sha512Ref (blockLevelPrims nvX myParams) })
    (vecU8 idPubB_vec) msg mySigU8 = true
  rw [xeddsaVerifyRef_blockLevelPrims_eq]
  have hcond : ((vecU8 idPubB_vec).length == 32 &&
      mySigU8.length == 64 &&
      ((mySigU8.getD 63 0 &&& 0x60) == 0)) = true := by
    rw [vecU8_length]; decide
  rw [hm_ite_true hcond]
  dsimp only
  have hs0 : ((mySigU8.getD 63 0 &&& 0x80) >>> 7).toBitVec = 0#8 := by decide
  rw [hs0, u8Vec_vecU8, hmont]
  dsimp only
  rw [hm_sha512_zero]
  have hh0 : leBytesToNat (u8Vec 64 (List.replicate 64 (0 : UInt8))).toList % edOrderL = 0 := by
    decide
  have hsNat0 : leBytesToNat (u8Vec 32
      ((mySigU8.drop 32).take 31 ++ [(mySigU8.drop 32).getD 31 0 &&& 0x7F])).toList %
      edOrderL = 0 := by decide
  rw [hh0, hsNat0,
    edSmul_eq_edNatSmul (by decide) edOnCurve_edBasepoint,
    edSmul_eq_edNatSmul (by decide) hP_on]
  change (toU8 (encodeEd (edSub edZero edZero)) == mySigU8.take 32) = true
  have hsub0 : edSub edZero edZero = edZero := by
    change edAdd edZero (edNeg edZero) = edZero
    rw [edNeg_edZero, edAdd_edZero edOnCurve_edZero]
  rw [hsub0]
  decide

private theorem basePubA_false_torsionFree :
    (edSmul edOrderL basePubA_false_ed == edZero) = true := by
  rw [edSmul_edOrderL_eq_edZero_of_extLoop (by decide +kernel)]
  decide

private theorem basePubA_true_torsionFree :
    (edSmul edOrderL basePubA_true_ed == edZero) = true := by
  rw [edSmul_edOrderL_eq_edZero_of_extLoop (by decide +kernel)]
  decide

private theorem hm_upd9_isCanonical (B1 : SignalPqxdh.Primitives)
    (sv h96 rcc cks ckn dmk ae ad) (pk : List UInt8) :
    ({ B1 with
        sigVerify := sv
        isCanonical := SignalPqxdh.isCanonicalRef B1
        hkdfDerive96 := h96
        rootCreateChain := rcc
        chainKdfSeed := cks
        chainKdfNext := ckn
        deriveMsgKeys := dmk
        aeadEnc := ae
        aeadDec := ad } : SignalPqxdh.Primitives).isCanonical pk =
      SignalPqxdh.isCanonicalRef B1 pk := rfl

private theorem hm_upd1_isCanonicalRef (B : SignalPqxdh.Primitives) (s512) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef { B with sha512 := s512 } pk =
      SignalPqxdh.isCanonicalRef B pk := rfl

private theorem hm_modelPrims_isCanonical_eq (pk : List UInt8) :
    (modelPrims nvX myParams).isCanonical pk =
      SignalPqxdh.isCanonicalRef (blockLevelPrims nvX myParams) pk :=
  (hm_upd9_isCanonical _ _ _ _ _ _ _ _ _ pk).trans (hm_upd1_isCanonicalRef _ _ pk)

private theorem hm_block_eq_upd :
    blockLevelPrims nvX myParams =
      { blockLevelPrims nvX myParams with isTorsionFree := fun P => edSmul edOrderL P == edZero } := rfl

private theorem hm_upd_isTorsionFree (B : SignalPqxdh.Primitives) (f : EdPoint → Bool) (P : EdPoint) :
    ({ B with isTorsionFree := f } : SignalPqxdh.Primitives).isTorsionFree P = f P := rfl

private theorem hm_block_isTorsionFree (P : EdPoint) :
    (blockLevelPrims nvX myParams).isTorsionFree P = (edSmul edOrderL P == edZero) :=
  (congrArg (fun B : SignalPqxdh.Primitives => B.isTorsionFree P) hm_block_eq_upd).trans
    (hm_upd_isTorsionFree _ _ P)

private theorem hm_block_montToEd_zero (pk : List UInt8) :
    (blockLevelPrims nvX myParams).montToEd pk 0 = montLiftEd (u8Vec 32 pk) 0#8 := by
  change SignalPqxdh.montLiftEd (u8Vec 32 pk).toList (0 : UInt8).toBitVec = _
  rw [show (0 : UInt8).toBitVec = 0#8 from rfl, signalMontLiftEd_eq]

private theorem hm_isCanonicalRef_of_some (B : SignalPqxdh.Primitives) (pk : List UInt8) (P : EdPoint)
    (hg : (pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && SignalPqxdh.scalarIsInRange pk) = true)
    (hm : B.montToEd pk 0 = some P) :
    SignalPqxdh.isCanonicalRef B pk = B.isTorsionFree P := by
  rw [SignalPqxdh.isCanonicalRef.eq_def, hm_ite_true hg]
  split
  · rename_i Q hQ; exact congrArg B.isTorsionFree (Option.some.inj (hQ.symm.trans hm))
  · rename_i hQ; exact absurd (hQ.symm.trans hm) nofun

theorem isCanonical_myParams_basePubA (withOpk : Bool) :
    (modelPrims nvX myParams).isCanonical (vecU8 (basePubA_vec withOpk)) = true := by
  have hguard : ((vecU8 (basePubA_vec withOpk)).length == 32 &&
      (((vecU8 (basePubA_vec withOpk)).getD 31 0 &&& 0x80) == 0) &&
      SignalPqxdh.scalarIsInRange (vecU8 (basePubA_vec withOpk))) = true := by
    cases withOpk <;> decide
  cases withOpk
  · have hm : (blockLevelPrims nvX myParams).montToEd (vecU8 (basePubA_vec false)) 0 =
        some basePubA_false_ed := by
      rw [hm_block_montToEd_zero, u8Vec_vecU8]
      exact basePubA_false_montLiftEd
    exact (hm_modelPrims_isCanonical_eq _).trans
      ((hm_isCanonicalRef_of_some _ _ basePubA_false_ed hguard hm).trans
        ((hm_block_isTorsionFree basePubA_false_ed).trans basePubA_false_torsionFree))
  · have hm : (blockLevelPrims nvX myParams).montToEd (vecU8 (basePubA_vec true)) 0 =
        some basePubA_true_ed := by
      rw [hm_block_montToEd_zero, u8Vec_vecU8]
      exact basePubA_true_montLiftEd
    exact (hm_modelPrims_isCanonical_eq _).trans
      ((hm_isCanonicalRef_of_some _ _ basePubA_true_ed hguard hm).trans
        ((hm_block_isTorsionFree basePubA_true_ed).trans basePubA_true_torsionFree))

@[expose] def myModelPrimsFast : SignalPqxdh.Primitives :=
  { modelPrims nvX myParams with
    sigVerify := fun _ _ _ => true
    isCanonical := fun _ => true }

@[expose] def initiateStateFast (P : CryptoGames.Party) (me : LocalIdentity) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : Option (RecordExtras × GhostState Bytes) :=
  match SignalPqxdh.Model.initiateKeys myModelPrimsFast (initiateInput myParams me b t) with
  | none => none
  | some (dk, hdr) =>
    let idA := keyPairOf myParams.C me.idPriv
    match initializeInitiatorSession myParams.C (pqxdhSpqrSession myParams)
        ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ ⟨b.spkPub⟩
        (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey))
        (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.chainKey))
        (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
        (CryptoGames.HKDF.bytesToKey32 ((t.toList.drop 160).take 32)) with
    | .error _ => none
    | .ok st =>
      some (initiatorRecordExtras me b ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt),
        ⟨P, st.setUnacknowledgedPreKeyMessage, 0, [0]⟩)

@[expose] def recvPrekeyStateFast (P : CryptoGames.Party) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (rc : BitVec 256) :
    Option (Option (RecordExtras × GhostState Bytes × Bytes)) :=
  match SignalMessage.tryFrom protoSignalCodec m.inner with
  | .error _ => some none
  | .ok inner =>
    if m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId then some none
    else
      match SignalPqxdh.Model.acceptKeys myModelPrimsFast (acceptInput myParams me k m) with
      | none => some none
      | some dk =>
        let st0 : SessionState Bytes :=
          initializeRecipientSession (pqxdhSpqrSession myParams)
            ⟨(keyPairOf myParams.C me.idPriv).publicKey⟩
            ⟨⟨m.idPub⟩⟩ (keyPairOf myParams.C k.spkPriv)
            (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey))
            (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.chainKey))
            (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
        match SessionState.tryDecryptFromRecord myParams.C (pqxdhSpqrSession myParams)
            ((pqxdhSessionParams myParams).expectedAddrs P) inner .preKey rc st0 with
        | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
        | (.error .panic, _) => none
        | (.error _, _) => some none

@[expose] def pqInitModelFast (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : Option (Option (PqParty × List (BitVec 8))) :=
  if !st.trusts ⟨⟨b.idPub⟩⟩ then some none
  else match initiateStateFast st.party st.me b t with
    | none => some none
    | some (x, g) => some (some ({ st with peerId := some ⟨⟨b.idPub⟩⟩, session := some (x, g) }, []))

@[expose] def pqRecvPrekeyModelFast (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256) :
    Option (Option (PqParty × List (BitVec 8))) :=
  match SignalMessage.tryFrom protoSignalCodec m.inner with
  | .error _ => some none
  | .ok inner =>
    let idA : CryptoGames.LibsignalSession.IdentityKey := ⟨⟨m.idPub⟩⟩
    if !st.trusts idA then some none
    else
      match st.session with
      | some (x, g) =>
        if CryptoVerification.SignalSession.PqSessionMatches x g m then
          if g.session.remoteIdentity ≠ some idA then some none
          else
            match SessionState.tryDecryptFromRecord myParams.C (pqxdhSpqrSession myParams)
                ((pqxdhSessionParams myParams).expectedAddrs g.party) inner .preKey rc g.session with
            | (.ok pt, s) =>
              some (some ({ st with peerId := some idA, session := some (x, { g with session := s }) },
                pt))
            | (.error .panic, _) => none
            | (.error _, _) => some none
        else some none
      | none =>
        match preKeysNamedBy st m with
        | none => some none
        | some k =>
          match recvPrekeyStateFast st.party st.me k m rc with
          | none => none
          | some none => some none
          | some (some (x, g, pt)) =>
            match markKyberUsed st m with
            | none => some none
            | some st1 =>
              some (some ({ removeOpk st1 m with peerId := some idA, session := some (x, g) }, pt))

theorem initiateState_eq_fast (P : CryptoGames.Party) (me : LocalIdentity)
    (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (hikB : b.idPub = idPubB_vec) (hspk : b.spkSig = mySigVec) (hkpk : b.kpkSig = mySigVec) :
    initiateState nvX myParams P me b t = initiateStateFast P me b t := by
  have hkeys : SignalPqxdh.Model.initiateKeys (modelPrims nvX myParams)
      (initiateInput myParams me b t) =
    SignalPqxdh.Model.initiateKeys myModelPrimsFast (initiateInput myParams me b t) := by
    unfold SignalPqxdh.Model.initiateKeys initiateInput
    dsimp only []
    rw [hikB, hspk, hkpk, sigVerify_myParams_idPubB, sigVerify_myParams_idPubB]
    rfl
  unfold initiateState initiateStateFast
  rw [hkeys]
  rfl

theorem recvPrekeyState_eq_fast (P : CryptoGames.Party) (me : LocalIdentity)
    (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc : BitVec 256)
    (withOpk : Bool) (hbase : m.baseKey = basePubA_vec withOpk) :
    recvPrekeyState nvX myParams P me k m rc = recvPrekeyStateFast P me k m rc := by
  have hkeys : SignalPqxdh.Model.acceptKeys (modelPrims nvX myParams)
      (acceptInput myParams me k m) =
    SignalPqxdh.Model.acceptKeys myModelPrimsFast (acceptInput myParams me k m) := by
    unfold SignalPqxdh.Model.acceptKeys acceptInput
    dsimp only []
    rw [hbase, isCanonical_myParams_basePubA withOpk]
    rfl
  unfold recvPrekeyState recvPrekeyStateFast
  rw [hkeys]
  rfl

theorem pqInitModel_eq_fast (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen)
    (hikB : b.idPub = idPubB_vec) (hspk : b.spkSig = mySigVec) (hkpk : b.kpkSig = mySigVec) :
    pqInitModel nvX myParams st b t = pqInitModelFast st b t := by
  unfold pqInitModel pqInitModelFast
  rw [initiateState_eq_fast st.party st.me b t hikB hspk hkpk]
  rfl

theorem pqRecvPrekeyModel_eq_fast (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (withOpk : Bool) (hbase : m.baseKey = basePubA_vec withOpk) :
    pqRecvPrekeyModel nvX myParams st m rc = pqRecvPrekeyModelFast st m rc := by
  unfold pqRecvPrekeyModel pqRecvPrekeyModelFast
  cases SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rfl
  | ok inner =>
    dsimp only []
    split_ifs
    · rfl
    · cases st.session with
      | some _ => rfl
      | none =>
        cases preKeysNamedBy st m with
        | none => rfl
        | some k =>
          dsimp only []
          rw [recvPrekeyState_eq_fast st.party st.me k m rc withOpk hbase]
          rfl

end FastCurveBridge

/-! ## Closed-Form Evaluation of the 3 CLI Calls -/

@[expose] def kyberWithTag0 (withOpk : Bool) : HwBytes :=
  if withOpk then
    [0x08#8, 0xa1#8] ++ List.replicate 32 0x1c#8 ++ List.replicate 32 0x77#8 ++
      List.replicate 1503 0x00#8
  else
    [0x08#8, 0xa1#8] ++ List.replicate 32 0x18#8 ++ List.replicate 32 0x77#8 ++
      List.replicate 1503 0x00#8

@[expose] def kyberCt0_vec (withOpk : Bool) : List.Vector (BitVec 8) 1568 :=
  bytesToVec 1568 ((kyberWithTag0 withOpk).drop 1)

@[expose] def x_A (withOpk : Bool) : RecordExtras :=
  { pending := ⟨if withOpk then some 3#32 else none, 1#32, ⟨basePubA_vec withOpk⟩, 0#64⟩
    kyber := some ⟨2#32, kyberWithTag0 withOpk⟩
    remoteRegistrationId := 20#32
    localRegistrationId := 10#32
    aliceBaseKey := [5#8] ++ (basePubA_vec withOpk).1 }

@[expose] def x_B (withOpk : Bool) : RecordExtras :=
  { pending := ⟨none, 0#32, ⟨basePubA_vec withOpk⟩, 0#64⟩
    kyber := none
    remoteRegistrationId := 10#32
    localRegistrationId := 20#32
    aliceBaseKey := [5#8] ++ (basePubA_vec withOpk).1 }

@[expose] def pqA0 (withOpk : Bool) : HwBytes :=
  if withOpk then
    [0x0a#8, 0x26#8, 0x0a#8, 0x20#8, 0x67#8, 0xaa#8, 0xb4#8, 0xe7#8, 0xb0#8, 0x56#8, 0x97#8,
     0xb3#8, 0x92#8, 0x65#8, 0xcc#8, 0x9d#8, 0xeb#8, 0x85#8, 0xa2#8, 0xdf#8, 0x36#8, 0xbb#8,
     0xe8#8, 0xaf#8, 0x06#8, 0x71#8, 0xe4#8, 0x68#8, 0x63#8, 0x09#8, 0xa7#8, 0x91#8, 0x10#8,
     0x6c#8, 0x7f#8, 0xcc#8, 0x18#8, 0x01#8, 0x22#8, 0x00#8, 0x1a#8, 0x4c#8, 0x0a#8, 0x4a#8,
     0x0a#8, 0x48#8, 0x08#8, 0x01#8, 0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0x6b#8, 0x14#8, 0x3d#8,
     0x5c#8, 0xb9#8, 0xe1#8, 0xfd#8, 0x13#8, 0x10#8, 0x15#8, 0x14#8, 0x27#8, 0x4e#8, 0x8a#8,
     0xca#8, 0x67#8, 0xd1#8, 0x19#8, 0xd4#8, 0x2e#8, 0xce#8, 0x89#8, 0xb0#8, 0x44#8, 0x22#8,
     0x75#8, 0x68#8, 0x3f#8, 0x5c#8, 0xdc#8, 0xa5#8, 0x69#8, 0x12#8, 0x20#8, 0x53#8, 0x35#8,
     0x3c#8, 0x74#8, 0x42#8, 0x33#8, 0xb5#8, 0xd6#8, 0x95#8, 0x29#8, 0x43#8, 0xee#8, 0xc9#8,
     0xd2#8, 0x38#8, 0x9e#8, 0x00#8, 0x59#8, 0x50#8, 0x1a#8, 0xe2#8, 0x17#8, 0x98#8, 0xef#8,
     0xdb#8, 0x29#8, 0x12#8, 0x59#8, 0xda#8, 0x89#8, 0xfc#8, 0xfb#8]
  else
    [0x0a#8, 0x26#8, 0x0a#8, 0x20#8, 0xce#8, 0x74#8, 0xe4#8, 0x1a#8, 0xdd#8, 0x00#8, 0xbf#8,
     0xb0#8, 0x07#8, 0x48#8, 0xb5#8, 0x48#8, 0x66#8, 0xab#8, 0xc0#8, 0x10#8, 0x05#8, 0x7b#8,
     0xa3#8, 0x82#8, 0x16#8, 0x1a#8, 0xf8#8, 0x43#8, 0x5f#8, 0xd1#8, 0x4f#8, 0x7b#8, 0xb9#8,
     0x07#8, 0x42#8, 0x81#8, 0x18#8, 0x01#8, 0x22#8, 0x00#8, 0x1a#8, 0x4c#8, 0x0a#8, 0x4a#8,
     0x0a#8, 0x48#8, 0x08#8, 0x01#8, 0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0x25#8, 0x35#8, 0x76#8,
     0x4e#8, 0x75#8, 0xc8#8, 0xe1#8, 0xcd#8, 0x3a#8, 0x0a#8, 0xd6#8, 0x15#8, 0x7b#8, 0x07#8,
     0x6d#8, 0xc2#8, 0x25#8, 0xde#8, 0x6c#8, 0xb3#8, 0xbd#8, 0x77#8, 0x4c#8, 0x18#8, 0xb7#8,
     0xd7#8, 0xc0#8, 0x06#8, 0xd3#8, 0x9f#8, 0x1d#8, 0x3d#8, 0x12#8, 0x20#8, 0xea#8, 0x4c#8,
     0x8a#8, 0x9c#8, 0x62#8, 0xce#8, 0xf4#8, 0x2a#8, 0x1a#8, 0xbf#8, 0xee#8, 0x59#8, 0x10#8,
     0xb5#8, 0x49#8, 0x50#8, 0xb4#8, 0x8c#8, 0x19#8, 0x71#8, 0xfb#8, 0xd6#8, 0xed#8, 0x45#8,
     0x18#8, 0x4c#8, 0xb2#8, 0x86#8, 0xec#8, 0xde#8, 0x7a#8, 0xd1#8]

@[expose] def pqA1 (withOpk : Bool) : HwBytes :=
  if withOpk then
    [0x0a#8, 0x26#8, 0x0a#8, 0x20#8, 0x67#8, 0xaa#8, 0xb4#8, 0xe7#8, 0xb0#8, 0x56#8, 0x97#8,
     0xb3#8, 0x92#8, 0x65#8, 0xcc#8, 0x9d#8, 0xeb#8, 0x85#8, 0xa2#8, 0xdf#8, 0x36#8, 0xbb#8,
     0xe8#8, 0xaf#8, 0x06#8, 0x71#8, 0xe4#8, 0x68#8, 0x63#8, 0x09#8, 0xa7#8, 0x91#8, 0x10#8,
     0x6c#8, 0x7f#8, 0xcc#8, 0x18#8, 0x01#8, 0x22#8, 0x00#8, 0x12#8, 0x70#8, 0x1a#8, 0x4a#8,
     0x0a#8, 0x24#8, 0x08#8, 0x01#8, 0x12#8, 0x20#8, 0xdc#8, 0x93#8, 0x84#8, 0xf0#8, 0x59#8,
     0x34#8, 0x6c#8, 0x30#8, 0xe4#8, 0xb2#8, 0xef#8, 0x59#8, 0x5f#8, 0x79#8, 0xb5#8, 0xf6#8,
     0xbc#8, 0x8e#8, 0xd5#8, 0x84#8, 0x3e#8, 0x99#8, 0x0c#8, 0x85#8, 0xa3#8, 0x92#8, 0xf9#8,
     0x1c#8, 0x59#8, 0xd5#8, 0xe5#8, 0x08#8, 0x12#8, 0x22#8, 0x12#8, 0x20#8, 0x88#8, 0x9d#8,
     0x56#8, 0x28#8, 0x5d#8, 0xec#8, 0x73#8, 0x3d#8, 0x47#8, 0x0e#8, 0xa8#8, 0x45#8, 0x68#8,
     0xca#8, 0xa3#8, 0x94#8, 0xaf#8, 0x6f#8, 0x69#8, 0x40#8, 0x05#8, 0x35#8, 0xeb#8, 0x72#8,
     0x8c#8, 0x39#8, 0x16#8, 0x5d#8, 0xc0#8, 0xdc#8, 0x04#8, 0x7c#8, 0x22#8, 0x20#8, 0xd1#8,
     0x64#8, 0x22#8, 0x4c#8, 0x75#8, 0x18#8, 0xc4#8, 0x95#8, 0xdf#8, 0xd7#8, 0x7a#8, 0xdf#8,
     0xc2#8, 0x27#8, 0x06#8, 0xf5#8, 0xe0#8, 0x7e#8, 0xc2#8, 0xa8#8, 0x52#8, 0x01#8, 0x0e#8,
     0xfe#8, 0x9f#8, 0x42#8, 0xbb#8, 0x4e#8, 0xd7#8, 0xe2#8, 0x9c#8, 0xe9#8, 0x32#8, 0x00#8,
     0x1a#8, 0xb9#8, 0x1d#8, 0x12#8, 0xb6#8, 0x1d#8, 0x0a#8, 0xae#8, 0x1c#8, 0x08#8, 0x01#8,
     0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0x6b#8, 0x14#8, 0x3d#8, 0x5c#8, 0xb9#8, 0xe1#8, 0xfd#8,
     0x13#8, 0x10#8, 0x15#8, 0x14#8, 0x27#8, 0x4e#8, 0x8a#8, 0xca#8, 0x67#8, 0xd1#8, 0x19#8,
     0xd4#8, 0x2e#8, 0xce#8, 0x89#8, 0xb0#8, 0x44#8, 0x22#8, 0x75#8, 0x68#8, 0x3f#8, 0x5c#8,
     0xdc#8, 0xa5#8, 0x69#8, 0x12#8, 0x20#8, 0x53#8, 0x35#8, 0x3c#8, 0x74#8, 0x42#8, 0x33#8,
     0xb5#8, 0xd6#8, 0x95#8, 0x29#8, 0x43#8, 0xee#8, 0xc9#8, 0xd2#8, 0x38#8, 0x9e#8, 0x00#8,
     0x59#8, 0x50#8, 0x1a#8, 0xe2#8, 0x17#8, 0x98#8, 0xef#8, 0xdb#8, 0x29#8, 0x12#8, 0x59#8,
     0xda#8, 0x89#8, 0xfc#8, 0xfb#8, 0x1a#8, 0x80#8, 0x09#8] ++ List.replicate 1152 0x00#8 ++
    [0x22#8, 0xe0#8, 0x12#8] ++ List.replicate 2400 0x00#8 ++
    [0x12#8, 0x82#8, 0x01#8, 0x08#8, 0x01#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
     0xce#8, 0x29#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x05#8, 0x9e#8, 0x12#8,
     0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x47#8, 0x51#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8,
     0x00#8, 0x00#8, 0xb6#8, 0x16#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xb4#8,
     0x48#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x92#8, 0xcd#8, 0x12#8, 0x06#8,
     0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x07#8, 0x7f#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8,
     0x00#8, 0x19#8, 0x0f#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x2e#8, 0x64#8,
     0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xb7#8, 0xd9#8, 0x12#8, 0x06#8, 0x00#8,
     0x00#8, 0x00#8, 0x00#8, 0xa9#8, 0xce#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
     0x46#8, 0x6b#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x93#8, 0x2a#8, 0x12#8,
     0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xb9#8, 0xf2#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8,
     0x00#8, 0x00#8, 0xe2#8, 0x4f#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x6d#8,
     0xc2#8]
  else
    [0x0a#8, 0x26#8, 0x0a#8, 0x20#8, 0xce#8, 0x74#8, 0xe4#8, 0x1a#8, 0xdd#8, 0x00#8, 0xbf#8,
     0xb0#8, 0x07#8, 0x48#8, 0xb5#8, 0x48#8, 0x66#8, 0xab#8, 0xc0#8, 0x10#8, 0x05#8, 0x7b#8,
     0xa3#8, 0x82#8, 0x16#8, 0x1a#8, 0xf8#8, 0x43#8, 0x5f#8, 0xd1#8, 0x4f#8, 0x7b#8, 0xb9#8,
     0x07#8, 0x42#8, 0x81#8, 0x18#8, 0x01#8, 0x22#8, 0x00#8, 0x12#8, 0x70#8, 0x1a#8, 0x4a#8,
     0x0a#8, 0x24#8, 0x08#8, 0x01#8, 0x12#8, 0x20#8, 0x79#8, 0xd3#8, 0xbe#8, 0xcb#8, 0xb0#8,
     0xb9#8, 0x21#8, 0xde#8, 0xec#8, 0xb9#8, 0x74#8, 0xfc#8, 0x8d#8, 0xe1#8, 0xae#8, 0x50#8,
     0x18#8, 0x41#8, 0x73#8, 0xeb#8, 0x93#8, 0xe1#8, 0x12#8, 0xe5#8, 0x9f#8, 0x79#8, 0x6b#8,
     0x4e#8, 0x54#8, 0x07#8, 0xed#8, 0x3c#8, 0x12#8, 0x22#8, 0x12#8, 0x20#8, 0x53#8, 0xc8#8,
     0x90#8, 0xe6#8, 0xa8#8, 0x96#8, 0x27#8, 0x7a#8, 0x8f#8, 0xed#8, 0x05#8, 0x57#8, 0x75#8,
     0xb1#8, 0x52#8, 0xd2#8, 0x83#8, 0x20#8, 0xf7#8, 0x8d#8, 0xc5#8, 0x75#8, 0x4b#8, 0x48#8,
     0x69#8, 0x87#8, 0x3c#8, 0xe0#8, 0x47#8, 0xe3#8, 0xd7#8, 0xbc#8, 0x22#8, 0x20#8, 0x7f#8,
     0x57#8, 0x01#8, 0xcb#8, 0x77#8, 0x8a#8, 0xb5#8, 0x34#8, 0x05#8, 0x3c#8, 0x21#8, 0x25#8,
     0xdb#8, 0xc2#8, 0xea#8, 0x1c#8, 0x02#8, 0x75#8, 0x49#8, 0x08#8, 0x7f#8, 0x05#8, 0x4c#8,
     0x8c#8, 0xd7#8, 0xff#8, 0x5e#8, 0x3a#8, 0x89#8, 0xce#8, 0x8d#8, 0x5e#8, 0x32#8, 0x00#8,
     0x1a#8, 0xb9#8, 0x1d#8, 0x12#8, 0xb6#8, 0x1d#8, 0x0a#8, 0xae#8, 0x1c#8, 0x08#8, 0x01#8,
     0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0x25#8, 0x35#8, 0x76#8, 0x4e#8, 0x75#8, 0xc8#8, 0xe1#8,
     0xcd#8, 0x3a#8, 0x0a#8, 0xd6#8, 0x15#8, 0x7b#8, 0x07#8, 0x6d#8, 0xc2#8, 0x25#8, 0xde#8,
     0x6c#8, 0xb3#8, 0xbd#8, 0x77#8, 0x4c#8, 0x18#8, 0xb7#8, 0xd7#8, 0xc0#8, 0x06#8, 0xd3#8,
     0x9f#8, 0x1d#8, 0x3d#8, 0x12#8, 0x20#8, 0xea#8, 0x4c#8, 0x8a#8, 0x9c#8, 0x62#8, 0xce#8,
     0xf4#8, 0x2a#8, 0x1a#8, 0xbf#8, 0xee#8, 0x59#8, 0x10#8, 0xb5#8, 0x49#8, 0x50#8, 0xb4#8,
     0x8c#8, 0x19#8, 0x71#8, 0xfb#8, 0xd6#8, 0xed#8, 0x45#8, 0x18#8, 0x4c#8, 0xb2#8, 0x86#8,
     0xec#8, 0xde#8, 0x7a#8, 0xd1#8, 0x1a#8, 0x80#8, 0x09#8] ++ List.replicate 1152 0x00#8 ++
    [0x22#8, 0xe0#8, 0x12#8] ++ List.replicate 2400 0x00#8 ++
    [0x12#8, 0x82#8, 0x01#8, 0x08#8, 0x01#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
     0xfb#8, 0x28#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x39#8, 0x90#8, 0x12#8,
     0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x24#8, 0x81#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8,
     0x00#8, 0x00#8, 0x87#8, 0xa5#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xe3#8,
     0x0f#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xff#8, 0xaf#8, 0x12#8, 0x06#8,
     0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x48#8, 0xab#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8,
     0x00#8, 0xd9#8, 0xd3#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xed#8, 0xa3#8,
     0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xb6#8, 0x2e#8, 0x12#8, 0x06#8, 0x00#8,
     0x00#8, 0x00#8, 0x00#8, 0xb3#8, 0x28#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
     0xcb#8, 0x43#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x10#8, 0x0b#8, 0x12#8,
     0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x47#8, 0x36#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8,
     0x00#8, 0x00#8, 0x86#8, 0xd5#8, 0x12#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x86#8,
     0x79#8]

@[expose] def rkA1 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0x3c01b0ab17b7b5be172d37e8bd6e2bf0772e490dfa1a9567f80ecb7758cf0cfc#256
  else 0xfdb888904f1a367fc174f4659658580c763ba158762cbc5b0252da3cc448edac#256

@[expose] def cksA1 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0x053b1e9ae021748969783b423f14a20f600502c3df99b3223b4179dfe3aaf665#256
  else 0xc2c1f5c5a8d431d07ea977dfc0fcbe08112d70bb0417841beb1d00ba63f50a96#256

@[expose] def ckrA1 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0xbbd58f58490818108a330de81ef41d4c4f8acc0b13614f90159038de044b44ac#256
  else 0xa886fc2f2cec35c909c03f0d7fcfbcd12ae8993676557c8f408b9ba3a7459cb8#256

@[expose] def cksA2 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0x0e7596039b2aa87c6036d42eb0f2fdca1a240e146f63fdb4a6c614dad13e657c#256
  else 0xaa5e60529f6a3b3c7cda3a8cc5bcd6a5c929511ef7652cd9eaaa2fac3f398b68#256

@[expose] def g_A1 (withOpk : Bool) : GhostState HwBytes :=
  ⟨.A,
    { sessionVersion := 4#32
      localIdentity := ⟨⟨idPubA_vec⟩⟩
      remoteIdentity := some ⟨⟨idPubB_vec⟩⟩
      rootKey := rkA1 withOpk
      previousCounter := 0#32
      senderChain := some ⟨⟨⟨ephPubA_vec withOpk⟩, ⟨ephPrivA_vec withOpk⟩⟩, ⟨cksA1 withOpk, 0#32⟩⟩
      receiverChains := [⟨⟨spkPubB_vec⟩, some ⟨ckrA1 withOpk, 0#32⟩, []⟩]
      pendingPreKey := true
      pqRatchetState := pqA0 withOpk },
    0, [0]⟩

@[expose] def g_A2 (withOpk : Bool) : GhostState HwBytes :=
  ⟨.A,
    { (g_A1 withOpk).session with
      senderChain := some ⟨⟨⟨ephPubA_vec withOpk⟩, ⟨ephPrivA_vec withOpk⟩⟩, ⟨cksA2 withOpk, 1#32⟩⟩
      pqRatchetState := pqA1 withOpk },
    0, [0]⟩

@[expose] def stA1_cli (withOpk : Bool) : PqParty :=
  { stA0_cli withOpk with peerId := some ⟨⟨idPubB_vec⟩⟩, session := some (x_A withOpk, g_A1 withOpk) }

@[expose] def stA2_cli (withOpk : Bool) : PqParty :=
  { stA0_cli withOpk with peerId := some ⟨⟨idPubB_vec⟩⟩, session := some (x_A withOpk, g_A2 withOpk) }

@[expose] def pkAddrMid : HwBytes :=
  [0x32#8, 0x24#8, 0x00#8, 0x8a#8, 0x6f#8, 0x1c#8, 0x2e#8, 0x3b#8, 0x4d#8, 0x4e#8, 0x5f#8,
   0x9a#8, 0x0b#8, 0x1c#8, 0x2d#8, 0x3e#8, 0x4f#8, 0x5a#8, 0x6b#8, 0x01#8, 0x00#8, 0x5d#8,
   0x3e#8, 0x2f#8, 0x10#8, 0x7a#8, 0x8b#8, 0x4c#8, 0x9d#8, 0x8e#8, 0x0f#8, 0xa1#8, 0xb2#8,
   0xc3#8, 0xd4#8, 0xe5#8, 0xf6#8, 0x01#8]

@[expose] def innerBytes0 (withOpk : Bool) : HwBytes :=
  if withOpk then
    [0x44#8, 0x0a#8, 0x21#8, 0x05#8] ++ (ephPubA_vec true).1 ++
      [0x10#8, 0x00#8, 0x18#8, 0x00#8, 0x22#8, 0x10#8,
       0x35#8, 0x3f#8, 0x0d#8, 0x3c#8, 0xdc#8, 0x2b#8, 0xce#8, 0x9a#8,
       0xe7#8, 0x73#8, 0xa4#8, 0xc3#8, 0x03#8, 0xcd#8, 0x70#8, 0x9b#8,
       0x2a#8, 0x25#8] ++ List.replicate 4 0x01#8 ++ List.replicate 33 0x00#8 ++
      pkAddrMid ++ [0x32#8, 0x9c#8, 0xc9#8, 0x69#8, 0xb9#8, 0x36#8, 0x76#8, 0xc5#8]
  else
    [0x44#8, 0x0a#8, 0x21#8, 0x05#8] ++ (ephPubA_vec false).1 ++
      [0x10#8, 0x00#8, 0x18#8, 0x00#8, 0x22#8, 0x10#8,
       0xe9#8, 0x60#8, 0xbb#8, 0x04#8, 0x66#8, 0x1c#8, 0x89#8, 0xc4#8,
       0x63#8, 0x13#8, 0xd6#8, 0x36#8, 0x86#8, 0x1b#8, 0xf6#8, 0x88#8,
       0x2a#8, 0x25#8] ++ List.replicate 4 0x01#8 ++ List.replicate 33 0x00#8 ++
      pkAddrMid ++ [0x7e#8, 0xa7#8, 0x54#8, 0x4c#8, 0x37#8, 0xca#8, 0xe4#8, 0x73#8]

@[expose] def pkMsg0 (withOpk : Bool) : PreKeyMessageFields where
  regId := 10#32
  opkId := if withOpk then some 3#32 else none
  spkId := 1#32
  kpkId := 2#32
  kyberCt := kyberCt0_vec withOpk
  baseKey := basePubA_vec withOpk
  idPub := idPubA_vec
  inner := innerBytes0 withOpk

@[expose] def wire0 (withOpk : Bool) : HwBytes :=
  wirePrekey :: (pkMsg0 withOpk).bytes

@[expose] def pqB1 (withOpk : Bool) : HwBytes :=
  (if withOpk then
    [0x12#8, 0x72#8, 0x08#8, 0x01#8, 0x1a#8, 0x4a#8, 0x0a#8, 0x22#8, 0x12#8, 0x20#8, 0x88#8,
     0x9d#8, 0x56#8, 0x28#8, 0x5d#8, 0xec#8, 0x73#8, 0x3d#8, 0x47#8, 0x0e#8, 0xa8#8, 0x45#8,
     0x68#8, 0xca#8, 0xa3#8, 0x94#8, 0xaf#8, 0x6f#8, 0x69#8, 0x40#8, 0x05#8, 0x35#8, 0xeb#8,
     0x72#8, 0x8c#8, 0x39#8, 0x16#8, 0x5d#8, 0xc0#8, 0xdc#8, 0x04#8, 0x7c#8, 0x12#8, 0x24#8,
     0x08#8, 0x01#8, 0x12#8, 0x20#8, 0xdc#8, 0x93#8, 0x84#8, 0xf0#8, 0x59#8, 0x34#8, 0x6c#8,
     0x30#8, 0xe4#8, 0xb2#8, 0xef#8, 0x59#8, 0x5f#8, 0x79#8, 0xb5#8, 0xf6#8, 0xbc#8, 0x8e#8,
     0xd5#8, 0x84#8, 0x3e#8, 0x99#8, 0x0c#8, 0x85#8, 0xa3#8, 0x92#8, 0xf9#8, 0x1c#8, 0x59#8,
     0xd5#8, 0xe5#8, 0x08#8, 0x22#8, 0x20#8, 0xd1#8, 0x64#8, 0x22#8, 0x4c#8, 0x75#8, 0x18#8,
     0xc4#8, 0x95#8, 0xdf#8, 0xd7#8, 0x7a#8, 0xdf#8, 0xc2#8, 0x27#8, 0x06#8, 0xf5#8, 0xe0#8,
     0x7e#8, 0xc2#8, 0xa8#8, 0x52#8, 0x01#8, 0x0e#8, 0xfe#8, 0x9f#8, 0x42#8, 0xbb#8, 0x4e#8,
     0xd7#8, 0xe2#8, 0x9c#8, 0xe9#8, 0x32#8, 0x00#8, 0x1a#8, 0xb3#8, 0x01#8, 0x32#8, 0xb0#8,
     0x01#8, 0x0a#8, 0x48#8, 0x08#8, 0x01#8, 0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0x6b#8, 0x14#8,
     0x3d#8, 0x5c#8, 0xb9#8, 0xe1#8, 0xfd#8, 0x13#8, 0x10#8, 0x15#8, 0x14#8, 0x27#8, 0x4e#8,
     0x8a#8, 0xca#8, 0x67#8, 0xd1#8, 0x19#8, 0xd4#8, 0x2e#8, 0xce#8, 0x89#8, 0xb0#8, 0x44#8,
     0x22#8, 0x75#8, 0x68#8, 0x3f#8, 0x5c#8, 0xdc#8, 0xa5#8, 0x69#8, 0x12#8, 0x20#8, 0x53#8,
     0x35#8, 0x3c#8, 0x74#8, 0x42#8, 0x33#8, 0xb5#8, 0xd6#8, 0x95#8, 0x29#8, 0x43#8, 0xee#8,
     0xc9#8, 0xd2#8, 0x38#8, 0x9e#8, 0x00#8, 0x59#8, 0x50#8, 0x1a#8, 0xe2#8, 0x17#8, 0x98#8,
     0xef#8, 0xdb#8, 0x29#8, 0x12#8, 0x59#8, 0xda#8, 0x89#8, 0xfc#8, 0xfb#8, 0x12#8, 0x64#8,
     0x08#8, 0x30#8, 0x10#8, 0x10#8]
  else
    [0x12#8, 0x72#8, 0x08#8, 0x01#8, 0x1a#8, 0x4a#8, 0x0a#8, 0x22#8, 0x12#8, 0x20#8, 0x53#8,
     0xc8#8, 0x90#8, 0xe6#8, 0xa8#8, 0x96#8, 0x27#8, 0x7a#8, 0x8f#8, 0xed#8, 0x05#8, 0x57#8,
     0x75#8, 0xb1#8, 0x52#8, 0xd2#8, 0x83#8, 0x20#8, 0xf7#8, 0x8d#8, 0xc5#8, 0x75#8, 0x4b#8,
     0x48#8, 0x69#8, 0x87#8, 0x3c#8, 0xe0#8, 0x47#8, 0xe3#8, 0xd7#8, 0xbc#8, 0x12#8, 0x24#8,
     0x08#8, 0x01#8, 0x12#8, 0x20#8, 0x79#8, 0xd3#8, 0xbe#8, 0xcb#8, 0xb0#8, 0xb9#8, 0x21#8,
     0xde#8, 0xec#8, 0xb9#8, 0x74#8, 0xfc#8, 0x8d#8, 0xe1#8, 0xae#8, 0x50#8, 0x18#8, 0x41#8,
     0x73#8, 0xeb#8, 0x93#8, 0xe1#8, 0x12#8, 0xe5#8, 0x9f#8, 0x79#8, 0x6b#8, 0x4e#8, 0x54#8,
     0x07#8, 0xed#8, 0x3c#8, 0x22#8, 0x20#8, 0x7f#8, 0x57#8, 0x01#8, 0xcb#8, 0x77#8, 0x8a#8,
     0xb5#8, 0x34#8, 0x05#8, 0x3c#8, 0x21#8, 0x25#8, 0xdb#8, 0xc2#8, 0xea#8, 0x1c#8, 0x02#8,
     0x75#8, 0x49#8, 0x08#8, 0x7f#8, 0x05#8, 0x4c#8, 0x8c#8, 0xd7#8, 0xff#8, 0x5e#8, 0x3a#8,
     0x89#8, 0xce#8, 0x8d#8, 0x5e#8, 0x32#8, 0x00#8, 0x1a#8, 0xb3#8, 0x01#8, 0x32#8, 0xb0#8,
     0x01#8, 0x0a#8, 0x48#8, 0x08#8, 0x01#8, 0x12#8, 0x44#8, 0x0a#8, 0x20#8, 0x25#8, 0x35#8,
     0x76#8, 0x4e#8, 0x75#8, 0xc8#8, 0xe1#8, 0xcd#8, 0x3a#8, 0x0a#8, 0xd6#8, 0x15#8, 0x7b#8,
     0x07#8, 0x6d#8, 0xc2#8, 0x25#8, 0xde#8, 0x6c#8, 0xb3#8, 0xbd#8, 0x77#8, 0x4c#8, 0x18#8,
     0xb7#8, 0xd7#8, 0xc0#8, 0x06#8, 0xd3#8, 0x9f#8, 0x1d#8, 0x3d#8, 0x12#8, 0x20#8, 0xea#8,
     0x4c#8, 0x8a#8, 0x9c#8, 0x62#8, 0xce#8, 0xf4#8, 0x2a#8, 0x1a#8, 0xbf#8, 0xee#8, 0x59#8,
     0x10#8, 0xb5#8, 0x49#8, 0x50#8, 0xb4#8, 0x8c#8, 0x19#8, 0x71#8, 0xfb#8, 0xd6#8, 0xed#8,
     0x45#8, 0x18#8, 0x4c#8, 0xb2#8, 0x86#8, 0xec#8, 0xde#8, 0x7a#8, 0xd1#8, 0x12#8, 0x64#8,
     0x08#8, 0x30#8, 0x10#8, 0x10#8]) ++
  (List.replicate 16 ([0x1a#8, 0x04#8] ++ List.replicate 4 0x00#8)).flatten

@[expose] def rkB1 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0xa38193e9e37473741d83c45a49a6923e138c9cf45dd3c79b4e5ee3c88a2021ae#256
  else 0x1fad72f18e51578c9453491933b63c52ed12bc983d5cccefcf3015eb51e07d02#256

@[expose] def cksB1 (withOpk : Bool) : BitVec 256 :=
  if withOpk then 0x0b9ec3a6cf4014de4b35b96ef106d99551724aae88d7f08659ea7abbe4ada8cc#256
  else 0xbe27055e7e3a248bfe4b781ae1eb29db832c222487b49430aafcb7c672667aa1#256

@[expose] def g_B1 (withOpk : Bool) : GhostState HwBytes :=
  ⟨.B,
    { sessionVersion := 4#32
      localIdentity := ⟨⟨idPubB_vec⟩⟩
      remoteIdentity := some ⟨⟨idPubA_vec⟩⟩
      rootKey := rkB1 withOpk
      previousCounter := 0#32
      senderChain := some ⟨⟨⟨ephPubB_vec withOpk⟩, ⟨ephPrivB_vec withOpk⟩⟩, ⟨cksB1 withOpk, 0#32⟩⟩
      receiverChains := [⟨⟨ephPubA_vec withOpk⟩, some ⟨cksA2 withOpk, 1#32⟩, []⟩]
      pendingPreKey := false
      pqRatchetState := pqB1 withOpk },
    1, [1]⟩

@[expose] def stB0Marked (withOpk : Bool) : PqParty :=
  { stB0_cli withOpk with
    kyberLastResort :=
      [(2#32, ⟨myKyberPub1568, myKyberSec3168, mySigVec, 0⟩,
        [(1#32, basePubA_vec withOpk)])] }

@[expose] def stB1_cli (withOpk : Bool) : PqParty :=
  { stB0Marked withOpk with
    peerId := some ⟨⟨idPubA_vec⟩⟩
    session := some (x_B withOpk, g_B1 withOpk)
    oneTime := if withOpk then [(3#32, none)] else [] }

theorem wire0_eq (withOpk : Bool) :
    wire0 withOpk = wirePrekey :: (pkMsg0 withOpk).bytes := rfl

private def reprParty : CryptoGames.Party → Bool
  | .A => false
  | .B => true

private theorem reprParty_inj {a b : CryptoGames.Party} (h : reprParty a = reprParty b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private def reprRecordExtras (x : RecordExtras) :=
  ((x.pending.1, x.pending.2, x.pending.3.bytes.1, x.pending.4),
   x.kyber.map (fun k => (k.1, @id (List (BitVec 8)) k.2)),
   x.remoteRegistrationId, x.localRegistrationId, @id (List (BitVec 8)) x.aliceBaseKey)

private theorem reprRecordExtras_inj {a b : RecordExtras}
    (h : reprRecordExtras a = reprRecordExtras b) : a = b := by
  rcases a with ⟨⟨p1, p2, ⟨pb⟩, p4⟩, kyA, rA, lA, bkA⟩
  rcases b with ⟨⟨q1, q2, ⟨qb⟩, q4⟩, kyB, rB, lB, bkB⟩
  simp only [reprRecordExtras, id_eq, Prod.mk.injEq] at h
  rcases h with ⟨⟨rfl, rfl, hpb, rfl⟩, hky, rfl, rfl, rfl⟩
  cases Subtype.ext hpb; congr 1
  cases kyA with
  | none => cases kyB with | none => rfl | some _ => cases hky
  | some ka =>
    cases kyB with
    | none => cases hky
    | some kb =>
      rcases ka with ⟨i1, c1⟩; rcases kb with ⟨i2, c2⟩
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hky
      rcases hky with ⟨rfl, rfl⟩; rfl

private def reprKyberKey (k : CryptoVerification.SignalSession.PqKyberKey) :=
  (k.pub.1, k.sec.1, k.sig.1, k.timestamp)

private theorem reprKyberKey_inj {a b : CryptoVerification.SignalSession.PqKyberKey}
    (h : reprKyberKey a = reprKyberKey b) : a = b := by
  rcases a with ⟨p1, s1, g1, t1⟩; rcases b with ⟨p2, s2, g2, t2⟩
  simp only [reprKyberKey, Prod.mk.injEq] at h
  rcases h with ⟨hp, hs, hg, rfl⟩
  rw [Subtype.ext hp, Subtype.ext hs, Subtype.ext hg]

private def reprSession (s : CryptoGames.LibsignalSession.SessionState CryptoVerification.E2E.Bytes) :=
  (s.sessionVersion, s.localIdentity.publicKey.bytes.1,
   s.remoteIdentity.map (fun k => k.publicKey.bytes.1), s.rootKey, s.previousCounter,
   s.senderChain.map (fun sc =>
     ((sc.ratchetKey.publicKey.bytes.1, sc.ratchetKey.privateKey.bytes.1),
      (sc.chainKey.key, sc.chainKey.index))),
   s.receiverChains.map (fun rc =>
     (rc.senderRatchetKey.bytes.1, rc.chainKey.map (fun ck => (ck.key, ck.index)),
      rc.messageKeys.map (fun mk => (mk.seed, mk.counter)))),
   s.pendingPreKey, @id (List (BitVec 8)) s.pqRatchetState)

private theorem reprSession_inj {a b : CryptoGames.LibsignalSession.SessionState CryptoVerification.E2E.Bytes}
    (h : reprSession a = reprSession b) : a = b := by
  rcases a with ⟨sv1, ⟨⟨li1⟩⟩, ri1, rk1, pc1, sc1, rc1, pp1, pq1⟩
  rcases b with ⟨sv2, ⟨⟨li2⟩⟩, ri2, rk2, pc2, sc2, rc2, pp2, pq2⟩
  simp only [reprSession, id_eq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, hli, hri, rfl, rfl, hsc, hrc, rfl, hpq⟩
  cases Subtype.ext hli
  have hri' : ri1 = ri2 := Option.map_injective (by rintro ⟨⟨v1⟩⟩ ⟨⟨v2⟩⟩ hv; cases Subtype.ext hv; rfl) hri
  have hsc' : sc1 = sc2 := by
    refine Option.map_injective ?_ hsc
    rintro ⟨⟨⟨pub1⟩, ⟨prv1⟩⟩, ⟨ck1, ci1⟩⟩ ⟨⟨⟨pub2⟩, ⟨prv2⟩⟩, ⟨ck2, ci2⟩⟩ hs
    simp only [Prod.mk.injEq] at hs; rcases hs with ⟨⟨hp1, hp2⟩, rfl, rfl⟩
    rw [Subtype.ext hp1, Subtype.ext hp2]
  have hrc' : rc1 = rc2 := by
    refine List.map_injective_iff.mpr ?_ hrc
    rintro ⟨⟨srk1⟩, ck1, mks1⟩ ⟨⟨srk2⟩, ck2, mks2⟩ hr
    simp only [Prod.mk.injEq] at hr; rcases hr with ⟨hsrk, hck, hmks⟩
    have hck' : ck1 = ck2 := Option.map_injective
      (by rintro ⟨k1, i1⟩ ⟨k2, i2⟩ hc; simp only [Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩; rfl) hck
    have hmks' : mks1 = mks2 := List.map_injective_iff.mpr
      (by rintro ⟨sd1, ct1⟩ ⟨sd2, ct2⟩ hm; simp only [Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩; rfl) hmks
    rw [Subtype.ext hsrk, hck', hmks']
  have hpq' : pq1 = pq2 := hpq
  rw [hri', hsc', hrc', hpq']

private def reprPqParty (st : PqParty) :=
  (reprParty st.party, (st.me.1.1, st.me.2), st.peerId.map (fun k => k.publicKey.bytes.1),
   st.session.map (fun (x, g) =>
     (reprRecordExtras x, reprParty g.party, reprSession g.session, g.epoch, g.chainEpochs)),
   st.signed.map (fun (i, s) => (i, s.priv.1, s.sig.1, s.timestamp)),
   st.oneTime.map (fun (i, o) => (i, o.map fun v : List.Vector (BitVec 8) 32 => v.1)),
   st.kyberOneTime.map (fun (i, o) => (i, o.map reprKyberKey)),
   st.kyberLastResort.map (fun (i, k, s) =>
     (i, reprKyberKey k, s.map fun p : BitVec 32 × List.Vector (BitVec 8) 32 => (p.1, p.2.1))))

private theorem reprPqParty_inj {a b : PqParty} (h : reprPqParty a = reprPqParty b) : a = b := by
  rcases a with ⟨pa, ⟨ma1, ma2⟩, pida, sa, sga, ota, kota, klra⟩
  rcases b with ⟨pb, ⟨mb1, mb2⟩, pidb, sb, sgb, otb, kotb, klrb⟩
  simp only [reprPqParty, Prod.mk.injEq] at h
  rcases h with ⟨hp, ⟨hma, rfl⟩, hpid, hsess, hsig, hot, hkot, hklr⟩
  cases reprParty_inj hp; cases Subtype.ext hma
  have hpid' : pida = pidb := Option.map_injective (by rintro ⟨⟨v1⟩⟩ ⟨⟨v2⟩⟩ hv; cases Subtype.ext hv; rfl) hpid
  have hsess' : sa = sb := by
    refine Option.map_injective ?_ hsess
    rintro ⟨xa, ⟨gpa, gsa, gea, gca⟩⟩ ⟨xb, ⟨gpb, gsb, geb, gcb⟩⟩ heq
    simp only [Prod.mk.injEq] at heq; rcases heq with ⟨hx, hgp, hgs, rfl, rfl⟩
    rw [reprRecordExtras_inj hx, reprParty_inj hgp, reprSession_inj hgs]
  have hsig' : sga = sgb := by
    refine List.map_injective_iff.mpr ?_ hsig
    rintro ⟨i1, ⟨pr1, sg1, ts1⟩⟩ ⟨i2, ⟨pr2, sg2, ts2⟩⟩ heq
    simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, hpr, hsg, rfl⟩
    rw [Subtype.ext hpr, Subtype.ext hsg]
  have hot' : ota = otb := List.map_injective_iff.mpr
    (by rintro ⟨i1, o1⟩ ⟨i2, o2⟩ heq; simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, ho⟩
        rw [Option.map_injective (fun _ _ => Subtype.ext) ho]) hot
  have hkot' : kota = kotb := List.map_injective_iff.mpr
    (by rintro ⟨i1, o1⟩ ⟨i2, o2⟩ heq; simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, ho⟩
        rw [Option.map_injective (fun _ _ => reprKyberKey_inj) ho]) hkot
  have hklr' : klra = klrb := by
    refine List.map_injective_iff.mpr ?_ hklr
    rintro ⟨i1, k1, l1⟩ ⟨i2, k2, l2⟩ heq
    simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, hk, hl⟩
    have hl' : l1 = l2 := List.map_injective_iff.mpr
      (by rintro ⟨j1, v1⟩ ⟨j2, v2⟩ hjv; simp only [Prod.mk.injEq] at hjv; rcases hjv with ⟨rfl, hv⟩
          rw [Subtype.ext hv]) hl
    rw [reprKyberKey_inj hk, hl']
  rw [hpid', hsess', hsig', hot', hkot', hklr']

private def reprOut (r : Option (Option (PqParty × HwBytes))) :=
  r.map (Option.map fun (st, out) => (reprPqParty st, @id (List (BitVec 8)) out))

private theorem eq_of_reprOut {a b : Option (Option (PqParty × HwBytes))}
    (h : reprOut a = reprOut b) : a = b := by
  unfold reprOut at h
  refine Option.map_injective (fun x y hxy => Option.map_injective ?_ hxy) h
  rintro ⟨s1, o1⟩ ⟨s2, o2⟩ hs
  simp only [Prod.mk.injEq, id_eq] at hs
  rw [reprPqParty_inj hs.1, hs.2]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
private def decReprOut (a b : Option (Option (PqParty × HwBytes))) : Bool :=
  reprOut a == reprOut b

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem eq_of_decReprOut {a b : Option (Option (PqParty × HwBytes))}
    (h : decReprOut a b = true) : a = b := by
  unfold decReprOut at h
  exact eq_of_reprOut (eq_of_beq h)

private theorem tapeInit_eq (withOpk : Bool) :
    tapeInit withOpk = ⟨tapeInitBytes withOpk, by cases withOpk <;> rfl⟩ := by
  cases withOpk
  · exact Subtype.ext (bytesToVec_toList_of_len (n := initiateTapeLen) (bs := tapeInitBytes false) (by decide))
  · exact Subtype.ext (bytesToVec_toList_of_len (n := initiateTapeLen) (bs := tapeInitBytes true) (by decide))

theorem initStep_eq (withOpk : Bool) :
    pqInitModel nvX myParams (stA0_cli withOpk) (bE_cli withOpk) (tapeInit withOpk) =
      some (some (stA1_cli withOpk, [])) := by
  rw [pqInitModel_eq_fast _ _ _ rfl rfl rfl, tapeInit_eq]
  cases withOpk <;> exact eq_of_decReprOut (by decide +kernel)

theorem initStep_eq_any (X : UnreachedPqxdhPrimitives) (withOpk : Bool) :
    pqInitModel X myParams (stA0_cli withOpk) (bE_cli withOpk) (tapeInit withOpk) =
      some (some (stA1_cli withOpk, [])) := by
  rw [pqInitModel_congr_extras X nvX]
  exact initStep_eq withOpk

theorem sendStep_eq (withOpk : Bool) :
    pqSendModel myParams (stA1_cli withOpk) pt0 cSend0 =
      some (some (stA2_cli withOpk, wire0 withOpk)) := by
  cases withOpk <;> exact eq_of_decReprOut (by decide +kernel)

theorem markKyberUsed_stB0 (withOpk : Bool) :
    markKyberUsed (stB0_cli withOpk) (pkMsg0 withOpk) =
      some (stB0Marked withOpk) := by
  cases withOpk
  · have hko : (stB0_cli false).kyberOneTime.lookup (pkMsg0 false).kpkId = none := rfl
    have hlr : (stB0_cli false).kyberLastResort.lookup (pkMsg0 false).kpkId =
        some (⟨myKyberPub1568, myKyberSec3168, mySigVec, 0⟩, []) := rfl
    unfold markKyberUsed
    rw [hko, hlr]
    simp only [List.not_mem_nil]
    rfl
  · have hko : (stB0_cli true).kyberOneTime.lookup (pkMsg0 true).kpkId = none := rfl
    have hlr : (stB0_cli true).kyberLastResort.lookup (pkMsg0 true).kpkId =
        some (⟨myKyberPub1568, myKyberSec3168, mySigVec, 0⟩, []) := rfl
    unfold markKyberUsed
    rw [hko, hlr]
    simp only [List.not_mem_nil]
    rfl

theorem recvStep_eq (withOpk : Bool) :
    pqRecvPrekeyModel nvX myParams (stB0_cli withOpk) (pkMsg0 withOpk) (rcVal withOpk) =
      some (some (stB1_cli withOpk, pt0)) := by
  rw [pqRecvPrekeyModel_eq_fast _ _ _ withOpk rfl]
  unfold pqRecvPrekeyModelFast
  rw [markKyberUsed_stB0]
  cases withOpk <;> exact eq_of_decReprOut (by decide +kernel)

theorem recvStep_eq_any (X : UnreachedPqxdhPrimitives) (withOpk : Bool) :
    pqRecvPrekeyModel X myParams (stB0_cli withOpk) (pkMsg0 withOpk) (rcVal withOpk) =
      some (some (stB1_cli withOpk, pt0)) := by
  rw [pqRecvPrekeyModel_congr_extras X nvX]
  exact recvStep_eq withOpk

/-! ## Domain Well-Formedness (`PqxdhPartyInSpecDomain`) -/

theorem wfPq_stA0 (withOpk : Bool) : PqxdhPartyInSpecDomain myParams (stA0_cli withOpk) := by
  have hcap : ∀ f ∈ encodeDir myParams (stA0_cli withOpk),
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
    cases withOpk <;>
      (unfold encodeDir CryptoVerification.SignalSession.fileCapBytes
       dsimp only [stA0_cli, List.map]; rw [keyPair_idA]; decide +kernel)
  have hfiles : ∀ f ∈ encodeDir myParams (stA0_cli withOpk),
      f.2.length < 2 ^ 31 ∧
        ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
          f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) :=
    fun f hf => ⟨by have h := hcap f hf; unfold CryptoVerification.SignalSession.fileCapBytes at h; omega,
      fun _ => hcap f hf⟩
  refine ⟨(fun _ _ hs => by cases withOpk <;> cases hs), hfiles, (by cases withOpk <;> decide),
    (by cases withOpk <;> decide), (by cases withOpk <;> decide), (by cases withOpk <;> decide)⟩

theorem wfPq_stB0 (withOpk : Bool) : PqxdhPartyInSpecDomain myParams (stB0_cli withOpk) := by
  have hcap : ∀ f ∈ encodeDir myParams (stB0_cli withOpk),
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
    cases withOpk
    · unfold encodeDir signedRecordBytes CryptoVerification.SignalSession.fileCapBytes
      dsimp only [stB0_cli, List.map]
      rw [keyPair_idB, keyPair_spkB]
      decide +kernel
    · unfold encodeDir signedRecordBytes oneTimeRecordBytes CryptoVerification.SignalSession.fileCapBytes
      dsimp only [stB0_cli]
      simp only [↓reduceIte, List.map]
      rw [keyPair_idB, keyPair_spkB, keyPair_opkB]
      decide +kernel
  have hfiles : ∀ f ∈ encodeDir myParams (stB0_cli withOpk),
      f.2.length < 2 ^ 31 ∧
        ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
          f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) :=
    fun f hf => ⟨by have h := hcap f hf; unfold CryptoVerification.SignalSession.fileCapBytes at h; omega,
      fun _ => hcap f hf⟩
  refine ⟨(fun _ _ hs => by cases withOpk <;> cases hs), hfiles, (by cases withOpk <;> decide),
    (by cases withOpk <;> decide), (by cases withOpk <;> decide), (by cases withOpk <;> decide)⟩

private theorem reachPq_gA1 (withOpk : Bool) :
    ReachablePqxdhSession myParams (stA0_cli withOpk).me (x_A withOpk) (g_A1 withOpk) := by
  have h1 := initStep_eq withOpk
  unfold pqInitModel at h1
  have htr : (stA0_cli withOpk).trusts ⟨⟨(bE_cli withOpk).idPub⟩⟩ = true := by
    cases withOpk <;> rfl
  have hpA : (stA0_cli withOpk).party = .A := rfl
  rw [htr, hpA] at h1
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
  cases hi : initiateState nvX myParams .A (stA0_cli withOpk).me (bE_cli withOpk) (tapeInit withOpk) with
  | none => rw [hi] at h1; cases h1
  | some xg =>
    rcases xg with ⟨x0, g0⟩
    rw [hi] at h1
    have hst := (Prod.mk.inj (Option.some.inj (Option.some.inj h1))).1
    have hsess : some (x0, g0) = some (x_A withOpk, g_A1 withOpk) := congrArg PqParty.session hst
    rcases Prod.mk.inj (Option.some.inj hsess) with ⟨rfl, rfl⟩
    exact ReachablePqxdhSession.initiate nvX .A (stA0_cli withOpk).me (bE_cli withOpk) (tapeInit withOpk)
      (x_A withOpk) (g_A1 withOpk) hi

theorem wfPq_stA1 (withOpk : Bool) : PqxdhPartyInSpecDomain myParams (stA1_cli withOpk) := by
  have hcap : ∀ f ∈ encodeDir myParams (stA1_cli withOpk),
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
    cases withOpk <;>
      (unfold encodeDir CryptoVerification.SignalSession.fileCapBytes
       dsimp only [stA1_cli, stA0_cli, List.map]; rw [keyPair_idA]; decide +kernel)
  have hfiles : ∀ f ∈ encodeDir myParams (stA1_cli withOpk),
      f.2.length < 2 ^ 31 ∧
        ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
          f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) :=
    fun f hf => ⟨by have h := hcap f hf; unfold CryptoVerification.SignalSession.fileCapBytes at h; omega,
      fun _ => hcap f hf⟩
  refine ⟨?_, hfiles, by cases withOpk <;> decide, by cases withOpk <;> decide,
    by cases withOpk <;> decide, by cases withOpk <;> decide⟩
  rintro x g hs
  have hsess0 : (stA1_cli withOpk).session = some (x_A withOpk, g_A1 withOpk) := rfl
  rw [hsess0] at hs
  rcases Prod.mk.inj (Option.some.inj hs) with ⟨rfl, rfl⟩
  have hmem : (sessionFile (partyAddress (stA1_cli withOpk).party.other),
      encodeRecordUnderExtras (fun _ => x_A withOpk) (g_A1 withOpk)) ∈
      encodeDir myParams (stA1_cli withOpk) := by
    unfold encodeDir; simp [hsess0]
  exact ⟨⟨g_A1 withOpk, reachPq_gA1 withOpk, rfl, rfl⟩, rfl, (hfiles _ hmem).1⟩

private theorem send_gA1_eq (withOpk : Bool) :
    ((pqxdhSessionParams myParams).send (g_A1 withOpk) pt0 cSend0).1.party = (g_A2 withOpk).party ∧
    ((pqxdhSessionParams myParams).send (g_A1 withOpk) pt0 cSend0).1.session = (g_A2 withOpk).session := by
  cases withOpk <;> exact ⟨by decide +kernel, by decide +kernel⟩

theorem wfPq_stA2 (withOpk : Bool) : PqxdhPartyInSpecDomain myParams (stA2_cli withOpk) := by
  have hcap : ∀ f ∈ encodeDir myParams (stA2_cli withOpk),
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
    cases withOpk <;>
      (unfold encodeDir CryptoVerification.SignalSession.fileCapBytes
       dsimp only [stA2_cli, stA0_cli, List.map]; rw [keyPair_idA]; decide +kernel)
  have hfiles : ∀ f ∈ encodeDir myParams (stA2_cli withOpk),
      f.2.length < 2 ^ 31 ∧
        ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
          f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) :=
    fun f hf => ⟨by have h := hcap f hf; unfold CryptoVerification.SignalSession.fileCapBytes at h; omega,
      fun _ => hcap f hf⟩
  refine ⟨?_, hfiles, by cases withOpk <;> decide, by cases withOpk <;> decide,
    by cases withOpk <;> decide, by cases withOpk <;> decide⟩
  rintro x g hs
  have hsess2 : (stA2_cli withOpk).session = some (x_A withOpk, g_A2 withOpk) := rfl
  rw [hsess2] at hs
  rcases Prod.mk.inj (Option.some.inj hs) with ⟨rfl, rfl⟩
  have hrec1 : (encodeRecordUnderExtras (fun _ => x_A withOpk) (g_A1 withOpk)).length < 2 ^ 31 :=
    ((wfPq_stA1 withOpk).1 (x_A withOpk) (g_A1 withOpk) rfl).2.2
  have hR2 := ReachablePqxdhSession.send pt0 cSend0 (reachPq_gA1 withOpk) hrec1
  obtain ⟨hp0, hs0⟩ := send_gA1_eq withOpk
  have hmem : (sessionFile (partyAddress (stA2_cli withOpk).party.other),
      encodeRecordUnderExtras (fun _ => x_A withOpk) (g_A2 withOpk)) ∈
      encodeDir myParams (stA2_cli withOpk) := by
    unfold encodeDir; simp [hsess2]
  exact ⟨⟨((pqxdhSessionParams myParams).send (g_A1 withOpk) pt0 cSend0).1, hR2, hp0, hs0⟩,
    rfl, (hfiles _ hmem).1⟩

theorem wfPq_stB1 (withOpk : Bool) : PqxdhPartyInSpecDomain myParams (stB1_cli withOpk) := by
  have hcap : ∀ f ∈ encodeDir myParams (stB1_cli withOpk),
      f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
    cases withOpk <;>
      (unfold encodeDir signedRecordBytes CryptoVerification.SignalSession.fileCapBytes
       dsimp only [stB1_cli, stB0Marked, stB0_cli, ↓reduceIte, List.map]
       rw [keyPair_idB, keyPair_spkB]
       decide +kernel)
  have hfiles : ∀ f ∈ encodeDir myParams (stB1_cli withOpk),
      f.2.length < 2 ^ 31 ∧
        ((∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) →
          f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes) :=
    fun f hf => ⟨by have h := hcap f hf; unfold CryptoVerification.SignalSession.fileCapBytes at h; omega,
      fun _ => hcap f hf⟩
  refine ⟨?_, hfiles, by cases withOpk <;> decide, by cases withOpk <;> decide,
    by cases withOpk <;> decide, by cases withOpk <;> decide⟩
  rintro x g hs
  have hsess1 : (stB1_cli withOpk).session = some (x_B withOpk, g_B1 withOpk) := rfl
  rw [hsess1] at hs
  rcases Prod.mk.inj (Option.some.inj hs) with ⟨rfl, rfl⟩
  have hr := recvStep_eq withOpk
  unfold pqRecvPrekeyModel at hr
  cases htry : SignalMessage.tryFrom protoSignalCodec (pkMsg0 withOpk).inner with
  | error _ => rw [htry] at hr; cases hr
  | ok _ =>
    rw [htry] at hr
    have htr : (stB0_cli withOpk).trusts ⟨⟨(pkMsg0 withOpk).idPub⟩⟩ = true := by
      cases withOpk <;> rfl
    have hs0 : (stB0_cli withOpk).session = none := rfl
    dsimp only at hr; rw [htr, hs0] at hr
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
    cases hk : preKeysNamedBy (stB0_cli withOpk) (pkMsg0 withOpk) with
    | none => rw [hk] at hr; cases hr
    | some k =>
      rw [hk] at hr; dsimp only at hr
      cases hrs : recvPrekeyState nvX myParams (stB0_cli withOpk).party (stB0_cli withOpk).me
          k (pkMsg0 withOpk) (rcVal withOpk) with
      | none => rw [hrs] at hr; cases hr
      | some o =>
        cases o with
        | none => rw [hrs] at hr; cases hr
        | some xgp =>
          rcases xgp with ⟨x0, g0, pt'⟩
          rw [hrs, markKyberUsed_stB0] at hr
          have hst := (Prod.mk.inj (Option.some.inj (Option.some.inj hr))).1
          have hpair : some (x0, g0) = some (x_B withOpk, g_B1 withOpk) :=
            congrArg PqParty.session hst
          rcases Prod.mk.inj (Option.some.inj hpair) with ⟨rfl, rfl⟩
          have hmem : (sessionFile (partyAddress (stB1_cli withOpk).party.other),
              encodeRecordUnderExtras (fun _ => x_B withOpk) (g_B1 withOpk)) ∈
              encodeDir myParams (stB1_cli withOpk) := by
            unfold encodeDir; simp [hsess1]
          exact ⟨⟨g_B1 withOpk, ReachablePqxdhSession.recvPrekey nvX (stB0_cli withOpk).party
              (stB0_cli withOpk).me k (pkMsg0 withOpk) (rcVal withOpk)
              (x_B withOpk) (g_B1 withOpk) pt' hrs,
              rfl, rfl⟩, rfl, (hfiles _ hmem).1⟩

end Symbolic.Proofs.Tests.CliNonvacuity.HandshakeModel

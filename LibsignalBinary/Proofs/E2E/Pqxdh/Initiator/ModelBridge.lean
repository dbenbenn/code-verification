/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhModelLink
import LibsignalBinary.Proofs.CodeLayout

/-!
# Bridge Between `Initiator` Protocol Model and `SignalPqxdh` Specifications

Equivalences and type conversions connecting the `Initiator.*` protocol model (`HandshakeDerive`)
under `ResponderCore.ofSignalPqxdhPrimitives` with `SignalPqxdh.*`:
- Lifts `SignalPqxdh.WellFormedPrimitives` to `Initiator.StructuralPrims` and discharges
  `StructuralPrims (initiatorModelPrims X W)` unconditionally.
- Establishes definitional and extensional agreement of the reference primitives and `Model.initiate*`
  / `Model.accept*` transitions.
- Proves `WellSized*` preservation and unconditional well-sizedness of `initiateInput` and
  `acceptInput`.
-/

public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.E2E.Pqxdh.Initiator

open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderCore

/-! ## 1. Pure Byte & Encoding Definitional Equalities (`Initiator.* = SignalPqxdh.*`) -/

@[simp] theorem INFO_PQXDH_eq : INFO_PQXDH = SignalPqxdh.INFO_PQXDH := rfl
@[simp] theorem INFO_RATCHET_eq : INFO_RATCHET = SignalPqxdh.INFO_RATCHET := rfl
@[simp] theorem INFO_MSG_KEYS_eq : INFO_MSG_KEYS = SignalPqxdh.INFO_MSG_KEYS := rfl
@[simp] theorem F_X25519_eq : F_X25519 = SignalPqxdh.F_X25519 := rfl

@[simp] theorem encodeEC_eq (pk32 : Bytes) : encodeEC pk32 = SignalPqxdh.encodeEC pk32 := rfl
@[simp] theorem encodeKEM_eq (pk1568 : Bytes) :
    encodeKEM pk1568 = SignalPqxdh.encodeKEM pk1568 := rfl
@[simp] theorem decodeEC_eq (bs : Bytes) : decodeEC bs = SignalPqxdh.decodeEC bs := rfl
@[simp] theorem decodeKEM_eq (bs : Bytes) : decodeKEM bs = SignalPqxdh.decodeKEM bs := rfl

@[simp] theorem buildSecrets_eq (dh1 dh2 dh3 : Bytes) (dh4? : Option Bytes) (ss : Bytes) :
    buildSecrets dh1 dh2 dh3 dh4? ss = SignalPqxdh.buildSecrets dh1 dh2 dh3 dh4? ss := rfl

@[simp] theorem firstMsgAD_eq (ikA ikB ephAPk pqRatchetMsg : Bytes) :
    firstMsgAD ikA ikB ephAPk pqRatchetMsg =
      SignalPqxdh.firstMsgAD ikA ikB ephAPk pqRatchetMsg := rfl

@[simp] theorem dhOptNonZero_eq (dh? : Option Bytes) :
    dhOptNonZero dh? = SignalPqxdh.dhOptNonZero dh? := rfl

@[simp] theorem scalarIsInRange_eq (pk : Bytes) :
    scalarIsInRange pk = SignalPqxdh.scalarIsInRange pk := rfl

@[simp] theorem fitBytesRef_eq (n : Nat) (bs : Bytes) :
    fitBytesRef n bs = SignalPqxdh.fitBytesRef n bs := rfl

@[simp] theorem fitBytes_eq (n : Nat) (bs : Bytes) :
    fitBytes n bs = SignalPqxdh.fitBytes n bs := rfl

@[simp] theorem clampScalar25519_eq (sk : Bytes) :
    clampScalar25519 sk = SignalPqxdh.clampScalar25519 sk := rfl

@[simp] theorem sha256InitState_eq : sha256InitState = SignalPqxdh.sha256InitState := rfl
@[simp] theorem sha512InitState_eq : sha512InitState = SignalPqxdh.sha512InitState := rfl

@[simp] theorem encodeBitLen64BE_eq (byteLen : Nat) :
    encodeBitLen64BE byteLen = SignalPqxdh.encodeBitLen64BE byteLen := rfl

@[simp] theorem encodeBitLen128BE_eq (byteLen : Nat) :
    encodeBitLen128BE byteLen = SignalPqxdh.encodeBitLen128BE byteLen := rfl

@[simp] theorem sha256Pad_eq (msg : Bytes) : sha256Pad msg = SignalPqxdh.sha256Pad msg := rfl
@[simp] theorem sha512Pad_eq (msg : Bytes) : sha512Pad msg = SignalPqxdh.sha512Pad msg := rfl

@[simp] theorem chunkBlocks_eq (blockSize : Nat) (bs : Bytes) :
    chunkBlocks blockSize bs = SignalPqxdh.chunkBlocks blockSize bs := rfl

@[simp] theorem xorBytes_eq (a b : Bytes) : xorBytes a b = SignalPqxdh.xorBytes a b := rfl
@[simp] theorem pkcs7Pad16_eq (pt : Bytes) : pkcs7Pad16 pt = SignalPqxdh.pkcs7Pad16 pt := rfl
@[simp] theorem pkcs7Unpad16_eq (padded : Bytes) :
    pkcs7Unpad16 padded = SignalPqxdh.pkcs7Unpad16 padded := rfl

@[simp] theorem toBlocks16_eq (bs : Bytes) : toBlocks16 bs = SignalPqxdh.toBlocks16 bs := by
  induction bs using toBlocks16.induct with
  | case1 bs hge ih =>
    rw [toBlocks16, SignalPqxdh.toBlocks16]
    simp [hge, ih]
  | case2 bs hlt =>
    rw [toBlocks16, SignalPqxdh.toBlocks16]
    simp [hlt]

@[simp] theorem fromBlocks16_eq (blks : List Bytes) :
    fromBlocks16 blks = SignalPqxdh.fromBlocks16 blks := rfl

@[simp] theorem cbcEncBlocksWith_eq (aesEnc : Bytes → Bytes → Bytes) (key iv : Bytes)
    (blks : List Bytes) :
    cbcEncBlocksWith aesEnc key iv blks = SignalPqxdh.cbcEncBlocksWith aesEnc key iv blks := by
  induction blks generalizing iv with
  | nil => rfl
  | cons ptBlk rest ih =>
    simp only [cbcEncBlocksWith, SignalPqxdh.cbcEncBlocksWith, fitBytesRef_eq, xorBytes_eq, ih]

@[simp] theorem cbcDecBlocksWith_eq (aesDec : Bytes → Bytes → Bytes) (key iv : Bytes)
    (blks : List Bytes) :
    cbcDecBlocksWith aesDec key iv blks = SignalPqxdh.cbcDecBlocksWith aesDec key iv blks := by
  induction blks generalizing iv with
  | nil => rfl
  | cons ctBlk rest ih =>
    simp only [cbcDecBlocksWith, SignalPqxdh.cbcDecBlocksWith, fitBytesRef_eq, xorBytes_eq, ih]

/-! ## 2. Structure Conversions (`Initiator.* ↔ SignalPqxdh.*`) -/

@[expose] def ofSignalPqxdhDRKey (dk : SignalPqxdh.DRKey) : DRKey :=
  ⟨dk.rootKey, dk.chainKey, dk.pqrKey⟩

@[expose] def toSignalPqxdhDRKey (dk : DRKey) : SignalPqxdh.DRKey :=
  ⟨dk.rootKey, dk.chainKey, dk.pqrKey⟩

@[simp] theorem toSignalPqxdhDRKey_ofSignalPqxdhDRKey (dk : SignalPqxdh.DRKey) :
    toSignalPqxdhDRKey (ofSignalPqxdhDRKey dk) = dk := by
  cases dk; rfl

@[simp] theorem ofSignalPqxdhDRKey_toSignalPqxdhDRKey (dk : DRKey) :
    ofSignalPqxdhDRKey (toSignalPqxdhDRKey dk) = dk := by
  cases dk; rfl

@[simp] theorem ofSignalPqxdhDRKey_toBytes96 (dk : SignalPqxdh.DRKey) :
    DRKey.toBytes96 (ofSignalPqxdhDRKey dk) = dk.toBytes96 := rfl

@[expose] def ofSignalPqxdhMessageKeys (mk : SignalPqxdh.MessageKeys) : MessageKeys :=
  ⟨mk.cipherKey, mk.macKey, mk.iv⟩

@[expose] def toSignalPqxdhMessageKeys (mk : MessageKeys) : SignalPqxdh.MessageKeys :=
  ⟨mk.cipherKey, mk.macKey, mk.iv⟩

@[simp] theorem toSignalPqxdhMessageKeys_ofSignalPqxdhMessageKeys (mk : SignalPqxdh.MessageKeys) :
    toSignalPqxdhMessageKeys (ofSignalPqxdhMessageKeys mk) = mk := by
  cases mk; rfl

@[simp] theorem ofSignalPqxdhMessageKeys_toSignalPqxdhMessageKeys (mk : MessageKeys) :
    ofSignalPqxdhMessageKeys (toSignalPqxdhMessageKeys mk) = mk := by
  cases mk; rfl

@[expose] def ofSignalPqxdhBundle (b : SignalPqxdh.PreKeyBundleInput) : PreKeyBundleInput where
  ikB      := b.ikB
  spkId    := b.spkId
  spkB     := b.spkB
  spkSig   := b.spkSig
  opkB?    := b.opkB?
  pqspkId  := b.pqspkId
  pqspkB   := b.pqspkB
  pqspkSig := b.pqspkSig

def toSignalPqxdhBundle (b : PreKeyBundleInput) : SignalPqxdh.PreKeyBundleInput where
  ikB      := b.ikB
  spkId    := b.spkId
  spkB     := b.spkB
  spkSig   := b.spkSig
  opkB?    := b.opkB?
  pqspkId  := b.pqspkId
  pqspkB   := b.pqspkB
  pqspkSig := b.pqspkSig

@[simp] theorem toSignalPqxdhBundle_ofSignalPqxdhBundle (b : SignalPqxdh.PreKeyBundleInput) :
    toSignalPqxdhBundle (ofSignalPqxdhBundle b) = b := by
  cases b; rfl

@[simp] theorem ofSignalPqxdhBundle_toSignalPqxdhBundle (b : PreKeyBundleInput) :
    ofSignalPqxdhBundle (toSignalPqxdhBundle b) = b := by
  cases b; rfl

@[expose] def ofSignalPqxdhHdr (h : SignalPqxdh.HandshakeHdr) : HandshakeHdr where
  ikAPk   := h.ikAPk
  ekAPk   := h.ekAPk
  spkId   := h.spkId
  opkId?  := h.opkId?
  pqspkId := h.pqspkId
  kemCt   := h.kemCt

def toSignalPqxdhHdr (h : HandshakeHdr) : SignalPqxdh.HandshakeHdr where
  ikAPk   := h.ikAPk
  ekAPk   := h.ekAPk
  spkId   := h.spkId
  opkId?  := h.opkId?
  pqspkId := h.pqspkId
  kemCt   := h.kemCt

@[simp] theorem toSignalPqxdhHdr_ofSignalPqxdhHdr (h : SignalPqxdh.HandshakeHdr) :
    toSignalPqxdhHdr (ofSignalPqxdhHdr h) = h := by
  cases h; rfl

@[simp] theorem ofSignalPqxdhHdr_toSignalPqxdhHdr (h : HandshakeHdr) :
    ofSignalPqxdhHdr (toSignalPqxdhHdr h) = h := by
  cases h; rfl

def ofSignalPqxdhPreKeyMsg (m : SignalPqxdh.PreKeyMsg) : PreKeyMsg where
  hdr          := ofSignalPqxdhHdr m.hdr
  ephAPk       := m.ephAPk
  pqRatchetMsg := m.pqRatchetMsg
  aeadCt       := m.aeadCt

def toSignalPqxdhPreKeyMsg (m : PreKeyMsg) : SignalPqxdh.PreKeyMsg where
  hdr          := toSignalPqxdhHdr m.hdr
  ephAPk       := m.ephAPk
  pqRatchetMsg := m.pqRatchetMsg
  aeadCt       := m.aeadCt

@[simp] theorem toSignalPqxdhPreKeyMsg_ofSignalPqxdhPreKeyMsg (m : SignalPqxdh.PreKeyMsg) :
    toSignalPqxdhPreKeyMsg (ofSignalPqxdhPreKeyMsg m) = m := by
  cases m; simp [toSignalPqxdhPreKeyMsg, ofSignalPqxdhPreKeyMsg]

@[simp] theorem ofSignalPqxdhPreKeyMsg_toSignalPqxdhPreKeyMsg (m : PreKeyMsg) :
    ofSignalPqxdhPreKeyMsg (toSignalPqxdhPreKeyMsg m) = m := by
  cases m; simp [toSignalPqxdhPreKeyMsg, ofSignalPqxdhPreKeyMsg]

@[expose] def ofSignalPqxdhInitiateKeysInput (inp : SignalPqxdh.InitiateKeysInput) : InitiateKeysInput where
  ikASk       := inp.ikASk
  ikAPk       := inp.ikAPk
  ekASk       := inp.ekASk
  kemCoins    := inp.kemCoins
  trustedPeer := inp.trustedPeer
  bundle      := ofSignalPqxdhBundle inp.bundle

def toSignalPqxdhInitiateKeysInput (inp : InitiateKeysInput) : SignalPqxdh.InitiateKeysInput where
  ikASk       := inp.ikASk
  ikAPk       := inp.ikAPk
  ekASk       := inp.ekASk
  kemCoins    := inp.kemCoins
  trustedPeer := inp.trustedPeer
  bundle      := toSignalPqxdhBundle inp.bundle

@[simp] theorem toSignalPqxdhInitiateKeysInput_ofSignalPqxdhInitiateKeysInput
    (inp : SignalPqxdh.InitiateKeysInput) :
    toSignalPqxdhInitiateKeysInput (ofSignalPqxdhInitiateKeysInput inp) = inp := by
  cases inp; simp [toSignalPqxdhInitiateKeysInput, ofSignalPqxdhInitiateKeysInput]

@[simp] theorem ofSignalPqxdhInitiateKeysInput_toSignalPqxdhInitiateKeysInput
    (inp : InitiateKeysInput) :
    ofSignalPqxdhInitiateKeysInput (toSignalPqxdhInitiateKeysInput inp) = inp := by
  cases inp; simp [toSignalPqxdhInitiateKeysInput, ofSignalPqxdhInitiateKeysInput]

def ofSignalPqxdhInitiateInput (inp : SignalPqxdh.InitiateInput) : InitiateInput where
  toInitiateKeysInput := ofSignalPqxdhInitiateKeysInput inp.toInitiateKeysInput
  ephASk              := inp.ephASk
  spqrCoins           := inp.spqrCoins
  plaintext           := inp.plaintext

def toSignalPqxdhInitiateInput (inp : InitiateInput) : SignalPqxdh.InitiateInput where
  toInitiateKeysInput := toSignalPqxdhInitiateKeysInput inp.toInitiateKeysInput
  ephASk              := inp.ephASk
  spqrCoins           := inp.spqrCoins
  plaintext           := inp.plaintext

@[simp] theorem toSignalPqxdhInitiateInput_ofSignalPqxdhInitiateInput
    (inp : SignalPqxdh.InitiateInput) :
    toSignalPqxdhInitiateInput (ofSignalPqxdhInitiateInput inp) = inp := by
  cases inp; simp [toSignalPqxdhInitiateInput, ofSignalPqxdhInitiateInput]

@[simp] theorem ofSignalPqxdhInitiateInput_toSignalPqxdhInitiateInput
    (inp : InitiateInput) :
    ofSignalPqxdhInitiateInput (toSignalPqxdhInitiateInput inp) = inp := by
  cases inp; simp [toSignalPqxdhInitiateInput, ofSignalPqxdhInitiateInput]

@[expose] def ofSignalPqxdhAcceptKeysInput (inp : SignalPqxdh.AcceptKeysInput) : AcceptKeysInput where
  ikBSk       := inp.ikBSk
  ikBPk       := inp.ikBPk
  spkBSk      := inp.spkBSk
  spkBPk      := inp.spkBPk
  opkBSk?     := inp.opkBSk?
  pqspkBSk    := inp.pqspkBSk
  pqspkBPk    := inp.pqspkBPk
  trustedPeer := inp.trustedPeer
  replayOk    := inp.replayOk
  hdr         := ofSignalPqxdhHdr inp.hdr

def toSignalPqxdhAcceptKeysInput (inp : AcceptKeysInput) : SignalPqxdh.AcceptKeysInput where
  ikBSk       := inp.ikBSk
  ikBPk       := inp.ikBPk
  spkBSk      := inp.spkBSk
  spkBPk      := inp.spkBPk
  opkBSk?     := inp.opkBSk?
  pqspkBSk    := inp.pqspkBSk
  pqspkBPk    := inp.pqspkBPk
  trustedPeer := inp.trustedPeer
  replayOk    := inp.replayOk
  hdr         := toSignalPqxdhHdr inp.hdr

@[simp] theorem toSignalPqxdhAcceptKeysInput_ofSignalPqxdhAcceptKeysInput
    (inp : SignalPqxdh.AcceptKeysInput) :
    toSignalPqxdhAcceptKeysInput (ofSignalPqxdhAcceptKeysInput inp) = inp := by
  cases inp; simp [toSignalPqxdhAcceptKeysInput, ofSignalPqxdhAcceptKeysInput]

@[simp] theorem ofSignalPqxdhAcceptKeysInput_toSignalPqxdhAcceptKeysInput
    (inp : AcceptKeysInput) :
    ofSignalPqxdhAcceptKeysInput (toSignalPqxdhAcceptKeysInput inp) = inp := by
  cases inp; simp [toSignalPqxdhAcceptKeysInput, ofSignalPqxdhAcceptKeysInput]

def ofSignalPqxdhAcceptInput (inp : SignalPqxdh.AcceptInput) : AcceptInput where
  keysInp := ofSignalPqxdhAcceptKeysInput inp.keysInp
  msg     := ofSignalPqxdhPreKeyMsg inp.msg

def toSignalPqxdhAcceptInput (inp : AcceptInput) : SignalPqxdh.AcceptInput where
  keysInp := toSignalPqxdhAcceptKeysInput inp.keysInp
  msg     := toSignalPqxdhPreKeyMsg inp.msg

@[simp] theorem toSignalPqxdhAcceptInput_ofSignalPqxdhAcceptInput
    (inp : SignalPqxdh.AcceptInput) :
    toSignalPqxdhAcceptInput (ofSignalPqxdhAcceptInput inp) = inp := by
  cases inp; simp [toSignalPqxdhAcceptInput, ofSignalPqxdhAcceptInput]

@[simp] theorem ofSignalPqxdhAcceptInput_toSignalPqxdhAcceptInput
    (inp : AcceptInput) :
    ofSignalPqxdhAcceptInput (toSignalPqxdhAcceptInput inp) = inp := by
  cases inp; simp [toSignalPqxdhAcceptInput, ofSignalPqxdhAcceptInput]

/-! ## 3. Reference & Primitive Function Bridges (`ofSignalPqxdhPrimitives P`) -/

@[simp] theorem sha256Step_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) :
    sha256Step (ofSignalPqxdhPrimitives P) = SignalPqxdh.sha256Step P := rfl

@[simp] theorem sha512Step_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) :
    sha512Step (ofSignalPqxdhPrimitives P) = SignalPqxdh.sha512Step P := rfl

@[simp] theorem sha256Ref_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (msg : Bytes) :
    sha256Ref (ofSignalPqxdhPrimitives P) msg = SignalPqxdh.sha256Ref P msg := rfl

@[simp] theorem sha512Ref_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (msg : Bytes) :
    sha512Ref (ofSignalPqxdhPrimitives P) msg = SignalPqxdh.sha512Ref P msg := rfl

@[simp] theorem hmacSha256Ref_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (key msg : Bytes) :
    hmacSha256Ref (ofSignalPqxdhPrimitives P) key msg =
      SignalPqxdh.hmacSha256Ref P key msg := rfl

@[simp] theorem hkdfExtractRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (salt? : Option Bytes) (ikm : Bytes) :
    hkdfExtractRef (ofSignalPqxdhPrimitives P) salt? ikm =
      SignalPqxdh.hkdfExtractRef P salt? ikm := rfl

@[simp] theorem hkdfExpand96Ref_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (prk info : Bytes) :
    hkdfExpand96Ref (ofSignalPqxdhPrimitives P) prk info =
      ofSignalPqxdhDRKey (SignalPqxdh.hkdfExpand96Ref P prk info) := rfl

@[simp] theorem hkdfDerive96Ref_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (secrets : Bytes) :
    hkdfDerive96Ref (ofSignalPqxdhPrimitives P) secrets =
      ofSignalPqxdhDRKey (SignalPqxdh.hkdfDerive96Ref P secrets) := rfl

@[simp] theorem hkdfDerive96_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (secrets : Bytes) :
    (ofSignalPqxdhPrimitives P).hkdfDerive96 secrets =
      ofSignalPqxdhDRKey (P.hkdfDerive96 secrets) := rfl

@[simp] theorem rootCreateChainRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (rk dhRatchet : Bytes) :
    rootCreateChainRef (ofSignalPqxdhPrimitives P) rk dhRatchet =
      SignalPqxdh.rootCreateChainRef P rk dhRatchet := rfl

@[simp] theorem rootCreateChain_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (rk dhRatchet : Bytes) :
    (ofSignalPqxdhPrimitives P).rootCreateChain rk dhRatchet =
      P.rootCreateChain rk dhRatchet := rfl

@[simp] theorem chainKdfSeedRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (ck : Bytes) :
    chainKdfSeedRef (ofSignalPqxdhPrimitives P) ck = SignalPqxdh.chainKdfSeedRef P ck := rfl

@[simp] theorem chainKdfSeed_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (ck : Bytes) :
    (ofSignalPqxdhPrimitives P).chainKdfSeed ck = P.chainKdfSeed ck := rfl

@[simp] theorem chainKdfNextRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (ck : Bytes) :
    chainKdfNextRef (ofSignalPqxdhPrimitives P) ck = SignalPqxdh.chainKdfNextRef P ck := rfl

@[simp] theorem chainKdfNext_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) (ck : Bytes) :
    (ofSignalPqxdhPrimitives P).chainKdfNext ck = P.chainKdfNext ck := rfl

@[simp] theorem deriveMsgKeysRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mkSeed : Bytes) (spqrSalt? : Option Bytes) :
    deriveMsgKeysRef (ofSignalPqxdhPrimitives P) mkSeed spqrSalt? =
      ofSignalPqxdhMessageKeys (SignalPqxdh.deriveMsgKeysRef P mkSeed spqrSalt?) := rfl

@[simp] theorem deriveMsgKeys_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mkSeed : Bytes) (spqrSalt? : Option Bytes) :
    (ofSignalPqxdhPrimitives P).deriveMsgKeys mkSeed spqrSalt? =
      ofSignalPqxdhMessageKeys (P.deriveMsgKeys mkSeed spqrSalt?) := rfl

@[simp] theorem cbcEncBlocks_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (key iv : Bytes) (blks : List Bytes) :
    cbcEncBlocks (ofSignalPqxdhPrimitives P) key iv blks =
      SignalPqxdh.cbcEncBlocks P key iv blks :=
  cbcEncBlocksWith_eq P.aesEncBlock key iv blks

@[simp] theorem cbcDecBlocks_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (key iv : Bytes) (blks : List Bytes) :
    cbcDecBlocks (ofSignalPqxdhPrimitives P) key iv blks =
      SignalPqxdh.cbcDecBlocks P key iv blks :=
  cbcDecBlocksWith_eq P.aesDecBlock key iv blks

@[simp] theorem aes256CbcEncRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (key iv pt : Bytes) :
    aes256CbcEncRef (ofSignalPqxdhPrimitives P) key iv pt =
      SignalPqxdh.aes256CbcEncRef P key iv pt := by
  simp [aes256CbcEncRef, SignalPqxdh.aes256CbcEncRef, cbcEncBlocks, SignalPqxdh.cbcEncBlocks,
    ofSignalPqxdhPrimitives]

@[simp] theorem aes256CbcDecRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (key iv ct : Bytes) :
    aes256CbcDecRef (ofSignalPqxdhPrimitives P) key iv ct =
      SignalPqxdh.aes256CbcDecRef P key iv ct := by
  simp [aes256CbcDecRef, SignalPqxdh.aes256CbcDecRef, cbcDecBlocks, SignalPqxdh.cbcDecBlocks,
    ofSignalPqxdhPrimitives]

@[simp] theorem aes256CbcHmacEncRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mk : MessageKeys) (ad pt : Bytes) :
    aes256CbcHmacEncRef (ofSignalPqxdhPrimitives P) mk ad pt =
      SignalPqxdh.aes256CbcHmacEncRef P (toSignalPqxdhMessageKeys mk) ad pt := by
  simp [aes256CbcHmacEncRef, SignalPqxdh.aes256CbcHmacEncRef, toSignalPqxdhMessageKeys]

@[simp] theorem aes256CbcHmacDecRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mk : MessageKeys) (ad ctAndTag : Bytes) :
    aes256CbcHmacDecRef (ofSignalPqxdhPrimitives P) mk ad ctAndTag =
      SignalPqxdh.aes256CbcHmacDecRef P (toSignalPqxdhMessageKeys mk) ad ctAndTag := by
  simp [aes256CbcHmacDecRef, SignalPqxdh.aes256CbcHmacDecRef, toSignalPqxdhMessageKeys]

@[simp] theorem aeadEnc_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mk : MessageKeys) (ad pt : Bytes) :
    (ofSignalPqxdhPrimitives P).aeadEnc mk ad pt =
      P.aeadEnc (toSignalPqxdhMessageKeys mk) ad pt := rfl

@[simp] theorem aeadDec_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (mk : MessageKeys) (ad ct : Bytes) :
    (ofSignalPqxdhPrimitives P).aeadDec mk ad ct =
      P.aeadDec (toSignalPqxdhMessageKeys mk) ad ct := rfl

theorem xeddsaVerifyRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (hWF : Shared.StructuralPrims P) (pk m sig : Bytes) :
    xeddsaVerifyRef (ofSignalPqxdhPrimitives P) pk m sig =
      SignalPqxdh.xeddsaVerifyRef P pk m sig := by
  unfold xeddsaVerifyRef SignalPqxdh.xeddsaVerifyRef ofSignalPqxdhPrimitives
  dsimp only [_root_.SignalPqxdh.Primitives.montToEdBytes,
    _root_.SignalPqxdh.Primitives.compressBytes,
    _root_.SignalPqxdh.Primitives.edNegBytes,
    _root_.SignalPqxdh.Primitives.doubleScalarMulBasepointBytes]
  split
  · rcases hm : P.montToEd pk ((sig.getD 63 0 &&& 0x80) >>> 7) with _ | edPk
    · rfl
    · have hlt := hWF.montToEd_lt pk ((sig.getD 63 0 &&& 0x80) >>> 7) edPk hm
      have hneg := hWF.edNeg_lt edPk
      dsimp only [Option.map]
      rw [LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.unpackEdBytes_packEdBytes
          hlt.1 hlt.2]
      have hdsmb := hWF.doubleScalarMulBasepoint_lt
        (P.scalarFromWide (P.sha512 (sig.take 32 ++ P.compress edPk ++ m)))
        (P.edNeg edPk)
        (P.scalarFromBytesModOrder ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]))
      rw [LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.unpackEdBytes_packEdBytes
          hneg.1 hneg.2,
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.unpackEdBytes_packEdBytes
          hdsmb.1 hdsmb.2]
  · rfl

theorem isCanonicalRef_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (hWF : Shared.StructuralPrims P) (pk : Bytes) :
    isCanonicalRef (ofSignalPqxdhPrimitives P) pk =
      SignalPqxdh.isCanonicalRef P pk := by
  unfold isCanonicalRef SignalPqxdh.isCanonicalRef ofSignalPqxdhPrimitives
  dsimp only [_root_.SignalPqxdh.Primitives.montToEdBytes,
    _root_.SignalPqxdh.Primitives.isTorsionFreeBytes]
  rw [scalarIsInRange_eq]
  split
  · rcases hm : P.montToEd pk 0 with _ | edPt
    · rfl
    · have hlt := hWF.montToEd_lt pk 0 edPt hm
      dsimp only [Option.map]
      rw [LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.unpackEdBytes_packEdBytes
          hlt.1 hlt.2]
  · rfl

@[simp] theorem xeddsaVerifyRef_ofSignalPqxdhPrimitives_modelPrims
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk m sig : Bytes) :
    xeddsaVerifyRef (ofSignalPqxdhPrimitives (modelPrims X W)) pk m sig =
      SignalPqxdh.xeddsaVerifyRef (modelPrims X W) pk m sig :=
  xeddsaVerifyRef_ofSignalPqxdhPrimitives (modelPrims X W) (Shared.structuralPrims_modelPrims X W)
    pk m sig

@[simp] theorem isCanonicalRef_ofSignalPqxdhPrimitives_modelPrims
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk : Bytes) :
    isCanonicalRef (ofSignalPqxdhPrimitives (modelPrims X W)) pk =
      SignalPqxdh.isCanonicalRef (modelPrims X W) pk :=
  isCanonicalRef_ofSignalPqxdhPrimitives (modelPrims X W) (Shared.structuralPrims_modelPrims X W) pk

/-! ## 4. Protocol Model Function Bridges (`Model.initiateKeys`, `Model.acceptKeys`,
  `Model.initiate`, `Model.accept`) -/

@[simp] private theorem option_map_bind' {α β γ : Type _}
    (x : Option α) (g : α → Option β) (f : β → γ) :
    Option.map f (x >>= g) = x >>= (fun a => Option.map f (g a)) := by
  cases x <;> rfl

@[simp] private theorem option_map_option_bind {α β γ : Type _}
    (x : Option α) (g : α → Option β) (f : β → γ) :
    Option.map f (Option.bind x g) = Option.bind x (fun a => Option.map f (g a)) := by
  cases x <;> rfl

theorem Model.initiateKeys_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (inp : SignalPqxdh.InitiateKeysInput) :
    Model.initiateKeys (ofSignalPqxdhPrimitives P) (ofSignalPqxdhInitiateKeysInput inp) =
      (SignalPqxdh.Model.initiateKeys P inp).map
        (fun (dk, hdr) => (ofSignalPqxdhDRKey dk, ofSignalPqxdhHdr hdr)) := by
  unfold Model.initiateKeys SignalPqxdh.Model.initiateKeys
  dsimp only [ofSignalPqxdhPrimitives, ofSignalPqxdhInitiateKeysInput, ofSignalPqxdhBundle,
    encodeEC_eq, encodeKEM_eq, dhOptNonZero_eq, buildSecrets_eq]
  rcases hkem : P.kemEncaps inp.bundle.pqspkB inp.kemCoins with _ | ⟨ss, kemCt⟩ <;>
    (simp [hkem, «guard», _root_.guard, bind, Function.comp_def, ofSignalPqxdhDRKey,
      ofSignalPqxdhHdr]; try rfl)

/-- Typeclass witnessing that `P.kemDecaps` returns `none` outside `kyberCtLen` or `inp.hdr.kemCt`
    already has length `kyberCtLen` (satisfied automatically at `modelPrims X W` and at
    `acceptInput W me k m`). -/
class AcceptKeysGuard (P : SignalPqxdh.Primitives) (inp : SignalPqxdh.AcceptKeysInput) : Prop where
  guard_ok : inp.hdr.kemCt.length = SignalPqxdh.kyberCtLen ∨
    P.kemDecaps inp.pqspkBSk inp.hdr.kemCt = none

instance acceptKeysGuard_modelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (inp : SignalPqxdh.AcceptKeysInput) :
    AcceptKeysGuard (modelPrims X W) inp where
  guard_ok := by
    by_cases h : inp.hdr.kemCt.length = SignalPqxdh.kyberCtLen
    · exact Or.inl h
    · exact Or.inr (by simp [modelPrims, blockLevelPrims, h])

instance acceptKeysGuard_acceptInput (P : SignalPqxdh.Primitives)
    (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) :
    AcceptKeysGuard P (CryptoVerification.E2E.acceptInput W me k m) where
  guard_ok := Or.inl (by
    simp [CryptoVerification.E2E.acceptInput, e2e_vecU8_length, SignalPqxdh.kyberCtLen])

theorem Model.acceptKeys_ofSignalPqxdhPrimitives_of_guard (P : SignalPqxdh.Primitives)
    (inp : SignalPqxdh.AcceptKeysInput)
    (hg : inp.hdr.kemCt.length = SignalPqxdh.kyberCtLen ∨
      P.kemDecaps inp.pqspkBSk inp.hdr.kemCt = none) :
    Model.acceptKeys (ofSignalPqxdhPrimitives P) (ofSignalPqxdhAcceptKeysInput inp) =
      (SignalPqxdh.Model.acceptKeys P inp).map ofSignalPqxdhDRKey := by
  unfold Model.acceptKeys SignalPqxdh.Model.acceptKeys
  dsimp only [ofSignalPqxdhPrimitives, ofSignalPqxdhAcceptKeysInput, ofSignalPqxdhHdr,
    dhOptNonZero_eq, buildSecrets_eq]
  rcases hg with hlen | hnone
  · have hbeq : (inp.hdr.kemCt.length == SignalPqxdh.kyberCtLen) = true := beq_iff_eq.mpr hlen
    rcases inp.hdr.opkId? with _ | opkId <;>
      rcases inp.opkBSk? with _ | opkSk <;>
      rcases P.kemDecaps inp.pqspkBSk inp.hdr.kemCt with _ | ss <;>
      (simp [hbeq, «guard», _root_.guard, bind, Function.comp_def, ofSignalPqxdhDRKey]; try rfl)
  · by_cases hlen : inp.hdr.kemCt.length = SignalPqxdh.kyberCtLen
    · have hbeq : (inp.hdr.kemCt.length == SignalPqxdh.kyberCtLen) = true := beq_iff_eq.mpr hlen
      rcases inp.hdr.opkId? with _ | opkId <;>
        rcases inp.opkBSk? with _ | opkSk <;>
        (simp [hbeq, hnone, «guard», _root_.guard, bind, Function.comp_def, ofSignalPqxdhDRKey]; try rfl)
    · have hbeq : (inp.hdr.kemCt.length == SignalPqxdh.kyberCtLen) = false :=
        beq_eq_false_iff_ne.mpr hlen
      rcases inp.hdr.opkId? with _ | opkId <;>
        rcases inp.opkBSk? with _ | opkSk <;>
        (simp [hbeq, hnone, «guard», _root_.guard, bind, Function.comp_def, ofSignalPqxdhDRKey]; try rfl)

theorem Model.acceptKeys_ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives)
    (inp : SignalPqxdh.AcceptKeysInput) [hG : AcceptKeysGuard P inp] :
    Model.acceptKeys (ofSignalPqxdhPrimitives P) (ofSignalPqxdhAcceptKeysInput inp) =
      (SignalPqxdh.Model.acceptKeys P inp).map ofSignalPqxdhDRKey :=
  Model.acceptKeys_ofSignalPqxdhPrimitives_of_guard P inp hG.guard_ok

/-! ## 5. `StructuralPrims` Bridge and Unconditional `initiatorModelPrims` Properties -/

/-- Lift `Shared.StructuralPrims P` across `ofSignalPqxdhPrimitives P`. -/
theorem structuralPrims_of_shared (P : SignalPqxdh.Primitives)
    (hWF : Shared.StructuralPrims P) :
    StructuralPrims (ofSignalPqxdhPrimitives P) where
  sha256Compress_len := hWF.sha256Compress_len
  sha512Compress_len := hWF.sha512Compress_len
  aesEncBlock_len := hWF.aesEncBlock_len
  aesDecBlock_len := hWF.aesDecBlock_len
  sha512_eq_ref := hWF.sha512_eq_ref
  hkdfDerive96_eq_ref s := by simp [hWF.hkdfDerive96_eq_ref s]
  rootCreateChain_eq_ref := hWF.rootCreateChain_eq_ref
  chainKdfSeed_eq_ref := hWF.chainKdfSeed_eq_ref
  chainKdfNext_eq_ref := hWF.chainKdfNext_eq_ref
  deriveMsgKeys_eq_ref s salt := by simp [hWF.deriveMsgKeys_eq_ref s salt]
  aeadEnc_eq_ref mk ad pt := by simp [hWF.aeadEnc_eq_ref]
  aeadDec_eq_ref mk ad ct := by simp [hWF.aeadDec_eq_ref]
  sigVerify_eq_xeddsaVerifyRef pk m sig :=
    (hWF.sigVerify_eq_xeddsaVerifyRef pk m sig).trans
      (xeddsaVerifyRef_ofSignalPqxdhPrimitives P hWF pk m sig).symm
  isCanonical_eq_isCanonicalRef pk :=
    (hWF.isCanonical_eq_isCanonicalRef pk).trans
      (isCanonicalRef_ofSignalPqxdhPrimitives P hWF pk).symm
  x25519_len := hWF.x25519_len
  x25519Base_len := hWF.x25519Base_len
  sha512_len := hWF.sha512_len
  scalarFromBytesModOrder_len := hWF.scalarFromBytesModOrder_len
  scalarFromWide_len := hWF.scalarFromWide_len
  montToEd_len := P.montToEdBytes_len
  edNeg_len := P.edNegBytes_len
  doubleScalarMulBasepoint_len := P.doubleScalarMulBasepointBytes_len
  compress_len := P.compressBytes_len hWF.compress_len
  kemEncaps_isSome := hWF.kemEncaps_isSome
  kemEncaps_len := hWF.kemEncaps_len
  kemDecaps_isSome := hWF.kemDecaps_isSome
  kemDecaps_len := hWF.kemDecaps_len
  spqrInitSend_some := hWF.spqrInitSend_some

/-- `initiatorModelPrims X W = ofSignalPqxdhPrimitives (modelPrims X W)` unconditionally satisfies
    all 28 structural/reference properties of `StructuralPrims` for all `X` and `W`. -/
theorem structuralPrims_initiatorModelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    StructuralPrims (initiatorModelPrims X W) :=
  structuralPrims_of_shared (modelPrims X W) (Shared.structuralPrims_modelPrims X W)

/-! ## 6. `WellSized*` Bridges and Unconditional Proofs for `initiateInput` / `acceptInput` -/

/-- Well-sizedness predicate for `InitiateKeysInput` (the handshake-only subset of
`WellSizedInitiateInput`). -/
@[expose] def WellSizedInitiateKeysInput (inp : InitiateKeysInput) : Prop :=
  inp.ikASk.length = 32 ∧
  inp.ikAPk.length = 32 ∧
  inp.ekASk.length = 32 ∧
  inp.kemCoins.length = 32 ∧
  inp.bundle.ikB.length = 32 ∧
  inp.bundle.spkB.length = 32 ∧
  inp.bundle.spkSig.length = 64 ∧
  (∀ id pk, inp.bundle.opkB? = some (id, pk) → pk.length = 32) ∧
  inp.bundle.pqspkB.length = 1568 ∧
  inp.bundle.pqspkSig.length = 64

/-- Extend `InitiateKeysInput` to `InitiateInput` with Epoch-1 ratchet scalar `ephASk` (and dummy
    32-byte `spqrCoins` + empty `plaintext`, since `initialize_alice_session` only uses
    `ephASk`). -/
def InitiateKeysInput.withEphASk (inp : InitiateKeysInput) (ephASk : Bytes)
    (spqrCoins : Bytes := List.replicate 32 0) (plaintext : Bytes := []) : InitiateInput where
  toInitiateKeysInput := inp
  ephASk              := ephASk
  spqrCoins           := spqrCoins
  plaintext           := plaintext

end CryptoVerification.E2E.Pqxdh.Initiator

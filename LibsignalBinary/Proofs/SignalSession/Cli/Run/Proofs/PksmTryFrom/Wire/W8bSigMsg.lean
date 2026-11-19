/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bIdentKey -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailC
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SigMsg
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.IdentKey -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysPlacedSym

/-!
# Inner `SignalMessage` Decode in `PreKeySignalMessage::try_from`

Discharges the `+0x864` continuation (`PreKey864OkW`) across the `SignalMessage::try_from` call and
`Box<[u8]>` slice clone on the inner message field, branching into the `+0x8c0` success
continuation (`PreKey8c0OkW`), clone allocation failure (`+0xa68`), and decode error
(`PreKeySigMsgErrW`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

/-! ## Message length bound -/

theorem w8b_decodePreKey_message_length_le {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {msg : List (BitVec 8)} (hdec : Pksm.decodeProto bs = some m) (hmsg : m.message = some msg) :
    msg.length ≤ bs.length :=
  (decodeProto_field_length_le hdec).2.2.1 msg hmsg

/-! ## Frames and `+0x8c0` continuation -/

/-- Postcondition state at `+0x8c0` after decoding `SignalMessage` (`sp' + 176 .. 288` and
`msgHeapAt`) and cloning `b` into `clonePtr`. -/
@[expose] def w8bRowSPost (A : RustAlloc) (sp' clonePtr : BitVec 64) (b : List (BitVec 8))
    (innerMsg : SignalMessage) (msgG : SignalMessageGhost)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56) : SepProp :=
  ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
    ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
    ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
    ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
    ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
    ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
    ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
    ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
    ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
    ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
    ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
    msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
    boxU8Buf A clonePtr b

theorem w8b_memRegion120_split (sp' : BitVec 64) :
    memRegion (sp' + 176#64) 120 =
      memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 := by
  rw [show (120 : Nat) = 112 + 8 by decide,
    Prost.memRegion_split (sp' + 176#64) 112 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Separation-logic frame preserved across the `SignalMessage::try_from` call (`+0x864 → +0x878`). -/
@[expose] def w8bSigCallFrame (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik bytes : List (BitVec 8)) (ipk : PublicKey) : SepProp :=
  ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
    ((sp' + 144#64) ↦ₛ ipk.bytes.toList) ∗
    ((sp' + 12#64) ↦₃₂ p7.zeroExtend 32) ∗
    ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
    ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    memRegion (sp' + 64#64) 4 ∗
    ((sp' + 68#64) ↦₃₂ p8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
    ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
    spUnused112 sp' ∗
    ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ p31) ∗
    ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
    sevenBytesHeadAt (sp' + 136#64) p0 p1 p2 p3 p4 p5 p6 ∗
    kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ∗
    vecU8Rest A ikCap ikPtr ik ∗
    Wire.vecU8Buf A bkCap bkPtr bk ∗
    memRegion sp' 12 ∗ memRegion (sp' + 176#64) 120 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 432#64) 8 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ memRegion sret 248 ∗ (ptr ↦ₛ bytes)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

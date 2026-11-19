/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bSigMsg -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailC -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SigMsg
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWShared
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysPlacedSym

/-!
# `PreKeySignalMessage::try_from`: `SignalMessage::try_from` Error Continuation (`PreKeySigMsgErrW`)

Proves `preKeySigMsgErrW_proof` (`+0x864 → +0x878 → +0x9f0 → +0x504 → ret`) from
`preKey_sigMsg_call_864_to_878_from_ident_wpX`, `preKey_sigMsg_err_878_to_9f0_wpX`,
`ErrTailC.e_9f0_words2_wpE`, and `w8b_errTail_close`.
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
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

theorem w8b_memRegion120_split48 (sp' : BitVec 64) :
    memRegion (sp' + 176#64) 120 =
      memRegion (sp' + 176#64) 48 ∗ memRegion (sp' + 224#64) 72 := by
  rw [show (120 : Nat) = 48 + 72 by decide,
    Prost.memRegion_split (sp' + 176#64) 48 72 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem w8bSigErr_memRegion184_split (sp' : BitVec 64) :
    memRegion (sp' + 112#64) 184 =
      memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 176#64) 48 ∗ memRegion (sp' + 224#64) 72 := by
  rw [ProofLib.memRegion_split (sp' + 112#64) 32 152 (by decide),
    ProofLib.memRegion_split (sp' + 112#64 + 32#64) 32 120 (by decide),
    ProofLib.memRegion_split (sp' + 112#64 + 32#64 + 32#64) 48 72 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem w8bSigErr_spills96_entails_memRegion
    (sp' : BitVec 64) (kpkVal opkTag opkVal spkId regTag regVal regId ikHi p8z : BitVec 32)
    (msgLen kyberLen w15 bkPtr bkCap msgPtr ikPtr : BitVec 64) :
    ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
      ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
      ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
      ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
      ((sp' + 56#64) ↦₃₂ regId) ∗ ((sp' + 60#64) ↦₃₂ ikHi) ∗
      memRegion (sp' + 64#64) 4 ∗
      ((sp' + 68#64) ↦₃₂ p8z) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ⊢
      memRegion (sp' + 16#64) 96 := by
  have hm56 : ((sp' + 56#64) ↦₃₂ regId) ∗ ((sp' + 60#64) ↦₃₂ ikHi) =
      ((sp' + 56#64) ↦₆₄ (ikHi ++ regId)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      pointsTo32_merge64 (sp' + 56#64) regId ikHi
  refine Entails.trans ?_
    (w8bSeg1Cells_entails_memRegion96 sp' bkCap bkPtr w15 kyberLen ikPtr (ikHi ++ regId)
      msgPtr msgLen regTag regVal opkTag opkVal spkId p8z kpkVal)
  rw [← hm56]
  apply entails_of_eq; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

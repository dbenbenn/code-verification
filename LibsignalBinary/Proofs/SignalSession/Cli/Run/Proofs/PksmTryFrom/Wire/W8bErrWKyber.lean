/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bKyber -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailC
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberb
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberc
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWShared
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysPlacedSym

/-!
# `PreKeySignalMessage::try_from`: Kyber Dispatch Error Continuation (`PreKeyKyberErrW`)

Proves `preKeyKyberErrW_proof` (`+0x684 → +0xa24 → +0x504 → ret`) from `pk_scatter_head_wp`,
`kyber_half_err_wpE` / `kyber_neither_v4_err_wpE`, `ErrTailC.tail_a24_wpX`, and
`w8b_errTail_close`.
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
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

theorem w8bKyberErr_memRegion152_split48 (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 152 =
      memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 312#64) 48 ∗
        memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
        memRegion (sp' + 440#64) 8 := by
  rw [show (152 : Nat) = 16 + (48 + (72 + (8 + 8))) by decide,
    Prost.memRegion_split (sp' + 296#64) 16 136 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 16#64) 48 88 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 16#64 + 48#64) 72 16 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 16#64 + 48#64 + 72#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

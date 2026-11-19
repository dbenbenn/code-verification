/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aBaseKey -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPostLoop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: `+0x5b4` Continuation via `base_key` Deserialization

Proves `preKey5b4OkW_of_684`, discharging `PreKey5b4OkW` (`+0x5b4 → ret`) by case analysis
on `PublicKey.deserialize bk` into `post_deser_bk_ok_full_to_684_wpW` + `PreKey684OkW` (`Ok`)
and `PreKeyBaseKeyErrW` (`Err`).
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
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

/-! ## 1. Frames and the `+0x684` continuation -/

/-- The part of `w8bXokPost ∗ w8bPostLoopFrame` untouched by `base_key` deserialization (`+0x5b4 → +0x684`): everything
except `sp' + 72`, `sp' + 80`, `memRegion (sp' + 312) 48`, the `bk` buffer and `logOff img`. -/
@[expose] def w8bRowKFrame (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap kyberCap kyberPtr kyberLen ikCap ikPtr msgCap msgPtr : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) (ik msg bytes : List (BitVec 8)) : SepProp :=
  ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
    ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 56#64) ↦₆₄ BitVec.ofNat 64 ik.length) ∗ memRegion (sp' + 64#64) 4 ∗
    ((sp' + 68#64) ↦₃₂ kpkTag) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
    ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
    memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
    Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
    A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
    memRegion sp' 16 ∗ memRegion (sp' + 112#64) 184 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ memRegion sret 248 ∗ (ptr ↦ₛ bytes) ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

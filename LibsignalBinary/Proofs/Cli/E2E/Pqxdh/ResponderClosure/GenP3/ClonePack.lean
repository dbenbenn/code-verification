/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBase
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import

public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Segment 5: Pack Source Stack Slots
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4

open Arm64 ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

/-- Spill + call-arg stack cells accessed during `+0x1bac .. +0x1cd0`. -/
@[expose] def packSrcSlotsAt (sp : BitVec 64) (recG : SessionGhost)
    (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness)
    (remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64) (msgVer : BitVec 32) : SepProp :=
  ((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗
  ((sp + 0x10#64) ↦₆₄ w.d10) ∗
  ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗
  ((sp + 0x24#64) ↦₃₂ w.w24) ∗
  ((sp + 0x28#64) ↦₃₂ w.w28) ∗
  ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
  ((sp + 0x30#64) ↦₃₂ w.regW0) ∗
  ((sp + 0x34#64) ↦₃₂ w.regW1) ∗
  ((sp + 0x38#64) ↦₆₄ w.kybCap') ∗
  ((sp + 0x40#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
  ((sp + 0x48#64) ↦₆₄ w.c0) ∗
  ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
  ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
  ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
  ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
  ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
  ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
  ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
  ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
  ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
  ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
  ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
  ((sp + 0x3ac#64) ↦₈ 3#8) ∗
  genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2SessV1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Defs

/-!
# Stage P2 Arm 6 and Normal-Exit Bridges

Proves `p2_v1_arm6_ok` (Arm 6 `get_local_registration_id` error unwind `+0x09f4 →
s0.readReg64 .x30`, dropping the unpromoted V1 `SessionState`) and `p2_v1_ok_entails` (folding
`sessionStateAt A (coroPtr + 0xf8#64)` at Stage P3 entry `+0x1778`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (mkBobSenderChainGhost)
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-- Heap allocations of Bob's freshly initialized V1 `SessionState` (7 key boxes + SPQR V1 vec). -/
@[expose] def p2BobSessHeapAt (A : RustAlloc) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (drKey : DRKey)
    (pqBytes : List (BitVec 8))
    (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
     ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64) : SepProp :=
  p2BobSpqrVecBuf A spqrCap spqrBufPtr pqBytes ∗
  (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
  (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
  (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
  (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
  (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗ A.live ratchetPubBoxPtr 33 1 ∗
  (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
  (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1

theorem p2BobSessRegIdsV1_eq (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (remoteRegId localRegId : BitVec 32) :
    p2BobSessRegIdsV1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
      remoteRegId localRegId =
    p2BobSessHead56Bv8 p1 p2 ++
      (p2BobSessMid280V1 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
        (unpack32 remoteRegId ++ unpack32 localRegId)) := by
  unfold p2BobSessRegIdsV1
  simp only [List.append_assoc]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

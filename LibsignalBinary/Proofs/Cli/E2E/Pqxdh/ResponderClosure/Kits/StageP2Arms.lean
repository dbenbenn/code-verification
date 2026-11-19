/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Bridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Defs

/-!
# Stage P2 Exit Arm Bridges

Spatial entailments into `p2ErrFrameAt` for Error Arms 1–3 (`p2_v1_arm1_entails`..`arm3`), full
`SepWPp` exit bridges for Error Arms 4–5 (`p2_v1_arm4_ok`, `p2_v1_arm5_ok`), and re-exports of Arm
6 and normal-exit bridges from `StageP2Arms2`.
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

theorem p2_sp3b0_8_40_eq_48 (sp : BitVec 64) :
    memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3b8#64) 40 =
      memRegion (sp + 0x3b0#64) 48 :=
  (ProofLib.memRegion_split' (b := sp + 0x3b0#64) (n := 8) (k := 40)
    (b' := sp + 0x3b8#64) rfl (by bv_omega) (by decide)).symm

/-- Frame held constant across `stageP2_sub1_to_4_kits` (`+0x0868 -> +0x36ac` and Arms 1–3). -/
@[expose] def p2Sub1To4Frame (A : RustAlloc) {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr idStorePtr
     v_330 v_388 u_80 u_88 : BitVec 64)
    (stId : ikit.IdState) (hdr : HandshakeHdr) (msgVerByte : BitVec 8)
    (remoteRegId : BitVec 32) (gMe gPeer : AddrGhost) (Frame : SepProp) : SepProp :=
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  memRegion (coroPtr + 0x298#64) 20 ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  memRegion (coroPtr + 0x508#64) 328 ∗
  memRegion (coroPtr + 0x650#64) 8 ∗
  memRegion (coroPtr + 0x658#64) 298 ∗
  memRegion (coroPtr + 0x788#64) 16 ∗
  memRegion (coroPtr + 0x798#64) 64 ∗
  ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
  ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
  ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 hdr.ikAPk) ∗
  ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
  (ctBufPtr ↦ₛ (8#8 :: bytesToBv8 hdr.kemCt)) ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  ((sp + 0x80#64) ↦₆₄ u_80) ∗
  ((sp + 0x88#64) ↦₆₄ u_88) ∗
  memRegion (sp + 0x3a0#64) 8 ∗
  memRegion (sp + 0x3ac#64) 1 ∗
  memRegion (sp + 0x3b8#64) 40 ∗
  cells (sp + 0x560#64) 4 ∗
  cells (sp + 0x6a0#64) 4 ∗
  cells (sp + 0x7e0#64) 4 ∗
  memRegion (sp + 0xad1#64) 223 ∗
  memRegion (fp + 0xffffffffffffff80#64) 9 ∗
  Frame

theorem p2_head56_mid280V1_zero_eq_regIds (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    p2BobSessHead56Bv8 p1 p2 ++
        (p2BobSessMid280V1 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
          unpack64 0#64) =
      p2BobSessRegIdsV1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 0#32 0#32 := by
  rw [← p2BobSession344Bv8V1_eq_head56_mid280V1, p2BobSession344Bv8V1_eq_regIds_zero]

theorem p2_stack_split_alloc (sp : BitVec 64) (stk : Nat)
    (h1 : allocHookStack ≤ stk) (h2 : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      stackAt sp allocHookStack ∗
      memRegion (sp - BitVec.ofNat 64 stk) (stk - allocHookStack) := by
  dsimp only [stackAt]
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 stk) (stk - allocHookStack) allocHookStack
    (by omega)
  have haddr : sp - BitVec.ofNat 64 stk + BitVec.ofNat 64 (stk - allocHookStack) =
      sp - BitVec.ofNat 64 allocHookStack := by bv_omega
  have hsum : stk - allocHookStack + allocHookStack = stk := Nat.sub_add_cancel h1
  rw [haddr, hsum] at hsplit
  rw [hsplit, sepConj_comm]

theorem p2_stack_split_dropSs3 (sp : BitVec 64) (stk : Nat)
    (h1 : dropSessionStructureLocal2Stack ≤ stk) (h2 : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      stackAt sp dropSessionStructureLocal2Stack ∗
      memRegion (sp - BitVec.ofNat 64 stk) (stk - dropSessionStructureLocal2Stack) := by
  dsimp only [stackAt]
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 stk)
    (stk - dropSessionStructureLocal2Stack) dropSessionStructureLocal2Stack (by omega)
  have haddr : sp - BitVec.ofNat 64 stk + BitVec.ofNat 64 (stk - dropSessionStructureLocal2Stack) =
      sp - BitVec.ofNat 64 dropSessionStructureLocal2Stack := by bv_omega
  have hsum : stk - dropSessionStructureLocal2Stack + dropSessionStructureLocal2Stack = stk :=
    Nat.sub_add_cancel h1
  rw [haddr, hsum] at hsplit
  rw [hsplit, sepConj_comm]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

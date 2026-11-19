/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.Sep

/-!
# Prologue and Branch Dispatch of `RatchetState::consume_message_key`

Symbolic execution from `cmkEntry_placed` (`+0x000`) to each initial seam checkpoint:
- `prologueSplit_past_placed_ok`: `counter < ck.index` (`+0x000 → +0x05c`, `cmkTakePC_placed`).
- `prologueSplit_tooFar_placed_ok`: `ck.index ≤ counter` (`+0x000 → +0x170`, `cmkTooFarPC_placed`).
- `prologueSplit_advance_placed_ok`: `ck.index ≤ counter` within `max_forward_jumps` (`+0x000 → +0x334` or
  `+0x4dc`, skipping the disabled `MAX_LOG_LEVEL_FILTER` branch).
-/

public section

namespace CryptoVerification.LibsignalSession.PrologueSplit

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  unfold leBytes unpack32 BitVec.extractLsb'
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map, Nat.shiftRight_eq_div_pow]
  rfl

theorem chainKeyBytes_pointsTo (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) =
      (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [pointsToBytes_append, hlen, leBytes_four_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

@[expose] def ratchetAtOpen (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost) (st : RatchetState) : SepProp :=
  (self ↦₆₄ G.chainsCap) ∗
  ((self + 8#64) ↦₆₄ G.chainsPtr) ∗
  ((self + 16#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
  vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
  ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
  ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
  ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4

theorem ratchetAt_eq_open (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost) (st : RatchetState)
    (hchains : G.chains.length = st.receiverChains.length) :
    ratchetAt A self G st =
      (⌜G.chains.length = st.receiverChains.length ∧ G.senderPad.length = 100 ∧
        st.maxForwardJumps < 2 ^ 64⌝ ∗ ratchetAtOpen A self G st) := by
  unfold ratchetAt vecAt vecHeader ratchetAtOpen
  have hzip : (G.chains.zip st.receiverChains).length = st.receiverChains.length := by
    simp [hchains]
  rw [hzip]
  sep_interval_eq

theorem stackAt_cmkStack_split (sp : BitVec 64) :
    stackAt sp cmkStack =
      stackAt (sp - 480#64) 7712 ∗
      memRegion (sp - 480#64) 384 ∗
      cells (sp - 96#64) 12 := by
  dsimp only [stackAt, cmkStack]; sep_interval_eq

@[expose] def prologueSplitScratch256 (sp : BitVec 64) (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64) : SepProp :=
  ((sp - 352#64) ↦₆₄ v352) ∗
  ((sp - 344#64) ↦₆₄ v344) ∗
  memRegion (sp - 336#64) 4 ∗
  ((sp - 332#64) ↦₃₂ v332) ∗
  ((sp - 328#64) ↦₆₄ v328) ∗
  memRegion (sp - 320#64) 224

theorem memRegion_256_split (sp : BitVec 64) :
    memRegion (sp - 352#64) 256 =
      ∃∗ v328 : BitVec 64, ∃∗ v332 : BitVec 32, ∃∗ v344 : BitVec 64, ∃∗ v352 : BitVec 64,
        prologueSplitScratch256 sp v352 v344 v332 v328 := by
  simp only [prologueSplitScratch256, ← sepExists_sepConj_left, ← sepExists_sepConj_right]
  sep_interval_eq

theorem prologueSplitScratch256_entails_memRegion (sp : BitVec 64)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64) :
    prologueSplitScratch256 sp v352 v344 v332 v328 ⊢ memRegion (sp - 352#64) 256 := by
  unfold prologueSplitScratch256; sep_interval

theorem memRegion_384_split (sp : BitVec 64) :
    memRegion (sp - 480#64) 384 =
      ∃∗ v356 : BitVec 32, ∃∗ v368 : BitVec 64, cmkLoopFrame sp v368 v356 := by
  simp only [cmkLoopFrame, ← sepExists_sepConj_left, ← sepExists_sepConj_right]
  sep_interval_eq

theorem cmkLoopFrame_entails_memRegion (sp ret : BitVec 64) (counter : BitVec 32) :
    cmkLoopFrame sp ret counter ⊢ memRegion (sp - 480#64) 384 := by
  unfold cmkLoopFrame; sep_interval

abbrev prologueSplitActive [LibsignalPlacement] (img : Unit) (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64) : SepProp :=
  ((x.self + 8#64) ↦₆₄ x.G.chainsPtr) ∗
  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
  ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 x.st.maxForwardJumps) ∗
  ((x.ckA + 32#64) ↦₃₂ x.ck.index) ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  ((s0.sp - 368#64) ↦₆₄ v368) ∗
  ((s0.sp - 356#64) ↦₃₂ v356) ∗
  ((s0.sp - 352#64) ↦₆₄ v352) ∗
  ((s0.sp - 344#64) ↦₆₄ v344) ∗
  ((s0.sp - 332#64) ↦₃₂ v332) ∗
  ((s0.sp - 328#64) ↦₆₄ v328) ∗
  ((s0.sp - 96#64) ↦₆₄ v96) ∗
  ((s0.sp - 88#64) ↦₆₄ v88) ∗
  ((s0.sp - 80#64) ↦₆₄ v80) ∗
  ((s0.sp - 72#64) ↦₆₄ v72) ∗
  ((s0.sp - 64#64) ↦₆₄ v64) ∗
  ((s0.sp - 56#64) ↦₆₄ v56) ∗
  ((s0.sp - 48#64) ↦₆₄ v48) ∗
  ((s0.sp - 40#64) ↦₆₄ v40) ∗
  ((s0.sp - 32#64) ↦₆₄ v32) ∗
  ((s0.sp - 24#64) ↦₆₄ v24) ∗
  ((s0.sp - 16#64) ↦₆₄ v16) ∗
  ((s0.sp - 8#64) ↦₆₄ v8)

@[expose] def prologueSplitPassiveFrame (A : RustAlloc) (x : ConsumeMessageKeyGhost) (s0 : State) : SepProp :=
  (x.self ↦₆₄ x.G.chainsCap) ∗
  vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
  ((x.self + 24#64) ↦ₛ optSenderChainBytes x.st.senderChain x.G.senderPad) ∗
  ((x.self + 128#64) ↦ₛ keyToBytes32 x.st.rootKey) ∗
  ((x.self + 168#64) ↦₃₂ x.st.previousCounter) ∗
  memRegion (x.self + 172#64) 4 ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ keyToBytes32 x.ck.key) ∗
  memRegion x.ret 88 ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  memRegion (s0.sp - 480#64) 112 ∗
  memRegion (s0.sp - 360#64) 4 ∗
  memRegion (s0.sp - 336#64) 4 ∗
  memRegion (s0.sp - 320#64) 224 ∗
  A.pool

theorem prologueSplitActive_entails_loopHeap_gen [LibsignalPlacement] (A : RustAlloc) (img : Unit) (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (hchains : x.G.chains.length = x.st.receiverChains.length)
    (hpad : x.G.senderPad.length = 100)
    (hmax : x.st.maxForwardJumps < 2 ^ 64) :
    (prologueSplitActive img x s0 v368 v356 v352 v344 v332 v328
        (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
        (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
      prologueSplitPassiveFrame A x s0) ⊢
      (ratchetAt A x.self x.G x.st ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       cmkLoopFrame s0.sp v368 v356 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) := by
  rw [ratchetAt_eq_open A x.self x.G x.st hchains, chainKeyBytes_pointsTo]
  unfold prologueSplitActive prologueSplitPassiveFrame ratchetAtOpen cmkLoopFrame cmkSavedRegs
  rw [memRegion_256_split s0.sp]
  unfold prologueSplitScratch256
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  bi_entail

theorem prologueSplitActive_entails_loopHeap [LibsignalPlacement] (A : RustAlloc) (img : Unit) (x : ConsumeMessageKeyGhost) (s0 : State)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (hchains : x.G.chains.length = x.st.receiverChains.length)
    (hpad : x.G.senderPad.length = 100)
    (hmax : x.st.maxForwardJumps < 2 ^ 64) :
    (prologueSplitActive img x s0 x.ret x.counter v352 v344 v332 v328
        (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
        (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
      prologueSplitPassiveFrame A x s0) ⊢
      cmkLoopHeap A img x x.G x.st x.ck s0 :=
  prologueSplitActive_entails_loopHeap_gen A img x s0 x.ret x.counter v352 v344 v332 v328 hchains hpad hmax

theorem cmkLoopHeap_entails_preLoopHeap [LibsignalPlacement] (A : RustAlloc) (img : Unit) (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32) :
    (ratchetAt A x.self x.G x.st ∗
     (x.theirA ↦ₛ x.their.bytes.toList) ∗
     (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
     memRegion x.ret 88 ∗
     (logFilterAddr img ↦₆₄ 0#64) ∗
     stackAt (s0.sp - 480#64) 7712 ∗
     cmkLoopFrame s0.sp v368 v356 ∗
     cmkSavedRegs s0.sp s0 ∗
     A.pool) ⊢ cmkPreLoopHeap A img x s0 := by
  unfold cmkPreLoopHeap
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (cmkLoopFrame_entails_memRegion s0.sp v368 v356)))))))

theorem prologueSplitActive_entails_preLoopHeap [LibsignalPlacement] (A : RustAlloc) (img : Unit) (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (hchains : x.G.chains.length = x.st.receiverChains.length)
    (hpad : x.G.senderPad.length = 100)
    (hmax : x.st.maxForwardJumps < 2 ^ 64) :
    (prologueSplitActive img x s0 v368 v356 v352 v344 v332 v328
        (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
        (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
      prologueSplitPassiveFrame A x s0) ⊢
      cmkPreLoopHeap A img x s0 :=
  Entails.trans
    (prologueSplitActive_entails_loopHeap_gen A img x s0 v368 v356 v352 v344 v332 v328 hchains hpad hmax)
    (cmkLoopHeap_entails_preLoopHeap A img x s0 v368 v356)

abbrev prologueSplitActiveAt (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64) : SepProp :=
  ((x.self + 8#64) ↦₆₄ x.G.chainsPtr) ∗
  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
  ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 x.st.maxForwardJumps) ∗
  ((x.ckA + 32#64) ↦₃₂ x.ck.index) ∗
  (logAddr ↦₆₄ 0#64) ∗
  ((s0.sp - 368#64) ↦₆₄ v368) ∗
  ((s0.sp - 356#64) ↦₃₂ v356) ∗
  ((s0.sp - 352#64) ↦₆₄ v352) ∗
  ((s0.sp - 344#64) ↦₆₄ v344) ∗
  ((s0.sp - 332#64) ↦₃₂ v332) ∗
  ((s0.sp - 328#64) ↦₆₄ v328) ∗
  ((s0.sp - 96#64) ↦₆₄ v96) ∗
  ((s0.sp - 88#64) ↦₆₄ v88) ∗
  ((s0.sp - 80#64) ↦₆₄ v80) ∗
  ((s0.sp - 72#64) ↦₆₄ v72) ∗
  ((s0.sp - 64#64) ↦₆₄ v64) ∗
  ((s0.sp - 56#64) ↦₆₄ v56) ∗
  ((s0.sp - 48#64) ↦₆₄ v48) ∗
  ((s0.sp - 40#64) ↦₆₄ v40) ∗
  ((s0.sp - 32#64) ↦₆₄ v32) ∗
  ((s0.sp - 24#64) ↦₆₄ v24) ∗
  ((s0.sp - 16#64) ↦₆₄ v16) ∗
  ((s0.sp - 8#64) ↦₆₄ v8)

theorem prologueSplitActiveAt_entails_loopHeapAt_gen (A : RustAlloc) (logAddr : BitVec 64)
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (hchains : x.G.chains.length = x.st.receiverChains.length)
    (hpad : x.G.senderPad.length = 100)
    (hmax : x.st.maxForwardJumps < 2 ^ 64) :
    (prologueSplitActiveAt logAddr x s0 v368 v356 v352 v344 v332 v328
        (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
        (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
      prologueSplitPassiveFrame A x s0) ⊢
      (ratchetAt A x.self x.G x.st ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗
       (logAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       cmkLoopFrame s0.sp v368 v356 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) := by
  rw [ratchetAt_eq_open A x.self x.G x.st hchains, chainKeyBytes_pointsTo]
  unfold prologueSplitActiveAt prologueSplitPassiveFrame ratchetAtOpen cmkLoopFrame cmkSavedRegs
  rw [memRegion_256_split s0.sp]
  unfold prologueSplitScratch256
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  bi_entail

theorem prologueSplitActiveAt_entails_loopHeapAt (A : RustAlloc) (logAddr : BitVec 64)
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (hchains : x.G.chains.length = x.st.receiverChains.length)
    (hpad : x.G.senderPad.length = 100)
    (hmax : x.st.maxForwardJumps < 2 ^ 64) :
    (prologueSplitActiveAt logAddr x s0 x.ret x.counter v352 v344 v332 v328
        (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
        (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
      prologueSplitPassiveFrame A x s0) ⊢
      cmkLoopHeapAt A logAddr x x.G x.st x.ck s0 :=
  prologueSplitActiveAt_entails_loopHeapAt_gen A logAddr x s0 x.ret x.counter v352 v344 v332 v328 hchains hpad hmax

theorem cmkLoopHeapAt_entails_preLoopHeapAt (A : RustAlloc) (logAddr : BitVec 64)
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32) :
    (ratchetAt A x.self x.G x.st ∗
     (x.theirA ↦ₛ x.their.bytes.toList) ∗
     (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
     memRegion x.ret 88 ∗
     (logAddr ↦₆₄ 0#64) ∗
     stackAt (s0.sp - 480#64) 7712 ∗
     cmkLoopFrame s0.sp v368 v356 ∗
     cmkSavedRegs s0.sp s0 ∗
     A.pool) ⊢ cmkPreLoopHeapAt A logAddr x s0 := by
  unfold cmkPreLoopHeapAt
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (cmkLoopFrame_entails_memRegion s0.sp v368 v356)))))))

theorem prologueSplitActiveAt_entails_preLoopHeapAt (A : RustAlloc) (logAddr : BitVec 64)
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (hchains : x.G.chains.length = x.st.receiverChains.length)
    (hpad : x.G.senderPad.length = 100)
    (hmax : x.st.maxForwardJumps < 2 ^ 64) :
    (prologueSplitActiveAt logAddr x s0 v368 v356 v352 v344 v332 v328
        (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
        (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
      prologueSplitPassiveFrame A x s0) ⊢
      cmkPreLoopHeapAt A logAddr x s0 :=
  Entails.trans
    (prologueSplitActiveAt_entails_loopHeapAt_gen A logAddr x s0 v368 v356 v352 v344 v332 v328 hchains hpad hmax)
    (cmkLoopHeapAt_entails_preLoopHeapAt A logAddr x s0 v368 v356)

theorem bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by
  rw [BitVec.sub_sub]

theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

/-! ## Relocatable `[LibsignalPlacement]` Prologue and Dispatch (Block 24) -/

theorem cmkPre_placed_unpack_at [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {x : ConsumeMessageKeyGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (cmkPlacedSpec F A).pre x s0 ∗ R) :
    LibsignalCodeLoaded lsmpl s0.mem ∧
    s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.theirA ∧ s0.readReg64 .x2 = x.ckA ∧
    (s0.readReg64 .x3).setWidth 32 = x.counter ∧
    (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s0.readReg64 .x8 = x.ret ∧
    x.G.chains.length = x.st.receiverChains.length ∧ x.G.senderPad.length = 100 ∧
    x.st.maxForwardJumps < 2 ^ 64 ∧
    ∃ (v368 : BitVec 64) (v356 : BitVec 32)
      (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
      (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64),
      s0.mem ⊨ prologueSplitActiveAt lsLogFilterAddr x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 ∗
        (prologueSplitPassiveFrame A x s0 ∗ R) := by
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  have h1 : s0.mem ⊨
      (⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.theirA ∧ s0.readReg64 .x2 = x.ckA ∧
         (s0.readReg64 .x3).setWidth 32 = x.counter ∧
         (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s0.readReg64 .x8 = x.ret⌝ ∗
       (ratchetAt A x.self x.G x.st ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
        memRegion x.ret 88 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp cmkStack ∗ A.pool ∗ R)) :=
    Satisfies.of_eq hpre
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx8⟩, h1⟩
  unfold ratchetAt at h1
  rw [sepConj_assoc, satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hchains, hpad, hmax⟩, h1⟩
  have hzip : (x.G.chains.zip x.st.receiverChains).length = x.st.receiverChains.length := by
    simp [hchains]
  unfold vecAt vecHeader at h1
  rw [hzip, chainKeyBytes_pointsTo, stackAt_cmkStack_split] at h1
  cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at h1
  rcases h1 with ⟨v96, v88, v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, h1⟩
  rw [memRegion_384_split] at h1
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at h1
  rcases h1 with ⟨v356, v368, h1⟩
  unfold cmkLoopFrame at h1
  rw [memRegion_256_split] at h1
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at h1
  rcases h1 with ⟨v328, v332, v344, v352, h1⟩
  unfold prologueSplitScratch256 at h1
  refine ⟨hcl, hx0, hx1, hx2, hx3, hx4, hx8, hchains, hpad, hmax,
    v368, v356, v352, v344, v332, v328, v96, v88, v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, ?_⟩
  unfold prologueSplitActiveAt prologueSplitPassiveFrame
  exact Satisfies.mono (by bi_entail) h1

theorem cmkPre_placed_unpack [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {x : ConsumeMessageKeyGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (cmkPlacedSpec F A).pre x s0 ∗ R) :
    LibsignalCodeLoaded lsmpl s0.mem ∧
    s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.theirA ∧ s0.readReg64 .x2 = x.ckA ∧
    (s0.readReg64 .x3).setWidth 32 = x.counter ∧
    (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s0.readReg64 .x8 = x.ret ∧
    x.G.chains.length = x.st.receiverChains.length ∧ x.G.senderPad.length = 100 ∧
    x.st.maxForwardJumps < 2 ^ 64 ∧
    ∃ (v368 : BitVec 64) (v356 : BitVec 32)
      (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
      (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64),
      s0.mem ⊨ prologueSplitActive cmkDummyImg x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 ∗
        (prologueSplitPassiveFrame A x s0 ∗ R) := by
  simpa only [prologueSplitActive, prologueSplitActiveAt, logFilterAddr_cmkDummyImg] using
    cmkPre_placed_unpack_at hpre

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_sub_lit bv_sub_add_lit

set_option maxHeartbeats 800000 in
theorem prologueSplit_past_wp_placed_at [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry_placed) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx8 : s0.readReg64 .x8 = x.ret) (hlt : x.counter < x.ck.index) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) cmkTakePC_placed s0
      (prologueSplitActiveAt lsLogFilterAddr x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        P_f = prologueSplitActiveAt lsLogFilterAddr x s0 v368 x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkTakeRegs x s0 sf) := by
  unfold cmkTakePC_placed
  unfold cmkEntry_placed at hpc ⊢
  have hsp480 : (s0.sp - 480#64) &&& 15#64 = 0#64 := beq_iff_eq.mp (s0.spAligned_sub 480#64 hsp)
  have h_not_ule : ¬(BitVec.ule x.ck.index x.counter = true) := by
    simp [BitVec.ule_iff_toNat_le, BitVec.lt_def] at hlt ⊢; omega
  dsimp only [prologueSplitActiveAt]
  wp_steps
  refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold CmkTakeRegs
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem prologueSplit_past_wp_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry_placed) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx8 : s0.readReg64 .x8 = x.ret) (hlt : x.counter < x.ck.index) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) cmkTakePC_placed s0
      (prologueSplitActive cmkDummyImg x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        P_f = prologueSplitActive cmkDummyImg x s0 v368 x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkTakeRegs x s0 sf) := by
  simpa only [prologueSplitActive, prologueSplitActiveAt, logFilterAddr_cmkDummyImg] using
    prologueSplit_past_wp_placed_at H x s0 v368 v356 v352 v344 v332 v328
      v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 hpc hrun hsp hx0 hx1 hx2 hx3 hx8 hlt

set_option maxHeartbeats 800000 in
theorem prologueSplit_tooFar_wp_placed_at [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry_placed) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx4 : (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType)
    (hx8 : s0.readReg64 .x8 = x.ret) (hle : x.ck.index ≤ x.counter) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) cmkTooFarPC_placed s0
      (prologueSplitActiveAt lsLogFilterAddr x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        P_f = prologueSplitActiveAt lsLogFilterAddr x s0 v368 x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkTooFarRegs x s0 sf) := by
  unfold cmkTooFarPC_placed
  unfold cmkEntry_placed at hpc ⊢
  have hsp480 : (s0.sp - 480#64) &&& 15#64 = 0#64 := beq_iff_eq.mp (s0.spAligned_sub 480#64 hsp)
  have h_ule : BitVec.ule x.ck.index x.counter = true := by
    simp [BitVec.ule_iff_toNat_le, BitVec.le_def] at hle ⊢; omega
  dsimp only [prologueSplitActiveAt]
  wp_steps
  refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold CmkTooFarRegs
  refine ⟨hx2, hx4, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem prologueSplit_tooFar_wp_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry_placed) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx4 : (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType)
    (hx8 : s0.readReg64 .x8 = x.ret) (hle : x.ck.index ≤ x.counter) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) cmkTooFarPC_placed s0
      (prologueSplitActive cmkDummyImg x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        P_f = prologueSplitActive cmkDummyImg x s0 v368 x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkTooFarRegs x s0 sf) := by
  simpa only [prologueSplitActive, prologueSplitActiveAt, logFilterAddr_cmkDummyImg] using
    prologueSplit_tooFar_wp_placed_at H x s0 v368 v356 v352 v344 v332 v328
      v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 hpc hrun hsp hx0 hx1 hx2 hx3 hx4 hx8 hle

set_option maxHeartbeats 800000 in
theorem prologueSplit_advance_wp_placed_at [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry_placed) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hmax : x.st.maxForwardJumps < 2 ^ 64)
    (hle : x.ck.index ≤ x.counter)
    (hj : (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps) :
    let targetPC := if x.ck.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
    SepWP ((blkPC_24).rebase (blkPl_24).base H) targetPC s0
      (prologueSplitActiveAt lsLogFilterAddr x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        P_f = prologueSplitActiveAt lsLogFilterAddr x s0 x.ret x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index ((x.counter - x.ck.index).zeroExtend 64)
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkLoopRegs x x.ck s0 sf ∧
        (targetPC = cmkLoopPC_placed → sf.readReg64 .x19 = 1#64)) := by
  intro targetPC
  unfold cmkEntry_placed at hpc
  have hsp480 : (s0.sp - 480#64) &&& 15#64 = 0#64 := beq_iff_eq.mp (s0.spAligned_sub 480#64 hsp)
  have h_ule : BitVec.ule x.ck.index x.counter = true := by
    simp [BitVec.ule_iff_toNat_le, BitVec.le_def] at hle ⊢; omega
  have h_jump_ule :
      BitVec.ule (BitVec.zeroExtend 64 (x.counter - x.ck.index))
        (BitVec.ofNat 64 x.st.maxForwardJumps) = true := by
    have := (x.counter - x.ck.index).isLt
    rw [BitVec.ule_iff_toNat_le, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  dsimp only [targetPC]
  by_cases hck_lt : x.ck.index < x.counter
  · simp only [hck_lt, ↓reduceIte]
    unfold cmkLoopPC_placed cmkEntry_placed
    have h_not_ck_ule : ¬(BitVec.ule x.counter x.ck.index = true) := by
      simp [BitVec.ule_iff_toNat_le, BitVec.lt_def] at hck_lt ⊢; omega
    dsimp only [prologueSplitActiveAt]
    by_cases h25000 : BitVec.ule (x.counter - x.ck.index) 25000#32 = true
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun _ => rfl⟩
      unfold CmkLoopRegs
      refine ⟨rfl, rfl, rfl, rfl, rfl⟩
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun _ => rfl⟩
      unfold CmkLoopRegs
      refine ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp only [hck_lt, ↓reduceIte]
    unfold cmkEpiloguePC_placed cmkLoopPC_placed cmkEntry_placed
    have h_loop_ne : (blkPl_24).base + bv% (1244) ≠ (blkPl_24).base + bv% (820) := by
      intro h
      have h2 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h2
      omega
    have h_ck_ule : BitVec.ule x.counter x.ck.index = true := by
      simp [BitVec.ule_iff_toNat_le, BitVec.le_def, BitVec.lt_def] at hle hck_lt ⊢; omega
    dsimp only [prologueSplitActiveAt]
    by_cases h25000 : BitVec.ule (x.counter - x.ck.index) 25000#32 = true
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun h => absurd h h_loop_ne⟩
      unfold CmkLoopRegs
      refine ⟨rfl, rfl, rfl, rfl, rfl⟩
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun h => absurd h h_loop_ne⟩
      unfold CmkLoopRegs
      refine ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem prologueSplit_advance_wp_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry_placed) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hmax : x.st.maxForwardJumps < 2 ^ 64)
    (hle : x.ck.index ≤ x.counter)
    (hj : (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps) :
    let targetPC := if x.ck.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
    SepWP ((blkPC_24).rebase (blkPl_24).base H) targetPC s0
      (prologueSplitActive cmkDummyImg x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        P_f = prologueSplitActive cmkDummyImg x s0 x.ret x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index ((x.counter - x.ck.index).zeroExtend 64)
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkLoopRegs x x.ck s0 sf ∧
        (targetPC = cmkLoopPC_placed → sf.readReg64 .x19 = 1#64)) := by
  simpa only [prologueSplitActive, prologueSplitActiveAt, logFilterAddr_cmkDummyImg] using
    prologueSplit_advance_wp_placed_at H x s0 v368 v356 v352 v344 v332 v328
      v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 hpc hrun hsp hx0 hx1 hx2 hx3 hx8 hmax hle hj

end CryptoVerification.LibsignalSession.PrologueSplit

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- Placed prologue dispatch to `cmkTakePC_placed`. -/
theorem prologueSplit_past_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    ProloguePastPlacedSpec F A H := by
  intro x R s0 hpc hrun hsp hpre hlt hL
  obtain ⟨hcl, hx0, hx1, hx2, hx3, _, hx8, hchains, hpad, hmax,
    v368, v356, v352, v344, v332, v328, v96, v88, v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, hm⟩ :=
    PrologueSplit.cmkPre_placed_unpack_at hpre
  have hwp := PrologueSplit.prologueSplit_past_wp_placed_at H x s0
    v368 v356 v352 v344 v332 v328 v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8
    hpc hrun hsp hx0 hx1 hx2 hx3 hx8 hlt
  rcases hwp.elim hm hL with
    ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, P_f, hm_sf, rfl, hsp_sf, hx29_sf, htr_sf, hvregs_sf, hregs_sf⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, hpc_sf, ?_, hregs_sf, ?_⟩⟩
  · refine ⟨hrun_sf, hsp_sf, hsp, ?_, hx29_sf, htr_sf, hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs_sf⟩
    unfold State.spAligned
    rw [hsp_sf]
    exact s0.spAligned_sub 480#64 hsp
  · rw [← sepConj_assoc] at hm_sf
    rw [cmkPreLoopHeap_placed_eq_at]
    exact Satisfies.mono
      (sepConj_mono_left (PrologueSplit.prologueSplitActiveAt_entails_preLoopHeapAt A lsLogFilterAddr x s0 v368 x.counter
        (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328 hchains hpad hmax))
      hm_sf

/-- Placed prologue dispatch to `cmkTooFarPC_placed`. -/
theorem prologueSplit_tooFar_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    PrologueTooFarPlacedSpec F A H := by
  intro x R s0 hpc hrun hsp hpre hle hL
  obtain ⟨hcl, hx0, hx1, hx2, hx3, hx4, hx8, hchains, hpad, hmax,
    v368, v356, v352, v344, v332, v328, v96, v88, v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, hm⟩ :=
    PrologueSplit.cmkPre_placed_unpack_at hpre
  have hwp := PrologueSplit.prologueSplit_tooFar_wp_placed_at H x s0
    v368 v356 v352 v344 v332 v328 v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8
    hpc hrun hsp hx0 hx1 hx2 hx3 hx4 hx8 hle
  rcases hwp.elim hm hL with
    ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, P_f, hm_sf, rfl, hsp_sf, hx29_sf, htr_sf, hvregs_sf, hregs_sf⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, hpc_sf, ?_, hregs_sf, ?_⟩⟩
  · refine ⟨hrun_sf, hsp_sf, hsp, ?_, hx29_sf, htr_sf, hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs_sf⟩
    unfold State.spAligned
    rw [hsp_sf]
    exact s0.spAligned_sub 480#64 hsp
  · rw [← sepConj_assoc] at hm_sf
    rw [cmkPreLoopHeap_placed_eq_at]
    exact Satisfies.mono
      (sepConj_mono_left (PrologueSplit.prologueSplitActiveAt_entails_preLoopHeapAt A lsLogFilterAddr x s0 v368 x.counter
        (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328 hchains hpad hmax))
      hm_sf

/-- Placed prologue dispatch to `cmkLoopPC_placed` or `cmkEpiloguePC_placed`. -/
theorem prologueSplit_advance_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    PrologueAdvanceEntryPlacedSpec F A H := by
  intro x R s0 hpc hrun hsp hpre hle hj targetPC hL
  obtain ⟨hcl, hx0, hx1, hx2, hx3, _, hx8, hchains, hpad, hmax,
    v368, v356, v352, v344, v332, v328, v96, v88, v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, hm⟩ :=
    PrologueSplit.cmkPre_placed_unpack_at hpre
  have hwp := PrologueSplit.prologueSplit_advance_wp_placed_at H x s0
    v368 v356 v352 v344 v332 v328 v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8
    hpc hrun hsp hx0 hx1 hx2 hx3 hx8 hmax hle hj
  rcases hwp.elim hm hL with
    ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, P_f, hm_sf, rfl, hsp_sf, hx29_sf, htr_sf, hvregs_sf, hregs_sf, hx19_sf⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, hpc_sf, ?_, hregs_sf, hx19_sf, ?_⟩⟩
  · refine ⟨hrun_sf, hsp_sf, hsp, ?_, hx29_sf, htr_sf, hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs_sf⟩
    unfold State.spAligned
    rw [hsp_sf]
    exact s0.spAligned_sub 480#64 hsp
  · rw [← sepConj_assoc] at hm_sf
    rw [cmkLoopHeap_placed_eq_at]
    exact Satisfies.mono
      (sepConj_mono_left (PrologueSplit.prologueSplitActiveAt_entails_loopHeapAt A lsLogFilterAddr x s0
        (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index
        ((x.counter - x.ck.index).zeroExtend 64) hchains hpad hmax))
      hm_sf

end CryptoVerification.LibsignalSession

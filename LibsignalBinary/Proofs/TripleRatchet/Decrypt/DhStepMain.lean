/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepErr -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Segment S3 (`DhStep`) Key-Generation, Sending Chain, and Top-Level Proofs

Composes key generation and the second `RootKey::create_chain` call (`+0x70c → +0x8ac / +0x30c`)
with `dhStep_missing_sender_chain`, `dhStep_recv_create_chain`, and `dhCommit_spec` to establish
`dhStep_ok` (`DhStepSpec`) and relocatable `DhStepBlockWp` contracts.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Relocatable intermediate state at `entry + 0x70c#64` after `RootKey::create_chain` #1 succeeds. -/
@[expose] def DhStepAfterRecvChainStatePlaced [LibsignalPlacement] (entry : BitVec 64)
    (A : RustAlloc) (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (rk1 : RootKey) (rck : ChainKey) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = entry + 0x70c#64 ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x26 = sp + 0x2c0#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x2c0#64 ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    ((sp + 0x190#64) ↦₃₂ 0#32) ∗
    ((sp + 0x194#64) ↦ₛ keyToBytes32 rk1) ∗
    ((sp + 0x1b4#64) ↦ₛ chainKeyBytes rck) ∗
    memRegion (sp + 0x1d8#64) 0x3a8 ∗
    tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R)

/-- Propagate an allocator failure panic from `createChainSpec` to `tryDecryptSpecPlaced.onPanic`. -/
theorem onPanic_of_createChain_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {ccG : CreateChainGhost} {s0 sc sm : State} {Frame R : SepProp}
    (htrace : sc.trace = s0.trace)
    (hpost : sm.mem ⊨ (createChainSpec C A).onPanic ccG sc sm ∗ (Frame ∗ R)) :
    sm.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sm ∗ R :=
  onPanic_of_createChain (ccG := ccG) htrace hpost

/-- Bundle of relocatable basic-block `SepWP` obligations for `DhStep` (`+0x500 → +0x8ac / +0x30c`). -/
structure DhStepBlockWp [LibsignalPlacement] (prog : Program)
    (entry rngFillEntry : BitVec 64) where
  missingScAddr : BitVec 64
  hro_missingSc : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) → (m ⊨ (missingScAddr ↦ᵣ invalidSessionStructureStr .missingSenderChain) ∗ P)
  wpp_2dc_to_30c :
    ∀ (s0 s : State) (w2c0 w2c8 : BitVec 64)
      (u34c u344 u338 u330 u2b8 u2b0 u180 u178 u170 u168 : BitVec 64)
      (u340 u2d0 u18c u188 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x2dc#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x12 = sp + 0x2c0#64 →
      s.readReg64 .x20 = sp + 0x140#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 780#64) s
        ((memRegion (sp + 0x140#64) 0x28 ∗ (sp + 0x168#64) ↦₆₄ u168 ∗ (sp + 0x170#64) ↦₆₄ u170 ∗
          (sp + 0x178#64) ↦₆₄ u178 ∗ (sp + 0x180#64) ↦₆₄ u180 ∗ (sp + 0x188#64) ↦₃₂ u188 ∗
          (sp + 0x18c#64) ↦₃₂ u18c ∗ memRegion (sp + 0x190#64) 0x120 ∗ (sp + 0x2b0#64) ↦₆₄ u2b0 ∗
          (sp + 0x2b8#64) ↦₆₄ u2b8) ∗ (sp + 0x2c0#64) ↦₆₄ w2c0 ∗ (sp + 0x2c8#64) ↦₆₄ w2c8 ∗
         ((sp + 0x2d0#64) ↦₃₂ u2d0 ∗ memRegion (sp + 0x2d4#64) 0x5c ∗ (sp + 0x330#64) ↦₆₄ u330 ∗
          (sp + 0x338#64) ↦₆₄ u338 ∗ (sp + 0x340#64) ↦₃₂ u340 ∗ (sp + 0x344#64) ↦₆₄ u344 ∗
          (sp + 0x34c#64) ↦₆₄ u34c ∗ memRegion (sp + 0x354#64) 0x22c))
        (fun sf P_f =>
          sf.sp = sp ∧ sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = sp + 0x140#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_f ∗ R) →
            (m ⊨ (memRegion (sp + 0x140#64) 0x28 ∗ ((sp + 0x168#64) ↦₆₄ w2c0) ∗
                  ((sp + 0x170#64) ↦₆₄ w2c8) ∗ memRegion (sp + 0x178#64) 24 ∗
                  memRegion (sp + 0x190#64) 0x3f0) ∗ R)))
  wpp_7f8_to_2dc :
    ∀ (s0 s : State) (u508 u500 u2c8 u2c0 u2b8 u2b0 : BitVec 64) (u2d0 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x7f8#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.readReg64 .x26 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 732#64) s
        (memRegion (sp + 0x140#64) 0x58 ∗ ((sp + 0x198#64) ↦₆₄ speWord 10) ∗
         memRegion (sp + 0x1a0#64) 0x110 ∗ ((sp + 0x2b0#64) ↦₆₄ u2b0) ∗
         ((sp + 0x2b8#64) ↦₆₄ u2b8) ∗ ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗
         ((sp + 0x2c8#64) ↦₆₄ u2c8) ∗ ((sp + 0x2d0#64) ↦₃₂ u2d0) ∗
         memRegion (sp + 0x2d4#64) 0x22c ∗ ((sp + 0x500#64) ↦₆₄ u500) ∗
         ((sp + 0x508#64) ↦₆₄ u508) ∗ memRegion (sp + 0x510#64) 0x70)
        (fun sm P_m =>
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x12 = sp + 0x2c0#64 ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = sp + 0x140#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧ sm.readReg64 .x26 = speTag .invalidKeyAgreement ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) → (m ⊨ memRegion (sp + 0x140#64) 0x440 ∗ R)))
  wpp_missing_sc :
    ∀ (s0 s : State) (x : TryDecryptGhost) (u2c0 u2c8 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x500#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x12 = sp + 0x2c0#64 →
      s.readReg64 .x19 = x.ret → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x27 = sp + 0x38#64 →
      s.readReg64 .x28 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 732#64) s
        (((sp + 0x50#64) ↦₃₂ 0#32) ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
         ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
         ((sp + 0x30#64) ↦₆₄ x.remA) ∗ ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗ ((sp + 0x2c8#64) ↦₆₄ u2c8))
        (fun sm P_m =>
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x12 = sp + 0x2c0#64 ∧
          sm.readReg64 .x19 = x.ret ∧ sm.readReg64 .x20 = sp + 0x140#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧
          sm.readReg64 .x26 = speTag (.invalidSessionStructure .missingSenderChain) ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) →
            (m ⊨ (((sp + 0x50#64) ↦₃₂ 0#32) ∗ memRegion sp 0x38 ∗
                  ((sp + 0x2c0#64) ↦₆₄ missingScAddr) ∗ ((sp + 0x2c8#64) ↦₆₄ 20#64)) ∗ R)))
  wpp_cc1_err :
    ∀ (s0 s : State) (u1bc u1b4 u1a8 u1a0 : BitVec 64) (u1c4 u1b0 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1352#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.readReg64 .x26 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 2040#64) s
        (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
         ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗ ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗ ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
         ((sp + 0x1c4#64) ↦₃₂ u1c4))
        (fun sm P_m =>
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = sp + 0x140#64 ∧ sm.readReg64 .x23 = sp + 0x500#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧ sm.readReg64 .x26 = sp + 0x2c0#64 ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
                  ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗ ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
                  ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗ ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
                  ((sp + 0x1c4#64) ↦₃₂ u1c4)) ∗ R)))
  wpp_cc1_ok :
    ∀ (s0 s : State),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1352#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      SepWP prog (entry + 1804#64) s ((sp + 0x190#64) ↦₃₂ 0#32)
        (fun sm P_m =>
          sm.sp = sp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_m ∗ R) → (m ⊨ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ R)))
  wpp_pre_cc1 :
    ∀ (s0 s : State) (x : TryDecryptGhost)
      (p0 p1 p2 p3 k0 k1 k2 k3 u390 u398 u3a0 u3a8 u3b0 u3b8 u3c0 u3c8 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x500#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x12 = sp + 0x2c0#64 →
      s.readReg64 .x19 = x.ret → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x21 = x.ss → s.readReg64 .x22 = x.msgA →
      s.readReg64 .x23 = sp + 0x500#64 → (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x27 = sp + 0x38#64 →
      s.readReg64 .x28 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (lsmpl.base 40) s
        (((sp + 0x50#64) ↦₃₂ 1#32) ∗
         ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
         ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3) ∗
         ((sp + 0xb8#64) ↦₆₄ k0) ∗ ((sp + 0xc0#64) ↦₆₄ k1) ∗
         ((sp + 0xc8#64) ↦₆₄ k2) ∗ ((sp + 0xd0#64) ↦₆₄ k3) ∗
         ((sp + 0x390#64) ↦₆₄ u390) ∗ ((sp + 0x398#64) ↦₆₄ u398) ∗
         ((sp + 0x3a0#64) ↦₆₄ u3a0) ∗ ((sp + 0x3a8#64) ↦₆₄ u3a8) ∗
         ((sp + 0x3b0#64) ↦₆₄ u3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u3b8) ∗
         ((sp + 0x3c0#64) ↦₆₄ u3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u3c8))
        (fun sc1 P_c1 =>
          sc1.sp = sp ∧ sc1.readReg64 .x0 = sp + 0x3b0#64 ∧
          sc1.readReg64 .x1 = x.msgA + 56#64 ∧ sc1.readReg64 .x2 = sp + 0x390#64 ∧
          sc1.readReg64 .x8 = sp + 0x190#64 ∧ sc1.readReg64 .x19 = x.ret ∧
          sc1.readReg64 .x20 = sp + 0x140#64 ∧ sc1.readReg64 .x21 = x.ss ∧
          sc1.readReg64 .x22 = x.msgA ∧ sc1.readReg64 .x23 = sp + 0x500#64 ∧
          (sc1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
          sc1.readReg64 .x25 = sp + 0x190#64 ∧ sc1.readReg64 .x26 = sp + 0x2c0#64 ∧
          sc1.readReg64 .x27 = sp + 0x38#64 ∧ sc1.readReg64 .x28 = sp + 0x2c0#64 ∧
          sc1.readReg64 .x29 = s0.sp - 96#64 ∧ sc1.readReg64 .x30 = entry + 1352#64 ∧
          sc1.trace = s0.trace ∧ calleeSavedVRegs sc1 = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_c1 ∗ R) →
            (m ⊨ (((sp + 0x50#64) ↦₃₂ 1#32) ∗
                  ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
                  ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3) ∗
                  ((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗
                  ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64) ∗
                  ((sp + 0x390#64) ↦₆₄ p0) ∗ ((sp + 0x398#64) ↦₆₄ p1) ∗
                  ((sp + 0x3a0#64) ↦₆₄ p2) ∗ ((sp + 0x3a8#64) ↦₆₄ p3) ∗
                  ((sp + 0x3b0#64) ↦₆₄ k0) ∗ ((sp + 0x3b8#64) ↦₆₄ k1) ∗
                  ((sp + 0x3c0#64) ↦₆₄ k2) ∗ ((sp + 0x3c8#64) ↦₆₄ k3)) ∗ R)))
  wpp_cc2_ok :
    ∀ (s0 s : State),
      let sp := s0.sp - 1504#64
      s.pc = entry + 2008#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      SepWP prog (entry + 2220#64) s ((sp + 0x190#64) ↦₃₂ 0#32)
        (fun sm P_m =>
          sm.sp = sp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_m ∗ R) → (m ⊨ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ R)))
  wpp_cc2_err :
    ∀ (s0 s : State) (msgW : BitVec 32) (u1bc u1b4 u1a8 u1a0 : BitVec 64) (u1c4 u1b0 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 2008#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.readReg64 .x26 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 2040#64) s
        (((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
         ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
         ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗ ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
         ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗ ((sp + 0x1c4#64) ↦₃₂ u1c4))
        (fun sm P_m =>
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = sp + 0x140#64 ∧ sm.readReg64 .x23 = sp + 0x500#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧ sm.readReg64 .x26 = sp + 0x2c0#64 ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) →
            (m ⊨ (((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
                  ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
                  ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗ ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
                  ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗ ((sp + 0x1c4#64) ↦₃₂ u1c4)) ∗ R)))
  wpp_70c_to_778 :
    ∀ (s0 s : State)
      (r0 r4 c2 u10 u1c u3e0 u4a0 u4bc u510 : BitVec 32)
      (r1 r2 r3 c0 c1 c3 c4 u3d0 u3d8 u3e4 u3ec u400 u408 u440 u448
       u4a4 u4ac u4b4 u4c0 u4c8 u4d0 u4d8 u500 u508 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x70c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x23 = sp + 0x500#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x26 = sp + 0x2c0#64 →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 1912#64) s
        (((sp + 0x10#64) ↦₃₂ u10) ∗ ((sp + 0x1c#64) ↦₃₂ u1c) ∗
         ((sp + 0x194#64) ↦₃₂ r0) ∗ ((sp + 0x198#64) ↦₆₄ r1) ∗
         ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3) ∗ ((sp + 0x1b0#64) ↦₃₂ r4) ∗
         ((sp + 0x1b4#64) ↦₆₄ c0) ∗ ((sp + 0x1bc#64) ↦₆₄ c1) ∗ ((sp + 0x1c4#64) ↦₃₂ c2) ∗
         ((sp + 0x1c8#64) ↦₆₄ c3) ∗ ((sp + 0x1d0#64) ↦₆₄ c4) ∗
         ((sp + 0x3d0#64) ↦₆₄ u3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u3d8) ∗ ((sp + 0x3e0#64) ↦₃₂ u3e0) ∗
         ((sp + 0x3e4#64) ↦₆₄ u3e4) ∗ ((sp + 0x3ec#64) ↦₆₄ u3ec) ∗
         ((sp + 0x400#64) ↦₆₄ u400) ∗ ((sp + 0x408#64) ↦₆₄ u408) ∗
         ((sp + 0x440#64) ↦₆₄ u440) ∗ ((sp + 0x448#64) ↦₆₄ u448) ∗
         ((sp + 0x4a0#64) ↦₃₂ u4a0) ∗ ((sp + 0x4a4#64) ↦₆₄ u4a4) ∗
         ((sp + 0x4ac#64) ↦₆₄ u4ac) ∗ ((sp + 0x4b4#64) ↦₆₄ u4b4) ∗ ((sp + 0x4bc#64) ↦₃₂ u4bc) ∗
         ((sp + 0x4c0#64) ↦₆₄ u4c0) ∗ ((sp + 0x4c8#64) ↦₆₄ u4c8) ∗
         ((sp + 0x4d0#64) ↦₆₄ u4d0) ∗ ((sp + 0x4d8#64) ↦₆₄ u4d8) ∗
         ((sp + 0x500#64) ↦₆₄ u500) ∗ ((sp + 0x508#64) ↦₆₄ u508) ∗ ((sp + 0x510#64) ↦₃₂ u510))
        (fun s1 P1 =>
          s1.sp = sp ∧ s1.readReg64 .x0 = sp + 0x190#64 ∧ s1.readReg64 .x1 = 32#64 ∧
          s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
          s1.readReg64 .x21 = s.readReg64 .x21 ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x23 = sp + 0x500#64 ∧ s1.readReg64 .x25 = sp + 0x190#64 ∧
          s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = sp + 0x3d0#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64 ∧
          s1.readVReg128 0#5 = 0#128 ∧ s1.trace = s0.trace ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P1 ∗ R) →
            (m ⊨ (((sp + 0x10#64) ↦₃₂ c2) ∗
                  ((sp + 0x1c#64) ↦₃₂ (s.readReg64 .x24).setWidth 32) ∗
                  ((sp + 0x194#64) ↦₃₂ r0) ∗ ((sp + 0x198#64) ↦₆₄ r1) ∗
                  ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3) ∗ ((sp + 0x1b0#64) ↦₃₂ r4) ∗
                  ((sp + 0x1b4#64) ↦₆₄ c0) ∗ ((sp + 0x1bc#64) ↦₆₄ c1) ∗ ((sp + 0x1c4#64) ↦₃₂ c2) ∗
                  ((sp + 0x1c8#64) ↦₆₄ c3) ∗ ((sp + 0x1d0#64) ↦₆₄ c4) ∗
                  ((sp + 0x3d0#64) ↦₆₄ c0) ∗ ((sp + 0x3d8#64) ↦₆₄ c1) ∗ ((sp + 0x3e0#64) ↦₃₂ c2) ∗
                  ((sp + 0x3e4#64) ↦₆₄ c3) ∗ ((sp + 0x3ec#64) ↦₆₄ c4) ∗
                  ((sp + 0x400#64) ↦₆₄ c0) ∗ ((sp + 0x408#64) ↦₆₄ c1) ∗
                  ((sp + 0x440#64) ↦₆₄ c3) ∗ ((sp + 0x448#64) ↦₆₄ c4) ∗
                  ((sp + 0x4a0#64) ↦₃₂ r0) ∗ ((sp + 0x4a4#64) ↦₆₄ r1) ∗
                  ((sp + 0x4ac#64) ↦₆₄ r2) ∗ ((sp + 0x4b4#64) ↦₆₄ r3) ∗ ((sp + 0x4bc#64) ↦₃₂ r4) ∗
                  ((sp + 0x4c0#64) ↦₆₄ c3) ∗ ((sp + 0x4c8#64) ↦₆₄ c4) ∗
                  ((sp + 0x4d0#64) ↦₆₄ c0) ∗ ((sp + 0x4d8#64) ↦₆₄ c1) ∗
                  ((sp + 0x500#64) ↦₆₄ r2) ∗ ((sp + 0x508#64) ↦₆₄ r3) ∗
                  ((sp + 0x510#64) ↦₃₂ r4)) ∗ R)))
  wpp_778_to_rng :
    ∀ (s0 s : State) (u0 u1 u2 u3 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1912#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x0 = sp + 0x190#64 → s.readReg64 .x1 = 32#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readVReg128 0#5 = 0#128 → s.trace = s0.trace →
      SepWP prog rngFillEntry s
        (((sp + 0x190#64) ↦₆₄ u0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ u1) ∗
         ((sp + 0x190#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ u3))
        (fun sc P_c =>
          sc.sp = sp ∧ sc.readReg64 .x0 = sp + 0x190#64 ∧ sc.readReg64 .x1 = 32#64 ∧
          sc.readReg64 .x30 = entry + 1920#64 ∧ CalleeSavedPreserved s sc ∧ sc.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_c ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₆₄ 0#64) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ 0#64) ∗
                  ((sp + 0x190#64 + 16#64) ↦₆₄ 0#64) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ 0#64)) ∗ R)))
  wpp_780_to_7a8 :
    ∀ (s0 s : State) (b0 b31 : BitVec 8),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1920#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x23 = sp + 0x500#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 1960#64) s (((sp + 0x190#64) ↦₈ b0) ∗ ((sp + 0x1af#64) ↦₈ b31))
        (fun s' P' =>
          s'.sp = sp ∧ s'.readReg64 .x0 = sp + 0x500#64 ∧ s'.readReg64 .x8 = sp + 0x400#64 ∧
          s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x20 = s.readReg64 .x20 ∧
          s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
          s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = sp + 0x400#64 ∧
          s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
          s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
          s'.readReg64 .x29 = s0.sp - 96#64 ∧ s'.trace = s0.trace ∧
          calleeSavedVRegs s' = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P' ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₈ (b0 &&& 0xf8#8)) ∗
                  ((sp + 0x1af#64) ↦₈ ((b31 &&& 0x7f#8) ||| 0x40#8))) ∗ R)))
  wpp_7a8_to_dpk :
    ∀ (s0 s : State) (p0 p1 p2 p3 u0 u1 u2 u3 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1960#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x0 = sp + 0x500#64 → s.readReg64 .x8 = sp + 0x400#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      SepWP prog (lsmpl.base 200) s
        (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
         ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3) ∗
         ((sp + 0x500#64) ↦₆₄ u0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ u1) ∗
         ((sp + 0x500#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ u3))
        (fun sc P_c =>
          sc.sp = sp ∧ sc.readReg64 .x0 = sp + 0x500#64 ∧ sc.readReg64 .x8 = sp + 0x400#64 ∧
          sc.readReg64 .x30 = entry + 1972#64 ∧ CalleeSavedPreserved s sc ∧ sc.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_c ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3) ∗
                  ((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) ∗ R)))
  wpp_7b4_to_sd :
    ∀ (s0 s : State) (p0 p1 p2 p3 u0 u1 u2 u3 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1972#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x28 = sp + 0x3d0#64 → s.trace = s0.trace →
      SepWP prog (lsmpl.ρ "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop") s
        (((sp + 0x420#64) ↦₆₄ u0) ∗ ((sp + 0x420#64 + 8#64) ↦₆₄ u1) ∗
         ((sp + 0x420#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x420#64 + 24#64) ↦₆₄ u3) ∗
         ((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
         ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3))
        (fun sc P_c =>
          sc.sp = sp ∧ sc.readReg64 .x0 = sp + 0x500#64 ∧ sc.readReg64 .x30 = entry + 1988#64 ∧
          CalleeSavedPreserved s sc ∧ sc.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_c ∗ R) →
            (m ⊨ (((sp + 0x420#64) ↦₆₄ p0) ∗ ((sp + 0x420#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x420#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x420#64 + 24#64) ↦₆₄ p3) ∗
                  ((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) ∗ R)))
  wpp_7c4_to_cc2 :
    ∀ (s0 s2 : State) (msgA : BitVec 64),
      let sp := s0.sp - 1504#64
      s2.pc = entry + 1988#64 → s2.status = .Running → s2.sp = sp → s2.spAligned = true →
      s2.readReg64 .x22 = msgA → s2.readReg64 .x24 = sp + 0x400#64 →
      s2.readReg64 .x29 = s0.sp - 96#64 → s2.trace = s0.trace →
      SepWP prog (lsmpl.base 40) s2 emp
        (fun s' P' =>
          s'.sp = sp ∧ s'.readReg64 .x0 = sp + 0x4a0#64 ∧ s'.readReg64 .x1 = msgA + 56#64 ∧
          s'.readReg64 .x2 = sp + 0x420#64 ∧ s'.readReg64 .x8 = sp + 0x190#64 ∧
          s'.readReg64 .x30 = entry + 2008#64 ∧ CalleeSavedPreserved s2 s' ∧ s'.trace = s0.trace ∧
          (∀ m R, (m ⊨ P' ∗ R) → (m ⊨ R)))

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep

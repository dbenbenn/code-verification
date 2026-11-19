/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStep
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetSteps -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepErr
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import ProofLib.RegChain
import ProofLib.Sep

/-!
# `VmPreserved` Branch and Pre-`create_chain` Steppers for `DhStep`

Lifts the relocatable `[LibsignalPlacement]` error-tail, missing-sender-chain, branch, and
`+0x70c → lsmpl.base 40` key-generation steppers of `DhStep` to carry `VmPreserved`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetAux

open Arm64 ProofLib
open CryptoGames.Ratchet (clampScalar keyToBytesVec32)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey Crypto KeyPair RootKey SessionState TripleRatchet
)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecAt vecU8At)
open CryptoVerification.LibsignalSessionRepr (
  chainAt chainKeyBytes msgTypeByte optSenderChainBytes ratchetAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  coinsOf invalidSessionStructureStr issStr_lengths protocolAddressAt sessionStateAt
  signalMessageAt speWord strRefAt tapeAfter utf8
)
open CryptoVerification.LibsignalTripleRatchet (
  TrGhost TryDecryptGhost createChainResultAt logOff trAt
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  DhStepStatePlaced ErrTailStatePlaced speBodyAt speTag
  tryDecryptCommonHeap tryDecryptMidMetaPlaced
  tryDecryptPlacedImg tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (
  DhStepAfterRecvChainStatePlaced optSenderChainBytes_none_pointsTo32
  split_190_4e0_for_cc2 split_1a0_56 split_400_500_for_keygen split_memRegion_for_7f8
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (derivePublicKeyBytesBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetSteps (
  dhStep_step_70c_to_778_vm_placed dhStep_step_778_to_780_vm_placed
  dhStep_step_780_to_7a8_vm_placed dhStep_step_7a8_to_7b4_vm_placed
  dhStep_step_7b4_to_7d4_vm_placed lsStaticDropSym rngFillAtBudgetSpec zeroizeSecretBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp (DhStepBlockVmWp)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem dhStep_err_tail_from_2dc_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (w2c0 w2c8 : BitVec 64) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 0x2dc#64) (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx12 : s.readReg64 .x12 = s0.sp - 1504#64 + 0x2c0#64)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨ memRegion (s0.sp - 1504#64 + 0x140#64) 0x180 ∗
      ((s0.sp - 1504#64 + 0x2c0#64) ↦₆₄ w2c0) ∗ ((s0.sp - 1504#64 + 0x2c8#64) ↦₆₄ w2c8) ∗
      memRegion (s0.sp - 1504#64 + 0x2d0#64) 0x2b0 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧ s'.pc = entry + 0x30c#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
      s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
      s'.readReg64 .x26 = s.readReg64 .x26 ∧
      (s'.mem ⊨ memRegion (s0.sp - 1504#64 + 0x140#64) 0x28 ∗
        ((s0.sp - 1504#64 + 0x168#64) ↦₆₄ w2c0) ∗ ((s0.sp - 1504#64 + 0x170#64) ↦₆₄ w2c8) ∗
        memRegion (s0.sp - 1504#64 + 0x178#64) 24 ∗
        memRegion (s0.sp - 1504#64 + 0x190#64) 0x3f0 ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64 with hsp_def
  have h140_split : memRegion (sp + 0x140#64) 0x180 =
      memRegion (sp + 0x140#64) 0x28 ∗ (∃∗ u168 : BitVec 64, (sp + 0x168#64) ↦₆₄ u168) ∗
      (∃∗ u170 : BitVec 64, (sp + 0x170#64) ↦₆₄ u170) ∗ (∃∗ u178 : BitVec 64, (sp + 0x178#64) ↦₆₄ u178) ∗
      (∃∗ u180 : BitVec 64, (sp + 0x180#64) ↦₆₄ u180) ∗ (∃∗ u188 : BitVec 32, (sp + 0x188#64) ↦₃₂ u188) ∗
      (∃∗ u18c : BitVec 32, (sp + 0x18c#64) ↦₃₂ u18c) ∗ memRegion (sp + 0x190#64) 0x120 ∗
      (∃∗ u2b0 : BitVec 64, (sp + 0x2b0#64) ↦₆₄ u2b0) ∗ (∃∗ u2b8 : BitVec 64, (sp + 0x2b8#64) ↦₆₄ u2b8) := by
    sep_interval_eq
  have h2d0_split : memRegion (sp + 0x2d0#64) 0x2b0 =
      (∃∗ u2d0 : BitVec 32, (sp + 0x2d0#64) ↦₃₂ u2d0) ∗ memRegion (sp + 0x2d4#64) 0x5c ∗
      (∃∗ u330 : BitVec 64, (sp + 0x330#64) ↦₆₄ u330) ∗ (∃∗ u338 : BitVec 64, (sp + 0x338#64) ↦₆₄ u338) ∗
      (∃∗ u340 : BitVec 32, (sp + 0x340#64) ↦₃₂ u340) ∗ (∃∗ u344 : BitVec 64, (sp + 0x344#64) ↦₆₄ u344) ∗
      (∃∗ u34c : BitVec 64, (sp + 0x34c#64) ↦₆₄ u34c) ∗ memRegion (sp + 0x354#64) 0x22c := by
    sep_interval_eq
  rw [h140_split, h2d0_split] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u34c, u344, u340, u338, u330, u2d0, u2b8, u2b0, u18c, u188, u180, u178, u170, u168, hmem⟩
  have hwp1 := hwp.wpp_2dc_to_30c s0 s w2c0 w2c8 u34c u344 u338 u330 u2b8 u2b0 u180 u178 u170 u168
    u340 u2d0 u18c u188 hpc hrun hsp hsp_al hx29 hx12 hx20 hx25 htrace hvregs
  obtain ⟨s', hsteps, hout⟩ := hwp1.elim (Satisfies.mono (by dsimp only [sp]; bi_frame) hmem) hcode
  obtain ⟨hpcs', hruns', P_f, hmem', hvms', hsp', hx29', hx19', hx20', hx26', htrace', hvregs', hent⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al' : s'.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp', ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  refine ⟨s', hsteps, hvms', hpcs',
    ⟨hruns', hsp', hsp0_al, hsp_al', hx29', htrace', hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs'⟩,
    hx19', hx20', hx26', ?_⟩
  exact Satisfies.mono (by dsimp only [sp]; bi_entail) (hent s'.mem _ hmem')

theorem dhStep_err_tail_from_7f8_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {A : RustAlloc}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 0x7f8#64) (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (hmem : s.mem ⊨ memRegion (s0.sp - 1504#64 + 0x140#64) 0x58 ∗
      ((s0.sp - 1504#64 + 0x198#64) ↦₆₄ speWord 10) ∗
      memRegion (s0.sp - 1504#64 + 0x1a0#64) 0x3e0 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧ s'.pc = entry + 0x30c#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
      s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
      s'.readReg64 .x26 = speTag .invalidKeyAgreement ∧
      (s'.mem ⊨ memRegion (s0.sp - 1504#64 + 0x140#64) 0x28 ∗
        speBodyAt A (utf8 "decrypt") (s0.sp - 1504#64 + 0x168#64) .invalidKeyAgreement ∗
        memRegion (s0.sp - 1504#64 + 0x190#64) 0x3f0 ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64 with hsp_def
  rw [split_memRegion_for_7f8 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u508, u500, u2d0, u2c8, u2c0, u2b8, u2b0, hmem⟩
  have hwp1 := hwp.wpp_7f8_to_2dc s0 s u508 u500 u2c8 u2c0 u2b8 u2b0 u2d0
    hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
  obtain ⟨sm, hsteps1, hout⟩ := hwp1.elim (Satisfies.mono (by dsimp only [sp]; bi_frame) hmem) hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hvmm, hsp_m, hx29_m, hx12_m, hx19_m, hx20_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl.of_keepsFrozen hsteps1.keepsFrozen, hvregs_m⟩
  have hmem_m0 : sm.mem ⊨ memRegion (sp + 0x140#64) 0x440 ∗ Rest :=
    Satisfies.mono (by dsimp only [sp]; bi_entail) (hent_m sm.mem _ hmem_m)
  have h2c0_split : memRegion (sp + 0x140#64) 0x440 =
      memRegion (sp + 0x140#64) 0x180 ∗ (∃∗ w2c0 : BitVec 64, (sp + 0x2c0#64) ↦₆₄ w2c0) ∗
      (∃∗ w2c8 : BitVec 64, (sp + 0x2c8#64) ↦₆₄ w2c8) ∗ memRegion (sp + 0x2d0#64) 0x2b0 := by
    sep_interval_eq
  rw [h2c0_split] at hmem_m0
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem_m0
  rcases hmem_m0 with ⟨w2c8, w2c0, hmem_m0⟩
  obtain ⟨s', hsteps2, hvm2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_2dc_vm_placed hwp w2c0 w2c8 Rest s0 sm
      hpcm hmeta_m hx12_m hx20_m hx25_m
      (Satisfies.mono (by dsimp only [sp]; bi_entail) hmem_m0) (hsteps1.codeLoaded hcode)
  refine ⟨s', Steps.trans hsteps1 hsteps2, hvmm.trans hvm2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s',
    hx26s'.trans hx26_m, ?_⟩
  dsimp only [speBodyAt]
  exact Satisfies.mono (by dsimp only [sp]; sep_interval) hmems'

theorem dhStep_missing_sender_chain_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {A : RustAlloc} {ctl : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hnone : tr.ratchet.senderChain = none)
    (hs3 : DhStepStatePlaced entry A ctl x trG tr st1 R s0 s)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧
      ErrTailStatePlaced entry A ctl x trG tr st1 (.invalidSessionStructure .missingSenderChain) 0 R s0 s' := by
  obtain ⟨hpc, hmeta, hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩ := hs3
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64 with hsp_def
  have hsc_tag : ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) =
      (((sp + 0x50#64) ↦₃₂ 0#32) ∗ ((sp + 0x54#64) ↦ₛ trG.ratchet.senderPad)) := by
    rw [hnone, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith,
        optSenderChainBytes_none_pointsTo32 (sp + 0x50#64) trG.ratchet.senderPad,
        show sp + 0x50#64 + 4#64 = sp + 0x54#64 by bv_arith]
  have h2c0_split : memRegion (sp + 0x140#64) 0x440 =
      memRegion (sp + 0x140#64) 0x180 ∗ (∃∗ u2c0 : BitVec 64, (sp + 0x2c0#64) ↦₆₄ u2c0) ∗
      (∃∗ u2c8 : BitVec 64, (sp + 0x2c8#64) ↦₆₄ u2c8) ∗ memRegion (sp + 0x2d0#64) 0x2b0 := by
    sep_interval_eq
  unfold trAt ratchetAt at hmem
  rw [hsc_tag, h2c0_split] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u2c8, u2c0, hmem⟩
  have hwp1 := hwp.wpp_missing_sc s0 s x u2c0 u2c8 hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx25 hx27 hx28 htrace hvregs
  have hmem_framed : s.mem ⊨
      (((sp + 0x50#64) ↦₃₂ 0#32) ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗ ((sp + 0x2c8#64) ↦₆₄ u2c8)) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       (⌜∀ sc, tr.ratchet.senderChain = some sc →
          clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
        (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
          trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
         vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
           (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
         ((sp + 0x54#64) ↦ₛ trG.ratchet.senderPad) ∗
         ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
         ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
         ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
         memRegion (sp + 0x38#64 + 172#64) 4) ∗
        vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
        ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
        ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ∗
       memRegion x.ret 48 ∗ memRegion (sp + 0x140#64) 0x180 ∗ memRegion (sp + 0x2d0#64) 0x2b0 ∗
       tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem
  obtain ⟨sm, hsteps1, hout⟩ := hwp1.elim hmem_framed hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hvmm, hsp_m, hx29_m, hx12_m, hx19_m, hx20_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl.of_keepsFrozen hsteps1.keepsFrozen, hvregs_m⟩
  have hmem_m0 := hent_m sm.mem _ hmem_m
  have hmem_m' : sm.mem ⊨ memRegion (sp + 0x140#64) 0x180 ∗
      ((sp + 0x2c0#64) ↦₆₄ hwp.missingScAddr) ∗ ((sp + 0x2c8#64) ↦₆₄ 20#64) ∗
      memRegion (sp + 0x2d0#64) 0x2b0 ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x38 ∗ tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R) := by
    unfold trAt ratchetAt; rw [hsc_tag]
    exact Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem_m0
  obtain ⟨s', hsteps2, hvm2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_2dc_vm_placed hwp hwp.missingScAddr 20#64
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x38 ∗ tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R)
      s0 sm hpcm hmeta_m hx12_m hx20_m hx25_m hmem_m' (hsteps1.codeLoaded hcode)
  refine ⟨s', Steps.trans hsteps1 hsteps2, hvmm.trans hvm2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s'.trans hx26_m, ?_⟩
  dsimp only [speBodyAt]; unfold strRefAt
  have hro : s'.mem ⊨ (hwp.missingScAddr ↦ᵣ invalidSessionStructureStr .missingSenderChain) ∗
      (memRegion (sp + 0x140#64) 0x28 ∗ ((sp + 0x168#64) ↦₆₄ hwp.missingScAddr) ∗
       ((sp + 0x170#64) ↦₆₄ 20#64) ∗ memRegion (sp + 0x178#64) 24 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
       (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
        memRegion x.ret 48 ∗ memRegion sp 0x38 ∗ tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R)) :=
    hwp.hro_missingSc hmetas'.2.2.2.2.2.2.1.2 hmems'
  have hlen : BitVec.ofNat 64 (invalidSessionStructureStr .missingSenderChain).length = 20#64 := by rw [issStr_lengths.1]
  rw [hlen, show sp + 0x168#64 + 8#64 = sp + 0x170#64 by bv_arith,
      show sp + 0x168#64 + 16#64 = sp + 0x178#64 by bv_arith]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨hwp.missingScAddr, ?_⟩
  dsimp only [sp] at hro ⊢
  exact Eq.mp (congrArg (s'.mem ⊨ ·) (by sep_ac_rfl)) hro

theorem dhStep_cc1_err_branch_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {A : RustAlloc}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 1352#64) (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (hmem : s.mem ⊨ memRegion (s0.sp - 1504#64 + 0x140#64) 0x50 ∗
      createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.error .invalidKeyAgreement) ∗
      memRegion (s0.sp - 1504#64 + 0x1d8#64) 0x3a8 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧ s'.pc = entry + 0x30c#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
      s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
      s'.readReg64 .x26 = speTag .invalidKeyAgreement ∧
      (s'.mem ⊨ memRegion (s0.sp - 1504#64 + 0x140#64) 0x28 ∗
        speBodyAt A (utf8 "decrypt") (s0.sp - 1504#64 + 0x168#64) .invalidKeyAgreement ∗
        memRegion (s0.sp - 1504#64 + 0x190#64) 0x3f0 ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64 with hsp_def
  dsimp only [createChainResultAt] at hmem
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_arith,
      show sp + 0x190#64 + 8#64 = sp + 0x198#64 by bv_arith,
      show sp + 0x190#64 + 16#64 = sp + 0x1a0#64 by bv_arith, split_1a0_56 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u1c4, u1bc, u1b4, u1b0, u1a8, u1a0, hmem⟩
  have hwp1 := hwp.wpp_cc1_err s0 s u1bc u1b4 u1a8 u1a0 u1c4 u1b0
    hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
  obtain ⟨sm, hsteps1, hout⟩ := hwp1.elim (Satisfies.mono (by dsimp only [sp]; bi_frame) hmem) hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hvmm, hsp_m, hx29_m, hx19_m, hx20_m, hx23_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl.of_keepsFrozen hsteps1.keepsFrozen, hvregs_m⟩
  obtain ⟨s', hsteps2, hvm2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_7f8_vm_placed hwp Rest s0 sm hpcm hmeta_m hx20_m hx23_m hx25_m hx26_m
      (Satisfies.mono (by sep_interval) (hent_m sm.mem _ hmem_m))
      (hsteps1.codeLoaded hcode)
  exact ⟨s', Steps.trans hsteps1 hsteps2, hvmm.trans hvm2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s', hmems'⟩

theorem dhStep_cc1_ok_branch_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (rk1 : RootKey) (rck : ChainKey) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 1352#64) (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨ createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.ok (rk1, rck)) ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧ s'.pc = entry + 0x70c#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨ ((s0.sp - 1504#64 + 0x190#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 1504#64 + 0x194#64) ↦ₛ keyToBytes32 rk1) ∗
        ((s0.sp - 1504#64 + 0x1b4#64) ↦ₛ chainKeyBytes rck) ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64 with hsp_def
  dsimp only [createChainResultAt] at hmem
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_arith,
      show sp + 0x190#64 + 0x24#64 = sp + 0x1b4#64 by bv_arith] at hmem
  have hwp1 := hwp.wpp_cc1_ok s0 s hpc hrun hsp hsp_al hx25 htrace
  obtain ⟨sm, hsteps1, hout⟩ := hwp1.elim (Satisfies.mono (by dsimp only [sp]; bi_frame) hmem) hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hvmm, hsp_m, hcs_m, htrace_m, hent_m⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := by reg_chain
  have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl.of_keepsFrozen hsteps1.keepsFrozen, by reg_chain⟩
  exact ⟨sm, hsteps1, hvmm, hpcm, hmeta_m, hcs_m, Satisfies.mono (by dsimp only [sp]; bi_entail) (hent_m sm.mem _ hmem_m)⟩

theorem dhStep_cc2_ok_branch_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (finalRootKey : RootKey) (senderChainKey : ChainKey) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 2008#64) (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨ createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.ok (finalRootKey, senderChainKey)) ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧ s'.pc = entry + 0x8ac#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨ ((s0.sp - 1504#64 + 0x190#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 1504#64 + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((s0.sp - 1504#64 + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64 with hsp_def
  dsimp only [createChainResultAt] at hmem
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_arith,
      show sp + 0x190#64 + 0x24#64 = sp + 0x1b4#64 by bv_arith] at hmem
  have hwp1 := hwp.wpp_cc2_ok s0 s hpc hrun hsp hsp_al hx25 htrace
  obtain ⟨sm, hsteps1, hout1⟩ := hwp1.elim (Satisfies.mono (by dsimp only [sp]; bi_frame) hmem) hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hvmm, hsp_m, hcs_m, htrace_m, hent_m⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := hcs_m.2.2.2.2.2.2.2.2.2.2.1.trans hx29
  have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl.of_keepsFrozen hsteps1.keepsFrozen, by reg_chain⟩
  exact ⟨sm, hsteps1, hvmm, hpcm, hmeta_m, hcs_m, Satisfies.mono (by dsimp only [sp]; bi_entail) (hent_m sm.mem _ hmem_m)⟩

theorem dhStep_cc2_err_branch_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {A : RustAlloc}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry) (msgW : BitVec 32) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 2008#64) (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (hmem : s.mem ⊨ ((s0.sp - 1504#64 + 0x1c#64) ↦₃₂ msgW) ∗
      memRegion (s0.sp - 1504#64 + 0x140#64) 0x50 ∗
      createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.error .invalidKeyAgreement) ∗
      memRegion (s0.sp - 1504#64 + 0x1d8#64) 0x3a8 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧ s'.pc = entry + 0x30c#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
      s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
      s'.readReg64 .x26 = speTag .invalidKeyAgreement ∧
      (s'.mem ⊨ ((s0.sp - 1504#64 + 0x1c#64) ↦₃₂ msgW) ∗
        memRegion (s0.sp - 1504#64 + 0x140#64) 0x28 ∗
        speBodyAt A (utf8 "decrypt") (s0.sp - 1504#64 + 0x168#64) .invalidKeyAgreement ∗
        memRegion (s0.sp - 1504#64 + 0x190#64) 0x3f0 ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64 with hsp_def
  dsimp only [createChainResultAt] at hmem
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_arith,
      show sp + 0x190#64 + 8#64 = sp + 0x198#64 by bv_arith,
      show sp + 0x190#64 + 16#64 = sp + 0x1a0#64 by bv_arith, split_1a0_56 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u1c4, u1bc, u1b4, u1b0, u1a8, u1a0, hmem⟩
  have hwp1 := hwp.wpp_cc2_err s0 s msgW u1bc u1b4 u1a8 u1a0 u1c4 u1b0
    hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
  obtain ⟨sm, hsteps1, hout1⟩ := hwp1.elim (Satisfies.mono (by dsimp only [sp]; bi_frame) hmem) hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hvmm, hsp_m, hx29_m, hx19_m, hx20_m, hx23_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl.of_keepsFrozen hsteps1.keepsFrozen, hvregs_m⟩
  obtain ⟨s', hsteps2, hvm2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_7f8_vm_placed (A := A) hwp (((sp + 0x1c#64) ↦₃₂ msgW) ∗ Rest) s0 sm hpcm hmeta_m
      hx20_m hx23_m hx25_m hx26_m
      (Satisfies.mono (by dsimp only [sp]; sep_interval) (hent_m sm.mem _ hmem_m))
      (hsteps1.codeLoaded hcode)
  exact ⟨s', Steps.trans hsteps1 hsteps2, hvmm.trans hvm2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s',
    Satisfies.mono (by dsimp only [sp]; bi_entail) hmems'⟩

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetAux

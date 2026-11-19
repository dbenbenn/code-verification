/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepTightTargets -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import ProofLib.RegChain
import ProofLib.Sep

/-!
# Segment S3 (`DhStep`) Proofs for `try_decrypt_with_state`

Re-exports `DhStepDefs`, `DhStepErr`, `DhStepRecvChain`, `DhStepBlocks`, and `DhStepMain`, and
proves the relocatable `[LibsignalPlacement]` Segment S3 seam theorems (`s3_placed_ok`,
`s3_placed_okT`, and block `130` / `433` specializations).
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

/-! ## Relocatable `[LibsignalPlacement]` Stepping & Segment S3 Theorems -/

theorem dhStep_err_tail_from_2dc_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} (hwp : DhStepBlockWp prog entry rngFillEntry)
    (w2c0 w2c8 : BitVec 64) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 0x2dc#64) (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx12 : s.readReg64 .x12 = s0.sp - 1504#64 + 0x2c0#64)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨ memRegion (s0.sp - 1504#64 + 0x140#64) 0x180 ∗
      ((s0.sp - 1504#64 + 0x2c0#64) ↦₆₄ w2c0) ∗ ((s0.sp - 1504#64 + 0x2c8#64) ↦₆₄ w2c8) ∗
      memRegion (s0.sp - 1504#64 + 0x2d0#64) 0x2b0 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ s'.pc = entry + 0x30c#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
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
  obtain ⟨hpcs', hruns', P_f, hmem', hsp', hx29', hx19', hx20', hx26', htrace', hvregs', hent⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al' : s'.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp', ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  refine ⟨s', hsteps, hpcs',
    ⟨hruns', hsp', hsp0_al, hsp_al', hx29', htrace', hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs'⟩,
    hx19', hx20', hx26', ?_⟩
  exact Satisfies.mono (by dsimp only [sp]; bi_entail) (hent s'.mem _ hmem')

theorem dhStep_err_tail_from_7f8_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {A : RustAlloc}
    (hwp : DhStepBlockWp prog entry rngFillEntry) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 0x7f8#64) (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (hmem : s.mem ⊨ memRegion (s0.sp - 1504#64 + 0x140#64) 0x58 ∗
      ((s0.sp - 1504#64 + 0x198#64) ↦₆₄ speWord 10) ∗
      memRegion (s0.sp - 1504#64 + 0x1a0#64) 0x3e0 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ s'.pc = entry + 0x30c#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
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
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hx29_m, hx12_m, hx19_m, hx20_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
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
  obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_2dc_placed hwp w2c0 w2c8 Rest s0 sm
      hpcm hmeta_m hx12_m hx20_m hx25_m
      (Satisfies.mono (by dsimp only [sp]; bi_entail) hmem_m0) (hsteps1.codeLoaded hcode)
  refine ⟨s', Steps.trans hsteps1 hsteps2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s',
    hx26s'.trans hx26_m, ?_⟩
  dsimp only [speBodyAt]
  exact Satisfies.mono (by dsimp only [sp]; sep_interval) hmems'

theorem dhStep_missing_sender_chain_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {A : RustAlloc} {ctl : BitVec 64}
    (hwp : DhStepBlockWp prog entry rngFillEntry)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hnone : tr.ratchet.senderChain = none)
    (hs3 : DhStepStatePlaced entry A ctl x trG tr st1 R s0 s) :
    reaches_pc prog (entry + 0x30c#64) s
      (ErrTailStatePlaced entry A ctl x trG tr st1 (.invalidSessionStructure .missingSenderChain) 0 R s0) := by
  intro hcode
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
          Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
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
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hmem
  obtain ⟨sm, hsteps1, hout⟩ := hwp1.elim hmem_framed hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hx29_m, hx12_m, hx19_m, hx20_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
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
    exact Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hmem_m0
  obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_2dc_placed hwp hwp.missingScAddr 20#64
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x38 ∗ tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R)
      s0 sm hpcm hmeta_m hx12_m hx20_m hx25_m hmem_m' (hsteps1.codeLoaded hcode)
  refine ⟨s', Steps.trans hsteps1 hsteps2, Or.inl ⟨hpcs', hmetas'.1, ?_⟩⟩
  refine ⟨hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s'.trans hx26_m, ?_⟩
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
  exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hro

theorem dhStep_cc1_err_branch_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {A : RustAlloc}
    (hwp : DhStepBlockWp prog entry rngFillEntry) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 1352#64) (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (hmem : s.mem ⊨ memRegion (s0.sp - 1504#64 + 0x140#64) 0x50 ∗
      createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.error .invalidKeyAgreement) ∗
      memRegion (s0.sp - 1504#64 + 0x1d8#64) 0x3a8 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ s'.pc = entry + 0x30c#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
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
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hx29_m, hx19_m, hx20_m, hx23_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl.of_keepsFrozen hsteps1.keepsFrozen, hvregs_m⟩
  obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_7f8_placed hwp Rest s0 sm hpcm hmeta_m hx20_m hx23_m hx25_m hx26_m
      (Satisfies.mono (by sep_interval) (hent_m sm.mem _ hmem_m))
      (hsteps1.codeLoaded hcode)
  exact ⟨s', Steps.trans hsteps1 hsteps2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s', hmems'⟩

theorem dhStep_cc1_ok_branch_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} (hwp : DhStepBlockWp prog entry rngFillEntry)
    (rk1 : RootKey) (rck : ChainKey) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 1352#64) (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨ createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.ok (rk1, rck)) ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ s'.pc = entry + 0x70c#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
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
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hcs_m, htrace_m, hent_m⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := by reg_chain
  have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl.of_keepsFrozen hsteps1.keepsFrozen, by reg_chain⟩
  exact ⟨sm, hsteps1, hpcm, hmeta_m, hcs_m, Satisfies.mono (by dsimp only [sp]; bi_entail) (hent_m sm.mem _ hmem_m)⟩

theorem dhStep_cc2_ok_branch_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} (hwp : DhStepBlockWp prog entry rngFillEntry)
    (finalRootKey : RootKey) (senderChainKey : ChainKey) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 2008#64) (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨ createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.ok (finalRootKey, senderChainKey)) ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ s'.pc = entry + 0x8ac#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
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
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hcs_m, htrace_m, hent_m⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := hcs_m.2.2.2.2.2.2.2.2.2.2.1.trans hx29
  have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl.of_keepsFrozen hsteps1.keepsFrozen, by reg_chain⟩
  exact ⟨sm, hsteps1, hpcm, hmeta_m, hcs_m, Satisfies.mono (by dsimp only [sp]; bi_entail) (hent_m sm.mem _ hmem_m)⟩

theorem dhStep_cc2_err_branch_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {A : RustAlloc}
    (hwp : DhStepBlockWp prog entry rngFillEntry) (msgW : BitVec 32) (Rest : SepProp) (s0 s : State)
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
    ∃ s', Steps prog s s' ∧ s'.pc = entry + 0x30c#64 ∧ tryDecryptMidMetaPlaced s0 s' ∧
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
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hx29_m, hx19_m, hx20_m, hx23_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl.of_keepsFrozen hsteps1.keepsFrozen, hvregs_m⟩
  obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_7f8_placed (A := A) hwp (((sp + 0x1c#64) ↦₃₂ msgW) ∗ Rest) s0 sm hpcm hmeta_m
      hx20_m hx23_m hx25_m hx26_m
      (Satisfies.mono (by dsimp only [sp]; sep_interval) (hent_m sm.mem _ hmem_m))
      (hsteps1.codeLoaded hcode)
  exact ⟨s', Steps.trans hsteps1 hsteps2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s',
    Satisfies.mono (by dsimp only [sp]; bi_entail) hmems'⟩

theorem dhStep_recv_create_chain_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    (hwp : DhStepBlockWp prog entry rngFillEntry) (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpec C A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain) (R : SepProp) (s0 s : State)
    (hsc : tr.ratchet.senderChain = some sc) (hrk1_ne : s0.sp - 1504#64 + 0x3b0#64 ≠ 0#64)
    (hs3 : DhStepStatePlaced entry A ctl x trG tr st1 R s0 s) (hcode : prog.CodeLoaded s.mem) :
    match rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | .ok (rk1, rck) =>
      ∃ s', Steps prog s s' ∧
        (DhStepAfterRecvChainStatePlaced entry A ctl x trG tr st1 rk1 rck R s0 s' ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)))
    | .error e =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG' r1, ErrTailStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 e 0 R s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  obtain ⟨hpc, hmeta, hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩ := hs3
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hpriv_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 := sc.ratchetKey.privateKey.bytes.2
  have hrk_len : (keyToBytes32 tr.ratchet.rootKey).length = 32 := length_keyToBytes32 _
  obtain ⟨p0, hp0⟩ : ∃ v, pack64 (sc.ratchetKey.privateKey.bytes.toList.take 8) = v := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ v, pack64 ((sc.ratchetKey.privateKey.bytes.toList.drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ v, pack64 ((sc.ratchetKey.privateKey.bytes.toList.drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ v, pack64 (sc.ratchetKey.privateKey.bytes.toList.drop 24) = v := ⟨_, rfl⟩
  obtain ⟨k0, hk0⟩ : ∃ v, pack64 ((keyToBytes32 tr.ratchet.rootKey).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ v, pack64 (((keyToBytes32 tr.ratchet.rootKey).drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ v, pack64 (((keyToBytes32 tr.ratchet.rootKey).drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k3, hk3⟩ : ∃ v, pack64 ((keyToBytes32 tr.ratchet.rootKey).drop 24) = v := ⟨_, rfl⟩
  have hsc_split : ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) =
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗ ((sp + 0x84#64) ↦₆₄ p2) ∗
       ((sp + 0x8c#64) ↦₆₄ p3) ∗ ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) := by
    rw [hsc, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith, optSenderChainBytes_some_split sp sc trG.ratchet.senderPad,
        pointsTo_32_as_four_64 (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len, hp0, hp1, hp2, hp3,
        show sp + 0x74#64 + 8#64 = sp + 0x7c#64 by bv_arith, show sp + 0x74#64 + 16#64 = sp + 0x84#64 by bv_arith,
        show sp + 0x74#64 + 24#64 = sp + 0x8c#64 by bv_arith]; ac_rfl
  have hrk_split : ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) =
      (((sp + 0xb8#64) ↦₆₄ k0) ∗ ((sp + 0xc0#64) ↦₆₄ k1) ∗ ((sp + 0xc8#64) ↦₆₄ k2) ∗ ((sp + 0xd0#64) ↦₆₄ k3)) := by
    rw [show sp + 0x38#64 + 128#64 = sp + 0xb8#64 by bv_arith,
        pointsTo_32_as_four_64 (sp + 0xb8#64) (keyToBytes32 tr.ratchet.rootKey) hrk_len, hk0, hk1, hk2, hk3,
        show sp + 0xb8#64 + 8#64 = sp + 0xc0#64 by bv_arith, show sp + 0xb8#64 + 16#64 = sp + 0xc8#64 by bv_arith,
        show sp + 0xb8#64 + 24#64 = sp + 0xd0#64 by bv_arith]
  unfold trAt ratchetAt at hmem
  rw [hsc_split, hrk_split, split_140_for_cc1 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3c8, u3c0, u3b8, u3b0, u3a8, u3a0, u398, u390, hmem⟩
  have hwp1 := hwp.wpp_pre_cc1 s0 s x p0 p1 p2 p3 k0 k1 k2 k3 u390 u398 u3a0 u3a8 u3b0 u3b8 u3c0 u3c8
    hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 htrace hvregs
  have hmem_framed : s.mem ⊨
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3) ∗ ((sp + 0xb8#64) ↦₆₄ k0) ∗
       ((sp + 0xc0#64) ↦₆₄ k1) ∗ ((sp + 0xc8#64) ↦₆₄ k2) ∗ ((sp + 0xd0#64) ↦₆₄ k3) ∗
       ((sp + 0x390#64) ↦₆₄ u390) ∗ ((sp + 0x398#64) ↦₆₄ u398) ∗ ((sp + 0x3a0#64) ↦₆₄ u3a0) ∗
       ((sp + 0x3a8#64) ↦₆₄ u3a8) ∗ ((sp + 0x3b0#64) ↦₆₄ u3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u3c8)) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       (⌜∀ sc', tr.ratchet.senderChain = some sc' →
          Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
        (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
          trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
         vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
           (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
         ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗ ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
         ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
         ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗ memRegion (sp + 0x38#64 + 172#64) 4) ∗
        vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
        ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
        ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 72 ∗ memRegion (sp + 0x1d8#64) 0x1b8 ∗ memRegion (sp + 0x3d0#64) 0x1b0 ∗
       tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hmem
  obtain ⟨sc1, hsteps1, hout1⟩ := hwp1.elim hmem_framed hcode
  obtain ⟨hpcc1, hrunc1, P_c1, hmem_c1, hsp_c1, hx0_c1, hx1_c1, hx2_c1, hx8_c1,
    hx19_c1, hx20_c1, hx21_c1, hx22_c1, hx23_c1, hx24_c1, hx25_c1, hx26_c1, hx27_c1, hx28_c1,
    hx29_c1, hx30_c1, htrace_c1, hvregs_c1, hent_c1⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c1 : sc1.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_c1, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hcl_c1 := hcl.of_keepsFrozen hsteps1.keepsFrozen
  have hmem_c1_0 := hent_c1 sc1.mem _ hmem_c1
  have h74_fold : ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
      (((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗ ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len, hp0, hp1, hp2, hp3,
        show sp + 0x74#64 + 8#64 = sp + 0x7c#64 by bv_arith, show sp + 0x74#64 + 16#64 = sp + 0x84#64 by bv_arith,
        show sp + 0x74#64 + 24#64 = sp + 0x8c#64 by bv_arith]
  have h390_fold : ((sp + 0x390#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
      (((sp + 0x390#64) ↦₆₄ p0) ∗ ((sp + 0x398#64) ↦₆₄ p1) ∗ ((sp + 0x3a0#64) ↦₆₄ p2) ∗ ((sp + 0x3a8#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x390#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len, hp0, hp1, hp2, hp3,
        show sp + 0x390#64 + 8#64 = sp + 0x398#64 by bv_arith, show sp + 0x390#64 + 16#64 = sp + 0x3a0#64 by bv_arith,
        show sp + 0x390#64 + 24#64 = sp + 0x3a8#64 by bv_arith]
  have h3b0_fold : ((sp + 0x3b0#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) =
      (((sp + 0x3b0#64) ↦₆₄ k0) ∗ ((sp + 0x3b8#64) ↦₆₄ k1) ∗ ((sp + 0x3c0#64) ↦₆₄ k2) ∗ ((sp + 0x3c8#64) ↦₆₄ k3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x3b0#64) (keyToBytes32 tr.ratchet.rootKey) hrk_len, hk0, hk1, hk2, hk3,
        show sp + 0x3b0#64 + 8#64 = sp + 0x3b8#64 by bv_arith, show sp + 0x3b0#64 + 16#64 = sp + 0x3c0#64 by bv_arith,
        show sp + 0x3b0#64 + 24#64 = sp + 0x3c8#64 by bv_arith]
  have hb8_zero : ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 (0 : RootKey)) =
      (((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗ ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64)) := by
    rw [show sp + 0x38#64 + 128#64 = sp + 0xb8#64 by bv_arith, ← pointsTo64_zero_32 (sp + 0xb8#64),
        show sp + 0xb8#64 + 8#64 = sp + 0xc0#64 by bv_arith, show sp + 0xb8#64 + 16#64 = sp + 0xc8#64 by bv_arith,
        show sp + 0xb8#64 + 24#64 = sp + 0xd0#64 by bv_arith]
  have htr0_fold : trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } =
      (⌜∀ sc', tr.ratchet.senderChain = some sc' →
          Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
       (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
         trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
        vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
          (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
        (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
         (((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗ ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3)) ∗
         ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) ∗
        (((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗ ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64)) ∗
        ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
        ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗ memRegion (sp + 0x38#64 + 172#64) 4) ∗
       vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
       ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) := by
    unfold trAt ratchetAt; dsimp only
    rw [hsc, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith,
        optSenderChainBytes_some_split sp sc trG.ratchet.senderPad, h74_fold, hb8_zero]
  let ccG1 : CreateChainGhost :=
    { rkA := sp + 0x3b0#64, rk := tr.ratchet.rootKey, theirA := x.msgA + 56#64,
      their := x.msg.senderRatchetKey, ourA := sp + 0x390#64, our := sc.ratchetKey.privateKey, ret := sp + 0x190#64 }
  let Frame1 : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x1d8#64) 0x1b8 ∗ memRegion (sp + 0x3d0#64) 0x1b0 ∗
    protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageRestAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest 0 ∗ logOff tryDecryptPlacedImg ∗
    stackAt (sp - BitVec.ofNat 64 createChainStack) (tryDecryptSubStack - createChainStack) ∗ tryDecryptSavedRegs s0.sp s0
  have hpre_cc1 : sc1.mem ⊨ (createChainSpec C A).pre ccG1 sc1 ∗ (Frame1 ∗ R) := by
    dsimp only [createChainSpec, ccG1, Frame1]; simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c1, hx1_c1, hx2_c1, hx8_c1, hrk1_ne⟩, ?_⟩
    rw [htr0_fold, h390_fold, h3b0_fold, show sc1.sp = sp from hsp_c1]
    unfold tryDecryptCommonHeap at hmem_c1_0
    rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
        show s0.sp - 1504#64 = sp from rfl, stackAt_subStack_createChain sp] at hmem_c1_0
    exact Eq.mp (congrArg (sc1.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hmem_c1_0
  obtain ⟨sm, hsteps_cc1, hout_cc1, _⟩ :=
    hcc.no_fault_before_outcome ccG1 (Frame1 ∗ R) sc1 hpcc1 hrunc1 hpre_cc1 hsp_al_c1 (hsteps1.codeLoaded hcode)
  have hsteps12 : Steps prog s sm := Steps.trans hsteps1 hsteps_cc1
  rcases hout_cc1 with ⟨hret_m, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, -, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · have hpcm : sm.pc = entry + 1352#64 := hret_m.1.trans hx30_c1
    have hrunm : sm.status = .Running := hret_m.2.2
    dsimp only [createChainSpec, ccG1] at hpost; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hcl_m := hcl_c1.of_keepsFrozen hsteps_cc1.keepsFrozen
    have htrace_m0 := hpost.1; have hpost := hpost.2
    have htrace_m : sm.trace = s0.trace := htrace_m0.trans htrace_c1
    have hsp_m : sm.sp = s0.sp - 1504#64 := hspm.trans hsp_c1
    have hsp_al_m : sm.spAligned = true := by unfold State.spAligned at hsp_al_c1 ⊢; rw [hspm]; exact hsp_al_c1
    have hx19_m : sm.readReg64 .x19 = x.ret := hcsm.1.trans hx19_c1
    have hx20_m : sm.readReg64 .x20 = sp + 0x140#64 := hcsm.2.1.trans hx20_c1
    have hx21_m : sm.readReg64 .x21 = x.ss := hcsm.2.2.1.trans hx21_c1
    have hx22_m : sm.readReg64 .x22 = x.msgA := hcsm.2.2.2.1.trans hx22_c1
    have hx23_m : sm.readReg64 .x23 = sp + 0x500#64 := hcsm.2.2.2.2.1.trans hx23_c1
    have hx24_m : (sm.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by rw [hcsm.2.2.2.2.2.1]; exact hx24_c1
    have hx25_m : sm.readReg64 .x25 = sp + 0x190#64 := hcsm.2.2.2.2.2.2.1.trans hx25_c1
    have hx26_m : sm.readReg64 .x26 = sp + 0x2c0#64 := hcsm.2.2.2.2.2.2.2.1.trans hx26_c1
    have hx27_m : sm.readReg64 .x27 = sp + 0x38#64 := hcsm.2.2.2.2.2.2.2.2.1.trans hx27_c1
    have hx28_m : sm.readReg64 .x28 = sp + 0x2c0#64 := hcsm.2.2.2.2.2.2.2.2.2.1.trans hx28_c1
    have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c1
    have hmeta_m : tryDecryptMidMetaPlaced s0 sm := ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl_m, by reg_chain⟩
    have hpost_grouped : sm.mem ⊨
        (memRegion (sp + 0x1d8#64) 0x1b8 ∗ ((sp + 0x390#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
         ((sp + 0x3b0#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗ memRegion (sp + 0x3d0#64) 0x1b0) ∗
        (memRegion (sp + 0x140#64) 0x50 ∗
         createChainResultAt (sp + 0x190#64) (rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
         memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
         memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
         tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R) := by
      dsimp only [Frame1] at hpost; rw [show sc1.sp = sp from hsp_c1] at hpost; unfold tryDecryptCommonHeap
      rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
          show s0.sp - 1504#64 = sp from rfl, stackAt_subStack_createChain sp]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hpost
    have hpost_folded := Satisfies.mono (sepConj_mono_left (fold_390_3b0_to_memRegion sp _ _ hpriv_len hrk_len)) hpost_grouped
    unfold rootCreateChain at hpost_folded ⊢
    cases hcc1 : Ratchet.createChain C.F C.X tr.ratchet.rootKey x.msg.senderRatchetKey.bytes sc.ratchetKey.privateKey.bytes with
    | none =>
      rw [hcc1] at hpost_folded; dsimp only [hcc1] at hpost_folded ⊢
      let Rest_err : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R
      have hmem_err : sm.mem ⊨ memRegion (sp + 0x140#64) 0x50 ∗
          createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗ memRegion (sp + 0x1d8#64) 0x3a8 ∗ Rest_err :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_err, sp]; ac_rfl)) hpost_folded
      obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
        dhStep_cc1_err_branch_placed (A := A) hwp Rest_err s0 sm hpcm hmeta_m
          hx20_m hx23_m hx25_m hx26_m hmem_err (hsteps12.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps12 hsteps2, Or.inl ⟨trG, { tr.ratchet with rootKey := (0 : RootKey) }, ?_⟩⟩
      refine ⟨hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s', ?_⟩
      dsimp only [Rest_err] at hmems'
      exact Satisfies.mono (by dsimp only [sp]; sep_interval) hmems'
    | some p1 =>
      rcases p1 with ⟨rk1, rckKey⟩; rw [hcc1] at hpost_folded; dsimp only [hcc1] at hpost_folded ⊢
      let Rest_ok : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x1d8#64) 0x3a8 ∗
        tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R
      have hmem_ok : sm.mem ⊨ createChainResultAt (sp + 0x190#64) (.ok (rk1, ⟨rckKey, 0⟩)) ∗ Rest_ok :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_ok, sp]; ac_rfl)) hpost_folded
      obtain ⟨s', hsteps2, hpcs', hmetas', hcss', hmems'⟩ :=
        dhStep_cc1_ok_branch_placed hwp rk1 ⟨rckKey, 0⟩ Rest_ok s0 sm hpcm hmeta_m hx25_m hmem_ok (hsteps12.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps12 hsteps2, Or.inl ?_⟩
      refine ⟨hpcs', hmetas',
        hcss'.1.trans hx19_m, hcss'.2.1.trans hx20_m, hcss'.2.2.1.trans hx21_m,
        hcss'.2.2.2.1.trans hx22_m, hcss'.2.2.2.2.1.trans hx23_m,
        by rw [hcss'.2.2.2.2.2.1]; exact hx24_m,
        hcss'.2.2.2.2.2.2.1.trans hx25_m, hcss'.2.2.2.2.2.2.2.1.trans hx26_m,
        hcss'.2.2.2.2.2.2.2.2.1.trans hx27_m, hcss'.2.2.2.2.2.2.2.2.2.1.trans hx28_m, ?_⟩
      dsimp only [Rest_ok, sp] at hmems' ⊢; exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems'
  · have hpan_td := onPanic_of_createChain_placed (ctl := ctl) (S := S) (x := x) htrace_c1 hpost
    cases rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | ok p1 => rcases p1 with ⟨rk1, rck⟩; exact ⟨sm, hsteps12, Or.inr ⟨hpan, hpan_td⟩⟩
    | error e => exact ⟨sm, hsteps12, Or.inr ⟨hpan, hpan_td⟩⟩
  · dsimp only [createChainSpec] at hpost; rw [satisfies_pure_sepConj] at hpost; exact False.elim hpost.1

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep


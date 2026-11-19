/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKey -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStack
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainSym

/-!
# Segment S2 (`FindChain`) Proofs for `try_decrypt_with_state`

Verifies Segment S2 (`+0x2a4 → +0x3e4 / +0x500 / +0x30c`), calling
`RatchetState::find_receiver_chain_key` and branching to `ConsumeMsgKeyState` (`Ok(Some ck)`),
`DhStepState` (`Ok(None)`), or `ErrTailState` (`Err e`).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem findChain_after_call_ok_none_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 680#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x20 ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 0x190#64) (.ok none) ∗
      memRegion ((s0.sp - 1504#64) + 0x1b8#64) 0x3c8 ∗
      tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segDhStepPC_placed s
      (DhStepState_placed A ctl x trG tr st1 R s0) := by
  let sp := s0.sp - 1504#64
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    (((sp + 0x190#64) ↦₃₂ 0#32) ∗ memRegion (sp + 0x190#64 + 4#64) 36) ∗
    memRegion (sp + 0x1b8#64) 0x3c8 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R at hm
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_omega,
      memRegion_split (sp + 0x1b8#64) 0x1c8 0x200 (by decide),
      show (sp + 0x1b8#64) + BitVec.ofNat 64 0x1c8 = sp + 0x380#64 by bv_omega,
      memRegion_split (sp + 0x380#64) 16 0x1f0 (by decide),
      show (sp + 0x380#64) + 16#64 = sp + 0x390#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ memRegion (sp + 0x194#64) 36 ∗
      (memRegion (sp + 0x380#64) 16 ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0x1c8 ∗ memRegion (sp + 0x390#64) 0x1f0 ∗
       tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, hm2⟩ := exists_words36_of_memRegion_36 hm1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm2
  have hm3 : s.mem ⊨ memRegion (sp + 0x380#64) 16 ∗
      ((((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
        ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗ memRegion x.ret 48 ∗ memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x1b8#64) 0x1c8 ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨d0, d1, hm4⟩ := exists_words16_of_memRegion_16 hm3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm4
  let F_none :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1b8#64) 0x1c8 ∗ memRegion (sp + 0x390#64) 0x1f0 ∗
    tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x194#64) ↦₃₂ w0) ∗
       ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x380#64) ↦₆₄ d0) ∗ ((sp + 0x388#64) ↦₆₄ d1)) ∗ F_none := by
    dsimp only [F_none]; convert hm4 using 1; sep_ac_rfl
  have hwp := findChain_ok_none_full_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (d0 := d0) (d1 := d1)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx25 hx28
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨hPf, hwpInv_f, hx12_f, hcs⟩ hinv_f hmf
  subst hPf
  refine ⟨hpcf, hwpInv_f.to_midMeta_placed hinv_f, hx12_f,
    (hcs.1).trans hx19, (hcs.2.1).trans hx20, (hcs.2.2.1).trans hx21,
    (hcs.2.2.2.1).trans hx22, (hcs.2.2.2.2.1).trans hx23,
    by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hcs.2.2.2.2.2.1]; exact hx24,
    (hcs.2.2.2.2.2.2.1).trans hx25, (hcs.2.2.2.2.2.2.2.2.1).trans hx27,
    (hcs.2.2.2.2.2.2.2.2.2.1).trans hx28, ?_⟩
  have hmf_re : sf.mem ⊨
      (memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗
        ((sp + 0x1a0#64) ↦₆₄ w2) ∗ ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x1b8#64) 0x1c8 ∗
       (((sp + 0x380#64) ↦₆₄ w3) ∗ ((sp + 0x388#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x390#64) 0x1f0) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    dsimp only [F_none, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono (sepConj_mono_left (findChain_none_stack_recombine sp w0 w1 w2 w3 w4)) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

theorem findChain_after_call_ok_some_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 680#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x20 ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 0x190#64) (.ok (some ck)) ∗
      memRegion ((s0.sp - 1504#64) + 0x1b8#64) 0x3c8 ∗
      tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segConsumeMsgKeyPC_placed s
      (ConsumeMsgKeyState_placed A ctl x trG tr st1 ck 0 R s0) := by
  let sp := s0.sp - 1504#64
  have htake_len : ((chainKeyBytes ck).take 20).length = 20 := by
    rw [List.length_take_of_le (by rw [chainKeyBytes_length]; decide)]
  have hdrop_len : ((chainKeyBytes ck).drop 20).length = 16 := by
    rw [List.length_drop, chainKeyBytes_length]
  obtain ⟨w0, w1, w2, hw20⟩ := exists_words20_of_length_20 htake_len
  obtain ⟨w3, w4, hw16⟩ := exists_words16_of_length_16 hdrop_len
  have hck_split :
      ((sp + 0x190#64 + 4#64) ↦ₛ chainKeyBytes ck) =
        (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
        (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) := by
    rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_omega,
        ← List.take_append_drop 20 (chainKeyBytes ck), pointsToBytes_append, htake_len,
        show (sp + 0x194#64) + BitVec.ofNat 64 20 = sp + 0x1a8#64 by bv_omega,
        hw20 (sp + 0x194#64), hw16 (sp + 0x1a8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x190#64 + 4#64) ↦ₛ chainKeyBytes ck)) ∗
    memRegion (sp + 0x1b8#64) 0x3c8 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R at hm
  rw [hck_split,
      memRegion_split (sp + 0x1b8#64) 0xf8 0x2d0 (by decide),
      show (sp + 0x1b8#64) + BitVec.ofNat 64 0xf8 = sp + 0x2b0#64 by bv_omega,
      memRegion_split (sp + 0x2b0#64) 16 0x2c0 (by decide),
      show (sp + 0x2b0#64) + 16#64 = sp + 0x2c0#64 by bv_omega,
      memRegion_split (sp + 0x2c0#64) 20 0x2ac (by decide),
      show (sp + 0x2c0#64) + 20#64 = sp + 0x2d4#64 by bv_omega,
      memRegion_split (sp + 0x2d4#64) 0xac 0x200 (by decide),
      show (sp + 0x2d4#64) + BitVec.ofNat 64 0xac = sp + 0x380#64 by bv_omega,
      memRegion_split (sp + 0x380#64) 16 0x1f0 (by decide),
      show (sp + 0x380#64) + 16#64 = sp + 0x390#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ memRegion (sp + 0x2b0#64) 16 ∗
      (memRegion (sp + 0x2c0#64) 20 ∗ memRegion (sp + 0x380#64) 16 ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
       (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0xf8 ∗ memRegion (sp + 0x2d4#64) 0xac ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨b0, b1, hm2⟩ := exists_words16_of_memRegion_16 hm1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm2
  have hm3 : s.mem ⊨ memRegion (sp + 0x2c0#64) 20 ∗
      ((((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1)) ∗
       memRegion (sp + 0x380#64) 16 ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
       (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0xf8 ∗ memRegion (sp + 0x2d4#64) 0xac ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨c0, c1, c2, hm4⟩ := exists_words20_of_memRegion_20 hm3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm4
  have hm5 : s.mem ⊨ memRegion (sp + 0x380#64) 16 ∗
      ((((sp + 0x2c0#64) ↦₃₂ c0) ∗ ((sp + 0x2c4#64) ↦₆₄ c1) ∗ ((sp + 0x2cc#64) ↦₆₄ c2)) ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1)) ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
       (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0xf8 ∗ memRegion (sp + 0x2d4#64) 0xac ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨d0, d1, hm6⟩ := exists_words16_of_memRegion_16 hm5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm6
  let F_some :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1b8#64) 0xf8 ∗ memRegion (sp + 0x2d4#64) 0xac ∗
    memRegion (sp + 0x390#64) 0x1f0 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x194#64) ↦₃₂ w0) ∗
       ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1) ∗
       ((sp + 0x2c0#64) ↦₃₂ c0) ∗ ((sp + 0x2c4#64) ↦₆₄ c1) ∗
       ((sp + 0x2cc#64) ↦₆₄ c2) ∗ ((sp + 0x380#64) ↦₆₄ d0) ∗
       ((sp + 0x388#64) ↦₆₄ d1)) ∗ F_some := by
    dsimp only [F_some]; convert hm6 using 1; sep_ac_rfl
  have hwp := findChain_ok_some_full_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (b0 := b0) (b1 := b1) (c0 := c0) (c1 := c1) (c2 := c2) (d0 := d0) (d1 := d1)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx25 hx28
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨hPf, hwpInv_f, hx12_f, hcs⟩ hinv_f hmf
  subst hPf
  refine ⟨hpcf, hwpInv_f.to_midMeta_placed hinv_f, hx12_f,
    (hcs.1).trans hx19, (hcs.2.1).trans hx20, (hcs.2.2.1).trans hx21,
    (hcs.2.2.2.1).trans hx22, (hcs.2.2.2.2.1).trans hx23,
    by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hcs.2.2.2.2.2.1]; exact hx24,
    (hcs.2.2.2.2.2.2.1).trans hx25, ?_⟩
  have h2b0 : (((sp + 0x2b0#64) ↦₆₄ w3) ∗ ((sp + 0x2b8#64) ↦₆₄ w4)) =
      ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes ck).drop 20) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using (hw16 (sp + 0x2b0#64)).symm
  have h2c0 : (((sp + 0x2c0#64) ↦₃₂ w0) ∗ ((sp + 0x2c4#64) ↦₆₄ w1) ∗ ((sp + 0x2cc#64) ↦₆₄ w2)) =
      ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes ck).take 20) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using (hw20 (sp + 0x2c0#64)).symm
  have hmf_re : sf.mem ⊨
      (memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
        ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x1b8#64) 0xf8) ∗
      (memRegion (sp + 0x2d4#64) 0xac ∗
       (((sp + 0x380#64) ↦₆₄ w3) ∗ ((sp + 0x388#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x390#64) 0x1f0) ∗
      (((sp + 0x2b0#64) ↦₆₄ w3) ∗ ((sp + 0x2b8#64) ↦₆₄ w4)) ∗
      (((sp + 0x2c0#64) ↦₃₂ w0) ∗ ((sp + 0x2c4#64) ↦₆₄ w1) ∗ ((sp + 0x2cc#64) ↦₆₄ w2)) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    dsimp only [F_some, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  rw [h2b0, h2c0] at hmf_re
  have hmf2 := Satisfies.mono
    (sepConj_mono (findChain_some_stack_recombine_left sp w0 w1 w2 w3 w4)
      (sepConj_mono_left (findChain_some_stack_recombine_right sp w3 w4))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

theorem tryDecryptMidMetaPlaced.to_placed [LibsignalPlacement] {s0 s : State}
    (h : tryDecryptMidMetaPlaced s0 s) :
    tryDecryptMidMeta_placed s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1.1, h.2.2.2.2.2.2.2⟩,
   h.2.2.2.2.2.2.1.2⟩

theorem tryDecryptMidMeta_placed.to_placed [LibsignalPlacement] {s0 s : State}
    (h : tryDecryptMidMeta_placed s0 s) (hro : LibsignalRoLoaded lsmpl s.mem) :
    tryDecryptMidMetaPlaced s0 s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ⟨h.2.2.2.2.2.2.1, hro⟩, h.2.2.2.2.2.2.2⟩

theorem FindChainStatePlaced.to_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : FindChainStatePlaced (blkPl_131).base A ctl x trG tr st1 R s0 s) :
    FindChainState_placed A ctl x trG tr st1 R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced.to_placed h.2.1).1, h.2.2⟩, (tryDecryptMidMetaPlaced.to_placed h.2.1).2⟩

theorem DhStepStatePlaced.of_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : DhStepState_placed A ctl x trG tr st1 R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    DhStepStatePlaced (blkPl_131).base A ctl x trG tr st1 R s0 s :=
  ⟨h.1, h.2.1.to_placed hro, h.2.2⟩

theorem ConsumeMsgKeyStatePlaced.of_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {draws : Nat} {R : SepProp} {s0 s : State}
    (h : ConsumeMsgKeyState_placed A ctl x trG tr st1 ck draws R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    ConsumeMsgKeyStatePlaced (blkPl_131).base A ctl x trG tr st1 ck draws R s0 s :=
  ⟨h.1, h.2.1.to_placed hro, h.2.2⟩

theorem ErrTailStatePlaced.of_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat} {R : SepProp} {s0 s : State}
    (h : ErrTailState_placed A ctl x trG tr st1 e draws R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    ErrTailStatePlaced (blkPl_131).base A ctl x trG tr st1 e draws R s0 s :=
  ⟨h.1, h.2.1.to_placed hro, h.2.2⟩

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

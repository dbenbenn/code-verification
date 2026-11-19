/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.LoopHw
import ProofLib.BV
import Arm64.Trusted.ISA.Eval
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Fixslice64 Software Full-Block CBC Loop (`+0x2d0..+0x4c8 -> +0x4cc`) (`CbcEnc.LoopSw`)

Verifies the `STORAGE != 1` full-block CBC encryption loop (`0` or `k + 1` blocks), bridging each
`aes256_encrypt` call to `Spec.Aes256.aes256Enc` and storing the running chain block at
`[x24, #0x3c0..0x3cf]` (`sp + 0x1050#64`) and ciphertext at `outBuf`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.LoopSw

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open CryptoGames.CBC (Block bytesToBlock blockToBytesLE)
open CryptoGames.HKDF (bytesToKey32)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (aes256KeyScheduleFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (fsKeys256At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
  (Aes256EncHwAddrs CbcEncCode Aes256CbcEncryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
  (cbcEncBlocks cbcChain ptFullBlocks length_blockToBytesLE)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
  (CbcPreserved byte16Cells16 byte16At pointsToBytes_16_eq_byte16At
   byte16Cells16_entails_memRegion_16 memRegion_16_eq_pts8
   inPad6Cells memRegion_48_eq_pts64 inPad6_entails_memRegion_48)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers
  (step_strSimd128_64_perm step_stpSimd128_64_perm zext32_zext64_eq trunc32_zext64_eq
   xor_zext_byte extractLsb_append64_lo extractLsb_append64_hi
   byte16Cells16_xor_eq call_aes256_encrypt_single)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.LoopHw
  (ptBlocksOf ptBlocksOf_eq_ptFullBlocks)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

private def SwPrevRegs (s : State) (prev : Block) : Prop :=
  let ps := blockToBytesLE prev
  s.readReg64 (.gpr 9#5) = (ps.getD 0 0#8).zeroExtend 64 ∧ s.readReg64 (.gpr 10#5) = (ps.getD 1 0#8).zeroExtend 64 ∧
  s.readReg64 (.gpr 8#5) = (ps.getD 2 0#8).zeroExtend 64 ∧ s.readReg64 (.gpr 11#5) = (ps.getD 3 0#8).zeroExtend 64 ∧
  s.readReg64 (.gpr 12#5) = (ps.getD 4 0#8).zeroExtend 64 ∧ s.readReg64 (.gpr 13#5) = (ps.getD 5 0#8).zeroExtend 64 ∧
  s.readReg64 (.gpr 14#5) = (ps.getD 6 0#8).zeroExtend 64 ∧ s.readReg64 (.gpr 15#5) = (ps.getD 7 0#8).zeroExtend 64 ∧
  s.readReg64 (.gpr 16#5) = (ps.getD 8 0#8).zeroExtend 64 ∧ s.readReg64 (.gpr 3#5) = (ps.getD 9 0#8).zeroExtend 64 ∧
  s.readReg64 (.gpr 2#5) = (ps.getD 10 0#8).zeroExtend 64 ∧ s.readReg64 (.gpr 1#5) = (ps.getD 11 0#8).zeroExtend 64 ∧
  s.readReg64 (.gpr 0#5) = (ps.getD 12 0#8).zeroExtend 64 ∧ s.readReg64 (.gpr 18#5) = (ps.getD 13 0#8).zeroExtend 64 ∧
  s.readReg64 (.gpr 17#5) = (ps.getD 14 0#8).zeroExtend 64 ∧ s.readReg64 (.gpr 4#5) = (ps.getD 15 0#8).zeroExtend 64

private theorem SwPrevRegs.of_eq_gprs {s1 s2 : State} {b : Block} (h : SwPrevRegs s1 b)
    (heq : ∀ r : BitVec 5, r ≠ 25#5 → s2.readReg64 (.gpr r) = s1.readReg64 (.gpr r)) : SwPrevRegs s2 b := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  exact ⟨(heq 9#5 (by decide)).trans h0, (heq 10#5 (by decide)).trans h1, (heq 8#5 (by decide)).trans h2,
    (heq 11#5 (by decide)).trans h3, (heq 12#5 (by decide)).trans h4, (heq 13#5 (by decide)).trans h5,
    (heq 14#5 (by decide)).trans h6, (heq 15#5 (by decide)).trans h7, (heq 16#5 (by decide)).trans h8,
    (heq 3#5 (by decide)).trans h9, (heq 2#5 (by decide)).trans h10, (heq 1#5 (by decide)).trans h11,
    (heq 0#5 (by decide)).trans h12, (heq 18#5 (by decide)).trans h13, (heq 17#5 (by decide)).trans h14,
    (heq 4#5 (by decide)).trans h15⟩

private theorem byte16At_inPad6_entails_memRegion_64 (inPtr : BitVec 64) (bs : List (BitVec 8))
    (u0 u1 u2 u3 u4 u5 : BitVec 64) :
    byte16At inPtr bs ∗ inPad6Cells inPtr u0 u1 u2 u3 u4 u5 ⊢ memRegion inPtr 64 := by
  rw [memRegion_split inPtr 16 48 (by decide)]
  exact sepConj_mono (byte16Cells16_entails_memRegion_16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (inPad6_entails_memRegion_48 inPtr u0 u1 u2 u3 u4 u5)

section
arm64_proof_prelude
attribute [local irreducible] aes256KeyScheduleFs fsKeys256At Spec.Aes256.aes256Enc bytesToKey32
attribute [local simp, local arm64_norm] zext32_zext64_eq trunc32_zext64_eq xor_zext_byte

@[local simp, local arm64_norm] private theorem trunc8_xor_zext32 (a b : BitVec 8) :
    (a.zeroExtend 32 ^^^ b.zeroExtend 32).truncate 8 = a ^^^ b := by bv_bits
@[local simp, local arm64_norm] private theorem trunc8_zext32 (a : BitVec 8) : (a.zeroExtend 32).truncate 8 = a := by bv_bits
@[local simp, local arm64_norm] private theorem trunc8_zext64 (a : BitVec 8) : (a.zeroExtend 64).truncate 8 = a := by bv_bits
@[local simp, local arm64_norm] private theorem sp_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_advancePC (s : State) : s.advancePC.sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_setMem (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_setPState (s : State) (p : PState) : (s.setPState p).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_writeVReg128 (s : State) (n : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 n v).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_writeReg64_gpr (s : State) (n : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr n) v).sp = s.sp := by simp [State.writeReg64]
@[local simp, local arm64_norm] private theorem readReg64_sp_eq (s : State) : s.readReg64 .sp = s.sp := rfl

private theorem cbcPreserved_setPC (s : State) (pc : BitVec 64) : CbcPreserved s (s.setPC pc) :=
  CbcPreserved.of_proj_perm (by cases s; rfl) (by cases s; rfl)

private theorem cbcPreserved_setPC_right {s0 s : State} {pc : BitVec 64} (h : CbcPreserved s0 s) :
    CbcPreserved s0 (s.setPC pc) := h.trans (cbcPreserved_setPC s pc)

private theorem readReg64_of_calleeSaved {s1 s2 : State} (hcs : CalleeSavedPreserved s1 s2)
    (r : BitVec 5) (h19 : 19 ≤ r.toNat) (h29 : r.toNat ≤ 29) :
    s2.readReg64 (.gpr r) = s1.readReg64 (.gpr r) := by
  rcases r with ⟨⟨v, _⟩⟩; simp [BitVec.toNat] at h19 h29
  have : v = 19 ∨ v = 20 ∨ v = 21 ∨ v = 22 ∨ v = 23 ∨ v = 24 ∨
         v = 25 ∨ v = 26 ∨ v = 27 ∨ v = 28 ∨ v = 29 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hcs.readReg64_x19, hcs.readReg64_x20, hcs.readReg64_x21, hcs.readReg64_x22,
    hcs.readReg64_x23, hcs.readReg64_x24, hcs.readReg64_x25, hcs.readReg64_x26,
    hcs.readReg64_x27, hcs.readReg64_x28, hcs.readReg64_x29]

local macro "wp_strSimd128 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_strSimd128_64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close (first | wp_norm_lhs | simp [wp_norm, arm64_norm, extractLsb_append64_lo, extractLsb_append64_hi]))
  (· wp_focus_close (first | wp_norm_lhs | simp [wp_norm, arm64_norm, extractLsb_append64_lo, extractLsb_append64_hi]))
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

local macro "wp_stpSimd128 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stpSimd128_64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close (first | wp_norm_lhs | simp [wp_norm, arm64_norm, extractLsb_append64_lo, extractLsb_append64_hi]))
  (· wp_focus_close (first | wp_norm_lhs | simp [wp_norm, arm64_norm, extractLsb_append64_lo, extractLsb_append64_hi]))
  (· wp_focus_close (first | wp_norm_lhs | simp [wp_norm, arm64_norm, extractLsb_append64_lo, extractLsb_append64_hi]))
  (· wp_focus_close (first | wp_norm_lhs | simp [wp_norm, arm64_norm, extractLsb_append64_lo, extractLsb_append64_hi]))
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

/-! ## 1. Iteration Pre-Call (`+0x320..+0x3f8`) & Post-Call (`+0x3fc..+0x4c8`) Steps -/

private theorem step_sw_iter_pre {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc inCur sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    {blkBs : List (BitVec 8)} (hblk : blkBs.length = 16) (prev : Block)
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x320#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (hprev : SwPrevRegs s prev)
    (hx22 : s.readReg64 (.gpr 22#5) = inCur + 7#64) (hx24 : s.readReg64 (.gpr 24#5) = sp + 0xc90#64)
    (hx28 : s.readReg64 (.gpr 28#5) = sp + 0x106c#64) (hx29 : s.readReg64 (.gpr 29#5) = sp + 0x10c0#64)
    (hnext : ∀ s1 : State,
      s1.pc = fnAddr + 0x3f8#64 → s1.status = .Running → s1.sp = sp →
      CbcPreserved s s1 → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 (.gpr 0#5) = sp + 0xc90#64 → s1.readReg64 (.gpr 1#5) = sp + 0x106c#64 →
      s1.readReg64 (.gpr 8#5) = sp + 0x7d0#64 →
      (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 → s1.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      SepWP P target_pc s1
        ((byte16At inCur blkBs ∗ byte16At (sp + 0x106c#64) (blockToBytesLE (bytesToBlock blkBs ^^^ prev)) ∗
          inPad6Cells (sp + 0x106c#64) 0#64 0#64 0#64 0#64 0#64 0#64) ∗ F) post oom) :
    SepWP P target_pc s ((byte16At inCur blkBs ∗ memRegion (sp + 0x106c#64) 64) ∗ F) post oom := by
  rcases hprev with ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15⟩
  rw [memRegion_split (sp + 0x106c#64) 16 48 (by decide),
      memRegion_16_eq_pts8 (sp + 0x106c#64), memRegion_48_eq_pts64 (sp + 0x106c#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 22 refine SepWP.exists_elim fun _ => ?_
  dsimp only [byte16At, byte16Cells16]
  have_instrs hc.segSwLoopPreA 0 27
  wp_steps 6; wp_str8 hf_6 mx0 hmx0; wp_steps 2; wp_str8 hf_9 mx1 hmx1
  wp_steps 2; wp_str8 hf_12 mx2 hmx2; wp_steps 1; wp_str8 hf_14 mx3 hmx3
  wp_steps 3; wp_str8 hf_18 mx4 hmx4; wp_steps 2; wp_str8 hf_21 mx5 hmx5
  wp_steps 1; wp_str8 hf_23 mx6 hmx6; wp_steps 3
  have_instrs hc.segSwLoopPreB 0 27
  wp_str8 hf_0 mx7 hmx7; wp_steps 2; wp_str8 hf_3 mx8 hmx8; wp_steps 1; wp_str8 hf_5 mx9 hmx9
  wp_steps 3; wp_str8 hf_9 mx10 hmx10; wp_steps 2; wp_str8 hf_12 mx11 hmx11
  wp_steps 1; wp_str8 hf_14 mx12 hmx12; wp_steps 6; wp_str8 hf_21 mx14 hmx14
  wp_steps 1; wp_str8 hf_23 mx13 hmx13; wp_str8 hf_24 mx15 hmx15
  wp_stpSimd128 hf_25 mzp0 hmzp0; wp_strSimd128 hf_26 mzp1 hmzp1
  have hperm : mzp1.perm = s.mem.perm := by
    simp [hmzp1, hmzp0, hmx15, hmx13, hmx14, hmx12, hmx11, hmx10, hmx9, hmx8,
      hmx7, hmx6, hmx5, hmx4, hmx3, hmx2, hmx1, hmx0, wp_norm, arm64_norm]
  refine SepWP.weaken_pre ?_
    (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp]) (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) hperm)
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm])
      (fun r hr19 _ => by
        simp [wp_norm, arm64_norm, show r ≠ 0#5 by bv_omega, show r ≠ 1#5 by bv_omega, show r ≠ 5#5 by bv_omega,
          show r ≠ 6#5 by bv_omega, show r ≠ 8#5 by bv_omega, show r ≠ 9#5 by bv_omega, show r ≠ 10#5 by bv_omega]))
  rw [← byte16Cells16_xor_eq (sp + 0x106c#64) hblk prev]
  dsimp only [byte16At, byte16Cells16, inPad6Cells]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem step_sw_iter_post {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc inCur outCur cnt sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (prev c : Block) {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x3fc#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_15 : sp &&& 15#64 = 0#64)
    (hx22 : s.readReg64 (.gpr 22#5) = inCur + 7#64) (hx24 : s.readReg64 (.gpr 24#5) = sp + 0xc90#64)
    (hx25 : s.readReg64 (.gpr 25#5) = outCur + 7#64) (hx27 : s.readReg64 (.gpr 27#5) = cnt)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0x4c8#64 → sf.status = .Running → sf.sp = sp → sf.pstate = subsPState64 cnt 1#64 →
      CbcPreserved s sf → calleeSavedVRegs sf = calleeSavedVRegs s → SwPrevRegs sf c →
      sf.readReg64 (.gpr 22#5) = (inCur + 16#64) + 7#64 → sf.readReg64 (.gpr 25#5) = (outCur + 16#64) + 7#64 →
      sf.readReg64 (.gpr 27#5) = cnt - 1#64 →
      (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 →
        r ≠ 22#5 → r ≠ 25#5 → r ≠ 27#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      SepWP P target_pc sf
        ((byte16At (sp + 0x7d0#64) (blockToBytesLE c) ∗ byte16At (sp + 0x1050#64) (blockToBytesLE c) ∗
          (outCur ↦ₛ blockToBytesLE c)) ∗ F) post oom) :
    SepWP P target_pc s
      ((byte16At (sp + 0x7d0#64) (blockToBytesLE c) ∗ byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗
        memRegion outCur 16) ∗ F) post oom := by
  have hsp_and : s.sp &&& 15#64 = 0#64 := hsp ▸ hsp_15
  rw [memRegion_16_eq_pts8 outCur]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 16 refine SepWP.exists_elim fun _ => ?_
  generalize h_prev : byte16At (sp + 0x1050#64) (blockToBytesLE prev) = prevCells
  dsimp only [byte16At, byte16Cells16]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have_instrs hc.segSwLoopOut 0 18; wp_steps 18
  have_instrs hc.segSwLoopCt 0 17
  wp_str8 hf_0 mc0 hmc0; wp_str8 hf_1 mc1 hmc1; wp_str8 hf_2 mc2 hmc2; wp_str8 hf_3 mc3 hmc3
  wp_str8 hf_4 mc4 hmc4; wp_str8 hf_5 mc5 hmc5; wp_str8 hf_6 mc6 hmc6; wp_str8 hf_7 mc7 hmc7
  wp_str8 hf_8 mc8 hmc8; wp_str8 hf_9 mc9 hmc9; wp_str8 hf_10 mc10 hmc10; wp_str8 hf_11 mc11 hmc11
  wp_str8 hf_12 mc12 hmc12; wp_str8 hf_13 mc13 hmc13; wp_str8 hf_14 mc14 hmc14; wp_str8 hf_15 mc15 hmc15
  wp_steps 1
  have hmc_perm : mc15.perm = s.mem.perm := by
    simp [hmc15, hmc14, hmc13, hmc12, hmc11, hmc10, hmc9, hmc8,
      hmc7, hmc6, hmc5, hmc4, hmc3, hmc2, hmc1, hmc0, wp_norm, arm64_norm]
  rw [← h_prev]; dsimp only [byte16At, byte16Cells16]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have_instrs hc.segSwLoopPrev 0 16
  wp_str8 hf_0 mp0 hmp0; wp_str8 hf_1 mp1 hmp1; wp_str8 hf_2 mp2 hmp2; wp_str8 hf_3 mp3 hmp3
  wp_str8 hf_4 mp4 hmp4; wp_str8 hf_5 mp5 hmp5; wp_str8 hf_6 mp6 hmp6; wp_str8 hf_7 mp7 hmp7
  wp_str8 hf_8 mp8 hmp8; wp_str8 hf_9 mp9 hmp9; wp_str8 hf_10 mp10 hmp10; wp_str8 hf_11 mp11 hmp11
  wp_str8 hf_12 mp12 hmp12; wp_str8 hf_13 mp13 hmp13; wp_str8 hf_14 mp14 hmp14; wp_str8 hf_15 mp15 hmp15
  have hmp_perm : mp15.perm = s.mem.perm := by
    simp [hmp15, hmp14, hmp13, hmp12, hmp11, hmp10, hmp9, hmp8,
      hmp7, hmp6, hmp5, hmp4, hmp3, hmp2, hmp1, hmp0, hmc_perm, wp_norm, arm64_norm]
  apply SepWP.weaken_pre; swap
  · exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp]) (by simp [wp_norm, arm64_norm])
      (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) hmp_perm)
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm]) (by simp [SwPrevRegs, wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm])
      (fun r hr19 _ hne22 hne25 hne27 => by
        simp [wp_norm, arm64_norm, hne22, hne25, hne27,
          show r ≠ 0#5 by bv_omega, show r ≠ 1#5 by bv_omega, show r ≠ 2#5 by bv_omega, show r ≠ 3#5 by bv_omega,
          show r ≠ 4#5 by bv_omega, show r ≠ 8#5 by bv_omega, show r ≠ 9#5 by bv_omega, show r ≠ 10#5 by bv_omega,
          show r ≠ 11#5 by bv_omega, show r ≠ 12#5 by bv_omega, show r ≠ 13#5 by bv_omega, show r ≠ 14#5 by bv_omega,
          show r ≠ 15#5 by bv_omega, show r ≠ 16#5 by bv_omega, show r ≠ 17#5 by bv_omega, show r ≠ 18#5 by bv_omega])
  rw [pointsToBytes_16_eq_byte16At outCur (length_blockToBytesLE c)]
  dsimp only [byte16At, byte16Cells16]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. Single Software Iteration Body (`+0x320..+0x4c8`) & Multi-Block Induction -/

private theorem step_sw_loop_body {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc inCur outCur cnt sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) {blkBs : List (BitVec 8)} (hblk : blkBs.length = 16) (prev : Block)
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsp_15 : sp &&& 15#64 = 0#64) (hk : x.key.length = 32)
    (hpc : s.pc = fnAddr + 0x320#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hprev : SwPrevRegs s prev)
    (hx22 : s.readReg64 (.gpr 22#5) = inCur + 7#64) (hx24 : s.readReg64 (.gpr 24#5) = sp + 0xc90#64)
    (hx25 : s.readReg64 (.gpr 25#5) = outCur + 7#64) (hx27 : s.readReg64 (.gpr 27#5) = cnt)
    (hx28 : s.readReg64 (.gpr 28#5) = sp + 0x106c#64) (hx29 : s.readReg64 (.gpr 29#5) = sp + 0x10c0#64)
    (hnext : ∀ sf : State,
      let c := Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock blkBs ^^^ prev)
      sf.pc = fnAddr + 0x4c8#64 → sf.status = .Running → sf.sp = sp →
      sf.pstate = subsPState64 cnt 1#64 → CbcPreserved s sf → calleeSavedVRegs sf = calleeSavedVRegs s →
      SwPrevRegs sf c → sf.readReg64 (.gpr 22#5) = (inCur + 16#64) + 7#64 →
      sf.readReg64 (.gpr 25#5) = (outCur + 16#64) + 7#64 → sf.readReg64 (.gpr 27#5) = cnt - 1#64 →
      (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 →
        r ≠ 22#5 → r ≠ 25#5 → r ≠ 27#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      SepWP P target_pc sf
        ((fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
          memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE c) ∗
          (inCur ↦ₛ blkBs) ∗ (outCur ↦ₛ blockToBytesLE c) ∗ stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s
      ((fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
        memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗
        (inCur ↦ₛ blkBs) ∗ memRegion outCur 16 ∗ stackAt sp allocHookStack) ∗ F) post oom := by
  rw [pointsToBytes_16_eq_byte16At inCur hblk]
  refine SepWP.weaken_pre (P' :=
      (byte16At inCur blkBs ∗ memRegion (sp + 0x106c#64) 64) ∗
      (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
        byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗ memRegion outCur 16 ∗ stackAt sp allocHookStack ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine step_sw_iter_pre hc hblk prev hpc hrun hsp hprev hx22 hx24 hx28 hx29
    fun s1 hpc1 hrun1 hsp1 hp1 hv1 hx0_1 hx1_1 hx8_1 hgpr1 => ?_
  let b0 := bytesToBlock blkBs ^^^ prev
  refine SepWP.weaken_pre (P' :=
      (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ byte16At (sp + 0x106c#64) (blockToBytesLE b0) ∗
        inPad6Cells (sp + 0x106c#64) 0#64 0#64 0#64 0#64 0#64 0#64 ∗ memRegion (sp + 0x7d0#64) 64 ∗ stackAt sp allocHookStack) ∗
      (byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗ byte16At inCur blkBs ∗ memRegion outCur 16 ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine call_aes256_encrypt_single hk b0 hc.bl_swLoopEnc hCallees.encrypt_ok
    hpc1 hrun1 hsp1 hsp_15 hx0_1 hx1_1 hx8_1 fun s2 hpc2 hrun2 hsp2 hcs2 hp2 => ?_
  rw [BitVec.add_assoc] at hpc2; simp only [BitVec.reduceAdd] at hpc2
  have hx22_2 : s2.readReg64 (.gpr 22#5) = inCur + 7#64 := by rw [hcs2.readReg64_x22, hgpr1 22#5 (by decide) (by decide), hx22]
  have hx24_2 : s2.readReg64 (.gpr 24#5) = sp + 0xc90#64 := by rw [hcs2.readReg64_x24, hgpr1 24#5 (by decide) (by decide), hx24]
  have hx25_2 : s2.readReg64 (.gpr 25#5) = outCur + 7#64 := by rw [hcs2.readReg64_x25, hgpr1 25#5 (by decide) (by decide), hx25]
  have hx27_2 : s2.readReg64 (.gpr 27#5) = cnt := by rw [hcs2.readReg64_x27, hgpr1 27#5 (by decide) (by decide), hx27]
  have hv2 : calleeSavedVRegs s2 = calleeSavedVRegs s := hcs2.vregs.trans hv1
  have hgpr2 : ∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 → s2.readReg64 (.gpr r) = s.readReg64 (.gpr r) := by
    intro r hr19 hr29; rw [readReg64_of_calleeSaved hcs2 r hr19 hr29, hgpr1 r hr19 hr29]
  have hp02 : CbcPreserved s s2 := hp1.trans hp2
  clear hcs2 hp2 hp1 hv1 hgpr1
  let c := Spec.Aes256.aes256Enc (bytesToKey32 x.key) b0
  have hmr_in : byte16At (sp + 0x106c#64) (blockToBytesLE b0) ∗
      inPad6Cells (sp + 0x106c#64) 0#64 0#64 0#64 0#64 0#64 0#64 ⊢ memRegion (sp + 0x106c#64) 64 :=
    byte16At_inPad6_entails_memRegion_64 _ _ _ _ _ _ _ _
  refine SepWP.weaken_pre (P' :=
      (byte16At (sp + 0x7d0#64) (blockToBytesLE c) ∗
        byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗ memRegion outCur 16) ∗
      (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗
        memRegion (sp + 0x7e0#64) 48 ∗ memRegion (sp + 0x106c#64) 64 ∗
        byte16At inCur blkBs ∗ stackAt sp allocHookStack ∗ F)) ?_ ?_
  · refine Entails.trans (Entails.of_eq (show _ =
        (byte16At (sp + 0x106c#64) (blockToBytesLE b0) ∗
          inPad6Cells (sp + 0x106c#64) 0#64 0#64 0#64 0#64 0#64 0#64) ∗
        ((byte16At (sp + 0x7d0#64) (blockToBytesLE c) ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗ memRegion outCur 16) ∗
         (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗
          memRegion (sp + 0x7e0#64) 48 ∗ byte16At inCur blkBs ∗
          stackAt sp allocHookStack ∗ F)) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hmr_in) (Entails.of_eq (by sep_ac_rfl))
  refine step_sw_iter_post hc prev c hpc2 hrun2 hsp2 hsp_15 hx22_2 hx24_2 hx25_2 hx27_2
    fun sf hpcf hrunf hspf hpstf hpf hvf hprevf hx22f hx25f hx27f hgprf => ?_
  have hmr_out : byte16At (sp + 0x7d0#64) (blockToBytesLE c) ∗ memRegion (sp + 0x7e0#64) 48 ⊢
      memRegion (sp + 0x7d0#64) 64 := by
    rw [memRegion_split (sp + 0x7d0#64) 16 48 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (byte16Cells16_entails_memRegion_16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  refine SepWP.weaken_pre ?_
    (hnext sf hpcf hrunf hspf hpstf (hp02.trans hpf) (hvf.trans hv2) hprevf hx22f hx25f hx27f
      (fun r hr19 hr29 hne22 hne25 hne27 =>
        (hgprf r hr19 hr29 hne22 hne25 hne27).trans (hgpr2 r hr19 hr29)))
  rw [← pointsToBytes_16_eq_byte16At inCur hblk]
  refine Entails.trans (Entails.of_eq (show _ =
      (byte16At (sp + 0x7d0#64) (blockToBytesLE c) ∗ memRegion (sp + 0x7e0#64) 48) ∗
      (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗
        memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE c) ∗
        (inCur ↦ₛ blkBs) ∗ (outCur ↦ₛ blockToBytesLE c) ∗ stackAt sp allocHookStack ∗ F) by sep_ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hmr_out) (Entails.of_eq (by sep_ac_rfl))

private theorem step_sw_loop_k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) (hsp_15 : sp &&& 15#64 = 0#64) (hk : x.key.length = 32) {s0 : State} :
    ∀ (k : Nat) {inCur outCur : BitVec 64} (prev : Block) (ptRem : List (BitVec 8))
      {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp},
      k + 1 < 2 ^ 40 → 16 * (k + 1) ≤ ptRem.length →
      s.pc = fnAddr + 0x320#64 → s.status = .Running → s.sp = sp →
      calleeSavedVRegs s = calleeSavedVRegs s0 → SwPrevRegs s prev →
      s.readReg64 (.gpr 22#5) = inCur + 7#64 → s.readReg64 (.gpr 24#5) = sp + 0xc90#64 →
      s.readReg64 (.gpr 25#5) = outCur + 7#64 → s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (k + 1) →
      s.readReg64 (.gpr 28#5) = sp + 0x106c#64 → s.readReg64 (.gpr 29#5) = sp + 0x10c0#64 →
      (∀ sf : State,
        let prevFinal := cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) prev (ptBlocksOf (k + 1) ptRem)
        sf.pc = fnAddr + 0x4cc#64 → sf.status = .Running → sf.sp = sp →
        CbcPreserved s sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
        (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 →
          r ≠ 22#5 → r ≠ 25#5 → r ≠ 27#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
        SepWP P target_pc sf
          ((fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
            memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE prevFinal) ∗
            (inCur ↦ₛ ptRem) ∗
            (outCur ↦ₛ (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) prev
              (ptBlocksOf (k + 1) ptRem)).flatMap blockToBytesLE) ∗
            stackAt sp allocHookStack) ∗ F) post oom) →
      SepWP P target_pc s
        ((fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
          memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗
          (inCur ↦ₛ ptRem) ∗ memRegion outCur (16 * (k + 1)) ∗ stackAt sp allocHookStack) ∗ F) post oom := by
  intro k; induction k with
  | zero =>
    intro inCur outCur prev ptRem s F post oom _ hpt_len hpc hrun hsp hv hprev
      hx22 hx24 hx25 hx27 hx28 hx29 hnext
    let blkBs := ptRem.take 16
    have hblk : blkBs.length = 16 := by dsimp [blkBs]; rw [List.length_take]; omega
    have hpt_split : (inCur ↦ₛ ptRem) = (inCur ↦ₛ blkBs) ∗ ((inCur + 16#64) ↦ₛ ptRem.drop 16) := by
      conv => lhs; rw [← List.take_append_drop 16 ptRem]
      rw [pointsToBytes_append, hblk, show BitVec.ofNat 64 16 = 16#64 from rfl]
    refine SepWP.weaken_pre (P' :=
        (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
          memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗
          (inCur ↦ₛ blkBs) ∗ memRegion outCur 16 ∗ stackAt sp allocHookStack) ∗
        (((inCur + 16#64) ↦ₛ ptRem.drop 16) ∗ F))
      (by rw [hpt_split, Nat.mul_one]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine step_sw_loop_body hc hCallees x hblk prev hsp_15 hk hpc hrun hsp hprev
      hx22 hx24 hx25 hx27 hx28 hx29 fun s1 hpc1 hrun1 hsp1 hpst1 hp1 hv1 _ _ _ _ hgpr1 => ?_
    have_instrs hc.segSwLoopPrev 16 1
    apply SepWP.step_pure hpc1 hrun1 hf_16 rfl (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
    conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hpst1, hpc1,
      BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.weaken_pre; swap
    · exact hnext _ (by simp only [State.setPC]) (by simp only [State.setPC, hrun1])
        (by simp only [sp_setPC, hsp1]) (cbcPreserved_setPC_right hp1)
        (by simpa only [calleeSavedVRegs, State.setPC] using hv1.trans hv)
        (fun r hr19 hr29 hne22 hne25 hne27 => by
          simpa only [State.readReg64_setPC] using hgpr1 r hr19 hr29 hne22 hne25 hne27)
    dsimp only [ptBlocksOf, cbcChain, cbcEncBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hpt_split]; exact Entails.of_eq (by sep_ac_rfl)
  | succ k ih =>
    intro inCur outCur prev ptRem s F post oom hk_lt hpt_len hpc hrun hsp hv hprev
      hx22 hx24 hx25 hx27 hx28 hx29 hnext
    let blkBs := ptRem.take 16
    have hblk : blkBs.length = 16 := by dsimp [blkBs]; rw [List.length_take]; omega
    have hpt_split : (inCur ↦ₛ ptRem) = (inCur ↦ₛ blkBs) ∗ ((inCur + 16#64) ↦ₛ ptRem.drop 16) := by
      conv => lhs; rw [← List.take_append_drop 16 ptRem]
      rw [pointsToBytes_append, hblk, show BitVec.ofNat 64 16 = 16#64 from rfl]
    have hout_split : memRegion outCur (16 * (k + 1 + 1)) =
        memRegion outCur 16 ∗ memRegion (outCur + 16#64) (16 * (k + 1)) := by
      rw [show 16 * (k + 1 + 1) = 16 + 16 * (k + 1) by omega, memRegion_split outCur 16 _ (by omega)]
    refine SepWP.weaken_pre (P' :=
        (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
          memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗
          (inCur ↦ₛ blkBs) ∗ memRegion outCur 16 ∗ stackAt sp allocHookStack) ∗
        (((inCur + 16#64) ↦ₛ ptRem.drop 16) ∗ memRegion (outCur + 16#64) (16 * (k + 1)) ∗ F))
      (by rw [hpt_split, hout_split]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine step_sw_loop_body hc hCallees x hblk prev hsp_15 hk hpc hrun hsp hprev
      hx22 hx24 hx25 hx27 hx28 hx29 fun s1 hpc1 hrun1 hsp1 hpst1 hp1 hv1 hprev1 hx22_1 hx25_1 hx27_1 hgpr1 => ?_
    have hne1 : (BitVec.ofNat 64 (k + 1 + 1) != 1#64) = true := by
      rw [bne_iff_ne]; intro heq; have ht := congrArg BitVec.toNat heq
      have hlt64 : k + 1 + 1 < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at ht; change k + 1 + 1 = 1 at ht; omega
    have hx27_sub : BitVec.ofNat 64 (k + 1 + 1) - 1#64 = BitVec.ofNat 64 (k + 1) := by
      apply BitVec.eq_of_toNat_eq
      have h1 : k + 1 + 1 < 2 ^ 64 := by omega
      have h2 : k + 1 < 2 ^ 64 := by omega
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]; omega
    have_instrs hc.segSwLoopPrev 16 1
    apply SepWP.step_pure hpc1 hrun1 hf_16 rfl (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
    conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hpst1, hne1, hpc1,
      BitVec.add_assoc, BitVec.reduceAdd]
    let c := Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock blkBs ^^^ prev)
    refine SepWP.weaken_pre (P' :=
        (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
          memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE c) ∗
          ((inCur + 16#64) ↦ₛ ptRem.drop 16) ∗ memRegion (outCur + 16#64) (16 * (k + 1)) ∗ stackAt sp allocHookStack) ∗
        ((inCur ↦ₛ blkBs) ∗ (outCur ↦ₛ blockToBytesLE c) ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine ih c (ptRem.drop 16) (by omega) (by rw [List.length_drop]; omega)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (by simp [wp_norm, arm64_norm, hsp1]) (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv1.trans hv)
      (SwPrevRegs.of_eq_gprs hprev1 (fun r _ => by simp [wp_norm, arm64_norm]))
      (by simp [wp_norm, arm64_norm, hx22_1])
      (by simp [wp_norm, arm64_norm, hgpr1 24#5 (by decide) (by decide) (by decide) (by decide) (by decide), hx24])
      (by simp [wp_norm, arm64_norm, hx25_1]) (by simp [wp_norm, arm64_norm, hx27_1, hx27_sub])
      (by simp [wp_norm, arm64_norm, hgpr1 28#5 (by decide) (by decide) (by decide) (by decide) (by decide), hx28])
      (by simp [wp_norm, arm64_norm, hgpr1 29#5 (by decide) (by decide) (by decide) (by decide) (by decide), hx29])
      fun sf hpcf hrunf hspf hpf hvf hgprf => ?_
    refine SepWP.weaken_pre ?_
      (hnext sf hpcf hrunf hspf (hp1.trans ((cbcPreserved_setPC _ _).trans hpf)) hvf
        (fun r hr19 hr29 hne22 hne25 hne27 => by
          rw [hgprf r hr19 hr29 hne22 hne25 hne27]; simp [wp_norm, arm64_norm, hgpr1 r hr19 hr29 hne22 hne25 hne27]))
    change _ ⊢ ((fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
      memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64)
        (blockToBytesLE (cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) c (ptBlocksOf (k + 1) (ptRem.drop 16)))) ∗
      (inCur ↦ₛ ptRem) ∗ (outCur ↦ₛ (blockToBytesLE c ++
        (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) c (ptBlocksOf (k + 1) (ptRem.drop 16))).flatMap blockToBytesLE)) ∗
      stackAt sp allocHookStack) ∗ F)
    rw [hpt_split, pointsToBytes_append outCur (blockToBytesLE c), length_blockToBytesLE,
        show BitVec.ofNat 64 16 = 16#64 from rfl]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Full Software Loop Entry (`+0x2d0..+0x4cc`) -/

theorem step_sw_loop {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc outBuf sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsp_15 : sp &&& 15#64 = 0#64) (hk : x.key.length = 32) (hin : x.input.length < 2 ^ 40)
    (hpc : s.pc = fnAddr + 0x2d0#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16))
    (hx21 : s.readReg64 (.gpr 21#5) = outBuf) (hx22 : s.readReg64 (.gpr 22#5) = x.inA)
    (hx23 : s.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)))
    (hx24 : s.readReg64 (.gpr 24#5) = sp + 0xc90#64) (hx26 : s.readReg64 (.gpr 26#5) = sp + 0xc90#64)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (x.input.length / 16))
    (hx29 : s.readReg64 (.gpr 29#5) = sp + 0x10c0#64)
    (hnext : ∀ sf : State,
      let prevFinal := cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) (bytesToBlock x.iv) (ptFullBlocks x.input)
      sf.pc = fnAddr + 0x4cc#64 → sf.status = .Running → sf.sp = sp →
      CbcPreserved s sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 (.gpr 19#5) = x.ret →
      sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) →
      sf.readReg64 (.gpr 21#5) = outBuf →
      sf.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)) →
      sf.readReg64 (.gpr 24#5) = sp + 0xc90#64 → sf.readReg64 (.gpr 26#5) = sp + 0xc90#64 →
      sf.readReg64 (.gpr 29#5) = sp + 0x10c0#64 →
      SepWP P target_pc sf
        ((fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
          memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE prevFinal) ∗
          (x.inA ↦ₛ x.input) ∗
          (outBuf ↦ₛ (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
            (bytesToBlock x.iv) (ptFullBlocks x.input)).flatMap blockToBytesLE) ∗
          stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s
      ((fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
        memRegion (sp + 0x106c#64) 64 ∗
        byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗
        (x.inA ↦ₛ x.input) ∗ memRegion outBuf (16 * (x.input.length / 16)) ∗
        stackAt sp allocHookStack) ∗ F) post oom := by
  have_instrs hc.segSwLoopCbz 0 1
  cases hq : x.input.length / 16 with
  | zero =>
    have hx27_0 : s.readReg64 (.gpr 27#5) = 0#64 := by rw [hx27, hq]
    have hnil : ptFullBlocks x.input = [] := by simp [ptFullBlocks, hq]
    apply SepWP.step_pure hpc hrun hf_0 rfl (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
    conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx27_0, hpc,
      BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.weaken_pre; swap
    · exact hnext _ (by simp only [State.setPC]) (by simp only [State.setPC, hrun])
        (by simp only [sp_setPC, hsp]) (cbcPreserved_setPC _ _)
        (by simpa only [calleeSavedVRegs, State.setPC] using hv)
        (by simpa only [State.readReg64_setPC] using hx19) (by simpa only [State.readReg64_setPC] using hx20)
        (by simpa only [State.readReg64_setPC] using hx21) (by simpa only [State.readReg64_setPC] using hx23)
        (by simpa only [State.readReg64_setPC] using hx24) (by simpa only [State.readReg64_setPC] using hx26)
        (by simpa only [State.readReg64_setPC] using hx29)
    rw [hnil]
    simp only [Nat.mul_zero, memRegion_zero, cbcChain, cbcEncBlocks, List.flatMap_nil, pointsToBytes_nil]
    exact Entails.refl _
  | succ k =>
    have hx27_ne : s.readReg64 (.gpr 27#5) ≠ 0 := by
      rw [hx27, hq]; intro h0; have ht := congrArg BitVec.toNat h0
      have hlt : k + 1 < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht; change k + 1 = 0 at ht; omega
    apply SepWP.step_pure hpc hrun hf_0 rfl (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
    conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx27_ne, hpc,
      BitVec.add_assoc, BitVec.reduceAdd]
    dsimp only [byte16At, byte16Cells16]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have_instrs hc.segSwLoopInit 0 19; wp_steps 19
    refine SepWP.weaken_pre (P' :=
        (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
          memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗
          (x.inA ↦ₛ x.input) ∗ memRegion outBuf (16 * (k + 1)) ∗ stackAt sp allocHookStack) ∗ F)
      (by dsimp only [byte16At, byte16Cells16]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.refl _) ?_
    refine step_sw_loop_k hc hCallees x hsp_15 hk k (bytesToBlock x.iv) x.input (by omega) (by omega)
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp]) (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv)
      (by simp [SwPrevRegs, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx24]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx27, hq]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hx29]) fun sf hpcf hrunf hspf hpf hvf hgprf => ?_
    refine SepWP.weaken_pre ?_ (hnext sf hpcf hrunf hspf
        ((CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl).trans hpf) hvf
        (by rw [hgprf 19#5 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [wp_norm, arm64_norm, hx19])
        (by rw [hgprf 20#5 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [wp_norm, arm64_norm, hx20, hq])
        (by rw [hgprf 21#5 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [wp_norm, arm64_norm, hx21])
        (by rw [hgprf 23#5 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [wp_norm, arm64_norm, hx23, hq])
        (by rw [hgprf 24#5 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [wp_norm, arm64_norm, hx24])
        (by rw [hgprf 26#5 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [wp_norm, arm64_norm, hx26])
        (by rw [hgprf 29#5 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [wp_norm, arm64_norm, hx29]))
    rw [ptBlocksOf_eq_ptFullBlocks x.input hq]; exact Entails.refl _

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.LoopSw

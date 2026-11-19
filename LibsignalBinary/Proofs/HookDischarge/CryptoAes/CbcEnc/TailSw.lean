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
import ProofLib.BV
import Arm64.Trusted.ISA.Eval
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Fixslice64 Software PKCS#7 Final Block (`+0x5f4..+0x7b0 -> +0x7b4`) (`CbcEnc.TailSw`)

Verifies the `STORAGE != 1` PKCS#7 padded final-block encryption, bridging `aes256_encrypt` to
`Spec.Aes256.aes256Enc` and storing the final ciphertext block at `[x23, #0x0..0xf]`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.TailSw

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
  (cbcChain ptFullBlocks pkcs7TailBytes pkcs7TailBytes_length length_blockToBytesLE)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
  (CbcPreserved spill16Words spill16At spill16Words_entails_memRegion_64
   byte16Cells16 byte16At pointsToBytes_16_eq_byte16At
   byte16Cells16_entails_memRegion_16 memRegion_16_eq_pts8
   inPad6Cells memRegion_48_eq_pts64 inPad6_entails_memRegion_48)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers
  (step_strSimd128_64_perm step_stpSimd128_64_perm zext32_zext64_eq trunc32_zext64_eq
   xor_zext_byte extractLsb_append64_lo extractLsb_append64_hi
   byte16Cells16_xor_comm_eq call_aes256_encrypt_single)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

section
arm64_proof_prelude
attribute [local irreducible] aes256KeyScheduleFs fsKeys256At Spec.Aes256.aes256Enc bytesToKey32
attribute [local simp, local arm64_norm] zext32_zext64_eq trunc32_zext64_eq xor_zext_byte

@[local simp, local arm64_norm] private theorem trunc8_xor_zext32 (a b : BitVec 8) :
    (a.zeroExtend 32 ^^^ b.zeroExtend 32).truncate 8 = a ^^^ b := by bv_bits
@[local simp, local arm64_norm] private theorem trunc8_zext32 (a : BitVec 8) :
    (a.zeroExtend 32).truncate 8 = a := by bv_bits
@[local simp, local arm64_norm] private theorem trunc8_zext64 (a : BitVec 8) :
    (a.zeroExtend 64).truncate 8 = a := by bv_bits
@[local simp, local arm64_norm] private theorem sp_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_advancePC (s : State) :
    s.advancePC.sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_setMem (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_setPState (s : State) (p : PState) :
    (s.setPState p).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_writeVReg128 (s : State) (n : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 n v).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_writeReg64_gpr (s : State) (n : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr n) v).sp = s.sp := by simp [State.writeReg64]
@[local simp, local arm64_norm] private theorem readReg64_sp_eq (s : State) : s.readReg64 .sp = s.sp := rfl

private theorem cbcPreserved_trans_rev {s0 s1 s2 : State}
    (h2 : CbcPreserved s1 s2) (h1 : CbcPreserved s0 s1) : CbcPreserved s0 s2 := h1.trans h2

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

theorem step_sw_tail {M : AllocCostModel} {A : RustCliAllocBudget M}
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
    (hsp_15 : sp &&& 15#64 = 0#64) (hk : x.key.length = 32)
    (hpc : s.pc = fnAddr + 0x5f4#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16))
    (hx21 : s.readReg64 (.gpr 21#5) = outBuf)
    (hx23 : s.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)))
    (hx24 : s.readReg64 (.gpr 24#5) = sp + 0xc90#64)
    (hx29 : s.readReg64 (.gpr 29#5) = sp + 0x10c0#64)
    (hnext : ∀ sf : State,
      let prevFinal := cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
        (bytesToBlock x.iv) (ptFullBlocks x.input)
      let cTail := Spec.Aes256.aes256Enc (bytesToKey32 x.key)
        (bytesToBlock (pkcs7TailBytes x.input) ^^^ prevFinal)
      sf.pc = fnAddr + 0x7b4#64 → sf.status = .Running → sf.sp = sp →
      CbcPreserved s sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 (.gpr 19#5) = x.ret →
      sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) →
      sf.readReg64 (.gpr 21#5) = outBuf →
      sf.readReg64 (.gpr 29#5) = sp + 0x10c0#64 →
      SepWP P target_pc sf
        ((fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗
          memRegion sp 64 ∗ memRegion (sp + 0x7d0#64) 64 ∗
          memRegion (sp + 0x106c#64) 64 ∗ memRegion (sp + 0x1050#64) 16 ∗
          ((outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) ↦ₛ blockToBytesLE cTail) ∗
          stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s
      ((fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗
        spill16At sp (pkcs7TailBytes x.input) ∗
        memRegion (sp + 0x7d0#64) 64 ∗
        memRegion (sp + 0x106c#64) 64 ∗
        byte16At (sp + 0x1050#64) (blockToBytesLE
          (cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) (bytesToBlock x.iv) (ptFullBlocks x.input))) ∗
        memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16 ∗
        stackAt sp allocHookStack) ∗ F) post oom := by
  have hsp_and : s.sp &&& 15#64 = 0#64 := hsp ▸ hsp_15
  let prevFinal := cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
    (bytesToBlock x.iv) (ptFullBlocks x.input)
  let tb := pkcs7TailBytes x.input
  rw [memRegion_split (sp + 0x106c#64) 16 48 (by decide),
      memRegion_16_eq_pts8 (sp + 0x106c#64), memRegion_48_eq_pts64 (sp + 0x106c#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 22 refine SepWP.exists_elim fun _ => ?_
  dsimp only [spill16At, spill16Words, byte16At, byte16Cells16]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have_instrs hc.segSwTailPreA 0 36
  wp_steps 8; wp_str8 hf_8 mx0 hmx0
  wp_steps 2; wp_str8 hf_11 mx1 hmx1
  wp_steps 4; wp_stpSimd128 hf_16 mzp0 hmzp0
  wp_steps 1; wp_str8 hf_18 mx2 hmx2
  wp_steps 1; wp_str8 hf_20 mx3 hmx3
  wp_steps 3; wp_strSimd128 hf_24 mzp1 hmzp1
  wp_steps 1; wp_str8 hf_26 mx4 hmx4
  wp_steps 1; wp_str8 hf_28 mx5 hmx5
  wp_steps 4; wp_str8 hf_33 mx6 hmx6
  wp_steps 1; wp_str8 hf_35 mx7 hmx7
  have_instrs hc.segSwTailPreB 0 27
  wp_steps 4; wp_str8 hf_4 mx8 hmx8
  wp_steps 1; wp_str8 hf_6 mx9 hmx9
  wp_steps 4; wp_str8 hf_11 mx10 hmx10
  wp_steps 1; wp_str8 hf_13 mx11 hmx11
  wp_steps 4; wp_str8 hf_18 mx12 hmx12
  wp_steps 1; wp_str8 hf_20 mx13 hmx13
  wp_steps 3; wp_str8 hf_24 mx14 hmx14
  wp_steps 1; wp_str8 hf_26 mx15 hmx15
  let b0 := bytesToBlock tb ^^^ prevFinal
  refine SepWP.weaken_pre (P' :=
      (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗
        byte16At (sp + 0x106c#64) (blockToBytesLE b0) ∗
        inPad6Cells (sp + 0x106c#64) 0#64 0#64 0#64 0#64 0#64 0#64 ∗
        memRegion (sp + 0x7d0#64) 64 ∗ stackAt sp allocHookStack) ∗
      (memRegion sp 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE prevFinal) ∗
        memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16 ∗ F)) ?_ ?_
  · refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_left
        (spill16Words_entails_memRegion_64 sp
          ((tb.getD 0 0#8).zeroExtend 32) ((tb.getD 1 0#8).zeroExtend 32)
          ((tb.getD 2 0#8).zeroExtend 32) ((tb.getD 3 0#8).zeroExtend 32)
          ((tb.getD 4 0#8).zeroExtend 32) ((tb.getD 5 0#8).zeroExtend 32)
          ((tb.getD 6 0#8).zeroExtend 32) ((tb.getD 7 0#8).zeroExtend 32)
          ((tb.getD 8 0#8).zeroExtend 32) ((tb.getD 9 0#8).zeroExtend 32)
          ((tb.getD 10 0#8).zeroExtend 32) ((tb.getD 11 0#8).zeroExtend 32)
          ((tb.getD 12 0#8).zeroExtend 32) ((tb.getD 13 0#8).zeroExtend 32)
          ((tb.getD 14 0#8).zeroExtend 32) ((tb.getD 15 0#8).zeroExtend 32))))
    dsimp only [b0, tb, prevFinal]
    rw [← byte16Cells16_xor_comm_eq (sp + 0x106c#64) (pkcs7TailBytes_length x.input) prevFinal]
    dsimp only [inPad6Cells, spill16Words, byte16At, byte16Cells16]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by sep_ac_rfl)
  refine call_aes256_encrypt_single hk b0 hc.bl_swTailEnc hCallees.encrypt_ok
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp]) hsp_15
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm]) fun s1 hpc1 hrun1 hsp1 hcs1 hp1 => ?_
  rw [BitVec.add_assoc] at hpc1; simp only [BitVec.reduceAdd] at hpc1
  have hx19_1 : s1.readReg64 (.gpr 19#5) = x.ret := by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm, hx19]
  have hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) := by
    rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm, hx20]
  have hx21_1 : s1.readReg64 (.gpr 21#5) = outBuf := by rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm, hx21]
  have hx23_1 : s1.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)) := by
    rw [hcs1.readReg64_x23]; simp [wp_norm, arm64_norm, hx23]
  have hx24_1 : s1.readReg64 (.gpr 24#5) = sp + 0xc90#64 := by rw [hcs1.readReg64_x24]; simp [wp_norm, arm64_norm, hx24]
  have hx29_1 : s1.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by rw [hcs1.readReg64_x29]; simp [wp_norm, arm64_norm, hx29]
  have hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
    rw [hcs1.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv
  have hp01 : CbcPreserved s s1 := cbcPreserved_trans_rev hp1
    (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hmx15, hmx14, hmx13, hmx12, hmx11, hmx10, hmx9, hmx8,
        hmx7, hmx6, hmx5, hmx4, hmzp1, hmx3, hmx2, hmzp0, hmx1, hmx0]))
  clear hcs1 hp1
  have hsp1_and : s1.sp &&& 15#64 = 0#64 := hsp1 ▸ hsp_15
  let cTail := Spec.Aes256.aes256Enc (bytesToKey32 x.key) b0
  let tailPtr := outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))
  have hmr_in : byte16At (sp + 0x106c#64) (blockToBytesLE b0) ∗
      inPad6Cells (sp + 0x106c#64) 0#64 0#64 0#64 0#64 0#64 0#64 ⊢ memRegion (sp + 0x106c#64) 64 := by
    rw [memRegion_split (sp + 0x106c#64) 16 48 (by decide)]
    exact sepConj_mono (byte16Cells16_entails_memRegion_16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (inPad6_entails_memRegion_48 _ _ _ _ _ _ _)
  refine SepWP.weaken_pre (P' :=
      byte16At (sp + 0x7d0#64) (blockToBytesLE cTail) ∗
      (byte16At (sp + 0x1050#64) (blockToBytesLE prevFinal) ∗
        memRegion tailPtr 16 ∗ fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗
        memRegion sp 64 ∗ memRegion (sp + 0x7e0#64) 48 ∗ memRegion (sp + 0x106c#64) 64 ∗
        stackAt sp allocHookStack ∗ F)) ?_ ?_
  · dsimp only [tailPtr]
    refine Entails.trans (Entails.of_eq (show _ =
        (byte16At (sp + 0x106c#64) (blockToBytesLE b0) ∗
          inPad6Cells (sp + 0x106c#64) 0#64 0#64 0#64 0#64 0#64 0#64) ∗
        (byte16At (sp + 0x7d0#64) (blockToBytesLE cTail) ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE prevFinal) ∗
          memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16 ∗
          (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗
            memRegion sp 64 ∗ memRegion (sp + 0x7e0#64) 48 ∗
            stackAt sp allocHookStack ∗ F)) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hmr_in) (Entails.of_eq (by sep_ac_rfl))
  generalize h_prev : byte16At (sp + 0x1050#64) (blockToBytesLE prevFinal) = prevCells
  dsimp only [byte16At, byte16Cells16]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have_instrs hc.segSwTailOut 0 16; wp_steps 16
  have hmr_out : byte16At (sp + 0x7d0#64) (blockToBytesLE cTail) ∗ memRegion (sp + 0x7e0#64) 48 ⊢
      memRegion (sp + 0x7d0#64) 64 := by
    rw [memRegion_split (sp + 0x7d0#64) 16 48 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (byte16Cells16_entails_memRegion_16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  rw [← h_prev]; dsimp only [byte16At, byte16Cells16] at hmr_out ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr_out ⊢
  refine SepWP.weaken_pre (P' :=
      memRegion (sp + 0x7d0#64) 64 ∗
      (byte16At (sp + 0x1050#64) (blockToBytesLE prevFinal) ∗
        memRegion tailPtr 16 ∗ fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗
        memRegion sp 64 ∗ memRegion (sp + 0x106c#64) 64 ∗ stackAt sp allocHookStack ∗ F)) ?_ ?_
  · refine Entails.trans ?_ (sepConj_mono_left hmr_out)
    dsimp only [byte16At, byte16Cells16]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by sep_ac_rfl)
  rw [memRegion_16_eq_pts8 tailPtr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 16 refine SepWP.exists_elim fun _ => ?_
  dsimp only [byte16At, byte16Cells16]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have_instrs hc.segSwTailPrev 0 16
  wp_str8 hf_0 mp0 hmp0; wp_str8 hf_1 mp1 hmp1; wp_str8 hf_2 mp2 hmp2; wp_str8 hf_3 mp3 hmp3
  wp_str8 hf_4 mp4 hmp4; wp_str8 hf_5 mp5 hmp5; wp_str8 hf_6 mp6 hmp6; wp_str8 hf_7 mp7 hmp7
  wp_str8 hf_8 mp8 hmp8; wp_str8 hf_9 mp9 hmp9; wp_str8 hf_10 mp10 hmp10; wp_str8 hf_11 mp11 hmp11
  wp_str8 hf_12 mp12 hmp12; wp_str8 hf_13 mp13 hmp13; wp_str8 hf_14 mp14 hmp14; wp_str8 hf_15 mp15 hmp15
  have hmp_perm : mp15.perm = s1.mem.perm := by
    simp [hmp15, hmp14, hmp13, hmp12, hmp11, hmp10, hmp9, hmp8,
      hmp7, hmp6, hmp5, hmp4, hmp3, hmp2, hmp1, hmp0, wp_norm, arm64_norm]
  have_instrs hc.segSwTailCt 0 16
  wp_str8 hf_0 mc0 hmc0; wp_str8 hf_1 mc1 hmc1; wp_str8 hf_2 mc2 hmc2; wp_str8 hf_3 mc3 hmc3
  wp_str8 hf_4 mc4 hmc4; wp_str8 hf_5 mc5 hmc5; wp_str8 hf_6 mc6 hmc6; wp_str8 hf_7 mc7 hmc7
  wp_str8 hf_8 mc8 hmc8; wp_str8 hf_9 mc9 hmc9; wp_str8 hf_10 mc10 hmc10; wp_str8 hf_11 mc11 hmc11
  wp_str8 hf_12 mc12 hmc12; wp_str8 hf_13 mc13 hmc13; wp_str8 hf_14 mc14 hmc14; wp_str8 hf_15 mc15 hmc15
  have hmc_perm : mc15.perm = s1.mem.perm := by
    simp [hmc15, hmc14, hmc13, hmc12, hmc11, hmc10, hmc9, hmc8,
      hmc7, hmc6, hmc5, hmc4, hmc3, hmc2, hmc1, hmc0, hmp_perm, wp_norm, arm64_norm]
  have hmr_prev : byte16At (sp + 0x1050#64) (blockToBytesLE cTail) ⊢ memRegion (sp + 0x1050#64) 16 :=
    byte16Cells16_entails_memRegion_16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  apply SepWP.weaken_pre; swap
  · exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1])
      (hp01.trans (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) hmc_perm))
      (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv1)
      (by simp [wp_norm, arm64_norm, hx19_1]) (by simp [wp_norm, arm64_norm, hx20_1])
      (by simp [wp_norm, arm64_norm, hx21_1]) (by simp [wp_norm, arm64_norm, hx29_1])
  refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmr_prev))))))
  rw [pointsToBytes_16_eq_byte16At (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) (length_blockToBytesLE cTail)]
  dsimp only [byte16At, byte16Cells16, tailPtr]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.TailSw

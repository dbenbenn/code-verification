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
# ARMv8 Hardware PKCS#7 Final Block (`+0x4dc..+0x5f0 -> +0x7b4`) (`CbcEnc.TailHw`)

Verifies the `STORAGE == 1` PKCS#7 padded final-block encryption, bridging `encrypt::<15>` to
`Spec.Aes256.aes256Enc` and storing the final ciphertext block at `[x23]`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.TailHw

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open CryptoGames.CBC (Block bytesToBlock blockToBytesLE)
open CryptoGames.HKDF (bytesToKey32)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (bytesToU128LE armv8ExpandKey roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockEnc
  (pointsTo128_eq_pointsToBytes pointsToBytes16_eq_pointsTo128 u128ToBytesLE_bytesToU128LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
  (Aes256EncHwAddrs CbcEncCode Aes256CbcEncryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
  (cbcChain ptFullBlocks pkcs7TailBytes pkcs7TailBytes_length length_blockToBytesLE)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
  (CbcPreserved spill16Words spill16At spill16Words_entails_memRegion_64
   byte16Cells16 byte16At byte16At_entails_memRegion_16 memRegion_16_eq_pts8)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers
  (zext32_zext64_eq trunc32_zext64_eq xor_zext_byte
   byte16Cells16_xor_comm_eq call_hw_encrypt_single)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand.Simp
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

section
arm64_proof_prelude
attribute [local irreducible] armv8ExpandKey roundKeys15At Spec.Aes256.aes256Enc bytesToKey32
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

theorem step_hw_tail {M : AllocCostModel} {A : RustCliAllocBudget M}
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
    (hpc : s.pc = fnAddr + 0x4dc#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16))
    (hx21 : s.readReg64 (.gpr 21#5) = outBuf)
    (hx23 : s.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)))
    (hx24 : s.readReg64 (.gpr 24#5) = sp + 0xc90#64)
    (hx26 : s.readReg64 (.gpr 26#5) = sp + 0xc90#64)
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
        ((roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗
          memRegion sp 64 ∗ memRegion (sp + 0x7d0#64) 16 ∗
          memRegion (sp + 0x1050#64) 16 ∗
          ((outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) ↦ₛ blockToBytesLE cTail)) ∗ F) post oom) :
    SepWP P target_pc s
      ((roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗
        spill16At sp (pkcs7TailBytes x.input) ∗
        memRegion (sp + 0x7d0#64) 16 ∗
        byte16At (sp + 0x1050#64) (blockToBytesLE
          (cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) (bytesToBlock x.iv) (ptFullBlocks x.input))) ∗
        memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16) ∗ F) post oom := by
  have hsp_and : s.sp &&& 15#64 = 0#64 := hsp ▸ hsp_15
  let prevFinal := cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
    (bytesToBlock x.iv) (ptFullBlocks x.input)
  let tb := pkcs7TailBytes x.input
  rw [memRegion_16_eq_pts8 (sp + 0x7d0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 16 refine SepWP.exists_elim fun _ => ?_
  dsimp only [spill16At, spill16Words, byte16At, byte16Cells16]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have_instrs hc.segHwTailPreA 0 35
  wp_steps 9; wp_str8 hf_9 mx0 hmx0
  wp_steps 1; wp_str8 hf_11 mx1 hmx1
  wp_steps 5; wp_str8 hf_17 mx2 hmx2; wp_str8 hf_18 mx3 hmx3
  wp_steps 3; wp_str8 hf_22 mx4 hmx4
  wp_steps 3; wp_str8 hf_26 mx5 hmx5
  wp_steps 3; wp_str8 hf_30 mx6 hmx6
  wp_steps 3; wp_str8 hf_34 mx7 hmx7
  have_instrs hc.segHwTailPreB 0 30
  wp_steps 3; wp_str8 hf_3 mx8 hmx8
  wp_steps 3; wp_str8 hf_7 mx9 hmx9
  wp_steps 3; wp_str8 hf_11 mx10 hmx10
  wp_steps 3; wp_str8 hf_15 mx11 hmx11
  wp_steps 3; wp_str8 hf_19 mx12 hmx12
  wp_steps 3; wp_str8 hf_23 mx13 hmx13
  wp_steps 2; wp_str8 hf_26 mx14 hmx14
  wp_steps 2; wp_str8 hf_29 mx15 hmx15
  refine SepWP.weaken_pre (P' :=
      (roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗
        byte16At (sp + 0x7d0#64) (blockToBytesLE (bytesToBlock tb ^^^ prevFinal))) ∗
      (memRegion sp 64 ∗ memRegion (sp + 0x1050#64) 16 ∗
        memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16 ∗ F)) ?_ ?_
  · refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono
        (spill16Words_entails_memRegion_64 sp
          ((tb.getD 0 0#8).zeroExtend 32) ((tb.getD 1 0#8).zeroExtend 32)
          ((tb.getD 2 0#8).zeroExtend 32) ((tb.getD 3 0#8).zeroExtend 32)
          ((tb.getD 4 0#8).zeroExtend 32) ((tb.getD 5 0#8).zeroExtend 32)
          ((tb.getD 6 0#8).zeroExtend 32) ((tb.getD 7 0#8).zeroExtend 32)
          ((tb.getD 8 0#8).zeroExtend 32) ((tb.getD 9 0#8).zeroExtend 32)
          ((tb.getD 10 0#8).zeroExtend 32) ((tb.getD 11 0#8).zeroExtend 32)
          ((tb.getD 12 0#8).zeroExtend 32) ((tb.getD 13 0#8).zeroExtend 32)
          ((tb.getD 14 0#8).zeroExtend 32) ((tb.getD 15 0#8).zeroExtend 32))
        (sepConj_mono_left (byte16At_entails_memRegion_16 _ (blockToBytesLE prevFinal)))))
    dsimp only [tb, prevFinal]; rw [← byte16Cells16_xor_comm_eq (sp + 0x7d0#64) (pkcs7TailBytes_length x.input) prevFinal]
    dsimp only [spill16Words, byte16At, byte16Cells16]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by sep_ac_rfl)
  refine call_hw_encrypt_single hk (bytesToBlock tb ^^^ prevFinal) hc.bl_hwTailEnc hCallees.hwEncrypt_ok
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp]) hsp_15
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) fun s1 hpc1 hrun1 hsp1 hcs1 hp1 => ?_
  rw [BitVec.add_assoc] at hpc1; simp only [BitVec.reduceAdd] at hpc1
  have hsp1_and : s1.sp &&& 15#64 = 0#64 := hsp1 ▸ hsp_15
  have hx19_1 : s1.readReg64 (.gpr 19#5) = x.ret := by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm, hx19]
  have hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) := by
    rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm, hx20]
  have hx21_1 : s1.readReg64 (.gpr 21#5) = outBuf := by rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm, hx21]
  have hx23_1 : s1.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)) := by
    rw [hcs1.readReg64_x23]; simp [wp_norm, arm64_norm, hx23]
  have hx26_1 : s1.readReg64 (.gpr 26#5) = sp + 0xc90#64 := by rw [hcs1.readReg64_x26]; simp [wp_norm, arm64_norm, hx26]
  have hx29_1 : s1.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by rw [hcs1.readReg64_x29]; simp [wp_norm, arm64_norm, hx29]
  have hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
    rw [hcs1.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv
  have hp01 : CbcPreserved s s1 := cbcPreserved_trans_rev hp1
    (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hmx15, hmx14, hmx13, hmx12, hmx11, hmx10, hmx9, hmx8,
        hmx7, hmx6, hmx5, hmx4, hmx3, hmx2, hmx1, hmx0]))
  clear hcs1 hp1
  let cTail := Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock tb ^^^ prevFinal)
  have_instrs hc.segHwTailPost 0 4
  wp_ldr128 hf_0
  wp_str128 hf_1 mp1 hmp1
  wp_str128 hf_2 mp2 hmp2
  wp_steps 1
  have hmr16 : ∀ a : BitVec 64, (a ↦₁₂₈ bytesToU128LE (blockToBytesLE cTail)) ⊢ memRegion a 16 := fun a => by
    rw [pointsTo128_eq_pointsToBytes, u128ToBytesLE_bytesToU128LE (length_blockToBytesLE cTail),
        ← length_blockToBytesLE cTail]
    exact pointsToBytes_entails_memRegion _ _
  have hout_eq : ((outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) ↦₁₂₈ bytesToU128LE (blockToBytesLE cTail)) =
      ((outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) ↦ₛ blockToBytesLE cTail) :=
    (pointsToBytes16_eq_pointsTo128 (length_blockToBytesLE cTail)).symm
  apply SepWP.weaken_pre; swap
  · exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1])
      (hp01.trans (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hmp2, hmp1])))
      (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv1)
      (by simp [wp_norm, arm64_norm, hx19_1]) (by simp [wp_norm, arm64_norm, hx20_1])
      (by simp [wp_norm, arm64_norm, hx21_1]) (by simp [wp_norm, arm64_norm, hx29_1])
  rw [hout_eq]
  refine Entails.trans (sepConj_mono (sepConj_mono_right (hmr16 _))
    (sepConj_mono_right (sepConj_mono_left (hmr16 _)))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.TailHw

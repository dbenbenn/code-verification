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
# ARMv8 Hardware Full-Block CBC Loop (`+0x198..+0x2cc -> +0x4cc`) (`CbcEnc.LoopHw`)

Verifies the `STORAGE == 1` full-block CBC encryption loop (`0` or `k + 1` blocks), bridging each
in-place `aes::armv8::encdec::encrypt::<15>` call to `Spec.Aes256.aes256Enc` and storing the running
chain block at `[x26, #0x3c0]` (`sp + 0x1050#64`) and ciphertext at `outBuf`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.LoopHw

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
  (cbcEncBlocks cbcChain ptFullBlocks length_blockToBytesLE)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
  (CbcPreserved byte16Cells16 byte16At byte16At_eq_pointsTo128
   byte16Cells16_entails_memRegion_16 byte16At_entails_memRegion_16)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers
  (zext32_zext64_eq trunc32_zext64_eq xor_zext_byte byte16Cells16_xor_eq call_hw_encrypt_single)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand.Simp
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

/-! ## 1. Recursive Plaintext Block List (`ptBlocksOf`) Shared Across HW & SW Loops -/

theorem drop_drop_eq {α : Type} (a b : Nat) (xs : List α) :
    (xs.drop a).drop b = xs.drop (a + b) := by
  induction a generalizing xs with
  | zero => simp
  | succ a ih =>
    cases xs with
    | nil => simp
    | cons _ xs => simp only [List.drop_succ_cons, Nat.succ_add, ih]

@[expose] def ptBlocksOf : Nat → List (BitVec 8) → List Block
  | 0, _ => []
  | k + 1, bs => bytesToBlock (bs.take 16) :: ptBlocksOf k (bs.drop 16)

theorem ptBlocksOf_length (k : Nat) (bs : List (BitVec 8)) :
    (ptBlocksOf k bs).length = k := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih => simp [ptBlocksOf, ih]

theorem ptBlocksOf_getElem (k : Nat) (bs : List (BitVec 8)) (i : Nat)
    (hi : i < (ptBlocksOf k bs).length) :
    (ptBlocksOf k bs)[i] = bytesToBlock ((bs.drop (16 * i)).take 16) := by
  induction k generalizing bs i with
  | zero => simp [ptBlocksOf] at hi
  | succ k ih =>
    cases i with
    | zero => simp [ptBlocksOf]
    | succ i =>
      have hi' : i < (ptBlocksOf k (bs.drop 16)).length := by rw [ptBlocksOf_length] at hi ⊢; omega
      simp only [ptBlocksOf, List.getElem_cons_succ, ih (bs.drop 16) i hi', drop_drop_eq]
      rw [show 16 + 16 * i = 16 * (i + 1) by omega]

theorem ptBlocksOf_eq_ptFullBlocks (pt : List (BitVec 8)) {q : Nat} (hq : pt.length / 16 = q) :
    ptBlocksOf q pt = ptFullBlocks pt := by
  apply List.ext_getElem
  · simp [ptBlocksOf_length, ptFullBlocks, hq]
  · intro i hi1 _; rw [ptBlocksOf_getElem q pt i hi1]; simp [ptFullBlocks]

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

private theorem cbcPreserved_trans_rev {s0 s1 s2 : State}
    (h2 : CbcPreserved s1 s2) (h1 : CbcPreserved s0 s1) : CbcPreserved s0 s2 := h1.trans h2

private theorem cbcPreserved_setPC (s : State) (pc : BitVec 64) : CbcPreserved s (s.setPC pc) :=
  CbcPreserved.of_proj_perm (by cases s; rfl) (by cases s; rfl)

private theorem cbcPreserved_setPC_right {s0 s : State} {pc : BitVec 64} (h : CbcPreserved s0 s) :
    CbcPreserved s0 (s.setPC pc) := h.trans (cbcPreserved_setPC s pc)

private theorem readReg64_of_calleeSaved {s1 s2 : State} (hcs : CalleeSavedPreserved s1 s2)
    (r : BitVec 5) (h19 : 19 ≤ r.toNat) (h29 : r.toNat ≤ 29) :
    s2.readReg64 (.gpr r) = s1.readReg64 (.gpr r) := by
  have hr : r = 19#5 ∨ r = 20#5 ∨ r = 21#5 ∨ r = 22#5 ∨ r = 23#5 ∨ r = 24#5 ∨
      r = 25#5 ∨ r = 26#5 ∨ r = 27#5 ∨ r = 28#5 ∨ r = 29#5 := by
    rcases r with ⟨⟨v, hv⟩⟩; simp [BitVec.toNat] at h19 h29
    have : v = 19 ∨ v = 20 ∨ v = 21 ∨ v = 22 ∨ v = 23 ∨ v = 24 ∨
           v = 25 ∨ v = 26 ∨ v = 27 ∨ v = 28 ∨ v = 29 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hcs.readReg64_x19
  · exact hcs.readReg64_x20
  · exact hcs.readReg64_x21
  · exact hcs.readReg64_x22
  · exact hcs.readReg64_x23
  · exact hcs.readReg64_x24
  · exact hcs.readReg64_x25
  · exact hcs.readReg64_x26
  · exact hcs.readReg64_x27
  · exact hcs.readReg64_x28
  · exact hcs.readReg64_x29

/-! ## 2. Single Hardware CBC Iteration Body (`+0x1a0..+0x2c8`) -/

private theorem step_hw_loop_body {M : AllocCostModel} {A : RustCliAllocBudget M}
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
    (hpc : s.pc = fnAddr + 0x1a0#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx22 : s.readReg64 (.gpr 22#5) = inCur)
    (hx24 : s.readReg64 (.gpr 24#5) = sp + 0xc90#64)
    (hx25 : s.readReg64 (.gpr 25#5) = outCur)
    (hx26 : s.readReg64 (.gpr 26#5) = sp + 0xc90#64)
    (hx27 : s.readReg64 (.gpr 27#5) = cnt)
    (hnext : ∀ sf : State,
      let c := Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock blkBs ^^^ prev)
      sf.pc = fnAddr + 0x2c8#64 → sf.status = .Running → sf.sp = sp →
      sf.pstate = subsPState64 cnt 1#64 →
      CbcPreserved s sf → calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 (.gpr 22#5) = inCur + 16#64 →
      sf.readReg64 (.gpr 25#5) = outCur + 16#64 →
      sf.readReg64 (.gpr 27#5) = cnt - 1#64 →
      (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 →
        r ≠ 22#5 → r ≠ 25#5 → r ≠ 27#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      SepWP P target_pc sf
        ((roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗
          memRegion (sp + 0x7d0#64) 16 ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE c) ∗
          (inCur ↦ₛ blkBs) ∗ (outCur ↦ₛ blockToBytesLE c)) ∗ F) post oom) :
    SepWP P target_pc s
      ((roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗
        memRegion (sp + 0x7d0#64) 16 ∗
        byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗
        (inCur ↦ₛ blkBs) ∗ memRegion outCur 16) ∗ F) post oom := by
  have hsp_and : s.sp &&& 15#64 = 0#64 := hsp ▸ hsp_15
  rw [pointsToBytes16_eq_pointsTo128 hblk]
  dsimp only [byte16At, byte16Cells16]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have_instrs hc.segHwLoopPreA 0 36
  wp_ldr128 hf_0
  wp_steps 4
  wp_str128 hf_5 m0 hm0
  rw [← byte16At_eq_pointsTo128 (sp + 0x7d0#64) hblk, ← pointsToBytes16_eq_pointsTo128 hblk]
  dsimp only [byte16At, byte16Cells16]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 11; wp_str8 hf_17 mx0 hmx0
  wp_steps 2; wp_str8 hf_20 mx1 hmx1
  wp_steps 2; wp_str8 hf_23 mx2 hmx2
  wp_steps 4; wp_str8 hf_28 mx3 hmx3; wp_str8 hf_29 mx4 hmx4
  wp_steps 5; wp_str8 hf_35 mx5 hmx5
  have_instrs hc.segHwLoopPreB 0 33
  wp_steps 4; wp_str8 hf_4 mx6 hmx6
  wp_steps 3; wp_str8 hf_8 mx7 hmx7
  wp_steps 3; wp_str8 hf_12 mx8 hmx8
  wp_steps 3; wp_str8 hf_16 mx9 hmx9
  wp_steps 3; wp_str8 hf_20 mx10 hmx10; wp_str8 hf_21 mx11 hmx11
  wp_steps 2; wp_str8 hf_24 mx12 hmx12
  wp_steps 5; wp_str8 hf_30 mx13 hmx13; wp_str8 hf_31 mx14 hmx14; wp_str8 hf_32 mx15 hmx15
  refine SepWP.weaken_pre (P' :=
      (roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗
        byte16At (sp + 0x7d0#64) (blockToBytesLE (bytesToBlock blkBs ^^^ prev))) ∗
      (memRegion (sp + 0x1050#64) 16 ∗ (inCur ↦ₛ blkBs) ∗ memRegion outCur 16 ∗ F)) ?_ ?_
  · refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_left (byte16At_entails_memRegion_16 _ (blockToBytesLE prev))))
    rw [← byte16Cells16_xor_eq (sp + 0x7d0#64) hblk prev]
    dsimp only [byte16At, byte16Cells16]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by sep_ac_rfl)
  refine call_hw_encrypt_single hk (bytesToBlock blkBs ^^^ prev) hc.bl_hwLoopEnc hCallees.hwEncrypt_ok
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp]) hsp_15
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) ?_
  intro s1 hpc1 hrun1 hsp1 hcs1 hp1
  rw [BitVec.add_assoc] at hpc1; simp only [BitVec.reduceAdd] at hpc1
  have hsp1_and : s1.sp &&& 15#64 = 0#64 := hsp1 ▸ hsp_15
  have hx22_1 : s1.readReg64 (.gpr 22#5) = inCur + 16#64 := by
    rw [hcs1.readReg64_x22]; simp [wp_norm, arm64_norm]
  have hx25_1 : s1.readReg64 (.gpr 25#5) = outCur := by
    rw [hcs1.readReg64_x25]; simp [wp_norm, arm64_norm, hx25]
  have hx26_1 : s1.readReg64 (.gpr 26#5) = sp + 0xc90#64 := by
    rw [hcs1.readReg64_x26]; simp [wp_norm, arm64_norm, hx26]
  have hx27_1 : s1.readReg64 (.gpr 27#5) = cnt := by
    rw [hcs1.readReg64_x27]; simp [wp_norm, arm64_norm, hx27]
  have hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s := by
    rw [hcs1.vregs]; simp [calleeSavedVRegs, wp_norm, arm64_norm]
  have hgpr1 : ∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 → r ≠ 22#5 →
      s1.readReg64 (.gpr r) = s.readReg64 (.gpr r) := by
    intro r hr19 hr29 hne22
    rw [readReg64_of_calleeSaved hcs1 r hr19 hr29]
    simp [wp_norm, arm64_norm, hne22,
      show r ≠ 0#5 by bv_omega, show r ≠ 1#5 by bv_omega, show r ≠ 2#5 by bv_omega,
      show r ≠ 8#5 by bv_omega, show r ≠ 9#5 by bv_omega, show r ≠ 10#5 by bv_omega,
      show r ≠ 11#5 by bv_omega, show r ≠ 12#5 by bv_omega, show r ≠ 13#5 by bv_omega,
      show r ≠ 14#5 by bv_omega, show r ≠ 15#5 by bv_omega, show r ≠ 16#5 by bv_omega]
  have hp01 : CbcPreserved s s1 := cbcPreserved_trans_rev hp1
    (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hmx15, hmx14, hmx13, hmx12, hmx11, hmx10, hmx9, hmx8,
        hmx7, hmx6, hmx5, hmx4, hmx3, hmx2, hmx1, hmx0, hm0]))
  clear hcs1 hp1
  let c := Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock blkBs ^^^ prev)
  have_instrs hc.segHwLoopPost 0 4
  wp_ldr128 hf_0
  wp_steps 1
  wp_str128 hf_2 mp1 hmp1
  wp_str128 hf_3 mp2 hmp2
  have h7d0_mr : ((sp + 0x7d0#64) ↦₁₂₈ bytesToU128LE (blockToBytesLE c)) ⊢ memRegion (sp + 0x7d0#64) 16 := by
    rw [pointsTo128_eq_pointsToBytes, u128ToBytesLE_bytesToU128LE (length_blockToBytesLE c),
        ← length_blockToBytesLE c]
    exact pointsToBytes_entails_memRegion _ _
  have hout_eq : (outCur ↦₁₂₈ bytesToU128LE (blockToBytesLE c)) = (outCur ↦ₛ blockToBytesLE c) :=
    (pointsToBytes16_eq_pointsTo128 (length_blockToBytesLE c)).symm
  refine SepWP.weaken_pre ?_
    (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1])
      (by simp [wp_norm, arm64_norm])
      (hp01.trans (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hmp2, hmp1])))
      (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv1)
      (by simp [wp_norm, arm64_norm, hx22_1])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (fun r hr19 hr29 hne22 hne25 hne27 => by
        simp [wp_norm, arm64_norm, hne25, hne27, hgpr1 r hr19 hr29 hne22]))
  rw [← byte16At_eq_pointsTo128 (sp + 0x1050#64) (length_blockToBytesLE c), hout_eq]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right h7d0_mr)) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Multi-Block Induction & Full Hardware Loop (`+0x198..+0x4cc`) -/

private theorem step_hw_loop_k {M : AllocCostModel} {A : RustCliAllocBudget M}
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
      s.pc = fnAddr + 0x1a0#64 → s.status = .Running → s.sp = sp →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 (.gpr 22#5) = inCur →
      s.readReg64 (.gpr 24#5) = sp + 0xc90#64 →
      s.readReg64 (.gpr 25#5) = outCur →
      s.readReg64 (.gpr 26#5) = sp + 0xc90#64 →
      s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (k + 1) →
      (∀ sf : State,
        let prevFinal := cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) prev (ptBlocksOf (k + 1) ptRem)
        sf.pc = fnAddr + 0x4cc#64 → sf.status = .Running → sf.sp = sp →
        CbcPreserved s sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
        (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 29 →
          r ≠ 22#5 → r ≠ 25#5 → r ≠ 27#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
        SepWP P target_pc sf
          ((roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗
            memRegion (sp + 0x7d0#64) 16 ∗
            byte16At (sp + 0x1050#64) (blockToBytesLE prevFinal) ∗
            (inCur ↦ₛ ptRem) ∗
            (outCur ↦ₛ (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) prev
              (ptBlocksOf (k + 1) ptRem)).flatMap blockToBytesLE)) ∗ F) post oom) →
      SepWP P target_pc s
        ((roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗
          memRegion (sp + 0x7d0#64) 16 ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗
          (inCur ↦ₛ ptRem) ∗ memRegion outCur (16 * (k + 1))) ∗ F) post oom := by
  intro k; induction k with
  | zero =>
    intro inCur outCur prev ptRem s F post oom _ hpt_len hpc hrun hsp hv hx22 hx24 hx25 hx26 hx27 hnext
    let blkBs := ptRem.take 16
    have hblk : blkBs.length = 16 := by dsimp [blkBs]; rw [List.length_take]; omega
    have hpt_split : (inCur ↦ₛ ptRem) = (inCur ↦ₛ blkBs) ∗ ((inCur + 16#64) ↦ₛ ptRem.drop 16) := by
      conv => lhs; rw [← List.take_append_drop 16 ptRem]
      rw [pointsToBytes_append, hblk, show BitVec.ofNat 64 16 = 16#64 from rfl]
    refine SepWP.weaken_pre (P' :=
        (roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗ memRegion (sp + 0x7d0#64) 16 ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗ (inCur ↦ₛ blkBs) ∗ memRegion outCur 16) ∗
        (((inCur + 16#64) ↦ₛ ptRem.drop 16) ∗ F))
      (by rw [hpt_split, Nat.mul_one]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine step_hw_loop_body hc hCallees x hblk prev hsp_15 hk hpc hrun hsp
      hx22 hx24 hx25 hx26 hx27 fun s1 hpc1 hrun1 hsp1 hpst1 hp1 hv1 _ _ _ hgpr1 => ?_
    have_instrs hc.segHwLoopPost 4 2
    apply SepWP.step_pure hpc1 hrun1 hf_4 rfl
      (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
    conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hpst1, hpc1,
      BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps 1
    apply SepWP.weaken_pre; swap
    · exact hnext _ (by simp only [State.setPC]; try bv_omega)
        (by simp only [State.setPC, hrun1]) (by simp only [sp_setPC, hsp1])
        (by repeat apply cbcPreserved_setPC_right; exact hp1)
        (by simpa only [calleeSavedVRegs, State.setPC] using hv1.trans hv)
        (fun r hr19 hr29 hne22 hne25 hne27 => by
          simpa only [State.readReg64_setPC] using hgpr1 r hr19 hr29 hne22 hne25 hne27)
    dsimp only [ptBlocksOf, cbcChain, cbcEncBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hpt_split]; exact Entails.of_eq (by sep_ac_rfl)
  | succ k ih =>
    intro inCur outCur prev ptRem s F post oom hk_lt hpt_len hpc hrun hsp hv hx22 hx24 hx25 hx26 hx27 hnext
    let blkBs := ptRem.take 16
    have hblk : blkBs.length = 16 := by dsimp [blkBs]; rw [List.length_take]; omega
    have hpt_split : (inCur ↦ₛ ptRem) = (inCur ↦ₛ blkBs) ∗ ((inCur + 16#64) ↦ₛ ptRem.drop 16) := by
      conv => lhs; rw [← List.take_append_drop 16 ptRem]
      rw [pointsToBytes_append, hblk, show BitVec.ofNat 64 16 = 16#64 from rfl]
    have hout_split : memRegion outCur (16 * (k + 1 + 1)) =
        memRegion outCur 16 ∗ memRegion (outCur + 16#64) (16 * (k + 1)) := by
      rw [show 16 * (k + 1 + 1) = 16 + 16 * (k + 1) by omega, memRegion_split outCur 16 _ (by omega)]
    refine SepWP.weaken_pre (P' :=
        (roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗ memRegion (sp + 0x7d0#64) 16 ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE prev) ∗ (inCur ↦ₛ blkBs) ∗ memRegion outCur 16) ∗
        (((inCur + 16#64) ↦ₛ ptRem.drop 16) ∗ memRegion (outCur + 16#64) (16 * (k + 1)) ∗ F))
      (by rw [hpt_split, hout_split]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine step_hw_loop_body hc hCallees x hblk prev hsp_15 hk hpc hrun hsp
      hx22 hx24 hx25 hx26 hx27 fun s1 hpc1 hrun1 hsp1 hpst1 hp1 hv1 hx22_1 hx25_1 hx27_1 hgpr1 => ?_
    have hne1 : (BitVec.ofNat 64 (k + 1 + 1) != 1#64) = true := by
      rw [bne_iff_ne]; intro heq; have ht := congrArg BitVec.toNat heq
      have hlt64 : k + 1 + 1 < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at ht; change k + 1 + 1 = 1 at ht; omega
    have hx27_sub : BitVec.ofNat 64 (k + 1 + 1) - 1#64 = BitVec.ofNat 64 (k + 1) := by
      apply BitVec.eq_of_toNat_eq
      have h1 : k + 1 + 1 < 2 ^ 64 := by omega
      have h2 : k + 1 < 2 ^ 64 := by omega
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]; omega
    have_instrs hc.segHwLoopPost 4 1
    apply SepWP.step_pure hpc1 hrun1 hf_4 rfl
      (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
    conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hpst1, hne1, hpc1,
      BitVec.add_assoc, BitVec.reduceAdd]
    let c := Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock blkBs ^^^ prev)
    refine SepWP.weaken_pre (P' :=
        (roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗ memRegion (sp + 0x7d0#64) 16 ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE c) ∗
          ((inCur + 16#64) ↦ₛ ptRem.drop 16) ∗ memRegion (outCur + 16#64) (16 * (k + 1))) ∗
        ((inCur ↦ₛ blkBs) ∗ (outCur ↦ₛ blockToBytesLE c) ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine ih c (ptRem.drop 16) (by omega) (by rw [List.length_drop]; omega)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1])
      (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv1.trans hv)
      (by simp [wp_norm, arm64_norm, hx22_1])
      (by simp [wp_norm, arm64_norm, hgpr1 24#5 (by decide) (by decide) (by decide) (by decide) (by decide), hx24])
      (by simp [wp_norm, arm64_norm, hx25_1])
      (by simp [wp_norm, arm64_norm, hgpr1 26#5 (by decide) (by decide) (by decide) (by decide) (by decide), hx26])
      (by simp [wp_norm, arm64_norm, hx27_1, hx27_sub])
      fun sf hpcf hrunf hspf hpf hvf hgprf => ?_
    refine SepWP.weaken_pre ?_
      (hnext sf hpcf hrunf hspf
        (hp1.trans ((CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl).trans hpf)) hvf
        (fun r hr19 hr29 hne22 hne25 hne27 => by
          rw [hgprf r hr19 hr29 hne22 hne25 hne27]
          simp [wp_norm, arm64_norm, hgpr1 r hr19 hr29 hne22 hne25 hne27]))
    change _ ⊢ ((roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗ memRegion (sp + 0x7d0#64) 16 ∗
      byte16At (sp + 0x1050#64) (blockToBytesLE
        (cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) c (ptBlocksOf (k + 1) (ptRem.drop 16)))) ∗
      (inCur ↦ₛ ptRem) ∗
      (outCur ↦ₛ (blockToBytesLE c ++
        (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) c
          (ptBlocksOf (k + 1) (ptRem.drop 16))).flatMap blockToBytesLE))) ∗ F)
    rw [hpt_split, pointsToBytes_append outCur (blockToBytesLE c), length_blockToBytesLE,
        show BitVec.ofNat 64 16 = 16#64 from rfl]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_hw_loop {M : AllocCostModel} {A : RustCliAllocBudget M}
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
    (hpc : s.pc = fnAddr + 0x198#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16))
    (hx21 : s.readReg64 (.gpr 21#5) = outBuf)
    (hx22 : s.readReg64 (.gpr 22#5) = x.inA)
    (hx23 : s.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)))
    (hx24 : s.readReg64 (.gpr 24#5) = sp + 0xc90#64)
    (hx26 : s.readReg64 (.gpr 26#5) = sp + 0xc90#64)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (x.input.length / 16))
    (hx29 : s.readReg64 (.gpr 29#5) = sp + 0x10c0#64)
    (hnext : ∀ sf : State,
      let prevFinal := cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
        (bytesToBlock x.iv) (ptFullBlocks x.input)
      sf.pc = fnAddr + 0x4cc#64 → sf.status = .Running → sf.sp = sp →
      CbcPreserved s sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 (.gpr 19#5) = x.ret →
      sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) →
      sf.readReg64 (.gpr 21#5) = outBuf →
      sf.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)) →
      sf.readReg64 (.gpr 24#5) = sp + 0xc90#64 →
      sf.readReg64 (.gpr 26#5) = sp + 0xc90#64 →
      sf.readReg64 (.gpr 29#5) = sp + 0x10c0#64 →
      SepWP P target_pc sf
        ((roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗
          memRegion (sp + 0x7d0#64) 16 ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE prevFinal) ∗
          (x.inA ↦ₛ x.input) ∗
          (outBuf ↦ₛ (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
            (bytesToBlock x.iv) (ptFullBlocks x.input)).flatMap blockToBytesLE)) ∗ F) post oom) :
    SepWP P target_pc s
      ((roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗
        memRegion (sp + 0x7d0#64) 16 ∗
        byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗
        (x.inA ↦ₛ x.input) ∗ memRegion outBuf (16 * (x.input.length / 16))) ∗ F) post oom := by
  have_instrs hc.segHwLoopHdr 0 2
  cases hq : x.input.length / 16 with
  | zero =>
    have hx27_0 : s.readReg64 (.gpr 27#5) = 0#64 := by rw [hx27, hq]
    have hnil : ptFullBlocks x.input = [] := by simp [ptFullBlocks, hq]
    apply SepWP.step_pure hpc hrun hf_0 rfl
      (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
    conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx27_0, hpc,
      BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.weaken_pre; swap
    · exact hnext _ (by simp only [State.setPC])
        (by simp only [State.setPC, hrun]) (by simp only [sp_setPC, hsp])
        (cbcPreserved_setPC _ _)
        (by simpa only [calleeSavedVRegs, State.setPC] using hv)
        (by simpa only [State.readReg64_setPC] using hx19)
        (by simpa only [State.readReg64_setPC] using hx20)
        (by simpa only [State.readReg64_setPC] using hx21)
        (by simpa only [State.readReg64_setPC] using hx23)
        (by simpa only [State.readReg64_setPC] using hx24)
        (by simpa only [State.readReg64_setPC] using hx26)
        (by simpa only [State.readReg64_setPC] using hx29)
    rw [hnil]
    simp only [Nat.mul_zero, memRegion_zero, cbcChain, cbcEncBlocks, List.flatMap_nil, pointsToBytes_nil]
    exact Entails.refl _
  | succ k =>
    have hx27_ne : s.readReg64 (.gpr 27#5) ≠ 0 := by
      rw [hx27, hq]; intro h0; have ht := congrArg BitVec.toNat h0
      have hlt : k + 1 < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht; change k + 1 = 0 at ht; omega
    apply SepWP.step_pure hpc hrun hf_0 rfl
      (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
    conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx27_ne, hpc,
      BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps 1
    refine step_hw_loop_k hc hCallees x hsp_15 hk k (bytesToBlock x.iv) x.input
      (by omega) (by omega)
      (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hsp])
      (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv)
      (by simp [wp_norm, arm64_norm, hx22]) (by simp [wp_norm, arm64_norm, hx24])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx26])
      (by simp [wp_norm, arm64_norm, hx27, hq])
      fun sf hpcf hrunf hspf hpf hvf hgprf => ?_
    refine SepWP.weaken_pre ?_
      (hnext sf hpcf hrunf hspf
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

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.LoopHw

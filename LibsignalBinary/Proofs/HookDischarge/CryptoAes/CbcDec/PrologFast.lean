/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Model
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WPp
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.Libc.Common

/-!
# Prologue, Fast-Reject & Key-Schedule Call/Copy Helpers (`CbcDec.PrologFast`)
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologFast

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.StdStartup (decodeWords hasInstrs)
open CryptoGames.CBC (bytesToBlock)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcDecrypt)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.AesDecErrRoBudget (errResultErrRo_pack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (aes256KeyScheduleFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved fsKeys256At fsKeys256Bytes fsKeys256At_eq_pointsToBytes)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule (aes256KeyScheduleSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (aesRconBytes armv8ExpandKey armv8InvExpandedKeys roundKeys15Bytes roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeySchedule (expandKey15RegionSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (invExpandedKeys15RegionSpec roundKeys15Bytes_length roundKeys15At_eq_pointsToBytes
   memRegion240_eq_exists_roundKeys15At)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
  (cbcPrologueWords cbcHwCopyEkWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code (Aes256DecHwAddrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs (CbcDecCodeSegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
  (aesDecEvents aesCbcDecrypt_of_badLen)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules (sepWP_weaken_pre)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
  (pureStepPreserved_bl sepWP_done_let step_bl_call step_adrpAddPair
   cbcPost cbcPanic cbcOom savedCells96 savedStack96 slots56 cbc_common_ret)

/-! ## 1. `3816`-Byte Local Workspace Split & Key-Bytes Invariant -/

theorem localWork3816_split (sp : BitVec 64) :
    memRegion (sp + 0x038#64) 3816 =
      memRegion (sp + 0x038#64) 168 ∗
      memRegion (sp + 0x0e0#64) 8 ∗
      memRegion (sp + 0x0e8#64) 968 ∗
      memRegion (sp + 0x4b0#64) 960 ∗
      memRegion (sp + 0x870#64) 240 ∗
      memRegion (sp + 0x960#64) 240 ∗
      memRegion (sp + 0xa50#64) 240 ∗
      memRegion (sp + 0xb40#64) 960 ∗
      memRegion (sp + 0xf00#64) 16 ∗
      memRegion (sp + 0xf10#64) 16 := by
  rw [show (3816 : Nat) = 168 + 3648 from rfl, memRegion_split (sp + 0x038#64) 168 3648 (by decide),
      show (3648 : Nat) = 8 + 3640 from rfl, memRegion_split _ 8 3640 (by decide),
      show (3640 : Nat) = 968 + 2672 from rfl, memRegion_split _ 968 2672 (by decide),
      show (2672 : Nat) = 960 + 1712 from rfl, memRegion_split _ 960 1712 (by decide),
      show (1712 : Nat) = 240 + 1472 from rfl, memRegion_split _ 240 1472 (by decide),
      show (1472 : Nat) = 240 + 1232 from rfl, memRegion_split _ 240 1232 (by decide),
      show (1232 : Nat) = 240 + 992 from rfl, memRegion_split _ 240 992 (by decide),
      show (992 : Nat) = 960 + 32 from rfl, memRegion_split _ 960 32 (by decide),
      show (32 : Nat) = 16 + 16 from rfl, memRegion_split _ 16 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

@[expose] def KeyBytes960Inv (b : BitVec 8) (key keyBytes960 : List (BitVec 8)) : Prop :=
  keyBytes960.length = 960 ∧
  (if b = 1#8 then
    ∃ head240 tail480 : List (BitVec 8),
      head240.length = 240 ∧ tail480.length = 480 ∧
      keyBytes960 =
        head240 ++ roundKeys15Bytes (armv8InvExpandedKeys (armv8ExpandKey key)) ++ tail480
   else
    keyBytes960 = fsKeys256Bytes (aes256KeyScheduleFs key))

theorem keyBytes960_unpack_hw {sp : BitVec 64} {key keyBytes960 : List (BitVec 8)}
    (h : KeyBytes960Inv 1#8 key keyBytes960) :
    ((sp + 0xb40#64) ↦ₛ keyBytes960) ⊢
      memRegion (sp + 0xb40#64) 240 ∗
      roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
      memRegion (sp + 0xd20#64) 480 := by
  rcases h with ⟨_, hbr⟩
  simp only [↓reduceIte] at hbr
  rcases hbr with ⟨head240, tail480, hh, ht, rfl⟩
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append, hh,
      roundKeys15Bytes_length, ← roundKeys15At_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hm1 : ((sp + 0xb40#64) ↦ₛ head240) ⊢ memRegion (sp + 0xb40#64) 240 := by
    simpa only [hh] using pointsToBytes_entails_memRegion (sp + 0xb40#64) head240
  have hm2 : ((sp + 0xd20#64) ↦ₛ tail480) ⊢ memRegion (sp + 0xd20#64) 480 := by
    simpa only [ht] using pointsToBytes_entails_memRegion (sp + 0xd20#64) tail480
  exact Entails.trans (sepConj_mono hm1 (sepConj_mono_right hm2)) (Entails.of_eq (by sep_ac_rfl))

theorem keyBytes960_unpack_sw {sp : BitVec 64} {b : BitVec 8} {key keyBytes960 : List (BitVec 8)}
    (hb : b ≠ 1#8) (h : KeyBytes960Inv b key keyBytes960) :
    ((sp + 0xb40#64) ↦ₛ keyBytes960) = fsKeys256At (sp + 0xb40#64) (aes256KeyScheduleFs key) := by
  rcases h with ⟨_, hbr⟩
  simp only [hb, ↓reduceIte] at hbr
  rw [hbr, ← fsKeys256At_eq_pointsToBytes]

theorem bv64_and15_eq_zero_iff (v : BitVec 64) :
    v &&& 15#64 = 0#64 ↔ v.toNat % 16 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and]
  have h15 : (15#64).toNat = 2 ^ 4 - 1 := rfl
  have h0 : (0#64).toNat = 0 := rfl
  rw [h15, h0, Nat.and_two_pow_sub_one_eq_mod]

/-! ## 2. Function Prologue (`fnAddr + 0x000#64 -> fnAddr + 0x028#64`) & Fast-Reject Path -/

theorem cbc_prologue_step {P : Program} {fnAddr target_pc : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64}
    {Rest : SepProp} {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hProl : hasInstrs P (fnAddr + 0x000#64) (decodeWords cbcPrologueWords))
    (hpc0 : s0.pc = fnAddr) (hrun0 : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hnext : ∀ s1 : State,
      s1.pc = fnAddr + 0x028#64 → s1.status = .Running →
      s1.sp = s0.sp - 3968#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      s1.readReg64 .x0 = s0.readReg64 .x0 → s1.readReg64 .x1 = s0.readReg64 .x1 →
      s1.readReg64 .x2 = s0.readReg64 .x2 → s1.readReg64 .x3 = s0.readReg64 .x3 →
      s1.readReg64 .x4 = s0.readReg64 .x4 → s1.readReg64 .x5 = s0.readReg64 .x5 →
      s1.readReg64 .x8 = s0.readReg64 .x8 → s1.readReg64 .lr = s0.readReg64 .lr →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 → PureStepPreserved s0 s1 →
      SepWP P target_pc s1
        (slots56 (s0.sp - 3968#64) 0#64 w1 w2 w3 w4 w5 (s0.readReg64 .x0) ∗
          savedStack96 s0 ∗ Rest) post oom) :
    SepWP P target_pc s0
      (slots56 (s0.sp - 3968#64) w0 w1 w2 w3 w4 w5 w6 ∗
        savedCells96 s0.sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 ∗ Rest) post oom := by
  have hProl0 : hasInstrs P fnAddr (decodeWords cbcPrologueWords) := by
    simpa only [BitVec.add_zero] using hProl
  have_instrs hProl0 0 10
  dsimp only [slots56, savedCells96, savedStack96]
  wp_stp64 hf_0 m0 hm0; wp_stp64 hf_1 m1 hm1; wp_stp64 hf_2 m2 hm2
  wp_stp64 hf_3 m3 hm3; wp_stp64 hf_4 m4 hm4; wp_stp64 hf_5 m5 hm5
  wp_steps 2; wp_str64 hf_8 m6 hm6; wp_str64 hf_9 m7 hm7
  refine hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun0])
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [calleeSavedVRegs, wp_norm, arm64_norm]) ?_
  exact PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hm7, hm6, hm5, hm4, hm3, hm2, hm1, hm0])

private theorem cbc_fast_reject_tail {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (x : AesCall) (st : M.σ) (r0 r1 r2 w0 w1 w2 w3 w4 w5 w6 : BitVec 64)
    (R : SepProp) (s0 sm : State)
    (hbad : x.input.length = 0 ∨ x.input.length % 16 ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpcm : sm.pc = fnAddr + 0x078#64) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 3968#64) (hx8 : sm.readReg64 .x8 = x.ret)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hpurem : PureStepPreserved s0 sm) :
    SepWPp P (s0.readReg64 .lr) sm
      ((hw.rconAddr ↦ᵣ aesRconBytes) ∗
        ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
        x.frame ∗ slots56 (s0.sp - 3968#64) w0 w1 w2 w3 w4 w5 w6 ∗
        memRegion (s0.sp - 3968#64 + 56#64) 3816 ∗ savedStack96 s0 ∗
        A.pool lim st s0 ∗ stackAt (s0.sp - 3968#64) allocHookStack)
      (cbcPost A lim hw.rconAddr errStr1Addr errStr2Addr x st R s0)
      (cbcPanic A lim x st R s0)
      (cbcOom M lim x st s0) := by
  have_instrs cs.postSoftKs 1 1
  apply SepWPp.of_sepWP (mid := fnAddr + 0x65c#64)
  wp_step; clear hf_1
  have_instrs cs.fastReject 0 4
  apply step_adrpAddPair cs.errStr1Pair (by decide)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrunm])
  have hpc84 : fnAddr + 0x07c#64 + 8#64 = fnAddr + 0x084#64 := by bv_lin
  try simp only [hpc84]
  wp_stp64 hf_0 m1 hm1
  wp_step
  wp_str64 hf_2 m2 hm2
  wp_step
  refine sepWP_done_let (by simp only [wp_norm, arm64_norm]; try bv_omega)
    (by simp [wp_norm, arm64_norm, hrunm]) fun sm2 hsm2 hpc2 hrun2 => ?_
  have hsp2 : sm2.sp = s0.sp - 3968#64 := by rw [hsm2]; simp [wp_norm, arm64_norm, hspm]
  have hv2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := by
    rw [hsm2]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hvm
  have hpure2 : PureStepPreserved s0 sm2 := by
    rw [hsm2]; exact hpurem.trans (PureStepPreserved.of_proj_perm
      (by simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm] at hm1 hm2 ⊢; exact hm2.trans hm1))
  have hpool2 : A.pool lim st sm2 = A.pool lim st s0 := hpure2.pool_eq A lim st
  clear hsm2
  have hx8' : sm.readReg64 (Reg.gpr 8#5) = x.ret := hx8
  try simp only [hx8', BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
  have hevs : aesDecEvents Spec.Aes256.aes256Dec x = [] := by
    unfold aesDecEvents; simp only [hbad, ↓reduceIte]
  have hst' : st = M.stepEvents (aesDecEvents Spec.Aes256.aes256Dec x) st := by
    rw [hevs, AllocCostModel.stepEvents_nil]
  have hdec : aesCbcDecrypt Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock x.iv) x.input = none :=
    aesCbcDecrypt_of_badLen Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock x.iv) hbad
  rw [← hpool2]
  let OutProp := x.frame ∗ ((x.ret ↦₆₄ errTag) ∗ ((x.ret + 8#64) ↦₆₄ errStr1Addr) ∗ ((x.ret + 16#64) ↦₆₄ 0x33#64))
  refine SepWPp.weaken_pre
    (P' := (hw.rconAddr ↦ᵣ aesRconBytes) ∗ OutProp ∗
      slots56 (s0.sp - 3968#64) w0 w1 w2 w3 w4 w5 w6 ∗
      memRegion (s0.sp - 3968#64 + 56#64) 3816 ∗
      savedStack96 s0 ∗ A.pool lim st sm2 ∗ stackAt (s0.sp - 3968#64) allocHookStack)
    (Entails.of_eq (by dsimp only [OutProp, errTag]; sep_ac_rfl)) ?_
  refine cbc_common_ret A lim hw.rconAddr errStr1Addr errStr2Addr cs.retEpilogue x st st
    w0 w1 w2 w3 w4 w5 w6 OutProp R s0 sm2 hsp0 hpc2 hrun2 hsp2 hv2 hpure2.allocCallPreserved hst' ?_
  rw [hdec]
  exact sepConj_mono_right
    (errResultErrRo_pack x.ret errStr1Addr errStr2Addr errStr1Addr 0x33#64 (Or.inl ⟨rfl, rfl⟩))

theorem cbc_fast_reject {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (x : AesCall) (st : M.σ) (r0 r1 r2 w0 w1 w2 w3 w4 w5 w6 : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hbad : x.input.length = 0 ∨ x.input.length % 16 ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = fnAddr + 0x028#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 3968#64)
    (hx1 : (s1.readReg64 .x1).toNat = x.input.length)
    (hx8 : s1.readReg64 .x8 = x.ret)
    (hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hpure1 : PureStepPreserved s0 s1) :
    SepWPp P (s0.readReg64 .lr) s1
      ((hw.rconAddr ↦ᵣ aesRconBytes) ∗
        ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
        x.frame ∗ slots56 (s0.sp - 3968#64) w0 w1 w2 w3 w4 w5 w6 ∗
        memRegion (s0.sp - 3968#64 + 56#64) 3816 ∗ savedStack96 s0 ∗
        A.pool lim st s0 ∗ stackAt (s0.sp - 3968#64) allocHookStack)
      (cbcPost A lim hw.rconAddr errStr1Addr errStr2Addr x st R s0)
      (cbcPanic A lim x st R s0)
      (cbcOom M lim x st s0) := by
  have_instrs cs.prologue 10 3
  apply SepWPp.of_sepWP (mid := fnAddr + 0x078#64)
  wp_step; wp_if hc1
  · refine sepWP_done_let (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun1]) fun sm hsm hpcm hrunm => ?_
    have hspm : sm.sp = s0.sp - 3968#64 := by rw [hsm]; simp [arm64_norm, hsp1]
    have hx8m : sm.readReg64 .x8 = x.ret := by rw [hsm]; simp [arm64_norm, hx8]
    have hvm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      rw [hsm]; simpa [calleeSavedVRegs, arm64_norm] using hv1
    have hpurem : PureStepPreserved s0 sm := by
      rw [hsm]; exact hpure1.trans
        (PureStepPreserved.of_proj_perm (by simp [arm64_norm]) (by simp [arm64_norm]))
    clear hsm
    exact cbc_fast_reject_tail A lim cs x st r0 r1 r2 w0 w1 w2 w3 w4 w5 w6 R s0 sm
      hbad hsp0 hpcm hrunm hspm hx8m hvm hpurem
  · wp_step; wp_step; wp_if hc2
    · refine sepWP_done_let (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun1]) fun sm hsm hpcm hrunm => ?_
      have hspm : sm.sp = s0.sp - 3968#64 := by rw [hsm]; simp [arm64_norm, hsp1]
      have hx8m : sm.readReg64 .x8 = x.ret := by rw [hsm]; simp [arm64_norm, hx8]
      have hvm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
        rw [hsm]; simpa [calleeSavedVRegs, arm64_norm] using hv1
      have hpurem : PureStepPreserved s0 sm := by
        rw [hsm]; exact hpure1.trans
          (PureStepPreserved.of_proj_perm (by simp [arm64_norm]) (by simp [arm64_norm]))
      clear hsm
      exact cbc_fast_reject_tail A lim cs x st r0 r1 r2 w0 w1 w2 w3 w4 w5 w6 R s0 sm
        hbad hsp0 hpcm hrunm hspm hx8m hvm hpurem
    · exfalso
      have hlen_ne : x.input.length ≠ 0 := by
        intro hlen0; apply hc1; apply BitVec.eq_of_toNat_eq; simpa [hx1] using hlen0
      exact (hbad.resolve_left hlen_ne) (hx1 ▸ (bv64_and15_eq_zero_iff (s1.readReg64 .x1)).mp hc2)

/-! ## 3. Key-Schedule Call Wrappers & 31-Insn SIMD `ek` Copy -/

theorem step_bl_keySchedule {P : Program}
    {blPc calleeAddr target_pc : BitVec 64} (sp outPtr keyPtr : BitVec 64) {key : List (BitVec 8)}
    (hbl : hasInstrs P blPc [.bl (calleeAddr - blPc)])
    (hcall : subroutine_ok P calleeAddr aes256KeyScheduleSpec)
    {s : State} {Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = keyPtr) (hx8 : s.readReg64 .x8 = outPtr) (hlen : key.length = 32)
    (hFull : Full = ((keyPtr ↦ₛ key) ∗ memRegion outPtr 960 ∗ stackFrameAt sp 1120) ∗ F)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running →
      sf.sp = sp → CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf
        (((keyPtr ↦ₛ key) ∗ fsKeys256At outPtr (aes256KeyScheduleFs key) ∗ stackFrameAt sp 1120) ∗ F)
        post oom) :
    SepWP P target_pc s Full post oom := by
  have hsp_cal : ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).sp = sp := by
    simp [arm64_norm, hsp]
  exact step_bl_call hbl hcall (false, outPtr, keyPtr, key)
    (φ := ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).readReg64 .x0 = keyPtr ∧
          ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).readReg64 .x8 = outPtr ∧
          key.length = 32)
    (ψ := fun sf => PureStepPreserved ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr) sf)
    hpc hrun hsp_al
    (by dsimp only [aes256KeyScheduleSpec, bytesAt]; simp only [Bool.false_eq_true, ↓reduceIte, hsp_cal])
    (fun sf => by dsimp only [aes256KeyScheduleSpec, bytesAt]; simp only [Bool.false_eq_true, ↓reduceIte, hsp_cal])
    hFull
    ⟨by simp [arm64_norm, hx0], by simp [arm64_norm, hx8], hlen⟩
    fun sf hpc' hrun' hsp' hcs hpure =>
      hnext sf hpc' hrun' (hsp'.trans hsp) hcs (pureStepPreserved_bl hpure)

theorem step_bl_expandKey15 {P : Program}
    {blPc calleeAddr rconAddr target_pc : BitVec 64} (sp outPtr keyPtr : BitVec 64) {key : List (BitVec 8)}
    (hbl : hasInstrs P blPc [.bl (calleeAddr - blPc)])
    (hcall : subroutine_ok P calleeAddr (expandKey15RegionSpec rconAddr))
    {s : State} {Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = outPtr) (hx1 : s.readReg64 .x1 = keyPtr) (hlen : key.length = 32)
    (hFull : Full = (memRegion outPtr 240 ∗ (keyPtr ↦ₛ key) ∗
                     (rconAddr ↦ᵣ aesRconBytes) ∗ stackFrameAt sp 0x100) ∗ F)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running →
      sf.sp = sp → CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf
        ((roundKeys15At outPtr (armv8ExpandKey key) ∗ (keyPtr ↦ₛ key) ∗
          (rconAddr ↦ᵣ aesRconBytes) ∗ stackFrameAt sp 0x100) ∗ F)
        post oom) :
    SepWP P target_pc s Full post oom := by
  have hsp_cal : ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).sp = sp := by
    simp [arm64_norm, hsp]
  have hbKey : bytesAt false keyPtr key = (keyPtr ↦ₛ key) := rfl
  have hbRcon : bytesAt true rconAddr aesRconBytes = (rconAddr ↦ᵣ aesRconBytes) := rfl
  exact step_bl_call hbl hcall (false, true, outPtr, keyPtr, key)
    (φ := ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).readReg64 .x0 = outPtr ∧
          ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).readReg64 .x1 = keyPtr ∧
          key.length = 32)
    (ψ := fun sf => PureStepPreserved ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr) sf ∧
                    sf.readReg64 .x0 = outPtr)
    hpc hrun hsp_al
    (by dsimp only [expandKey15RegionSpec]; rw [hbKey, hbRcon, hsp_cal])
    (fun sf => by dsimp only [expandKey15RegionSpec]; rw [hbKey, hbRcon, hsp_cal])
    hFull
    ⟨by simp [arm64_norm, hx0], by simp [arm64_norm, hx1], hlen⟩
    fun sf hpc' hrun' hsp' hcs ⟨hpure, _⟩ =>
      hnext sf hpc' hrun' (hsp'.trans hsp) hcs (pureStepPreserved_bl hpure)

theorem step_bl_invExpand15 {P : Program}
    {blPc calleeAddr target_pc : BitVec 64} (sp dkPtr ekPtr : BitVec 64) {ek : Vector (BitVec 128) 15}
    (hbl : hasInstrs P blPc [.bl (calleeAddr - blPc)])
    (hcall : subroutine_ok P calleeAddr invExpandedKeys15RegionSpec)
    {s : State} {Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = dkPtr) (hx1 : s.readReg64 .x1 = ekPtr)
    (hFull : Full = (memRegion dkPtr 240 ∗ roundKeys15At ekPtr ek) ∗ F)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running →
      sf.sp = sp → CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf
        ((roundKeys15At dkPtr (armv8InvExpandedKeys ek) ∗ roundKeys15At ekPtr ek) ∗ F)
        post oom) :
    SepWP P target_pc s Full post oom :=
  let s' := (s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr
  step_bl_call hbl hcall (dkPtr, ekPtr, ek)
    (φ := s'.readReg64 .x0 = dkPtr ∧ s'.readReg64 .x1 = ekPtr)
    (ψ := fun sf => PureStepPreserved s' sf ∧ sf.regs = s'.regs)
    hpc hrun hsp_al rfl (fun _ => rfl) hFull
    ⟨by simp [s', arm64_norm, hx0], by simp [s', arm64_norm, hx1]⟩
    fun sf hpc' hrun' hsp' hcs ⟨hpure, _⟩ =>
      hnext sf hpc' hrun' (hsp'.trans hsp) hcs (pureStepPreserved_bl hpure)

theorem cbc_hw_copy_ek {P : Program} {fnAddr target_pc sp : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x0c0#64) (decodeWords cbcHwCopyEkWords))
    (ek : Vector (BitVec 128) 15) (Rest : SepProp) (s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x0c0#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (_hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0x13c#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x0 = sp + 0xb40#64 →
      sf.readReg64 .x1 = sp + 0x870#64 →
      sf.readReg64 .x2 = 480#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (roundKeys15At (sp + 0x870#64) ek ∗ roundKeys15At (sp + 0xa50#64) ek ∗ Rest)
        post oom) :
    SepWP P target_pc s
      (memRegion (sp + 0x870#64) 240 ∗ roundKeys15At (sp + 0xa50#64) ek ∗ Rest) post oom := by
  rw [memRegion240_eq_exists_roundKeys15At (sp + 0x870#64), sepExists_sepConj_left]
  apply SepWP.exists_elim; intro dst0
  have_instrs hc 0 31
  simp only [roundKeys15At, BitVec.add_assoc, BitVec.reduceAdd]
  wp_ldr128 hf_0; wp_ldr128 hf_1; wp_step; wp_ldr128 hf_3; wp_ldr128 hf_4; wp_step
  wp_str128 hf_6 m1 hm1; wp_ldr128 hf_7; wp_step; wp_str128 hf_9 m2 hm2
  wp_ldr128 hf_10; wp_str128 hf_11 m3 hm3; wp_ldr128 hf_12; wp_str128 hf_13 m4 hm4
  wp_ldr128 hf_14; wp_str128 hf_15 m5 hm5; wp_ldr128 hf_16; wp_str128 hf_17 m6 hm6
  wp_ldr128 hf_18; wp_str128 hf_19 m7 hm7; wp_ldr128 hf_20; wp_str128 hf_21 m8 hm8
  wp_ldr128 hf_22; wp_str128 hf_23 m9 hm9; wp_ldr128 hf_24; wp_str128 hf_25 m10 hm10
  wp_ldr128 hf_26; wp_stp128 hf_27 m11 hm11; wp_ldr128 hf_28; wp_stp128 hf_29 m12 hm12
  wp_str128 hf_30 m13 hm13
  refine sepWP_weaken_pre (Entails.of_eq (by dsimp only [roundKeys15At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]))
    (hnext _
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp])
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx24])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm] at hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11 hm12 hm13 ⊢
            exact hm13.trans (hm12.trans (hm11.trans (hm10.trans (hm9.trans (hm8.trans
              (hm7.trans (hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1))))))))))))))

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologFast

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Model
public import ProofLib.SepLogic.WP
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
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftCommon
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadIter

/-!
# `Fixslice64` 4-Block Parallel CBC Decryption Loop (`CbcDec.SoftQuad`)

Verifies `fnAddr + 0x67c#64 -> fnAddr + 0xbc0#64` (`0x4c97d0..0x4c9d10`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuad

open Arm64 ProofLib SepProp ProofLib.SepLogic
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (aes256KeyScheduleFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (PureStepPreserved)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (Aes256DecHwAddrs Aes256CbcDecryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs (CbcDecCodeSegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
  (cbcChainAt cbcPrefixBytes cbcPrefixBytes_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules (sepWP_weaken_pre)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules.Macros
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common (slots56)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftCommon
  (cbcSoftWork lsr6_ofNat_eq ubfx4_2_shift_and_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadIter (cbc_quad_iter)

private theorem cbc_quad_loop_from {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp outBuf : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (Other : SepProp) (s0 : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlt40 : x.input.length < 2 ^ 40)
    (hkey32 : x.key.length = 32) (hiv16 : x.iv.length = 16)
    (hspAl : (sp &&& 15#64 == 0#64) = true) :
    ∀ (k q : Nat) (s : State),
      q + (k + 1) = x.input.length / 64 →
      s.pc = fnAddr + 0x694#64 → s.status = .Running → s.sp = sp →
      s.readReg64 .x20 = outBuf + BitVec.ofNat 64 (64 * q) →
      s.readReg64 .x24 = sp + 0x4b0#64 →
      s.readReg64 .x26 = x.inA + BitVec.ofNat 64 (64 * q) + 0x18#64 →
      s.readReg64 .x27 = BitVec.ofNat 64 (x.input.length / 64 - q) →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ sf : State,
        sf.pc = fnAddr + 0xbc0#64 → sf.status = .Running → sf.sp = sp →
        sf.readReg64 .x22 = sp + 0xb40#64 →
        sf.readReg64 .x24 = sp + 0x4b0#64 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        PureStepPreserved s sf →
        SepWP P target_pc sf
          (cbcSoftWork sp (aes256KeyScheduleFs x.key)
            (cbcChainAt x.iv x.input (4 * (x.input.length / 64))) ∗
           (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input (4 * (x.input.length / 64)) ++
             List.replicate (x.input.length - 64 * (x.input.length / 64)) 0#8)) ∗
           (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Other)
          post oom) →
      SepWP P target_pc s
        (cbcSoftWork sp (aes256KeyScheduleFs x.key) (cbcChainAt x.iv x.input (4 * q)) ∗
         (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input (4 * q) ++
           List.replicate (x.input.length - 64 * q) 0#8)) ∗
         (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Other)
        post oom := by
  intro k
  induction k with
  | zero =>
    intro q s hqk hpc hrun hsp hx20 hx24 hx26 hx27 hv hnext
    refine cbc_quad_iter (hSplit := hSplit) cs hCal x q Other s0 s (by omega) hlt40 hkey32 hiv16 hspAl
      hpc hrun hsp hx20 hx24 hx26 hx27 hv
      fun sf hpc_f hrun_f hsp_f _ hx22_f hx24_f _ _ hx29_f hv_f hpure_f => ?_
    have hq1 : q + 1 = x.input.length / 64 := by omega
    simp only [hq1, ↓reduceIte] at hpc_f
    rw [hq1]
    exact hnext sf hpc_f hrun_f hsp_f hx22_f hx24_f hx29_f hv_f hpure_f
  | succ k ih =>
    intro q s hqk hpc hrun hsp hx20 hx24 hx26 hx27 hv hnext
    refine cbc_quad_iter (hSplit := hSplit) cs hCal x q Other s0 s (by omega) hlt40 hkey32 hiv16 hspAl
      hpc hrun hsp hx20 hx24 hx26 hx27 hv
      fun s1 hpc1 hrun1 hsp1 hx20_1 _ hx24_1 hx26_1 hx27_1 hx29_1 hv1 hpure1 => ?_
    have hq1 : q + 1 ≠ x.input.length / 64 := by omega
    simp only [hq1, ↓reduceIte] at hpc1
    exact ih (q + 1) s1 (by omega) hpc1 hrun1 hsp1 hx20_1 hx24_1 hx26_1 hx27_1 hv1
      fun sf hpc_f hrun_f hsp_f hx22_f hx24_f hx29_f hv_f hpure_f =>
        hnext sf hpc_f hrun_f hsp_f hx22_f hx24_f (hx29_f.trans hx29_1) hv_f (hpure1.trans hpure_f)

set_option maxHeartbeats 400000 in
theorem cbc_quad_loop {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp outBuf : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (w0 w1 w2 w3 w4 : BitVec 64) (Rest : SepProp) (s0 s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlt40 : x.input.length < 2 ^ 40)
    (hkey32 : x.key.length = 32) (hiv16 : x.iv.length = 16)
    (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = fnAddr + 0x67c#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx22 : s.readReg64 .x22 = sp + 0xb40#64)
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.input.length)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0xbc0#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x22 = sp + 0xb40#64 →
      sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (slots56 sp w0 (BitVec.ofNat 64 ((x.input.length / 16) % 4)) w2 w3 w4 outBuf x.inA ∗
         cbcSoftWork sp (aes256KeyScheduleFs x.key)
           (cbcChainAt x.iv x.input (4 * (x.input.length / 64))) ∗
         (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input (4 * (x.input.length / 64)) ++
           List.replicate (x.input.length - 64 * (x.input.length / 64)) 0#8)) ∗
         (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Rest)
        post oom) :
    SepWP P target_pc s
      (slots56 sp w0 w1 w2 w3 w4 outBuf x.inA ∗
       cbcSoftWork sp (aes256KeyScheduleFs x.key) x.iv ∗
       (outBuf ↦ₛ List.replicate x.input.length 0#8) ∗
       (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Rest)
      post oom := by
  have hlt64 : x.input.length < 2 ^ 64 := by omega
  have hlsr6 := lsr6_ofNat_eq x.input.length hlt64
  have hubfx := ubfx4_2_shift_and_eq x.input.length hlt64
  have_instrs cs.softQuadSetup 0 6
  dsimp only [slots56]
  wp_steps 2
  wp_str64 hf_2 m0 hm0
  wp_step
  wp_if h_cbz
  · have hq0 : x.input.length / 64 = 0 := by
      have heq : BitVec.ofNat 64 (x.input.length / 64) = 0#64 := by
        simpa [wp_norm, arm64_norm, hx25, hlsr6] using h_cbz
      have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      exact ht
    have hnext0 := hnext
    rw [hq0] at hnext0
    dsimp only [Nat.mul_zero, Nat.sub_zero, cbcChainAt, cbcPrefixBytes_zero, List.nil_append, slots56] at hnext0
    refine sepWP_weaken_pre
      (Entails.of_eq (by simp only [wp_norm, arm64_norm]))
      (hnext0 _
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp [wp_norm, arm64_norm, hx22])
        (by simp [wp_norm, arm64_norm, hx24])
        (by simp [wp_norm, arm64_norm])
        (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv)
        (PureStepPreserved.of_proj_perm
          (by simp [wp_norm, arm64_norm])
          (by simpa [wp_norm, arm64_norm] using hm0)))
  · have hqpos : 0 < x.input.length / 64 := by
      rcases Nat.eq_zero_or_pos (x.input.length / 64) with h0 | hp
      · exfalso; simp [wp_norm, arm64_norm, h0] at h_cbz
      · exact hp
    wp_steps 2
    refine sepWP_weaken_pre
      (Entails.of_eq (by
        dsimp only [Nat.mul_zero, Nat.sub_zero, cbcChainAt, cbcPrefixBytes_zero, List.nil_append, slots56]
        simp only [wp_norm, arm64_norm]; try sep_ac_rfl))
      (cbc_quad_loop_from (hSplit := hSplit) cs hCal x
        (slots56 sp w0 (BitVec.ofNat 64 ((x.input.length / 16) % 4)) w2 w3 w4 outBuf x.inA ∗ Rest) s0
        hlt40 hkey32 hiv16 hspAl (x.input.length / 64 - 1) 0 _ (by omega)
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hx24])
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm])
        (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv)
        fun sf hpc_f hrun_f hsp_f hx22_f hx24_f hx29_f hv_f hpure_f => ?_)
    refine sepWP_weaken_pre (Entails.of_eq (by dsimp only [slots56]; sep_ac_rfl))
      (hnext sf hpc_f hrun_f hsp_f hx22_f hx24_f
        (hx29_f.trans (by simp [wp_norm, arm64_norm]))
        hv_f
        (PureStepPreserved.trans
          (PureStepPreserved.of_proj_perm
            (by simp [wp_norm, arm64_norm])
            (by simpa [wp_norm, arm64_norm] using hm0))
          hpure_f))

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuad

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
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.Bytes
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadStepsA
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadStepsB

/-!
# `Fixslice64` Single 64-Byte (4-Block) CBC Iteration (`CbcDec.SoftQuadIter`)
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadIter

open Arm64 ProofLib SepProp ProofLib.SepLogic
open CryptoGames.CBC (blockToBytesLE blockToBytesLE_bytesToBlock)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (Blocks4 aes256KeyScheduleFs aes256DecryptFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing (Blocks4.Wf)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved fsKeys256At blocks4Bytes)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec
  (blocks4Bytes_aes256DecryptFs_quad)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (Aes256DecHwAddrs Aes256CbcDecryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs (CbcDecCodeSegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
  (cbcChainAt cbcChainAt_succ cbcChainAt_length
   cbcPrefixBytes cbcPrefixBytes_length cbcPrefixBytes_step4)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
  (sepWP_weaken_pre pack8LE bytes16At pointsToBytes16_eq_bytes16At
   pointsToBytes16_eq_pts64_pair pts64_pair_eq_bytes16At exists_bytes16
   pts64x8At pts64x8At_entails_memRegion64 sepWP_memRegion64_pts64x8_elim
   spill14At spill14At_entails_memRegion56 sepWP_memRegion56_spill14_elim)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
  (step_bl_decrypt stackAt_allocHook_split208)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftCommon
  (cbcSoftWork bv64_ofNat_sub_one bv64_ofNat_beq_zero bv64_add_ofNat_64
   list_slice64_eq exists_bytes64 pts64x8At_pack8LE_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadStepsA
  (cbc_quad_pre1 cbc_quad_pre2 cbc_quad_post1a cbc_quad_post1b)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadStepsB
  (cbc_quad_post2 cbc_quad_post3 cbc_quad_post4 cbc_quad_post5)

set_option maxHeartbeats 500000 in
theorem cbc_quad_iter {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp outBuf : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (q : Nat) (Other : SepProp) (s0 s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hq : q < x.input.length / 64) (hlt40 : x.input.length < 2 ^ 40)
    (hkey32 : x.key.length = 32) (hiv16 : x.iv.length = 16)
    (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = fnAddr + 0x694#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = outBuf + BitVec.ofNat 64 (64 * q))
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hx26 : s.readReg64 .x26 = x.inA + BitVec.ofNat 64 (64 * q) + 0x18#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (x.input.length / 64 - q))
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ sf : State,
      sf.pc = (if q + 1 = x.input.length / 64 then fnAddr + 0xbc0#64 else fnAddr + 0x694#64) →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x20 = outBuf + BitVec.ofNat 64 (64 * (q + 1)) →
      sf.readReg64 .x22 = sp + 0xb40#64 → sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x26 = x.inA + BitVec.ofNat 64 (64 * (q + 1)) + 0x18#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 (x.input.length / 64 - (q + 1)) →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → PureStepPreserved s sf →
      SepWP P target_pc sf
        (cbcSoftWork sp (aes256KeyScheduleFs x.key) (cbcChainAt x.iv x.input (4 * (q + 1))) ∗
         (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input (4 * (q + 1)) ++
           List.replicate (x.input.length - 64 * (q + 1)) 0#8)) ∗
         (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Other)
        post oom) :
    SepWP P target_pc s
      (cbcSoftWork sp (aes256KeyScheduleFs x.key) (cbcChainAt x.iv x.input (4 * q)) ∗
       (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input (4 * q) ++
         List.replicate (x.input.length - 64 * q) 0#8)) ∗
       (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Other)
      post oom := by
  let ks := aes256KeyScheduleFs x.key
  let src := x.inA + BitVec.ofNat 64 (64 * q)
  let dst := outBuf + BitVec.ofNat 64 (64 * q)
  have h64q : 64 * (q + 1) ≤ x.input.length := by omega
  have hm4 : 4 * q + 4 ≤ x.input.length / 16 := by omega
  let c0_bs := (x.input.drop (16 * (4 * q))).take 16
  let c1_bs := (x.input.drop (16 * (4 * q + 1))).take 16
  let c2_bs := (x.input.drop (16 * (4 * q + 2))).take 16
  let c3_bs := (x.input.drop (16 * (4 * q + 3))).take 16
  let prev_bs := cbcChainAt x.iv x.input (4 * q)
  have hc0_len : c0_bs.length = 16 := by dsimp [c0_bs]; rw [List.length_take, List.length_drop]; omega
  have hc1_len : c1_bs.length = 16 := by dsimp [c1_bs]; rw [List.length_take, List.length_drop]; omega
  have hc2_len : c2_bs.length = 16 := by dsimp [c2_bs]; rw [List.length_take, List.length_drop]; omega
  have hc3_len : c3_bs.length = 16 := by dsimp [c3_bs]; rw [List.length_take, List.length_drop]; omega
  have hp_len : prev_bs.length = 16 := cbcChainAt_length hiv16 (by omega)
  have hin_split :
      (x.inA ↦ₛ x.input) =
        ((x.inA ↦ₛ x.input.take (64 * q)) ∗ (src ↦ₛ c0_bs) ∗ ((src + 16#64) ↦ₛ c1_bs) ∗
         ((src + 32#64) ↦ₛ c2_bs) ∗ ((src + 48#64) ↦ₛ c3_bs) ∗
         ((x.inA + BitVec.ofNat 64 (64 * (q + 1))) ↦ₛ x.input.drop (64 * (q + 1)))) := by
    conv => lhs; rw [list_slice64_eq h64q]
    change (x.inA ↦ₛ (x.input.take (64 * q) ++ (c0_bs ++ (c1_bs ++ (c2_bs ++ (c3_bs ++ x.input.drop (64 * (q + 1)))))))) = _
    have htake_len : (x.input.take (64 * q)).length = 64 * q := by rw [List.length_take]; omega
    rw [pointsToBytes_append, htake_len, pointsToBytes_append, hc0_len,
        pointsToBytes_append, hc1_len, pointsToBytes_append, hc2_len, pointsToBytes_append, hc3_len]
    dsimp only [src]
    have ha32 : x.inA + BitVec.ofNat 64 (64 * q) + 16#64 + 16#64 = x.inA + BitVec.ofNat 64 (64 * q) + 32#64 := by bv_lin
    have ha48 : x.inA + BitVec.ofNat 64 (64 * q) + 32#64 + 16#64 = x.inA + BitVec.ofNat 64 (64 * q) + 48#64 := by bv_lin
    have ha64 : x.inA + BitVec.ofNat 64 (64 * q) + 48#64 + 16#64 = x.inA + BitVec.ofNat 64 (64 * (q + 1)) := by
      rw [show x.inA + BitVec.ofNat 64 (64 * q) + 48#64 + 16#64 = x.inA + BitVec.ofNat 64 (64 * q) + 64#64 from by bv_lin]
      exact bv64_add_ofNat_64 x.inA (by omega)
    rw [ha32, ha48, ha64]
  have hpre_len : (cbcPrefixBytes x.key x.iv x.input (4 * q)).length = 64 * q := by
    rw [cbcPrefixBytes_length (by omega)]; omega
  have hrep_split : List.replicate (x.input.length - 64 * q) 0#8 =
      List.replicate 64 0#8 ++ List.replicate (x.input.length - 64 * (q + 1)) 0#8 := by
    rw [← List.replicate_add]; exact congrArg (List.replicate · 0#8) (by omega)
  have hout_split :
      (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input (4 * q) ++ List.replicate (x.input.length - 64 * q) 0#8)) =
        ((outBuf ↦ₛ cbcPrefixBytes x.key x.iv x.input (4 * q)) ∗ (dst ↦ₛ List.replicate 64 0#8) ∗
         ((outBuf + BitVec.ofNat 64 (64 * (q + 1))) ↦ₛ List.replicate (x.input.length - 64 * (q + 1)) 0#8)) := by
    rw [hrep_split, pointsToBytes_append, hpre_len, pointsToBytes_append, List.length_replicate]
    dsimp only [dst]; rw [bv64_add_ofNat_64 outBuf (by omega)]
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15, hc0_eq⟩ := exists_bytes16 hc0_len
  obtain ⟨c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31, hc1_eq⟩ := exists_bytes16 hc1_len
  obtain ⟨c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47, hc2_eq⟩ := exists_bytes16 hc2_len
  obtain ⟨c48,c49,c50,c51,c52,c53,c54,c55,c56,c57,c58,c59,c60,c61,c62,c63, hc3_eq⟩ := exists_bytes16 hc3_len
  obtain ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15, hp_eq⟩ := exists_bytes16 hp_len
  have hdst_mem : (dst ↦ₛ List.replicate 64 0#8) ⊢ memRegion dst 64 := by
    simpa only [List.length_replicate] using pointsToBytes_entails_memRegion dst (List.replicate 64 0#8)
  have h168_split : memRegion (sp + 0x03c#64) 168 =
      memRegion (sp + 0x03c#64) 56 ∗ memRegion (sp + 0x074#64) 56 ∗ memRegion (sp + 0x0ac#64) 56 := by
    have hs1 := memRegion_split (sp + 0x03c#64) 56 112 (by decide)
    have hs2 := memRegion_split (sp + 0x074#64) 56 56 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs1 hs2
    rw [show (168 : Nat) = 56 + 112 from rfl, hs1, show (112 : Nat) = 56 + 56 from rfl, hs2]
  let TailRest :=
    (outBuf ↦ₛ cbcPrefixBytes x.key x.iv x.input (4 * q)) ∗
    ((outBuf + BitVec.ofNat 64 (64 * (q + 1))) ↦ₛ List.replicate (x.input.length - 64 * (q + 1)) 0#8) ∗
    (x.inA ↦ₛ x.input.take (64 * q)) ∗
    ((x.inA + BitVec.ofNat 64 (64 * (q + 1))) ↦ₛ x.input.drop (64 * (q + 1))) ∗ Other
  rw [hin_split, hout_split]
  dsimp only [cbcSoftWork]
  refine sepWP_weaken_pre
    (P2 := memRegion (sp + 0x870#64) 64 ∗ memRegion (sp + 0x4b0#64) 64 ∗ memRegion dst 64 ∗
      memRegion (sp + 0x03c#64) 56 ∗ memRegion (sp + 0x074#64) 56 ∗ memRegion (sp + 0x0ac#64) 56 ∗
      ((src ↦ₛ c0_bs) ∗ ((src + 16#64) ↦ₛ c1_bs) ∗ ((src + 32#64) ↦ₛ c2_bs) ∗ ((src + 48#64) ↦ₛ c3_bs) ∗
       ((sp + 0xf00#64) ↦ₛ prev_bs) ∗ fsKeys256At (sp + 0xb40#64) ks ∗ stackAt sp allocHookStack ∗ TailRest))
    (by
      dsimp only [TailRest]; rw [h168_split]
      refine Entails.trans (Entails.of_eq (show _ = (dst ↦ₛ List.replicate 64 0#8) ∗ _ by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hdst_mem) (Entails.of_eq (by sep_ac_rfl))) ?_
  refine sepWP_memRegion64_pts64x8_elim fun i0 i1 i2 i3 i4 i5 i6 i7 => ?_
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (sp + 0x4b0#64) 64 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion64_pts64x8_elim fun o0 o1 o2 o3 o4 o5 o6 o7 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion dst 64 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion64_pts64x8_elim fun z0 z1 z2 z3 z4 z5 z6 z7 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (sp + 0x03c#64) 56 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion56_spill14_elim fun g0_0 g0_1 g0_2 g0_3 g0_4 g0_5 g0_6 g0_7 g0_8 g0_9 g0_10 g0_11 g0_12 g0_13 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (sp + 0x074#64) 56 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion56_spill14_elim fun g1_0 g1_1 g1_2 g1_3 g1_4 g1_5 g1_6 g1_7 g1_8 g1_9 g1_10 g1_11 g1_12 g1_13 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (sp + 0x0ac#64) 56 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion56_spill14_elim fun g2_0 g2_1 g2_2 g2_3 g2_4 g2_5 g2_6 g2_7 g2_8 g2_9 g2_10 g2_11 g2_12 g2_13 => ?_)
  have hc0_at : (src ↦ₛ c0_bs) = bytes16At src c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 := by
    rw [hc0_eq, pointsToBytes16_eq_bytes16At]
  have hc1_p : ((src + 16#64) ↦ₛ c1_bs) =
      (((src + 16#64) ↦₆₄ pack8LE c16 c17 c18 c19 c20 c21 c22 c23) ∗
       ((src + 24#64) ↦₆₄ pack8LE c24 c25 c26 c27 c28 c29 c30 c31)) := by
    rw [hc1_eq, pointsToBytes16_eq_pts64_pair]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hc2_p : ((src + 32#64) ↦ₛ c2_bs) =
      (((src + 32#64) ↦₆₄ pack8LE c32 c33 c34 c35 c36 c37 c38 c39) ∗
       ((src + 40#64) ↦₆₄ pack8LE c40 c41 c42 c43 c44 c45 c46 c47)) := by
    rw [hc2_eq, pointsToBytes16_eq_pts64_pair]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hc3_p : ((src + 48#64) ↦ₛ c3_bs) =
      (((src + 48#64) ↦₆₄ pack8LE c48 c49 c50 c51 c52 c53 c54 c55) ∗
       ((src + 56#64) ↦₆₄ pack8LE c56 c57 c58 c59 c60 c61 c62 c63)) := by
    rw [hc3_eq, pointsToBytes16_eq_pts64_pair]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  let StableRest := pts64x8At dst z0 z1 z2 z3 z4 z5 z6 z7 ∗ ((sp + 0xf00#64) ↦ₛ prev_bs) ∗
    fsKeys256At (sp + 0xb40#64) ks ∗ stackAt sp allocHookStack ∗ TailRest
  refine sepWP_weaken_pre (Entails.of_eq (by
      rw [hc0_at, hc1_p, hc2_p, hc3_p]; dsimp only [StableRest]; sep_ac_rfl))
    (cbc_quad_pre1 cs.softQuadPre1
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31
      c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56 c57 c58 c59 c60 c61 c62 c63
      i0 i1 i2 i3 i4 i5 i6 i7 o0 o1 o2 o3 o4 o5 o6 o7
      g0_0 g0_1 g0_2 g0_3 g0_4 g0_5 g0_6 g0_7 g0_8 g0_9 g0_10 g0_11 g0_12 g0_13
      (spill14At (sp + 0x074#64) g1_0 g1_1 g1_2 g1_3 g1_4 g1_5 g1_6 g1_7 g1_8 g1_9 g1_10 g1_11 g1_12 g1_13 ∗
       spill14At (sp + 0x0ac#64) g2_0 g2_1 g2_2 g2_3 g2_4 g2_5 g2_6 g2_7 g2_8 g2_9 g2_10 g2_11 g2_12 g2_13 ∗ StableRest)
      s hpc hrun hsp hspAl hx24 hx26
      fun s1 hpc1 hrun1 hsp1 hx0_1 hx1_1 _ _ hx10_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
          hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hv1 hpure1 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (cbc_quad_pre2 cs.softQuadPre2
      c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31
      c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47
      g1_0 g1_1 g1_2 g1_3 g1_4 g1_5 g1_6 g1_7 g1_8 g1_9 g1_10 g1_11 g1_12 g1_13
      g2_0 g2_1 g2_2 g2_3 g2_4 g2_5 g2_6 g2_7 g2_8 g2_9 g2_10 g2_11 g2_12 g2_13
      (bytes16At src c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 ∗
       ((src + 48#64) ↦₆₄ pack8LE c48 c49 c50 c51 c52 c53 c54 c55) ∗
       ((src + 56#64) ↦₆₄ pack8LE c56 c57 c58 c59 c60 c61 c62 c63) ∗
       pts64x8At (sp + 0x870#64)
         (pack8LE c0 c1 c2 c3 c4 c5 c6 c7) (pack8LE c8 c9 c10 c11 c12 c13 c14 c15)
         (pack8LE c16 c17 c18 c19 c20 c21 c22 c23) (pack8LE c24 c25 c26 c27 c28 c29 c30 c31)
         (pack8LE c32 c33 c34 c35 c36 c37 c38 c39) (pack8LE c40 c41 c42 c43 c44 c45 c46 c47)
         (pack8LE c48 c49 c50 c51 c52 c53 c54 c55) (pack8LE c56 c57 c58 c59 c60 c61 c62 c63) ∗
       pts64x8At (sp + 0x4b0#64)
         o0 o1
         (pack8LE c16 c17 c18 c19 c20 c21 c22 c23) (pack8LE c24 c25 c26 c27 c28 c29 c30 c31)
         (pack8LE c32 c33 c34 c35 c36 c37 c38 c39) (pack8LE c40 c41 c42 c43 c44 c45 c46 c47)
         (pack8LE c48 c49 c50 c51 c52 c53 c54 c55) (pack8LE c56 c57 c58 c59 c60 c61 c62 c63) ∗
       spill14At (sp + 0x03c#64)
         (c7.zeroExtend 32) (c6.zeroExtend 32) (c8.zeroExtend 32) (c9.zeroExtend 32)
         (c11.zeroExtend 32) (c10.zeroExtend 32) (c12.zeroExtend 32) (c13.zeroExtend 32)
         (c15.zeroExtend 32) (c14.zeroExtend 32) (c16.zeroExtend 32) (c17.zeroExtend 32)
         (c19.zeroExtend 32) (c18.zeroExtend 32) ∗ StableRest)
      s1 hpc1 hrun1 hsp1 hspAl hx10_1 hx26_1
      fun s2 hpc2 hrun2 hsp2 hx0_2 hx1_2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
          hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hv2 hpure2 => ?_)
  let bs_in : Blocks4 := ⟨c0_bs, c1_bs, c2_bs, c3_bs⟩
  have hwf_in : Blocks4.Wf bs_in := ⟨hc0_len, hc1_len, hc2_len, hc3_len⟩
  have hin_buf_eq :
      pts64x8At (sp + 0x870#64)
        (pack8LE c0 c1 c2 c3 c4 c5 c6 c7) (pack8LE c8 c9 c10 c11 c12 c13 c14 c15)
        (pack8LE c16 c17 c18 c19 c20 c21 c22 c23) (pack8LE c24 c25 c26 c27 c28 c29 c30 c31)
        (pack8LE c32 c33 c34 c35 c36 c37 c38 c39) (pack8LE c40 c41 c42 c43 c44 c45 c46 c47)
        (pack8LE c48 c49 c50 c51 c52 c53 c54 c55) (pack8LE c56 c57 c58 c59 c60 c61 c62 c63) =
        ((sp + 0x870#64) ↦ₛ blocks4Bytes bs_in) := by
    rw [pts64x8At_pack8LE_eq_pointsToBytes]; dsimp only [blocks4Bytes, bs_in]
    rw [hc0_eq, hc1_eq, hc2_eq, hc3_eq]; rfl
  let SrcAndSpills :=
    bytes16At src c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 ∗
    bytes16At (src + 16#64) c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 ∗
    bytes16At (src + 32#64) c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 ∗
    ((src + 48#64) ↦₆₄ pack8LE c48 c49 c50 c51 c52 c53 c54 c55) ∗
    ((src + 56#64) ↦₆₄ pack8LE c56 c57 c58 c59 c60 c61 c62 c63) ∗
    spill14At (sp + 0x03c#64)
      (c7.zeroExtend 32) (c6.zeroExtend 32) (c8.zeroExtend 32) (c9.zeroExtend 32)
      (c11.zeroExtend 32) (c10.zeroExtend 32) (c12.zeroExtend 32) (c13.zeroExtend 32)
      (c15.zeroExtend 32) (c14.zeroExtend 32) (c16.zeroExtend 32) (c17.zeroExtend 32)
      (c19.zeroExtend 32) (c18.zeroExtend 32) ∗
    spill14At (sp + 0x074#64)
      (c20.zeroExtend 32) (c21.zeroExtend 32) (c23.zeroExtend 32) (c22.zeroExtend 32)
      (c24.zeroExtend 32) (c25.zeroExtend 32) (c27.zeroExtend 32) (c26.zeroExtend 32)
      (c28.zeroExtend 32) (c29.zeroExtend 32) (c32.zeroExtend 32) (c31.zeroExtend 32)
      (c30.zeroExtend 32) (c33.zeroExtend 32) ∗
    spill14At (sp + 0x0ac#64)
      (c35.zeroExtend 32) (c34.zeroExtend 32) (c36.zeroExtend 32) (c37.zeroExtend 32)
      (c39.zeroExtend 32) (c38.zeroExtend 32) (c40.zeroExtend 32) (c41.zeroExtend 32)
      (c43.zeroExtend 32) (c42.zeroExtend 32) (c44.zeroExtend 32) (c45.zeroExtend 32)
      (c47.zeroExtend 32) (c46.zeroExtend 32) ∗
    pts64x8At dst z0 z1 z2 z3 z4 z5 z6 z7 ∗ TailRest
  let CallFrame := SrcAndSpills ∗ ((sp + 0xf00#64) ↦ₛ prev_bs) ∗ stackFrameAt (sp - 208#64) 3888
  refine sepWP_weaken_pre
    (P2 := (fsKeys256At (sp + 0xb40#64) ks ∗ ((sp + 0x870#64) ↦ₛ blocks4Bytes bs_in) ∗
            memRegion (sp + 0x4b0#64) 64 ∗ stackFrameAt sp 208) ∗ CallFrame)
    (by
      dsimp only [StableRest, CallFrame, SrcAndSpills]
      rw [hin_buf_eq, stackAt_allocHook_split208 sp]
      refine Entails.trans (Entails.of_eq (show _ =
          pts64x8At (sp + 0x4b0#64) o0 o1
            (pack8LE c16 c17 c18 c19 c20 c21 c22 c23) (pack8LE c24 c25 c26 c27 c28 c29 c30 c31)
            (pack8LE c32 c33 c34 c35 c36 c37 c38 c39) (pack8LE c40 c41 c42 c43 c44 c45 c46 c47)
            (pack8LE c48 c49 c50 c51 c52 c53 c54 c55) (pack8LE c56 c57 c58 c59 c60 c61 c62 c63) ∗ _ by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left (pts64x8At_entails_memRegion64 (sp + 0x4b0#64) _ _ _ _ _ _ _ _))
        (Entails.of_eq (by sep_ac_rfl))) ?_
  refine step_bl_decrypt (sp := sp) (outPtr := sp + 0x4b0#64) (keysPtr := sp + 0xb40#64)
    (inPtr := sp + 0x870#64) cs.bl_decQuad hCal.decrypt_ok hpc2 hrun2 hsp2
    (by simpa [State.spAligned, hsp2] using hspAl)
    (hx0_2.trans hx0_1) (hx1_2.trans hx1_1) hx8_2 hwf_in rfl
    fun s3 hpc3 hrun3 hsp3 hcs3 hpure3 => ?_
  have hpc3' : s3.pc = fnAddr + 0x7ec#64 := by simpa [BitVec.add_assoc] using hpc3
  have hx19_3 : s3.readReg64 .x19 = c1.zeroExtend 64 := hcs3.readReg64_x19.trans (hx19_2.trans hx19_1)
  have hx20_3 : s3.readReg64 .x20 = dst := hcs3.readReg64_x20.trans (hx20_2.trans (hx20_1.trans hx20))
  have hx21_3 : s3.readReg64 .x21 = c4.zeroExtend 64 := hcs3.readReg64_x21.trans (hx21_2.trans hx21_1)
  have hx22_3 : s3.readReg64 .x22 = c2.zeroExtend 64 := hcs3.readReg64_x22.trans (hx22_2.trans hx22_1)
  have hx23_3 : s3.readReg64 .x23 = c3.zeroExtend 64 := hcs3.readReg64_x23.trans (hx23_2.trans hx23_1)
  have hx24_3 : s3.readReg64 .x24 = sp + 0x4b0#64 := hcs3.readReg64_x24.trans (hx24_2.trans hx24_1)
  have hx25_3 : s3.readReg64 .x25 = c0.zeroExtend 64 := hcs3.readReg64_x25.trans (hx25_2.trans hx25_1)
  have hx26_3 : s3.readReg64 .x26 = src + 0x18#64 := hcs3.readReg64_x26.trans hx26_2
  have hx27_3 : s3.readReg64 .x27 = BitVec.ofNat 64 (x.input.length / 64 - q) :=
    hcs3.readReg64_x27.trans (hx27_2.trans (hx27_1.trans hx27))
  have hx28_3 : s3.readReg64 .x28 = c5.zeroExtend 64 := hcs3.readReg64_x28.trans (hx28_2.trans hx28_1)
  have hx29_3 : s3.readReg64 .x29 = s.readReg64 .x29 := hcs3.readReg64_x29.trans (hx29_2.trans hx29_1)
  have hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hcs3.vregs.trans (hv2.trans (hv1.trans hv))
  have hpure_s3 : PureStepPreserved s s3 := (hpure1.trans hpure2).trans hpure3
  let dec_bs := blocks4Bytes (aes256DecryptFs ks bs_in)
  have hdec_len : dec_bs.length = 64 := by
    have hc0_b := blockToBytesLE_bytesToBlock c0_bs hc0_len
    have hc1_b := blockToBytesLE_bytesToBlock c1_bs hc1_len
    have hc2_b := blockToBytesLE_bytesToBlock c2_bs hc2_len
    have hc3_b := blockToBytesLE_bytesToBlock c3_bs hc3_len
    dsimp only [dec_bs, bs_in, ks]
    rw [← hc0_b, ← hc1_b, ← hc2_b, ← hc3_b, blocks4Bytes_aes256DecryptFs_quad hkey32]
    simp [blockToBytesLE]
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15,
          d16,d17,d18,d19,d20,d21,d22,d23,d24,d25,d26,d27,d28,d29,d30,d31,
          d32,d33,d34,d35,d36,d37,d38,d39,d40,d41,d42,d43,d44,d45,d46,d47,
          d48,d49,d50,d51,d52,d53,d54,d55,d56,d57,d58,d59,d60,d61,d62,d63, hdec_eq⟩ := exists_bytes64 hdec_len
  have hout_buf_eq : ((sp + 0x4b0#64) ↦ₛ dec_bs) =
      pts64x8At (sp + 0x4b0#64)
        (pack8LE d0 d1 d2 d3 d4 d5 d6 d7) (pack8LE d8 d9 d10 d11 d12 d13 d14 d15)
        (pack8LE d16 d17 d18 d19 d20 d21 d22 d23) (pack8LE d24 d25 d26 d27 d28 d29 d30 d31)
        (pack8LE d32 d33 d34 d35 d36 d37 d38 d39) (pack8LE d40 d41 d42 d43 d44 d45 d46 d47)
        (pack8LE d48 d49 d50 d51 d52 d53 d54 d55) (pack8LE d56 d57 d58 d59 d60 d61 d62 d63) := by
    rw [hdec_eq, ← pts64x8At_pack8LE_eq_pointsToBytes]
  have hp_at : ((sp + 0xf00#64) ↦ₛ prev_bs) =
      bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 := by
    rw [hp_eq, pointsToBytes16_eq_bytes16At]
  let PostRest := fsKeys256At (sp + 0xb40#64) ks ∗ SrcAndSpills ∗ stackAt sp allocHookStack
  refine sepWP_weaken_pre (Entails.of_eq (by
      dsimp only [CallFrame, PostRest]
      rw [← hin_buf_eq, stackAt_allocHook_split208 sp, hp_at]
      change (fsKeys256At (sp + 0xb40#64) ks ∗ pts64x8At (sp + 0x870#64) _ _ _ _ _ _ _ _ ∗
              ((sp + 0x4b0#64) ↦ₛ dec_bs) ∗ _) ∗ _ = _
      rw [hout_buf_eq]; sep_ac_rfl))
    (cbc_quad_post1a cs.softQuadPost1a
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31
      d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47 d48 d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62 d63
      p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 _ _ _ _ _ _ _ _ PostRest
      s3 hpc3' hrun3 hsp3 hspAl hx24_3
      fun s4 hpc4 hrun4 hsp4 hx8_4 hx9_4 hx10_4 hx11_4 hx12_4 hx13_4 hx14_4
          hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
          hpz4 hv4 hpure4 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (cbc_quad_post1b cs.softQuadPost1b
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31
      p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 c0 _
      s4 hpc4 hrun4 hsp4 hspAl hx8_4 hx9_4 hx10_4 hx11_4 hx12_4 hx13_4 hx14_4 (hx25_4.trans hx25_3)
      fun s5 hpc5 hrun5 hsp5 hx8_5 hx9_5 hx11_5
          hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 _ hx26_5 hx27_5 hx28_5 hx29_5
          hp5 hv5 hpure5 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (cbc_quad_post2 cs.softQuadPost2
      d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 _
      s5 hpc5 hrun5 hsp5 hspAl hx8_5 hx9_5 hx11_5
      (hx19_5.trans (hx19_4.trans hx19_3)) (hx21_5.trans (hx21_4.trans hx21_3))
      (hx22_5.trans (hx22_4.trans hx22_3)) (hx23_5.trans (hx23_4.trans hx23_3))
      (hx28_5.trans (hx28_4.trans hx28_3))
      fun s6 hpc6 hrun6 hsp6 hx8_6 hx9_6 hx11_6 hx12_6
          hx20_6 hx22_6 hx24_6 hx26_6 hx27_6 hx29_6 hp6 hv6 hpure6 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (cbc_quad_post3 cs.softQuadPost3
      d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47 d48 d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62 d63
      c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 _
      s6 hpc6 hrun6 hsp6 hspAl hx8_6 hx9_6 hx11_6 hx12_6
      fun s7 hpc7 hrun7 hsp7 hx8_7 hx9_7 hx11_7
          hx20_7 hx22_7 hx24_7 hx26_7 hx27_7 hx29_7 hp7 hv7 hpure7 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (cbc_quad_post4 cs.softQuadPost4
      d0 (d1 ^^^ p1) (d2 ^^^ p2) (d3 ^^^ p3) (d4 ^^^ p4) (d5 ^^^ p5)
      (d6 ^^^ p6) (d7 ^^^ p7) (d8 ^^^ p8) (d9 ^^^ p9) (d10 ^^^ p10) (d11 ^^^ p11)
      (d12 ^^^ p12) (d13 ^^^ p13) (d14 ^^^ p14) (d15 ^^^ p15)
      d48 d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62 d63
      p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
      c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 _
      s7 hpc7 hrun7 hsp7 hspAl hx8_7 hx9_7 hx11_7
      fun s8 hpc8 hrun8 hsp8 hx8_8
          hx20_8 hx22_8 hx24_8 hx26_8 hx27_8 hx29_8 hp8 hv8 hpure8 => ?_)
  let rem1 := BitVec.ofNat 64 (x.input.length / 64 - (q + 1))
  have hrem1_eq : s3.readReg64 .x27 - 1#64 = rem1 := by
    rw [hx27_3, bv64_ofNat_sub_one (by omega) (by omega),
        show x.input.length / 64 - q - 1 = x.input.length / 64 - (q + 1) from by omega]
  have hx20_8' : s8.readReg64 .x20 = dst :=
    hx20_8.trans (hx20_7.trans (hx20_6.trans (hx20_5.trans (hx20_4.trans hx20_3))))
  have hx22_8' : s8.readReg64 .x22 = sp + 0xb40#64 := hx22_8.trans (hx22_7.trans hx22_6)
  have hx24_8' : s8.readReg64 .x24 = sp + 0x4b0#64 :=
    hx24_8.trans (hx24_7.trans (hx24_6.trans (hx24_5.trans hx24_4)))
  have hx26_8' : s8.readReg64 .x26 = src + 0x18#64 :=
    hx26_8.trans (hx26_7.trans (hx26_6.trans (hx26_5.trans (hx26_4.trans hx26_3))))
  have hx27_8' : s8.readReg64 .x27 = rem1 :=
    hx27_8.trans (hx27_7.trans (hx27_6.trans (hx27_5.trans (hx27_4.trans hrem1_eq))))
  have hx29_8' : s8.readReg64 .x29 = s.readReg64 .x29 :=
    hx29_8.trans (hx29_7.trans (hx29_6.trans (hx29_5.trans (hx29_4.trans hx29_3))))
  have hpz8 : s8.pstate.z = (rem1 == 0#64) := by rw [hp8, hp7, hp6, hp5, hpz4, hrem1_eq]
  refine sepWP_weaken_pre (Entails.of_eq (by
      try dsimp only [PostRest, SrcAndSpills]
      rw [← pts64_pair_eq_bytes16At (sp + 0x880#64), ← pts64_pair_eq_bytes16At (sp + 0x890#64),
          ← pts64_pair_eq_bytes16At (sp + 0x8a0#64), ← pts64_pair_eq_bytes16At (sp + 0xf00#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl))
    (cbc_quad_post5 cs.softQuadPost5
      (pack8LE (d16 ^^^ c0) (d17 ^^^ c1) (d18 ^^^ c2) (d19 ^^^ c3) (d20 ^^^ c4) (d21 ^^^ c5) (d22 ^^^ c6) (d23 ^^^ c7))
      (pack8LE (d24 ^^^ c8) (d25 ^^^ c9) (d26 ^^^ c10) (d27 ^^^ c11) (d28 ^^^ c12) (d29 ^^^ c13) (d30 ^^^ c14) (d31 ^^^ c15))
      (pack8LE (d32 ^^^ c16) (d33 ^^^ c17) (d34 ^^^ c18) (d35 ^^^ c19) (d36 ^^^ c20) (d37 ^^^ c21) (d38 ^^^ c22) (d39 ^^^ c23))
      (pack8LE (d40 ^^^ c24) (d41 ^^^ c25) (d42 ^^^ c26) (d43 ^^^ c27) (d44 ^^^ c28) (d45 ^^^ c29) (d46 ^^^ c30) (d47 ^^^ c31))
      (pack8LE (d48 ^^^ c32) (d49 ^^^ c33) (d50 ^^^ c34) (d51 ^^^ c35) (d52 ^^^ c36) (d53 ^^^ c37) (d54 ^^^ c38) (d55 ^^^ c39))
      (pack8LE (d56 ^^^ c40) (d57 ^^^ c41) (d58 ^^^ c42) (d59 ^^^ c43) (d60 ^^^ c44) (d61 ^^^ c45) (d62 ^^^ c46) (d63 ^^^ c47))
      (pack8LE c48 c49 c50 c51 c52 c53 c54 c55) (pack8LE c56 c57 c58 c59 c60 c61 c62 c63)
      (pack8LE p0 p1 p2 p3 p4 p5 p6 p7) (pack8LE p8 p9 p10 p11 p12 p13 p14 p15)
      z0 z1 z2 z3 z4 z5 z6 z7
      d0 (d0 ^^^ p0) (d1 ^^^ p1) (d2 ^^^ p2) (d3 ^^^ p3) (d4 ^^^ p4) (d5 ^^^ p5)
      (d6 ^^^ p6) (d7 ^^^ p7) (d8 ^^^ p8) (d9 ^^^ p9) (d10 ^^^ p10) (d11 ^^^ p11)
      (d12 ^^^ p12) (d13 ^^^ p13) (d14 ^^^ p14) (d15 ^^^ p15) _
      s8 hpc8 hrun8 hsp8 hspAl hx8_8 hx20_8' hx22_8' hx24_8' hx26_8' hx27_8' hpz8
      fun sf hpc_f hrun_f hsp_f hx20_f hx22_f hx24_f hx26_f hx27_f hx29_f hv_f hpure_f => ?_)
  have hpc_f' : sf.pc = (if q + 1 = x.input.length / 64 then fnAddr + 0xbc0#64 else fnAddr + 0x694#64) := by
    rw [hpc_f]
    have hrem_zero : (rem1 == 0#64) = decide (q + 1 = x.input.length / 64) := by
      dsimp only [rem1]; rw [bv64_ofNat_beq_zero (by omega)]; exact decide_eq_decide.mpr (by omega)
    rw [hrem_zero]; by_cases hq1 : q + 1 = x.input.length / 64 <;> simp [hq1]
  have hx20_f' : sf.readReg64 .x20 = outBuf + BitVec.ofNat 64 (64 * (q + 1)) := by
    rw [hx20_f]; exact bv64_add_ofNat_64 outBuf (by omega)
  have hx26_f' : sf.readReg64 .x26 = x.inA + BitVec.ofNat 64 (64 * (q + 1)) + 0x18#64 := by
    rw [hx26_f]; dsimp only [src]; rw [← bv64_add_ofNat_64 x.inA (by omega)]
  have hv_f' : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
    hv_f.trans (hv8.trans (hv7.trans (hv6.trans (hv5.trans (hv4.trans hv3)))))
  have hpure_all : PureStepPreserved s sf :=
    hpure_s3.trans (hpure4.trans (hpure5.trans (hpure6.trans (hpure7.trans (hpure8.trans hpure_f)))))
  have hzip_eq :
      [d0 ^^^ p0, d1 ^^^ p1, d2 ^^^ p2, d3 ^^^ p3, d4 ^^^ p4, d5 ^^^ p5, d6 ^^^ p6, d7 ^^^ p7,
       d8 ^^^ p8, d9 ^^^ p9, d10 ^^^ p10, d11 ^^^ p11, d12 ^^^ p12, d13 ^^^ p13, d14 ^^^ p14, d15 ^^^ p15,
       d16 ^^^ c0, d17 ^^^ c1, d18 ^^^ c2, d19 ^^^ c3, d20 ^^^ c4, d21 ^^^ c5, d22 ^^^ c6, d23 ^^^ c7,
       d24 ^^^ c8, d25 ^^^ c9, d26 ^^^ c10, d27 ^^^ c11, d28 ^^^ c12, d29 ^^^ c13, d30 ^^^ c14, d31 ^^^ c15,
       d32 ^^^ c16, d33 ^^^ c17, d34 ^^^ c18, d35 ^^^ c19, d36 ^^^ c20, d37 ^^^ c21, d38 ^^^ c22, d39 ^^^ c23,
       d40 ^^^ c24, d41 ^^^ c25, d42 ^^^ c26, d43 ^^^ c27, d44 ^^^ c28, d45 ^^^ c29, d46 ^^^ c30, d47 ^^^ c31,
       d48 ^^^ c32, d49 ^^^ c33, d50 ^^^ c34, d51 ^^^ c35, d52 ^^^ c36, d53 ^^^ c37, d54 ^^^ c38, d55 ^^^ c39,
       d56 ^^^ c40, d57 ^^^ c41, d58 ^^^ c42, d59 ^^^ c43, d60 ^^^ c44, d61 ^^^ c45, d62 ^^^ c46, d63 ^^^ c47] =
        List.zipWith (· ^^^ ·) dec_bs (prev_bs ++ c0_bs ++ c1_bs ++ c2_bs) := by
    rw [hdec_eq, hp_eq, hc0_eq, hc1_eq, hc2_eq]; rfl
  have hstep4 :
      cbcPrefixBytes x.key x.iv x.input (4 * q) ++
        List.zipWith (· ^^^ ·) dec_bs (prev_bs ++ c0_bs ++ c1_bs ++ c2_bs) =
        cbcPrefixBytes x.key x.iv x.input (4 * (q + 1)) := by
    rw [show 4 * (q + 1) = 4 * q + 4 from by omega]; exact cbcPrefixBytes_step4 hkey32 hiv16 hm4
  let z_bs := List.zipWith (· ^^^ ·) dec_bs (prev_bs ++ c0_bs ++ c1_bs ++ c2_bs)
  have hout_recombine :
      ((outBuf ↦ₛ cbcPrefixBytes x.key x.iv x.input (4 * q)) ∗ (dst ↦ₛ z_bs) ∗
       ((outBuf + BitVec.ofNat 64 (64 * (q + 1))) ↦ₛ List.replicate (x.input.length - 64 * (q + 1)) 0#8)) =
        (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input (4 * (q + 1)) ++
          List.replicate (x.input.length - 64 * (q + 1)) 0#8)) := by
    have hz_len : z_bs.length = 64 := by dsimp only [z_bs]; rw [← hzip_eq]; rfl
    have hrhs : cbcPrefixBytes x.key x.iv x.input (4 * (q + 1)) ++
        List.replicate (x.input.length - 64 * (q + 1)) 0#8 =
        cbcPrefixBytes x.key x.iv x.input (4 * q) ++
          (z_bs ++ List.replicate (x.input.length - 64 * (q + 1)) 0#8) := by
      dsimp only [z_bs]; rw [← hstep4, List.append_assoc]
    rw [hrhs, pointsToBytes_append, hpre_len, pointsToBytes_append, hz_len]
    dsimp only [dst]; rw [bv64_add_ofNat_64 outBuf (by omega)]
  have hchain_next :
      [c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63] =
        cbcChainAt x.iv x.input (4 * (q + 1)) := by
    rw [← hc3_eq, show 4 * (q + 1) = (4 * q + 3) + 1 from by omega, cbcChainAt_succ]
  have hin_recombine :
      ((x.inA ↦ₛ x.input.take (64 * q)) ∗
       bytes16At src c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 ∗
       bytes16At (src + 16#64) c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 ∗
       bytes16At (src + 32#64) c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 ∗
       ((src + 48#64) ↦₆₄ pack8LE c48 c49 c50 c51 c52 c53 c54 c55) ∗
       ((src + 56#64) ↦₆₄ pack8LE c56 c57 c58 c59 c60 c61 c62 c63) ∗
       ((x.inA + BitVec.ofNat 64 (64 * (q + 1))) ↦ₛ x.input.drop (64 * (q + 1)))) =
        (x.inA ↦ₛ x.input) := by
    have hc1_at : ((src + 16#64) ↦ₛ c1_bs) =
        bytes16At (src + 16#64) c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 := by
      rw [hc1_eq, pointsToBytes16_eq_bytes16At]
    have hc2_at : ((src + 32#64) ↦ₛ c2_bs) =
        bytes16At (src + 32#64) c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 := by
      rw [hc2_eq, pointsToBytes16_eq_bytes16At]
    rw [← hc0_at, ← hc1_at, ← hc2_at, hin_split, hc3_p]; sep_ac_rfl
  have hp_next_eq :
      ((sp + 0xf00#64) ↦₆₄ pack8LE c48 c49 c50 c51 c52 c53 c54 c55) ∗
      ((sp + 0xf08#64) ↦₆₄ pack8LE c56 c57 c58 c59 c60 c61 c62 c63) =
        ((sp + 0xf00#64) ↦ₛ cbcChainAt x.iv x.input (4 * (q + 1))) := by
    rw [← hchain_next, pointsToBytes16_eq_pts64_pair (sp + 0xf00#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine sepWP_weaken_pre ?_
    (hnext sf hpc_f' hrun_f hsp_f hx20_f' hx22_f hx24_f hx26_f' hx27_f
      (hx29_f.trans hx29_8') hv_f' hpure_all)
  rw [pts64x8At_pack8LE_eq_pointsToBytes dst, hzip_eq]
  change ((dst ↦ₛ z_bs) ∗ _) ⊢ _
  dsimp only [cbcSoftWork, ks, TailRest]
  rw [h168_split]
  refine Entails.trans (Entails.of_eq (show _ =
      (spill14At (sp + 0x03c#64) _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∗
       spill14At (sp + 0x074#64) _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∗
       spill14At (sp + 0x0ac#64) _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∗
       pts64x8At (sp + 0x4b0#64) _ _ _ _ _ _ _ _ ∗
       pts64x8At (sp + 0x870#64) _ _ _ _ _ _ _ _) ∗
      (((outBuf ↦ₛ cbcPrefixBytes x.key x.iv x.input (4 * q)) ∗ (dst ↦ₛ z_bs) ∗
        ((outBuf + BitVec.ofNat 64 (64 * (q + 1))) ↦ₛ List.replicate (x.input.length - 64 * (q + 1)) 0#8)) ∗
       ((x.inA ↦ₛ x.input.take (64 * q)) ∗
        bytes16At src c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 ∗
        bytes16At (src + 16#64) c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 ∗
        bytes16At (src + 32#64) c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 ∗
        ((src + 48#64) ↦₆₄ pack8LE c48 c49 c50 c51 c52 c53 c54 c55) ∗
        ((src + 56#64) ↦₆₄ pack8LE c56 c57 c58 c59 c60 c61 c62 c63) ∗
        ((x.inA + BitVec.ofNat 64 (64 * (q + 1))) ↦ₛ x.input.drop (64 * (q + 1)))) ∗
       (((sp + 0xf00#64) ↦₆₄ pack8LE c48 c49 c50 c51 c52 c53 c54 c55) ∗
        ((sp + 0xf08#64) ↦₆₄ pack8LE c56 c57 c58 c59 c60 c61 c62 c63)) ∗
       fsKeys256At (sp + 0xb40#64) ks ∗ stackAt sp allocHookStack ∗ Other) by
      simp only [src, dst, BitVec.add_assoc]; sep_ac_rfl)) ?_
  rw [hout_recombine, hin_recombine, hp_next_eq]
  refine Entails.trans
    (sepConj_mono_left
      (sepConj_mono (spill14At_entails_memRegion56 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (sepConj_mono (spill14At_entails_memRegion56 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
          (sepConj_mono (spill14At_entails_memRegion56 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
            (sepConj_mono (pts64x8At_entails_memRegion64 _ _ _ _ _ _ _ _ _)
              (pts64x8At_entails_memRegion64 _ _ _ _ _ _ _ _ _)))))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadIter

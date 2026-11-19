/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import ProofLib.SepLogic.WP
public import ProofLib.StdStartup.MemOps
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDec
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopAux
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.Lemmas
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers

/-! # 1-Block Remainder ARMv8 Hardware CBC Decryption Loop (`CbcDec.HwLoopRem`) -/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopRem

open Arm64 ProofLib SepProp
open ProofLib.StdStartup (decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (PureStepPreserved)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (bytesToU128LE u128ToBytesLE armv8ExpandKey armv8InvExpandedKeys armv8Decrypt15 roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDec (decrypt15InplaceSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Aux
  (u128ToBytesLE_length pointsTo128_eq_pointsToBytes_u128ToBytesLE
   u128ToBytesLE_bytesToU128LE step_ldr128 step_str128_perm)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopAux
  (lsl4_ofNat cbcChainAt cbcChainAt_succ cbcChainAt_length cbcPrefixBytes cbcPrefixBytes_length
   cbcPrefixBytes_step1 bytes16At pointsToBytes16_eq_bytes16At exists_bytes16
   sepWP_weaken_pre sepWP_checkpoint cs_trans step_ldr128_post step_str128_post_perm step_bl_decrypt15)

attribute [local irreducible]
  bytesToU128LE u128ToBytesLE armv8ExpandKey armv8InvExpandedKeys armv8Decrypt15 cbcPrefixBytes

public section

@[expose] def hwRemSetupWords : List (BitVec 32) := [
  0xf100429f#32, 0x54004948#32, 0xa9415ffa#32, 0x912d03f9#32, 0xf94073e8#32, 0xeb08035f#32,
  0x540043c0#32, 0xa942abe9#32, 0xd37ced08#32, 0x92800016#32, 0x8b080153#32, 0x8b080135#32]
@[expose] def hwRemPreDecWords : List (BitVec 32) := [
  0xb4004976#32, 0x3dc00260#32, 0x9103c320#32, 0x912943e1#32, 0x912943e2#32, 0x3d816b00#32]
@[expose] def hwRemPostWords : List (BitVec 32) := [
  0x397c03e8#32, 0x396943e9#32, 0xd1000694#32, 0x397c07ea#32, 0x396947eb#32, 0xd10006d6#32, 0x397c0bec#32, 0x39694bed#32,
  0x4a080128#32, 0x4a0a0169#32, 0x392943e8#32, 0x397c0fe8#32, 0x392947e9#32, 0x39694fe9#32, 0x4a0c01aa#32, 0x39294bea#32,
  0x396953ea#32, 0x397c2feb#32, 0x4a080128#32, 0x397c13e9#32, 0x39696fec#32, 0x39294fe8#32, 0x397c33ed#32, 0x396973ee#32,
  0x4a090148#32, 0x397c17e9#32, 0x396957ea#32, 0x392953e8#32, 0x397c37ef#32, 0x396977f0#32, 0x4a090148#32, 0x397c1be9#32,
  0x39695bea#32, 0x392957e8#32, 0x3cc10661#32, 0x4a090148#32, 0x397c1fe9#32, 0x39695fea#32, 0x39295be8#32, 0x4a090148#32,
  0x397c23e9#32, 0x396963ea#32, 0x39295fe8#32, 0x4a090148#32, 0x397c27e9#32, 0x396967ea#32, 0x392963e8#32, 0x4a090148#32,
  0x397c2be9#32, 0x39696bea#32, 0x392967e8#32, 0x4a0d01c8#32, 0x4a090149#32, 0x4a0b018a#32, 0x392973e8#32, 0x39296be9#32,
  0x397c3be9#32, 0x397c3fe8#32, 0x39296fea#32, 0x39697bea#32, 0x39697fec#32, 0x4a0f020b#32, 0x3d80f321#32, 0x4a090149#32,
  0x4a080188#32, 0x392977eb#32, 0x39297be9#32, 0x39297fe8#32, 0x3dc16b00#32, 0x3c8106a0#32, 0xb5fff674#32]
@[expose] def hwRemExitWords : List (BitVec 32) := [0x140001ca#32]

structure RemLoopSegs (P : Program) (fnAddr hwDecryptAddr : BitVec 64) : Prop where
  setup  : hasInstrs P (fnAddr + 0x490#64) (decodeWords hwRemSetupWords)
  preDec : hasInstrs P (fnAddr + 0x4c0#64) (decodeWords hwRemPreDecWords)
  blDec  : hasInstrs P (fnAddr + 0x4d8#64) [.bl (hwDecryptAddr - (fnAddr + 0x4d8#64))]
  post   : hasInstrs P (fnAddr + 0x4dc#64) (decodeWords hwRemPostWords)
  exit   : hasInstrs P (fnAddr + 0x5f8#64) (decodeWords hwRemExitWords)

local macro "close_cs_pure" : tactic =>
  `(tactic| refine ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm], by simp [calleeSavedVRegs, wp_norm, arm64_norm]⟩)

private theorem sepWP_mem128_elim {P : Program} {pc p : BitVec 64} {Rest : SepProp} {s : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hk : ∀ v : BitVec 128, SepWP P pc s ((p ↦₁₂₈ v) ∗ Rest) post oom) :
    SepWP P pc s (memRegion p 16 ∗ Rest) post oom := by
  rw [memRegion_eq_exists_bytes p 16 (by decide), sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hbs => ?_
  have hp128 : (p ↦ₛ bs) = (p ↦₁₂₈ bytesToU128LE bs) := by
    rw [pointsTo128_eq_pointsToBytes_u128ToBytesLE, u128ToBytesLE_bytesToU128LE hbs]
  rw [hp128]; exact hk (bytesToU128LE bs)

set_option maxHeartbeats 500000 in
private theorem step_rem_post {P : Program}
    {fnAddr target_pc sp srcPtr dstPtr x20Val x22Val : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x4dc#64) (decodeWords hwRemPostWords))
    (decBs prevBs c0 : List (BitVec 8)) (oldDst : BitVec 128) (Rest : SepProp) (s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hdec : decBs.length = 16) (hprev : prevBs.length = 16) (hc0 : c0.length = 16)
    (hpc : s.pc = fnAddr + 0x4dc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = srcPtr) (hx20 : s.readReg64 .x20 = x20Val)
    (hx21 : s.readReg64 .x21 = dstPtr) (hx22 : s.readReg64 .x22 = x22Val)
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64) (hx25 : s.readReg64 .x25 = sp + 0xb40#64)
    (hnext : ∀ sf : State,
      sf.pc = (if x20Val - 1#64 != 0#64 then fnAddr + 0x4c0#64 else fnAddr + 0x5f8#64) →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = srcPtr + 16#64 → sf.readReg64 .x20 = x20Val - 1#64 →
      sf.readReg64 .x21 = dstPtr + 16#64 → sf.readReg64 .x22 = x22Val - 1#64 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x25 = sp + 0xb40#64 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = s.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        ((dstPtr ↦ₛ List.zipWith (· ^^^ ·) decBs prevBs) ∗
         (srcPtr ↦₁₂₈ bytesToU128LE c0) ∗
         ((sp + 0xa50#64) ↦ₛ List.zipWith (· ^^^ ·) decBs prevBs) ∗
         ((sp + 0xf00#64) ↦ₛ c0) ∗ Rest) post oom) :
    SepWP P target_pc s
      ((dstPtr ↦₁₂₈ oldDst) ∗ (srcPtr ↦₁₂₈ bytesToU128LE c0) ∗
       ((sp + 0xa50#64) ↦ₛ decBs) ∗ ((sp + 0xf00#64) ↦ₛ prevBs) ∗ Rest) post oom := by
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, hd_eq⟩ := exists_bytes16 hdec
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, hp_eq⟩ := exists_bytes16 hprev
  have hd_at : ((sp + 0xa50#64) ↦ₛ decBs) = bytes16At (sp + 0xa50#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 := by
    rw [hd_eq, pointsToBytes16_eq_bytes16At]
  have hp_at : ((sp + 0xf00#64) ↦ₛ prevBs) = bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 := by
    rw [hp_eq, pointsToBytes16_eq_bytes16At]
  have hp_128 : bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 =
      ((sp + 0xf00#64) ↦₁₂₈ bytesToU128LE prevBs) := by
    rw [← hp_at, pointsTo128_eq_pointsToBytes_u128ToBytesLE, u128ToBytesLE_bytesToU128LE hprev]
  let ptBs := List.zipWith (· ^^^ ·) decBs prevBs
  have hpt_len : ptBs.length = 16 := by dsimp [ptBs]; rw [List.length_zipWith, hdec, hprev]; rfl
  have hpt_at : bytes16At (sp + 0xa50#64) (d0 ^^^ p0) (d1 ^^^ p1) (d2 ^^^ p2) (d3 ^^^ p3) (d4 ^^^ p4)
      (d5 ^^^ p5) (d6 ^^^ p6) (d7 ^^^ p7) (d8 ^^^ p8) (d9 ^^^ p9) (d10 ^^^ p10)
      (d11 ^^^ p11) (d12 ^^^ p12) (d13 ^^^ p13) (d14 ^^^ p14) (d15 ^^^ p15) =
      ((sp + 0xa50#64) ↦₁₂₈ bytesToU128LE ptBs) := by
    rw [← pointsToBytes16_eq_bytes16At, pointsTo128_eq_pointsToBytes_u128ToBytesLE,
        u128ToBytesLE_bytesToU128LE hpt_len]
    dsimp [ptBs]; rw [hd_eq, hp_eq]; rfl
  refine sepWP_weaken_pre (Entails.of_eq (show _ =
      (dstPtr ↦₁₂₈ oldDst) ∗ (srcPtr ↦₁₂₈ bytesToU128LE c0) ∗
      bytes16At (sp + 0xa50#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
      bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗ Rest by
      rw [hd_at, hp_at])) ?_
  have_instrs hc 0 71
  dsimp only [bytes16At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 10; wp_str8 hf_10 m1 hm1; wp_step; wp_str8 hf_12 m2 hm2
  wp_steps 2; wp_str8 hf_15 m3 hm3; wp_steps 5; wp_str8 hf_21 m4 hm4
  wp_steps 5; wp_str8 hf_27 m5 hm5; wp_steps 5; wp_str8 hf_33 m6 hm6
  refine sepWP_checkpoint (φ := fun sM =>
      sM.pc = fnAddr + 0x564#64 ∧ sM.status = .Running ∧ sM.sp = sp ∧
      sM.readReg64 .x9 = p6.zeroExtend 64 ∧ sM.readReg64 .x10 = d6.zeroExtend 64 ∧
      sM.readReg64 .x11 = p11.zeroExtend 64 ∧ sM.readReg64 .x12 = d11.zeroExtend 64 ∧
      sM.readReg64 .x13 = p12.zeroExtend 64 ∧ sM.readReg64 .x14 = d12.zeroExtend 64 ∧
      sM.readReg64 .x15 = p13.zeroExtend 64 ∧ sM.readReg64 (.gpr 16#5) = d13.zeroExtend 64 ∧
      sM.readReg64 .x19 = srcPtr ∧ sM.readReg64 .x20 = x20Val - 1#64 ∧
      sM.readReg64 .x21 = dstPtr ∧ sM.readReg64 .x22 = x22Val - 1#64 ∧
      sM.readReg64 .x23 = s.readReg64 .x23 ∧ sM.readReg64 .x24 = sp + 0x4b0#64 ∧
      sM.readReg64 .x25 = sp + 0xb40#64 ∧ sM.readReg64 .x26 = s.readReg64 .x26 ∧
      sM.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sM = calleeSavedVRegs s ∧
      PureStepPreserved s sM)
    ⟨by simp [wp_norm, arm64_norm]; try bv_lin, by simp [wp_norm, arm64_norm, hrun],
     by simp [wp_norm, arm64_norm, hsp], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hx19],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hx21],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm, hx24], by simp [wp_norm, arm64_norm, hx25],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [calleeSavedVRegs, wp_norm, arm64_norm],
     PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
       (by simp [wp_norm, arm64_norm, hm6, hm5, hm4, hm3, hm2, hm1])⟩
    fun sM ⟨hpcM, hrunM, hspM, hx9M, hx10M, hx11M, hx12M, hx13M, hx14M, hx15M, hx16M,
            hx19M, hx20M, hx21M, hx22M, hx23M, hx24M, hx25M, hx26M, hx29M, hvM, hpureM⟩ => ?_
  clear m1 hm1 m2 hm2 m3 hm3 m4 hm4 m5 hm5 m6 hm6
  refine step_ldr128_post hf_34 hpcM hrunM hx19M (by rw [sepConj_left_comm]) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 3; wp_str8 hf_38 m7 hm7; wp_steps 3; wp_str8 hf_42 m8 hm8
  wp_steps 3; wp_str8 hf_46 m9 hm9; wp_steps 3; wp_str8 hf_50 m10 hm10
  wp_steps 3; wp_str8 hf_54 m11 hm11; wp_str8 hf_55 m12 hm12
  wp_steps 2; wp_str8 hf_58 m13 hm13; wp_steps 3
  refine sepWP_weaken_pre (Entails.of_eq (by
      have hp' := hp_128; dsimp only [bytes16At] at hp'; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp'
      rw [show ∀ (A B C D E : SepProp), A ∗ (B ∗ C ∗ D ∗ E) = D ∗ (A ∗ B ∗ C ∗ E) by intros; sep_ac_rfl, hp'])) ?_
  refine step_str128_perm hf_62 (ea := sp + 0xf00#64) (old := bytesToU128LE prevBs) (val := bytesToU128LE c0)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrunM])
    (by have h25 : sM.readReg64 (.gpr 25#5) = sp + 0xb40#64 := hx25M
        simp [wp_norm, arm64_norm, h25]; try bv_lin)
    (by simp [wp_norm, arm64_norm]) rfl fun m14 hm14 => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 2; wp_str8 hf_65 m15 hm15; wp_str8 hf_66 m16 hm16; wp_str8 hf_67 m17 hm17
  refine sepWP_weaken_pre (Entails.of_eq (show _ =
      ((sp + 0xa50#64) ↦₁₂₈ bytesToU128LE ptBs) ∗
      ((dstPtr ↦₁₂₈ oldDst) ∗ ((srcPtr ↦₁₂₈ bytesToU128LE c0) ∗
       ((sp + 0xf00#64) ↦₁₂₈ bytesToU128LE c0) ∗ Rest)) by
      rw [← hpt_at]; dsimp only [bytes16At]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl)) ?_
  refine step_ldr128 hf_68 (ea := sp + 0xa50#64) (v := bytesToU128LE ptBs)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrunM])
    (by have h24 : sM.readReg64 (.gpr 24#5) = sp + 0x4b0#64 := hx24M
        simp [wp_norm, arm64_norm, h24]; try bv_lin)
    rfl ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine step_str128_post_perm hf_69 (ea := dstPtr) (old := oldDst) (val := bytesToU128LE ptBs)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrunM])
    (by have h21 : sM.readReg64 (.gpr 21#5) = dstPtr := hx21M; simp [wp_norm, arm64_norm, h21])
    (by simp [wp_norm, arm64_norm]) (by rw [sepConj_left_comm]) fun m18 hm18 => ?_
  have hfin_spatial :
      ((dstPtr ↦₁₂₈ bytesToU128LE ptBs) ∗
       (((sp + 0xa50#64) ↦₁₂₈ bytesToU128LE ptBs) ∗
        ((srcPtr ↦₁₂₈ bytesToU128LE c0) ∗ ((sp + 0xf00#64) ↦₁₂₈ bytesToU128LE c0) ∗ Rest))) =
      ((dstPtr ↦ₛ ptBs) ∗ (srcPtr ↦₁₂₈ bytesToU128LE c0) ∗
       ((sp + 0xa50#64) ↦ₛ ptBs) ∗ ((sp + 0xf00#64) ↦ₛ c0) ∗ Rest) := by
    rw [pointsTo128_eq_pointsToBytes_u128ToBytesLE dstPtr,
        pointsTo128_eq_pointsToBytes_u128ToBytesLE (sp + 0xa50#64),
        pointsTo128_eq_pointsToBytes_u128ToBytesLE (sp + 0xf00#64),
        u128ToBytesLE_bytesToU128LE hpt_len, u128ToBytesLE_bytesToU128LE hc0]
    sep_ac_rfl
  refine sepWP_weaken_pre (Entails.of_eq hfin_spatial) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_step; wp_if hcbnz
  · have hcond : (x20Val - 1#64 != 0#64) = true := by
      rw [bne_iff_ne]; simpa [beq_iff_eq, bne_iff_ne, Classical.not_not, wp_norm, arm64_norm, hx20M] using hcbnz
    exact hnext _ (by simp [wp_norm, arm64_norm, hcond]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrunM]) (by simp [wp_norm, arm64_norm, hspM])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx20M])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx22M])
      (by simp [wp_norm, arm64_norm, hx23M]) (by simp [wp_norm, arm64_norm, hx24M])
      (by simp [wp_norm, arm64_norm, hx25M]) (by simp [wp_norm, arm64_norm, hx26M])
      (by simp [wp_norm, arm64_norm, hx29M])
      (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hvM)
      (hpureM.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm18, hm17, hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7])))
  · have hcond : (x20Val - 1#64 != 0#64) = false := by
      rw [bne_eq_false_iff_eq]; simpa [beq_iff_eq, bne_iff_ne, Classical.not_not, wp_norm, arm64_norm, hx20M] using hcbnz
    exact hnext _ (by simp [wp_norm, arm64_norm, hcond]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrunM]) (by simp [wp_norm, arm64_norm, hspM])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx20M])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx22M])
      (by simp [wp_norm, arm64_norm, hx23M]) (by simp [wp_norm, arm64_norm, hx24M])
      (by simp [wp_norm, arm64_norm, hx25M]) (by simp [wp_norm, arm64_norm, hx26M])
      (by simp [wp_norm, arm64_norm, hx29M])
      (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hvM)
      (hpureM.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm18, hm17, hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7])))

private theorem step_rem_loop_from {P : Program}
    {fnAddr hwDecryptAddr target_pc sp outBuf inA : BitVec 64}
    (cs : RemLoopSegs P fnAddr hwDecryptAddr)
    (hDec1 : subroutine_ok P hwDecryptAddr decrypt15InplaceSpec)
    (key iv ct : List (BitVec 8)) (Rest : SepProp)
    (rem m idx : Nat) (hrem : rem = ct.length / 16 - m)
    (hm_lt : m < ct.length / 16) (hidx_lt : idx + rem ≤ 16)
    (hkey : key.length = 32) (hiv : iv.length = 16)
    (hct_mod : ct.length % 16 = 0) (hct_lt : ct.length < 2 ^ 40)
    (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x4c0#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 (.gpr 19#5) = inA + BitVec.ofNat 64 (16 * m))
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 rem)
    (hx21 : s.readReg64 (.gpr 21#5) = outBuf + BitVec.ofNat 64 (16 * m))
    (hx22 : s.readReg64 (.gpr 22#5) = 0xffffffffffffffff#64 - BitVec.ofNat 64 idx)
    (hx24 : s.readReg64 (.gpr 24#5) = sp + 0x4b0#64)
    (hx25 : s.readReg64 (.gpr 25#5) = sp + 0xb40#64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0xd20#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = s.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        ((outBuf ↦ₛ cbcPrefixBytes key iv ct (ct.length / 16)) ∗
         (inA ↦ₛ ct) ∗ memRegion (sp + 0xa50#64) 0x10 ∗
         roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
         ((sp + 0xf00#64) ↦ₛ cbcChainAt iv ct (ct.length / 16)) ∗ Rest) post oom) :
    SepWP P target_pc s
      ((outBuf ↦ₛ cbcPrefixBytes key iv ct m) ∗
       memRegion (outBuf + BitVec.ofNat 64 (16 * m)) (ct.length - 16 * m) ∗
       (inA ↦ₛ ct) ∗ memRegion (sp + 0xa50#64) 0x10 ∗
       roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
       ((sp + 0xf00#64) ↦ₛ cbcChainAt iv ct m) ∗ Rest) post oom := by
  induction rem generalizing m idx s with
  | zero => omega
  | succ rem' ih =>
    let srcPtr := inA + BitVec.ofNat 64 (16 * m)
    let dstPtr := outBuf + BitVec.ofNat 64 (16 * m)
    let c0 := (ct.drop (16 * m)).take 16
    let prevBs := cbcChainAt iv ct m
    let dk := armv8InvExpandedKeys (armv8ExpandKey key)
    have hc0_len : c0.length = 16 := by dsimp [c0]; rw [List.length_take, List.length_drop]; omega
    have hprev_len : prevBs.length = 16 := cbcChainAt_length hiv (by omega)
    have hct_split : (inA ↦ₛ ct) = (srcPtr ↦₁₂₈ bytesToU128LE c0) ∗
        ((inA ↦ₛ ct.take (16 * m)) ∗ ((inA + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ ct.drop (16 * (m + 1)))) := by
      have hcd : ct.drop (16 * m) = c0 ++ ct.drop (16 * (m + 1)) := by
        rw [← List.take_append_drop 16 (ct.drop (16 * m)), List.drop_drop,
            show 16 * m + 16 = 16 * (m + 1) by omega]
      rw [pointsToBytes_take_drop inA (16 * m) ct (by omega), hcd, pointsToBytes_append, hc0_len,
          pointsTo128_eq_pointsToBytes_u128ToBytesLE, u128ToBytesLE_bytesToU128LE hc0_len]
      have hadj : srcPtr + BitVec.ofNat 64 16 = inA + BitVec.ofNat 64 (16 * (m + 1)) := by
        dsimp [srcPtr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * m + 16 = 16 * (m + 1) by omega]
      dsimp [srcPtr] at hadj ⊢; rw [hadj]; sep_ac_rfl
    have hout_split : memRegion dstPtr (ct.length - 16 * m) = memRegion dstPtr 16 ∗
        memRegion (outBuf + BitVec.ofNat 64 (16 * (m + 1))) (ct.length - 16 * (m + 1)) := by
      rw [memRegion_split_le dstPtr 16 (ct.length - 16 * m) (by omega) (by omega)]
      have hadj : dstPtr + BitVec.ofNat 64 16 = outBuf + BitVec.ofNat 64 (16 * (m + 1)) := by
        dsimp [dstPtr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * m + 16 = 16 * (m + 1) by omega]
      rw [hadj, show ct.length - 16 * m - 16 = ct.length - 16 * (m + 1) by omega]
    let IterTail := (srcPtr ↦₁₂₈ bytesToU128LE c0) ∗ roundKeys15At (sp + 0xc30#64) dk ∗
      ((sp + 0xf00#64) ↦ₛ prevBs) ∗ (outBuf ↦ₛ cbcPrefixBytes key iv ct m) ∗
      memRegion (outBuf + BitVec.ofNat 64 (16 * (m + 1))) (ct.length - 16 * (m + 1)) ∗
      (inA ↦ₛ ct.take (16 * m)) ∗ ((inA + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ ct.drop (16 * (m + 1))) ∗ Rest
    refine sepWP_weaken_pre (Entails.of_eq (show _ =
        memRegion (sp + 0xa50#64) 16 ∗ (memRegion dstPtr 16 ∗ IterTail) by
        rw [hct_split, hout_split]; dsimp only [IterTail, dk, prevBs]; sep_ac_rfl)) ?_
    refine sepWP_mem128_elim fun oldA50 => ?_
    refine sepWP_weaken_pre (Entails.of_eq (show _ =
        memRegion dstPtr 16 ∗ (((sp + 0xa50#64) ↦₁₂₈ oldA50) ∗ IterTail) by
        rw [sepConj_left_comm])) ?_
    refine sepWP_mem128_elim fun oldDst => ?_
    dsimp only [IterTail]
    -- Step [187..192]: cbz x22 (untaken); ldr q0, [x19]; add x0; add x1; add x2; str q0, [x24, #0x5a0]
    have hx22_ne : 0xffffffffffffffff#64 - BitVec.ofNat 64 idx ≠ 0#64 := by
      intro hz; have heq : BitVec.ofNat 64 idx = 0xffffffffffffffff#64 := by bv_omega
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : idx < 2 ^ 64)] at this
      have hm1 : (0xffffffffffffffff#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
      omega
    have_instrs cs.preDec 0 6
    wp_step; wp_if hcbz
    · exfalso; exact hx22_ne (by simpa [wp_norm, arm64_norm, hx22] using hcbz)
    · refine step_ldr128 hf_1 (ea := srcPtr) (v := bytesToU128LE c0)
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun])
        (by have h19 : s.readReg64 (.gpr 19#5) = srcPtr := hx19; simp [wp_norm, arm64_norm, h19])
        (by sep_ac_rfl) ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps 3
      refine step_str128_perm hf_5 (ea := sp + 0xa50#64) (old := oldA50) (val := bytesToU128LE c0)
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun])
        (by have h24 : s.readReg64 (.gpr 24#5) = sp + 0x4b0#64 := hx24; simp [wp_norm, arm64_norm, h24]; try bv_lin)
        (by simp [wp_norm, arm64_norm]) (by sep_ac_rfl) fun m1 hm1 => ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      -- [193] bl decrypt::<15>
      refine step_bl_decrypt15 cs.blDec hDec1 (dkPtr := sp + 0xc30#64) (blkPtr := sp + 0xa50#64)
        (dk := dk) (blk := bytesToU128LE c0) (sp := sp)
        (by simp [wp_norm, arm64_norm]; try bv_lin) (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simpa [State.spAligned, wp_norm, arm64_norm, hsp] using hspAl)
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by sep_ac_rfl) fun s1 hpc1 hrun1 hsp1 hcs1 hpure1 => ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpc1
      clear hf_0 hf_1 hf_2 hf_3 hf_4 hf_5
      let decBs := u128ToBytesLE (armv8Decrypt15 dk (bytesToU128LE c0))
      have hdec_len : decBs.length = 16 := u128ToBytesLE_length _
      have ha50_bs : ((sp + 0xa50#64) ↦₁₂₈ armv8Decrypt15 dk (bytesToU128LE c0)) = ((sp + 0xa50#64) ↦ₛ decBs) :=
        pointsTo128_eq_pointsToBytes_u128ToBytesLE _ _
      let PostRest := roundKeys15At (sp + 0xc30#64) dk ∗
        ((outBuf ↦ₛ cbcPrefixBytes key iv ct m) ∗
         memRegion (outBuf + BitVec.ofNat 64 (16 * (m + 1))) (ct.length - 16 * (m + 1)) ∗
         (inA ↦ₛ ct.take (16 * m)) ∗ ((inA + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ ct.drop (16 * (m + 1))) ∗ Rest)
      refine sepWP_weaken_pre (Entails.of_eq (show _ =
          (dstPtr ↦₁₂₈ oldDst) ∗ (srcPtr ↦₁₂₈ bytesToU128LE c0) ∗
          ((sp + 0xa50#64) ↦ₛ decBs) ∗ ((sp + 0xf00#64) ↦ₛ prevBs) ∗ PostRest by
          rw [ha50_bs]; dsimp only [PostRest]; sep_ac_rfl)) ?_
      refine step_rem_post (srcPtr := srcPtr) (dstPtr := dstPtr)
        (x20Val := BitVec.ofNat 64 (rem' + 1)) (x22Val := 0xffffffffffffffff#64 - BitVec.ofNat 64 idx)
        cs.post decBs prevBs c0 oldDst PostRest s1 hdec_len hprev_len hc0_len
        hpc1 hrun1 hsp1 hspAl
        (hcs1.1.trans (by simp [wp_norm, arm64_norm, hx19]; rfl))
        (hcs1.2.1.trans (by simp [wp_norm, arm64_norm, hx20]))
        (hcs1.2.2.1.trans (by simp [wp_norm, arm64_norm, hx21]; rfl))
        (hcs1.2.2.2.1.trans (by simp [wp_norm, arm64_norm, hx22]))
        (hcs1.2.2.2.2.2.1.trans (by simp [wp_norm, arm64_norm, hx24]))
        (hcs1.2.2.2.2.2.2.1.trans (by simp [wp_norm, arm64_norm, hx25]))
        fun s2 hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 hv2 hpure2 => ?_
      have hpure_s_2 : PureStepPreserved s s2 :=
        ((PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hm1])).trans hpure1).trans hpure2
      have hx23_s : s2.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) :=
        hx23_2.trans (hcs1.2.2.2.2.1.trans (by simp [wp_norm, arm64_norm]))
      have hx26_s : s2.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) :=
        hx26_2.trans (hcs1.2.2.2.2.2.2.2.1.trans (by simp [wp_norm, arm64_norm]))
      have hx29_s : s2.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) :=
        hx29_2.trans (hcs1.2.2.2.2.2.2.2.2.2.2.1.trans (by simp [wp_norm, arm64_norm]))
      have hv_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
        hv2.trans (hcs1.2.2.2.2.2.2.2.2.2.2.2.trans (by simp [calleeSavedVRegs, wp_norm, arm64_norm]))
      let ptBs := List.zipWith (· ^^^ ·) decBs prevBs
      have hpt_len : ptBs.length = 16 := by dsimp [ptBs]; rw [List.length_zipWith, hdec_len, hprev_len]; rfl
      have hout_join : ((outBuf ↦ₛ cbcPrefixBytes key iv ct m) ∗ (dstPtr ↦ₛ ptBs)) =
          (outBuf ↦ₛ cbcPrefixBytes key iv ct (m + 1)) := by
        have hpfx_len : (cbcPrefixBytes key iv ct m).length = 16 * m := cbcPrefixBytes_length (by omega)
        rw [← cbcPrefixBytes_step1 hkey hiv hm_lt, pointsToBytes_append, hpfx_len]
      have hrem_dec : BitVec.ofNat 64 (rem' + 1) - 1#64 = BitVec.ofNat 64 rem' := by
        have h1 : BitVec.ofNat 64 (rem' + 1) = BitVec.ofNat 64 rem' + 1#64 := by
          show _ = BitVec.ofNat 64 rem' + BitVec.ofNat 64 1; rw [← BitVec.ofNat_add]
        rw [h1]; bv_lin
      have hent_iter :
          ((dstPtr ↦ₛ ptBs) ∗ (srcPtr ↦₁₂₈ bytesToU128LE c0) ∗ ((sp + 0xa50#64) ↦ₛ ptBs) ∗
           ((sp + 0xf00#64) ↦ₛ c0) ∗ (roundKeys15At (sp + 0xc30#64) dk ∗
            ((outBuf ↦ₛ cbcPrefixBytes key iv ct m) ∗
             memRegion (outBuf + BitVec.ofNat 64 (16 * (m + 1))) (ct.length - 16 * (m + 1)) ∗
             (inA ↦ₛ ct.take (16 * m)) ∗ ((inA + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ ct.drop (16 * (m + 1))) ∗ Rest))) ⊢
          ((outBuf ↦ₛ cbcPrefixBytes key iv ct (m + 1)) ∗
           memRegion (outBuf + BitVec.ofNat 64 (16 * (m + 1))) (ct.length - 16 * (m + 1)) ∗
           (inA ↦ₛ ct) ∗ memRegion (sp + 0xa50#64) 0x10 ∗
           roundKeys15At (sp + 0xc30#64) dk ∗ ((sp + 0xf00#64) ↦ₛ cbcChainAt iv ct (m + 1)) ∗ Rest) := by
        have hma50 : ((sp + 0xa50#64) ↦ₛ ptBs) ⊢ memRegion (sp + 0xa50#64) 0x10 := by
          have h := pointsToBytes_entails_memRegion (sp + 0xa50#64) ptBs; rwa [hpt_len] at h
        refine Entails.trans (Entails.of_eq (show _ = ((sp + 0xa50#64) ↦ₛ ptBs) ∗
            (((outBuf ↦ₛ cbcPrefixBytes key iv ct m) ∗ (dstPtr ↦ₛ ptBs)) ∗
             ((srcPtr ↦₁₂₈ bytesToU128LE c0) ∗ ((inA ↦ₛ ct.take (16 * m)) ∗
              ((inA + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ ct.drop (16 * (m + 1))))) ∗
             memRegion (outBuf + BitVec.ofNat 64 (16 * (m + 1))) (ct.length - 16 * (m + 1)) ∗
             roundKeys15At (sp + 0xc30#64) dk ∗ ((sp + 0xf00#64) ↦ₛ c0) ∗ Rest) by sep_ac_rfl)) ?_
        dsimp only [c0]; rw [hout_join, ← hct_split, ← cbcChainAt_succ iv ct m]
        exact Entails.trans (sepConj_mono_left hma50) (Entails.of_eq (by sep_ac_rfl))
      refine sepWP_weaken_pre hent_iter ?_
      cases rem' with
      | zero =>
        have hm_end : m + 1 = ct.length / 16 := by omega
        have hrem0 : ct.length - 16 * (ct.length / 16) = 0 := by omega
        have hpc_exit : s2.pc = fnAddr + 0x5f8#64 := by rw [hrem_dec] at hpc2; exact hpc2
        have_instrs cs.exit 0 1; wp_step
        refine sepWP_weaken_pre (Entails.of_eq (by
            rw [hm_end, hrem0, memRegion_zero]; dsimp only [dk]; sep_ac_rfl))
          (hnext _ (by simp [wp_norm, arm64_norm]; try bv_lin)
            (by simp [wp_norm, arm64_norm, hrun2]) (by simp [wp_norm, arm64_norm, hsp2])
            (by simp [wp_norm, arm64_norm, hx23_s]) (by simp [wp_norm, arm64_norm, hx26_s])
            (by simp [wp_norm, arm64_norm, hx29_s])
            (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv_s)
            (hpure_s_2.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))))
      | succ rem'' =>
        have hne : (BitVec.ofNat 64 (rem'' + 1) != 0#64) = true := by
          rw [bne_iff_ne]; intro hz; have := congrArg BitVec.toNat hz
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rem'' + 1 < 2 ^ 64)] at this; omega
        have hpc_loop : s2.pc = fnAddr + 0x4c0#64 := by rw [hrem_dec, hne] at hpc2; exact hpc2
        have hsrc_next : srcPtr + BitVec.ofNat 64 16 = inA + BitVec.ofNat 64 (16 * (m + 1)) := by
          dsimp [srcPtr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * m + 16 = 16 * (m + 1) by omega]
        have hdst_next : dstPtr + BitVec.ofNat 64 16 = outBuf + BitVec.ofNat 64 (16 * (m + 1)) := by
          dsimp [dstPtr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * m + 16 = 16 * (m + 1) by omega]
        have hx22_next : 0xffffffffffffffff#64 - BitVec.ofNat 64 idx - 1#64 =
            0xffffffffffffffff#64 - BitVec.ofNat 64 (idx + 1) := by
          have : BitVec.ofNat 64 (idx + 1) = BitVec.ofNat 64 idx + 1#64 := by
            show _ = BitVec.ofNat 64 idx + BitVec.ofNat 64 1; rw [← BitVec.ofNat_add]
          rw [this]; bv_lin
        exact ih (m + 1) (idx + 1) (by omega) (by omega) (by omega) s2
          hpc_loop hrun2 hsp2 (hsrc_next ▸ hx19_2) (hrem_dec ▸ hx20_2)
          (hdst_next ▸ hx21_2) (hx22_next ▸ hx22_2) hx24_2 hx25_2
          fun sf hpc_f hrun_f hsp_f hx23_f hx26_f hx29_f hv_f hpure_f =>
            hnext sf hpc_f hrun_f hsp_f (hx23_f.trans hx23_s) (hx26_f.trans hx26_s)
              (hx29_f.trans hx29_s) (hv_f.trans hv_s) (hpure_s_2.trans hpure_f)

/-- Remainder setup & `1`-block hardware CBC loop (`fnAddr + 0x490#64` → `fnAddr + 0xd20#64`). -/
theorem step_cbcDec_hwRem {P : Program}
    {fnAddr hwDecryptAddr target_pc sp outBuf inA : BitVec 64}
    (cs : RemLoopSegs P fnAddr hwDecryptAddr)
    (hDec1 : subroutine_ok P hwDecryptAddr decrypt15InplaceSpec)
    (key iv ct : List (BitVec 8)) (Rest : SepProp)
    (hkey : key.length = 32) (hiv : iv.length = 16)
    (hct_mod : ct.length % 16 = 0) (hct_lt : ct.length < 2 ^ 40)
    (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x490#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 ((ct.length / 16) % 17))
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0xd20#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x26 = BitVec.ofNat 64 (ct.length / 16) →
      sf.readReg64 .x23 = BitVec.ofNat 64 ct.length →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        ((outBuf ↦ₛ cbcPrefixBytes key iv ct (ct.length / 16)) ∗
         (inA ↦ₛ ct) ∗
         ((sp + 0x010#64) ↦₆₄ BitVec.ofNat 64 (ct.length / 16)) ∗
         ((sp + 0x018#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
         ((sp + 0x028#64) ↦₆₄ outBuf) ∗ ((sp + 0x030#64) ↦₆₄ inA) ∗
         ((sp + 0x0e0#64) ↦₆₄ BitVec.ofNat 64 (17 * (ct.length / 272))) ∗
         memRegion (sp + 0xa50#64) 0x10 ∗
         roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
         ((sp + 0xf00#64) ↦ₛ cbcChainAt iv ct (ct.length / 16)) ∗ Rest) post oom) :
    SepWP P target_pc s
      ((outBuf ↦ₛ cbcPrefixBytes key iv ct (17 * (ct.length / 272))) ∗
       memRegion (outBuf + BitVec.ofNat 64 (272 * (ct.length / 272))) (ct.length - 272 * (ct.length / 272)) ∗
       (inA ↦ₛ ct) ∗
       ((sp + 0x010#64) ↦₆₄ BitVec.ofNat 64 (ct.length / 16)) ∗
       ((sp + 0x018#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
       ((sp + 0x028#64) ↦₆₄ outBuf) ∗ ((sp + 0x030#64) ↦₆₄ inA) ∗
       ((sp + 0x0e0#64) ↦₆₄ BitVec.ofNat 64 (17 * (ct.length / 272))) ∗
       memRegion (sp + 0xa50#64) 0x10 ∗
       roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
       ((sp + 0xf00#64) ↦ₛ cbcChainAt iv ct (17 * (ct.length / 272))) ∗ Rest) post oom := by
  have hdiv272 : (ct.length / 16) / 17 = ct.length / 272 := by omega
  have_instrs cs.setup 0 12
  wp_steps 2; wp_if hhi
  · exfalso
    have hlt : (0x10#64).toNat < (BitVec.ofNat 64 ((ct.length / 16) % 17)).toNat := by
      simpa [wp_norm, arm64_norm, hx20, BitVec.ult] using hhi
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (ct.length / 16) % 17 < 2 ^ 64)] at hlt
    have h16 : (0x10#64 : BitVec 64).toNat = 16 := rfl
    omega
  · wp_steps 5; wp_if heq_blk
    · -- Zero remainder blocks: nBlocks = 17 * (ct.length / 272)
      have hm_eq : 17 * (ct.length / 272) = ct.length / 16 := by
        have hb : BitVec.ofNat 64 (ct.length / 16) = BitVec.ofNat 64 (17 * (ct.length / 272)) := by
          simpa [wp_norm, arm64_norm] using heq_blk
        have ht := congrArg BitVec.toNat hb
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ct.length / 16 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 17 * (ct.length / 272) < 2 ^ 64)] at ht
        exact ht.symm
      have hrem0 : ct.length - 272 * (ct.length / 272) = 0 := by omega
      refine sepWP_weaken_pre (Entails.of_eq (by rw [hm_eq, hrem0, memRegion_zero]; sep_ac_rfl))
        (hnext _ (by simp [wp_norm, arm64_norm]; try bv_lin)
          (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hsp])
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]) (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
          (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])))
    · -- Non-zero remainder blocks: 1 ≤ (ct.length / 16) % 17 ≤ 16
      have hm_lt : 17 * (ct.length / 272) < ct.length / 16 := by
        have hne : ct.length / 16 ≠ 17 * (ct.length / 272) := by
          intro he
          exact heq_blk (by simp [wp_norm, arm64_norm, he])
        omega
      wp_steps 5
      have hlsl : (BitVec.ofNat 64 (17 * (ct.length / 272))) <<< 4 =
          BitVec.ofNat 64 (16 * (17 * (ct.length / 272))) := lsl4_ofNat _
      have h272 : 272 * (ct.length / 272) = 16 * (17 * (ct.length / 272)) := by omega
      have hrem_mod : (ct.length / 16) % 17 = ct.length / 16 - 17 * (ct.length / 272) := by omega
      let RemFrame := ((sp + 0x010#64) ↦₆₄ BitVec.ofNat 64 (ct.length / 16)) ∗
        ((sp + 0x018#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
        ((sp + 0x028#64) ↦₆₄ outBuf) ∗ ((sp + 0x030#64) ↦₆₄ inA) ∗
        ((sp + 0x0e0#64) ↦₆₄ BitVec.ofNat 64 (17 * (ct.length / 272))) ∗ Rest
      refine sepWP_weaken_pre (Entails.of_eq (show _ =
          (outBuf ↦ₛ cbcPrefixBytes key iv ct (17 * (ct.length / 272))) ∗
          memRegion (outBuf + BitVec.ofNat 64 (16 * (17 * (ct.length / 272))))
            (ct.length - 16 * (17 * (ct.length / 272))) ∗
          (inA ↦ₛ ct) ∗ memRegion (sp + 0xa50#64) 0x10 ∗
          roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
          ((sp + 0xf00#64) ↦ₛ cbcChainAt iv ct (17 * (ct.length / 272))) ∗ RemFrame by
          rw [h272]; dsimp only [RemFrame]; sep_ac_rfl)) ?_
      exact step_rem_loop_from cs hDec1 key iv ct RemFrame
        (ct.length / 16 - 17 * (ct.length / 272)) (17 * (ct.length / 272)) 0 rfl hm_lt (by omega)
        hkey hiv hct_mod hct_lt _
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hsp]) hspAl
        (by simp [wp_norm, arm64_norm, hlsl])
        (by simp [wp_norm, arm64_norm, hx20, hrem_mod])
        (by simp [wp_norm, arm64_norm, hlsl])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx24])
        (by simp [wp_norm, arm64_norm])
        fun sf hpc_f hrun_f hsp_f hx23_f hx26_f hx29_f hv_f hpure_f =>
          sepWP_weaken_pre (Entails.of_eq (by dsimp only [RemFrame]; sep_ac_rfl))
            (hnext sf hpc_f hrun_f hsp_f
              (hx26_f.trans (by simp [wp_norm, arm64_norm]))
              (hx23_f.trans (by simp [wp_norm, arm64_norm]))
              (hx29_f.trans (by simp [wp_norm, arm64_norm]))
              (hv_f.trans (by simp [calleeSavedVRegs, wp_norm, arm64_norm]))
              ((PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
                (by simp [wp_norm, arm64_norm])).trans hpure_f))

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopRem

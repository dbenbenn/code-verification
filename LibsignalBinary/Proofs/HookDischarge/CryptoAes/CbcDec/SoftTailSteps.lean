/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Straight-Line Step Chunks for `Fixslice64` 1-Block Tail Loop (`CbcDec.SoftTailSteps`)

Verifies `0x4c9d38..0x4c9d54` (`cbc_tail_pre`), `0x4c9d5c..0x4c9de4` (`cbc_tail_post1`),
`0x4c9de8..0x4c9e4c` (`cbc_tail_post2a`), and `0x4c9e50..0x4c9e70` (`cbc_tail_post2b`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftTailSteps

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.StdStartup (decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (PureStepPreserved)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
  (cbcSoftTailPreWords cbcSoftTailPost1Words cbcSoftTailPost2Words)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
  (sepWP_weaken_pre bytes16At pts64x8At)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules.Macros
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules.Simp

@[local simp]
private theorem zeroExtend64_xor32_eq (a b : BitVec 8) :
    ((a.zeroExtend 64).truncate 32 ^^^ (b.zeroExtend 64).truncate 32).zeroExtend 64 =
      (a ^^^ b).zeroExtend 64 := by bv_bits

@[local simp]
private theorem truncate8_zeroExtend64_eq (a : BitVec 8) :
    (a.zeroExtend 64).truncate 8 = a := by bv_bits

private theorem subsPState64_z_one (v : BitVec 64) :
    (subsPState64 v 1#64).z = (v - 1#64 == 0#64) := by
  change ConditionHolds .EQ (subsPState64 v 1#64) = (v - 1#64 == 0#64)
  rw [conditionHolds_eq_subsPState64]
  by_cases h : v = 1#64
  · subst h; rfl
  · have hne1 : (v == 1#64) = false := beq_false_of_ne h
    have hne2 : (v - 1#64 == 0#64) = false := beq_false_of_ne (fun h0 =>
      h (calc v = (v - 1#64) + 1#64 := by bv_lin
              _ = 0#64 + 1#64 := by rw [h0]
              _ = 1#64 := rfl))
    rw [hne1, hne2]

/-! ## 1. Pre-Decrypt Load & Zero-Pad (`fnAddr + 0xbe4#64 -> fnAddr + 0xc04#64`) -/

set_option maxHeartbeats 400000 in
theorem cbc_tail_pre {P : Program} {fnAddr target_pc sp src : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0xbe4#64) (decodeWords cbcSoftTailPreWords))
    (cw0 cw1 i0 i1 i2 i3 i4 i5 i6 i7 : BitVec 64)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0xbe4#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx19 : s.readReg64 .x19 = sp + 0x870#64)
    (hx20 : s.readReg64 .x20 = src + 7#64)
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0xc04#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x0 = sp + 0xb40#64 →
      sf.readReg64 .x1 = sp + 0x870#64 →
      sf.readReg64 .x8 = sp + 0x4b0#64 →
      sf.readReg64 .x19 = sp + 0x870#64 →
      sf.readReg64 .x20 = src + 7#64 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s → PureStepPreserved s sf →
      SepWP P target_pc sf
        ((src ↦₆₄ cw0) ∗ ((src + 8#64) ↦₆₄ cw1) ∗
         pts64x8At (sp + 0x870#64) cw0 cw1 0#64 0#64 0#64 0#64 0#64 0#64 ∗ Rest)
        post oom) :
    SepWP P target_pc s
      ((src ↦₆₄ cw0) ∗ ((src + 8#64) ↦₆₄ cw1) ∗
       pts64x8At (sp + 0x870#64) i0 i1 i2 i3 i4 i5 i6 i7 ∗ Rest)
      post oom := by
  have_instrs hc 0 8
  dsimp only [pts64x8At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_step
  wp_step
  wp_steps 3
  wp_str128 hf_5 m1 hm1
  wp_stp128 hf_6 m2 hm2
  wp_str128 hf_7 m3 hm3
  refine sepWP_weaken_pre (Entails.of_eq (by
      dsimp only [pts64x8At]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; try sep_ac_rfl))
    (hnext _
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp])
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hx19])
      (by simp [wp_norm, arm64_norm, hx20])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx24])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm3, hm2, hm1])))

/-! ## 2. Post-Decrypt XOR Half 1 (`fnAddr + 0xc08#64 -> fnAddr + 0xc94#64`) -/

set_option maxHeartbeats 500000 in
theorem cbc_tail_post1 {P : Program} {fnAddr target_pc sp dst : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0xc08#64) (decodeWords cbcSoftTailPost1Words))
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
     p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
     z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 : BitVec 8)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0xc08#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx21 : s.readReg64 .x21 = dst + 7#64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0xc94#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x9 = (p8 ^^^ d8).zeroExtend 64 →
      sf.readReg64 .x10 = (p7 ^^^ d7).zeroExtend 64 →
      sf.readReg64 .x11 = (p3 ^^^ d3).zeroExtend 64 →
      sf.readReg64 .x12 = d10.zeroExtend 64 →
      sf.readReg64 .x13 = (p5 ^^^ d5).zeroExtend 64 →
      sf.readReg64 .x14 = d11.zeroExtend 64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = dst + 7#64 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 - 1#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.pstate.z = (s.readReg64 .x25 - 1#64 == 0#64) →
      calleeSavedVRegs sf = calleeSavedVRegs s → PureStepPreserved s sf →
      SepWP P target_pc sf
        (bytes16At (sp + 0x4b0#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
         bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
         bytes16At dst (p0 ^^^ d0) (p1 ^^^ d1) (p2 ^^^ d2) z3 (p4 ^^^ d4) z5 (p6 ^^^ d6)
           z7 z8 z9 z10 z11 z12 z13 z14 z15 ∗ Rest)
        post oom) :
    SepWP P target_pc s
      (bytes16At (sp + 0x4b0#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
       bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
       bytes16At dst z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 ∗ Rest)
      post oom := by
  have_instrs hc 0 35
  dsimp only [bytes16At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 12
  wp_str8 hf_12 m1 hm1
  wp_steps 9
  wp_str8 hf_22 m2 hm2
  wp_steps 5
  wp_str8 hf_28 m3 hm3
  wp_step
  wp_str8 hf_30 m4 hm4
  wp_steps 3
  wp_str8 hf_34 m5 hm5
  refine sepWP_weaken_pre (Entails.of_eq (by
      dsimp only [bytes16At]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; try sep_ac_rfl))
    (hnext _
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp])
      (by simp [wp_norm, arm64_norm]; try bv_bits)
      (by simp [wp_norm, arm64_norm]; try bv_bits)
      (by simp [wp_norm, arm64_norm]; try bv_bits)
      (by simp [wp_norm, arm64_norm]; try bv_bits)
      (by simp [wp_norm, arm64_norm]; try bv_bits)
      (by simp [wp_norm, arm64_norm]; try bv_bits)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx21])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, subsPState64_z_one])
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm5, hm4, hm3, hm2, hm1])))

/-! ## 3. Post-Decrypt XOR Half 2A (`fnAddr + 0xc94#64 -> fnAddr + 0xcfc#64`) -/

set_option maxHeartbeats 500000 in
theorem cbc_tail_post2a {P : Program} {fnAddr target_pc sp dst : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0xc94#64) (decodeWords cbcSoftTailPost2Words))
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
     p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
     y0 y1 y2 y3 y4 y5 y6 y7 y8 z3 z5 z7 z8 z9 z10 z11 z12 z13 z14 z15 : BitVec 8)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0xc94#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx9 : s.readReg64 .x9 = y8.zeroExtend 64)
    (hx10 : s.readReg64 .x10 = y7.zeroExtend 64)
    (hx11 : s.readReg64 .x11 = y3.zeroExtend 64)
    (hx12 : s.readReg64 .x12 = d10.zeroExtend 64)
    (hx13 : s.readReg64 .x13 = y5.zeroExtend 64)
    (hx14 : s.readReg64 .x14 = d11.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = dst + 7#64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0xcfc#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x8 = (p14 ^^^ d14).zeroExtend 64 →
      sf.readReg64 .x9 = (p15 ^^^ d15).zeroExtend 64 →
      sf.readReg64 .x10 = (p12 ^^^ d12).zeroExtend 64 →
      sf.readReg64 .x11 = (p13 ^^^ d13).zeroExtend 64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = dst + 7#64 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.pstate.z = s.pstate.z →
      calleeSavedVRegs sf = calleeSavedVRegs s → PureStepPreserved s sf →
      SepWP P target_pc sf
        (bytes16At (sp + 0x4b0#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
         bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
         bytes16At dst y0 y1 y2 y3 y4 y5 y6 y7 y8
           (p9 ^^^ d9) (p10 ^^^ d10) (p11 ^^^ d11) z12 z13 z14 z15 ∗ Rest)
        post oom) :
    SepWP P target_pc s
      (bytes16At (sp + 0x4b0#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
       bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
       bytes16At dst y0 y1 y2 z3 y4 z5 y6 z7 z8 z9 z10 z11 z12 z13 z14 z15 ∗ Rest)
      post oom := by
  have_instrs hc 0 26
  dsimp only [bytes16At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 5
  wp_str8 hf_5 m1 hm1
  wp_step
  wp_str8 hf_7 m2 hm2
  wp_steps 2
  wp_str8 hf_10 m3 hm3
  wp_steps 3
  wp_str8 hf_14 m4 hm4
  wp_steps 2
  wp_str8 hf_17 m5 hm5
  wp_step
  wp_str8 hf_19 m6 hm6
  wp_steps 3
  wp_str8 hf_23 m7 hm7
  wp_steps 2
  refine sepWP_weaken_pre (Entails.of_eq (by
      dsimp only [bytes16At]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; try sep_ac_rfl))
    (hnext _
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp])
      (by simp [wp_norm, arm64_norm]; try bv_bits)
      (by simp [wp_norm, arm64_norm]; try bv_bits)
      (by simp [wp_norm, arm64_norm]; try bv_bits)
      (by simp [wp_norm, arm64_norm]; try bv_bits)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx21])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm7, hm6, hm5, hm4, hm3, hm2, hm1])))

/-! ## 4. Post-Decrypt XOR Half 2B & Latch (`fnAddr + 0xcfc#64 -> +0xd20 / +0xbe4`) -/

set_option maxHeartbeats 400000 in
theorem cbc_tail_post2b {P : Program} {fnAddr target_pc sp src dst rem1 : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0xc94#64) (decodeWords cbcSoftTailPost2Words))
    (cw0 cw1 pv0 pv1 : BitVec 64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 z12 z13 z14 z15 : BitVec 8)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0xcfc#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = y14.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = y15.zeroExtend 64)
    (hx10 : s.readReg64 .x10 = y12.zeroExtend 64)
    (hx11 : s.readReg64 .x11 = y13.zeroExtend 64)
    (hx20 : s.readReg64 .x20 = src + 7#64)
    (hx21 : s.readReg64 .x21 = dst + 7#64)
    (hx22 : s.readReg64 .x22 = sp + 0xb40#64)
    (hx25 : s.readReg64 .x25 = rem1)
    (hpz : s.pstate.z = (rem1 == 0#64))
    (hnext : ∀ sf : State,
      sf.pc = (if rem1 == 0#64 then fnAddr + 0xd20#64 else fnAddr + 0xbe4#64) →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = src + 16#64 + 7#64 →
      sf.readReg64 .x21 = dst + 16#64 + 7#64 →
      sf.readReg64 .x22 = sp + 0xb40#64 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = rem1 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s → PureStepPreserved s sf →
      SepWP P target_pc sf
        ((src ↦₆₄ cw0) ∗ ((src + 8#64) ↦₆₄ cw1) ∗
         ((sp + 0xf00#64) ↦₆₄ cw0) ∗ ((sp + 0xf08#64) ↦₆₄ cw1) ∗
         bytes16At dst y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 ∗ Rest)
        post oom) :
    SepWP P target_pc s
      ((src ↦₆₄ cw0) ∗ ((src + 8#64) ↦₆₄ cw1) ∗
       ((sp + 0xf00#64) ↦₆₄ pv0) ∗ ((sp + 0xf08#64) ↦₆₄ pv1) ∗
       bytes16At dst y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 z12 z13 z14 z15 ∗ Rest)
      post oom := by
  have_instrs hc 26 9
  dsimp only [bytes16At]
  wp_step
  wp_step
  wp_str8 hf_28 m1 hm1
  wp_str8 hf_29 m2 hm2
  wp_str8 hf_30 m3 hm3
  wp_str8 hf_31 m4 hm4
  wp_step
  wp_str128 hf_33 m5 hm5
  wp_step
  wp_if hbne
  · have hrem_ne : (rem1 == 0#64) = false := by
      simpa [ConditionHolds, wp_norm, arm64_norm, hpz] using hbne
    refine sepWP_weaken_pre (Entails.of_eq (by dsimp only [bytes16At]))
      (hnext _
        (by simp [wp_norm, arm64_norm, hrem_ne]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hx22])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx25])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm])
        (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
        (PureStepPreserved.of_proj_perm
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hm5, hm4, hm3, hm2, hm1])))
  · have hrem_eq : (rem1 == 0#64) = true := by
      simpa [ConditionHolds, wp_norm, arm64_norm, hpz] using hbne
    refine sepWP_weaken_pre (Entails.of_eq (by dsimp only [bytes16At]))
      (hnext _
        (by simp [wp_norm, arm64_norm, hrem_eq]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hx22])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx25])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm])
        (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
        (PureStepPreserved.of_proj_perm
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hm5, hm4, hm3, hm2, hm1])))

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftTailSteps

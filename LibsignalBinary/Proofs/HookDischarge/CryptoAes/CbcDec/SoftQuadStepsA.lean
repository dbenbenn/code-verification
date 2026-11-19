/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `Fixslice64` 4-Block CBC Loop Body Steps A (`CbcDec.SoftQuadStepsA`)

Verifies straight-line segments `cbcSoftQuadPre1Words` (`+0x694 -> +0x73c`),
`cbcSoftQuadPre2Words` (`+0x73c -> +0x7e8`), `cbcSoftQuadPost1aWords` (`+0x7ec -> +0x874`),
and `cbcSoftQuadPost1bWords` (`+0x874 -> +0x900`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadStepsA

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.StdStartup (decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (PureStepPreserved)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
  (cbcSoftQuadPre1Words cbcSoftQuadPre2Words cbcSoftQuadPost1aWords cbcSoftQuadPost1bWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
  (sepWP_weaken_pre pack8LE bytes16At pts64_pair_eq_bytes16At pts64_pair_off_eq_bytes16At
   pts64x8At spill14At)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules.Macros
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules.Simp

@[local simp]
private theorem zeroExtend64_xor32_eq (a b : BitVec 8) :
    ((a.zeroExtend 64).truncate 32 ^^^ (b.zeroExtend 64).truncate 32).zeroExtend 64 =
      (a ^^^ b).zeroExtend 64 := by bv_bits

@[local simp]
private theorem truncate8_zeroExtend64_eq (a : BitVec 8) :
    (a.zeroExtend 64).truncate 8 = a := by bv_bits

/-! ## 1. `cbc_quad_pre1` (`fnAddr + 0x694#64 -> fnAddr + 0x73c#64`, 42 insns) -/

set_option maxHeartbeats 400000 in
theorem cbc_quad_pre1 {P : Program} {fnAddr target_pc sp src : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x694#64) (decodeWords cbcSoftQuadPre1Words))
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
     c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31
     c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47
     c48 c49 c50 c51 c52 c53 c54 c55 c56 c57 c58 c59 c60 c61 c62 c63 : BitVec 8)
    (i0 i1 i2 i3 i4 i5 i6 i7 o0 o1 o2 o3 o4 o5 o6 o7 : BitVec 64)
    (g0_0 g0_1 g0_2 g0_3 g0_4 g0_5 g0_6 g0_7 g0_8 g0_9 g0_10 g0_11 g0_12 g0_13 : BitVec 32)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x694#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hx26 : s.readReg64 .x26 = src + 0x18#64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0x73c#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x0 = sp + 0xb40#64 →
      sf.readReg64 .x1 = sp + 0x870#64 →
      sf.readReg64 .x8 = c19.zeroExtend 64 →
      sf.readReg64 .x9 = c18.zeroExtend 64 →
      sf.readReg64 .x10 = c34.zeroExtend 64 →
      sf.readReg64 .x19 = c1.zeroExtend 64 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = c4.zeroExtend 64 →
      sf.readReg64 .x22 = c2.zeroExtend 64 →
      sf.readReg64 .x23 = c3.zeroExtend 64 →
      sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x25 = c0.zeroExtend 64 →
      sf.readReg64 .x26 = src + 0x18#64 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = c5.zeroExtend 64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (bytes16At src c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 ∗
         bytes16At (src + 16#64) c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 ∗
         bytes16At (src + 32#64) c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 ∗
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
           (c19.zeroExtend 32) (c18.zeroExtend 32) ∗
         Rest)
        post oom) :
    SepWP P target_pc s
      (bytes16At src c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 ∗
       ((src + 16#64) ↦₆₄ pack8LE c16 c17 c18 c19 c20 c21 c22 c23) ∗
       ((src + 24#64) ↦₆₄ pack8LE c24 c25 c26 c27 c28 c29 c30 c31) ∗
       ((src + 32#64) ↦₆₄ pack8LE c32 c33 c34 c35 c36 c37 c38 c39) ∗
       ((src + 40#64) ↦₆₄ pack8LE c40 c41 c42 c43 c44 c45 c46 c47) ∗
       ((src + 48#64) ↦₆₄ pack8LE c48 c49 c50 c51 c52 c53 c54 c55) ∗
       ((src + 56#64) ↦₆₄ pack8LE c56 c57 c58 c59 c60 c61 c62 c63) ∗
       pts64x8At (sp + 0x870#64) i0 i1 i2 i3 i4 i5 i6 i7 ∗
       pts64x8At (sp + 0x4b0#64) o0 o1 o2 o3 o4 o5 o6 o7 ∗
       spill14At (sp + 0x03c#64)
         g0_0 g0_1 g0_2 g0_3 g0_4 g0_5 g0_6 g0_7 g0_8 g0_9 g0_10 g0_11 g0_12 g0_13 ∗
       Rest)
      post oom := by
  have_instrs hc 0 42
  rw [bytes16At, pts64x8At, pts64x8At, spill14At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 6
  wp_stp128 hf_6 m1 hm1
  rw [pts64_pair_off_eq_bytes16At src 16#64 24#64 (by bv_lin),
      pts64_pair_off_eq_bytes16At src 32#64 40#64 (by bv_lin),
      bytes16At, bytes16At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 2
  wp_str128 hf_9 m2 hm2
  wp_step
  rw [← bytes16At, ← pts64_pair_eq_bytes16At src]
  wp_step
  rw [pts64_pair_eq_bytes16At src, bytes16At]
  wp_steps 2
  wp_stp32 hf_14 m3 hm3
  wp_steps 2
  wp_str128 hf_17 m4 hm4
  wp_steps 2
  wp_stp32 hf_20 m5 hm5
  wp_steps 5
  wp_stp32 hf_26 m6 hm6
  wp_steps 3
  wp_stp128 hf_30 m7 hm7
  wp_stp32 hf_31 m8 hm8
  wp_steps 2
  wp_str128 hf_34 m9 hm9
  wp_stp32 hf_35 m10 hm10
  wp_steps 2
  wp_stp32 hf_38 m11 hm11
  wp_steps 2
  wp_stp32 hf_41 m12 hm12
  refine sepWP_weaken_pre (Entails.of_eq ?_)
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
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx24])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx26])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by
          simp only [wp_norm, arm64_norm] at hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11 hm12 ⊢
          exact hm12.trans (hm11.trans (hm10.trans (hm9.trans (hm8.trans (hm7.trans
            (hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1)))))))))))))
  dsimp only [bytes16At, pts64x8At, spill14At, pack8LE]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-! ## 2. `cbc_quad_pre2` (`fnAddr + 0x73c#64 -> fnAddr + 0x7e8#64`, 43 insns) -/

set_option maxHeartbeats 400000 in
theorem cbc_quad_pre2 {P : Program} {fnAddr target_pc sp src : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x73c#64) (decodeWords cbcSoftQuadPre2Words))
    (c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31
     c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 : BitVec 8)
    (g1_0 g1_1 g1_2 g1_3 g1_4 g1_5 g1_6 g1_7 g1_8 g1_9 g1_10 g1_11 g1_12 g1_13
     g2_0 g2_1 g2_2 g2_3 g2_4 g2_5 g2_6 g2_7 g2_8 g2_9 g2_10 g2_11 g2_12 g2_13 : BitVec 32)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x73c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx10 : s.readReg64 .x10 = c34.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = src + 0x18#64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0x7e8#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x0 = s.readReg64 .x0 →
      sf.readReg64 .x1 = s.readReg64 .x1 →
      sf.readReg64 .x8 = sp + 0x4b0#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = src + 0x18#64 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (bytes16At (src + 16#64) c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 ∗
         bytes16At (src + 32#64) c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 ∗
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
         Rest)
        post oom) :
    SepWP P target_pc s
      (bytes16At (src + 16#64) c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 ∗
       bytes16At (src + 32#64) c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 ∗
       spill14At (sp + 0x074#64)
         g1_0 g1_1 g1_2 g1_3 g1_4 g1_5 g1_6 g1_7 g1_8 g1_9 g1_10 g1_11 g1_12 g1_13 ∗
       spill14At (sp + 0x0ac#64)
         g2_0 g2_1 g2_2 g2_3 g2_4 g2_5 g2_6 g2_7 g2_8 g2_9 g2_10 g2_11 g2_12 g2_13 ∗
       Rest)
      post oom := by
  have_instrs hc 0 43
  rw [bytes16At, bytes16At, spill14At, spill14At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 2
  wp_stp32 hf_2 n1 hn1
  wp_steps 2
  wp_stp32 hf_5 n2 hn2
  wp_steps 2
  wp_stp32 hf_8 n3 hn3
  wp_steps 2
  wp_stp32 hf_11 n4 hn4
  wp_steps 2
  wp_stp32 hf_14 n5 hn5
  wp_steps 2
  wp_stp32 hf_17 n6 hn6
  wp_steps 2
  wp_str32 hf_20 n7 hn7
  wp_step
  wp_stp32 hf_22 n8 hn8
  wp_steps 2
  wp_stp32 hf_25 n9 hn9
  wp_steps 2
  wp_stp32 hf_28 n10 hn10
  wp_steps 2
  wp_stp32 hf_31 n11 hn11
  wp_steps 2
  wp_stp32 hf_34 n12 hn12
  wp_steps 2
  wp_stp32 hf_37 n13 hn13
  wp_step
  wp_str32 hf_39 n14 hn14
  wp_step
  wp_stp32 hf_41 n15 hn15
  wp_step
  refine sepWP_weaken_pre (Entails.of_eq ?_)
    (hnext _
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx26])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by
          simp only [wp_norm, arm64_norm] at hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9 hn10 hn11 hn12 hn13 hn14 hn15 ⊢
          exact hn15.trans (hn14.trans (hn13.trans (hn12.trans (hn11.trans (hn10.trans (hn9.trans
            (hn8.trans (hn7.trans (hn6.trans (hn5.trans (hn4.trans (hn3.trans (hn2.trans hn1))))))))))))))))
  dsimp only [bytes16At, spill14At]
  simp only [wp_norm, arm64_norm]

/-! ## 3. `cbc_quad_post1a` (`fnAddr + 0x7ec#64 -> fnAddr + 0x874#64`, 34 insns) -/

set_option maxHeartbeats 400000 in
theorem cbc_quad_post1a {P : Program} {fnAddr target_pc sp : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x7ec#64) (decodeWords cbcSoftQuadPost1aWords))
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
     d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31
     d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47
     d48 d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62 d63
     p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 8)
    (i0 i1 i2 i3 i4 i5 i6 i7 : BitVec 64)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x7ec#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0x874#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x8 = (d6 ^^^ p6).zeroExtend 64 →
      sf.readReg64 .x9 = p7.zeroExtend 64 →
      sf.readReg64 .x10 = d7.zeroExtend 64 →
      sf.readReg64 .x11 = d11.zeroExtend 64 →
      sf.readReg64 .x12 = d12.zeroExtend 64 →
      sf.readReg64 .x13 = p15.zeroExtend 64 →
      sf.readReg64 .x14 = d15.zeroExtend 64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 - 1#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.pstate.z = (s.readReg64 .x27 - 1#64 == 0#64) →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (bytes16At (sp + 0x870#64)
           d0 (d1 ^^^ p1) (d2 ^^^ p2) (d3 ^^^ p3) (d4 ^^^ p4) (d5 ^^^ p5)
           d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
         bytes16At (sp + 0x880#64) d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
         bytes16At (sp + 0x890#64) d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47 ∗
         bytes16At (sp + 0x8a0#64) d48 d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62 d63 ∗
         pts64x8At (sp + 0x4b0#64)
           (pack8LE d0 d1 d2 d3 d4 d5 d6 d7) (pack8LE d8 d9 d10 d11 d12 d13 d14 d15)
           (pack8LE d16 d17 d18 d19 d20 d21 d22 d23) (pack8LE d24 d25 d26 d27 d28 d29 d30 d31)
           (pack8LE d32 d33 d34 d35 d36 d37 d38 d39) (pack8LE d40 d41 d42 d43 d44 d45 d46 d47)
           (pack8LE d48 d49 d50 d51 d52 d53 d54 d55) (pack8LE d56 d57 d58 d59 d60 d61 d62 d63) ∗
         bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
         Rest)
        post oom) :
    SepWP P target_pc s
      (pts64x8At (sp + 0x870#64) i0 i1 i2 i3 i4 i5 i6 i7 ∗
       pts64x8At (sp + 0x4b0#64)
         (pack8LE d0 d1 d2 d3 d4 d5 d6 d7) (pack8LE d8 d9 d10 d11 d12 d13 d14 d15)
         (pack8LE d16 d17 d18 d19 d20 d21 d22 d23) (pack8LE d24 d25 d26 d27 d28 d29 d30 d31)
         (pack8LE d32 d33 d34 d35 d36 d37 d38 d39) (pack8LE d40 d41 d42 d43 d44 d45 d46 d47)
         (pack8LE d48 d49 d50 d51 d52 d53 d54 d55) (pack8LE d56 d57 d58 d59 d60 d61 d62 d63) ∗
       bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
       Rest)
      post oom := by
  have_instrs hc 0 34
  rw [pts64x8At, pts64x8At, bytes16At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 5
  wp_stp128 hf_5 m1 hm1
  wp_step
  wp_stp128 hf_7 m2 hm2
  rw [pts64_pair_off_eq_bytes16At sp 0x870#64 0x878#64 (by bv_lin), bytes16At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 7
  wp_str8 hf_15 m3 hm3
  wp_steps 2
  wp_str8 hf_18 m4 hm4
  wp_steps 3
  wp_str8 hf_22 m5 hm5
  wp_steps 3
  wp_str8 hf_26 m6 hm6
  wp_steps 3
  wp_str8 hf_30 m7 hm7
  wp_steps 3
  refine sepWP_weaken_pre (Entails.of_eq ?_)
    (hnext _
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx24])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by
        simp only [wp_norm, arm64_norm]
        generalize s.readReg64 .x27 = v
        change ConditionHolds .EQ (subsPState64 v 1#64) = (v - 1#64 == 0#64)
        rw [conditionHolds_eq_subsPState64]
        by_cases h : v = 1#64
        · subst h; rfl
        · have hne1 : (v == 1#64) = false := beq_false_of_ne h
          have hne2 : (v - 1#64 == 0#64) = false := beq_false_of_ne (fun h0 =>
            h (calc v = (v - 1#64) + 1#64 := by bv_lin
                    _ = 0#64 + 1#64 := by rw [h0]
                    _ = 1#64 := rfl))
          rw [hne1, hne2])
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by
          simp only [wp_norm, arm64_norm] at hm1 hm2 hm3 hm4 hm5 hm6 hm7 ⊢
          exact hm7.trans (hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1))))))))
  rw [← pts64_pair_eq_bytes16At (sp + 0x880#64),
      ← pts64_pair_eq_bytes16At (sp + 0x890#64),
      ← pts64_pair_eq_bytes16At (sp + 0x8a0#64)]
  unfold bytes16At pts64x8At pack8LE
  simp only [wp_norm, arm64_norm]

/-! ## 4. `cbc_quad_post1b` (`fnAddr + 0x874#64 -> fnAddr + 0x900#64`, 35 insns) -/

set_option maxHeartbeats 400000 in
theorem cbc_quad_post1b {P : Program} {fnAddr target_pc sp : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x874#64) (decodeWords cbcSoftQuadPost1bWords))
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
     d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31
     p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
     c0 : BitVec 8)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x874#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = (d6 ^^^ p6).zeroExtend 64)
    (hx9 : s.readReg64 .x9 = p7.zeroExtend 64)
    (hx10 : s.readReg64 .x10 = d7.zeroExtend 64)
    (hx11 : s.readReg64 .x11 = d11.zeroExtend 64)
    (hx12 : s.readReg64 .x12 = d12.zeroExtend 64)
    (hx13 : s.readReg64 .x13 = p15.zeroExtend 64)
    (hx14 : s.readReg64 .x14 = d15.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = c0.zeroExtend 64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0x900#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x8 = (d16 ^^^ c0).zeroExtend 64 →
      sf.readReg64 .x9 = d17.zeroExtend 64 →
      sf.readReg64 .x11 = d19.zeroExtend 64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = c0.zeroExtend 64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.pstate = s.pstate →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (bytes16At (sp + 0x870#64)
           d0 (d1 ^^^ p1) (d2 ^^^ p2) (d3 ^^^ p3) (d4 ^^^ p4) (d5 ^^^ p5)
           (d6 ^^^ p6) (d7 ^^^ p7) (d8 ^^^ p8) (d9 ^^^ p9) (d10 ^^^ p10) (d11 ^^^ p11)
           (d12 ^^^ p12) (d13 ^^^ p13) (d14 ^^^ p14) (d15 ^^^ p15) ∗
         bytes16At (sp + 0x880#64) d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
         bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
         Rest)
        post oom) :
    SepWP P target_pc s
      (bytes16At (sp + 0x870#64)
         d0 (d1 ^^^ p1) (d2 ^^^ p2) (d3 ^^^ p3) (d4 ^^^ p4) (d5 ^^^ p5)
         d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
       bytes16At (sp + 0x880#64) d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
       Rest)
      post oom := by
  have_instrs hc 0 35
  rw [bytes16At, bytes16At, bytes16At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_str8 hf_0 m1 hm1
  wp_steps 3
  wp_str8 hf_4 m2 hm2
  wp_steps 3
  wp_str8 hf_8 m3 hm3
  wp_steps 3
  wp_str8 hf_12 m4 hm4
  wp_steps 4
  wp_str8 hf_17 m5 hm5
  wp_step
  wp_str8 hf_19 m6 hm6
  wp_steps 4
  wp_str8 hf_24 m7 hm7
  wp_steps 4
  wp_str8 hf_29 m8 hm8
  wp_step
  wp_str8 hf_31 m9 hm9
  wp_steps 2
  wp_str8 hf_34 m10 hm10
  refine sepWP_weaken_pre (Entails.of_eq ?_)
    (hnext _
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx25])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by
          simp only [wp_norm, arm64_norm] at hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 ⊢
          exact hm10.trans (hm9.trans (hm8.trans (hm7.trans (hm6.trans (hm5.trans
            (hm4.trans (hm3.trans (hm2.trans hm1)))))))))))
  unfold bytes16At
  simp only [wp_norm, arm64_norm]

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadStepsA

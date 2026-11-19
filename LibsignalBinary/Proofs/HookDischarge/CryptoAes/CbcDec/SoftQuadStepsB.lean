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
# `Fixslice64` 4-Block CBC Loop Body Steps B (`CbcDec.SoftQuadStepsB`)

Verifies `cbcSoftQuadPost2Words` (`+0x900 -> +0x9d4`), `cbcSoftQuadPost3Words` (`+0x9d4 -> +0xacc`),
`cbcSoftQuadPost4Words` (`+0xacc -> +0xb9c`), and `cbcSoftQuadPost5Words` (`+0xb9c -> +0xbc0 | +0x694`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadStepsB

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.StdStartup (decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (PureStepPreserved)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
  (cbcSoftQuadPost2Words cbcSoftQuadPost3Words cbcSoftQuadPost4Words cbcSoftQuadPost5Words)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
  (sepWP_weaken_pre pack8LE bytes16At pts64_pair_off_eq_bytes16At pts64x8At spill14At)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules.Macros
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules.Simp

@[local simp]
private theorem zeroExtend64_xor32_eq (a b : BitVec 8) :
    ((a.zeroExtend 64).truncate 32 ^^^ (b.zeroExtend 64).truncate 32).zeroExtend 64 =
      (a ^^^ b).zeroExtend 64 := by bv_bits

@[local simp]
private theorem truncate8_zeroExtend64_eq (a : BitVec 8) :
    (a.zeroExtend 64).truncate 8 = a := by bv_bits

/-! ## 1. `cbc_quad_post2` (`fnAddr + 0x900#64 -> fnAddr + 0x9d4#64`, 53 insns) -/

set_option maxHeartbeats 400000 in
theorem cbc_quad_post2 {P : Program} {fnAddr target_pc sp : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x900#64) (decodeWords cbcSoftQuadPost2Words))
    (d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31
     d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47
     c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 : BitVec 8)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x900#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = (d16 ^^^ c0).zeroExtend 64)
    (hx9 : s.readReg64 .x9 = d17.zeroExtend 64)
    (hx11 : s.readReg64 .x11 = d19.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = c1.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = c4.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = c2.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = c3.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = c5.zeroExtend 64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0x9d4#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x8 = d32.zeroExtend 64 →
      sf.readReg64 .x9 = c16.zeroExtend 64 →
      sf.readReg64 .x11 = d35.zeroExtend 64 →
      sf.readReg64 .x12 = c17.zeroExtend 64 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = sp + 0xb40#64 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.pstate = s.pstate →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (bytes16At (sp + 0x880#64)
           (d16 ^^^ c0) (d17 ^^^ c1) (d18 ^^^ c2) (d19 ^^^ c3) (d20 ^^^ c4) (d21 ^^^ c5)
           (d22 ^^^ c6) (d23 ^^^ c7) (d24 ^^^ c8) (d25 ^^^ c9) (d26 ^^^ c10) (d27 ^^^ c11)
           (d28 ^^^ c12) (d29 ^^^ c13) (d30 ^^^ c14) (d31 ^^^ c15) ∗
         bytes16At (sp + 0x890#64) d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47 ∗
         spill14At (sp + 0x03c#64)
           (c7.zeroExtend 32) (c6.zeroExtend 32) (c8.zeroExtend 32) (c9.zeroExtend 32)
           (c11.zeroExtend 32) (c10.zeroExtend 32) (c12.zeroExtend 32) (c13.zeroExtend 32)
           (c15.zeroExtend 32) (c14.zeroExtend 32) (c16.zeroExtend 32) (c17.zeroExtend 32)
           (c19.zeroExtend 32) (c18.zeroExtend 32) ∗
         Rest)
        post oom) :
    SepWP P target_pc s
      (bytes16At (sp + 0x880#64) d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       bytes16At (sp + 0x890#64) d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47 ∗
       spill14At (sp + 0x03c#64)
         (c7.zeroExtend 32) (c6.zeroExtend 32) (c8.zeroExtend 32) (c9.zeroExtend 32)
         (c11.zeroExtend 32) (c10.zeroExtend 32) (c12.zeroExtend 32) (c13.zeroExtend 32)
         (c15.zeroExtend 32) (c14.zeroExtend 32) (c16.zeroExtend 32) (c17.zeroExtend 32)
         (c19.zeroExtend 32) (c18.zeroExtend 32) ∗
       Rest)
      post oom := by
  have_instrs hc 0 53
  rw [bytes16At, bytes16At, spill14At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 3
  wp_str8 hf_3 m1 hm1
  wp_str8 hf_4 m2 hm2
  wp_steps 3
  wp_str8 hf_8 m3 hm3
  wp_steps 3
  wp_str8 hf_12 m4 hm4
  wp_steps 2
  wp_str8 hf_15 m5 hm5
  wp_steps 2
  wp_str8 hf_18 m6 hm6
  wp_steps 2
  wp_str8 hf_21 m7 hm7
  wp_steps 4
  wp_str8 hf_26 m8 hm8
  wp_steps 2
  wp_str8 hf_29 m9 hm9
  wp_steps 2
  wp_str8 hf_32 m10 hm10
  wp_steps 3
  wp_str8 hf_36 m11 hm11
  wp_step
  wp_str8 hf_38 m12 hm12
  wp_steps 3
  wp_str8 hf_42 m13 hm13
  wp_steps 3
  wp_str8 hf_46 m14 hm14
  wp_steps 3
  wp_str8 hf_50 m15 hm15
  wp_step
  wp_str8 hf_52 m16 hm16
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
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by
          simp only [wp_norm, arm64_norm] at hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11 hm12 hm13 hm14 hm15 hm16 ⊢
          exact hm16.trans (hm15.trans (hm14.trans (hm13.trans (hm12.trans (hm11.trans (hm10.trans
            (hm9.trans (hm8.trans (hm7.trans (hm6.trans (hm5.trans (hm4.trans (hm3.trans
              (hm2.trans hm1)))))))))))))))))
  unfold bytes16At spill14At
  simp only [wp_norm, arm64_norm]

/-! ## 2. `cbc_quad_post3` (`fnAddr + 0x9d4#64 -> fnAddr + 0xacc#64`, 62 insns) -/

set_option maxHeartbeats 400000 in
theorem cbc_quad_post3 {P : Program} {fnAddr target_pc sp : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x9d4#64) (decodeWords cbcSoftQuadPost3Words))
    (d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47
     d48 d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62 d63
     c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
     c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 : BitVec 8)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x9d4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = d32.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = c16.zeroExtend 64)
    (hx11 : s.readReg64 .x11 = d35.zeroExtend 64)
    (hx12 : s.readReg64 .x12 = c17.zeroExtend 64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0xacc#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x8 = d52.zeroExtend 64 →
      sf.readReg64 .x9 = (d49 ^^^ c33).zeroExtend 64 →
      sf.readReg64 .x11 = d51.zeroExtend 64 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.pstate = s.pstate →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (bytes16At (sp + 0x890#64)
           (d32 ^^^ c16) (d33 ^^^ c17) (d34 ^^^ c18) (d35 ^^^ c19) (d36 ^^^ c20) (d37 ^^^ c21)
           (d38 ^^^ c22) (d39 ^^^ c23) (d40 ^^^ c24) (d41 ^^^ c25) (d42 ^^^ c26) (d43 ^^^ c27)
           (d44 ^^^ c28) (d45 ^^^ c29) (d46 ^^^ c30) (d47 ^^^ c31) ∗
         bytes16At (sp + 0x8a0#64)
           (d48 ^^^ c32) d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62 d63 ∗
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
         Rest)
        post oom) :
    SepWP P target_pc s
      (bytes16At (sp + 0x890#64) d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47 ∗
       bytes16At (sp + 0x8a0#64) d48 d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62 d63 ∗
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
       Rest)
      post oom := by
  have_instrs hc 0 62
  rw [bytes16At, bytes16At, spill14At, spill14At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 3
  wp_str8 hf_3 m1 hm1
  wp_steps 3
  wp_str8 hf_7 m2 hm2
  wp_steps 3
  wp_str8 hf_11 m3 hm3
  wp_step
  wp_str8 hf_13 m4 hm4
  wp_steps 3
  wp_str8 hf_17 m5 hm5
  wp_steps 3
  wp_str8 hf_21 m6 hm6
  wp_steps 3
  wp_str8 hf_25 m7 hm7
  wp_step
  wp_str8 hf_27 m8 hm8
  wp_steps 3
  wp_str8 hf_31 m9 hm9
  wp_steps 3
  wp_str8 hf_35 m10 hm10
  wp_steps 3
  wp_str8 hf_39 m11 hm11
  wp_step
  wp_str8 hf_41 m12 hm12
  wp_steps 3
  wp_str8 hf_45 m13 hm13
  wp_steps 3
  wp_str8 hf_49 m14 hm14
  wp_steps 6
  wp_str8 hf_56 m15 hm15
  wp_step
  wp_str8 hf_58 m16 hm16
  wp_steps 2
  wp_str8 hf_61 m17 hm17
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
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by
          simp only [wp_norm, arm64_norm] at hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11 hm12 hm13 hm14 hm15 hm16 hm17 ⊢
          exact hm17.trans (hm16.trans (hm15.trans (hm14.trans (hm13.trans (hm12.trans (hm11.trans
            (hm10.trans (hm9.trans (hm8.trans (hm7.trans (hm6.trans (hm5.trans (hm4.trans
              (hm3.trans (hm2.trans hm1))))))))))))))))))
  unfold bytes16At spill14At
  simp only [wp_norm, arm64_norm]

/-! ## 3. `cbc_quad_post4` (`fnAddr + 0xacc#64 -> fnAddr + 0xb9c#64`, 52 insns) -/

set_option maxHeartbeats 400000 in
theorem cbc_quad_post4 {P : Program} {fnAddr target_pc sp : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0xacc#64) (decodeWords cbcSoftQuadPost4Words))
    (d0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
     d48 d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62 d63
     p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
     c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 : BitVec 8)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0xacc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = d52.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = (d49 ^^^ c33).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = d51.zeroExtend 64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0xb9c#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x8 = (d0 ^^^ p0).zeroExtend 64 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.pstate = s.pstate →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (bytes16At (sp + 0x870#64) d0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 ∗
         bytes16At (sp + 0x8a0#64)
           (d48 ^^^ c32) (d49 ^^^ c33) (d50 ^^^ c34) (d51 ^^^ c35) (d52 ^^^ c36) (d53 ^^^ c37)
           (d54 ^^^ c38) (d55 ^^^ c39) (d56 ^^^ c40) (d57 ^^^ c41) (d58 ^^^ c42) (d59 ^^^ c43)
           (d60 ^^^ c44) (d61 ^^^ c45) (d62 ^^^ c46) (d63 ^^^ c47) ∗
         bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
         spill14At (sp + 0x0ac#64)
           (c35.zeroExtend 32) (c34.zeroExtend 32) (c36.zeroExtend 32) (c37.zeroExtend 32)
           (c39.zeroExtend 32) (c38.zeroExtend 32) (c40.zeroExtend 32) (c41.zeroExtend 32)
           (c43.zeroExtend 32) (c42.zeroExtend 32) (c44.zeroExtend 32) (c45.zeroExtend 32)
           (c47.zeroExtend 32) (c46.zeroExtend 32) ∗
         Rest)
        post oom) :
    SepWP P target_pc s
      (bytes16At (sp + 0x870#64) d0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 ∗
       bytes16At (sp + 0x8a0#64)
         (d48 ^^^ c32) d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62 d63 ∗
       bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
       spill14At (sp + 0x0ac#64)
         (c35.zeroExtend 32) (c34.zeroExtend 32) (c36.zeroExtend 32) (c37.zeroExtend 32)
         (c39.zeroExtend 32) (c38.zeroExtend 32) (c40.zeroExtend 32) (c41.zeroExtend 32)
         (c43.zeroExtend 32) (c42.zeroExtend 32) (c44.zeroExtend 32) (c45.zeroExtend 32)
         (c47.zeroExtend 32) (c46.zeroExtend 32) ∗
       Rest)
      post oom := by
  have_instrs hc 0 52
  rw [bytes16At, bytes16At, bytes16At, spill14At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 2
  wp_str8 hf_2 m1 hm1
  wp_steps 3
  wp_str8 hf_6 m2 hm2
  wp_step
  wp_str8 hf_8 m3 hm3
  wp_steps 3
  wp_str8 hf_12 m4 hm4
  wp_steps 3
  wp_str8 hf_16 m5 hm5
  wp_steps 3
  wp_str8 hf_20 m6 hm6
  wp_step
  wp_str8 hf_22 m7 hm7
  wp_steps 3
  wp_str8 hf_26 m8 hm8
  wp_steps 3
  wp_str8 hf_30 m9 hm9
  wp_steps 3
  wp_str8 hf_34 m10 hm10
  wp_step
  wp_str8 hf_36 m11 hm11
  wp_steps 3
  wp_str8 hf_40 m12 hm12
  wp_steps 4
  wp_str8 hf_45 m13 hm13
  wp_step
  wp_str8 hf_47 m14 hm14
  wp_steps 2
  wp_str8 hf_50 m15 hm15
  wp_step
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
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by
          simp only [wp_norm, arm64_norm] at hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11 hm12 hm13 hm14 hm15 ⊢
          exact hm15.trans (hm14.trans (hm13.trans (hm12.trans (hm11.trans (hm10.trans (hm9.trans
            (hm8.trans (hm7.trans (hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1))))))))))))))))
  unfold bytes16At spill14At
  simp only [wp_norm, arm64_norm]

/-! ## 4. `cbc_quad_post5` (`fnAddr + 0xb9c#64 -> fnAddr + 0xbc0#64 | fnAddr + 0x694#64`, 9 insns) -/

set_option maxHeartbeats 400000 in
theorem cbc_quad_post5 {P : Program} {fnAddr target_pc sp src dst rem1 : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0xb9c#64) (decodeWords cbcSoftQuadPost5Words))
    (w2 w3 w4 w5 w6 w7 cw6 cw7 pv0 pv1 z0 z1 z2 z3 z4 z5 z6 z7 : BitVec 64)
    (d0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : BitVec 8)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0xb9c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = y0.zeroExtend 64)
    (hx20 : s.readReg64 .x20 = dst)
    (hx22 : s.readReg64 .x22 = sp + 0xb40#64)
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hx26 : s.readReg64 .x26 = src + 0x18#64)
    (hx27 : s.readReg64 .x27 = rem1)
    (hpz : s.pstate.z = (rem1 == 0#64))
    (hnext : ∀ sf : State,
      sf.pc = (if rem1 == 0#64 then fnAddr + 0xbc0#64 else fnAddr + 0x694#64) →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x20 = dst + 64#64 →
      sf.readReg64 .x22 = sp + 0xb40#64 →
      sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x26 = src + 64#64 + 0x18#64 →
      sf.readReg64 .x27 = rem1 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (pts64x8At dst
           (pack8LE y0 y1 y2 y3 y4 y5 y6 y7) (pack8LE y8 y9 y10 y11 y12 y13 y14 y15)
           w2 w3 w4 w5 w6 w7 ∗
         ((sp + 0xf00#64) ↦₆₄ cw6) ∗ ((sp + 0xf08#64) ↦₆₄ cw7) ∗
         pts64x8At (sp + 0x870#64)
           (pack8LE y0 y1 y2 y3 y4 y5 y6 y7) (pack8LE y8 y9 y10 y11 y12 y13 y14 y15)
           w2 w3 w4 w5 w6 w7 ∗
         ((src + 48#64) ↦₆₄ cw6) ∗ ((src + 56#64) ↦₆₄ cw7) ∗
         Rest)
        post oom) :
    SepWP P target_pc s
      (bytes16At (sp + 0x870#64) d0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 ∗
       ((sp + 0x880#64) ↦₆₄ w2) ∗ ((sp + 0x888#64) ↦₆₄ w3) ∗
       ((sp + 0x890#64) ↦₆₄ w4) ∗ ((sp + 0x898#64) ↦₆₄ w5) ∗
       ((sp + 0x8a0#64) ↦₆₄ w6) ∗ ((sp + 0x8a8#64) ↦₆₄ w7) ∗
       ((src + 48#64) ↦₆₄ cw6) ∗ ((src + 56#64) ↦₆₄ cw7) ∗
       ((sp + 0xf00#64) ↦₆₄ pv0) ∗ ((sp + 0xf08#64) ↦₆₄ pv1) ∗
       pts64x8At dst z0 z1 z2 z3 z4 z5 z6 z7 ∗
       Rest)
      post oom := by
  have_instrs hc 0 9
  rw [bytes16At, pts64x8At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_step
  wp_str8 hf_1 m1 hm1
  refine sepWP_weaken_pre
    (Entails.of_eq (show _ =
      ((sp + 0x870#64) ↦₆₄ pack8LE y0 y1 y2 y3 y4 y5 y6 y7) ∗
      ((sp + 0x878#64) ↦₆₄ pack8LE y8 y9 y10 y11 y12 y13 y14 y15) ∗
      ((sp + 0x880#64) ↦₆₄ w2) ∗ ((sp + 0x888#64) ↦₆₄ w3) ∗
      ((sp + 0x890#64) ↦₆₄ w4) ∗ ((sp + 0x898#64) ↦₆₄ w5) ∗
      ((sp + 0x8a0#64) ↦₆₄ w6) ∗ ((sp + 0x8a8#64) ↦₆₄ w7) ∗
      ((src + 48#64) ↦₆₄ cw6) ∗ ((src + 56#64) ↦₆₄ cw7) ∗
      ((sp + 0xf00#64) ↦₆₄ pv0) ∗ ((sp + 0xf08#64) ↦₆₄ pv1) ∗
      (dst ↦₆₄ z0) ∗ ((dst + 8#64) ↦₆₄ z1) ∗ ((dst + 16#64) ↦₆₄ z2) ∗ ((dst + 24#64) ↦₆₄ z3) ∗
      ((dst + 32#64) ↦₆₄ z4) ∗ ((dst + 40#64) ↦₆₄ z5) ∗ ((dst + 48#64) ↦₆₄ z6) ∗ ((dst + 56#64) ↦₆₄ z7) ∗
      Rest by
      rw [pts64_pair_off_eq_bytes16At sp 0x870#64 0x878#64 (by bv_lin)]
      unfold bytes16At
      simp only [wp_norm, arm64_norm])) ?_
  generalize hw0 : pack8LE y0 y1 y2 y3 y4 y5 y6 y7 = w0
  generalize hw1 : pack8LE y8 y9 y10 y11 y12 y13 y14 y15 = w1
  wp_stp128 hf_2 m2 hm2
  wp_steps 3
  wp_stp128 hf_6 m3 hm3
  wp_str128 hf_7 m4 hm4
  wp_step
  wp_if h_ne
  · have hz_false : (rem1 == 0#64) = false := by
      simpa [ConditionHolds, wp_norm, arm64_norm, hpz] using h_ne
    refine sepWP_weaken_pre (Entails.of_eq ?_)
      (hnext _
        (by rw [hz_false]; simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hx22])
        (by simp [wp_norm, arm64_norm, hx24])
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hx27])
        (by simp [wp_norm, arm64_norm])
        (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
        (PureStepPreserved.of_proj_perm
          (by simp [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm] at hm1 hm2 hm3 hm4 ⊢; exact hm4.trans (hm3.trans (hm2.trans hm1)))))
    subst hw0 hw1
    unfold pts64x8At
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    sep_ac_rfl
  · have hz_true : (rem1 == 0#64) = true := by
      simpa [ConditionHolds, wp_norm, arm64_norm, hpz] using h_ne
    refine sepWP_weaken_pre (Entails.of_eq ?_)
      (hnext _
        (by rw [hz_true]; simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp])
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hx22])
        (by simp [wp_norm, arm64_norm, hx24])
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hx27])
        (by simp [wp_norm, arm64_norm])
        (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
        (PureStepPreserved.of_proj_perm
          (by simp [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm] at hm1 hm2 hm3 hm4 ⊢; exact hm4.trans (hm3.trans (hm2.trans hm1)))))
    subst hw0 hw1
    unfold pts64x8At
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    sep_ac_rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuadStepsB

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1b -- proof-setup: allow-public-import
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1c

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (SExpr SymCfg SymState symInit runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure (symUpperFwdNtt symBarrettMap checkNoSpillVreg checkAstEq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1a (cfgFwd1)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1b (symFwd1MidB)

@[expose] def symFwd1PreHi2 : SymState :=
  { symFwd1MidB with gprs := { symFwd1MidB.gprs with g8 := .gpr0 8 } }

@[expose] def symFwd1HiEnd : SymState :=
  let t0 : SExpr := .montmul (.poly 17) 0xfd0a#16
  let t1 : SExpr := .sub (.poly 1) t0
  let t2 : SExpr := .montmul (.poly 25) 0xfd0a#16
  let t3 : SExpr := .montmul (.sub (.poly 9) t2) 0xfa13#16
  let t4 : SExpr := .sub t1 t3
  let t5 : SExpr := .montmul (.poly 21) 0xfd0a#16
  let t6 : SExpr := .sub (.poly 5) t5
  let t7 : SExpr := .montmul (.poly 29) 0xfd0a#16
  let t8 : SExpr := .montmul (.sub (.poly 13) t7) 0xfa13#16
  let t9 : SExpr := .montmul (.sub t6 t8) 0x00ca#16
  let t10 : SExpr := .sub t4 t9
  let t11 : SExpr := .montmul (.poly 19) 0xfd0a#16
  let t12 : SExpr := .sub (.poly 3) t11
  let t13 : SExpr := .montmul (.poly 27) 0xfd0a#16
  let t14 : SExpr := .montmul (.sub (.poly 11) t13) 0xfa13#16
  let t15 : SExpr := .sub t12 t14
  let t16 : SExpr := .montmul (.poly 23) 0xfd0a#16
  let t17 : SExpr := .sub (.poly 7) t16
  let t18 : SExpr := .montmul (.poly 31) 0xfd0a#16
  let t19 : SExpr := .montmul (.sub (.poly 15) t18) 0xfa13#16
  let t20 : SExpr := .montmul (.sub t17 t19) 0x00ca#16
  let t21 : SExpr := .montmul (.sub t15 t20) 0x05bc#16
  let t22 : SExpr := .sub t10 t21
  let t23 : SExpr := .montmul t22 0xf9dd#16
  let t24 : SExpr := .montmul (.poly 16) 0xfd0a#16
  let t25 : SExpr := .sub (.poly 0) t24
  let t26 : SExpr := .montmul (.poly 24) 0xfd0a#16
  let t27 : SExpr := .montmul (.sub (.poly 8) t26) 0xfa13#16
  let t28 : SExpr := .sub t25 t27
  let t29 : SExpr := .montmul (.poly 20) 0xfd0a#16
  let t30 : SExpr := .sub (.poly 4) t29
  let t31 : SExpr := .montmul (.poly 28) 0xfd0a#16
  let t32 : SExpr := .montmul (.sub (.poly 12) t31) 0xfa13#16
  let t33 : SExpr := .montmul (.sub t30 t32) 0x00ca#16
  let t34 : SExpr := .sub t28 t33
  let t35 : SExpr := .montmul (.poly 18) 0xfd0a#16
  let t36 : SExpr := .sub (.poly 2) t35
  let t37 : SExpr := .montmul (.poly 26) 0xfd0a#16
  let t38 : SExpr := .montmul (.sub (.poly 10) t37) 0xfa13#16
  let t39 : SExpr := .sub t36 t38
  let t40 : SExpr := .montmul (.poly 22) 0xfd0a#16
  let t41 : SExpr := .sub (.poly 6) t40
  let t42 : SExpr := .montmul (.poly 30) 0xfd0a#16
  let t43 : SExpr := .montmul (.sub (.poly 14) t42) 0xfa13#16
  let t44 : SExpr := .montmul (.sub t41 t43) 0x00ca#16
  let t45 : SExpr := .montmul (.sub t39 t44) 0x05bc#16
  let t46 : SExpr := .sub t34 t45
  let t47 : SExpr := .add t23 t46
  let t48 : SExpr := .sub t46 t23
  let t49 : SExpr := .add t21 t10
  let t50 : SExpr := .montmul t49 0xff33#16
  let t51 : SExpr := .add t45 t34
  let t52 : SExpr := .add t50 t51
  let t53 : SExpr := .sub t51 t50
  let t54 : SExpr := .add t3 t1
  let t55 : SExpr := .montmul (.add t8 t6) 0x011f#16
  let t56 : SExpr := .sub t54 t55
  let t57 : SExpr := .add t14 t12
  let t58 : SExpr := .montmul (.add t19 t17) 0x011f#16
  let t59 : SExpr := .montmul (.sub t57 t58) 0xfb4e#16
  let t60 : SExpr := .montmul (.sub t56 t59) 0x0260#16
  let t61 : SExpr := .add t27 t25
  let t62 : SExpr := .montmul (.add t32 t30) 0x011f#16
  let t63 : SExpr := .sub t61 t62
  let t64 : SExpr := .add t38 t36
  let t65 : SExpr := .montmul (.add t43 t41) 0x011f#16
  let t66 : SExpr := .montmul (.sub t64 t65) 0xfb4e#16
  let t67 : SExpr := .sub t63 t66
  let t68 : SExpr := .add t60 t67
  let t69 : SExpr := .sshr (.sqdmulh t22 (.const 0xf9dd#16)) 1
  let t70 : SExpr := .sqdmulh t49 (.const 0xff33#16)
  let t71 : SExpr := .sqdmulh (.mul t22 (.const 0xc0dd#16)) (.const 0x0d01#16)
  let t72 : SExpr := .add t9 t4
  let t73 : SExpr := .montmul (.add t20 t15) 0xfa3e#16
  let t74 : SExpr := .sub t72 t73
  let t75 : SExpr := .sshr (.sqdmulh t74 (.const 0x019b#16)) 1
  let t76 : SExpr := .sqdmulh (.mul t49 (.const 0x6833#16)) (.const 0x0d01#16)
  let t77 : SExpr := .add t16 (.poly 7)
  let t78 : SExpr := .montmul (.add t18 (.poly 15)) 0xfe99#16
  let t79 : SExpr := .montmul (.sub t77 t78) 0x058e#16
  let t80 : SExpr := .add t11 (.poly 3)
  let t81 : SExpr := .montmul (.add t13 (.poly 11)) 0xfe99#16
  let t82 : SExpr := .sub t80 t81
  let t83 : SExpr := .montmul (.add t79 t82) 0x0629#16
  let t84 : SExpr := .add t5 (.poly 5)
  let t85 : SExpr := .montmul (.add t7 (.poly 13)) 0xfe99#16
  let t86 : SExpr := .montmul (.sub t84 t85) 0x058e#16
  let t87 : SExpr := .add t0 (.poly 1)
  let t88 : SExpr := .montmul (.add t2 (.poly 9)) 0xfe99#16
  let t89 : SExpr := .sub t87 t88
  let t90 : SExpr := .add t86 t89
  let t91 : SExpr := .add t83 t90
  let t92 : SExpr := .montmul (.add t78 t77) 0x05d5#16
  let t93 : SExpr := .add t81 t80
  let t94 : SExpr := .montmul (.add t92 t93) 0xff55#16
  let t95 : SExpr := .montmul (.add t85 t84) 0x05d5#16
  let t96 : SExpr := .add t88 t87
  let t97 : SExpr := .add t95 t96
  let t98 : SExpr := .montmul (.add t94 t97) 0x023d#16
  let t99 : SExpr := .montmul (.add t42 (.poly 14)) 0xfe99#16
  let t100 : SExpr := .add t40 (.poly 6)
  let t101 : SExpr := .montmul (.add t99 t100) 0x05d5#16
  let t102 : SExpr := .montmul (.add t37 (.poly 10)) 0xfe99#16
  let t103 : SExpr := .add t35 (.poly 2)
  let t104 : SExpr := .add t102 t103
  let t105 : SExpr := .montmul (.add t101 t104) 0xff55#16
  let t106 : SExpr := .montmul (.add t31 (.poly 12)) 0xfe99#16
  let t107 : SExpr := .add t29 (.poly 4)
  let t108 : SExpr := .montmul (.add t106 t107) 0x05d5#16
  let t109 : SExpr := .montmul (.add t26 (.poly 8)) 0xfe99#16
  let t110 : SExpr := .add t24 (.poly 0)
  let t111 : SExpr := .add t109 t110
  let t112 : SExpr := .add t108 t111
  let t113 : SExpr := .add t105 t112
  let t114 : SExpr := .montmul (.sub t97 t94) 0xfad3#16
  let t115 : SExpr := .sub t112 t105
  let t116 : SExpr := .montmul (.sub t93 t92) 0x026e#16
  let t117 : SExpr := .sub t96 t95
  let t118 : SExpr := .montmul (.add t116 t117) 0x0108#16
  let t119 : SExpr := .montmul (.sub t104 t101) 0x026e#16
  let t120 : SExpr := .sub t111 t108
  let t121 : SExpr := .add t119 t120
  let t122 : SExpr := .montmul (.sub t117 t116) 0x017f#16
  let t123 : SExpr := .sub t120 t119
  let t124 : SExpr := .montmul t91 0xfcc3#16
  let t125 : SExpr := .montmul (.sub t100 t99) 0x058e#16
  let t126 : SExpr := .sub t103 t102
  let t127 : SExpr := .montmul (.add t125 t126) 0x0629#16
  let t128 : SExpr := .montmul (.sub t107 t106) 0x058e#16
  let t129 : SExpr := .sub t110 t109
  let t130 : SExpr := .add t128 t129
  let t131 : SExpr := .add t127 t130
  let t132 : SExpr := .montmul (.sub t90 t83) 0x05b2#16
  let t133 : SExpr := .sub t130 t127
  let t134 : SExpr := .montmul (.sub t82 t79) 0x00b6#16
  let t135 : SExpr := .sub t89 t86
  let t136 : SExpr := .montmul (.add t134 t135) 0xf9be#16
  let t137 : SExpr := .montmul (.sub t126 t125) 0x00b6#16
  let t138 : SExpr := .sub t129 t128
  let t139 : SExpr := .add t137 t138
  let t140 : SExpr := .montmul (.sub t135 t134) 0xff7e#16
  let t141 : SExpr := .sub t138 t137
  let t142 : SExpr := .montmul (.add t58 t57) 0x03c2#16
  let t143 : SExpr := .add t55 t54
  let t144 : SExpr := .montmul (.add t142 t143) 0xfd57#16
  let t145 : SExpr := .montmul (.add t65 t64) 0x03c2#16
  let t146 : SExpr := .add t62 t61
  let t147 : SExpr := .add t145 t146
  let t148 : SExpr := .montmul (.sub t143 t142) 0x03f9#16
  let t149 : SExpr := .sub t146 t145
  let t150 : SExpr := .montmul (.add t59 t56) 0x02dc#16
  let t151 : SExpr := .add t66 t63
  let t152 : SExpr := .montmul (.add t73 t72) 0xf9fa#16
  let t153 : SExpr := .montmul (.add t44 t39) 0xfa3e#16
  let t154 : SExpr := .add t33 t28
  let t155 : SExpr := .add t153 t154
  let t156 : SExpr := .montmul t74 0x019b#16
  let t157 : SExpr := .sub t154 t153
  { vregs := ⟨t47, t48, t52, t23,
     t53, t50, t68, t69,
     .vreg0 8, .const 0x011f#16, .const 0x6e1f#16, .const 0x0d01#16,
     .const 0xcf8e#16, .const 0x34d5#16, .vreg0 14, .vreg0 15,
     .sshr t70 1, .sshr t71 1, t71, t75,
     .sshr t76 1, t76, .const 0xf9dd#16, t70,
     t51, t22, t46, .const 0xff33#16,
     .const 0x29c2#16, t91, .const 0x00b6#16, .const 0xf129#16⟩
    spill13 := ⟨.spill13_0 0, .spill13_0 1, .spill13_0 2, .spill13_0 3,
     .spill13_0 4, .spill13_0 5, .spill13_0 6, .spill13_0 7,
     .spill13_0 8, .spill13_0 9, .spill13_0 10, .spill13_0 11,
     .spill13_0 12⟩
    spill6 := ⟨.spill6_0 0, .spill6_0 1, .spill6_0 2, .spill6_0 3,
     .spill6_0 4, .spill6_0 5⟩
    spill21 := ⟨.const 0x03c2#16, .const 0xc2b6#16, .const 0xf129#16, .const 0x0629#16,
     .const 0x6c6e#16, .const 0x026e#16, .const 0xae55#16, .const 0xbeca#16,
     .const 0x6e1f#16, .const 0x011f#16, .const 0xcf8e#16, .const 0x058e#16,
     .const 0x34d5#16, .const 0x05d5#16, .const 0x0313#16, .const 0xfa13#16,
     .const 0x3999#16, .const 0xfe99#16, .const 0x0d01#16, .const 0x7b0a#16,
     .const 0xfd0a#16⟩
    poly := ⟨.add t98 t113, .sub t113 t98, .add t114 t115, .sub t115 t114,
     .add t118 t121, .sub t121 t118, .add t122 t123, .sub t123 t122,
     .add t124 t131, .sub t131 t124, .add t132 t133, .sub t133 t132,
     .add t136 t139, .sub t139 t136, .add t140 t141, .sub t141 t140,
     .add t144 t147, .sub t147 t144, .add t148 t149, .sub t149 t148,
     .add t150 t151, .sub t151 t150, t68, .sub t67 t60,
     .add t152 t155, .sub t155 t152, .add t156 t157, .sub t157 t156,
     t52, t53, t47, t48⟩
    gprs := ⟨.gpr0 0, .gpr0 1, .gpr0 2, .gpr0 3, .gpr0 4, .gpr0 5,
     .gpr0 6, .gpr0 7, .gpr0 8, .gpr0 23, .const64 16#64, .gpr0 11,
     .gpr0 12, .gpr0 13, .gpr0 14, .gpr0 15, .gpr0 16, .gpr0 17,
     .gpr0 18, .gpr0 19, .gpr0 20, .gpr0 21, .gpr0 22, .gpr0 23,
     .gpr0 24, .gpr0 25, .gpr0 26, .gpr0 27, .gpr0 28, .gpr0 29,
     .gpr0 30⟩
    pstate := .pstate0 }

theorem run_fwd1_hi2 : runSymRange cfgFwd1 1306 27 symFwd1PreHi2 = some symFwd1HiEnd := by
  rfl_kernel

theorem fwd1_hi_noSpillVreg : checkNoSpillVreg symFwd1HiEnd.poly = true := by rfl_kernel

set_option maxRecDepth 40000 in
theorem fwd1_hi_ast_eq : checkAstEq symFwd1HiEnd.poly symUpperFwdNtt = true := by rfl_kernel

@[expose] def cfgFwd1Tail : SymCfg := ⟨some 21#5, .none, false⟩

@[expose] def symFwd1TailEnd : SymState :=
  let t0 : SExpr := .add (.sqdmulh (.poly 31) (.const 0x4ebf#16)) (.const 0x0400#16)
  let t1 : SExpr := .sqdmulh (.poly 30) (.const 0x4ebf#16)
  let t2 : SExpr := .add t1 (.const 0x0400#16)
  let t3 : SExpr := .barrett (.poly 23)
  let t4 : SExpr := .barrett (.poly 24)
  let t5 : SExpr := .barrett (.poly 25)
  let t6 : SExpr := .barrett (.poly 26)
  let t7 : SExpr := .barrett (.poly 27)
  let t8 : SExpr := .sqdmulh (.poly 28) (.const 0x4ebf#16)
  let t9 : SExpr := .add t8 (.const 0x0400#16)
  let t10 : SExpr := .sqdmulh (.poly 29) (.const 0x4ebf#16)
  let t11 : SExpr := .add t10 (.const 0x0400#16)
  let t12 : SExpr := .add (.sqdmulh (.poly 27) (.const 0x4ebf#16)) (.const 0x0400#16)
  let t13 : SExpr := .barrett (.poly 28)
  let t14 : SExpr := .barrett (.poly 29)
  let t15 : SExpr := .barrett (.poly 30)
  let t16 : SExpr := .barrett (.poly 31)
  { vregs := ⟨.sshr t0 11, .sshr t2 11, t3, t4,
     t5, t6, t7, .sshr t9 11,
     .vreg0 8, .vreg0 9, .vreg0 10, .vreg0 11,
     .vreg0 12, .vreg0 13, .vreg0 14, .vreg0 15,
     .sshr t11 11, .sshr t12 11, t9, t11,
     t13, t2, t14, t8,
     t15, t10, t16, t1,
     .sqdmulh (.poly 20) (.const 0x4ebf#16), .sqdmulh (.poly 21) (.const 0x4ebf#16), .const 0x0400#16, .const 0xf2ff#16⟩
    spill13 := ⟨.spill13_0 0, .spill13_0 1, .spill13_0 2, .spill13_0 3,
     .spill13_0 4, .spill13_0 5, .spill13_0 6, .spill13_0 7,
     .spill13_0 8, .spill13_0 9, .spill13_0 10, .spill13_0 11,
     .spill13_0 12⟩
    spill6 := ⟨.spill6_0 0, .spill6_0 1, .spill6_0 2, .spill6_0 3,
     .spill6_0 4, .spill6_0 5⟩
    spill21 := ⟨.spill21_0 0, .spill21_0 1, .spill21_0 2, .spill21_0 3,
     .spill21_0 4, .spill21_0 5, .spill21_0 6, .spill21_0 7,
     .spill21_0 8, .spill21_0 9, .spill21_0 10, .spill21_0 11,
     .spill21_0 12, .spill21_0 13, .spill21_0 14, .spill21_0 15,
     .spill21_0 16, .spill21_0 17, .spill21_0 18, .spill21_0 19,
     .spill21_0 20⟩
    poly := ⟨.barrett (.poly 0), .barrett (.poly 1), .barrett (.poly 2), .barrett (.poly 3),
     .barrett (.poly 4), .barrett (.poly 5), .barrett (.poly 6), .barrett (.poly 7),
     .barrett (.poly 8), .barrett (.poly 9), .barrett (.poly 10), .barrett (.poly 11),
     .barrett (.poly 12), .barrett (.poly 13), .barrett (.poly 14), .barrett (.poly 15),
     .barrett (.poly 16), .barrett (.poly 17), .barrett (.poly 18), .barrett (.poly 19),
     .barrett (.poly 20), .barrett (.poly 21), .barrett (.poly 22), t3,
     t4, t5, t6, t7,
     t13, t14, t15, t16⟩
    gprs := ⟨.gpr0 0, .gpr0 1, .gpr0 2, .gpr0 3, .gpr0 4, .gpr0 5,
     .gpr0 6, .gpr0 7, .gpr0 19, .gpr0 9, .gpr0 10, .gpr0 11,
     .gpr0 12, .gpr0 13, .gpr0 14, .gpr0 15, .gpr0 16, .gpr0 17,
     .gpr0 18, .gpr0 19, .gpr0 20, .gpr0 21, .gpr0 22, .addImm (.gpr0 23) 512#64,
     .addImm (.gpr0 24) 512#64, .addImm (.gpr0 25) 320#64, .gpr0 26, .gpr0 27, .gpr0 28, .gpr0 29,
     .gpr0 30⟩
    pstate := .cmpImm64 (.gpr0 19) 3#64 }

theorem run_fwd1_tail : runSymRange cfgFwd1Tail 1393 169 symInit = some symFwd1TailEnd := by
  rfl_kernel

theorem fwd1_tail_noSpillVreg : checkNoSpillVreg symFwd1TailEnd.poly = true := by rfl_kernel

theorem fwd1_tail_ast_eq : checkAstEq symFwd1TailEnd.poly symBarrettMap = true := by rfl_kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1c

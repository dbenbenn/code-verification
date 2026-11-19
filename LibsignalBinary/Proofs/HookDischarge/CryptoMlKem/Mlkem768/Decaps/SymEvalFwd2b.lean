/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2a -- proof-setup: allow-public-import
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2b

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (SExpr SymState runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure (symUpperFwdNttBinomial checkNoSpillVreg checkAstEq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2a (cfgFwd2 symFwd2MidA)

@[expose] def symFwd2HiEnd : SymState :=
  let t0 : SExpr := .mul (.inPoly 17) (.const 0xf9c0#16)
  let t1 : SExpr := .sub (.inPoly 1) t0
  let t2 : SExpr := .mul (.inPoly 25) (.const 0xf9c0#16)
  let t3 : SExpr := .montmul (.sub (.inPoly 9) t2) 0xfa13#16
  let t4 : SExpr := .sub t1 t3
  let t5 : SExpr := .mul (.inPoly 21) (.const 0xf9c0#16)
  let t6 : SExpr := .sub (.inPoly 5) t5
  let t7 : SExpr := .mul (.inPoly 29) (.const 0xf9c0#16)
  let t8 : SExpr := .montmul (.sub (.inPoly 13) t7) 0xfa13#16
  let t9 : SExpr := .sub t6 t8
  let t10 : SExpr := .montmul t9 0x00ca#16
  let t11 : SExpr := .sub t4 t10
  let t12 : SExpr := .mul (.inPoly 19) (.const 0xf9c0#16)
  let t13 : SExpr := .sub (.inPoly 3) t12
  let t14 : SExpr := .mul (.inPoly 27) (.const 0xf9c0#16)
  let t15 : SExpr := .montmul (.sub (.inPoly 11) t14) 0xfa13#16
  let t16 : SExpr := .sub t13 t15
  let t17 : SExpr := .mul (.inPoly 23) (.const 0xf9c0#16)
  let t18 : SExpr := .sub (.inPoly 7) t17
  let t19 : SExpr := .mul (.inPoly 31) (.const 0xf9c0#16)
  let t20 : SExpr := .montmul (.sub (.inPoly 15) t19) 0xfa13#16
  let t21 : SExpr := .sub t18 t20
  let t22 : SExpr := .montmul t21 0x00ca#16
  let t23 : SExpr := .montmul (.sub t16 t22) 0x05bc#16
  let t24 : SExpr := .sub t11 t23
  let t25 : SExpr := .montmul t24 0xf9dd#16
  let t26 : SExpr := .mul (.inPoly 16) (.const 0xf9c0#16)
  let t27 : SExpr := .sub (.inPoly 0) t26
  let t28 : SExpr := .mul (.inPoly 24) (.const 0xf9c0#16)
  let t29 : SExpr := .montmul (.sub (.inPoly 8) t28) 0xfa13#16
  let t30 : SExpr := .sub t27 t29
  let t31 : SExpr := .mul (.inPoly 20) (.const 0xf9c0#16)
  let t32 : SExpr := .sub (.inPoly 4) t31
  let t33 : SExpr := .mul (.inPoly 28) (.const 0xf9c0#16)
  let t34 : SExpr := .montmul (.sub (.inPoly 12) t33) 0xfa13#16
  let t35 : SExpr := .montmul (.sub t32 t34) 0x00ca#16
  let t36 : SExpr := .sub t30 t35
  let t37 : SExpr := .mul (.inPoly 18) (.const 0xf9c0#16)
  let t38 : SExpr := .sub (.inPoly 2) t37
  let t39 : SExpr := .mul (.inPoly 26) (.const 0xf9c0#16)
  let t40 : SExpr := .montmul (.sub (.inPoly 10) t39) 0xfa13#16
  let t41 : SExpr := .sub t38 t40
  let t42 : SExpr := .mul (.inPoly 22) (.const 0xf9c0#16)
  let t43 : SExpr := .sub (.inPoly 6) t42
  let t44 : SExpr := .mul (.inPoly 30) (.const 0xf9c0#16)
  let t45 : SExpr := .montmul (.sub (.inPoly 14) t44) 0xfa13#16
  let t46 : SExpr := .sub t43 t45
  let t47 : SExpr := .montmul t46 0x00ca#16
  let t48 : SExpr := .montmul (.sub t41 t47) 0x05bc#16
  let t49 : SExpr := .sub t36 t48
  let t50 : SExpr := .add t25 t49
  let t51 : SExpr := .sub t49 t25
  let t52 : SExpr := .add t23 t11
  let t53 : SExpr := .montmul t52 0xff33#16
  let t54 : SExpr := .add t48 t36
  let t55 : SExpr := .add t53 t54
  let t56 : SExpr := .sub t54 t53
  let t57 : SExpr := .sshr (.sqdmulh t24 (.const 0xf9dd#16)) 1
  let t58 : SExpr := .montmul (.add t34 t32) 0x011f#16
  let t59 : SExpr := .add t29 t27
  let t60 : SExpr := .add t58 t59
  let t61 : SExpr := .add (.inPoly 7) t17
  let t62 : SExpr := .montmul (.add (.inPoly 15) t19) 0xfe99#16
  let t63 : SExpr := .montmul (.sub t61 t62) 0x058e#16
  let t64 : SExpr := .add (.inPoly 3) t12
  let t65 : SExpr := .montmul (.add (.inPoly 11) t14) 0xfe99#16
  let t66 : SExpr := .sub t64 t65
  let t67 : SExpr := .add t63 t66
  let t68 : SExpr := .montmul (.add (.inPoly 9) t2) 0xfe99#16
  let t69 : SExpr := .add (.inPoly 1) t0
  let t70 : SExpr := .add t68 t69
  let t71 : SExpr := .montmul (.add (.inPoly 13) t7) 0xfe99#16
  let t72 : SExpr := .add (.inPoly 5) t5
  let t73 : SExpr := .montmul (.add t71 t72) 0x05d5#16
  let t74 : SExpr := .sub t70 t73
  let t75 : SExpr := .sub t66 t63
  let t76 : SExpr := .add (.inPoly 2) t37
  let t77 : SExpr := .montmul (.add (.inPoly 10) t39) 0xfe99#16
  let t78 : SExpr := .sub t76 t77
  let t79 : SExpr := .add (.inPoly 6) t42
  let t80 : SExpr := .montmul (.add (.inPoly 14) t44) 0xfe99#16
  let t81 : SExpr := .montmul (.sub t79 t80) 0x058e#16
  let t82 : SExpr := .sub t78 t81
  let t83 : SExpr := .add t3 t1
  let t84 : SExpr := .montmul (.add t8 t6) 0x011f#16
  let t85 : SExpr := .sub t83 t84
  let t86 : SExpr := .add t15 t13
  let t87 : SExpr := .montmul (.add t20 t18) 0x011f#16
  let t88 : SExpr := .sub t86 t87
  let t89 : SExpr := .montmul t88 0xfb4e#16
  let t90 : SExpr := .montmul (.sub t85 t89) 0x0260#16
  let t91 : SExpr := .sub t59 t58
  let t92 : SExpr := .add t40 t38
  let t93 : SExpr := .montmul (.add t45 t43) 0x011f#16
  let t94 : SExpr := .sub t92 t93
  let t95 : SExpr := .montmul t94 0xfb4e#16
  let t96 : SExpr := .sub t91 t95
  let t97 : SExpr := .add t90 t96
  let t98 : SExpr := .sqdmulh (.mul t24 (.const 0xc0dd#16)) (.const 0x0d01#16)
  let t99 : SExpr := .sqdmulh t52 (.const 0xff33#16)
  let t100 : SExpr := .add t10 t4
  let t101 : SExpr := .montmul (.add t22 t16) 0xfa3e#16
  let t102 : SExpr := .sub t100 t101
  let t103 : SExpr := .sqdmulh (.mul t102 (.const 0x229b#16)) (.const 0x0d01#16)
  let t104 : SExpr := .sqdmulh (.mul t52 (.const 0x6833#16)) (.const 0x0d01#16)
  let t105 : SExpr := .sqdmulh (.mul t94 (.const 0x054e#16)) (.const 0x0d01#16)
  let t106 : SExpr := .sqdmulh (.mul t88 (.const 0x054e#16)) (.const 0x0d01#16)
  let t107 : SExpr := .montmul (.add (.inPoly 8) t28) 0xfe99#16
  let t108 : SExpr := .add (.inPoly 0) t26
  let t109 : SExpr := .add t107 t108
  let t110 : SExpr := .sub t108 t107
  let t111 : SExpr := .sub t69 t68
  let t112 : SExpr := .montmul (.add t62 t61) 0x05d5#16
  let t113 : SExpr := .add t65 t64
  let t114 : SExpr := .montmul (.add t112 t113) 0xff55#16
  let t115 : SExpr := .add t73 t70
  let t116 : SExpr := .montmul (.add t114 t115) 0x023d#16
  let t117 : SExpr := .montmul (.add t80 t79) 0x05d5#16
  let t118 : SExpr := .add t77 t76
  let t119 : SExpr := .montmul (.add t117 t118) 0xff55#16
  let t120 : SExpr := .montmul (.add (.inPoly 12) t33) 0xfe99#16
  let t121 : SExpr := .add (.inPoly 4) t31
  let t122 : SExpr := .montmul (.add t120 t121) 0x05d5#16
  let t123 : SExpr := .add t122 t109
  let t124 : SExpr := .add t119 t123
  let t125 : SExpr := .montmul (.sub t115 t114) 0xfad3#16
  let t126 : SExpr := .sub t123 t119
  let t127 : SExpr := .montmul (.sub t113 t112) 0x026e#16
  let t128 : SExpr := .montmul (.add t127 t74) 0x0108#16
  let t129 : SExpr := .montmul (.sub t118 t117) 0x026e#16
  let t130 : SExpr := .sub t109 t122
  let t131 : SExpr := .add t129 t130
  let t132 : SExpr := .montmul (.sub t74 t127) 0x017f#16
  let t133 : SExpr := .sub t130 t129
  let t134 : SExpr := .montmul t67 0x0629#16
  let t135 : SExpr := .montmul (.sub t72 t71) 0x058e#16
  let t136 : SExpr := .add t135 t111
  let t137 : SExpr := .montmul (.add t134 t136) 0xfcc3#16
  let t138 : SExpr := .montmul (.add t81 t78) 0x0629#16
  let t139 : SExpr := .montmul (.sub t121 t120) 0x058e#16
  let t140 : SExpr := .add t139 t110
  let t141 : SExpr := .add t138 t140
  let t142 : SExpr := .montmul (.sub t136 t134) 0x05b2#16
  let t143 : SExpr := .sub t140 t138
  let t144 : SExpr := .montmul t75 0x00b6#16
  let t145 : SExpr := .sub t111 t135
  let t146 : SExpr := .montmul (.add t144 t145) 0xf9be#16
  let t147 : SExpr := .montmul t82 0x00b6#16
  let t148 : SExpr := .sub t110 t139
  let t149 : SExpr := .add t147 t148
  let t150 : SExpr := .montmul (.sub t145 t144) 0xff7e#16
  let t151 : SExpr := .sub t148 t147
  let t152 : SExpr := .montmul (.add t87 t86) 0x03c2#16
  let t153 : SExpr := .add t84 t83
  let t154 : SExpr := .montmul (.add t152 t153) 0xfd57#16
  let t155 : SExpr := .montmul (.add t93 t92) 0x03c2#16
  let t156 : SExpr := .add t155 t60
  let t157 : SExpr := .montmul (.sub t153 t152) 0x03f9#16
  let t158 : SExpr := .sub t60 t155
  let t159 : SExpr := .montmul (.add t89 t85) 0x02dc#16
  let t160 : SExpr := .add t95 t91
  let t161 : SExpr := .montmul (.add t101 t100) 0xf9fa#16
  let t162 : SExpr := .montmul (.add t47 t41) 0xfa3e#16
  let t163 : SExpr := .add t35 t30
  let t164 : SExpr := .add t162 t163
  let t165 : SExpr := .montmul t102 0x019b#16
  let t166 : SExpr := .sub t163 t162
  { vregs := ⟨t50, t51, t55, .const 0x0d01#16,
     t25, t56, t57, t53,
     t60, t41, t16, .mul t67 (.const 0xf129#16),
     t74, .const 0x00ca#16, t75, t82,
     t97, .sshr t98 1, .sshr t99 1, .sshr t103 1,
     t98, .sshr t104 1, t104, .const 0xf9dd#16,
     t99, t54, t24, t49,
     .const 0xff33#16, t105, .sqdmulh t88 (.const 0xfb4e#16), t106⟩
    spill13 := ⟨.const 0xd43e#16, .const 0xfa3e#16, .const 0x054e#16, .const 0xfb4e#16,
     .const 0x29c2#16, .const 0x03c2#16, .const 0xc2b6#16, .const 0xf129#16,
     .const 0x0629#16, .const 0x6c6e#16, .const 0x026e#16, .const 0xae55#16,
     .const 0xbeca#16⟩
    spill6 := ⟨.const 0x6e1f#16, .const 0x011f#16, .const 0xcf8e#16, .const 0x058e#16,
     .const 0x34d5#16, .const 0x05d5#16⟩
    spill21 := ⟨.const 0x0313#16, .const 0xfa13#16, .const 0x3999#16, .const 0xfe99#16,
     .const 0xf9c0#16, t109, t83, t59,
     t110, t111, t32, t9,
     t46, t66, t21, t85,
     t91, t16, t41, t30,
     t4⟩
    poly := ⟨.add t116 t124, .sub t124 t116, .add t125 t126, .sub t126 t125,
     .add t128 t131, .sub t131 t128, .add t132 t133, .sub t133 t132,
     .add t137 t141, .sub t141 t137, .add t142 t143, .sub t143 t142,
     .add t146 t149, .sub t149 t146, .add t150 t151, .sub t151 t150,
     .add t154 t156, .sub t156 t154, .add t157 t158, .sub t158 t157,
     .add t159 t160, .sub t160 t159, t97, .sub t96 t90,
     .add t161 t164, .sub t164 t161, .add t165 t166, .sub t166 t165,
     t55, t56, t50, t51⟩
    gprs := ⟨.gpr0 0, .gpr0 1, .gpr0 2, .gpr0 3, .gpr0 4, .gpr0 5,
     .gpr0 9, .gpr0 7, .gpr0 0, .gpr0 9, .gpr0 10, .gpr0 11,
     .const64 63994#64, .const64 18426#64, .const64 411#64, .const64 8859#64, .const64 26675#64, .const64 63965#64,
     .const64 49373#64, .gpr0 19, .gpr0 20, .gpr0 21, .const64 16#64, .gpr0 23,
     .gpr0 24, .gpr0 25, .gpr0 26, .gpr0 27, .gpr0 28, .gpr0 29,
     .gpr0 30⟩
    pstate := .pstate0 }

theorem run_fwd2b : runSymRange cfgFwd2 7947 391 symFwd2MidA = some symFwd2HiEnd := by
  rfl_kernel

theorem fwd2_hi_noSpillVreg : checkNoSpillVreg symFwd2HiEnd.poly = true := by rfl_kernel

set_option maxRecDepth 40000 in
theorem fwd2_hi_ast_eq : checkAstEq symFwd2HiEnd.poly symUpperFwdNttBinomial = true := by rfl_kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2b

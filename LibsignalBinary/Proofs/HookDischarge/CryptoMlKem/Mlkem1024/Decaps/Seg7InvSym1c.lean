/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvSym1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvSym1b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvSym1c

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (SExpr SymState runSymRange runSymRange_append)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast (runSymRange_of_fast)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (symUpperInvNtt polyNoSpillVreg polyAstEq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvSym1a (cfgSeg7InvSym symSeg7InvSymInit run_seg7_inv1a)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvSym1b (symSeg7InvSymMidB run_seg7_inv1b)

@[expose] def symSeg7InvSymEnd : SymState :=
  let t0 : SExpr := .montmul (.sub (.poly 31) (.poly 30)) 0x023d#16
  let t1 : SExpr := .montmul (.sub (.poly 29) (.poly 28)) 0xfad3#16
  let t2 : SExpr := .montmul (.sub t0 t1) 0xff55#16
  let t3 : SExpr := .montmul (.sub (.poly 27) (.poly 26)) 0x0108#16
  let t4 : SExpr := .montmul (.sub (.poly 25) (.poly 24)) 0x017f#16
  let t5 : SExpr := .montmul (.sub t3 t4) 0x026e#16
  let t6 : SExpr := .montmul (.sub t2 t5) 0x05d5#16
  let t7 : SExpr := .montmul (.sub (.poly 23) (.poly 22)) 0xfcc3#16
  let t8 : SExpr := .montmul (.sub (.poly 21) (.poly 20)) 0x05b2#16
  let t9 : SExpr := .montmul (.sub t7 t8) 0x0629#16
  let t10 : SExpr := .montmul (.sub (.poly 19) (.poly 18)) 0xf9be#16
  let t11 : SExpr := .montmul (.sub (.poly 17) (.poly 16)) 0xff7e#16
  let t12 : SExpr := .montmul (.sub t10 t11) 0x00b6#16
  let t13 : SExpr := .montmul (.sub t9 t12) 0x058e#16
  let t14 : SExpr := .montmul (.sub t6 t13) 0xfe99#16
  let t15 : SExpr := .montmul (.sub (.poly 15) (.poly 14)) 0xfd57#16
  let t16 : SExpr := .montmul (.sub (.poly 13) (.poly 12)) 0x03f9#16
  let t17 : SExpr := .montmul (.sub t15 t16) 0x03c2#16
  let t18 : SExpr := .montmul (.sub (.poly 11) (.poly 10)) 0x02dc#16
  let t19 : SExpr := .montmul (.sub (.poly 9) (.poly 8)) 0x0260#16
  let t20 : SExpr := .montmul (.sub t18 t19) 0xfb4e#16
  let t21 : SExpr := .montmul (.sub t17 t20) 0x011f#16
  let t22 : SExpr := .montmul (.sub (.poly 7) (.poly 6)) 0xf9fa#16
  let t23 : SExpr := .montmul (.sub (.poly 5) (.poly 4)) 0x019b#16
  let t24 : SExpr := .montmul (.sub t22 t23) 0xfa3e#16
  let t25 : SExpr := .montmul (.sub (.poly 3) (.poly 2)) 0xff33#16
  let t26 : SExpr := .montmul (.sub (.poly 1) (.poly 0)) 0xf9dd#16
  let t27 : SExpr := .montmul (.sub t25 t26) 0x05bc#16
  let t28 : SExpr := .montmul (.sub t24 t27) 0x00ca#16
  let t29 : SExpr := .montmul (.sub t21 t28) 0xfa13#16
  let t30 : SExpr := .montmul (.sub t14 t29) 0xfd0a#16
  let t31 : SExpr := .sqdmulh t30 (.const 0x4ebf#16)
  let t32 : SExpr := .add t31 (.const 0x0400#16)
  let t33 : SExpr := .add (.poly 30) (.poly 31)
  let t34 : SExpr := .add (.poly 28) (.poly 29)
  let t35 : SExpr := .barrett (.add t33 t34)
  let t36 : SExpr := .add (.poly 26) (.poly 27)
  let t37 : SExpr := .add (.poly 24) (.poly 25)
  let t38 : SExpr := .barrett (.add t36 t37)
  let t39 : SExpr := .montmul (.sub t35 t38) 0x05d5#16
  let t40 : SExpr := .add (.poly 22) (.poly 23)
  let t41 : SExpr := .add (.poly 20) (.poly 21)
  let t42 : SExpr := .barrett (.add t40 t41)
  let t43 : SExpr := .add (.poly 18) (.poly 19)
  let t44 : SExpr := .add (.poly 16) (.poly 17)
  let t45 : SExpr := .barrett (.add t43 t44)
  let t46 : SExpr := .montmul (.sub t42 t45) 0x058e#16
  let t47 : SExpr := .montmul (.sub t39 t46) 0xfe99#16
  let t48 : SExpr := .add (.poly 14) (.poly 15)
  let t49 : SExpr := .add (.poly 12) (.poly 13)
  let t50 : SExpr := .barrett (.add t48 t49)
  let t51 : SExpr := .add (.poly 10) (.poly 11)
  let t52 : SExpr := .add (.poly 8) (.poly 9)
  let t53 : SExpr := .barrett (.add t51 t52)
  let t54 : SExpr := .montmul (.sub t50 t53) 0x011f#16
  let t55 : SExpr := .add (.poly 6) (.poly 7)
  let t56 : SExpr := .add (.poly 4) (.poly 5)
  let t57 : SExpr := .barrett (.add t55 t56)
  let t58 : SExpr := .add (.poly 2) (.poly 3)
  let t59 : SExpr := .add (.poly 0) (.poly 1)
  let t60 : SExpr := .barrett (.add t58 t59)
  let t61 : SExpr := .montmul (.sub t57 t60) 0x00ca#16
  let t62 : SExpr := .montmul (.sub t54 t61) 0xfa13#16
  let t63 : SExpr := .montmul (.sub t47 t62) 0xfd0a#16
  let t64 : SExpr := .sqdmulh t63 (.const 0x4ebf#16)
  let t65 : SExpr := .sshr (.add t64 (.const 0x0400#16)) 11
  let t66 : SExpr := .barrett (.add t0 t1)
  let t67 : SExpr := .barrett (.add t3 t4)
  let t68 : SExpr := .montmul (.sub t66 t67) 0x05d5#16
  let t69 : SExpr := .barrett (.add t7 t8)
  let t70 : SExpr := .barrett (.add t10 t11)
  let t71 : SExpr := .montmul (.sub t69 t70) 0x058e#16
  let t72 : SExpr := .montmul (.sub t68 t71) 0xfe99#16
  let t73 : SExpr := .barrett (.add t15 t16)
  let t74 : SExpr := .barrett (.add t18 t19)
  let t75 : SExpr := .montmul (.sub t73 t74) 0x011f#16
  let t76 : SExpr := .barrett (.add t22 t23)
  let t77 : SExpr := .barrett (.add t25 t26)
  let t78 : SExpr := .montmul (.sub t76 t77) 0x00ca#16
  let t79 : SExpr := .montmul (.sub t75 t78) 0xfa13#16
  let t80 : SExpr := .sub t72 t79
  let t81 : SExpr := .montmul t80 0xfd0a#16
  let t82 : SExpr := .add (.sqdmulh t81 (.const 0x4ebf#16)) (.const 0x0400#16)
  let t83 : SExpr := .montmul (.sub t33 t34) 0xff55#16
  let t84 : SExpr := .montmul (.sub t36 t37) 0x026e#16
  let t85 : SExpr := .montmul (.sub t83 t84) 0x05d5#16
  let t86 : SExpr := .montmul (.sub t40 t41) 0x0629#16
  let t87 : SExpr := .montmul (.sub t43 t44) 0x00b6#16
  let t88 : SExpr := .montmul (.sub t86 t87) 0x058e#16
  let t89 : SExpr := .montmul (.sub t85 t88) 0xfe99#16
  let t90 : SExpr := .montmul (.sub t48 t49) 0x03c2#16
  let t91 : SExpr := .montmul (.sub t51 t52) 0xfb4e#16
  let t92 : SExpr := .sub t90 t91
  let t93 : SExpr := .montmul t92 0x011f#16
  let t94 : SExpr := .montmul (.sub t55 t56) 0xfa3e#16
  let t95 : SExpr := .montmul (.sub t58 t59) 0x05bc#16
  let t96 : SExpr := .montmul (.sub t94 t95) 0x00ca#16
  let t97 : SExpr := .montmul (.sub t93 t96) 0xfa13#16
  let t98 : SExpr := .montmul (.sub t89 t97) 0xfd0a#16
  let t99 : SExpr := .sqdmulh t98 (.const 0x4ebf#16)
  let t100 : SExpr := .sshr (.add t99 (.const 0x0400#16)) 11
  let t101 : SExpr := .barrett (.add t66 t67)
  let t102 : SExpr := .barrett (.add t69 t70)
  let t103 : SExpr := .montmul (.sub t101 t102) 0xfe99#16
  let t104 : SExpr := .barrett (.add t73 t74)
  let t105 : SExpr := .barrett (.add t76 t77)
  let t106 : SExpr := .montmul (.sub t104 t105) 0xfa13#16
  let t107 : SExpr := .montmul (.sub t103 t106) 0xfd0a#16
  let t108 : SExpr := .barrett t107
  let t109 : SExpr := .barrett (.add t83 t84)
  let t110 : SExpr := .barrett (.add t86 t87)
  let t111 : SExpr := .montmul (.sub t109 t110) 0xfe99#16
  let t112 : SExpr := .barrett (.add t90 t91)
  let t113 : SExpr := .barrett (.add t94 t95)
  let t114 : SExpr := .montmul (.sub t112 t113) 0xfa13#16
  let t115 : SExpr := .montmul (.sub t111 t114) 0xfd0a#16
  let t116 : SExpr := .barrett t115
  let t117 : SExpr := .barrett (.add t2 t5)
  let t118 : SExpr := .barrett (.add t9 t12)
  let t119 : SExpr := .montmul (.sub t117 t118) 0xfe99#16
  let t120 : SExpr := .barrett (.add t17 t20)
  let t121 : SExpr := .barrett (.add t24 t27)
  let t122 : SExpr := .montmul (.sub t120 t121) 0xfa13#16
  let t123 : SExpr := .montmul (.sub t119 t122) 0xfd0a#16
  let t124 : SExpr := .barrett t123
  let t125 : SExpr := .barrett (.add t35 t38)
  let t126 : SExpr := .add (.sqdmulh t115 (.const 0x4ebf#16)) (.const 0x0400#16)
  let t127 : SExpr := .add (.sqdmulh t123 (.const 0x4ebf#16)) (.const 0x0400#16)
  let t128 : SExpr := .barrett t63
  let t129 : SExpr := .barrett t81
  let t130 : SExpr := .barrett t98
  let t131 : SExpr := .barrett t30
  let t132 : SExpr := .barrett (.add t50 t53)
  let t133 : SExpr := .barrett (.add t57 t60)
  let t134 : SExpr := .barrett (.add t42 t45)
  let t135 : SExpr := .barrett (.add t125 t134)
  let t136 : SExpr := .barrett (.add t132 t133)
  let t137 : SExpr := .barrett (.add t135 t136)
  let t138 : SExpr := .barrett (.add t101 t102)
  let t139 : SExpr := .barrett (.add t104 t105)
  let t140 : SExpr := .barrett (.add t138 t139)
  let t141 : SExpr := .barrett (.add t109 t110)
  let t142 : SExpr := .barrett (.add t112 t113)
  let t143 : SExpr := .barrett (.add t141 t142)
  let t144 : SExpr := .barrett (.add t117 t118)
  let t145 : SExpr := .barrett (.add t120 t121)
  let t146 : SExpr := .barrett (.add t144 t145)
  let t147 : SExpr := .barrett (.add t39 t46)
  let t148 : SExpr := .barrett (.add t54 t61)
  let t149 : SExpr := .barrett (.add t147 t148)
  let t150 : SExpr := .barrett (.add t68 t71)
  let t151 : SExpr := .barrett (.add t75 t78)
  let t152 : SExpr := .barrett (.add t150 t151)
  let t153 : SExpr := .barrett (.add t85 t88)
  let t154 : SExpr := .barrett (.add t93 t96)
  let t155 : SExpr := .barrett (.add t153 t154)
  let t156 : SExpr := .barrett (.add t6 t13)
  let t157 : SExpr := .barrett (.add t21 t28)
  let t158 : SExpr := .barrett (.add t156 t157)
  let t159 : SExpr := .montmul (.sub t125 t134) 0xfe99#16
  let t160 : SExpr := .montmul (.sub t132 t133) 0xfa13#16
  let t161 : SExpr := .barrett (.add t159 t160)
  let t162 : SExpr := .barrett (.add t103 t106)
  let t163 : SExpr := .barrett (.add t111 t114)
  let t164 : SExpr := .barrett (.add t119 t122)
  let t165 : SExpr := .barrett (.add t47 t62)
  let t166 : SExpr := .barrett (.add t72 t79)
  let t167 : SExpr := .barrett (.add t89 t97)
  let t168 : SExpr := .barrett (.add t14 t29)
  let t169 : SExpr := .montmul (.sub t135 t136) 0xfd0a#16
  let t170 : SExpr := .montmul (.sub t138 t139) 0xfd0a#16
  let t171 : SExpr := .montmul (.sub t141 t142) 0xfd0a#16
  let t172 : SExpr := .montmul (.sub t144 t145) 0xfd0a#16
  let t173 : SExpr := .montmul (.sub t147 t148) 0xfd0a#16
  let t174 : SExpr := .montmul (.sub t150 t151) 0xfd0a#16
  let t175 : SExpr := .montmul (.sub t153 t154) 0xfd0a#16
  let t176 : SExpr := .montmul (.sub t156 t157) 0xfd0a#16
  let t177 : SExpr := .montmul (.sub t159 t160) 0xfd0a#16
  { vregs := ⟨.vreg0 0, .sshr t32 11, t65, .sshr t82 11,
     t100, t108, t116, t124,
     .const 0xf2ff#16, t125, t2, t101,
     t109, .const 0x05d5#16, t112, t92,
     .const 0x0d01#16, .const 0x4ebf#16, .sshr t126 11, t32,
     t82, .sshr t127 11, t128, .const 0xf2ff#16,
     t129, t64, t130, .const 0x0400#16,
     t131, t99, t31, .mul t80 (.const 0x7b0a#16)⟩
    spill := ⟨t132, t35, t104, t83,
     t9, t2, t54, t75,
     t70, t87, t84, t12,
     t90, t5, t121, t113,
     t133, t17, t38, t105,
     t67, t91, t20, t78,
     t61, t96, t28, .spill0 27,
     .spill0 28, .spill0 29, .spill0 30, .spill0 31,
     .spill0 32, .spill0 33, .spill0 34, .spill0 35,
     .spill0 36, .spill0 37, .spill0 38, .spill0 39⟩
    poly  := ⟨.barrett t137, .barrett t140, .barrett t143, .barrett t146,
     .barrett t149, .barrett t152, .barrett t155, .barrett t158,
     .barrett t161, .barrett t162, .barrett t163, .barrett t164,
     .barrett t165, .barrett t166, .barrett t167, .barrett t168,
     .barrett t169, .barrett t170, .barrett t171, .barrett t172,
     .barrett t173, .barrett t174, .barrett t175, .barrett t176,
     .barrett t177, t108, t116, t124,
     t128, t129, t130, t131⟩
    gprs  := ⟨.gpr0 0#5 0#64, .gpr0 1#5 0#64, .gpr0 2#5 0#64, .const64 0#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .gpr0 8#5 0#64, .addGpr0 20#5 12#5, .gpr0 10#5 0#64, .gpr0 11#5 0#64,
     .gpr0 12#5 0#64, .gpr0 13#5 0#64, .gpr0 14#5 0#64, .gpr0 15#5 0#64,
     .gpr0 16#5 0#64, .gpr0 17#5 0#64, .gpr0 18#5 0#64, .gpr0 19#5 0#64,
     .gpr0 20#5 0#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .const64 64778#64, .const64 31498#64, .const64 1441#64,
     .const64 55457#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

theorem run_seg7_inv1c : runSymRange cfgSeg7InvSym 10722 486 symSeg7InvSymMidB = some symSeg7InvSymEnd :=
  runSymRange_of_fast (by rfl_kernel)

private theorem run_seg7_inv1ab : runSymRange cfgSeg7InvSym 9750 972 symSeg7InvSymInit = some symSeg7InvSymMidB :=
  runSymRange_append run_seg7_inv1a run_seg7_inv1b

theorem run_seg7_inv1 : runSymRange cfgSeg7InvSym 9750 1458 symSeg7InvSymInit = some symSeg7InvSymEnd :=
  runSymRange_append run_seg7_inv1ab run_seg7_inv1c

theorem seg7_inv_noSpillVreg : polyNoSpillVreg false symSeg7InvSymEnd.poly = true := by rfl_kernel

set_option maxRecDepth 40000 in
theorem seg7_inv_ast_eq : polyAstEq false symSeg7InvSymEnd.poly symUpperInvNtt = true := by rfl_kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvSym1c

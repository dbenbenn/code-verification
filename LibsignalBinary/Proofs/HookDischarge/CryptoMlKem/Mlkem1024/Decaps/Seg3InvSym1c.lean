/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3InvSym1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3InvSym1b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3InvSym1c

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
  (SExpr SymState symInitState runSymRange runSymRange_append)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast
  (runSymRange_of_fast)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure
  (symUpperInvNtt polyNoSpillVreg polyAstEq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3InvSym1a
  (cfgSeg3Inv run_seg3_inv1a)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3InvSym1b
  (symSeg3InvMidB run_seg3_inv1b)

@[expose] def symSeg3InvEnd : SymState :=
  let t0 : SExpr := .add (.poly 30) (.poly 31)
  let t1 : SExpr := .add (.poly 28) (.poly 29)
  let t2 : SExpr := .montmul (.sub t0 t1) 0xff55#16
  let t3 : SExpr := .add (.poly 26) (.poly 27)
  let t4 : SExpr := .add (.poly 24) (.poly 25)
  let t5 : SExpr := .montmul (.sub t3 t4) 0x026e#16
  let t6 : SExpr := .montmul (.sub t2 t5) 0x05d5#16
  let t7 : SExpr := .add (.poly 22) (.poly 23)
  let t8 : SExpr := .add (.poly 20) (.poly 21)
  let t9 : SExpr := .montmul (.sub t7 t8) 0x0629#16
  let t10 : SExpr := .add (.poly 18) (.poly 19)
  let t11 : SExpr := .add (.poly 16) (.poly 17)
  let t12 : SExpr := .montmul (.sub t10 t11) 0x00b6#16
  let t13 : SExpr := .sub t9 t12
  let t14 : SExpr := .montmul t13 0x058e#16
  let t15 : SExpr := .montmul (.sub t6 t14) 0xfe99#16
  let t16 : SExpr := .add (.poly 14) (.poly 15)
  let t17 : SExpr := .add (.poly 12) (.poly 13)
  let t18 : SExpr := .montmul (.sub t16 t17) 0x03c2#16
  let t19 : SExpr := .add (.poly 10) (.poly 11)
  let t20 : SExpr := .add (.poly 8) (.poly 9)
  let t21 : SExpr := .montmul (.sub t19 t20) 0xfb4e#16
  let t22 : SExpr := .montmul (.sub t18 t21) 0x011f#16
  let t23 : SExpr := .add (.poly 6) (.poly 7)
  let t24 : SExpr := .add (.poly 4) (.poly 5)
  let t25 : SExpr := .montmul (.sub t23 t24) 0xfa3e#16
  let t26 : SExpr := .add (.poly 2) (.poly 3)
  let t27 : SExpr := .add (.poly 0) (.poly 1)
  let t28 : SExpr := .montmul (.sub t26 t27) 0x05bc#16
  let t29 : SExpr := .montmul (.sub t25 t28) 0x00ca#16
  let t30 : SExpr := .montmul (.sub t22 t29) 0xfa13#16
  let t31 : SExpr := .montmul (.sub t15 t30) 0xfd0a#16
  let t32 : SExpr := .sqdmulh t31 (.const 0x4ebf#16)
  let t33 : SExpr := .add t32 (.const 0x0400#16)
  let t34 : SExpr := .montmul (.sub (.poly 31) (.poly 30)) 0x023d#16
  let t35 : SExpr := .montmul (.sub (.poly 29) (.poly 28)) 0xfad3#16
  let t36 : SExpr := .montmul (.sub t34 t35) 0xff55#16
  let t37 : SExpr := .montmul (.sub (.poly 27) (.poly 26)) 0x0108#16
  let t38 : SExpr := .montmul (.sub (.poly 25) (.poly 24)) 0x017f#16
  let t39 : SExpr := .montmul (.sub t37 t38) 0x026e#16
  let t40 : SExpr := .montmul (.sub t36 t39) 0x05d5#16
  let t41 : SExpr := .montmul (.sub (.poly 23) (.poly 22)) 0xfcc3#16
  let t42 : SExpr := .montmul (.sub (.poly 21) (.poly 20)) 0x05b2#16
  let t43 : SExpr := .montmul (.sub t41 t42) 0x0629#16
  let t44 : SExpr := .montmul (.sub (.poly 19) (.poly 18)) 0xf9be#16
  let t45 : SExpr := .montmul (.sub (.poly 17) (.poly 16)) 0xff7e#16
  let t46 : SExpr := .montmul (.sub t44 t45) 0x00b6#16
  let t47 : SExpr := .montmul (.sub t43 t46) 0x058e#16
  let t48 : SExpr := .montmul (.sub t40 t47) 0xfe99#16
  let t49 : SExpr := .montmul (.sub (.poly 15) (.poly 14)) 0xfd57#16
  let t50 : SExpr := .montmul (.sub (.poly 13) (.poly 12)) 0x03f9#16
  let t51 : SExpr := .montmul (.sub t49 t50) 0x03c2#16
  let t52 : SExpr := .montmul (.sub (.poly 11) (.poly 10)) 0x02dc#16
  let t53 : SExpr := .montmul (.sub (.poly 9) (.poly 8)) 0x0260#16
  let t54 : SExpr := .montmul (.sub t52 t53) 0xfb4e#16
  let t55 : SExpr := .montmul (.sub t51 t54) 0x011f#16
  let t56 : SExpr := .montmul (.sub (.poly 7) (.poly 6)) 0xf9fa#16
  let t57 : SExpr := .montmul (.sub (.poly 5) (.poly 4)) 0x019b#16
  let t58 : SExpr := .montmul (.sub t56 t57) 0xfa3e#16
  let t59 : SExpr := .montmul (.sub (.poly 3) (.poly 2)) 0xff33#16
  let t60 : SExpr := .montmul (.sub (.poly 1) (.poly 0)) 0xf9dd#16
  let t61 : SExpr := .montmul (.sub t59 t60) 0x05bc#16
  let t62 : SExpr := .montmul (.sub t58 t61) 0x00ca#16
  let t63 : SExpr := .montmul (.sub t55 t62) 0xfa13#16
  let t64 : SExpr := .montmul (.sub t48 t63) 0xfd0a#16
  let t65 : SExpr := .sqdmulh t64 (.const 0x4ebf#16)
  let t66 : SExpr := .add t65 (.const 0x0400#16)
  let t67 : SExpr := .barrett (.add t0 t1)
  let t68 : SExpr := .barrett (.add t3 t4)
  let t69 : SExpr := .barrett (.add t67 t68)
  let t70 : SExpr := .barrett (.add t7 t8)
  let t71 : SExpr := .barrett (.add t10 t11)
  let t72 : SExpr := .barrett (.add t70 t71)
  let t73 : SExpr := .montmul (.sub t69 t72) 0xfe99#16
  let t74 : SExpr := .barrett (.add t16 t17)
  let t75 : SExpr := .barrett (.add t19 t20)
  let t76 : SExpr := .barrett (.add t74 t75)
  let t77 : SExpr := .barrett (.add t23 t24)
  let t78 : SExpr := .barrett (.add t26 t27)
  let t79 : SExpr := .barrett (.add t77 t78)
  let t80 : SExpr := .montmul (.sub t76 t79) 0xfa13#16
  let t81 : SExpr := .montmul (.sub t73 t80) 0xfd0a#16
  let t82 : SExpr := .barrett t81
  let t83 : SExpr := .barrett (.add t34 t35)
  let t84 : SExpr := .barrett (.add t37 t38)
  let t85 : SExpr := .barrett (.add t83 t84)
  let t86 : SExpr := .barrett (.add t41 t42)
  let t87 : SExpr := .barrett (.add t44 t45)
  let t88 : SExpr := .barrett (.add t86 t87)
  let t89 : SExpr := .montmul (.sub t85 t88) 0xfe99#16
  let t90 : SExpr := .barrett (.add t49 t50)
  let t91 : SExpr := .barrett (.add t52 t53)
  let t92 : SExpr := .barrett (.add t90 t91)
  let t93 : SExpr := .barrett (.add t56 t57)
  let t94 : SExpr := .barrett (.add t59 t60)
  let t95 : SExpr := .barrett (.add t93 t94)
  let t96 : SExpr := .montmul (.sub t92 t95) 0xfa13#16
  let t97 : SExpr := .montmul (.sub t89 t96) 0xfd0a#16
  let t98 : SExpr := .barrett t97
  let t99 : SExpr := .barrett (.add t2 t5)
  let t100 : SExpr := .barrett (.add t9 t12)
  let t101 : SExpr := .montmul (.sub t99 t100) 0xfe99#16
  let t102 : SExpr := .barrett (.add t18 t21)
  let t103 : SExpr := .barrett (.add t25 t28)
  let t104 : SExpr := .montmul (.sub t102 t103) 0xfa13#16
  let t105 : SExpr := .montmul (.sub t101 t104) 0xfd0a#16
  let t106 : SExpr := .barrett t105
  let t107 : SExpr := .barrett (.add t36 t39)
  let t108 : SExpr := .barrett (.add t43 t46)
  let t109 : SExpr := .montmul (.sub t107 t108) 0xfe99#16
  let t110 : SExpr := .barrett (.add t51 t54)
  let t111 : SExpr := .barrett (.add t58 t61)
  let t112 : SExpr := .montmul (.sub t110 t111) 0xfa13#16
  let t113 : SExpr := .montmul (.sub t109 t112) 0xfd0a#16
  let t114 : SExpr := .barrett t113
  let t115 : SExpr := .montmul (.sub t67 t68) 0x05d5#16
  let t116 : SExpr := .sub t70 t71
  let t117 : SExpr := .montmul t116 0x058e#16
  let t118 : SExpr := .montmul (.sub t115 t117) 0xfe99#16
  let t119 : SExpr := .montmul (.sub t74 t75) 0x011f#16
  let t120 : SExpr := .montmul (.sub t77 t78) 0x00ca#16
  let t121 : SExpr := .montmul (.sub t119 t120) 0xfa13#16
  let t122 : SExpr := .montmul (.sub t118 t121) 0xfd0a#16
  let t123 : SExpr := .sqdmulh t122 (.const 0x4ebf#16)
  let t124 : SExpr := .sshr (.add t123 (.const 0x0400#16)) 11
  let t125 : SExpr := .mul t116 (.const 0xcf8e#16)
  let t126 : SExpr := .sshr (.sqdmulh t125 (.const 0x0d01#16)) 1
  let t127 : SExpr := .sub t86 t87
  let t128 : SExpr := .sshr (.sqdmulh t127 (.const 0x058e#16)) 1
  let t129 : SExpr := .montmul (.sub t83 t84) 0x05d5#16
  let t130 : SExpr := .montmul t127 0x058e#16
  let t131 : SExpr := .montmul (.sub t129 t130) 0xfe99#16
  let t132 : SExpr := .montmul (.sub t90 t91) 0x011f#16
  let t133 : SExpr := .montmul (.sub t93 t94) 0x00ca#16
  let t134 : SExpr := .montmul (.sub t132 t133) 0xfa13#16
  let t135 : SExpr := .montmul (.sub t131 t134) 0xfd0a#16
  let t136 : SExpr := .sqdmulh t135 (.const 0x4ebf#16)
  let t137 : SExpr := .add t136 (.const 0x0400#16)
  let t138 : SExpr := .add (.sqdmulh t113 (.const 0x4ebf#16)) (.const 0x0400#16)
  let t139 : SExpr := .barrett t122
  let t140 : SExpr := .barrett t135
  let t141 : SExpr := .barrett t31
  let t142 : SExpr := .barrett t64
  let t143 : SExpr := .barrett (.add t129 t130)
  let t144 : SExpr := .barrett (.add t132 t133)
  let t145 : SExpr := .montmul (.sub t143 t144) 0xfd0a#16
  let t146 : SExpr := .barrett (.add t69 t72)
  let t147 : SExpr := .barrett (.add t76 t79)
  let t148 : SExpr := .barrett (.add t146 t147)
  let t149 : SExpr := .barrett (.add t85 t88)
  let t150 : SExpr := .barrett (.add t92 t95)
  let t151 : SExpr := .barrett (.add t149 t150)
  let t152 : SExpr := .barrett (.add t99 t100)
  let t153 : SExpr := .barrett (.add t102 t103)
  let t154 : SExpr := .barrett (.add t152 t153)
  let t155 : SExpr := .barrett (.add t107 t108)
  let t156 : SExpr := .barrett (.add t110 t111)
  let t157 : SExpr := .barrett (.add t155 t156)
  let t158 : SExpr := .barrett (.add t115 t117)
  let t159 : SExpr := .barrett (.add t119 t120)
  let t160 : SExpr := .barrett (.add t158 t159)
  let t161 : SExpr := .barrett (.add t143 t144)
  let t162 : SExpr := .barrett (.add t6 t14)
  let t163 : SExpr := .barrett (.add t22 t29)
  let t164 : SExpr := .barrett (.add t162 t163)
  let t165 : SExpr := .barrett (.add t40 t47)
  let t166 : SExpr := .barrett (.add t55 t62)
  let t167 : SExpr := .barrett (.add t165 t166)
  let t168 : SExpr := .barrett (.add t73 t80)
  let t169 : SExpr := .barrett (.add t89 t96)
  let t170 : SExpr := .barrett (.add t101 t104)
  let t171 : SExpr := .barrett (.add t109 t112)
  let t172 : SExpr := .barrett (.add t118 t121)
  let t173 : SExpr := .barrett (.add t131 t134)
  let t174 : SExpr := .barrett (.add t15 t30)
  let t175 : SExpr := .barrett (.add t48 t63)
  let t176 : SExpr := .montmul (.sub t146 t147) 0xfd0a#16
  let t177 : SExpr := .montmul (.sub t149 t150) 0xfd0a#16
  let t178 : SExpr := .montmul (.sub t152 t153) 0xfd0a#16
  let t179 : SExpr := .montmul (.sub t155 t156) 0xfd0a#16
  let t180 : SExpr := .montmul (.sub t158 t159) 0xfd0a#16
  let t181 : SExpr := .montmul (.sub t162 t163) 0xfd0a#16
  let t182 : SExpr := .montmul (.sub t165 t166) 0xfd0a#16
  { vregs := ⟨.sshr t33 11, .sshr t66 11, t82, t98,
     t106, t114, t124, t66,
     t13, t2, t126, t128,
     .const 0xf2ff#16, t125, .mul t127 (.const 0xcf8e#16), .const 0x0d01#16,
     .sshr t137 11, t137, .sshr t138 11, t139,
     t33, t140, t123, t141,
     t136, t142, t32, t65,
     .sqdmulh t145 (.const 0x4ebf#16), .const 0x0400#16, .const 0xf2ff#16, .const 0x4ebf#16⟩
    spill := ⟨.spill0 0, .spill0 1, .spill0 2, .spill0 3,
     .spill0 4, .spill0 5, .spill0 6, .spill0 7,
     .spill0 8, .spill0 9, .spill0 10, .spill0 11,
     .spill0 12, .spill0 13, .const 0x4ebf#16, t84,
     t87, t71, t68, .const 0x0d01#16,
     t46, .spill0 21, .spill0 22, .spill0 23,
     .spill0 24, .spill0 25, .spill0 26, .spill0 27,
     .spill0 28, .spill0 29, .spill0 30, .spill0 31,
     .spill0 32, .spill0 33, .spill0 34, .spill0 35,
     .spill0 36, .spill0 37, .spill0 38, .spill0 39⟩
    poly  := ⟨.barrett t148, .barrett t151, .barrett t154, .barrett t157,
     .barrett t160, .barrett t161, .barrett t164, .barrett t167,
     .barrett t168, .barrett t169, .barrett t170, .barrett t171,
     .barrett t172, .barrett t173, .barrett t174, .barrett t175,
     .barrett t176, .barrett t177, .barrett t178, .barrett t179,
     .barrett t180, .barrett t145, .barrett t181, .barrett t182,
     t82, t98, t106, t114,
     t139, t140, t141, t142⟩
    gprs  := ⟨.spAdd 14432#64, .spAdd 28368#64, .const64 512#64, .gpr0 3#5 0#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .const64 64778#64, .const64 573#64, .gpr0 10#5 0#64, .gpr0 11#5 0#64,
     .gpr0 12#5 0#64, .gpr0 13#5 0#64, .gpr0 14#5 0#64, .gpr0 15#5 0#64,
     .gpr0 16#5 0#64, .gpr0 17#5 0#64, .gpr0 18#5 0#64, .spAdd 14432#64,
     .gpr0 20#5 0#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

theorem run_seg3_inv1c : runSymRange cfgSeg3Inv 3076 520 symSeg3InvMidB = some symSeg3InvEnd :=
  runSymRange_of_fast (by rfl_kernel)

private theorem runSymRange_append' {cfg : PolySymDefs.SymCfg} {m n mn w wm : Nat} {st0 st1 st2 : SymState}
    (hwm : w + m = wm) (hmn : m + n = mn)
    (h1 : runSymRange cfg w m st0 = some st1)
    (h2 : runSymRange cfg wm n st1 = some st2) :
    runSymRange cfg w mn st0 = some st2 := by
  subst hwm; subst hmn; exact runSymRange_append h1 h2

private theorem run_seg3_inv1ab : runSymRange cfgSeg3Inv 2036 1040 symInitState = some symSeg3InvMidB :=
  runSymRange_append' rfl rfl run_seg3_inv1a run_seg3_inv1b

theorem run_seg3_inv1 : runSymRange cfgSeg3Inv 2036 1560 symInitState = some symSeg3InvEnd :=
  runSymRange_append' rfl rfl run_seg3_inv1ab run_seg3_inv1c

theorem seg3_inv1_noSpillVreg : polyNoSpillVreg false symSeg3InvEnd.poly = true := by rfl_kernel

set_option maxRecDepth 40000 in
theorem seg3_inv1_ast_eq : polyAstEq false symSeg3InvEnd.poly symUpperInvNtt = true := by rfl_kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3InvSym1c

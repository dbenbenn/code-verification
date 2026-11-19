/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatSym1a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatSym1b

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
  (SExpr SymState runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast
  (runSymRange_of_fast)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatSym1a
  (cfgSeg2Fwd symSeg2MidA)

@[expose] def symSeg2MidB : SymState :=
  let t0 : SExpr := .montmul (.poly 26) 0xfd0a#16
  let t1 : SExpr := .montmul (.sub (.poly 10) t0) 0xfa13#16
  let t2 : SExpr := .montmul (.poly 18) 0xfd0a#16
  let t3 : SExpr := .sub (.poly 2) t2
  let t4 : SExpr := .add t1 t3
  let t5 : SExpr := .montmul (.poly 30) 0xfd0a#16
  let t6 : SExpr := .montmul (.sub (.poly 14) t5) 0xfa13#16
  let t7 : SExpr := .montmul (.poly 22) 0xfd0a#16
  let t8 : SExpr := .sub (.poly 6) t7
  let t9 : SExpr := .montmul (.add t6 t8) 0x011f#16
  let t10 : SExpr := .montmul (.sub t4 t9) 0xfb4e#16
  let t11 : SExpr := .montmul (.poly 24) 0xfd0a#16
  let t12 : SExpr := .montmul (.sub (.poly 8) t11) 0xfa13#16
  let t13 : SExpr := .montmul (.poly 16) 0xfd0a#16
  let t14 : SExpr := .sub (.poly 0) t13
  let t15 : SExpr := .add t12 t14
  let t16 : SExpr := .montmul (.poly 28) 0xfd0a#16
  let t17 : SExpr := .montmul (.sub (.poly 12) t16) 0xfa13#16
  let t18 : SExpr := .montmul (.poly 20) 0xfd0a#16
  let t19 : SExpr := .sub (.poly 4) t18
  let t20 : SExpr := .montmul (.add t17 t19) 0x011f#16
  let t21 : SExpr := .sub t15 t20
  let t22 : SExpr := .add t10 t21
  let t23 : SExpr := .montmul (.poly 27) 0xfd0a#16
  let t24 : SExpr := .montmul (.sub (.poly 11) t23) 0xfa13#16
  let t25 : SExpr := .montmul (.poly 19) 0xfd0a#16
  let t26 : SExpr := .sub (.poly 3) t25
  let t27 : SExpr := .add t24 t26
  let t28 : SExpr := .montmul (.poly 31) 0xfd0a#16
  let t29 : SExpr := .montmul (.sub (.poly 15) t28) 0xfa13#16
  let t30 : SExpr := .montmul (.poly 23) 0xfd0a#16
  let t31 : SExpr := .sub (.poly 7) t30
  let t32 : SExpr := .montmul (.add t29 t31) 0x011f#16
  let t33 : SExpr := .montmul (.sub t27 t32) 0xfb4e#16
  let t34 : SExpr := .montmul (.poly 25) 0xfd0a#16
  let t35 : SExpr := .montmul (.sub (.poly 9) t34) 0xfa13#16
  let t36 : SExpr := .montmul (.poly 17) 0xfd0a#16
  let t37 : SExpr := .sub (.poly 1) t36
  let t38 : SExpr := .add t35 t37
  let t39 : SExpr := .montmul (.poly 29) 0xfd0a#16
  let t40 : SExpr := .montmul (.sub (.poly 13) t39) 0xfa13#16
  let t41 : SExpr := .montmul (.poly 21) 0xfd0a#16
  let t42 : SExpr := .sub (.poly 5) t41
  let t43 : SExpr := .montmul (.add t40 t42) 0x011f#16
  let t44 : SExpr := .sub t38 t43
  let t45 : SExpr := .add t33 t44
  let t46 : SExpr := .montmul t45 0x02dc#16
  let t47 : SExpr := .sub t21 t10
  let t48 : SExpr := .montmul (.sub t8 t6) 0x00ca#16
  let t49 : SExpr := .sub t3 t1
  let t50 : SExpr := .montmul (.add t48 t49) 0xfa3e#16
  let t51 : SExpr := .montmul (.sub t19 t17) 0x00ca#16
  let t52 : SExpr := .sub t14 t12
  let t53 : SExpr := .add t51 t52
  let t54 : SExpr := .add t50 t53
  let t55 : SExpr := .sub t53 t50
  let t56 : SExpr := .sub t44 t33
  let t57 : SExpr := .montmul (.sub t31 t29) 0x00ca#16
  let t58 : SExpr := .sub t26 t24
  let t59 : SExpr := .montmul (.add t57 t58) 0xfa3e#16
  let t60 : SExpr := .montmul (.sub t42 t40) 0x00ca#16
  let t61 : SExpr := .sub t37 t35
  let t62 : SExpr := .add t60 t61
  let t63 : SExpr := .add t59 t62
  let t64 : SExpr := .sqdmulh (.mul t63 (.const 0x47fa#16)) (.const 0x0d01#16)
  let t65 : SExpr := .sub t62 t59
  let t66 : SExpr := .sqdmulh (.mul t65 (.const 0x229b#16)) (.const 0x0d01#16)
  let t67 : SExpr := .sshr (.sqdmulh t63 (.const 0xf9fa#16)) 1
  let t68 : SExpr := .sub t61 t60
  let t69 : SExpr := .montmul (.sub t58 t57) 0x05bc#16
  let t70 : SExpr := .sub t68 t69
  let t71 : SExpr := .sqdmulh (.mul t56 (.const 0x2260#16)) (.const 0x0d01#16)
  let t72 : SExpr := .add t69 t68
  let t73 : SExpr := .sqdmulh (.mul t72 (.const 0x6833#16)) (.const 0x0d01#16)
  let t74 : SExpr := .montmul (.sub t49 t48) 0x05bc#16
  let t75 : SExpr := .sub t52 t51
  let t76 : SExpr := .add t74 t75
  let t77 : SExpr := .sub t75 t74
  let t78 : SExpr := .add t30 (.poly 7)
  let t79 : SExpr := .montmul (.add t28 (.poly 15)) 0xfe99#16
  let t80 : SExpr := .montmul (.sub t78 t79) 0x058e#16
  let t81 : SExpr := .add t25 (.poly 3)
  let t82 : SExpr := .montmul (.add t23 (.poly 11)) 0xfe99#16
  let t83 : SExpr := .sub t81 t82
  let t84 : SExpr := .montmul (.add t80 t83) 0x0629#16
  let t85 : SExpr := .add t41 (.poly 5)
  let t86 : SExpr := .montmul (.add t39 (.poly 13)) 0xfe99#16
  let t87 : SExpr := .montmul (.sub t85 t86) 0x058e#16
  let t88 : SExpr := .add t36 (.poly 1)
  let t89 : SExpr := .montmul (.add t34 (.poly 9)) 0xfe99#16
  let t90 : SExpr := .sub t88 t89
  let t91 : SExpr := .add t87 t90
  let t92 : SExpr := .add t84 t91
  let t93 : SExpr := .montmul (.add t79 t78) 0x05d5#16
  let t94 : SExpr := .add t82 t81
  let t95 : SExpr := .montmul (.add t93 t94) 0xff55#16
  let t96 : SExpr := .montmul (.add t86 t85) 0x05d5#16
  let t97 : SExpr := .add t89 t88
  let t98 : SExpr := .add t96 t97
  let t99 : SExpr := .montmul (.add t95 t98) 0x023d#16
  let t100 : SExpr := .montmul (.add t5 (.poly 14)) 0xfe99#16
  let t101 : SExpr := .add t7 (.poly 6)
  let t102 : SExpr := .montmul (.add t100 t101) 0x05d5#16
  let t103 : SExpr := .montmul (.add t0 (.poly 10)) 0xfe99#16
  let t104 : SExpr := .add t2 (.poly 2)
  let t105 : SExpr := .add t103 t104
  let t106 : SExpr := .montmul (.add t102 t105) 0xff55#16
  let t107 : SExpr := .montmul (.add t16 (.poly 12)) 0xfe99#16
  let t108 : SExpr := .add t18 (.poly 4)
  let t109 : SExpr := .montmul (.add t107 t108) 0x05d5#16
  let t110 : SExpr := .montmul (.add t11 (.poly 8)) 0xfe99#16
  let t111 : SExpr := .add t13 (.poly 0)
  let t112 : SExpr := .add t110 t111
  let t113 : SExpr := .add t109 t112
  let t114 : SExpr := .add t106 t113
  let t115 : SExpr := .montmul (.sub t98 t95) 0xfad3#16
  let t116 : SExpr := .sub t113 t106
  let t117 : SExpr := .montmul (.sub t94 t93) 0x026e#16
  let t118 : SExpr := .sub t97 t96
  let t119 : SExpr := .montmul (.add t117 t118) 0x0108#16
  let t120 : SExpr := .montmul (.sub t105 t102) 0x026e#16
  let t121 : SExpr := .sub t112 t109
  let t122 : SExpr := .add t120 t121
  let t123 : SExpr := .montmul (.sub t118 t117) 0x017f#16
  let t124 : SExpr := .sub t121 t120
  let t125 : SExpr := .montmul t92 0xfcc3#16
  let t126 : SExpr := .montmul (.sub t101 t100) 0x058e#16
  let t127 : SExpr := .sub t104 t103
  let t128 : SExpr := .montmul (.add t126 t127) 0x0629#16
  let t129 : SExpr := .montmul (.sub t108 t107) 0x058e#16
  let t130 : SExpr := .sub t111 t110
  let t131 : SExpr := .add t129 t130
  let t132 : SExpr := .add t128 t131
  let t133 : SExpr := .montmul (.sub t91 t84) 0x05b2#16
  let t134 : SExpr := .sub t131 t128
  let t135 : SExpr := .montmul (.sub t83 t80) 0x00b6#16
  let t136 : SExpr := .sub t90 t87
  let t137 : SExpr := .montmul (.add t135 t136) 0xf9be#16
  let t138 : SExpr := .montmul (.sub t127 t126) 0x00b6#16
  let t139 : SExpr := .sub t130 t129
  let t140 : SExpr := .add t138 t139
  let t141 : SExpr := .montmul (.sub t136 t135) 0xff7e#16
  let t142 : SExpr := .sub t139 t138
  let t143 : SExpr := .montmul (.add t32 t27) 0x03c2#16
  let t144 : SExpr := .add t43 t38
  let t145 : SExpr := .montmul (.add t143 t144) 0xfd57#16
  let t146 : SExpr := .montmul (.add t9 t4) 0x03c2#16
  let t147 : SExpr := .add t20 t15
  let t148 : SExpr := .add t146 t147
  let t149 : SExpr := .montmul (.sub t144 t143) 0x03f9#16
  let t150 : SExpr := .sub t147 t146
  { vregs := ⟨.sub t22 t46, t47, t54, t55,
     .montmul t56 0x0260#16, .sshr t64 1, .add t46 t22, t66,
     .vreg0 8, .const 0x011f#16, .const 0x6e1f#16, .const 0x0d01#16,
     .const 0xcf8e#16, .const 0x34d5#16, .vreg0 14, .vreg0 15,
     t67, .sqdmulh t70 (.const 0xf9dd#16), .mul t70 (.const 0xc0dd#16), .sqdmulh t65 (.const 0x019b#16),
     .sshr t71 1, t73, .const 0xf9dd#16, .sqdmulh t72 (.const 0xff33#16),
     t76, t70, t77, .const 0xff33#16,
     .const 0x29c2#16, t92, .const 0x00b6#16, .const 0xf129#16⟩
    spill := ⟨.const 0x03c2#16, .const 0xc2b6#16, .const 0xf129#16, .const 0x0629#16,
     .const 0x6c6e#16, .const 0x026e#16, .const 0xae55#16, .const 0xbeca#16,
     .const 0x6e1f#16, .const 0x011f#16, .const 0xcf8e#16, .const 0x058e#16,
     .const 0x34d5#16, .const 0x05d5#16, .const 0x0313#16, .const 0xfa13#16,
     .const 0x3999#16, .const 0xfe99#16, .const 0x0d01#16, .const 0x7b0a#16,
     .const 0xfd0a#16, .spill0 21, .spill0 22, .spill0 23,
     .spill0 24, .spill0 25, .spill0 26, .spill0 27,
     .spill0 28, .spill0 29, .spill0 30, .spill0 31,
     .spill0 32, .spill0 33, .spill0 34, .spill0 35,
     .spill0 36, .spill0 37, .spill0 38, .spill0 39⟩
    poly  := ⟨.add t99 t114, .sub t114 t99, .add t115 t116, .sub t116 t115,
     .add t119 t122, .sub t122 t119, .add t123 t124, .sub t124 t123,
     .add t125 t132, .sub t132 t125, .add t133 t134, .sub t134 t133,
     .add t137 t140, .sub t140 t137, .add t141 t142, .sub t142 t141,
     .add t145 t148, .sub t148 t145, .add t149 t150, .sub t150 t149,
     t22, t45, t47, t56,
     t54, t63, t55, t65,
     t76, t72, t77, t70⟩
    gprs  := ⟨.gpr0 0#5 0#64, .gpr0 1#5 0#64, .gpr0 2#5 0#64, .gpr0 3#5 0#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .const64 63965#64, .gpr0 23#5 0#64, .const64 16#64, .gpr0 11#5 0#64,
     .gpr0 12#5 0#64, .gpr0 13#5 0#64, .gpr0 14#5 0#64, .gpr0 15#5 0#64,
     .gpr0 16#5 0#64, .gpr0 17#5 0#64, .gpr0 18#5 0#64, .gpr0 19#5 0#64,
     .gpr0 20#5 0#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

theorem run_seg2_fwd1b : runSymRange cfgSeg2Fwd 871 422 symSeg2MidA = some symSeg2MidB :=
  runSymRange_of_fast (by rfl_kernel)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatSym1b

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4a -- proof-setup: allow-public-import
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4b

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
  (SExpr SymState runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4a (symState4a)

@[expose] def symState4b : SymState :=
  let t0 : SExpr := .add (.poly 30) (.poly 31)
  let t1 : SExpr := .add (.poly 28) (.poly 29)
  let t2 : SExpr := .sub t0 t1
  let t3 : SExpr := .montmul t2 0xff55#16
  let t4 : SExpr := .add (.poly 26) (.poly 27)
  let t5 : SExpr := .add (.poly 24) (.poly 25)
  let t6 : SExpr := .sub t4 t5
  let t7 : SExpr := .montmul t6 0x026e#16
  let t8 : SExpr := .add t3 t7
  let t9 : SExpr := .barrett t8
  let t10 : SExpr := .add (.poly 22) (.poly 23)
  let t11 : SExpr := .add (.poly 20) (.poly 21)
  let t12 : SExpr := .sub t10 t11
  let t13 : SExpr := .montmul t12 0x0629#16
  let t14 : SExpr := .add (.poly 18) (.poly 19)
  let t15 : SExpr := .add (.poly 16) (.poly 17)
  let t16 : SExpr := .sub t14 t15
  let t17 : SExpr := .montmul t16 0x00b6#16
  let t18 : SExpr := .add t13 t17
  let t19 : SExpr := .barrett t18
  let t20 : SExpr := .add t9 t19
  let t21 : SExpr := .barrett t20
  let t22 : SExpr := .montmul (.sub (.poly 31) (.poly 30)) 0x023d#16
  let t23 : SExpr := .montmul (.sub (.poly 29) (.poly 28)) 0xfad3#16
  let t24 : SExpr := .sub t22 t23
  let t25 : SExpr := .montmul t24 0xff55#16
  let t26 : SExpr := .montmul (.sub (.poly 27) (.poly 26)) 0x0108#16
  let t27 : SExpr := .montmul (.sub (.poly 25) (.poly 24)) 0x017f#16
  let t28 : SExpr := .sub t26 t27
  let t29 : SExpr := .montmul t28 0x026e#16
  let t30 : SExpr := .add t25 t29
  let t31 : SExpr := .barrett t30
  let t32 : SExpr := .montmul (.sub (.poly 23) (.poly 22)) 0xfcc3#16
  let t33 : SExpr := .montmul (.sub (.poly 21) (.poly 20)) 0x05b2#16
  let t34 : SExpr := .sub t32 t33
  let t35 : SExpr := .montmul t34 0x0629#16
  let t36 : SExpr := .montmul (.sub (.poly 19) (.poly 18)) 0xf9be#16
  let t37 : SExpr := .montmul (.sub (.poly 17) (.poly 16)) 0xff7e#16
  let t38 : SExpr := .sub t36 t37
  let t39 : SExpr := .montmul t38 0x00b6#16
  let t40 : SExpr := .add t35 t39
  let t41 : SExpr := .barrett t40
  let t42 : SExpr := .add t31 t41
  let t43 : SExpr := .sub t31 t41
  let t44 : SExpr := .sqdmulh t43 (.const 0xfe99#16)
  let t45 : SExpr := .mul t43 (.const 0x3999#16)
  let t46 : SExpr := .sqdmulh t45 (.const 0x0d01#16)
  let t47 : SExpr := .add t22 t23
  let t48 : SExpr := .barrett t47
  let t49 : SExpr := .add t26 t27
  let t50 : SExpr := .barrett t49
  let t51 : SExpr := .sub t48 t50
  let t52 : SExpr := .montmul t51 0x05d5#16
  let t53 : SExpr := .add t32 t33
  let t54 : SExpr := .barrett t53
  let t55 : SExpr := .add t36 t37
  let t56 : SExpr := .barrett t55
  let t57 : SExpr := .sub t54 t56
  let t58 : SExpr := .montmul t57 0x058e#16
  let t59 : SExpr := .add t52 t58
  let t60 : SExpr := .add t0 t1
  let t61 : SExpr := .barrett t60
  let t62 : SExpr := .add t4 t5
  let t63 : SExpr := .barrett t62
  let t64 : SExpr := .sub t61 t63
  let t65 : SExpr := .montmul t64 0x05d5#16
  let t66 : SExpr := .add t10 t11
  let t67 : SExpr := .barrett t66
  let t68 : SExpr := .add t14 t15
  let t69 : SExpr := .barrett t68
  let t70 : SExpr := .sub t67 t69
  let t71 : SExpr := .montmul t70 0x058e#16
  let t72 : SExpr := .add t65 t71
  let t73 : SExpr := .sub t13 t17
  let t74 : SExpr := .mul t70 (.const 0xcf8e#16)
  let t75 : SExpr := .sqdmulh t74 (.const 0x0d01#16)
  let t76 : SExpr := .sshr t75 1
  let t77 : SExpr := .sqdmulh t57 (.const 0x058e#16)
  let t78 : SExpr := .sshr t77 1
  let t79 : SExpr := .mul t57 (.const 0xcf8e#16)
  let t80 : SExpr := .sub t9 t19
  let t81 : SExpr := .montmul t80 0xfe99#16
  let t82 : SExpr := .sub t65 t71
  let t83 : SExpr := .mul t80 (.const 0x3999#16)
  let t84 : SExpr := .sqdmulh t83 (.const 0x0d01#16)
  let t85 : SExpr := .sshr t84 1
  let t86 : SExpr := .sub t52 t58
  let t87 : SExpr := .sqdmulh t42 (.const 0x4ebf#16)
  let t88 : SExpr := .add t87 (.const 0x0400#16)
  let t89 : SExpr := .sshr t88 11
  let t90 : SExpr := .mul t82 (.const 0x3999#16)
  let t91 : SExpr := .montmul t73 0x058e#16
  let t92 : SExpr := .sub t25 t29
  let t93 : SExpr := .montmul t92 0x05d5#16
  let t94 : SExpr := .sqdmulh t72 (.const 0x4ebf#16)
  let t95 : SExpr := .sqdmulh t59 (.const 0x4ebf#16)
  let t96 : SExpr := .add (.poly 14) (.poly 15)
  let t97 : SExpr := .add (.poly 12) (.poly 13)
  let t98 : SExpr := .add t96 t97
  let t99 : SExpr := .barrett t98
  let t100 : SExpr := .add (.poly 10) (.poly 11)
  let t101 : SExpr := .add (.poly 8) (.poly 9)
  let t102 : SExpr := .add t100 t101
  let t103 : SExpr := .barrett t102
  let t104 : SExpr := .sub t99 t103
  let t105 : SExpr := .montmul t104 0x011f#16
  let t106 : SExpr := .add (.poly 6) (.poly 7)
  let t107 : SExpr := .add (.poly 4) (.poly 5)
  let t108 : SExpr := .add t106 t107
  let t109 : SExpr := .barrett t108
  let t110 : SExpr := .add (.poly 2) (.poly 3)
  let t111 : SExpr := .add (.poly 0) (.poly 1)
  let t112 : SExpr := .add t110 t111
  let t113 : SExpr := .barrett t112
  let t114 : SExpr := .sub t109 t113
  let t115 : SExpr := .montmul t114 0x00ca#16
  let t116 : SExpr := .sub t105 t115
  let t117 : SExpr := .sqdmulh t116 (.const 0xfa13#16)
  let t118 : SExpr := .add t99 t103
  let t119 : SExpr := .barrett t118
  let t120 : SExpr := .add t109 t113
  let t121 : SExpr := .barrett t120
  let t122 : SExpr := .add t119 t121
  let t123 : SExpr := .barrett t122
  let t124 : SExpr := .montmul (.sub (.poly 15) (.poly 14)) 0xfd57#16
  let t125 : SExpr := .montmul (.sub (.poly 13) (.poly 12)) 0x03f9#16
  let t126 : SExpr := .add t124 t125
  let t127 : SExpr := .barrett t126
  let t128 : SExpr := .montmul (.sub (.poly 11) (.poly 10)) 0x02dc#16
  let t129 : SExpr := .montmul (.sub (.poly 9) (.poly 8)) 0x0260#16
  let t130 : SExpr := .add t128 t129
  let t131 : SExpr := .barrett t130
  let t132 : SExpr := .add t127 t131
  let t133 : SExpr := .barrett t132
  let t134 : SExpr := .montmul (.sub (.poly 7) (.poly 6)) 0xf9fa#16
  let t135 : SExpr := .montmul (.sub (.poly 5) (.poly 4)) 0x019b#16
  let t136 : SExpr := .add t134 t135
  let t137 : SExpr := .barrett t136
  let t138 : SExpr := .montmul (.sub (.poly 3) (.poly 2)) 0xff33#16
  let t139 : SExpr := .montmul (.sub (.poly 1) (.poly 0)) 0xf9dd#16
  let t140 : SExpr := .add t138 t139
  let t141 : SExpr := .barrett t140
  let t142 : SExpr := .add t137 t141
  let t143 : SExpr := .barrett t142
  let t144 : SExpr := .add t133 t143
  let t145 : SExpr := .barrett t144
  let t146 : SExpr := .sub t96 t97
  let t147 : SExpr := .montmul t146 0x03c2#16
  let t148 : SExpr := .sub t100 t101
  let t149 : SExpr := .montmul t148 0xfb4e#16
  let t150 : SExpr := .add t147 t149
  let t151 : SExpr := .barrett t150
  let t152 : SExpr := .sub t106 t107
  let t153 : SExpr := .montmul t152 0xfa3e#16
  let t154 : SExpr := .sub t110 t111
  let t155 : SExpr := .montmul t154 0x05bc#16
  let t156 : SExpr := .add t153 t155
  let t157 : SExpr := .barrett t156
  let t158 : SExpr := .add t151 t157
  let t159 : SExpr := .barrett t158
  let t160 : SExpr := .sub t124 t125
  let t161 : SExpr := .montmul t160 0x03c2#16
  let t162 : SExpr := .sub t128 t129
  let t163 : SExpr := .montmul t162 0xfb4e#16
  let t164 : SExpr := .add t161 t163
  let t165 : SExpr := .barrett t164
  let t166 : SExpr := .sub t134 t135
  let t167 : SExpr := .montmul t166 0xfa3e#16
  let t168 : SExpr := .sub t138 t139
  let t169 : SExpr := .montmul t168 0x05bc#16
  let t170 : SExpr := .add t167 t169
  let t171 : SExpr := .barrett t170
  let t172 : SExpr := .add t165 t171
  let t173 : SExpr := .barrett t172
  let t174 : SExpr := .add t105 t115
  let t175 : SExpr := .barrett t174
  let t176 : SExpr := .sub t127 t131
  let t177 : SExpr := .montmul t176 0x011f#16
  let t178 : SExpr := .sub t137 t141
  let t179 : SExpr := .montmul t178 0x00ca#16
  let t180 : SExpr := .add t177 t179
  let t181 : SExpr := .barrett t180
  let t182 : SExpr := .sub t147 t149
  let t183 : SExpr := .montmul t182 0x011f#16
  let t184 : SExpr := .sub t153 t155
  let t185 : SExpr := .montmul t184 0x00ca#16
  let t186 : SExpr := .add t183 t185
  let t187 : SExpr := .barrett t186
  let t188 : SExpr := .sub t161 t163
  let t189 : SExpr := .montmul t188 0x011f#16
  let t190 : SExpr := .sub t167 t169
  let t191 : SExpr := .montmul t190 0x00ca#16
  let t192 : SExpr := .add t189 t191
  let t193 : SExpr := .barrett t192
  let t194 : SExpr := .sub t119 t121
  let t195 : SExpr := .montmul t194 0xfa13#16
  let t196 : SExpr := .sub t133 t143
  let t197 : SExpr := .montmul t196 0xfa13#16
  let t198 : SExpr := .sub t151 t157
  let t199 : SExpr := .montmul t198 0xfa13#16
  let t200 : SExpr := .sub t165 t171
  let t201 : SExpr := .montmul t200 0xfa13#16
  let t202 : SExpr := .montmul t116 0xfa13#16
  let t203 : SExpr := .sub t177 t179
  let t204 : SExpr := .montmul t203 0xfa13#16
  let t205 : SExpr := .sub t183 t185
  let t206 : SExpr := .montmul t205 0xfa13#16
  let t207 : SExpr := .sub t189 t191
  let t208 : SExpr := .montmul t207 0xfa13#16
  let t209 : SExpr := .add t61 t63
  let t210 : SExpr := .barrett t209
  let t211 : SExpr := .add t67 t69
  let t212 : SExpr := .barrett t211
  let t213 : SExpr := .add t210 t212
  let t214 : SExpr := .barrett t213
  let t215 : SExpr := .add t48 t50
  let t216 : SExpr := .barrett t215
  let t217 : SExpr := .add t54 t56
  let t218 : SExpr := .barrett t217
  let t219 : SExpr := .add t216 t218
  let t220 : SExpr := .barrett t219
  let t221 : SExpr := .sub t35 t39
  let t222 : SExpr := .montmul t221 0x058e#16
  let t223 : SExpr := .sub t210 t212
  let t224 : SExpr := .montmul t223 0xfe99#16
  let t225 : SExpr := .sub t216 t218
  let t226 : SExpr := .montmul t225 0xfe99#16
  let t227 : SExpr := .sub t3 t7
  let t228 : SExpr := .montmul t227 0x05d5#16
  { vregs := ⟨(.const 0xfe99#16), (.const 0x3999#16), t21, t42, t44, t46, t59, t72, t73, t3, t76, t78, (.const 0xf2ff#16), t74, t79, (.const 0x0d01#16), t81, t82, t85, t86, t89, t90, t71, t91, t93, t94, t58, t95, t117, (.const 0x0400#16), (.const 0xf2ff#16), (.const 0x4ebf#16)⟩
    spill := ⟨(.spill0 0), (.spill0 1), (.spill0 2), (.spill0 3), (.spill0 4), (.spill0 5), (.const 0x4ebf#16), t50, t56, t69, t63, (.const 0x0d01#16), t39⟩
    poly  := ⟨t123, t145, t159, t173, t175, t181, t187, t193, t195, t197, t199, t201, t202, t204, t206, t208, t214, t220, t19, t41, t71, t58, t91, t222, t224, t226, t9, t31, t65, t52, t228, t93⟩
    gprs  := ⟨.spAdd 3440#64, .spAdd 2928#64, .const64 512#64, .const64 31498#64, .const64 573#64, .spAdd 3440#64⟩ }

theorem seg4b_eval : runSymRange (0x18e0 / 4) 514 symState4a = some symState4b := by
  rfl_kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4b

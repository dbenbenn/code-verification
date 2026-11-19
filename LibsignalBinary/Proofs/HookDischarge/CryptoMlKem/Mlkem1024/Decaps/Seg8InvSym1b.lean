/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvSym1a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvSym1b

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (SExpr SymState runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast (runSymRange_of_fast)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvSym1a (cfgSeg8InvSym symSeg8InvSymMidA)

@[expose] def symSeg8InvSymMidB : SymState :=
  let t0 : SExpr := .add (.poly 30) (.poly 31)
  let t1 : SExpr := .add (.poly 28) (.poly 29)
  let t2 : SExpr := .montmul (.sub t0 t1) 0xff55#16
  let t3 : SExpr := .add (.poly 26) (.poly 27)
  let t4 : SExpr := .add (.poly 24) (.poly 25)
  let t5 : SExpr := .montmul (.sub t3 t4) 0x026e#16
  let t6 : SExpr := .barrett (.add t2 t5)
  let t7 : SExpr := .add (.poly 22) (.poly 23)
  let t8 : SExpr := .add (.poly 20) (.poly 21)
  let t9 : SExpr := .montmul (.sub t7 t8) 0x0629#16
  let t10 : SExpr := .add (.poly 18) (.poly 19)
  let t11 : SExpr := .add (.poly 16) (.poly 17)
  let t12 : SExpr := .montmul (.sub t10 t11) 0x00b6#16
  let t13 : SExpr := .barrett (.add t9 t12)
  let t14 : SExpr := .add t6 t13
  let t15 : SExpr := .montmul (.sub (.poly 31) (.poly 30)) 0x023d#16
  let t16 : SExpr := .montmul (.sub (.poly 29) (.poly 28)) 0xfad3#16
  let t17 : SExpr := .montmul (.sub t15 t16) 0xff55#16
  let t18 : SExpr := .montmul (.sub (.poly 27) (.poly 26)) 0x0108#16
  let t19 : SExpr := .montmul (.sub (.poly 25) (.poly 24)) 0x017f#16
  let t20 : SExpr := .montmul (.sub t18 t19) 0x026e#16
  let t21 : SExpr := .barrett (.add t17 t20)
  let t22 : SExpr := .montmul (.sub (.poly 23) (.poly 22)) 0xfcc3#16
  let t23 : SExpr := .montmul (.sub (.poly 21) (.poly 20)) 0x05b2#16
  let t24 : SExpr := .montmul (.sub t22 t23) 0x0629#16
  let t25 : SExpr := .montmul (.sub (.poly 19) (.poly 18)) 0xf9be#16
  let t26 : SExpr := .montmul (.sub (.poly 17) (.poly 16)) 0xff7e#16
  let t27 : SExpr := .montmul (.sub t25 t26) 0x00b6#16
  let t28 : SExpr := .barrett (.add t24 t27)
  let t29 : SExpr := .add t21 t28
  let t30 : SExpr := .add (.sqdmulh t14 (.const 0x4ebf#16)) (.const 0x0400#16)
  let t31 : SExpr := .sub t21 t28
  let t32 : SExpr := .barrett (.add t15 t16)
  let t33 : SExpr := .barrett (.add t18 t19)
  let t34 : SExpr := .montmul (.sub t32 t33) 0x05d5#16
  let t35 : SExpr := .barrett (.add t22 t23)
  let t36 : SExpr := .barrett (.add t25 t26)
  let t37 : SExpr := .sub t35 t36
  let t38 : SExpr := .montmul t37 0x058e#16
  let t39 : SExpr := .barrett (.add t0 t1)
  let t40 : SExpr := .barrett (.add t3 t4)
  let t41 : SExpr := .montmul (.sub t39 t40) 0x05d5#16
  let t42 : SExpr := .barrett (.add t7 t8)
  let t43 : SExpr := .barrett (.add t10 t11)
  let t44 : SExpr := .sub t42 t43
  let t45 : SExpr := .montmul t44 0x058e#16
  let t46 : SExpr := .add t41 t45
  let t47 : SExpr := .sub t9 t12
  let t48 : SExpr := .mul t44 (.const 0xcf8e#16)
  let t49 : SExpr := .sshr (.sqdmulh t48 (.const 0x0d01#16)) 1
  let t50 : SExpr := .sshr (.sqdmulh t37 (.const 0x058e#16)) 1
  let t51 : SExpr := .sub t6 t13
  let t52 : SExpr := .sqdmulh (.mul t51 (.const 0x3999#16)) (.const 0x0d01#16)
  let t53 : SExpr := .barrett (.add t32 t33)
  let t54 : SExpr := .barrett (.add t35 t36)
  let t55 : SExpr := .montmul (.sub t53 t54) 0xfe99#16
  let t56 : SExpr := .add (.sqdmulh t29 (.const 0x4ebf#16)) (.const 0x0400#16)
  let t57 : SExpr := .sshr (.sqdmulh t51 (.const 0xfe99#16)) 1
  let t58 : SExpr := .montmul (.sub t17 t20) 0x05d5#16
  let t59 : SExpr := .add (.poly 14) (.poly 15)
  let t60 : SExpr := .add (.poly 12) (.poly 13)
  let t61 : SExpr := .barrett (.add t59 t60)
  let t62 : SExpr := .add (.poly 10) (.poly 11)
  let t63 : SExpr := .add (.poly 8) (.poly 9)
  let t64 : SExpr := .barrett (.add t62 t63)
  let t65 : SExpr := .montmul (.sub t61 t64) 0x011f#16
  let t66 : SExpr := .add (.poly 6) (.poly 7)
  let t67 : SExpr := .add (.poly 4) (.poly 5)
  let t68 : SExpr := .barrett (.add t66 t67)
  let t69 : SExpr := .add (.poly 2) (.poly 3)
  let t70 : SExpr := .add (.poly 0) (.poly 1)
  let t71 : SExpr := .barrett (.add t69 t70)
  let t72 : SExpr := .montmul (.sub t68 t71) 0x00ca#16
  let t73 : SExpr := .sub t65 t72
  let t74 : SExpr := .barrett (.add t61 t64)
  let t75 : SExpr := .barrett (.add t68 t71)
  let t76 : SExpr := .barrett (.add t74 t75)
  let t77 : SExpr := .montmul (.sub (.poly 15) (.poly 14)) 0xfd57#16
  let t78 : SExpr := .montmul (.sub (.poly 13) (.poly 12)) 0x03f9#16
  let t79 : SExpr := .barrett (.add t77 t78)
  let t80 : SExpr := .montmul (.sub (.poly 11) (.poly 10)) 0x02dc#16
  let t81 : SExpr := .montmul (.sub (.poly 9) (.poly 8)) 0x0260#16
  let t82 : SExpr := .barrett (.add t80 t81)
  let t83 : SExpr := .barrett (.add t79 t82)
  let t84 : SExpr := .montmul (.sub (.poly 7) (.poly 6)) 0xf9fa#16
  let t85 : SExpr := .montmul (.sub (.poly 5) (.poly 4)) 0x019b#16
  let t86 : SExpr := .barrett (.add t84 t85)
  let t87 : SExpr := .montmul (.sub (.poly 3) (.poly 2)) 0xff33#16
  let t88 : SExpr := .montmul (.sub (.poly 1) (.poly 0)) 0xf9dd#16
  let t89 : SExpr := .barrett (.add t87 t88)
  let t90 : SExpr := .barrett (.add t86 t89)
  let t91 : SExpr := .barrett (.add t83 t90)
  let t92 : SExpr := .montmul (.sub t59 t60) 0x03c2#16
  let t93 : SExpr := .montmul (.sub t62 t63) 0xfb4e#16
  let t94 : SExpr := .barrett (.add t92 t93)
  let t95 : SExpr := .montmul (.sub t66 t67) 0xfa3e#16
  let t96 : SExpr := .montmul (.sub t69 t70) 0x05bc#16
  let t97 : SExpr := .barrett (.add t95 t96)
  let t98 : SExpr := .barrett (.add t94 t97)
  let t99 : SExpr := .montmul (.sub t77 t78) 0x03c2#16
  let t100 : SExpr := .montmul (.sub t80 t81) 0xfb4e#16
  let t101 : SExpr := .barrett (.add t99 t100)
  let t102 : SExpr := .montmul (.sub t84 t85) 0xfa3e#16
  let t103 : SExpr := .montmul (.sub t87 t88) 0x05bc#16
  let t104 : SExpr := .barrett (.add t102 t103)
  let t105 : SExpr := .barrett (.add t101 t104)
  let t106 : SExpr := .barrett (.add t65 t72)
  let t107 : SExpr := .montmul (.sub t79 t82) 0x011f#16
  let t108 : SExpr := .montmul (.sub t86 t89) 0x00ca#16
  let t109 : SExpr := .barrett (.add t107 t108)
  let t110 : SExpr := .montmul (.sub t92 t93) 0x011f#16
  let t111 : SExpr := .montmul (.sub t95 t96) 0x00ca#16
  let t112 : SExpr := .barrett (.add t110 t111)
  let t113 : SExpr := .montmul (.sub t99 t100) 0x011f#16
  let t114 : SExpr := .montmul (.sub t102 t103) 0x00ca#16
  let t115 : SExpr := .barrett (.add t113 t114)
  let t116 : SExpr := .montmul (.sub t74 t75) 0xfa13#16
  let t117 : SExpr := .montmul (.sub t83 t90) 0xfa13#16
  let t118 : SExpr := .montmul (.sub t94 t97) 0xfa13#16
  let t119 : SExpr := .montmul (.sub t101 t104) 0xfa13#16
  let t120 : SExpr := .montmul (.sub t107 t108) 0xfa13#16
  let t121 : SExpr := .montmul (.sub t110 t111) 0xfa13#16
  let t122 : SExpr := .montmul (.sub t113 t114) 0xfa13#16
  let t123 : SExpr := .barrett (.add t39 t40)
  let t124 : SExpr := .barrett (.add t42 t43)
  let t125 : SExpr := .barrett (.add t123 t124)
  let t126 : SExpr := .barrett (.add t53 t54)
  let t127 : SExpr := .montmul (.sub t24 t27) 0x058e#16
  let t128 : SExpr := .montmul (.sub t123 t124) 0xfe99#16
  let t129 : SExpr := .montmul (.sub t2 t5) 0x05d5#16
  { vregs := ⟨.const 0xfe99#16, .const 0x3999#16, t14, t29,
     .sshr t30 11, .mul t31 (.const 0x3999#16), .add t34 t38, t46,
     t47, t2, t49, t50,
     .const 0xf2ff#16, t48, .mul t37 (.const 0xcf8e#16), .const 0x0d01#16,
     t31, .sub t41 t45, .sshr t52 1, t55,
     .sshr t56 11, t57, t45, t34,
     t58, .sqdmulh t46 (.const 0x4ebf#16), t38, t56,
     .sqdmulh t73 (.const 0xfa13#16), .const 0x0400#16, .const 0xf2ff#16, .const 0x4ebf#16⟩
    spill := ⟨.const 0x4ebf#16, t33, t36, t43,
     t40, .const 0x0d01#16, t27, .spill0 7,
     .spill0 8, .spill0 9, .spill0 10, .spill0 11,
     .spill0 12, .spill0 13, .spill0 14, .spill0 15,
     .spill0 16, .spill0 17, .spill0 18, .spill0 19,
     .spill0 20, .spill0 21, .spill0 22, .spill0 23,
     .spill0 24, .spill0 25, .spill0 26, .spill0 27,
     .spill0 28, .spill0 29, .spill0 30, .spill0 31,
     .spill0 32, .spill0 33, .spill0 34, .spill0 35,
     .spill0 36, .spill0 37, .spill0 38, .spill0 39⟩
    poly  := ⟨t76, t91, t98, t105,
     t106, t109, t112, t115,
     t116, t117, t118, t119,
     .montmul t73 0xfa13#16, t120, t121, t122,
     t125, t126, t13, t28,
     t45, t38, .montmul t47 0x058e#16, t127,
     t128, t55, t6, t21,
     t41, t34, t129, t58⟩
    gprs  := ⟨.spAdd 32496#64, .spAdd 28368#64, .const64 512#64, .gpr0 3#5 0#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .const64 31498#64, .const64 573#64, .gpr0 10#5 0#64, .gpr0 11#5 0#64,
     .gpr0 12#5 0#64, .gpr0 13#5 0#64, .gpr0 14#5 0#64, .gpr0 15#5 0#64,
     .gpr0 16#5 0#64, .gpr0 17#5 0#64, .gpr0 18#5 0#64, .spAdd 32496#64,
     .gpr0 20#5 0#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

theorem run_seg8_inv1b : runSymRange cfgSeg8InvSym 12662 520 symSeg8InvSymMidA = some symSeg8InvSymMidB :=
  runSymRange_of_fast (by rfl_kernel)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvSym1b

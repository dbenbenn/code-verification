/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2a -- proof-setup: allow-public-import
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2b

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (SExpr SymState runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2a (cfgInv2 symInv2MidA)

@[expose] def symInv2MidB : SymState :=
  let t0 : SExpr := .add (.poly 30) (.poly 31)
  let t1 : SExpr := .add (.poly 28) (.poly 29)
  let t2 : SExpr := .barrett (.add t0 t1)
  let t3 : SExpr := .add (.poly 26) (.poly 27)
  let t4 : SExpr := .add (.poly 24) (.poly 25)
  let t5 : SExpr := .barrett (.add t3 t4)
  let t6 : SExpr := .montmul (.sub t2 t5) 0x05d5#16
  let t7 : SExpr := .add (.poly 22) (.poly 23)
  let t8 : SExpr := .add (.poly 20) (.poly 21)
  let t9 : SExpr := .barrett (.add t7 t8)
  let t10 : SExpr := .add (.poly 18) (.poly 19)
  let t11 : SExpr := .add (.poly 16) (.poly 17)
  let t12 : SExpr := .barrett (.add t10 t11)
  let t13 : SExpr := .montmul (.sub t9 t12) 0x058e#16
  let t14 : SExpr := .montmul (.sub (.poly 31) (.poly 30)) 0x023d#16
  let t15 : SExpr := .montmul (.sub (.poly 29) (.poly 28)) 0xfad3#16
  let t16 : SExpr := .barrett (.add t14 t15)
  let t17 : SExpr := .montmul (.sub (.poly 27) (.poly 26)) 0x0108#16
  let t18 : SExpr := .montmul (.sub (.poly 25) (.poly 24)) 0x017f#16
  let t19 : SExpr := .barrett (.add t17 t18)
  let t20 : SExpr := .montmul (.sub t16 t19) 0x05d5#16
  let t21 : SExpr := .montmul (.sub (.poly 23) (.poly 22)) 0xfcc3#16
  let t22 : SExpr := .montmul (.sub (.poly 21) (.poly 20)) 0x05b2#16
  let t23 : SExpr := .barrett (.add t21 t22)
  let t24 : SExpr := .montmul (.sub (.poly 19) (.poly 18)) 0xf9be#16
  let t25 : SExpr := .montmul (.sub (.poly 17) (.poly 16)) 0xff7e#16
  let t26 : SExpr := .barrett (.add t24 t25)
  let t27 : SExpr := .montmul (.sub t23 t26) 0x058e#16
  let t28 : SExpr := .add t20 t27
  let t29 : SExpr := .montmul (.sub t14 t15) 0xff55#16
  let t30 : SExpr := .montmul (.sub t17 t18) 0x026e#16
  let t31 : SExpr := .barrett (.add t29 t30)
  let t32 : SExpr := .montmul (.sub t21 t22) 0x0629#16
  let t33 : SExpr := .montmul (.sub t24 t25) 0x00b6#16
  let t34 : SExpr := .barrett (.add t32 t33)
  let t35 : SExpr := .sub t31 t34
  let t36 : SExpr := .sqdmulh (.mul t35 (.const 0x3999#16)) (.const 0x0d01#16)
  let t37 : SExpr := .montmul (.sub t0 t1) 0xff55#16
  let t38 : SExpr := .montmul (.sub t3 t4) 0x026e#16
  let t39 : SExpr := .barrett (.add t37 t38)
  let t40 : SExpr := .montmul (.sub t7 t8) 0x0629#16
  let t41 : SExpr := .montmul (.sub t10 t11) 0x00b6#16
  let t42 : SExpr := .barrett (.add t40 t41)
  let t43 : SExpr := .barrett (.add t39 t42)
  let t44 : SExpr := .add t6 t13
  let t45 : SExpr := .barrett (.add t2 t5)
  let t46 : SExpr := .barrett (.add t16 t19)
  let t47 : SExpr := .add (.poly 14) (.poly 15)
  let t48 : SExpr := .add (.poly 12) (.poly 13)
  let t49 : SExpr := .montmul (.sub t47 t48) 0x03c2#16
  let t50 : SExpr := .add (.poly 10) (.poly 11)
  let t51 : SExpr := .add (.poly 8) (.poly 9)
  let t52 : SExpr := .montmul (.sub t50 t51) 0xfb4e#16
  let t53 : SExpr := .barrett (.add t49 t52)
  let t54 : SExpr := .sub t49 t52
  let t55 : SExpr := .barrett (.add t31 t34)
  let t56 : SExpr := .sshr (.sqdmulh t35 (.const 0xfe99#16)) 1
  let t57 : SExpr := .sub t39 t42
  let t58 : SExpr := .mul t57 (.const 0x3999#16)
  let t59 : SExpr := .sshr (.sqdmulh t58 (.const 0x0d01#16)) 1
  let t60 : SExpr := .montmul (.sub t29 t30) 0x05d5#16
  let t61 : SExpr := .montmul (.sub t37 t38) 0x05d5#16
  let t62 : SExpr := .barrett (.add t47 t48)
  let t63 : SExpr := .barrett (.add t50 t51)
  let t64 : SExpr := .barrett (.add t62 t63)
  let t65 : SExpr := .montmul (.sub (.poly 15) (.poly 14)) 0xfd57#16
  let t66 : SExpr := .montmul (.sub (.poly 13) (.poly 12)) 0x03f9#16
  let t67 : SExpr := .barrett (.add t65 t66)
  let t68 : SExpr := .montmul (.sub (.poly 11) (.poly 10)) 0x02dc#16
  let t69 : SExpr := .montmul (.sub (.poly 9) (.poly 8)) 0x0260#16
  let t70 : SExpr := .barrett (.add t68 t69)
  let t71 : SExpr := .barrett (.add t67 t70)
  let t72 : SExpr := .montmul (.sub t62 t63) 0x011f#16
  let t73 : SExpr := .montmul (.sub t67 t70) 0x011f#16
  let t74 : SExpr := .montmul (.sub (.poly 7) (.poly 6)) 0xf9fa#16
  let t75 : SExpr := .montmul (.sub (.poly 5) (.poly 4)) 0x019b#16
  let t76 : SExpr := .montmul (.sub t74 t75) 0xfa3e#16
  let t77 : SExpr := .montmul (.sub (.poly 3) (.poly 2)) 0xff33#16
  let t78 : SExpr := .montmul (.sub (.poly 1) (.poly 0)) 0xf9dd#16
  let t79 : SExpr := .montmul (.sub t77 t78) 0x05bc#16
  let t80 : SExpr := .barrett (.add t76 t79)
  let t81 : SExpr := .add (.poly 6) (.poly 7)
  let t82 : SExpr := .add (.poly 4) (.poly 5)
  let t83 : SExpr := .montmul (.sub t81 t82) 0xfa3e#16
  let t84 : SExpr := .add (.poly 2) (.poly 3)
  let t85 : SExpr := .add (.poly 0) (.poly 1)
  let t86 : SExpr := .montmul (.sub t84 t85) 0x05bc#16
  let t87 : SExpr := .barrett (.add t83 t86)
  let t88 : SExpr := .barrett (.add t81 t82)
  let t89 : SExpr := .barrett (.add t84 t85)
  let t90 : SExpr := .barrett (.add t88 t89)
  let t91 : SExpr := .montmul (.sub t65 t66) 0x03c2#16
  let t92 : SExpr := .barrett (.add t74 t75)
  let t93 : SExpr := .barrett (.add t77 t78)
  let t94 : SExpr := .barrett (.add t92 t93)
  let t95 : SExpr := .montmul (.sub t68 t69) 0xfb4e#16
  let t96 : SExpr := .montmul (.sub t92 t93) 0x00ca#16
  let t97 : SExpr := .montmul (.sub t88 t89) 0x00ca#16
  let t98 : SExpr := .montmul (.sub t83 t86) 0x00ca#16
  let t99 : SExpr := .montmul (.sub t76 t79) 0x00ca#16
  let t100 : SExpr := .barrett (.add t64 t90)
  let t101 : SExpr := .barrett (.add t71 t94)
  let t102 : SExpr := .barrett (.add t53 t87)
  let t103 : SExpr := .barrett (.add t91 t95)
  let t104 : SExpr := .barrett (.add t103 t80)
  let t105 : SExpr := .barrett (.add t72 t97)
  let t106 : SExpr := .barrett (.add t73 t96)
  let t107 : SExpr := .montmul t54 0x011f#16
  let t108 : SExpr := .barrett (.add t107 t98)
  let t109 : SExpr := .montmul (.sub t91 t95) 0x011f#16
  let t110 : SExpr := .barrett (.add t109 t99)
  let t111 : SExpr := .montmul (.sub t64 t90) 0xfa13#16
  let t112 : SExpr := .montmul (.sub t71 t94) 0xfa13#16
  let t113 : SExpr := .montmul (.sub t53 t87) 0xfa13#16
  let t114 : SExpr := .montmul (.sub t103 t80) 0xfa13#16
  let t115 : SExpr := .montmul (.sub t72 t97) 0xfa13#16
  let t116 : SExpr := .montmul (.sub t73 t96) 0xfa13#16
  let t117 : SExpr := .montmul (.sub t107 t98) 0xfa13#16
  let t118 : SExpr := .montmul (.sub t109 t99) 0xfa13#16
  let t119 : SExpr := .barrett (.add t9 t12)
  let t120 : SExpr := .barrett (.add t45 t119)
  let t121 : SExpr := .barrett (.add t23 t26)
  let t122 : SExpr := .barrett (.add t46 t121)
  let t123 : SExpr := .montmul (.sub t40 t41) 0x058e#16
  let t124 : SExpr := .montmul (.sub t32 t33) 0x058e#16
  let t125 : SExpr := .montmul (.sub t45 t119) 0xfe99#16
  let t126 : SExpr := .montmul (.sub t46 t121) 0xfe99#16
  { vregs := ⟨.vreg0 0, .sub t6 t13, .sqdmulh t28 (.const 0x4ebf#16), .const 0xfe99#16,
     .const 0x3999#16, .sshr t36 1, t43, t44,
     .const 0xf2ff#16, t45, t29, t46,
     t39, .const 0x05d5#16, t53, t54,
     .const 0x0d01#16, .const 0x4ebf#16, t55, t28,
     t56, .montmul t57 0xfe99#16, .sub t20 t27, .const 0x0400#16,
     t59, t13, t60, t61,
     t36, .sqdmulh t44 (.const 0x4ebf#16), t58, .const 0xf2ff#16⟩
    spill13 := ⟨.spill13_0 0, .spill13_0 1, .spill13_0 2, .spill13_0 3,
     .spill13_0 4, .spill13_0 5, .spill13_0 6, .spill13_0 7,
     .spill13_0 8, .spill13_0 9, .spill13_0 10, .spill13_0 11,
     .spill13_0 12⟩
    spill6 := ⟨t64, t2, t71, t37,
     t32, t29⟩
    spill21 := ⟨t72, t73, t26, t41,
     t38, t33, t49, t30,
     t80, t87, t90, t91,
     t5, t94, t19, t52,
     t95, t96, t97, t98,
     t99⟩
    poly := ⟨t100, t101, t102, t104,
     t105, t106, t108, t110,
     t111, t112, t113, t114,
     t115, t116, t117, t118,
     t120, t122, t42, t34,
     t13, t27, t123, t124,
     t125, t126, t39, t31,
     t6, t20, t61, t60⟩
    gprs := ⟨.gpr0 0, .gpr0 1, .gpr0 2, .gpr0 3, .gpr0 4, .gpr0 5,
     .gpr0 6, .gpr0 7, .gpr0 8, .gpr0 9, .gpr0 10, .gpr0 11,
     .addReg (.gpr0 20) (.gpr0 10), .gpr0 13, .gpr0 14, .gpr0 15, .gpr0 16, .gpr0 17,
     .gpr0 18, .gpr0 19, .gpr0 20, .const64 64778#64, .const64 31498#64, .gpr0 23,
     .gpr0 24, .gpr0 25, .gpr0 26, .const64 0#64, .gpr0 28, .gpr0 29,
     .gpr0 30⟩
    pstate := .pstate0 }

theorem run_inv2b : runSymRange cfgInv2 9819 486 symInv2MidA = some symInv2MidB := by
  rfl_kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2b

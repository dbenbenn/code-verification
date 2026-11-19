/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4a

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
  (SExpr SymState symInit4 runSymRange)

@[expose] def symState4a : SymState :=
  let t0 : SExpr := .add (.poly 26) (.poly 27)
  let t1 : SExpr := .add (.poly 24) (.poly 25)
  let t2 : SExpr := .add t0 t1
  let t3 : SExpr := .barrett t2
  let t4 : SExpr := .montmul (.sub (.poly 27) (.poly 26)) 0x0108#16
  let t5 : SExpr := .montmul (.sub (.poly 25) (.poly 24)) 0x017f#16
  let t6 : SExpr := .add t4 t5
  let t7 : SExpr := .add (.poly 22) (.poly 23)
  let t8 : SExpr := .add (.poly 20) (.poly 21)
  let t9 : SExpr := .add t7 t8
  let t10 : SExpr := .barrett t9
  let t11 : SExpr := .add (.poly 18) (.poly 19)
  let t12 : SExpr := .add (.poly 16) (.poly 17)
  let t13 : SExpr := .sub t11 t12
  let t14 : SExpr := .montmul t13 0x00b6#16
  let t15 : SExpr := .sub t7 t8
  let t16 : SExpr := .montmul t15 0x0629#16
  let t17 : SExpr := .sqdmulh t2 (.const 0x4ebf#16)
  let t18 : SExpr := .add t17 (.const 0x0400#16)
  let t19 : SExpr := .sshr t18 11
  let t20 : SExpr := .sub t0 t1
  let t21 : SExpr := .sqdmulh t20 (.const 0x026e#16)
  let t22 : SExpr := .add (.poly 6) (.poly 7)
  let t23 : SExpr := .add (.poly 4) (.poly 5)
  let t24 : SExpr := .add t22 t23
  let t25 : SExpr := .barrett t24
  let t26 : SExpr := .add (.poly 2) (.poly 3)
  let t27 : SExpr := .add (.poly 0) (.poly 1)
  let t28 : SExpr := .add t26 t27
  let t29 : SExpr := .barrett t28
  let t30 : SExpr := .add t25 t29
  let t31 : SExpr := .sqdmulh t30 (.const 0x4ebf#16)
  let t32 : SExpr := .montmul (.sub (.poly 7) (.poly 6)) 0xf9fa#16
  let t33 : SExpr := .montmul (.sub (.poly 5) (.poly 4)) 0x019b#16
  let t34 : SExpr := .add t32 t33
  let t35 : SExpr := .barrett t34
  let t36 : SExpr := .montmul (.sub (.poly 3) (.poly 2)) 0xff33#16
  let t37 : SExpr := .montmul (.sub (.poly 1) (.poly 0)) 0xf9dd#16
  let t38 : SExpr := .add t36 t37
  let t39 : SExpr := .barrett t38
  let t40 : SExpr := .add t35 t39
  let t41 : SExpr := .sqdmulh t40 (.const 0x4ebf#16)
  let t42 : SExpr := .sub t25 t29
  let t43 : SExpr := .mul t42 (.const 0xbeca#16)
  let t44 : SExpr := .montmul (.sub (.poly 23) (.poly 22)) 0xfcc3#16
  let t45 : SExpr := .montmul (.sub (.poly 21) (.poly 20)) 0x05b2#16
  let t46 : SExpr := .add t44 t45
  let t47 : SExpr := .barrett t46
  let t48 : SExpr := .sub t44 t45
  let t49 : SExpr := .sqdmulh t48 (.const 0x0629#16)
  let t50 : SExpr := .sshr t49 1
  let t51 : SExpr := .sub t4 t5
  let t52 : SExpr := .sqdmulh t51 (.const 0x026e#16)
  let t53 : SExpr := .montmul t48 0x0629#16
  let t54 : SExpr := .mul t48 (.const 0xf129#16)
  let t55 : SExpr := .sqdmulh t54 (.const 0x0d01#16)
  let t56 : SExpr := .sshr t55 1
  let t57 : SExpr := .mul t51 (.const 0x6c6e#16)
  let t58 : SExpr := .sqdmulh t6 (.const 0x4ebf#16)
  let t59 : SExpr := .mul t20 (.const 0x6c6e#16)
  let t60 : SExpr := .montmul (.sub (.poly 19) (.poly 18)) 0xf9be#16
  let t61 : SExpr := .montmul (.sub (.poly 17) (.poly 16)) 0xff7e#16
  let t62 : SExpr := .add t60 t61
  let t63 : SExpr := .barrett t62
  let t64 : SExpr := .add t11 t12
  let t65 : SExpr := .barrett t64
  let t66 : SExpr := .montmul (.sub (.poly 31) (.poly 30)) 0x023d#16
  let t67 : SExpr := .sub t60 t61
  let t68 : SExpr := .montmul t67 0x00b6#16
  let t69 : SExpr := .sub t26 t27
  let t70 : SExpr := .montmul t69 0x05bc#16
  let t71 : SExpr := .sub t36 t37
  let t72 : SExpr := .montmul t71 0x05bc#16
  let t73 : SExpr := .sub t22 t23
  let t74 : SExpr := .montmul t73 0xfa3e#16
  let t75 : SExpr := .sub t32 t33
  let t76 : SExpr := .montmul t75 0xfa3e#16
  let t77 : SExpr := .add (.poly 10) (.poly 11)
  let t78 : SExpr := .add (.poly 8) (.poly 9)
  let t79 : SExpr := .add t77 t78
  let t80 : SExpr := .barrett t79
  let t81 : SExpr := .montmul (.sub (.poly 11) (.poly 10)) 0x02dc#16
  let t82 : SExpr := .montmul (.sub (.poly 9) (.poly 8)) 0x0260#16
  let t83 : SExpr := .add t81 t82
  let t84 : SExpr := .barrett t83
  let t85 : SExpr := .sub t77 t78
  let t86 : SExpr := .montmul t85 0xfb4e#16
  let t87 : SExpr := .sub t81 t82
  let t88 : SExpr := .montmul t87 0xfb4e#16
  let t89 : SExpr := .add (.poly 14) (.poly 15)
  let t90 : SExpr := .add (.poly 12) (.poly 13)
  let t91 : SExpr := .add t89 t90
  let t92 : SExpr := .barrett t91
  let t93 : SExpr := .montmul (.sub (.poly 15) (.poly 14)) 0xfd57#16
  let t94 : SExpr := .montmul (.sub (.poly 13) (.poly 12)) 0x03f9#16
  let t95 : SExpr := .add t93 t94
  let t96 : SExpr := .barrett t95
  let t97 : SExpr := .sub t89 t90
  let t98 : SExpr := .montmul t97 0x03c2#16
  let t99 : SExpr := .sub t93 t94
  let t100 : SExpr := .montmul t99 0x03c2#16
  { vregs := ⟨t3, (.const 0xf2ff#16), t6, (.const 0x0400#16), t10, t4, t14, t16, t19, t21, t31, t41, t43, (.const 0x0d01#16), (.const 0xf2ff#16), (.const 0x4ebf#16), t47, t50, t52, t53, t56, (.const 0x00ca#16), t57, (.const 0xbeca#16), t30, t40, t35, t58, (.const 0x026e#16), t39, t59, t42⟩
    spill := ⟨(.spill0 0), (.spill0 1), (.spill0 2), (.spill0 3), (.spill0 4), (.spill0 5), (.spill0 6), t4, t63, t65, t66, (.spill0 11), t68⟩
    poly  := ⟨t29, t39, t70, t72, t25, t35, t74, t76, t80, t84, t86, t88, t92, t96, t98, t100, t12, t61, t11, t60, t8, t45, t7, t44, t1, t5, t0, t4, (.add (.poly 28) (.poly 29)), (.montmul (.sub (.poly 29) (.poly 28)) 0xfad3#16), (.add (.poly 30) (.poly 31)), t66⟩
    gprs  := ⟨.spAdd 3440#64, .spAdd 2928#64, .const64 512#64, .const64 28191#64, .const64 573#64, .spAdd 3440#64⟩ }

theorem seg4a_eval : runSymRange (0x10a0 / 4) 528 symInit4 = some symState4a := by
  rfl_kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4a

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1a

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (SExpr SymCfg SymState runSymRange)

@[expose] def cfgFwd1 : SymCfg := ⟨some 21#5, .s21, false⟩

@[expose] def symFwd1Init : SymState :=
  { vregs := ⟨.vreg0 0, .vreg0 1, .vreg0 2, .vreg0 3,
     .vreg0 4, .vreg0 5, .vreg0 6, .vreg0 7,
     .vreg0 8, .vreg0 9, .vreg0 10, .vreg0 11,
     .vreg0 12, .vreg0 13, .vreg0 14, .vreg0 15,
     .vreg0 16, .vreg0 17, .vreg0 18, .vreg0 19,
     .vreg0 20, .vreg0 21, .vreg0 22, .vreg0 23,
     .vreg0 24, .vreg0 25, .vreg0 26, .vreg0 27,
     .vreg0 28, .vreg0 29, .vreg0 30, .vreg0 31⟩
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
    poly := ⟨.poly 0, .poly 1, .poly 2, .poly 3,
     .poly 4, .poly 5, .poly 6, .poly 7,
     .poly 8, .poly 9, .poly 10, .poly 11,
     .poly 12, .poly 13, .poly 14, .poly 15,
     .poly 16, .poly 17, .poly 18, .poly 19,
     .poly 20, .poly 21, .poly 22, .poly 23,
     .poly 24, .poly 25, .poly 26, .poly 27,
     .poly 28, .poly 29, .poly 30, .poly 31⟩
    gprs := ⟨.gpr0 0, .gpr0 1, .gpr0 2, .gpr0 3, .gpr0 4, .gpr0 5,
     .gpr0 6, .gpr0 7, .gpr0 8, .gpr0 9, .gpr0 10, .gpr0 11,
     .gpr0 12, .gpr0 13, .gpr0 14, .gpr0 15, .gpr0 16, .gpr0 17,
     .gpr0 18, .gpr0 19, .gpr0 20, .gpr0 21, .gpr0 22, .gpr0 23,
     .gpr0 24, .gpr0 25, .gpr0 26, .gpr0 27, .gpr0 28, .gpr0 29,
     .gpr0 30⟩
    pstate := .pstate0 }

@[expose] def symFwd1MidA : SymState :=
  let t0 : SExpr := .montmul (.poly 17) 0xfd0a#16
  let t1 : SExpr := .sub (.poly 1) t0
  let t2 : SExpr := .montmul (.poly 25) 0xfd0a#16
  let t3 : SExpr := .montmul (.sub (.poly 9) t2) 0xfa13#16
  let t4 : SExpr := .montmul (.poly 19) 0xfd0a#16
  let t5 : SExpr := .sub (.poly 3) t4
  let t6 : SExpr := .montmul (.poly 27) 0xfd0a#16
  let t7 : SExpr := .montmul (.sub (.poly 11) t6) 0xfa13#16
  let t8 : SExpr := .montmul (.poly 18) 0xfd0a#16
  let t9 : SExpr := .sub (.poly 2) t8
  let t10 : SExpr := .montmul (.poly 26) 0xfd0a#16
  let t11 : SExpr := .montmul (.sub (.poly 10) t10) 0xfa13#16
  let t12 : SExpr := .montmul (.poly 16) 0xfd0a#16
  let t13 : SExpr := .sub (.poly 0) t12
  let t14 : SExpr := .montmul (.poly 24) 0xfd0a#16
  let t15 : SExpr := .montmul (.sub (.poly 8) t14) 0xfa13#16
  let t16 : SExpr := .montmul (.poly 23) 0xfd0a#16
  let t17 : SExpr := .sub (.poly 7) t16
  let t18 : SExpr := .montmul (.poly 31) 0xfd0a#16
  let t19 : SExpr := .montmul (.sub (.poly 15) t18) 0xfa13#16
  let t20 : SExpr := .montmul (.poly 22) 0xfd0a#16
  let t21 : SExpr := .sub (.poly 6) t20
  let t22 : SExpr := .montmul (.poly 30) 0xfd0a#16
  let t23 : SExpr := .montmul (.sub (.poly 14) t22) 0xfa13#16
  let t24 : SExpr := .montmul (.poly 21) 0xfd0a#16
  let t25 : SExpr := .sub (.poly 5) t24
  let t26 : SExpr := .montmul (.poly 29) 0xfd0a#16
  let t27 : SExpr := .montmul (.sub (.poly 13) t26) 0xfa13#16
  let t28 : SExpr := .add t27 t25
  let t29 : SExpr := .montmul (.poly 20) 0xfd0a#16
  let t30 : SExpr := .sub (.poly 4) t29
  let t31 : SExpr := .montmul (.poly 28) 0xfd0a#16
  let t32 : SExpr := .montmul (.sub (.poly 12) t31) 0xfa13#16
  let t33 : SExpr := .add t32 t30
  let t34 : SExpr := .add t19 t17
  let t35 : SExpr := .sqdmulh (.mul t34 (.const 0x6e1f#16)) (.const 0x0d01#16)
  let t36 : SExpr := .add t4 (.poly 3)
  let t37 : SExpr := .montmul (.add t6 (.poly 11)) 0xfe99#16
  let t38 : SExpr := .sub t36 t37
  let t39 : SExpr := .add t16 (.poly 7)
  let t40 : SExpr := .montmul (.add t18 (.poly 15)) 0xfe99#16
  let t41 : SExpr := .montmul (.sub t39 t40) 0x058e#16
  let t42 : SExpr := .sub t38 t41
  let t43 : SExpr := .add t15 t13
  let t44 : SExpr := .add t3 t1
  let t45 : SExpr := .add t23 t21
  let t46 : SExpr := .sshr (.sqdmulh t45 (.const 0x011f#16)) 1
  let t47 : SExpr := .sshr (.sqdmulh t33 (.const 0x011f#16)) 1
  let t48 : SExpr := .sqdmulh (.mul t45 (.const 0x6e1f#16)) (.const 0x0d01#16)
  let t49 : SExpr := .montmul (.add t31 (.poly 12)) 0xfe99#16
  let t50 : SExpr := .add t29 (.poly 4)
  let t51 : SExpr := .montmul (.add t49 t50) 0x05d5#16
  let t52 : SExpr := .montmul (.add t14 (.poly 8)) 0xfe99#16
  let t53 : SExpr := .add t12 (.poly 0)
  let t54 : SExpr := .add t52 t53
  let t55 : SExpr := .montmul (.add t26 (.poly 13)) 0xfe99#16
  let t56 : SExpr := .add t24 (.poly 5)
  let t57 : SExpr := .montmul (.add t55 t56) 0x05d5#16
  let t58 : SExpr := .montmul (.add t2 (.poly 9)) 0xfe99#16
  let t59 : SExpr := .add t0 (.poly 1)
  let t60 : SExpr := .add t58 t59
  let t61 : SExpr := .montmul (.add t22 (.poly 14)) 0xfe99#16
  let t62 : SExpr := .add t20 (.poly 6)
  let t63 : SExpr := .montmul (.add t61 t62) 0x05d5#16
  let t64 : SExpr := .montmul (.add t10 (.poly 10)) 0xfe99#16
  let t65 : SExpr := .add t8 (.poly 2)
  let t66 : SExpr := .add t64 t65
  let t67 : SExpr := .montmul (.add t40 t39) 0x05d5#16
  let t68 : SExpr := .add t37 t36
  let t69 : SExpr := .montmul (.sub t50 t49) 0x058e#16
  let t70 : SExpr := .sub t53 t52
  let t71 : SExpr := .montmul (.sub t56 t55) 0x058e#16
  let t72 : SExpr := .sub t59 t58
  let t73 : SExpr := .montmul (.sub t62 t61) 0x058e#16
  let t74 : SExpr := .sub t65 t64
  { vregs := ⟨.sub t1 t3, .sub t5 t7, .sub t9 t11, .sub t13 t15,
     t17, t19, .sub t21 t23, .sub t17 t19,
     .vreg0 8, .const 0x011f#16, .const 0x6e1f#16, .const 0x0d01#16,
     .const 0xcf8e#16, .const 0x34d5#16, .vreg0 14, .vreg0 15,
     .sub t25 t27, .montmul t28 0x011f#16, .sub t30 t32, .montmul t33 0x011f#16,
     t35, .sqdmulh t34 (.const 0x011f#16), t42, t43,
     t44, t46, t47, .const 0xae55#16,
     t48, .const 0xbeca#16, .const 0x026e#16, .const 0xf129#16⟩
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
    poly := ⟨.add t51 t54, .add t57 t60, .add t63 t66, .add t67 t68,
     .sub t54 t51, .sub t60 t57, .sub t66 t63, .sub t68 t67,
     .add t69 t70, .add t71 t72, .add t73 t74, .add t41 t38,
     .sub t70 t69, .sub t72 t71, .sub t74 t73, t42,
     t43, t44, .add t11 t9, .add t7 t5,
     t33, t28, t45, t34,
     .poly 24, .poly 25, .poly 26, .poly 27,
     .poly 28, .poly 29, .poly 30, .poly 31⟩
    gprs := ⟨.gpr0 0, .gpr0 1, .gpr0 2, .gpr0 3, .gpr0 4, .gpr0 5,
     .gpr0 6, .gpr0 7, .const64 10690#64, .gpr0 23, .const64 16#64, .gpr0 11,
     .gpr0 12, .gpr0 13, .gpr0 14, .gpr0 15, .gpr0 16, .gpr0 17,
     .gpr0 18, .gpr0 19, .gpr0 20, .gpr0 21, .gpr0 22, .gpr0 23,
     .gpr0 24, .gpr0 25, .gpr0 26, .gpr0 27, .gpr0 28, .gpr0 29,
     .gpr0 30⟩
    pstate := .pstate0 }

theorem run_fwd1a : runSymRange cfgFwd1 461 422 symFwd1Init = some symFwd1MidA := by
  rfl_kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1a

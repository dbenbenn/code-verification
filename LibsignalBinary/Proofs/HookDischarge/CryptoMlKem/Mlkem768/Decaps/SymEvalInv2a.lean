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

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2a

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (SExpr SymCfg SymState runSymRange)

@[expose] def cfgInv2 : SymCfg := ⟨some 26#5, .s27, false⟩

@[expose] def symInv2Init : SymState :=
  { vregs := ⟨.vreg0 0, .vreg0 1, .vreg0 2, .vreg0 3,
     .vreg0 4, .vreg0 5, .vreg0 6, .vreg0 7,
     .vreg0 8, .vreg0 9, .vreg0 10, .vreg0 11,
     .vreg0 12, .vreg0 13, .vreg0 14, .vreg0 15,
     .const 0x0d01#16, .const 0x4ebf#16, .vreg0 18, .vreg0 19,
     .vreg0 20, .vreg0 21, .vreg0 22, .const 0xf2ff#16,
     .vreg0 24, .vreg0 25, .vreg0 26, .const 0x0400#16,
     .vreg0 28, .vreg0 29, .vreg0 30, .vreg0 31⟩
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
     .gpr0 18, .gpr0 19, .gpr0 20, .const64 64778#64, .const64 31498#64, .gpr0 23,
     .gpr0 24, .gpr0 25, .gpr0 26, .gpr0 27, .gpr0 28, .gpr0 29,
     .gpr0 30⟩
    pstate := .pstate0 }

@[expose] def symInv2MidA : SymState :=
  let t0 : SExpr := .add (.poly 26) (.poly 27)
  let t1 : SExpr := .add (.poly 24) (.poly 25)
  let t2 : SExpr := .sub t0 t1
  let t3 : SExpr := .sqdmulh t2 (.const 0x026e#16)
  let t4 : SExpr := .montmul (.sub (.poly 27) (.poly 26)) 0x0108#16
  let t5 : SExpr := .montmul (.sub (.poly 25) (.poly 24)) 0x017f#16
  let t6 : SExpr := .sub t4 t5
  let t7 : SExpr := .sqdmulh (.mul t6 (.const 0x6c6e#16)) (.const 0x0d01#16)
  let t8 : SExpr := .sqdmulh (.mul t2 (.const 0x6c6e#16)) (.const 0x0d01#16)
  let t9 : SExpr := .montmul (.sub (.poly 29) (.poly 28)) 0xfad3#16
  let t10 : SExpr := .add (.poly 22) (.poly 23)
  let t11 : SExpr := .add (.poly 20) (.poly 21)
  let t12 : SExpr := .barrett (.add t10 t11)
  let t13 : SExpr := .montmul (.sub (.poly 7) (.poly 6)) 0xf9fa#16
  let t14 : SExpr := .montmul (.sub (.poly 5) (.poly 4)) 0x019b#16
  let t15 : SExpr := .montmul (.sub t13 t14) 0xfa3e#16
  let t16 : SExpr := .montmul (.sub (.poly 15) (.poly 14)) 0xfd57#16
  let t17 : SExpr := .montmul (.sub (.poly 13) (.poly 12)) 0x03f9#16
  let t18 : SExpr := .barrett (.add t16 t17)
  let t19 : SExpr := .montmul (.sub (.poly 31) (.poly 30)) 0x023d#16
  let t20 : SExpr := .add t19 t9
  let t21 : SExpr := .montmul (.sub t10 t11) 0x0629#16
  let t22 : SExpr := .add (.poly 6) (.poly 7)
  let t23 : SExpr := .add (.poly 4) (.poly 5)
  let t24 : SExpr := .barrett (.add t22 t23)
  let t25 : SExpr := .add (.poly 2) (.poly 3)
  let t26 : SExpr := .add (.poly 0) (.poly 1)
  let t27 : SExpr := .barrett (.add t25 t26)
  let t28 : SExpr := .add (.poly 30) (.poly 31)
  let t29 : SExpr := .add (.poly 28) (.poly 29)
  let t30 : SExpr := .montmul (.sub (.poly 3) (.poly 2)) 0xff33#16
  let t31 : SExpr := .montmul (.sub (.poly 1) (.poly 0)) 0xf9dd#16
  let t32 : SExpr := .barrett (.add t30 t31)
  let t33 : SExpr := .add (.poly 14) (.poly 15)
  let t34 : SExpr := .add (.poly 12) (.poly 13)
  let t35 : SExpr := .barrett (.add t33 t34)
  let t36 : SExpr := .barrett (.add t13 t14)
  let t37 : SExpr := .add t28 t29
  let t38 : SExpr := .montmul (.sub (.poly 23) (.poly 22)) 0xfcc3#16
  let t39 : SExpr := .montmul (.sub (.poly 21) (.poly 20)) 0x05b2#16
  let t40 : SExpr := .barrett (.add t38 t39)
  let t41 : SExpr := .add (.poly 18) (.poly 19)
  let t42 : SExpr := .add (.poly 16) (.poly 17)
  let t43 : SExpr := .barrett (.add t41 t42)
  let t44 : SExpr := .montmul (.sub t38 t39) 0x0629#16
  let t45 : SExpr := .montmul (.sub (.poly 19) (.poly 18)) 0xf9be#16
  let t46 : SExpr := .montmul (.sub (.poly 17) (.poly 16)) 0xff7e#16
  let t47 : SExpr := .barrett (.add t45 t46)
  let t48 : SExpr := .montmul (.sub t41 t42) 0x00b6#16
  let t49 : SExpr := .montmul (.sub t45 t46) 0x00b6#16
  let t50 : SExpr := .montmul (.sub t33 t34) 0x03c2#16
  let t51 : SExpr := .montmul (.sub (.poly 11) (.poly 10)) 0x02dc#16
  let t52 : SExpr := .montmul (.sub (.poly 9) (.poly 8)) 0x0260#16
  let t53 : SExpr := .barrett (.add t51 t52)
  let t54 : SExpr := .add (.poly 10) (.poly 11)
  let t55 : SExpr := .add (.poly 8) (.poly 9)
  let t56 : SExpr := .barrett (.add t54 t55)
  let t57 : SExpr := .montmul (.sub t22 t23) 0xfa3e#16
  let t58 : SExpr := .montmul (.sub t16 t17) 0x03c2#16
  let t59 : SExpr := .barrett (.add t0 t1)
  let t60 : SExpr := .barrett (.add t4 t5)
  let t61 : SExpr := .montmul (.sub t54 t55) 0xfb4e#16
  let t62 : SExpr := .montmul (.sub t51 t52) 0xfb4e#16
  let t63 : SExpr := .montmul (.sub t25 t26) 0x05bc#16
  let t64 : SExpr := .montmul (.sub t30 t31) 0x05bc#16
  { vregs := ⟨.vreg0 0, .const 0x0400#16, t3, t7,
     t8, t9, t2, .sqdmulh t6 (.const 0x026e#16),
     t12, t15, t18, .sqdmulh t20 (.const 0x4ebf#16),
     t21, t20, .const 0xae55#16, .sub t24 t27,
     .const 0x0d01#16, .const 0x4ebf#16, .sshr t3 1, .sub t28 t29,
     .const 0xff55#16, .add t24 t27, t32, t35,
     .add t36 t32, .sqdmulh t37 (.const 0x4ebf#16), t40, t36,
     t37, t43, .sub t19 t9, .const 0xf2ff#16⟩
    spill13 := ⟨.spill13_0 0, .spill13_0 1, .spill13_0 2, .spill13_0 3,
     .spill13_0 4, .spill13_0 5, .spill13_0 6, .spill13_0 7,
     .spill13_0 8, .spill13_0 9, .spill13_0 10, .spill13_0 11,
     .spill13_0 12⟩
    spill6 := ⟨.spill6_0 0, .spill6_0 1, .spill6_0 2, .spill6_0 3,
     t44, .spill6_0 5⟩
    spill21 := ⟨t36, t32, t47, t48,
     .spill21_0 4, t49, t50, t27,
     t53, t56, t57, t58,
     t59, t5, t60, t61,
     t62, t63, t64, t29,
     t9⟩
    poly := ⟨t26, t31, t25, t30,
     t23, t14, t22, t13,
     t55, t52, t54, t51,
     t34, t17, t33, t16,
     t42, t46, t41, t45,
     t11, t39, t10, t38,
     t1, t5, t0, t4,
     t29, t9, t28, t19⟩
    gprs := ⟨.gpr0 0, .gpr0 1, .gpr0 2, .gpr0 3, .gpr0 4, .gpr0 5,
     .gpr0 6, .gpr0 7, .gpr0 8, .gpr0 9, .gpr0 10, .gpr0 11,
     .const64 48842#64, .gpr0 13, .gpr0 14, .gpr0 15, .gpr0 16, .gpr0 17,
     .gpr0 18, .gpr0 19, .gpr0 20, .const64 64778#64, .const64 31498#64, .gpr0 23,
     .gpr0 24, .gpr0 25, .gpr0 26, .const64 0#64, .gpr0 28, .gpr0 29,
     .gpr0 30⟩
    pstate := .pstate0 }

theorem run_inv2a : runSymRange cfgInv2 9333 486 symInv2Init = some symInv2MidA := by
  rfl_kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2a

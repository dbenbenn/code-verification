/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvSym1a

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (SExpr SymCfg SymState symInitState runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast (runSymRange_of_fast)

@[expose] def cfgSeg8InvSym : SymCfg := ⟨2320, 7, .spOff 28368, false⟩

@[expose] def symSeg8InvSymMidA : SymState :=
  let t0 : SExpr := .add (.poly 26) (.poly 27)
  let t1 : SExpr := .add (.poly 24) (.poly 25)
  let t2 : SExpr := .add t0 t1
  let t3 : SExpr := .montmul (.sub (.poly 27) (.poly 26)) 0x0108#16
  let t4 : SExpr := .montmul (.sub (.poly 25) (.poly 24)) 0x017f#16
  let t5 : SExpr := .add t3 t4
  let t6 : SExpr := .add (.poly 22) (.poly 23)
  let t7 : SExpr := .add (.poly 20) (.poly 21)
  let t8 : SExpr := .barrett (.add t6 t7)
  let t9 : SExpr := .add (.poly 18) (.poly 19)
  let t10 : SExpr := .add (.poly 16) (.poly 17)
  let t11 : SExpr := .montmul (.sub t9 t10) 0x00b6#16
  let t12 : SExpr := .montmul (.sub t6 t7) 0x0629#16
  let t13 : SExpr := .add (.sqdmulh t2 (.const 0x4ebf#16)) (.const 0x0400#16)
  let t14 : SExpr := .sub t0 t1
  let t15 : SExpr := .add (.poly 6) (.poly 7)
  let t16 : SExpr := .add (.poly 4) (.poly 5)
  let t17 : SExpr := .barrett (.add t15 t16)
  let t18 : SExpr := .add (.poly 2) (.poly 3)
  let t19 : SExpr := .add (.poly 0) (.poly 1)
  let t20 : SExpr := .barrett (.add t18 t19)
  let t21 : SExpr := .add t17 t20
  let t22 : SExpr := .montmul (.sub (.poly 11) (.poly 10)) 0x02dc#16
  let t23 : SExpr := .add (.poly 10) (.poly 11)
  let t24 : SExpr := .montmul (.sub (.poly 23) (.poly 22)) 0xfcc3#16
  let t25 : SExpr := .montmul (.sub (.poly 21) (.poly 20)) 0x05b2#16
  let t26 : SExpr := .barrett (.add t24 t25)
  let t27 : SExpr := .sub t24 t25
  let t28 : SExpr := .sshr (.sqdmulh t27 (.const 0x0629#16)) 1
  let t29 : SExpr := .sub t3 t4
  let t30 : SExpr := .sqdmulh (.mul t27 (.const 0xf129#16)) (.const 0x0d01#16)
  let t31 : SExpr := .montmul (.sub (.poly 7) (.poly 6)) 0xf9fa#16
  let t32 : SExpr := .montmul (.sub (.poly 5) (.poly 4)) 0x019b#16
  let t33 : SExpr := .barrett (.add t31 t32)
  let t34 : SExpr := .montmul (.sub (.poly 3) (.poly 2)) 0xff33#16
  let t35 : SExpr := .montmul (.sub (.poly 1) (.poly 0)) 0xf9dd#16
  let t36 : SExpr := .barrett (.add t34 t35)
  let t37 : SExpr := .montmul (.sub (.poly 19) (.poly 18)) 0xf9be#16
  let t38 : SExpr := .montmul (.sub (.poly 17) (.poly 16)) 0xff7e#16
  let t39 : SExpr := .barrett (.add t37 t38)
  let t40 : SExpr := .barrett (.add t9 t10)
  let t41 : SExpr := .montmul (.sub (.poly 31) (.poly 30)) 0x023d#16
  let t42 : SExpr := .montmul (.sub t37 t38) 0x00b6#16
  let t43 : SExpr := .montmul (.sub t18 t19) 0x05bc#16
  let t44 : SExpr := .montmul (.sub t34 t35) 0x05bc#16
  let t45 : SExpr := .montmul (.sub t15 t16) 0xfa3e#16
  let t46 : SExpr := .montmul (.sub t31 t32) 0xfa3e#16
  let t47 : SExpr := .add (.poly 8) (.poly 9)
  let t48 : SExpr := .barrett (.add t23 t47)
  let t49 : SExpr := .montmul (.sub (.poly 9) (.poly 8)) 0x0260#16
  let t50 : SExpr := .barrett (.add t22 t49)
  let t51 : SExpr := .montmul (.sub t23 t47) 0xfb4e#16
  let t52 : SExpr := .montmul (.sub t22 t49) 0xfb4e#16
  let t53 : SExpr := .add (.poly 14) (.poly 15)
  let t54 : SExpr := .add (.poly 12) (.poly 13)
  let t55 : SExpr := .barrett (.add t53 t54)
  let t56 : SExpr := .montmul (.sub (.poly 15) (.poly 14)) 0xfd57#16
  let t57 : SExpr := .montmul (.sub (.poly 13) (.poly 12)) 0x03f9#16
  let t58 : SExpr := .barrett (.add t56 t57)
  let t59 : SExpr := .montmul (.sub t53 t54) 0x03c2#16
  let t60 : SExpr := .montmul (.sub t56 t57) 0x03c2#16
  let t61 : SExpr := .montmul (.sub (.poly 29) (.poly 28)) 0xfad3#16
  { vregs := ⟨t2, .const 0xf2ff#16, t5, .const 0x0400#16,
     t8, t3, t11, t12,
     .sshr t13 11, .sqdmulh t14 (.const 0x026e#16), .sqdmulh t21 (.const 0x4ebf#16), t22,
     t23, .const 0x0d01#16, .const 0xf2ff#16, .const 0x4ebf#16,
     t26, t28, t29, t14,
     .sshr t30 1, t13, .mul t29 (.const 0x6c6e#16), .const 0xbeca#16,
     t21, .add t33 t36, t33, .sqdmulh t5 (.const 0x4ebf#16),
     .const 0x026e#16, t36, .mul t14 (.const 0x6c6e#16), .sub t17 t20⟩
    spill := ⟨.spill0 0, t3, t39, t40,
     t41, .spill0 5, t42, .spill0 7,
     .spill0 8, .spill0 9, .spill0 10, .spill0 11,
     .spill0 12, .spill0 13, .spill0 14, .spill0 15,
     .spill0 16, .spill0 17, .spill0 18, .spill0 19,
     .spill0 20, .spill0 21, .spill0 22, .spill0 23,
     .spill0 24, .spill0 25, .spill0 26, .spill0 27,
     .spill0 28, .spill0 29, .spill0 30, .spill0 31,
     .spill0 32, .spill0 33, .spill0 34, .spill0 35,
     .spill0 36, .spill0 37, .spill0 38, .spill0 39⟩
    poly  := ⟨t20, t36, t43, t44,
     t17, t33, t45, t46,
     t48, t50, t51, t52,
     t55, t58, t59, t60,
     t10, t38, t9, t37,
     t7, t25, t6, t24,
     t1, t4, t0, t3,
     .add (.poly 28) (.poly 29), t61, .add (.poly 30) (.poly 31), t41⟩
    gprs  := ⟨.spAdd 28672#64, .gpr0 1#5 0#64, .gpr0 2#5 0#64, .gpr0 3#5 0#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .const64 48842#64, .const64 573#64, .gpr0 10#5 0#64, .gpr0 11#5 0#64,
     .gpr0 12#5 0#64, .gpr0 13#5 0#64, .gpr0 14#5 0#64, .gpr0 15#5 0#64,
     .gpr0 16#5 0#64, .gpr0 17#5 0#64, .gpr0 18#5 0#64, .gpr0 19#5 0#64,
     .gpr0 20#5 0#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

theorem run_seg8_inv1a : runSymRange cfgSeg8InvSym 12142 520 symInitState = some symSeg8InvSymMidA :=
  runSymRange_of_fast (by rfl_kernel)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvSym1a

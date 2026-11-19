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

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1a

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (SExpr SymCfg SymState runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast (runSymRange_of_fast)

@[expose] def cfgSeg6Fwd : SymCfg := ⟨1792, 40, .gpr 5#5, true⟩

@[expose] def symSeg6FwdInit : SymState :=
  { vregs := ⟨.src 16, .vreg0 1, .src 18, .const 0x0d01#16,
     .vreg0 4, .vreg0 5, .vreg0 6, .vreg0 7,
     .vreg0 8, .vreg0 9, .vreg0 10, .vreg0 11,
     .vreg0 12, .vreg0 13, .vreg0 14, .vreg0 15,
     .vreg0 16, .vreg0 17, .vreg0 18, .vreg0 19,
     .vreg0 20, .vreg0 21, .vreg0 22, .vreg0 23,
     .vreg0 24, .vreg0 25, .vreg0 26, .vreg0 27,
     .vreg0 28, .vreg0 29, .vreg0 30, .vreg0 31⟩
    spill := ⟨.const 0xd43e#16, .const 0xfa3e#16, .const 0x054e#16, .const 0xfb4e#16,
     .const 0x29c2#16, .const 0x03c2#16, .const 0xc2b6#16, .const 0xf129#16,
     .const 0x0629#16, .const 0x6c6e#16, .const 0x026e#16, .const 0xae55#16,
     .const 0xbeca#16, .const 0x6e1f#16, .const 0x011f#16, .const 0xcf8e#16,
     .const 0x058e#16, .const 0x34d5#16, .const 0x05d5#16, .const 0x0313#16,
     .const 0xfa13#16, .const 0x3999#16, .const 0xfe99#16, .const 0xf9c0#16,
     .spill0 24, .spill0 25, .spill0 26, .spill0 27,
     .spill0 28, .spill0 29, .spill0 30, .spill0 31,
     .spill0 32, .spill0 33, .spill0 34, .spill0 35,
     .spill0 36, .spill0 37, .spill0 38, .spill0 39⟩
    poly  := ⟨.poly 0, .poly 1, .poly 2, .poly 3,
     .poly 4, .poly 5, .poly 6, .poly 7,
     .poly 8, .poly 9, .poly 10, .poly 11,
     .poly 12, .poly 13, .poly 14, .poly 15,
     .poly 16, .poly 17, .poly 18, .poly 19,
     .poly 20, .poly 21, .poly 22, .poly 23,
     .poly 24, .poly 25, .poly 26, .poly 27,
     .poly 28, .poly 29, .poly 30, .poly 31⟩
    gprs  := ⟨.gpr0 0#5 0#64, .gpr0 1#5 0#64, .gpr0 2#5 0#64, .gpr0 3#5 0#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .gpr0 8#5 0#64, .gpr0 9#5 0#64, .gpr0 10#5 0#64, .gpr0 11#5 0#64,
     .const64 63994#64, .const64 18426#64, .const64 411#64, .const64 8859#64,
     .const64 26675#64, .const64 63965#64, .const64 49373#64, .gpr0 19#5 0#64,
     .gpr0 20#5 0#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

@[expose] def symSeg6FwdMidA : SymState :=
  let t0 : SExpr := .mul (.src 26) (.const 0xf9c0#16)
  let t1 : SExpr := .montmul (.add (.src 10) t0) 0xfe99#16
  let t2 : SExpr := .mul (.src 18) (.const 0xf9c0#16)
  let t3 : SExpr := .add (.src 2) t2
  let t4 : SExpr := .add t1 t3
  let t5 : SExpr := .mul (.src 30) (.const 0xf9c0#16)
  let t6 : SExpr := .montmul (.add (.src 14) t5) 0xfe99#16
  let t7 : SExpr := .mul (.src 22) (.const 0xf9c0#16)
  let t8 : SExpr := .add (.src 6) t7
  let t9 : SExpr := .montmul (.add t6 t8) 0x05d5#16
  let t10 : SExpr := .sub t4 t9
  let t11 : SExpr := .sqdmulh (.mul t10 (.const 0x6c6e#16)) (.const 0x0d01#16)
  let t12 : SExpr := .mul (.src 31) (.const 0xf9c0#16)
  let t13 : SExpr := .montmul (.add (.src 15) t12) 0xfe99#16
  let t14 : SExpr := .mul (.src 23) (.const 0xf9c0#16)
  let t15 : SExpr := .add (.src 7) t14
  let t16 : SExpr := .montmul (.add t13 t15) 0x05d5#16
  let t17 : SExpr := .mul (.src 27) (.const 0xf9c0#16)
  let t18 : SExpr := .montmul (.add (.src 11) t17) 0xfe99#16
  let t19 : SExpr := .mul (.src 19) (.const 0xf9c0#16)
  let t20 : SExpr := .add (.src 3) t19
  let t21 : SExpr := .add t18 t20
  let t22 : SExpr := .montmul (.add t16 t21) 0xff55#16
  let t23 : SExpr := .mul (.src 28) (.const 0xf9c0#16)
  let t24 : SExpr := .montmul (.add (.src 12) t23) 0xfe99#16
  let t25 : SExpr := .mul (.src 20) (.const 0xf9c0#16)
  let t26 : SExpr := .add (.src 4) t25
  let t27 : SExpr := .montmul (.add t24 t26) 0x05d5#16
  let t28 : SExpr := .mul (.src 24) (.const 0xf9c0#16)
  let t29 : SExpr := .montmul (.add (.src 8) t28) 0xfe99#16
  let t30 : SExpr := .mul (.src 16) (.const 0xf9c0#16)
  let t31 : SExpr := .add (.src 0) t30
  let t32 : SExpr := .add t29 t31
  let t33 : SExpr := .add t27 t32
  let t34 : SExpr := .montmul (.add t9 t4) 0xff55#16
  let t35 : SExpr := .montmul (.sub (.src 15) t12) 0xfa13#16
  let t36 : SExpr := .sub (.src 7) t14
  let t37 : SExpr := .montmul (.add t35 t36) 0x011f#16
  let t38 : SExpr := .montmul (.sub (.src 11) t17) 0xfa13#16
  let t39 : SExpr := .sub (.src 3) t19
  let t40 : SExpr := .add t38 t39
  let t41 : SExpr := .sub (.src 4) t25
  let t42 : SExpr := .montmul (.sub (.src 12) t23) 0xfa13#16
  let t43 : SExpr := .sub t41 t42
  let t44 : SExpr := .montmul (.sub (.src 14) t5) 0xfa13#16
  let t45 : SExpr := .sub (.src 6) t7
  let t46 : SExpr := .montmul (.add t44 t45) 0x011f#16
  let t47 : SExpr := .montmul (.sub (.src 10) t0) 0xfa13#16
  let t48 : SExpr := .sub (.src 2) t2
  let t49 : SExpr := .add t47 t48
  let t50 : SExpr := .sub t31 t29
  let t51 : SExpr := .montmul (.sub t26 t24) 0x058e#16
  let t52 : SExpr := .mul (.src 25) (.const 0xf9c0#16)
  let t53 : SExpr := .montmul (.add (.src 9) t52) 0xfe99#16
  let t54 : SExpr := .mul (.src 17) (.const 0xf9c0#16)
  let t55 : SExpr := .add (.src 1) t54
  let t56 : SExpr := .add t53 t55
  let t57 : SExpr := .mul (.src 29) (.const 0xf9c0#16)
  let t58 : SExpr := .montmul (.add (.src 13) t57) 0xfe99#16
  let t59 : SExpr := .mul (.src 21) (.const 0xf9c0#16)
  let t60 : SExpr := .add (.src 5) t59
  let t61 : SExpr := .montmul (.add t58 t60) 0x05d5#16
  let t62 : SExpr := .sub t20 t18
  let t63 : SExpr := .montmul (.sub t15 t13) 0x058e#16
  let t64 : SExpr := .sub t3 t1
  let t65 : SExpr := .montmul (.sub t8 t6) 0x058e#16
  let t66 : SExpr := .sqdmulh (.mul t43 (.const 0xbeca#16)) (.const 0x0d01#16)
  let t67 : SExpr := .sub t21 t16
  let t68 : SExpr := .add t61 t56
  let t69 : SExpr := .montmul (.sub (.src 13) t57) 0xfa13#16
  let t70 : SExpr := .sub (.src 5) t59
  let t71 : SExpr := .montmul (.add t69 t70) 0x011f#16
  let t72 : SExpr := .montmul (.sub (.src 9) t52) 0xfa13#16
  let t73 : SExpr := .sub (.src 1) t54
  let t74 : SExpr := .add t72 t73
  let t75 : SExpr := .add t71 t74
  let t76 : SExpr := .sqdmulh (.mul t67 (.const 0x6c6e#16)) (.const 0x0d01#16)
  let t77 : SExpr := .sub t70 t69
  let t78 : SExpr := .sub t55 t53
  let t79 : SExpr := .montmul (.sub t60 t58) 0x058e#16
  let t80 : SExpr := .montmul (.sub (.src 8) t28) 0xfa13#16
  let t81 : SExpr := .sub (.src 0) t30
  let t82 : SExpr := .add t80 t81
  let t83 : SExpr := .montmul (.add t42 t41) 0x011f#16
  { vregs := ⟨t11, t22, .sub t33 t34, .const 0x0d01#16,
     .add t37 t40, .sub t40 t37, .sqdmulh t43 (.const 0x00ca#16), .add t46 t49,
     .sub t32 t27, .sub t50 t51, t43, t40,
     .sub t56 t61, .const 0x00ca#16, .sub t62 t63, .sub t64 t65,
     t66, .sqdmulh t67 (.const 0x026e#16), .sqdmulh t10 (.const 0x026e#16), .add t34 t33,
     .const 0xbeca#16, .sub t49 t46, .add t22 t68, t75,
     t76, t77, .add t63 t62, .add t51 t50,
     t68, .sub t78 t79, .add t79 t78, .add t65 t64⟩
    spill := ⟨.const 0xd43e#16, .const 0xfa3e#16, .const 0x054e#16, .const 0xfb4e#16,
     .const 0x29c2#16, .const 0x03c2#16, .const 0xc2b6#16, .const 0xf129#16,
     .const 0x0629#16, .const 0x6c6e#16, .const 0x026e#16, .const 0xae55#16,
     .const 0xbeca#16, .const 0x6e1f#16, .const 0x011f#16, .const 0xcf8e#16,
     .const 0x058e#16, .const 0x34d5#16, .const 0x05d5#16, .const 0x0313#16,
     .const 0xfa13#16, .const 0x3999#16, .const 0xfe99#16, .const 0xf9c0#16,
     t32, t74, t82, t50,
     t78, t41, t77, .sub t45 t44,
     t62, .sub t36 t35, .sub t74 t71, .sub t82 t83,
     .sub t39 t38, .sub t48 t47, .sub t81 t80, .sub t73 t72⟩
    poly  := ⟨.poly 0, .poly 1, .poly 2, .poly 3,
     .poly 4, .poly 5, .poly 6, .poly 7,
     .poly 8, .poly 9, .poly 10, .poly 11,
     .poly 12, .poly 13, .poly 14, .poly 15,
     .add t83 t82, t75, .poly 18, .poly 19,
     .poly 20, .poly 21, .poly 22, .poly 23,
     .poly 24, .poly 25, .poly 26, .poly 27,
     .poly 28, .poly 29, .poly 30, .poly 31⟩
    gprs  := ⟨.gpr0 0#5 0#64, .gpr0 1#5 0#64, .gpr0 2#5 0#64, .gpr0 3#5 0#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 9#5 0#64, .gpr0 7#5 0#64,
     .const64 31164#64, .gpr0 9#5 0#64, .gpr0 10#5 0#64, .gpr0 11#5 0#64,
     .const64 63994#64, .const64 18426#64, .const64 411#64, .const64 8859#64,
     .const64 26675#64, .const64 63965#64, .const64 49373#64, .gpr0 19#5 0#64,
     .const64 16#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

theorem run_seg6_fwd1a : runSymRange cfgSeg6Fwd 7940 391 symSeg6FwdInit = some symSeg6FwdMidA :=
  runSymRange_of_fast (by rfl_kernel)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1a

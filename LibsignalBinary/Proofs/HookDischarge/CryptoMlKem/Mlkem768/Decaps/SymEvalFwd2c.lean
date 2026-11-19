/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure -- proof-setup: allow-public-import
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2c

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (SExpr SymCfg SymState symInit runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure (symBarrettMap checkNoSpillVreg checkAstEq)

@[expose] def cfgFwd2Tail : SymCfg := ⟨some 5#5, .none, false⟩

@[expose] def symFwd2TailInit : SymState :=
  { symInit with gprs := { symInit.gprs with g3 := .const64 20159#64 } }

@[expose] def symFwd2TailEnd : SymState :=
  let t0 : SExpr := .sqdmulh (.poly 30) (.const 0x4ebf#16)
  let t1 : SExpr := .add t0 (.const 0x0400#16)
  let t2 : SExpr := .sqdmulh (.poly 31) (.const 0x4ebf#16)
  let t3 : SExpr := .add t2 (.const 0x0400#16)
  let t4 : SExpr := .barrett (.poly 24)
  let t5 : SExpr := .barrett (.poly 25)
  let t6 : SExpr := .barrett (.poly 26)
  let t7 : SExpr := .barrett (.poly 27)
  let t8 : SExpr := .sqdmulh (.poly 28) (.const 0x4ebf#16)
  let t9 : SExpr := .sshr (.add t8 (.const 0x0400#16)) 11
  let t10 : SExpr := .sqdmulh (.poly 29) (.const 0x4ebf#16)
  let t11 : SExpr := .add t10 (.const 0x0400#16)
  let t12 : SExpr := .add (.sqdmulh (.poly 27) (.const 0x4ebf#16)) (.const 0x0400#16)
  let t13 : SExpr := .barrett (.poly 28)
  let t14 : SExpr := .barrett (.poly 29)
  let t15 : SExpr := .barrett (.poly 30)
  let t16 : SExpr := .barrett (.poly 31)
  { vregs := ⟨.sshr t1 11, .sshr t3 11, t4, .vreg0 3,
     t5, t6, t7, t9,
     .const 0xf2ff#16, .vreg0 9, .vreg0 10, .vreg0 11,
     .vreg0 12, .vreg0 13, .vreg0 14, .vreg0 15,
     .sshr t11 11, .sshr t12 11, t3, t11,
     t2, t13, t1, t14,
     t8, t15, t10, t16,
     t0, .sqdmulh (.poly 20) (.const 0x4ebf#16), .sqdmulh (.poly 21) (.const 0x4ebf#16), .const 0x0400#16⟩
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
    poly := ⟨.barrett (.poly 0), .barrett (.poly 1), .barrett (.poly 2), .barrett (.poly 3),
     .barrett (.poly 4), .barrett (.poly 5), .barrett (.poly 6), .barrett (.poly 7),
     .barrett (.poly 8), .barrett (.poly 9), .barrett (.poly 10), .barrett (.poly 11),
     .barrett (.poly 12), .barrett (.poly 13), .barrett (.poly 14), .barrett (.poly 15),
     .barrett (.poly 16), .barrett (.poly 17), .barrett (.poly 18), .barrett (.poly 19),
     .barrett (.poly 20), .barrett (.poly 21), .barrett (.poly 22), .barrett (.poly 23),
     t4, t5, t6, t7,
     t13, t14, t15, t16⟩
    gprs := ⟨.gpr0 0, .gpr0 1, .gpr0 2, .const64 20159#64, .gpr0 4, .gpr0 5,
     .gpr0 6, .addImm (.gpr0 7) 128#64, .gpr0 8, .addImm (.gpr0 9) 512#64, .addImm (.gpr0 10) 512#64, .gpr0 11,
     .gpr0 12, .gpr0 13, .gpr0 14, .gpr0 15, .gpr0 16, .gpr0 17,
     .gpr0 18, .gpr0 19, .gpr0 20, .gpr0 21, .gpr0 22, .gpr0 23,
     .gpr0 24, .gpr0 25, .gpr0 26, .gpr0 27, .gpr0 28, .gpr0 29,
     .gpr0 30⟩
    pstate := .cmpImm64 (.gpr0 4) 3#64 }

theorem run_fwd2_tail : runSymRange cfgFwd2Tail 8397 167 symFwd2TailInit = some symFwd2TailEnd := by
  rfl_kernel

theorem fwd2_tail_noSpillVreg : checkNoSpillVreg symFwd2TailEnd.poly = true := by rfl_kernel

theorem fwd2_tail_ast_eq : checkAstEq symFwd2TailEnd.poly symBarrettMap = true := by rfl_kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2c

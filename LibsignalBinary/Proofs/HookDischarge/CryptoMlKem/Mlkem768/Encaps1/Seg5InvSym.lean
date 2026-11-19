/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Sym -- proof-setup: allow-public-import

/-!
# `encapsulate1_serialized` (`B03`) — Symbolic Certificate for Upper 5-Stage `InvNTT` (`Seg5InvSym`)

Certifies the 1,458-instruction relocation-free NEON upper 5-stage `InvNTT` slice
(`+0x5310 .. +0x69d8`, `w = 5316 .. 6774`) on `blkTree03` against `symUpperInvNtt`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5InvSym

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr SymCfg SymGpr SymSpill40 SymState)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast (symGprBeq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  polyAstEq polyNoSpillVreg symUpperInvNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Sym (
  blk03NoRelocInRange runSymRange03Fast)

@[expose] def cfgSeg5Inv : SymCfg := ⟨1760, 27, .gpr 26#5, false⟩

@[expose] def symSeg5InvInit : SymState :=
  { vregs := ⟨.vreg0 0, .vreg0 1, .vreg0 2, .vreg0 3,
     .vreg0 4, .vreg0 5, .vreg0 6, .vreg0 7,
     .vreg0 8, .vreg0 9, .vreg0 10, .vreg0 11,
     .vreg0 12, .vreg0 13, .vreg0 14, .vreg0 15,
     .const 0x0d01#16, .const 0x4ebf#16, .vreg0 18, .vreg0 19,
     .vreg0 20, .vreg0 21, .vreg0 22, .const 0xf2ff#16,
     .vreg0 24, .vreg0 25, .vreg0 26, .const 0x0400#16,
     .vreg0 28, .vreg0 29, .vreg0 30, .vreg0 31⟩
    spill := SymSpill40.ofFn SExpr.spill0
    poly  := ⟨.poly 0, .poly 1, .poly 2, .poly 3, .poly 4, .poly 5, .poly 6, .poly 7,
     .poly 8, .poly 9, .poly 10, .poly 11, .poly 12, .poly 13, .poly 14, .poly 15,
     .poly 16, .poly 17, .poly 18, .poly 19, .poly 20, .poly 21, .poly 22, .poly 23,
     .poly 24, .poly 25, .poly 26, .poly 27, .poly 28, .poly 29, .poly 30, .poly 31⟩
    gprs  := ⟨.gpr0 0#5 0#64, .gpr0 1#5 0#64, .gpr0 2#5 0#64, .gpr0 3#5 0#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .gpr0 8#5 0#64, .gpr0 9#5 0#64, .gpr0 10#5 0#64, .gpr0 11#5 0#64,
     .gpr0 12#5 0#64, .gpr0 13#5 0#64, .gpr0 14#5 0#64, .gpr0 15#5 0#64,
     .gpr0 16#5 0#64, .gpr0 17#5 0#64, .gpr0 18#5 0#64, .gpr0 19#5 0#64,
     .gpr0 20#5 0#64, .const64 64778#64, .const64 31498#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

@[expose] def symSeg5InvEnd : SymState :=
  (runSymRange03Fast false cfgSeg5Inv 5316 1458 symSeg5InvInit).getD symSeg5InvInit

private theorem eq_some_getD03 {α : Type} {o : Option α} (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => contradiction
  | some v => rfl

theorem noReloc_seg5_inv : blk03NoRelocInRange 5316 6774 = true := by decide +kernel

set_option maxRecDepth 400000 in
theorem run_seg5_inv :
    runSymRange03Fast false cfgSeg5Inv 5316 1458 symSeg5InvInit = some symSeg5InvEnd :=
  eq_some_getD03 symSeg5InvInit (by decide +kernel)

set_option maxRecDepth 400000 in
theorem seg5_inv_noSpillVreg : polyNoSpillVreg false symSeg5InvEnd.poly = true := by
  decide +kernel

set_option maxRecDepth 400000 in
theorem seg5_inv_ast_eq : polyAstEq false symSeg5InvEnd.poly symUpperInvNtt = true := by
  decide +kernel

private theorem eq_of_symGprBeq {a b : SymGpr} (h : symGprBeq a b = true) : a = b := by
  cases a <;> cases b <;> simp [symGprBeq] at h ⊢ <;> exact h

private theorem eq_of_sExprBeq {a b : SExpr} (h : a.beq b = true) : a = b :=
  SExpr.beq_eq_true h

set_option maxRecDepth 400000 in
private theorem symSeg5InvEnd_vregs_bool :
    ((symSeg5InvEnd.vregs.get 0).beq (.vreg0 0) &&
     (symSeg5InvEnd.vregs.get 16).beq (.const 0x0d01#16) &&
     (symSeg5InvEnd.vregs.get 17).beq (.const 0x4ebf#16) &&
     (symSeg5InvEnd.vregs.get 23).beq (.const 0xf2ff#16) &&
     (symSeg5InvEnd.vregs.get 27).beq (.const 0x0400#16)) = true := by
  decide +kernel

theorem symSeg5InvEnd_vregs :
    symSeg5InvEnd.vregs.get 0 = .vreg0 0 ∧
    symSeg5InvEnd.vregs.get 16 = .const 0x0d01#16 ∧
    symSeg5InvEnd.vregs.get 17 = .const 0x4ebf#16 ∧
    symSeg5InvEnd.vregs.get 23 = .const 0xf2ff#16 ∧
    symSeg5InvEnd.vregs.get 27 = .const 0x0400#16 := by
  have h := symSeg5InvEnd_vregs_bool
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨h0, h16⟩, h17⟩, h23⟩, h27⟩
  exact ⟨eq_of_sExprBeq h0, eq_of_sExprBeq h16, eq_of_sExprBeq h17,
    eq_of_sExprBeq h23, eq_of_sExprBeq h27⟩

set_option maxRecDepth 400000 in
private theorem symSeg5InvEnd_gprs_bool :
    (symGprBeq (symSeg5InvEnd.gprs.get 1) (.gpr0 1#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 4) (.gpr0 4#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 8) (.gpr0 8#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 9) (.gpr0 9#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 10) (.addGpr0 19#5 12#5) &&
     symGprBeq (symSeg5InvEnd.gprs.get 11) (.gpr0 11#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 12) (.gpr0 12#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 13) (.gpr0 13#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 14) (.gpr0 14#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 16) (.gpr0 16#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 17) (.gpr0 17#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 18) (.gpr0 18#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 19) (.gpr0 19#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 21) (.const64 64778#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 22) (.const64 31498#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 23) (.gpr0 23#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 24) (.gpr0 24#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 25) (.gpr0 25#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 26) (.gpr0 26#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 27) (.const64 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 28) (.gpr0 28#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 29) (.gpr0 29#5 0#64)) = true := by
  decide +kernel

theorem symSeg5InvEnd_gprs :
    symSeg5InvEnd.gprs.get 1 = .gpr0 1#5 0#64 ∧
    symSeg5InvEnd.gprs.get 4 = .gpr0 4#5 0#64 ∧
    symSeg5InvEnd.gprs.get 8 = .gpr0 8#5 0#64 ∧
    symSeg5InvEnd.gprs.get 9 = .gpr0 9#5 0#64 ∧
    symSeg5InvEnd.gprs.get 10 = .addGpr0 19#5 12#5 ∧
    symSeg5InvEnd.gprs.get 11 = .gpr0 11#5 0#64 ∧
    symSeg5InvEnd.gprs.get 12 = .gpr0 12#5 0#64 ∧
    symSeg5InvEnd.gprs.get 13 = .gpr0 13#5 0#64 ∧
    symSeg5InvEnd.gprs.get 14 = .gpr0 14#5 0#64 ∧
    symSeg5InvEnd.gprs.get 16 = .gpr0 16#5 0#64 ∧
    symSeg5InvEnd.gprs.get 17 = .gpr0 17#5 0#64 ∧
    symSeg5InvEnd.gprs.get 18 = .gpr0 18#5 0#64 ∧
    symSeg5InvEnd.gprs.get 19 = .gpr0 19#5 0#64 ∧
    symSeg5InvEnd.gprs.get 21 = .const64 64778#64 ∧
    symSeg5InvEnd.gprs.get 22 = .const64 31498#64 ∧
    symSeg5InvEnd.gprs.get 23 = .gpr0 23#5 0#64 ∧
    symSeg5InvEnd.gprs.get 24 = .gpr0 24#5 0#64 ∧
    symSeg5InvEnd.gprs.get 25 = .gpr0 25#5 0#64 ∧
    symSeg5InvEnd.gprs.get 26 = .gpr0 26#5 0#64 ∧
    symSeg5InvEnd.gprs.get 27 = .const64 0#64 ∧
    symSeg5InvEnd.gprs.get 28 = .gpr0 28#5 0#64 ∧
    symSeg5InvEnd.gprs.get 29 = .gpr0 29#5 0#64 := by
  have h := symSeg5InvEnd_gprs_bool
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h4⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h16⟩, h17⟩, h18⟩, h19⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩, h27⟩, h28⟩, h29⟩
  exact ⟨eq_of_symGprBeq h1, eq_of_symGprBeq h4, eq_of_symGprBeq h8, eq_of_symGprBeq h9,
    eq_of_symGprBeq h10, eq_of_symGprBeq h11, eq_of_symGprBeq h12, eq_of_symGprBeq h13,
    eq_of_symGprBeq h14, eq_of_symGprBeq h16, eq_of_symGprBeq h17, eq_of_symGprBeq h18,
    eq_of_symGprBeq h19, eq_of_symGprBeq h21, eq_of_symGprBeq h22, eq_of_symGprBeq h23,
    eq_of_symGprBeq h24, eq_of_symGprBeq h25, eq_of_symGprBeq h26, eq_of_symGprBeq h27,
    eq_of_symGprBeq h28, eq_of_symGprBeq h29⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5InvSym

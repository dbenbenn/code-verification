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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Sym -- proof-setup: allow-public-import

/-!
# `kyber::encapsulate` (`B07`) — Symbolic Certificate for `Seg5` Upper 5-Stage `InvNTT` (`Seg5InvSym`)

Certifies the 1,560-instruction relocation-free NEON upper 5-stage `InvNTT` slice
(`+0x840c .. +0x9c6c`, `w = 8451 .. 10011`) on `blkTree07` against `symUpperInvNtt`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5InvSym

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr SymCfg SymGpr SymState symInitState)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast (symGprBeq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  polyAstEq polyNoSpillVreg symUpperInvNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Sym (
  blk07NoRelocInRange runSymRange07Fast)

@[expose] def cfgSeg5Inv : SymCfg := ⟨2320, 7, .spOff 26768, false⟩

@[expose] def symSeg5InvEnd : SymState :=
  (runSymRange07Fast false cfgSeg5Inv 8451 1560 symInitState).getD symInitState

private theorem eq_some_getD07 {α : Type} {o : Option α} (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => contradiction
  | some v => rfl

theorem noReloc_seg5_inv : blk07NoRelocInRange 8451 10011 = true := by decide +kernel

set_option maxRecDepth 400000 in
theorem run_seg5_inv :
    runSymRange07Fast false cfgSeg5Inv 8451 1560 symInitState = some symSeg5InvEnd :=
  eq_some_getD07 symInitState (by decide +kernel)

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
private theorem symSeg5InvEnd_spills_bool :
    ((symSeg5InvEnd.spill.get 0).beq (.const 0x4ebf#16) &&
     (symSeg5InvEnd.spill.get 5).beq (.const 0x0d01#16)) = true := by
  decide +kernel

theorem symSeg5InvEnd_spills :
    symSeg5InvEnd.spill.get 0 = .const 0x4ebf#16 ∧
    symSeg5InvEnd.spill.get 5 = .const 0x0d01#16 := by
  have h := symSeg5InvEnd_spills_bool
  simp only [Bool.and_eq_true] at h
  exact ⟨eq_of_sExprBeq h.1, eq_of_sExprBeq h.2⟩

set_option maxRecDepth 400000 in
private theorem symSeg5InvEnd_gprs_bool :
    (symGprBeq (symSeg5InvEnd.gprs.get 0) (.spAdd 30896#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 1) (.spAdd 26768#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 2) (.const64 512#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 19) (.spAdd 30896#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 29) (.gpr0 29#5 0#64) &&
     symGprBeq (symSeg5InvEnd.gprs.get 30) (.gpr0 30#5 0#64)) = true := by
  decide +kernel

theorem symSeg5InvEnd_gprs :
    symSeg5InvEnd.gprs.get 0 = .spAdd 30896#64 ∧
    symSeg5InvEnd.gprs.get 1 = .spAdd 26768#64 ∧
    symSeg5InvEnd.gprs.get 2 = .const64 512#64 ∧
    symSeg5InvEnd.gprs.get 19 = .spAdd 30896#64 ∧
    symSeg5InvEnd.gprs.get 29 = .gpr0 29#5 0#64 ∧
    symSeg5InvEnd.gprs.get 30 = .gpr0 30#5 0#64 := by
  have h := symSeg5InvEnd_gprs_bool
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h19⟩, h29⟩, h30⟩
  exact ⟨eq_of_symGprBeq h0, eq_of_symGprBeq h1, eq_of_symGprBeq h2,
    eq_of_symGprBeq h19, eq_of_symGprBeq h29, eq_of_symGprBeq h30⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5InvSym

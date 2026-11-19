/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3Sym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast

/-!
# `generate_keypair_compressed` (`B05`): `eHat` symbolic NEON certificates

Certifies the `eHat` upper `Fwd2` NTT (`+0x4c2c .. +0x58d8`, `w = 4875 .. 5686`) and Barrett
reduction (`+0x59c0 .. +0x5c58`, `w = 5744 .. 5910`) in `B05`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SymE

open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SymCfg SymSpill40 SymState)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast (symGprBeq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  polyAstEq polyNoSpillVreg symBarrett symLowerNttBinomial5)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3Sym (
  blk05NoRelocInRange eq_of_sExprConstBeq eq_of_symGprBeq eq_some_getD05 runSymRange05Fast
  sExprConstBeq)

/-! ## 1. `eHat` Upper `Fwd2` NTT (`+0x4c2c .. +0x58d8`, `w = 4875 .. 5686`) -/

@[expose] def cfgEHatNtt : SymCfg := ⟨1952, 16, .gpr 1#5, false⟩

@[expose] def symEHatSpillInit : SymSpill40 :=
  ⟨.spill0 0, .spill0 1, .spill0 2, .spill0 3, .spill0 4, .spill0 5, .spill0 6, .spill0 7,
   .spill0 8, .spill0 9, .spill0 10, .spill0 11, .spill0 12, .spill0 13, .spill0 14, .spill0 15,
   .spill0 16, .spill0 17, .spill0 18, .spill0 19, .spill0 20, .spill0 21, .spill0 22, .spill0 23,
   .spill0 24, .spill0 25, .spill0 26, .spill0 27, .spill0 28, .spill0 29, .spill0 30, .spill0 31,
   .spill0 32, .spill0 33, .spill0 34, .spill0 35, .spill0 36, .spill0 37, .spill0 38, .spill0 39⟩

@[expose] def symEHatNttInit : SymState :=
  { vregs := ⟨.vreg0 0, .vreg0 1, .vreg0 2, .vreg0 3,
     .vreg0 4, .vreg0 5, .vreg0 6, .vreg0 7,
     .vreg0 8, .vreg0 9, .vreg0 10, .vreg0 11,
     .vreg0 12, .vreg0 13, .vreg0 14, .vreg0 15,
     .vreg0 16, .vreg0 17, .vreg0 18, .vreg0 19,
     .vreg0 20, .vreg0 21, .vreg0 22, .vreg0 23,
     .vreg0 24, .vreg0 25, .vreg0 26, .vreg0 27,
     .vreg0 28, .vreg0 29, .vreg0 30, .vreg0 31⟩
    spill := symEHatSpillInit
    poly  := ⟨.poly 0, .poly 1, .poly 2, .poly 3, .poly 4, .poly 5, .poly 6, .poly 7,
     .poly 8, .poly 9, .poly 10, .poly 11, .poly 12, .poly 13, .poly 14, .poly 15,
     .poly 16, .poly 17, .poly 18, .poly 19, .poly 20, .poly 21, .poly 22, .poly 23,
     .poly 24, .poly 25, .poly 26, .poly 27, .poly 28, .poly 29, .poly 30, .poly 31⟩
    gprs  := ⟨.gpr0 0#5 0#64, .gpr0 31#5 0#64, .gpr0 2#5 0#64, .gpr0 3#5 0#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .gpr0 8#5 0#64, .gpr0 9#5 0#64, .const64 0x019b#64, .const64 0x229b#64,
     .const64 0x6833#64, .const64 0xf9dd#64, .const64 0xc0dd#64, .gpr0 15#5 0#64,
     .const64 0xf301#64, .gpr0 17#5 0#64, .const64 0x4ebf#64, .gpr0 19#5 0#64,
     .const64 0x47fa#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .const64 0x0260#64,
     .const64 0x2260#64, .gpr0 29#5 0#64, .const64 0xf9fa#64⟩ }

@[expose] def symEHatNttA : SymState :=
  (runSymRange05Fast (some 9984) cfgEHatNtt 4875 358 symEHatNttInit).getD symEHatNttInit

@[expose] def symEHatNttA' : SymState :=
  { symEHatNttA with gprs := symEHatNttA.gprs.set 1 (.gpr0 1#5 0#64) }

@[expose] def symEHatNttEnd : SymState :=
  (runSymRange05Fast (some 9984) cfgEHatNtt 5234 452 symEHatNttA').getD symEHatNttA'

theorem noReloc_eHat_ntt_a : blk05NoRelocInRange 4875 5233 = true := by decide +kernel
theorem noReloc_eHat_ntt_b : blk05NoRelocInRange 5234 5686 = true := by decide +kernel

private def checkEHatNttA (st : SymState) : Bool :=
  symGprBeq (st.gprs.get 8) (.spAdd 17376#64) &&
  symGprBeq (st.gprs.get 1) (.gpr0 31#5 0#64)

set_option maxRecDepth 200000 in
private theorem eHat_ntt_a_cert :
    (match runSymRange05Fast (some 9984) cfgEHatNtt 4875 358 symEHatNttInit with
     | some st => checkEHatNttA st
     | none => false) = true := by
  decide +kernel

theorem run_eHat_ntt_a :
    runSymRange05Fast (some 9984) cfgEHatNtt 4875 358 symEHatNttInit = some symEHatNttA := by
  have h := eHat_ntt_a_cert
  unfold symEHatNttA
  cases hr : runSymRange05Fast (some 9984) cfgEHatNtt 4875 358 symEHatNttInit with
  | none => simp [hr] at h
  | some st => rfl

private theorem eHat_ntt_a_ok : checkEHatNttA symEHatNttA = true := by
  have h := eHat_ntt_a_cert
  rwa [run_eHat_ntt_a] at h

theorem symEHatNttA_gpr8 : symEHatNttA.gprs.get 8 = .spAdd 17376#64 := by
  have h := eHat_ntt_a_ok; unfold checkEHatNttA at h; simp only [Bool.and_eq_true] at h
  exact eq_of_symGprBeq h.1

theorem symEHatNttA_gpr1 : symEHatNttA.gprs.get 1 = .gpr0 31#5 0#64 := by
  have h := eHat_ntt_a_ok; unfold checkEHatNttA at h; simp only [Bool.and_eq_true] at h
  exact eq_of_symGprBeq h.2

private def checkEHatNttEnd (st : SymState) : Bool :=
  polyNoSpillVreg true st.poly &&
  polyAstEq true st.poly symLowerNttBinomial5 &&
  sExprConstBeq (st.vregs.get 7) (.const 0x0d01#16) &&
  (symGprBeq (st.gprs.get 0) (.gpr0 0#5 0#64) &&
   symGprBeq (st.gprs.get 1) (.gpr0 1#5 0#64) &&
   symGprBeq (st.gprs.get 2) (.gpr0 9#5 0#64) &&
   symGprBeq (st.gprs.get 3) (.gpr0 3#5 0#64) &&
   symGprBeq (st.gprs.get 4) (.const64 16#64) &&
   symGprBeq (st.gprs.get 8) (.gpr0 15#5 0#64) &&
   symGprBeq (st.gprs.get 9) (.gpr0 9#5 0#64) &&
   symGprBeq (st.gprs.get 10) (.const64 0x019b#64) &&
   symGprBeq (st.gprs.get 11) (.const64 0x229b#64) &&
   symGprBeq (st.gprs.get 12) (.const64 0x6833#64) &&
   symGprBeq (st.gprs.get 13) (.const64 0xf9dd#64) &&
   symGprBeq (st.gprs.get 14) (.const64 0xc0dd#64) &&
   symGprBeq (st.gprs.get 15) (.gpr0 15#5 0#64) &&
   symGprBeq (st.gprs.get 16) (.const64 0xf301#64) &&
   symGprBeq (st.gprs.get 17) (.gpr0 17#5 0#64) &&
   symGprBeq (st.gprs.get 18) (.const64 0x4ebf#64) &&
   symGprBeq (st.gprs.get 19) (.gpr0 19#5 0#64) &&
   symGprBeq (st.gprs.get 20) (.const64 0x47fa#64) &&
   symGprBeq (st.gprs.get 21) (.gpr0 21#5 0#64) &&
   symGprBeq (st.gprs.get 23) (.gpr0 23#5 0#64) &&
   symGprBeq (st.gprs.get 27) (.const64 0x0260#64) &&
   symGprBeq (st.gprs.get 28) (.const64 0x2260#64) &&
   symGprBeq (st.gprs.get 29) (.gpr0 29#5 0#64) &&
   symGprBeq (st.gprs.get 30) (.const64 0xf9fa#64))

set_option maxRecDepth 200000 in
private theorem eHat_ntt_cert_all :
    (match runSymRange05Fast (some 9984) cfgEHatNtt 5234 452 symEHatNttA' with
     | some st => checkEHatNttEnd st
     | none => false) = true := by
  decide +kernel

theorem run_eHat_ntt_b :
    runSymRange05Fast (some 9984) cfgEHatNtt 5234 452 symEHatNttA' = some symEHatNttEnd := by
  have h := eHat_ntt_cert_all
  unfold symEHatNttEnd
  cases hr : runSymRange05Fast (some 9984) cfgEHatNtt 5234 452 symEHatNttA' with
  | none => simp [hr] at h
  | some st => rfl

private theorem eHat_ntt_end_ok : checkEHatNttEnd symEHatNttEnd = true := by
  have h := eHat_ntt_cert_all
  rwa [run_eHat_ntt_b] at h

private theorem eHat_ntt_end_parts :
    polyNoSpillVreg true symEHatNttEnd.poly = true ∧
    polyAstEq true symEHatNttEnd.poly symLowerNttBinomial5 = true ∧
    sExprConstBeq (symEHatNttEnd.vregs.get 7) (.const 0x0d01#16) = true := by
  have h := eHat_ntt_end_ok
  unfold checkEHatNttEnd at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

theorem eHat_ntt_noSpillVreg : polyNoSpillVreg true symEHatNttEnd.poly = true :=
  eHat_ntt_end_parts.1

theorem eHat_ntt_ast_eq : polyAstEq true symEHatNttEnd.poly symLowerNttBinomial5 = true :=
  eHat_ntt_end_parts.2.1

theorem symEHatNttEnd_vreg7 : symEHatNttEnd.vregs.get 7 = .const 0x0d01#16 :=
  eq_of_sExprConstBeq eHat_ntt_end_parts.2.2

theorem symEHatNttEnd_gprs :
    symEHatNttEnd.gprs.get 0 = .gpr0 0#5 0#64 ∧
    symEHatNttEnd.gprs.get 1 = .gpr0 1#5 0#64 ∧
    symEHatNttEnd.gprs.get 2 = .gpr0 9#5 0#64 ∧
    symEHatNttEnd.gprs.get 3 = .gpr0 3#5 0#64 ∧
    symEHatNttEnd.gprs.get 4 = .const64 16#64 ∧
    symEHatNttEnd.gprs.get 8 = .gpr0 15#5 0#64 ∧
    symEHatNttEnd.gprs.get 9 = .gpr0 9#5 0#64 ∧
    symEHatNttEnd.gprs.get 10 = .const64 0x019b#64 ∧
    symEHatNttEnd.gprs.get 11 = .const64 0x229b#64 ∧
    symEHatNttEnd.gprs.get 12 = .const64 0x6833#64 ∧
    symEHatNttEnd.gprs.get 13 = .const64 0xf9dd#64 ∧
    symEHatNttEnd.gprs.get 14 = .const64 0xc0dd#64 ∧
    symEHatNttEnd.gprs.get 15 = .gpr0 15#5 0#64 ∧
    symEHatNttEnd.gprs.get 16 = .const64 0xf301#64 ∧
    symEHatNttEnd.gprs.get 17 = .gpr0 17#5 0#64 ∧
    symEHatNttEnd.gprs.get 18 = .const64 0x4ebf#64 ∧
    symEHatNttEnd.gprs.get 19 = .gpr0 19#5 0#64 ∧
    symEHatNttEnd.gprs.get 20 = .const64 0x47fa#64 ∧
    symEHatNttEnd.gprs.get 21 = .gpr0 21#5 0#64 ∧
    symEHatNttEnd.gprs.get 23 = .gpr0 23#5 0#64 ∧
    symEHatNttEnd.gprs.get 27 = .const64 0x0260#64 ∧
    symEHatNttEnd.gprs.get 28 = .const64 0x2260#64 ∧
    symEHatNttEnd.gprs.get 29 = .gpr0 29#5 0#64 ∧
    symEHatNttEnd.gprs.get 30 = .const64 0xf9fa#64 := by
  have h0 := eHat_ntt_end_ok
  unfold checkEHatNttEnd at h0
  simp only [Bool.and_eq_true] at h0
  have h := h0.2
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h8⟩, h9⟩, h10⟩,
    h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h23⟩, h27⟩, h28⟩, h29⟩, h30⟩
  exact ⟨eq_of_symGprBeq h0, eq_of_symGprBeq h1, eq_of_symGprBeq h2, eq_of_symGprBeq h3,
    eq_of_symGprBeq h4, eq_of_symGprBeq h8, eq_of_symGprBeq h9, eq_of_symGprBeq h10,
    eq_of_symGprBeq h11, eq_of_symGprBeq h12, eq_of_symGprBeq h13, eq_of_symGprBeq h14,
    eq_of_symGprBeq h15, eq_of_symGprBeq h16, eq_of_symGprBeq h17, eq_of_symGprBeq h18,
    eq_of_symGprBeq h19, eq_of_symGprBeq h20, eq_of_symGprBeq h21, eq_of_symGprBeq h23,
    eq_of_symGprBeq h27, eq_of_symGprBeq h28, eq_of_symGprBeq h29, eq_of_symGprBeq h30⟩

/-! ## 2. `eHat` Barrett Reduction (`+0x59c0 .. +0x5c58`, `w = 5744 .. 5910`) -/

@[expose] def cfgEHatBar : SymCfg := ⟨0, 0, .gpr 1#5, false⟩

@[expose] def symEHatBarInit : SymState :=
  { symEHatNttInit with gprs := symEHatNttInit.gprs.set 1 (.gpr0 1#5 0#64) }

@[expose] def symEHatBarMid : SymState :=
  (runSymRange05Fast none cfgEHatBar 5744 8 symEHatBarInit).getD symEHatBarInit

@[expose] def symEHatBarEnd : SymState :=
  (runSymRange05Fast none cfgEHatBar 5753 157 symEHatBarMid).getD symEHatBarMid

theorem noReloc_eHat_bar_a : blk05NoRelocInRange 5744 5752 = true := by decide +kernel
theorem noReloc_eHat_bar_b : blk05NoRelocInRange 5753 5910 = true := by decide +kernel

theorem run_eHat_bar_a :
    runSymRange05Fast none cfgEHatBar 5744 8 symEHatBarInit = some symEHatBarMid :=
  eq_some_getD05 symEHatBarInit (by decide +kernel)

theorem symEHatBarMid_gpr0 : symEHatBarMid.gprs.get 0 = .gpr0 0#5 0#64 :=
  eq_of_symGprBeq (by decide +kernel)

private def checkEHatBarEnd (st : SymState) : Bool :=
  polyNoSpillVreg false st.poly &&
  polyAstEq false st.poly symBarrett &&
  (symGprBeq (st.gprs.get 0) (.gpr0 0#5 0#64) &&
   symGprBeq (st.gprs.get 1) (.gpr0 1#5 0#64) &&
   symGprBeq (st.gprs.get 3) (.gpr0 3#5 128#64) &&
   symGprBeq (st.gprs.get 9) (.gpr0 9#5 512#64) &&
   symGprBeq (st.gprs.get 10) (.const64 0x019b#64) &&
   symGprBeq (st.gprs.get 11) (.const64 0x229b#64) &&
   symGprBeq (st.gprs.get 12) (.const64 0x6833#64) &&
   symGprBeq (st.gprs.get 13) (.const64 0xf9dd#64) &&
   symGprBeq (st.gprs.get 14) (.const64 0xc0dd#64) &&
   symGprBeq (st.gprs.get 15) (.gpr0 15#5 0#64) &&
   symGprBeq (st.gprs.get 16) (.const64 0xf301#64) &&
   symGprBeq (st.gprs.get 17) (.gpr0 17#5 0#64) &&
   symGprBeq (st.gprs.get 18) (.const64 0x4ebf#64) &&
   symGprBeq (st.gprs.get 19) (.gpr0 19#5 0#64) &&
   symGprBeq (st.gprs.get 20) (.const64 0x47fa#64) &&
   symGprBeq (st.gprs.get 21) (.gpr0 21#5 0#64) &&
   symGprBeq (st.gprs.get 23) (.gpr0 23#5 0#64) &&
   symGprBeq (st.gprs.get 27) (.const64 0x0260#64) &&
   symGprBeq (st.gprs.get 28) (.const64 0x2260#64) &&
   symGprBeq (st.gprs.get 29) (.gpr0 29#5 0#64) &&
   symGprBeq (st.gprs.get 30) (.const64 0xf9fa#64))

set_option maxRecDepth 100000 in
private theorem eHat_bar_cert_all :
    (match runSymRange05Fast none cfgEHatBar 5753 157 symEHatBarMid with
     | some st => checkEHatBarEnd st
     | none => false) = true := by
  decide +kernel

theorem run_eHat_bar_b :
    runSymRange05Fast none cfgEHatBar 5753 157 symEHatBarMid = some symEHatBarEnd := by
  have h := eHat_bar_cert_all
  unfold symEHatBarEnd
  cases hr : runSymRange05Fast none cfgEHatBar 5753 157 symEHatBarMid with
  | none => simp [hr] at h
  | some st => rfl

private theorem eHat_bar_end_ok : checkEHatBarEnd symEHatBarEnd = true := by
  have h := eHat_bar_cert_all
  rwa [run_eHat_bar_b] at h

theorem eHat_bar_noSpillVreg : polyNoSpillVreg false symEHatBarEnd.poly = true := by
  have h := eHat_bar_end_ok; unfold checkEHatBarEnd at h; simp only [Bool.and_eq_true] at h
  exact h.1.1

theorem eHat_bar_ast_eq : polyAstEq false symEHatBarEnd.poly symBarrett = true := by
  have h := eHat_bar_end_ok; unfold checkEHatBarEnd at h; simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem symEHatBarEnd_gprs :
    symEHatBarEnd.gprs.get 0 = .gpr0 0#5 0#64 ∧
    symEHatBarEnd.gprs.get 1 = .gpr0 1#5 0#64 ∧
    symEHatBarEnd.gprs.get 3 = .gpr0 3#5 128#64 ∧
    symEHatBarEnd.gprs.get 9 = .gpr0 9#5 512#64 ∧
    symEHatBarEnd.gprs.get 10 = .const64 0x019b#64 ∧
    symEHatBarEnd.gprs.get 11 = .const64 0x229b#64 ∧
    symEHatBarEnd.gprs.get 12 = .const64 0x6833#64 ∧
    symEHatBarEnd.gprs.get 13 = .const64 0xf9dd#64 ∧
    symEHatBarEnd.gprs.get 14 = .const64 0xc0dd#64 ∧
    symEHatBarEnd.gprs.get 15 = .gpr0 15#5 0#64 ∧
    symEHatBarEnd.gprs.get 16 = .const64 0xf301#64 ∧
    symEHatBarEnd.gprs.get 17 = .gpr0 17#5 0#64 ∧
    symEHatBarEnd.gprs.get 18 = .const64 0x4ebf#64 ∧
    symEHatBarEnd.gprs.get 19 = .gpr0 19#5 0#64 ∧
    symEHatBarEnd.gprs.get 20 = .const64 0x47fa#64 ∧
    symEHatBarEnd.gprs.get 21 = .gpr0 21#5 0#64 ∧
    symEHatBarEnd.gprs.get 23 = .gpr0 23#5 0#64 ∧
    symEHatBarEnd.gprs.get 27 = .const64 0x0260#64 ∧
    symEHatBarEnd.gprs.get 28 = .const64 0x2260#64 ∧
    symEHatBarEnd.gprs.get 29 = .gpr0 29#5 0#64 ∧
    symEHatBarEnd.gprs.get 30 = .const64 0xf9fa#64 := by
  have h0 := eHat_bar_end_ok; unfold checkEHatBarEnd at h0; simp only [Bool.and_eq_true] at h0
  have h := h0.2
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h3⟩, h9⟩, h10⟩,
    h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h23⟩, h27⟩, h28⟩, h29⟩, h30⟩
  exact ⟨eq_of_symGprBeq h0, eq_of_symGprBeq h1, eq_of_symGprBeq h3, eq_of_symGprBeq h9,
    eq_of_symGprBeq h10, eq_of_symGprBeq h11, eq_of_symGprBeq h12, eq_of_symGprBeq h13,
    eq_of_symGprBeq h14, eq_of_symGprBeq h15, eq_of_symGprBeq h16, eq_of_symGprBeq h17,
    eq_of_symGprBeq h18, eq_of_symGprBeq h19, eq_of_symGprBeq h20, eq_of_symGprBeq h21,
    eq_of_symGprBeq h23, eq_of_symGprBeq h27, eq_of_symGprBeq h28, eq_of_symGprBeq h29,
    eq_of_symGprBeq h30⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SymE

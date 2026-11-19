/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem

/-!
# `decapsulate_compressed_key` (`B04`) — Concrete Evaluation & State Relation (`SymPolyEval`)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
  (neonMontgomeryReduce16 neonMontgomeryMul16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
  (lane16 dup8x16 ext_lane16 lane16_dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
  (simdAdd8h simdSub8h simdMul8h simdMla8h simdSqdmulh8h simdSshr8h
   lane16_simdAdd8h lane16_simdSub8h lane16_simdMul8h lane16_simdMla8h
   lane16_simdSqdmulh8h lane16_simdSshr8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
  (simdMontMul8h lane16_simdMontMul8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
  (simdBarrett8h lane16_simdBarrett8h simdBarrett8h_eq_mla)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (Vec32 Poly32Mem Spill13 Spill13Mem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem
  (Spill6 Spill6Mem Spill21 Spill21Mem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
  (SExpr SymGpr SymPState SymVRegs SymSpill13 SymSpill6 SymSpill21 SymVec32
   SymGprs31 SpillMode SymCfg SymState symInit smartMla smartSub)

/-! ## 1. Concrete Environment, Evaluation, & Smart-Constructor Soundness -/

structure SymEnv where
  vreg0     : Nat → BitVec 128
  spill13_0 : Spill13
  spill6_0  : Spill6
  spill21_0 : Spill21
  poly0     : Vec32
  inPoly0   : Vec32
  gpr0      : Nat → BitVec 64
  pstate0   : PState

@[expose] def evalSExpr (env : SymEnv) : SExpr → BitVec 128
  | .poly k => env.poly0.get k
  | .inPoly k => env.inPoly0.get k
  | .spill13_0 k => env.spill13_0.get k
  | .spill6_0 k => env.spill6_0.get k
  | .spill21_0 k => env.spill21_0.get k
  | .vreg0 r => env.vreg0 r
  | .const c => dup8x16 c
  | .add a b => simdAdd8h (evalSExpr env a) (evalSExpr env b)
  | .sub a b => simdSub8h (evalSExpr env a) (evalSExpr env b)
  | .mul a b => simdMul8h (evalSExpr env a) (evalSExpr env b)
  | .mla d a b => simdMla8h (evalSExpr env d) (evalSExpr env a) (evalSExpr env b)
  | .sqdmulh a b => simdSqdmulh8h (evalSExpr env a) (evalSExpr env b)
  | .sshr a sh => simdSshr8h (evalSExpr env a) sh
  | .barrett a => simdBarrett8h (evalSExpr env a)
  | .montmul a z => simdMontMul8h (evalSExpr env a) (dup8x16 z)

@[expose] def evalSymGpr (sp : BitVec 64) (env : SymEnv) : SymGpr → BitVec 64
  | .gpr0 r => env.gpr0 r
  | .const64 v => v
  | .spAdd off => sp + off
  | .addImm a off => evalSymGpr sp env a + off
  | .addReg a b => evalSymGpr sp env a + evalSymGpr sp env b

@[expose] def evalSymPState (sp : BitVec 64) (env : SymEnv) : SymPState → PState
  | .pstate0 => env.pstate0
  | .cmpImm64 lhs imm => (AddWithCarry64 (evalSymGpr sp env lhs) (~~~imm) true).2

@[expose] def evalSymSpill13 (env : SymEnv) (t : SymSpill13) : Spill13 :=
  ⟨evalSExpr env t.s0, evalSExpr env t.s1, evalSExpr env t.s2, evalSExpr env t.s3,
   evalSExpr env t.s4, evalSExpr env t.s5, evalSExpr env t.s6, evalSExpr env t.s7,
   evalSExpr env t.s8, evalSExpr env t.s9, evalSExpr env t.s10, evalSExpr env t.s11,
   evalSExpr env t.s12⟩

@[expose] def evalSymSpill6 (env : SymEnv) (t : SymSpill6) : Spill6 :=
  ⟨evalSExpr env t.s0, evalSExpr env t.s1, evalSExpr env t.s2,
   evalSExpr env t.s3, evalSExpr env t.s4, evalSExpr env t.s5⟩

@[expose] def evalSymSpill21 (env : SymEnv) (t : SymSpill21) : Spill21 :=
  ⟨evalSExpr env t.s0, evalSExpr env t.s1, evalSExpr env t.s2, evalSExpr env t.s3,
   evalSExpr env t.s4, evalSExpr env t.s5, evalSExpr env t.s6, evalSExpr env t.s7,
   evalSExpr env t.s8, evalSExpr env t.s9, evalSExpr env t.s10, evalSExpr env t.s11,
   evalSExpr env t.s12, evalSExpr env t.s13, evalSExpr env t.s14, evalSExpr env t.s15,
   evalSExpr env t.s16, evalSExpr env t.s17, evalSExpr env t.s18, evalSExpr env t.s19,
   evalSExpr env t.s20⟩

@[expose] def evalSymVec32 (env : SymEnv) (t : SymVec32) : Vec32 :=
  ⟨evalSExpr env t.v0, evalSExpr env t.v1, evalSExpr env t.v2, evalSExpr env t.v3,
   evalSExpr env t.v4, evalSExpr env t.v5, evalSExpr env t.v6, evalSExpr env t.v7,
   evalSExpr env t.v8, evalSExpr env t.v9, evalSExpr env t.v10, evalSExpr env t.v11,
   evalSExpr env t.v12, evalSExpr env t.v13, evalSExpr env t.v14, evalSExpr env t.v15,
   evalSExpr env t.v16, evalSExpr env t.v17, evalSExpr env t.v18, evalSExpr env t.v19,
   evalSExpr env t.v20, evalSExpr env t.v21, evalSExpr env t.v22, evalSExpr env t.v23,
   evalSExpr env t.v24, evalSExpr env t.v25, evalSExpr env t.v26, evalSExpr env t.v27,
   evalSExpr env t.v28, evalSExpr env t.v29, evalSExpr env t.v30, evalSExpr env t.v31⟩

private theorem simdAdd8h_comm (a b : BitVec 128) : simdAdd8h a b = simdAdd8h b a := by
  apply ext_lane16; intro i; simp [BitVec.add_comm]

theorem eval_smartMla (env : SymEnv) (d q c : SExpr) :
    evalSExpr env (smartMla d q c) =
      simdMla8h (evalSExpr env d) (evalSExpr env q) (evalSExpr env c) := by
  unfold smartMla; split
  · rename_i a1 a2
    by_cases h1 : (a2.beq (.const 0x0400#16) && a1.beq (.sqdmulh d (.const 0x4ebf#16))) = true
    · simp only [h1, ↓reduceIte]
      simp only [Bool.and_eq_true] at h1
      rw [SExpr.beq_eq_true h1.1, SExpr.beq_eq_true h1.2]
      exact (simdBarrett8h_eq_mla (evalSExpr env d)).symm
    · have h1f := Bool.eq_false_iff.mpr h1
      simp only [h1f, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : (a1.beq (.const 0x0400#16) && a2.beq (.sqdmulh d (.const 0x4ebf#16))) = true
      · simp only [h2, ↓reduceIte]
        simp only [Bool.and_eq_true] at h2
        rw [SExpr.beq_eq_true h2.1, SExpr.beq_eq_true h2.2]
        simp only [evalSExpr]
        rw [simdAdd8h_comm (dup8x16 0x0400#16)]
        exact (simdBarrett8h_eq_mla (evalSExpr env d)).symm
      · simp only [Bool.eq_false_iff.mpr h2, Bool.false_eq_true, ↓reduceIte]; rfl
  · rfl

theorem eval_smartSub (env : SymEnv) (hi lo : SExpr) :
    evalSExpr env (smartSub hi lo) =
      simdSub8h (evalSExpr env hi) (evalSExpr env lo) := by
  unfold smartSub; split
  · rename_i x z km
    by_cases h : km.beq (.mul x (.const (z * 62209#16))) = true
    · simp only [h, ↓reduceIte]
      rw [SExpr.beq_eq_true h]
      apply ext_lane16; intro i
      simp [evalSExpr, neonMontgomeryMul16, neonMontgomeryReduce16, BitVec.mul_assoc]
    · simp only [Bool.eq_false_iff.mpr h, Bool.false_eq_true, ↓reduceIte]; rfl
  · rfl


/-! ## 2. Flat Structure Accessor & Evaluation Lemmas -/

theorem symVRegs_ofFn_get (f : Nat → SExpr) (i : Nat) (hi : i < 32) :
    (SymVRegs.ofFn f).get i = f i := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
  | _ + 32 => omega

private theorem symVRegs_set_eq_ofFn (t : SymVRegs) (k : Nat) (x : SExpr) (hk : k < 32) :
    t.set k x = SymVRegs.ofFn (fun j => if j = k then x else t.get j) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
  | _ + 32 => omega

theorem symVRegs_set_get (t : SymVRegs) (k : Nat) (x : SExpr) (hk : k < 32)
    (i : Nat) (hi : i < 32) :
    (t.set k x).get i = if i = k then x else t.get i := by
  rw [symVRegs_set_eq_ofFn t k x hk, symVRegs_ofFn_get _ i hi]

theorem symGprs31_ofFn_get (f : Nat → SymGpr) (i : Nat) (hi : i < 31) :
    (SymGprs31.ofFn f).get i = f i := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => rfl
  | _ + 31 => omega

private theorem symGprs31_set_eq_ofFn (t : SymGprs31) (k : Nat) (x : SymGpr) (hk : k < 31) :
    t.set k x = SymGprs31.ofFn (fun j => if j = k then x else t.get j) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => rfl
  | _ + 31 => omega

theorem symGprs31_set_get (t : SymGprs31) (k : Nat) (x : SymGpr) (hk : k < 31)
    (i : Nat) (hi : i < 31) :
    (t.set k x).get i = if i = k then x else t.get i := by
  rw [symGprs31_set_eq_ofFn t k x hk, symGprs31_ofFn_get _ i hi]

theorem symSpill13_eval_get (env : SymEnv) (t : SymSpill13) (k : Nat) (hk : k < 13) :
    (evalSymSpill13 env t).get k = evalSExpr env (t.get k) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => rfl
  | _ + 13 => omega

theorem symSpill13_eval_set (env : SymEnv) (t : SymSpill13) (k : Nat) (x : SExpr) :
    evalSymSpill13 env (t.set k x) = (evalSymSpill13 env t).set k (evalSExpr env x) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | _ + 13 => rfl

theorem symSpill6_eval_get (env : SymEnv) (t : SymSpill6) (k : Nat) (hk : k < 6) :
    (evalSymSpill6 env t).get k = evalSExpr env (t.get k) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | _ + 6 => omega

theorem symSpill6_eval_set (env : SymEnv) (t : SymSpill6) (k : Nat) (x : SExpr) :
    evalSymSpill6 env (t.set k x) = (evalSymSpill6 env t).set k (evalSExpr env x) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | _ + 6 => rfl

theorem symSpill21_eval_get (env : SymEnv) (t : SymSpill21) (k : Nat) (hk : k < 21) :
    (evalSymSpill21 env t).get k = evalSExpr env (t.get k) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 => rfl
  | _ + 21 => omega

theorem symSpill21_eval_set (env : SymEnv) (t : SymSpill21) (k : Nat) (x : SExpr) :
    evalSymSpill21 env (t.set k x) = (evalSymSpill21 env t).set k (evalSExpr env x) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | _ + 21 => rfl

theorem symVec32_eval_get (env : SymEnv) (t : SymVec32) (k : Nat) (hk : k < 32) :
    (evalSymVec32 env t).get k = evalSExpr env (t.get k) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
  | _ + 32 => omega

theorem symVec32_eval_set (env : SymEnv) (t : SymVec32) (k : Nat) (x : SExpr) :
    evalSymVec32 env (t.set k x) = (evalSymVec32 env t).set k (evalSExpr env x) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 | _ + 32 => rfl

/-! ## 3. Spatial Footprint & State Matching Relation -/

@[expose] def polyAddr (cfg : SymCfg) (sp polyPtr : BitVec 64) : BitVec 64 :=
  match cfg.polyReg? with
  | some _ => polyPtr
  | none   => sp + 20704#64

@[expose] def spillMemAt (mode : SpillMode) (sp : BitVec 64) (env : SymEnv) (st : SymState) : SepProp :=
  match mode with
  | .none => emp
  | .s21  => Spill21Mem (sp + 1920#64) (evalSymSpill21 env st.spill21)
  | .s27  => Spill6Mem (sp + 1824#64) (evalSymSpill6 env st.spill6) ∗
             Spill21Mem (sp + 1920#64) (evalSymSpill21 env st.spill21)
  | .s40  => Spill13Mem (sp + 1616#64) (evalSymSpill13 env st.spill13) ∗
             Spill6Mem (sp + 1824#64) (evalSymSpill6 env st.spill6) ∗
             Spill21Mem (sp + 1920#64) (evalSymSpill21 env st.spill21)

@[expose] def inPolyMemAt (hasInPoly : Bool) (sp : BitVec 64) (env : SymEnv) : SepProp :=
  match hasInPoly with
  | false => emp
  | true  => Poly32Mem (sp + 11856#64) env.inPoly0

@[expose] def SymSpatial (cfg : SymCfg) (sp polyPtr : BitVec 64)
    (env : SymEnv) (st : SymState) (F : SepProp) : SepProp :=
  Poly32Mem (polyAddr cfg sp polyPtr) (evalSymVec32 env st.poly) ∗
  spillMemAt cfg.spillMode sp env st ∗
  inPolyMemAt cfg.hasInPoly sp env ∗ F

structure SymStateMatches (cfg : SymCfg) (sp polyPtr : BitVec 64) (env : SymEnv)
    (st : SymState) (s : State) : Prop where
  hsp     : s.sp = sp
  hsp_al  : s.spAligned = true
  hpoly   : ∀ r, cfg.polyReg? = some r → s.readReg64 (.gpr r) = polyPtr
  hvregs  : ∀ r : BitVec 5, s.readVReg128 r = evalSExpr env (st.vregs.get r.toNat)
  hgprs   : ∀ r : BitVec 5, r.toNat < 31 → s.readReg64 (.gpr r) = evalSymGpr sp env (st.gprs.get r.toNat)
  hpstate : s.pstate = evalSymPState sp env st.pstate

@[expose] def symEnvOf (s : State) (spill13_0 : Spill13) (spill6_0 : Spill6) (spill21_0 : Spill21)
    (poly0 inPoly0 : Vec32) : SymEnv where
  vreg0     := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill13_0 := spill13_0
  spill6_0  := spill6_0
  spill21_0 := spill21_0
  poly0     := poly0
  inPoly0   := inPoly0
  gpr0      := fun r => s.readReg64 (.gpr (BitVec.ofNat 5 r))
  pstate0   := s.pstate

theorem symInit_matches (cfg : SymCfg) (s : State) (sp polyPtr : BitVec 64)
    (spill13_0 : Spill13) (spill6_0 : Spill6) (spill21_0 : Spill21) (poly0 inPoly0 : Vec32)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hpoly : ∀ r, cfg.polyReg? = some r → s.readReg64 (.gpr r) = polyPtr) :
    let env := symEnvOf s spill13_0 spill6_0 spill21_0 poly0 inPoly0
    SymStateMatches cfg sp polyPtr env symInit s ∧
    evalSymSpill13 env symInit.spill13 = spill13_0 ∧
    evalSymSpill6 env symInit.spill6 = spill6_0 ∧
    evalSymSpill21 env symInit.spill21 = spill21_0 ∧
    evalSymVec32 env symInit.poly = poly0 := by
  refine ⟨⟨hsp, hsp_al, hpoly, ?_, ?_, rfl⟩,
    by cases spill13_0; rfl, by cases spill6_0; rfl, by cases spill21_0; rfl, by cases poly0; rfl⟩
  · intro r
    rw [show symInit.vregs.get r.toNat = .vreg0 r.toNat from
      symVRegs_ofFn_get SExpr.vreg0 r.toNat r.isLt]
    simp [evalSExpr, symEnvOf, BitVec.ofNat_toNat]
  · intro r hr
    rw [show symInit.gprs.get r.toNat = .gpr0 r.toNat from
      symGprs31_ofFn_get SymGpr.gpr0 r.toNat hr]
    simp [evalSymGpr, symEnvOf, BitVec.ofNat_toNat]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval

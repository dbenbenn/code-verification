/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base

/-!
# `decapsulate_compressed_key` (`B04`) — Symbolic NEON + GPR AST & Stepper (`SymPolyDefs`)

Unified straight-line symbolic evaluator covering all 8 NEON NTT / InvNTT / Barrett blocks in `B04`
(`6,566` instructions total).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
  (blkTree04)

/-! ## 1. Symbolic Vector, GPR, & PState ASTs -/

inductive SExpr where
  | poly (k : Nat) | inPoly (k : Nat)
  | spill13_0 (k : Nat) | spill6_0 (k : Nat) | spill21_0 (k : Nat)
  | vreg0 (r : Nat) | const (c : BitVec 16)
  | add (a b : SExpr) | sub (a b : SExpr) | mul (a b : SExpr) | mla (d a b : SExpr)
  | sqdmulh (a b : SExpr) | sshr (a : SExpr) (sh : Nat)
  | barrett (a : SExpr) | montmul (a : SExpr) (z : BitVec 16)
  deriving DecidableEq, Repr

@[expose] def SExpr.beq : SExpr → SExpr → Bool
  | .poly k1, .poly k2 => k1 == k2
  | .inPoly k1, .inPoly k2 => k1 == k2
  | .spill13_0 k1, .spill13_0 k2 => k1 == k2
  | .spill6_0 k1, .spill6_0 k2 => k1 == k2
  | .spill21_0 k1, .spill21_0 k2 => k1 == k2
  | .vreg0 r1, .vreg0 r2 => r1 == r2
  | .const c1, .const c2 => c1 == c2
  | .add a1 b1, .add a2 b2 => a1.beq a2 && b1.beq b2
  | .sub a1 b1, .sub a2 b2 => a1.beq a2 && b1.beq b2
  | .mul a1 b1, .mul a2 b2 => a1.beq a2 && b1.beq b2
  | .mla d1 a1 b1, .mla d2 a2 b2 => d1.beq d2 && a1.beq a2 && b1.beq b2
  | .sqdmulh a1 b1, .sqdmulh a2 b2 => a1.beq a2 && b1.beq b2
  | .sshr a1 s1, .sshr a2 s2 => a1.beq a2 && s1 == s2
  | .barrett a1, .barrett a2 => a1.beq a2
  | .montmul a1 z1, .montmul a2 z2 => a1.beq a2 && z1 == z2
  | _, _ => false

theorem SExpr.beq_eq_true : ∀ {a b : SExpr}, a.beq b = true → a = b
  | .poly _, .poly _, h => by simp [SExpr.beq] at h; subst h; rfl
  | .inPoly _, .inPoly _, h => by simp [SExpr.beq] at h; subst h; rfl
  | .spill13_0 _, .spill13_0 _, h => by simp [SExpr.beq] at h; subst h; rfl
  | .spill6_0 _, .spill6_0 _, h => by simp [SExpr.beq] at h; subst h; rfl
  | .spill21_0 _, .spill21_0 _, h => by simp [SExpr.beq] at h; subst h; rfl
  | .vreg0 _, .vreg0 _, h => by simp [SExpr.beq] at h; subst h; rfl
  | .const _, .const _, h => by simp [SExpr.beq] at h; subst h; rfl
  | .add _ _, .add _ _, h => by
    simp only [SExpr.beq, Bool.and_eq_true] at h; rw [beq_eq_true h.1, beq_eq_true h.2]
  | .sub _ _, .sub _ _, h => by
    simp only [SExpr.beq, Bool.and_eq_true] at h; rw [beq_eq_true h.1, beq_eq_true h.2]
  | .mul _ _, .mul _ _, h => by
    simp only [SExpr.beq, Bool.and_eq_true] at h; rw [beq_eq_true h.1, beq_eq_true h.2]
  | .mla _ _ _, .mla _ _ _, h => by
    simp only [SExpr.beq, Bool.and_eq_true] at h
    rw [beq_eq_true h.1.1, beq_eq_true h.1.2, beq_eq_true h.2]
  | .sqdmulh _ _, .sqdmulh _ _, h => by
    simp only [SExpr.beq, Bool.and_eq_true] at h; rw [beq_eq_true h.1, beq_eq_true h.2]
  | .sshr _ _, .sshr _ _, h => by
    simp only [SExpr.beq, Bool.and_eq_true, beq_iff_eq] at h; rw [beq_eq_true h.1, h.2]
  | .barrett _, .barrett _, h => by simp only [SExpr.beq] at h; rw [beq_eq_true h]
  | .montmul _ _, .montmul _ _, h => by
    simp only [SExpr.beq, Bool.and_eq_true, beq_iff_eq] at h; rw [beq_eq_true h.1, h.2]

inductive SymGpr where
  | gpr0 (r : Nat)
  | const64 (v : BitVec 64)
  | spAdd (off : BitVec 64)
  | addImm (a : SymGpr) (off : BitVec 64)
  | addReg (a b : SymGpr)
  deriving DecidableEq, Repr

inductive SymPState where
  | pstate0
  | cmpImm64 (lhs : SymGpr) (imm : BitVec 64)
  deriving DecidableEq, Repr

structure SymVRegs where
  (v0 v1 v2 v3 v4 v5 v6 v7 : SExpr)
  (v8 v9 v10 v11 v12 v13 v14 v15 : SExpr)
  (v16 v17 v18 v19 v20 v21 v22 v23 : SExpr)
  (v24 v25 v26 v27 v28 v29 v30 v31 : SExpr)
  deriving DecidableEq, Repr

@[expose] def SymVRegs.get (t : SymVRegs) : Nat → SExpr
  | 0 => t.v0 | 1 => t.v1 | 2 => t.v2 | 3 => t.v3 | 4 => t.v4 | 5 => t.v5 | 6 => t.v6 | 7 => t.v7
  | 8 => t.v8 | 9 => t.v9 | 10 => t.v10 | 11 => t.v11 | 12 => t.v12 | 13 => t.v13 | 14 => t.v14 | 15 => t.v15
  | 16 => t.v16 | 17 => t.v17 | 18 => t.v18 | 19 => t.v19 | 20 => t.v20 | 21 => t.v21 | 22 => t.v22 | 23 => t.v23
  | 24 => t.v24 | 25 => t.v25 | 26 => t.v26 | 27 => t.v27 | 28 => t.v28 | 29 => t.v29 | 30 => t.v30 | 31 => t.v31
  | _ => .const 0#16

@[expose] def SymVRegs.set (t : SymVRegs) (k : Nat) (x : SExpr) : SymVRegs :=
  match k with
  | 0 => { t with v0 := x } | 1 => { t with v1 := x } | 2 => { t with v2 := x } | 3 => { t with v3 := x }
  | 4 => { t with v4 := x } | 5 => { t with v5 := x } | 6 => { t with v6 := x } | 7 => { t with v7 := x }
  | 8 => { t with v8 := x } | 9 => { t with v9 := x } | 10 => { t with v10 := x } | 11 => { t with v11 := x }
  | 12 => { t with v12 := x } | 13 => { t with v13 := x } | 14 => { t with v14 := x } | 15 => { t with v15 := x }
  | 16 => { t with v16 := x } | 17 => { t with v17 := x } | 18 => { t with v18 := x } | 19 => { t with v19 := x }
  | 20 => { t with v20 := x } | 21 => { t with v21 := x } | 22 => { t with v22 := x } | 23 => { t with v23 := x }
  | 24 => { t with v24 := x } | 25 => { t with v25 := x } | 26 => { t with v26 := x } | 27 => { t with v27 := x }
  | 28 => { t with v28 := x } | 29 => { t with v29 := x } | 30 => { t with v30 := x } | 31 => { t with v31 := x }
  | _ => t

@[expose] def SymVRegs.ofFn (f : Nat → SExpr) : SymVRegs :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7,
   f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15,
   f 16, f 17, f 18, f 19, f 20, f 21, f 22, f 23,
   f 24, f 25, f 26, f 27, f 28, f 29, f 30, f 31⟩

structure SymSpill13 where
  (s0 s1 s2 s3 s4 s5 s6 s7 : SExpr)
  (s8 s9 s10 s11 s12 : SExpr)
  deriving DecidableEq, Repr

@[expose] def SymSpill13.get (t : SymSpill13) : Nat → SExpr
  | 0 => t.s0 | 1 => t.s1 | 2 => t.s2 | 3 => t.s3 | 4 => t.s4 | 5 => t.s5 | 6 => t.s6 | 7 => t.s7
  | 8 => t.s8 | 9 => t.s9 | 10 => t.s10 | 11 => t.s11 | 12 => t.s12
  | _ => .const 0#16

@[expose] def SymSpill13.set (t : SymSpill13) (k : Nat) (x : SExpr) : SymSpill13 :=
  match k with
  | 0 => { t with s0 := x } | 1 => { t with s1 := x } | 2 => { t with s2 := x } | 3 => { t with s3 := x }
  | 4 => { t with s4 := x } | 5 => { t with s5 := x } | 6 => { t with s6 := x } | 7 => { t with s7 := x }
  | 8 => { t with s8 := x } | 9 => { t with s9 := x } | 10 => { t with s10 := x } | 11 => { t with s11 := x }
  | 12 => { t with s12 := x }
  | _ => t

structure SymSpill6 where
  (s0 s1 s2 s3 s4 s5 : SExpr)
  deriving DecidableEq, Repr

@[expose] def SymSpill6.get (t : SymSpill6) : Nat → SExpr
  | 0 => t.s0 | 1 => t.s1 | 2 => t.s2 | 3 => t.s3 | 4 => t.s4 | 5 => t.s5
  | _ => .const 0#16

@[expose] def SymSpill6.set (t : SymSpill6) (k : Nat) (x : SExpr) : SymSpill6 :=
  match k with
  | 0 => { t with s0 := x } | 1 => { t with s1 := x } | 2 => { t with s2 := x }
  | 3 => { t with s3 := x } | 4 => { t with s4 := x } | 5 => { t with s5 := x }
  | _ => t

structure SymSpill21 where
  (s0 s1 s2 s3 s4 s5 s6 s7 : SExpr)
  (s8 s9 s10 s11 s12 s13 s14 s15 : SExpr)
  (s16 s17 s18 s19 s20 : SExpr)
  deriving DecidableEq, Repr

@[expose] def SymSpill21.get (t : SymSpill21) : Nat → SExpr
  | 0 => t.s0 | 1 => t.s1 | 2 => t.s2 | 3 => t.s3 | 4 => t.s4 | 5 => t.s5 | 6 => t.s6 | 7 => t.s7
  | 8 => t.s8 | 9 => t.s9 | 10 => t.s10 | 11 => t.s11 | 12 => t.s12 | 13 => t.s13 | 14 => t.s14 | 15 => t.s15
  | 16 => t.s16 | 17 => t.s17 | 18 => t.s18 | 19 => t.s19 | 20 => t.s20
  | _ => .const 0#16

@[expose] def SymSpill21.set (t : SymSpill21) (k : Nat) (x : SExpr) : SymSpill21 :=
  match k with
  | 0 => { t with s0 := x } | 1 => { t with s1 := x } | 2 => { t with s2 := x } | 3 => { t with s3 := x }
  | 4 => { t with s4 := x } | 5 => { t with s5 := x } | 6 => { t with s6 := x } | 7 => { t with s7 := x }
  | 8 => { t with s8 := x } | 9 => { t with s9 := x } | 10 => { t with s10 := x } | 11 => { t with s11 := x }
  | 12 => { t with s12 := x } | 13 => { t with s13 := x } | 14 => { t with s14 := x } | 15 => { t with s15 := x }
  | 16 => { t with s16 := x } | 17 => { t with s17 := x } | 18 => { t with s18 := x } | 19 => { t with s19 := x }
  | 20 => { t with s20 := x }
  | _ => t

structure SymVec32 where
  (v0 v1 v2 v3 v4 v5 v6 v7 : SExpr)
  (v8 v9 v10 v11 v12 v13 v14 v15 : SExpr)
  (v16 v17 v18 v19 v20 v21 v22 v23 : SExpr)
  (v24 v25 v26 v27 v28 v29 v30 v31 : SExpr)
  deriving DecidableEq, Repr

@[expose] def SymVec32.get (t : SymVec32) : Nat → SExpr
  | 0 => t.v0 | 1 => t.v1 | 2 => t.v2 | 3 => t.v3 | 4 => t.v4 | 5 => t.v5 | 6 => t.v6 | 7 => t.v7
  | 8 => t.v8 | 9 => t.v9 | 10 => t.v10 | 11 => t.v11 | 12 => t.v12 | 13 => t.v13 | 14 => t.v14 | 15 => t.v15
  | 16 => t.v16 | 17 => t.v17 | 18 => t.v18 | 19 => t.v19 | 20 => t.v20 | 21 => t.v21 | 22 => t.v22 | 23 => t.v23
  | 24 => t.v24 | 25 => t.v25 | 26 => t.v26 | 27 => t.v27 | 28 => t.v28 | 29 => t.v29 | 30 => t.v30 | 31 => t.v31
  | _ => .const 0#16

@[expose] def SymVec32.set (t : SymVec32) (k : Nat) (x : SExpr) : SymVec32 :=
  match k with
  | 0 => { t with v0 := x } | 1 => { t with v1 := x } | 2 => { t with v2 := x } | 3 => { t with v3 := x }
  | 4 => { t with v4 := x } | 5 => { t with v5 := x } | 6 => { t with v6 := x } | 7 => { t with v7 := x }
  | 8 => { t with v8 := x } | 9 => { t with v9 := x } | 10 => { t with v10 := x } | 11 => { t with v11 := x }
  | 12 => { t with v12 := x } | 13 => { t with v13 := x } | 14 => { t with v14 := x } | 15 => { t with v15 := x }
  | 16 => { t with v16 := x } | 17 => { t with v17 := x } | 18 => { t with v18 := x } | 19 => { t with v19 := x }
  | 20 => { t with v20 := x } | 21 => { t with v21 := x } | 22 => { t with v22 := x } | 23 => { t with v23 := x }
  | 24 => { t with v24 := x } | 25 => { t with v25 := x } | 26 => { t with v26 := x } | 27 => { t with v27 := x }
  | 28 => { t with v28 := x } | 29 => { t with v29 := x } | 30 => { t with v30 := x } | 31 => { t with v31 := x }
  | _ => t

structure SymGprs31 where
  (g0 g1 g2 g3 g4 g5 g6 g7 : SymGpr)
  (g8 g9 g10 g11 g12 g13 g14 g15 : SymGpr)
  (g16 g17 g18 g19 g20 g21 g22 g23 : SymGpr)
  (g24 g25 g26 g27 g28 g29 g30 : SymGpr)
  deriving DecidableEq, Repr

@[expose] def SymGprs31.get (t : SymGprs31) : Nat → SymGpr
  | 0 => t.g0 | 1 => t.g1 | 2 => t.g2 | 3 => t.g3 | 4 => t.g4 | 5 => t.g5 | 6 => t.g6 | 7 => t.g7
  | 8 => t.g8 | 9 => t.g9 | 10 => t.g10 | 11 => t.g11 | 12 => t.g12 | 13 => t.g13 | 14 => t.g14 | 15 => t.g15
  | 16 => t.g16 | 17 => t.g17 | 18 => t.g18 | 19 => t.g19 | 20 => t.g20 | 21 => t.g21 | 22 => t.g22 | 23 => t.g23
  | 24 => t.g24 | 25 => t.g25 | 26 => t.g26 | 27 => t.g27 | 28 => t.g28 | 29 => t.g29 | 30 => t.g30
  | _ => .const64 0#64

@[expose] def SymGprs31.set (t : SymGprs31) (k : Nat) (x : SymGpr) : SymGprs31 :=
  match k with
  | 0 => { t with g0 := x } | 1 => { t with g1 := x } | 2 => { t with g2 := x } | 3 => { t with g3 := x }
  | 4 => { t with g4 := x } | 5 => { t with g5 := x } | 6 => { t with g6 := x } | 7 => { t with g7 := x }
  | 8 => { t with g8 := x } | 9 => { t with g9 := x } | 10 => { t with g10 := x } | 11 => { t with g11 := x }
  | 12 => { t with g12 := x } | 13 => { t with g13 := x } | 14 => { t with g14 := x } | 15 => { t with g15 := x }
  | 16 => { t with g16 := x } | 17 => { t with g17 := x } | 18 => { t with g18 := x } | 19 => { t with g19 := x }
  | 20 => { t with g20 := x } | 21 => { t with g21 := x } | 22 => { t with g22 := x } | 23 => { t with g23 := x }
  | 24 => { t with g24 := x } | 25 => { t with g25 := x } | 26 => { t with g26 := x } | 27 => { t with g27 := x }
  | 28 => { t with g28 := x } | 29 => { t with g29 := x } | 30 => { t with g30 := x }
  | _ => t

@[expose] def SymGprs31.ofFn (f : Nat → SymGpr) : SymGprs31 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7,
   f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15,
   f 16, f 17, f 18, f 19, f 20, f 21, f 22, f 23,
   f 24, f 25, f 26, f 27, f 28, f 29, f 30⟩

inductive SpillMode where
  | none | s21 | s27 | s40
  deriving DecidableEq, Repr

structure SymCfg where
  polyReg?  : Option (BitVec 5)
  spillMode : SpillMode
  hasInPoly : Bool
  deriving DecidableEq, Repr

structure SymState where
  vregs   : SymVRegs
  spill13 : SymSpill13
  spill6  : SymSpill6
  spill21 : SymSpill21
  poly    : SymVec32
  gprs    : SymGprs31
  pstate  : SymPState
  deriving DecidableEq, Repr

@[expose] def symInit : SymState where
  vregs   := SymVRegs.ofFn SExpr.vreg0
  spill13 := ⟨.spill13_0 0, .spill13_0 1, .spill13_0 2, .spill13_0 3, .spill13_0 4,
              .spill13_0 5, .spill13_0 6, .spill13_0 7, .spill13_0 8, .spill13_0 9,
              .spill13_0 10, .spill13_0 11, .spill13_0 12⟩
  spill6  := ⟨.spill6_0 0, .spill6_0 1, .spill6_0 2, .spill6_0 3, .spill6_0 4, .spill6_0 5⟩
  spill21 := ⟨.spill21_0 0, .spill21_0 1, .spill21_0 2, .spill21_0 3, .spill21_0 4,
              .spill21_0 5, .spill21_0 6, .spill21_0 7, .spill21_0 8, .spill21_0 9,
              .spill21_0 10, .spill21_0 11, .spill21_0 12, .spill21_0 13, .spill21_0 14,
              .spill21_0 15, .spill21_0 16, .spill21_0 17, .spill21_0 18, .spill21_0 19,
              .spill21_0 20⟩
  poly    := ⟨.poly 0, .poly 1, .poly 2, .poly 3, .poly 4, .poly 5, .poly 6, .poly 7,
              .poly 8, .poly 9, .poly 10, .poly 11, .poly 12, .poly 13, .poly 14, .poly 15,
              .poly 16, .poly 17, .poly 18, .poly 19, .poly 20, .poly 21, .poly 22, .poly 23,
              .poly 24, .poly 25, .poly 26, .poly 27, .poly 28, .poly 29, .poly 30, .poly 31⟩
  gprs    := SymGprs31.ofFn SymGpr.gpr0
  pstate  := .pstate0

/-! ## 2. Smart Constructors & Symbolic Stepper -/

@[expose] def smartMla (d q c : SExpr) : SExpr :=
  match q, c with
  | .sshr (.add a1 a2) 11, .const 0xf2ff#16 =>
      if a2.beq (.const 0x0400#16) && a1.beq (.sqdmulh d (.const 0x4ebf#16)) then .barrett d
      else if a1.beq (.const 0x0400#16) && a2.beq (.sqdmulh d (.const 0x4ebf#16)) then .barrett d
      else .mla d q c
  | _, _ => .mla d q c

@[expose] def smartSub (hi lo : SExpr) : SExpr :=
  match hi, lo with
  | .sshr (.sqdmulh x (.const z)) 1, .sshr (.sqdmulh km (.const 0x0d01#16)) 1 =>
      if km.beq (.mul x (.const (z * 62209#16))) then .montmul x z
      else .sub hi lo
  | _, _ => .sub hi lo

@[expose] def fetchWordTree04 (j : Nat) : Option Instr :=
  match blkTree04.getQuad? j with
  | some (b0, b1, b2, b3) => Arm64.decode (b3 ++ b2 ++ b1 ++ b0)
  | none => none

@[expose] def stepSymInst (cfg : SymCfg) (inst : Instr) (st : SymState) : Option SymState :=
  match inst with
  | .ldrSimd .Q128 vt (.Offset (.gpr base) off) =>
      let o := off.toNat
      if cfg.polyReg? == some base && o < 512 && o % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (st.poly.get (o / 16)) }
      else none
  | .strSimd .Q128 vt (.Offset (.gpr base) off) =>
      let o := off.toNat
      let val := st.vregs.get vt.toNat
      if cfg.polyReg? == some base && o < 512 && o % 16 == 0 then
        some { st with poly := st.poly.set (o / 16) val }
      else none
  | .ldpSimd .Q128 vt1 vt2 (.Offset (.gpr base) off) =>
      let o := off.toNat
      if cfg.polyReg? == some base && o + 16 < 512 && o % 16 == 0 then
        let k := o / 16
        some { st with vregs := (st.vregs.set vt1.toNat (st.poly.get k)).set vt2.toNat (st.poly.get (k + 1)) }
      else none
  | .stpSimd .Q128 vt1 vt2 (.Offset (.gpr base) off) =>
      let o := off.toNat
      let v1 := st.vregs.get vt1.toNat
      let v2 := st.vregs.get vt2.toNat
      if cfg.polyReg? == some base && o + 16 < 512 && o % 16 == 0 then
        let k := o / 16
        some { st with poly := (st.poly.set k v1).set (k + 1) v2 }
      else none
  | .ldrSimd .Q128 vt (.Offset .sp off) =>
      let o := off.toNat
      if cfg.spillMode == .s40 && 1616 ≤ o && o < 1824 && (o - 1616) % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (st.spill13.get ((o - 1616) / 16)) }
      else if (cfg.spillMode == .s27 || cfg.spillMode == .s40) && 1824 ≤ o && o < 1920 && (o - 1824) % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (st.spill6.get ((o - 1824) / 16)) }
      else if cfg.spillMode != .none && 1920 ≤ o && o < 2256 && (o - 1920) % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (st.spill21.get ((o - 1920) / 16)) }
      else if cfg.hasInPoly && 11856 ≤ o && o < 12368 && (o - 11856) % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (.inPoly ((o - 11856) / 16)) }
      else if cfg.polyReg? == none && 20704 ≤ o && o < 21216 && (o - 20704) % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (st.poly.get ((o - 20704) / 16)) }
      else none
  | .strSimd .Q128 vt (.Offset .sp off) =>
      let o := off.toNat
      let val := st.vregs.get vt.toNat
      if cfg.spillMode == .s40 && 1616 ≤ o && o < 1824 && (o - 1616) % 16 == 0 then
        some { st with spill13 := st.spill13.set ((o - 1616) / 16) val }
      else if (cfg.spillMode == .s27 || cfg.spillMode == .s40) && 1824 ≤ o && o < 1920 && (o - 1824) % 16 == 0 then
        some { st with spill6 := st.spill6.set ((o - 1824) / 16) val }
      else if cfg.spillMode != .none && 1920 ≤ o && o < 2256 && (o - 1920) % 16 == 0 then
        some { st with spill21 := st.spill21.set ((o - 1920) / 16) val }
      else if cfg.polyReg? == none && 20704 ≤ o && o < 21216 && (o - 20704) % 16 == 0 then
        some { st with poly := st.poly.set ((o - 20704) / 16) val }
      else none
  | .ldpSimd .Q128 vt1 vt2 (.Offset .sp off) =>
      let o := off.toNat
      if cfg.spillMode == .s40 && 1616 ≤ o && o + 16 < 1824 && (o - 1616) % 16 == 0 then
        let k := (o - 1616) / 16
        some { st with vregs := (st.vregs.set vt1.toNat (st.spill13.get k)).set vt2.toNat (st.spill13.get (k + 1)) }
      else if (cfg.spillMode == .s27 || cfg.spillMode == .s40) && 1824 ≤ o && o + 16 < 1920 && (o - 1824) % 16 == 0 then
        let k := (o - 1824) / 16
        some { st with vregs := (st.vregs.set vt1.toNat (st.spill6.get k)).set vt2.toNat (st.spill6.get (k + 1)) }
      else if cfg.spillMode != .none && 1920 ≤ o && o + 16 < 2256 && (o - 1920) % 16 == 0 then
        let k := (o - 1920) / 16
        some { st with vregs := (st.vregs.set vt1.toNat (st.spill21.get k)).set vt2.toNat (st.spill21.get (k + 1)) }
      else if cfg.hasInPoly && 11856 ≤ o && o + 16 < 12368 && (o - 11856) % 16 == 0 then
        let k := (o - 11856) / 16
        some { st with vregs := (st.vregs.set vt1.toNat (.inPoly k)).set vt2.toNat (.inPoly (k + 1)) }
      else if cfg.polyReg? == none && 20704 ≤ o && o + 16 < 21216 && (o - 20704) % 16 == 0 then
        let k := (o - 20704) / 16
        some { st with vregs := (st.vregs.set vt1.toNat (st.poly.get k)).set vt2.toNat (st.poly.get (k + 1)) }
      else none
  | .stpSimd .Q128 vt1 vt2 (.Offset .sp off) =>
      let o := off.toNat
      let v1 := st.vregs.get vt1.toNat
      let v2 := st.vregs.get vt2.toNat
      if cfg.spillMode == .s40 && 1616 ≤ o && o + 16 < 1824 && (o - 1616) % 16 == 0 then
        let k := (o - 1616) / 16
        some { st with spill13 := (st.spill13.set k v1).set (k + 1) v2 }
      else if (cfg.spillMode == .s27 || cfg.spillMode == .s40) && 1824 ≤ o && o + 16 < 1920 && (o - 1824) % 16 == 0 then
        let k := (o - 1824) / 16
        some { st with spill6 := (st.spill6.set k v1).set (k + 1) v2 }
      else if cfg.spillMode != .none && 1920 ≤ o && o + 16 < 2256 && (o - 1920) % 16 == 0 then
        let k := (o - 1920) / 16
        some { st with spill21 := (st.spill21.set k v1).set (k + 1) v2 }
      else if cfg.polyReg? == none && 20704 ≤ o && o + 16 < 21216 && (o - 20704) % 16 == 0 then
        let k := (o - 20704) / 16
        some { st with poly := (st.poly.set k v1).set (k + 1) v2 }
      else none
  | .moveWide .W32 .MOVZ (.gpr rd) imm16 0 =>
      if cfg.polyReg? != some rd && rd.toNat < 31 then
        some { st with gprs := st.gprs.set rd.toNat (.const64 (imm16.zeroExtend 64)) }
      else none
  | .logicalShift .W64 .ORR (.gpr rd) .xzr rm .LSL 0 =>
      if cfg.polyReg? != some rd && rd.toNat < 31 then
        match rm with
        | .xzr => some { st with gprs := st.gprs.set rd.toNat (.const64 0#64) }
        | .gpr rs =>
            if rs.toNat < 31 then
              some { st with gprs := st.gprs.set rd.toNat (st.gprs.get rs.toNat) }
            else none
        | .sp => none
      else none
  | .addSubImm .W64 .ADD (.gpr rd) .sp imm12 shift12 =>
      if cfg.polyReg? != some rd && rd.toNat < 31 then
        let off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
        some { st with gprs := st.gprs.set rd.toNat (.spAdd off64) }
      else none
  | .addSubImm .W64 .ADD (.gpr rd) (.gpr rn) imm12 shift12 =>
      if cfg.polyReg? != some rd && rd.toNat < 31 && rn.toNat < 31 then
        let off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
        some { st with gprs := st.gprs.set rd.toNat (.addImm (st.gprs.get rn.toNat) off64) }
      else none
  | .addSubShift .W64 .ADD (.gpr rd) (.gpr rn) (.gpr rm) .LSL 0 =>
      if cfg.polyReg? != some rd && rd.toNat < 31 && rn.toNat < 31 && rm.toNat < 31 then
        some { st with gprs := st.gprs.set rd.toNat (.addReg (st.gprs.get rn.toNat) (st.gprs.get rm.toNat)) }
      else none
  | .addSubImm .W64 .SUBS .xzr (.gpr rn) imm12 false =>
      if rn.toNat < 31 then
        some { st with pstate := .cmpImm64 (st.gprs.get rn.toNat) (imm12.zeroExtend 64) }
      else none
  | .simdInsDup true false 2#5 1#4 rn rd =>
      if rn.toNat < 31 then
        match st.gprs.get rn.toNat with
        | .const64 v => some { st with vregs := st.vregs.set rd.toNat (.const (v.truncate 16)) }
        | _ => none
      else none
  | .simdThreeSame true u sz rm opcode rn rd =>
      if !u && sz == 2#2 && opcode == 0b00011#5 && rm == rn then
        some { st with vregs := st.vregs.set rd.toNat (st.vregs.get rn.toNat) }
      else if !u && sz == 1#2 && opcode == 0b10000#5 then
        some { st with vregs := st.vregs.set rd.toNat (.add (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)) }
      else if u && sz == 1#2 && opcode == 0b10000#5 then
        some { st with vregs := st.vregs.set rd.toNat (smartSub (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)) }
      else if !u && sz == 1#2 && opcode == 0b10011#5 then
        some { st with vregs := st.vregs.set rd.toNat (.mul (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)) }
      else if !u && sz == 1#2 && opcode == 0b10010#5 then
        let res := smartMla (st.vregs.get rd.toNat) (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)
        some { st with vregs := st.vregs.set rd.toNat res }
      else if !u && sz == 1#2 && opcode == 0b10110#5 then
        some { st with vregs := st.vregs.set rd.toNat (.sqdmulh (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)) }
      else none
  | .simdImmShift true op immh immb opcode rn rd =>
      if immh == 0#4 && opcode == 0b10000#5 then
        let c16 := (immb ++ rn).zeroExtend 16
        some { st with vregs := st.vregs.set rd.toNat (.const (if op then ~~~c16 else c16)) }
      else if immh == 0#4 && opcode == 0b10100#5 then
        let c16 := ((immb ++ rn).zeroExtend 16) <<< 8
        some { st with vregs := st.vregs.set rd.toNat (.const (if op then ~~~c16 else c16)) }
      else if !op && immh == 0b0011#4 && immb == 0b111#3 && opcode == 0b00000#5 then
        some { st with vregs := st.vregs.set rd.toNat (.sshr (st.vregs.get rn.toNat) 1) }
      else if !op && immh == 0b0010#4 && immb == 0b101#3 && opcode == 0b00000#5 then
        some { st with vregs := st.vregs.set rd.toNat (.sshr (st.vregs.get rn.toNat) 11) }
      else none
  | _ => none

@[expose] def runSymRange (cfg : SymCfg) (startWord : Nat) : Nat → SymState → Option SymState
  | 0, st => some st
  | n + 1, st =>
      match fetchWordTree04 startWord with
      | some inst =>
          match stepSymInst cfg inst st with
          | some st' => runSymRange cfg (startWord + 1) n st'
          | none => none
      | none => none

theorem runSymRange_add (cfg : SymCfg) (w m n : Nat) (st0 st1 st2 : SymState)
    (h1 : runSymRange cfg w m st0 = some st1)
    (h2 : runSymRange cfg (w + m) n st1 = some st2) :
    runSymRange cfg w (m + n) st0 = some st2 := by
  induction m generalizing w st0 with
  | zero =>
    simp only [runSymRange, Option.some.injEq] at h1
    subst h1
    simpa [Nat.zero_add] using h2
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 from by omega]
    unfold runSymRange at h1 ⊢
    cases hfw : fetchWordTree04 w with
    | none => simp [hfw] at h1
    | some inst =>
      simp only [hfw] at h1 ⊢
      cases hst : stepSymInst cfg inst st0 with
      | none => simp [hst] at h1
      | some st' =>
        simp only [hst] at h1 ⊢
        exact ih (w + 1) st' h1 (by simpa [show w + 1 + m = w + (m + 1) from by omega] using h2)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs

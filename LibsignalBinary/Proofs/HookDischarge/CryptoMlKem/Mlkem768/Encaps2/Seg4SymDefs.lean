/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import

/-!
# `encapsulate2` (`B20`) — Symbolic AST, Stepper, & State Relation (`Seg4SymDefs`)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs

open Arm64 Arm64.Obj ProofLib SepProp
open ProofLib.ProgramReflection (WordTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
  (sqdmulh16 neonBarrettReduce16 neonMontgomeryReduce16 neonMontgomeryMul16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
  (lane16 pack8x16 dup8x16 ext_lane16 lane16_pack8x16 lane16_dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
  (simdAdd8h simdSub8h simdMul8h simdMla8h simdSqdmulh8h simdSshr8h
   lane16_simdAdd8h lane16_simdSub8h lane16_simdMul8h lane16_simdMla8h
   lane16_simdSqdmulh8h lane16_simdSshr8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
  (simdMontMul8h lane16_simdMontMul8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
  (simdBarrett8h lane16_simdBarrett8h simdBarrett8h_eq_mla)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
  (blkTree20 UnspilledSaved20)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (Vec32 Poly32Mem Spill13 Spill13Mem)

/-! ## 1. Symbolic Vector AST & Flat Symbolic State -/

inductive SExpr where
  | poly (k : Nat) | spill0 (k : Nat) | vreg0 (r : Nat) | const (c : BitVec 16)
  | add (a b : SExpr) | sub (a b : SExpr) | mul (a b : SExpr) | mla (d a b : SExpr)
  | sqdmulh (a b : SExpr) | sshr (a : SExpr) (sh : Nat)
  | barrett (a : SExpr) | montmul (a : SExpr) (z : BitVec 16)
  deriving DecidableEq, Repr

@[expose] def SExpr.beq : SExpr → SExpr → Bool
  | .poly k1, .poly k2 => k1 == k2
  | .spill0 k1, .spill0 k2 => k1 == k2
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
  | .spill0 _, .spill0 _, h => by simp [SExpr.beq] at h; subst h; rfl
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
  | unknown | const64 (v : BitVec 64) | spAdd (off : BitVec 64)
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

structure SymGprs where
  (x0 x1 x2 x8 x9 x20 : SymGpr)
  deriving DecidableEq, Repr

@[expose] def SymGprs.get? (g : SymGprs) (r : BitVec 5) : Option SymGpr :=
  if r == 0#5 then some g.x0
  else if r == 1#5 then some g.x1
  else if r == 2#5 then some g.x2
  else if r == 8#5 then some g.x8
  else if r == 9#5 then some g.x9
  else if r == 20#5 then some g.x20
  else none

@[expose] def SymGprs.set? (g : SymGprs) (r : BitVec 5) (v : SymGpr) : Option SymGprs :=
  if r == 0#5 then some { g with x0 := v }
  else if r == 1#5 then some { g with x1 := v }
  else if r == 2#5 then some { g with x2 := v }
  else if r == 8#5 then some { g with x8 := v }
  else if r == 9#5 then some { g with x9 := v }
  else if r == 20#5 then some { g with x20 := v }
  else none

structure SymState where
  vregs : SymVRegs
  spill : SymSpill13
  poly  : SymVec32
  gprs  : SymGprs
  deriving DecidableEq, Repr

@[expose] def symInit4 : SymState where
  vregs := ⟨.vreg0 0, .vreg0 1, .vreg0 2, .vreg0 3, .vreg0 4, .vreg0 5, .vreg0 6, .vreg0 7,
            .vreg0 8, .vreg0 9, .vreg0 10, .vreg0 11, .vreg0 12, .vreg0 13, .vreg0 14, .vreg0 15,
            .vreg0 16, .vreg0 17, .vreg0 18, .vreg0 19, .vreg0 20, .vreg0 21, .vreg0 22, .vreg0 23,
            .vreg0 24, .vreg0 25, .vreg0 26, .vreg0 27, .vreg0 28, .vreg0 29, .vreg0 30, .vreg0 31⟩
  spill := ⟨.spill0 0, .spill0 1, .spill0 2, .spill0 3, .spill0 4, .spill0 5, .spill0 6, .spill0 7,
            .spill0 8, .spill0 9, .spill0 10, .spill0 11, .spill0 12⟩
  poly  := ⟨.poly 0, .poly 1, .poly 2, .poly 3, .poly 4, .poly 5, .poly 6, .poly 7,
            .poly 8, .poly 9, .poly 10, .poly 11, .poly 12, .poly 13, .poly 14, .poly 15,
            .poly 16, .poly 17, .poly 18, .poly 19, .poly 20, .poly 21, .poly 22, .poly 23,
            .poly 24, .poly 25, .poly 26, .poly 27, .poly 28, .poly 29, .poly 30, .poly 31⟩
  gprs  := ⟨.unknown, .unknown, .unknown, .unknown, .unknown, .unknown⟩

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

@[expose] def fetchWordTree20 (j : Nat) : Option Instr :=
  match blkTree20.getQuad? j with
  | some (b0, b1, b2, b3) => Arm64.decode (b3 ++ b2 ++ b1 ++ b0)
  | none => none

@[expose] def stepSymInst (inst : Instr) (st : SymState) : Option SymState :=
  match inst with
  | .ldrSimd .Q128 vt (.Offset .sp off) =>
      let o := off.toNat
      if o < 208 && o % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (st.spill.get (o / 16)) }
      else if 2928 ≤ o && o < 3440 && (o - 2928) % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (st.poly.get ((o - 2928) / 16)) }
      else none
  | .strSimd .Q128 vt (.Offset .sp off) =>
      let o := off.toNat
      let val := st.vregs.get vt.toNat
      if o < 208 && o % 16 == 0 then
        some { st with spill := st.spill.set (o / 16) val }
      else if 2928 ≤ o && o < 3440 && (o - 2928) % 16 == 0 then
        some { st with poly := st.poly.set ((o - 2928) / 16) val }
      else none
  | .ldpSimd .Q128 vt1 vt2 (.Offset .sp off) =>
      let o := off.toNat
      if o + 16 < 208 && o % 16 == 0 then
        let k := o / 16
        some { st with vregs := (st.vregs.set vt1.toNat (st.spill.get k)).set vt2.toNat (st.spill.get (k + 1)) }
      else if 2928 ≤ o && o + 16 < 3440 && (o - 2928) % 16 == 0 then
        let k := (o - 2928) / 16
        some { st with vregs := (st.vregs.set vt1.toNat (st.poly.get k)).set vt2.toNat (st.poly.get (k + 1)) }
      else none
  | .stpSimd .Q128 vt1 vt2 (.Offset .sp off) =>
      let o := off.toNat
      let v1 := st.vregs.get vt1.toNat
      let v2 := st.vregs.get vt2.toNat
      if o + 16 < 208 && o % 16 == 0 then
        let k := o / 16
        some { st with spill := (st.spill.set k v1).set (k + 1) v2 }
      else if 2928 ≤ o && o + 16 < 3440 && (o - 2928) % 16 == 0 then
        let k := (o - 2928) / 16
        some { st with poly := (st.poly.set k v1).set (k + 1) v2 }
      else none
  | .moveWide .W32 .MOVZ (.gpr rd) imm16 0 =>
      match st.gprs.set? rd (.const64 (imm16.zeroExtend 64)) with
      | some g' => some { st with gprs := g' }
      | none => none
  | .addSubImm .W64 .ADD (.gpr rd) .sp imm12 shift12 =>
      let off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
      match st.gprs.set? rd (.spAdd off64) with
      | some g' => some { st with gprs := g' }
      | none => none
  | .simdInsDup true false 2#5 1#4 rn rd =>
      match st.gprs.get? rn with
      | some (.const64 v) => some { st with vregs := st.vregs.set rd.toNat (.const (v.truncate 16)) }
      | _ => none
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

@[expose] def runSymRange (startWord : Nat) : Nat → SymState → Option SymState
  | 0, st => some st
  | n + 1, st =>
      match fetchWordTree20 startWord with
      | some inst =>
          match stepSymInst inst st with
          | some st' => runSymRange (startWord + 1) n st'
          | none => none
      | none => none

theorem runSymRange_add (w m n : Nat) (st0 st1 st2 : SymState)
    (h1 : runSymRange w m st0 = some st1)
    (h2 : runSymRange (w + m) n st1 = some st2) :
    runSymRange w (m + n) st0 = some st2 := by
  induction m generalizing w st0 with
  | zero =>
    simp only [runSymRange, Option.some.injEq] at h1
    subst h1
    simpa [Nat.zero_add] using h2
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 from by omega]
    unfold runSymRange at h1 ⊢
    cases hfw : fetchWordTree20 w with
    | none => simp [hfw] at h1
    | some inst =>
      simp only [hfw] at h1 ⊢
      cases hst : stepSymInst inst st0 with
      | none => simp [hst] at h1
      | some st' =>
        simp only [hst] at h1 ⊢
        exact ih (w + 1) st' h1 (by simpa [show w + 1 + m = w + (m + 1) from by omega] using h2)

/-! ## 3. Concrete Environment, Evaluation, & Smart-Constructor Soundness -/

structure SymEnv where
  vreg0  : Nat → BitVec 128
  spill0 : Spill13
  poly0  : Vec32

@[expose] def evalSExpr (env : SymEnv) : SExpr → BitVec 128
  | .poly k => env.poly0.get k
  | .spill0 k => env.spill0.get k
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

@[expose] def SymSpill13.eval (env : SymEnv) (t : SymSpill13) : Spill13 :=
  ⟨evalSExpr env t.s0, evalSExpr env t.s1, evalSExpr env t.s2, evalSExpr env t.s3,
   evalSExpr env t.s4, evalSExpr env t.s5, evalSExpr env t.s6, evalSExpr env t.s7,
   evalSExpr env t.s8, evalSExpr env t.s9, evalSExpr env t.s10, evalSExpr env t.s11,
   evalSExpr env t.s12⟩

@[expose] def SymVec32.eval (env : SymEnv) (t : SymVec32) : Vec32 :=
  ⟨evalSExpr env t.v0, evalSExpr env t.v1, evalSExpr env t.v2, evalSExpr env t.v3,
   evalSExpr env t.v4, evalSExpr env t.v5, evalSExpr env t.v6, evalSExpr env t.v7,
   evalSExpr env t.v8, evalSExpr env t.v9, evalSExpr env t.v10, evalSExpr env t.v11,
   evalSExpr env t.v12, evalSExpr env t.v13, evalSExpr env t.v14, evalSExpr env t.v15,
   evalSExpr env t.v16, evalSExpr env t.v17, evalSExpr env t.v18, evalSExpr env t.v19,
   evalSExpr env t.v20, evalSExpr env t.v21, evalSExpr env t.v22, evalSExpr env t.v23,
   evalSExpr env t.v24, evalSExpr env t.v25, evalSExpr env t.v26, evalSExpr env t.v27,
   evalSExpr env t.v28, evalSExpr env t.v29, evalSExpr env t.v30, evalSExpr env t.v31⟩

theorem simdAdd8h_comm (a b : BitVec 128) : simdAdd8h a b = simdAdd8h b a := by
  apply ext_lane16
  intro i
  simp [BitVec.add_comm]

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

/-! ## 4. Flat Table Indexing & Concrete State Matching -/

theorem symVRegs_ofFn_get (f : Nat → SExpr) (j : Nat) (hj : j < 32) :
    (SymVRegs.ofFn f).get j = f j := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
  | _ + 32 => omega

private theorem symVRegs_set_eq_ofFn (t : SymVRegs) (k : Nat) (hk : k < 32) (x : SExpr) :
    t.set k x = SymVRegs.ofFn (fun j => if j = k then x else t.get j) := by
  cases t
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
  | _ + 32 => omega

theorem symVRegs_set_get (t : SymVRegs) (k j : Nat) (hk : k < 32) (hj : j < 32) (x : SExpr) :
    (t.set k x).get j = if j = k then x else t.get j := by
  rw [symVRegs_set_eq_ofFn t k hk x, symVRegs_ofFn_get _ j hj]

theorem symSpill13_eval_get (env : SymEnv) (t : SymSpill13) (k : Nat) (hk : k < 13) :
    (t.eval env).get k = evalSExpr env (t.get k) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => rfl
  | _ + 13 => omega

theorem symSpill13_eval_set (env : SymEnv) (t : SymSpill13) (k : Nat) (x : SExpr) :
    (t.set k x).eval env = (t.eval env).set k (evalSExpr env x) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | _ + 13 => rfl

theorem symVec32_eval_get (env : SymEnv) (t : SymVec32) (k : Nat) (hk : k < 32) :
    (t.eval env).get k = evalSExpr env (t.get k) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
  | _ + 32 => omega

theorem symVec32_eval_set (env : SymEnv) (t : SymVec32) (k : Nat) (x : SExpr) :
    (t.set k x).eval env = (t.eval env).set k (evalSExpr env x) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 | _ + 32 => rfl

@[expose] def SymGprMatches (sp val : BitVec 64) : SymGpr → Prop
  | .unknown => True
  | .const64 v => val = v
  | .spAdd off => val = sp + off

structure SymStateMatches (s0 : State) (sp ret : BitVec 64) (env : SymEnv)
    (st : SymState) (s : State) : Prop where
  hsp    : s.sp = sp
  hsp_al : s.spAligned = true
  hx19   : s.readReg64 .x19 = ret
  hunsp  : UnspilledSaved20 s0 s
  hvregs : ∀ r : BitVec 5, s.readVReg128 r = evalSExpr env (st.vregs.get r.toNat)
  hx0    : SymGprMatches sp (s.readReg64 .x0) st.gprs.x0
  hx1    : SymGprMatches sp (s.readReg64 .x1) st.gprs.x1
  hx2    : SymGprMatches sp (s.readReg64 .x2) st.gprs.x2
  hx8    : SymGprMatches sp (s.readReg64 .x8) st.gprs.x8
  hx9    : SymGprMatches sp (s.readReg64 .x9) st.gprs.x9
  hx20   : SymGprMatches sp (s.readReg64 .x20) st.gprs.x20

@[expose] def SymSpatial (sp : BitVec 64) (env : SymEnv) (st : SymState) (F : SepProp) : SepProp :=
  Spill13Mem sp (st.spill.eval env) ∗ Poly32Mem (sp + 2928#64) (st.poly.eval env) ∗ F

theorem symInit4_matches (s0 s : State) (sp ret : BitVec 64) (spill0 : Spill13) (poly0 : Vec32)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = ret) (hunsp : UnspilledSaved20 s0 s) :
    let env : SymEnv :=
      { vreg0 := fun r => s.readVReg128 (BitVec.ofNat 5 r), spill0 := spill0, poly0 := poly0 }
    SymStateMatches s0 sp ret env symInit4 s ∧
    (∀ F, SymSpatial sp env symInit4 F = (Spill13Mem sp spill0 ∗ Poly32Mem (sp + 2928#64) poly0 ∗ F)) := by
  refine ⟨⟨hsp, hsp_al, hx19, hunsp, ?_, trivial, trivial, trivial, trivial, trivial, trivial⟩, ?_⟩
  · intro r
    have hr : r.toNat < 32 := r.isLt
    have hget : symInit4.vregs.get r.toNat = .vreg0 r.toNat :=
      symVRegs_ofFn_get SExpr.vreg0 r.toNat hr
    rw [hget]
    simp [evalSExpr, BitVec.ofNat_toNat]
  · intro F
    have hs : symInit4.spill.eval
        { vreg0 := fun r => s.readVReg128 (BitVec.ofNat 5 r), spill0 := spill0, poly0 := poly0 } =
        spill0 := by
      cases spill0; rfl
    have hp : symInit4.poly.eval
        { vreg0 := fun r => s.readVReg128 (BitVec.ofNat 5 r), spill0 := spill0, poly0 := poly0 } =
        poly0 := by
      cases poly0; rfl
    simp [SymSpatial, hs, hp]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs

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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base

/-!
# `kyber_decapsulate` (`B06`): Generalized Symbolic NEON Engine

1. `SExpr` vector AST (mutable `poly` and read-only `src` 32-vector arrays), 40-slot flat
   `Spill40` / `SymSpill40`, 31-register flat `SymGprs`, and `SymCfg`.
2. `stepSymInst` and `runSymRange` covering all 8 straight-line NEON slices in `B06` (`6,566`
   instructions across forward Montgomery/binomial `NTT`, `Barrett`, and `upperInvNtt16`).
3. Concrete evaluation (`evalSExpr`) and smart-constructor soundness (`eval_smartMla`,
   `eval_smartSub`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs

open Arm64 ProofLib SepProp BitVec
open ProofLib.ProgramReflection (WordTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  neonBarrettReduce16
  neonMontgomeryMul16
  neonMontgomeryReduce16
  sqdmulh16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16
  ext_lane16
  lane16
  lane16_dup8x16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_simdAdd8h
  lane16_simdMla8h
  lane16_simdMul8h
  lane16_simdSqdmulh8h
  lane16_simdSshr8h
  lane16_simdSub8h
  simdAdd8h
  simdMla8h
  simdMul8h
  simdSqdmulh8h
  simdSshr8h
  simdSub8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (
  lane16_simdMontMul8h
  simdMontMul8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt (
  lane16_simdBarrett8h
  simdBarrett8h
  simdBarrett8h_eq_mla
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem
  SepLoad128
  SepStore128
  Vec32
  VecRangeMem
  vecRangeMem_congr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (blkTree06)

/-! ## 1. Symbolic Vector AST, 40-Slot Spill Table, & 31-Register GPR Table -/

inductive SExpr where
  | poly (k : Nat) | src (k : Nat) | spill0 (k : Nat) | vreg0 (r : Nat) | const (c : BitVec 16)
  | add (a b : SExpr) | sub (a b : SExpr) | mul (a b : SExpr) | mla (d a b : SExpr)
  | sqdmulh (a b : SExpr) | sshr (a : SExpr) (sh : Nat)
  | barrett (a : SExpr) | montmul (a : SExpr) (z : BitVec 16)
  deriving DecidableEq, Repr

@[expose] def SExpr.beq : SExpr → SExpr → Bool
  | .poly k1, .poly k2 => k1 == k2
  | .src k1, .src k2 => k1 == k2
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
  | .src _, .src _, h => by simp [SExpr.beq] at h; subst h; rfl
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
  | gpr0 (r : BitVec 5) (off : BitVec 64)
  | spAdd (off : BitVec 64)
  | const64 (v : BitVec 64)
  | addGpr0 (r1 r2 : BitVec 5)
  deriving DecidableEq, Repr

@[expose] def evalSymGpr (sp : BitVec 64) (gpr0 : BitVec 5 → BitVec 64) : SymGpr → BitVec 64
  | .gpr0 r off => gpr0 r + off
  | .spAdd off => sp + off
  | .const64 v => v
  | .addGpr0 r1 r2 => gpr0 r1 + gpr0 r2

structure Spill40 where
  (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 128)
  (s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 : BitVec 128)
  (s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 : BitVec 128)
  (s30 s31 s32 s33 s34 s35 s36 s37 s38 s39 : BitVec 128)

@[expose] def Spill40.get (t : Spill40) : Nat → BitVec 128
  | 0 => t.s0 | 1 => t.s1 | 2 => t.s2 | 3 => t.s3 | 4 => t.s4
  | 5 => t.s5 | 6 => t.s6 | 7 => t.s7 | 8 => t.s8 | 9 => t.s9
  | 10 => t.s10 | 11 => t.s11 | 12 => t.s12 | 13 => t.s13 | 14 => t.s14
  | 15 => t.s15 | 16 => t.s16 | 17 => t.s17 | 18 => t.s18 | 19 => t.s19
  | 20 => t.s20 | 21 => t.s21 | 22 => t.s22 | 23 => t.s23 | 24 => t.s24
  | 25 => t.s25 | 26 => t.s26 | 27 => t.s27 | 28 => t.s28 | 29 => t.s29
  | 30 => t.s30 | 31 => t.s31 | 32 => t.s32 | 33 => t.s33 | 34 => t.s34
  | 35 => t.s35 | 36 => t.s36 | 37 => t.s37 | 38 => t.s38 | 39 => t.s39
  | _ => 0#128

@[expose] def Spill40.set (t : Spill40) (k : Nat) (x : BitVec 128) : Spill40 :=
  match k with
  | 0 => { t with s0 := x } | 1 => { t with s1 := x } | 2 => { t with s2 := x } | 3 => { t with s3 := x }
  | 4 => { t with s4 := x } | 5 => { t with s5 := x } | 6 => { t with s6 := x } | 7 => { t with s7 := x }
  | 8 => { t with s8 := x } | 9 => { t with s9 := x } | 10 => { t with s10 := x } | 11 => { t with s11 := x }
  | 12 => { t with s12 := x } | 13 => { t with s13 := x } | 14 => { t with s14 := x } | 15 => { t with s15 := x }
  | 16 => { t with s16 := x } | 17 => { t with s17 := x } | 18 => { t with s18 := x } | 19 => { t with s19 := x }
  | 20 => { t with s20 := x } | 21 => { t with s21 := x } | 22 => { t with s22 := x } | 23 => { t with s23 := x }
  | 24 => { t with s24 := x } | 25 => { t with s25 := x } | 26 => { t with s26 := x } | 27 => { t with s27 := x }
  | 28 => { t with s28 := x } | 29 => { t with s29 := x } | 30 => { t with s30 := x } | 31 => { t with s31 := x }
  | 32 => { t with s32 := x } | 33 => { t with s33 := x } | 34 => { t with s34 := x } | 35 => { t with s35 := x }
  | 36 => { t with s36 := x } | 37 => { t with s37 := x } | 38 => { t with s38 := x } | 39 => { t with s39 := x }
  | _ => t

@[expose] def Spill40.ofFn (f : Nat → BitVec 128) : Spill40 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9,
   f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18, f 19,
   f 20, f 21, f 22, f 23, f 24, f 25, f 26, f 27, f 28, f 29,
   f 30, f 31, f 32, f 33, f 34, f 35, f 36, f 37, f 38, f 39⟩

@[expose] def Spill40.zero : Spill40 := Spill40.ofFn (fun _ => 0#128)
@[expose] def SpillSliceMem (n : Nat) (ptr : BitVec 64) (t : Spill40) : SepProp :=
  VecRangeMem n ptr t.get

theorem spill40_ofFn_get (f : Nat → BitVec 128) (i : Nat) (hi : i < 40) :
    (Spill40.ofFn f).get i = f i := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29
  | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 => rfl
  | _ + 40 => omega

private theorem spill40_set_eq_ofFn (t : Spill40) (k : Nat) (x : BitVec 128) (hk : k < 40) :
    t.set k x = Spill40.ofFn (fun j => if j = k then x else t.get j) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29
  | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 => rfl
  | _ + 40 => omega

theorem spill40_set_get (t : Spill40) (k : Nat) (x : BitVec 128) (hk : k < 40)
    (i : Nat) (hi : i < 40) :
    Function.update t.get k x i = (t.set k x).get i := by
  rw [spill40_set_eq_ofFn t k x hk, spill40_ofFn_get _ i hi]
  by_cases h : i = k <;> simp [h]

theorem SepLoad128.spillSlice {n k : Nat} {ea ptr : BitVec 64} {t : Spill40} {v : BitVec 128}
    (hk : k < n) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (hv : t.get k = v) :
    SepLoad128 ea (SpillSliceMem n ptr t) v := by
  rw [← hv]; exact SepLoad128.vecRange hk ha

theorem SepStore128.spillSlice {n k : Nat} {ea ptr : BitVec 64} {t t' : Spill40} {val : BitVec 128}
    (hk : k < n) (hn : n ≤ 40) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (ht : t.set k val = t') :
    SepStore128 ea val (SpillSliceMem n ptr t) (SpillSliceMem n ptr t') := by
  rw [← ht]; unfold SpillSliceMem
  rw [← vecRangeMem_congr (fun i hi => spill40_set_get t k val (by omega) i (by omega))]
  exact SepStore128.vecRange hk ha

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

structure SymSpill40 where
  (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : SExpr)
  (s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 : SExpr)
  (s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 : SExpr)
  (s30 s31 s32 s33 s34 s35 s36 s37 s38 s39 : SExpr)
  deriving DecidableEq, Repr

@[expose] def SymSpill40.get (t : SymSpill40) : Nat → SExpr
  | 0 => t.s0 | 1 => t.s1 | 2 => t.s2 | 3 => t.s3 | 4 => t.s4
  | 5 => t.s5 | 6 => t.s6 | 7 => t.s7 | 8 => t.s8 | 9 => t.s9
  | 10 => t.s10 | 11 => t.s11 | 12 => t.s12 | 13 => t.s13 | 14 => t.s14
  | 15 => t.s15 | 16 => t.s16 | 17 => t.s17 | 18 => t.s18 | 19 => t.s19
  | 20 => t.s20 | 21 => t.s21 | 22 => t.s22 | 23 => t.s23 | 24 => t.s24
  | 25 => t.s25 | 26 => t.s26 | 27 => t.s27 | 28 => t.s28 | 29 => t.s29
  | 30 => t.s30 | 31 => t.s31 | 32 => t.s32 | 33 => t.s33 | 34 => t.s34
  | 35 => t.s35 | 36 => t.s36 | 37 => t.s37 | 38 => t.s38 | 39 => t.s39
  | _ => .const 0#16

@[expose] def SymSpill40.set (t : SymSpill40) (k : Nat) (x : SExpr) : SymSpill40 :=
  match k with
  | 0 => { t with s0 := x } | 1 => { t with s1 := x } | 2 => { t with s2 := x } | 3 => { t with s3 := x }
  | 4 => { t with s4 := x } | 5 => { t with s5 := x } | 6 => { t with s6 := x } | 7 => { t with s7 := x }
  | 8 => { t with s8 := x } | 9 => { t with s9 := x } | 10 => { t with s10 := x } | 11 => { t with s11 := x }
  | 12 => { t with s12 := x } | 13 => { t with s13 := x } | 14 => { t with s14 := x } | 15 => { t with s15 := x }
  | 16 => { t with s16 := x } | 17 => { t with s17 := x } | 18 => { t with s18 := x } | 19 => { t with s19 := x }
  | 20 => { t with s20 := x } | 21 => { t with s21 := x } | 22 => { t with s22 := x } | 23 => { t with s23 := x }
  | 24 => { t with s24 := x } | 25 => { t with s25 := x } | 26 => { t with s26 := x } | 27 => { t with s27 := x }
  | 28 => { t with s28 := x } | 29 => { t with s29 := x } | 30 => { t with s30 := x } | 31 => { t with s31 := x }
  | 32 => { t with s32 := x } | 33 => { t with s33 := x } | 34 => { t with s34 := x } | 35 => { t with s35 := x }
  | 36 => { t with s36 := x } | 37 => { t with s37 := x } | 38 => { t with s38 := x } | 39 => { t with s39 := x }
  | _ => t

@[expose] def SymSpill40.ofFn (f : Nat → SExpr) : SymSpill40 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9,
   f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18, f 19,
   f 20, f 21, f 22, f 23, f 24, f 25, f 26, f 27, f 28, f 29,
   f 30, f 31, f 32, f 33, f 34, f 35, f 36, f 37, f 38, f 39⟩

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

@[expose] def SymVec32.ofFn (f : Nat → SExpr) : SymVec32 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7,
   f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15,
   f 16, f 17, f 18, f 19, f 20, f 21, f 22, f 23,
   f 24, f 25, f 26, f 27, f 28, f 29, f 30, f 31⟩

structure SymGprs where
  (g0 g1 g2 g3 g4 g5 g6 g7 : SymGpr)
  (g8 g9 g10 g11 g12 g13 g14 g15 : SymGpr)
  (g16 g17 g18 g19 g20 g21 g22 g23 : SymGpr)
  (g24 g25 g26 g27 g28 g29 g30 : SymGpr)
  deriving DecidableEq, Repr

@[expose] def SymGprs.get (t : SymGprs) : Nat → SymGpr
  | 0 => t.g0 | 1 => t.g1 | 2 => t.g2 | 3 => t.g3 | 4 => t.g4 | 5 => t.g5 | 6 => t.g6 | 7 => t.g7
  | 8 => t.g8 | 9 => t.g9 | 10 => t.g10 | 11 => t.g11 | 12 => t.g12 | 13 => t.g13 | 14 => t.g14 | 15 => t.g15
  | 16 => t.g16 | 17 => t.g17 | 18 => t.g18 | 19 => t.g19 | 20 => t.g20 | 21 => t.g21 | 22 => t.g22 | 23 => t.g23
  | 24 => t.g24 | 25 => t.g25 | 26 => t.g26 | 27 => t.g27 | 28 => t.g28 | 29 => t.g29 | 30 => t.g30
  | _ => .const64 0#64

@[expose] def SymGprs.set (t : SymGprs) (k : Nat) (x : SymGpr) : SymGprs :=
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

@[expose] def SymGprs.ofFn (f : Nat → SymGpr) : SymGprs :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7,
   f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15,
   f 16, f 17, f 18, f 19, f 20, f 21, f 22, f 23,
   f 24, f 25, f 26, f 27, f 28, f 29, f 30⟩

inductive PolyLoc where
  | spOff (off : Nat)
  | gpr (r : BitVec 5)
  deriving DecidableEq, Repr

structure SymCfg where
  spillOff : Nat
  spillLen : Nat
  polyLoc  : PolyLoc
  hasSrc   : Bool := false
  deriving DecidableEq, Repr

@[expose] def SymCfg.spPolyOff? (cfg : SymCfg) : Option Nat :=
  match cfg.polyLoc with
  | .spOff pOff => some pOff
  | .gpr _ => none

structure SymState where
  vregs : SymVRegs
  spill : SymSpill40
  poly  : SymVec32
  gprs  : SymGprs
  deriving DecidableEq, Repr

@[expose] def symInitState : SymState where
  vregs := SymVRegs.ofFn SExpr.vreg0
  spill := SymSpill40.ofFn SExpr.spill0
  poly  := SymVec32.ofFn SExpr.poly
  gprs  := SymGprs.ofFn (fun k => .gpr0 (BitVec.ofNat 5 k) 0#64)

/-! ## 2. Smart Constructors & Configurable Symbolic Stepper -/

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

@[expose] def fetchWordTree06 (j : Nat) : Option Instr :=
  match blkTree06.getQuad? j with
  | some (b0, b1, b2, b3) => Arm64.decode (b3 ++ b2 ++ b1 ++ b0)
  | none => none

@[expose] def stepSymInst (cfg : SymCfg) (inst : Instr) (st : SymState) : Option SymState :=
  match inst with
  | .ldrSimd .Q128 vt (.Offset .sp off) =>
      let o := off.toNat
      if cfg.spillLen ≤ 40 && cfg.spillOff ≤ o && o < cfg.spillOff + 16 * cfg.spillLen &&
          (o - cfg.spillOff) % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (st.spill.get ((o - cfg.spillOff) / 16)) }
      else match cfg.spPolyOff? with
        | some pOff =>
            if pOff ≤ o && o < pOff + 512 && (o - pOff) % 16 == 0 then
              some { st with vregs := st.vregs.set vt.toNat (st.poly.get ((o - pOff) / 16)) }
            else if cfg.hasSrc && 14432 ≤ o && o < 14944 && (o - 14432) % 16 == 0 then
              some { st with vregs := st.vregs.set vt.toNat (.src ((o - 14432) / 16)) }
            else none
        | none =>
            if cfg.hasSrc && 14432 ≤ o && o < 14944 && (o - 14432) % 16 == 0 then
              some { st with vregs := st.vregs.set vt.toNat (.src ((o - 14432) / 16)) }
            else none
  | .strSimd .Q128 vt (.Offset .sp off) =>
      let o := off.toNat
      let val := st.vregs.get vt.toNat
      if cfg.spillLen ≤ 40 && cfg.spillOff ≤ o && o < cfg.spillOff + 16 * cfg.spillLen &&
          (o - cfg.spillOff) % 16 == 0 then
        some { st with spill := st.spill.set ((o - cfg.spillOff) / 16) val }
      else match cfg.spPolyOff? with
        | some pOff =>
            if pOff ≤ o && o < pOff + 512 && (o - pOff) % 16 == 0 then
              some { st with poly := st.poly.set ((o - pOff) / 16) val }
            else none
        | none => none
  | .ldrSimd .Q128 vt (.Offset (.gpr rb) off) =>
      let o := off.toNat
      if rb != 31#5 && cfg.polyLoc == .gpr rb && st.gprs.get rb.toNat == .gpr0 rb 0#64 &&
          o < 512 && o % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (st.poly.get (o / 16)) }
      else none
  | .strSimd .Q128 vt (.Offset (.gpr rb) off) =>
      let o := off.toNat
      if rb != 31#5 && cfg.polyLoc == .gpr rb && st.gprs.get rb.toNat == .gpr0 rb 0#64 &&
          o < 512 && o % 16 == 0 then
        some { st with poly := st.poly.set (o / 16) (st.vregs.get vt.toNat) }
      else none
  | .ldpSimd .Q128 vt1 vt2 (.Offset (.gpr rb) off) =>
      let o := off.toNat
      if rb != 31#5 && cfg.polyLoc == .gpr rb && st.gprs.get rb.toNat == .gpr0 rb 0#64 &&
          o + 16 < 512 && o % 16 == 0 then
        let k := o / 16
        some { st with vregs := (st.vregs.set vt1.toNat (st.poly.get k)).set vt2.toNat (st.poly.get (k + 1)) }
      else none
  | .stpSimd .Q128 vt1 vt2 (.Offset (.gpr rb) off) =>
      let o := off.toNat
      if rb != 31#5 && cfg.polyLoc == .gpr rb && st.gprs.get rb.toNat == .gpr0 rb 0#64 &&
          o + 16 < 512 && o % 16 == 0 then
        let k := o / 16
        some { st with poly := (st.poly.set k (st.vregs.get vt1.toNat)).set (k + 1) (st.vregs.get vt2.toNat) }
      else none
  | .moveWide .W32 .MOVZ (.gpr rd) imm16 0 =>
      if rd != 31#5 then
        some { st with gprs := st.gprs.set rd.toNat (.const64 (imm16.zeroExtend 64)) }
      else none
  | .addSubImm .W64 .ADD (.gpr rd) .sp imm12 shift12 =>
      if rd != 31#5 then
        let off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
        some { st with gprs := st.gprs.set rd.toNat (.spAdd off64) }
      else none
  | .addSubImm .W64 .ADD (.gpr rd) (.gpr rn) imm12 shift12 =>
      if rd != 31#5 && rn != 31#5 then
        let off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
        match st.gprs.get rn.toNat with
        | .gpr0 r0 o0 => some { st with gprs := st.gprs.set rd.toNat (.gpr0 r0 (o0 + off64)) }
        | .spAdd o0 => some { st with gprs := st.gprs.set rd.toNat (.spAdd (o0 + off64)) }
        | .const64 v => some { st with gprs := st.gprs.set rd.toNat (.const64 (v + off64)) }
        | _ => none
      else none
  | .logicalShift .W64 .ORR (.gpr rd) .xzr .xzr .LSL 0 =>
      if rd != 31#5 then
        some { st with gprs := st.gprs.set rd.toNat (.const64 0#64) }
      else none
  | .logicalShift .W64 .ORR (.gpr rd) .xzr (.gpr rm) .LSL 0 =>
      if rd != 31#5 && rm != 31#5 then
        some { st with gprs := st.gprs.set rd.toNat (st.gprs.get rm.toNat) }
      else none
  | .addSubShift .W64 .ADD (.gpr rd) (.gpr rn) (.gpr rm) .LSL 0 =>
      if rd != 31#5 && rn != 31#5 && rm != 31#5 then
        match st.gprs.get rn.toNat, st.gprs.get rm.toNat with
        | .gpr0 r1 0#64, .gpr0 r2 0#64 =>
            some { st with gprs := st.gprs.set rd.toNat (.addGpr0 r1 r2) }
        | _, _ => none
      else none
  | .simdInsDup true false 2#5 1#4 rn rd =>
      if rn != 31#5 then
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
        some { st with vregs := st.vregs.set rd.toNat (smartMla (st.vregs.get rd.toNat) (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)) }
      else if !u && sz == 1#2 && opcode == 0b10110#5 then
        some { st with vregs := st.vregs.set rd.toNat (.sqdmulh (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)) }
      else none
  | .simdImmShift true op immh immb opcode rn rd =>
      if immh == 0#4 && opcode == 0b10000#5 then
        let c16 : BitVec 16 := (immb ++ rn).zeroExtend 16
        some { st with vregs := st.vregs.set rd.toNat (.const (if op then ~~~c16 else c16)) }
      else if immh == 0#4 && opcode == 0b10100#5 then
        let c16 : BitVec 16 := ((immb ++ rn).zeroExtend 16) <<< 8
        some { st with vregs := st.vregs.set rd.toNat (.const (if op then ~~~c16 else c16)) }
      else if !op && immh == 0b0011#4 && immb == 0b111#3 && opcode == 0b00000#5 then
        some { st with vregs := st.vregs.set rd.toNat (.sshr (st.vregs.get rn.toNat) 1) }
      else if !op && immh == 0b0010#4 && immb == 0b101#3 && opcode == 0b00000#5 then
        some { st with vregs := st.vregs.set rd.toNat (.sshr (st.vregs.get rn.toNat) 11) }
      else none
  | _ => none

@[expose] def runSymRange (cfg : SymCfg) : Nat → Nat → SymState → Option SymState
  | _, 0, st => some st
  | w, n + 1, st =>
      match fetchWordTree06 w with
      | some inst =>
          match stepSymInst cfg inst st with
          | some st' => runSymRange cfg (w + 1) n st'
          | none => none
      | none => none

theorem runSymRange_append {cfg : SymCfg} {m n : Nat} {w : Nat} {st0 st1 st2 : SymState}
    (h1 : runSymRange cfg w m st0 = some st1)
    (h2 : runSymRange cfg (w + m) n st1 = some st2) :
    runSymRange cfg w (m + n) st0 = some st2 := by
  induction m generalizing w st0 with
  | zero =>
    simp only [runSymRange, Option.some.injEq] at h1; subst h1
    simpa using h2
  | succ m ih =>
    rw [Nat.succ_add]
    unfold runSymRange at h1 ⊢
    cases hfw : fetchWordTree06 w with
    | none => simp [hfw] at h1
    | some inst =>
      simp only [hfw] at h1 ⊢
      cases hst : stepSymInst cfg inst st0 with
      | none => simp [hst] at h1
      | some st' =>
        simp only [hst] at h1 ⊢
        exact ih h1 (by simpa [show w + 1 + m = w + (m + 1) from by omega] using h2)

/-! ## 3. Concrete Environment, Evaluation, & Smart-Constructor Soundness -/

structure SymEnv where
  vreg0   : Nat → BitVec 128
  spill0  : Spill40
  poly0   : Vec32
  src0    : Vec32
  gpr0    : BitVec 5 → BitVec 64
  pstate0 : PState

@[expose] def evalSExpr (env : SymEnv) : SExpr → BitVec 128
  | .poly k => env.poly0.get k
  | .src k => env.src0.get k
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

@[expose] def SymSpill40.eval (env : SymEnv) (t : SymSpill40) : Spill40 :=
  Spill40.ofFn (fun k => evalSExpr env (t.get k))

@[expose] def SymVec32.eval (env : SymEnv) (t : SymVec32) : Vec32 :=
  Vec32.ofFn (fun k => evalSExpr env (t.get k))

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
        have hcomm : ∀ x y : BitVec 128, simdAdd8h x y = simdAdd8h y x := by
          intro x y; apply ext_lane16; intro i; simp [BitVec.add_comm]
        rw [hcomm (dup8x16 0x0400#16)]
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

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge

/-!
# `kyber_decapsulate` (`B06`): Symbolic-to-`Poly16` Equivalence Bridges

Kernel-decidable AST equivalence bridges (`poly_eq_lowerNtt5`, `poly_eq_lowerNttBinomial5_src`,
`poly_eq_barrett`, and `poly_eq_upperInvNtt16`) connecting symbolic `SymVec32` outputs of
`PolySym` to `Poly16` specifications across all 8 straight-line NEON slices in `B06`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16
  neonBarrettReduce16
  neonInvNttStage16
  neonMontgomeryMul16
  sqdmulh16
  zetasTimesMontgomeryR
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  ext_lane16
  lane16
  lane16_dup8x16
  lane16_pack8x16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_simdAdd8h
  lane16_simdMla8h
  lane16_simdMul8h
  lane16_simdSqdmulh8h
  lane16_simdSshr8h
  lane16_simdSub8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  zetaTableAt_eq_zetasTimesMontgomeryR
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (
  lane16_simdMontMul8h
  neonNttBinomialLayer7_16
  neonNttStage16
  neonPolyNtt16
  neonPolyNttBinomial16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt (lane16_simdBarrett8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem
  PolyMem
  Vec32
  polyVecNat
  vec32_ofFn_get
  vecRangeMem_congr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure (upperInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr
  SymEnv
  SymVec32
  evalSExpr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  symVec32_eval_get
)

/-! ## 1. Forward 5-Stage `NTT` Specification Seams (`lowerNtt5_16` & `lowerNttBinomial5_16`) -/

/-- Forward 5 Montgomery `NTT` stages (`len = 128, 64, 32, 16, 8`, `k = 1 .. 31`). -/
@[expose] def lowerNtt5_16 (p0 : Poly16) : Poly16 :=
  let (p, k) := neonNttStage16 128 1 p0
  let (p, k) := neonNttStage16 64 k p
  let (p, k) := neonNttStage16 32 k p
  let (p, k) := neonNttStage16 16 k p
  (neonNttStage16 8 k p).1

/-- Forward binomial layer 7 + 4 Montgomery `NTT` stages (`len = 64, 32, 16, 8`, `k = 2 .. 31`). -/
@[expose] def lowerNttBinomial5_16 (p0 : Poly16) : Poly16 :=
  let p1 := neonNttBinomialLayer7_16 p0
  let (p, k) := neonNttStage16 64 2 p1
  let (p, k) := neonNttStage16 32 k p
  let (p, k) := neonNttStage16 16 k p
  (neonNttStage16 8 k p).1

private theorem foldl_add1_snd {α : Type} (xs : List Nat) (g : α × Nat → Nat → α × Nat)
    (hg : ∀ x b, (g x b).2 = x.2 + 1) :
    ∀ (x0 : α × Nat), (xs.foldl g x0).2 = x0.2 + xs.length := by
  induction xs with
  | nil => intro x0; simp
  | cons _ rest ih =>
    intro x0; simp only [List.foldl_cons, List.length_cons]; rw [ih, hg]; omega

private theorem foldl_sub1_snd {α : Type} (xs : List Nat) (g : α × Nat → Nat → α × Nat)
    (hg : ∀ x b, (g x b).2 = x.2 - 1) :
    ∀ (x0 : α × Nat), (xs.foldl g x0).2 = x0.2 - xs.length := by
  induction xs with
  | nil => intro x0; simp
  | cons _ rest ih =>
    intro x0; simp only [List.foldl_cons, List.length_cons]; rw [ih, hg]; omega

theorem neonNttStage16_snd (len kInit : Nat) (p : Poly16) :
    (neonNttStage16 len kInit p).2 = kInit + 256 / (2 * len) := by
  dsimp only [neonNttStage16]
  rw [foldl_add1_snd _ _ (fun _ _ => rfl), List.length_range]

private theorem neonInvNttStage16_snd (len kInit : Nat) (bf : Bool) (p : Poly16) :
    (neonInvNttStage16 len kInit bf p).2 = kInit - 256 / (2 * len) := by
  dsimp only [neonInvNttStage16]
  rw [foldl_sub1_snd _ _ (fun _ _ => rfl), List.length_range]

theorem neonNttStage16_size (len kInit : Nat) (p : Poly16) :
    (neonNttStage16 len kInit p).1.size = p.size := by
  unfold neonNttStage16
  have hinner : ∀ (ls : List Nat) (f : Poly16 → Nat → Poly16) (hs : ∀ a o, (f a o).size = a.size)
      (a : Poly16), (ls.foldl f a).size = a.size := by
    intro ls f hs
    induction ls with
    | nil => intro a; rfl
    | cons _ rest ih => intro a; simp [List.foldl_cons, ih, hs]
  have houter : ∀ (ls : List Nat) (a : Poly16) (k : Nat),
      (ls.foldl
        (fun (cur, k) blk =>
          let start := blk * 2 * len
          let zeta := zetasTimesMontgomeryR.getD k 0#16
          let next := (List.range len).foldl
            (fun arr off =>
              let j := start + off
              let a := arr.getD j 0#16
              let b := arr.getD (j + len) 0#16
              let t := neonMontgomeryMul16 b zeta
              (arr.set! j (a + t)).set! (j + len) (a - t))
            cur
          (next, k + 1))
        (a, k)).1.size = a.size := by
    intro ls
    induction ls with
    | nil => intro a k; rfl
    | cons _ rest ih =>
      intro a k; simp only [List.foldl_cons]; rw [ih]
      exact hinner _ _ (fun arr _ => by simp [Array.set!]) a
  exact houter _ p kInit

theorem neonNttBinomialLayer7_16_size (p : Poly16) :
    (neonNttBinomialLayer7_16 p).size = p.size := by
  unfold neonNttBinomialLayer7_16
  have h : ∀ (ls : List Nat) (a : Poly16),
      (ls.foldl
        (fun arr j =>
          let x := arr.getD j 0#16
          let y := arr.getD (j + 128) 0#16
          let t := y * 0xf9c0#16
          (arr.set! j (x + t)).set! (j + 128) (x - t))
        a).size = a.size := by
    intro ls
    induction ls with
    | nil => intro a; rfl
    | cons _ rest ih => intro a; simp only [List.foldl_cons]; rw [ih]; simp [Array.set!]
  exact h _ p

@[simp] theorem lowerNtt5_16_size (p0 : Poly16) :
    (lowerNtt5_16 p0).size = p0.size := by
  unfold lowerNtt5_16; simp only [neonNttStage16_size]

@[simp] theorem lowerNttBinomial5_16_size (p0 : Poly16) :
    (lowerNttBinomial5_16 p0).size = p0.size := by
  unfold lowerNttBinomial5_16; simp only [neonNttStage16_size, neonNttBinomialLayer7_16_size]

theorem neonPolyNtt16_of_lower5 (p0 : Poly16) :
    let p5 := lowerNtt5_16 p0
    let (p6, _) := neonNttStage16 4 32 p5
    let (p7, _) := neonNttStage16 2 64 p6
    p7.map neonBarrettReduce16 = neonPolyNtt16 p0 := by
  dsimp only [lowerNtt5_16, neonPolyNtt16]
  have hk1 : (neonNttStage16 128 1 p0).2 = 2 := by rw [neonNttStage16_snd]
  have hk2 : (neonNttStage16 64 2 (neonNttStage16 128 1 p0).1).2 = 4 := by rw [neonNttStage16_snd]
  rw [hk1]
  have hk3 : (neonNttStage16 32 4 (neonNttStage16 64 2 (neonNttStage16 128 1 p0).1).1).2 = 8 := by
    rw [neonNttStage16_snd]
  rw [hk2]
  have hk4 : (neonNttStage16 16 8 (neonNttStage16 32 4 (neonNttStage16 64 2 (neonNttStage16 128 1 p0).1).1).1).2 = 16 := by
    rw [neonNttStage16_snd]
  rw [hk3]
  have hk5 : (neonNttStage16 8 16 (neonNttStage16 16 8 (neonNttStage16 32 4 (neonNttStage16 64 2 (neonNttStage16 128 1 p0).1).1).1).1).2 = 32 := by
    rw [neonNttStage16_snd]
  rw [hk4, hk5]
  have hk6 : (neonNttStage16 4 32 (neonNttStage16 8 16 (neonNttStage16 16 8 (neonNttStage16 32 4 (neonNttStage16 64 2 (neonNttStage16 128 1 p0).1).1).1).1).1).2 = 64 := by
    rw [neonNttStage16_snd]
  rw [hk6]

theorem neonPolyNttBinomial16_of_lower5 (p0 : Poly16) :
    let p5 := lowerNttBinomial5_16 p0
    let (p6, _) := neonNttStage16 4 32 p5
    let (p7, _) := neonNttStage16 2 64 p6
    p7.map neonBarrettReduce16 = neonPolyNttBinomial16 p0 := by
  dsimp only [lowerNttBinomial5_16, neonPolyNttBinomial16]
  set p1 := neonNttBinomialLayer7_16 p0
  have hk2 : (neonNttStage16 64 2 p1).2 = 4 := by rw [neonNttStage16_snd]
  have hk3 : (neonNttStage16 32 4 (neonNttStage16 64 2 p1).1).2 = 8 := by rw [neonNttStage16_snd]
  rw [hk2]
  have hk4 : (neonNttStage16 16 8 (neonNttStage16 32 4 (neonNttStage16 64 2 p1).1).1).2 = 16 := by
    rw [neonNttStage16_snd]
  rw [hk3]
  have hk5 : (neonNttStage16 8 16 (neonNttStage16 16 8 (neonNttStage16 32 4 (neonNttStage16 64 2 p1).1).1).1).2 = 32 := by
    rw [neonNttStage16_snd]
  rw [hk4, hk5]
  have hk6 : (neonNttStage16 4 32 (neonNttStage16 8 16 (neonNttStage16 16 8 (neonNttStage16 32 4 (neonNttStage16 64 2 p1).1).1).1).1).2 = 64 := by
    rw [neonNttStage16_snd]
  rw [hk6]

/-! ## 2. Per-Lane Symbolic Evaluation & Canonicalization -/

@[expose] def evalLane (f : Nat → BitVec 16) : SExpr → BitVec 16
  | .poly idx => f idx
  | .src _ | .spill0 _ | .vreg0 _ => 0#16
  | .const c => c
  | .add a b => evalLane f a + evalLane f b
  | .sub a b => evalLane f a - evalLane f b
  | .mul a b => evalLane f a * evalLane f b
  | .mla d a b => evalLane f d + evalLane f a * evalLane f b
  | .sqdmulh a b => sqdmulh16 (evalLane f a) (evalLane f b)
  | .sshr a sh => (evalLane f a).sshiftRight sh
  | .barrett a => neonBarrettReduce16 (evalLane f a)
  | .montmul a z => neonMontgomeryMul16 (evalLane f a) z

@[expose] def noSpillVreg (useSrc : Bool) : SExpr → Bool
  | .poly _ => !useSrc
  | .src _ => useSrc
  | .const _ => true
  | .spill0 _ | .vreg0 _ => false
  | .add a b | .sub a b | .mul a b | .sqdmulh a b => noSpillVreg useSrc a && noSpillVreg useSrc b
  | .mla d a b => noSpillVreg useSrc d && noSpillVreg useSrc a && noSpillVreg useSrc b
  | .sshr a _ | .barrett a | .montmul a _ => noSpillVreg useSrc a

@[expose] def shiftIdx (useSrc : Bool) (lane : Nat) : SExpr → SExpr
  | .poly k => if useSrc then .poly k else .poly (8 * k + lane)
  | .src k => if useSrc then .poly (8 * k + lane) else .src k
  | .spill0 k => .spill0 k
  | .vreg0 r => .vreg0 r
  | .const c => .const c
  | .add a b => .add (shiftIdx useSrc lane a) (shiftIdx useSrc lane b)
  | .sub a b => .sub (shiftIdx useSrc lane a) (shiftIdx useSrc lane b)
  | .mul a b => .mul (shiftIdx useSrc lane a) (shiftIdx useSrc lane b)
  | .mla d a b => .mla (shiftIdx useSrc lane d) (shiftIdx useSrc lane a) (shiftIdx useSrc lane b)
  | .sqdmulh a b => .sqdmulh (shiftIdx useSrc lane a) (shiftIdx useSrc lane b)
  | .sshr a sh => .sshr (shiftIdx useSrc lane a) sh
  | .barrett a => .barrett (shiftIdx useSrc lane a)
  | .montmul a z => .montmul (shiftIdx useSrc lane a) z

private theorem lane16_evalSExpr_eq (useSrc : Bool) (env : SymEnv) (i : Fin 8) :
    ∀ (e : SExpr), noSpillVreg useSrc e = true →
      lane16 (evalSExpr env e) i =
        evalLane
          (fun idx => lane16 ((if useSrc then env.src0 else env.poly0).get (idx / 8)) ⟨idx % 8, by omega⟩)
          (shiftIdx useSrc i.val e)
  | .poly k, h => by
    cases useSrc <;> simp [noSpillVreg] at h
    have hdiv : (8 * k + i.val) / 8 = k := by omega
    have hmod : (8 * k + i.val) % 8 = i.val := by omega
    simp [evalSExpr, shiftIdx, evalLane, hdiv, hmod]
  | .src k, h => by
    cases useSrc <;> simp [noSpillVreg] at h
    have hdiv : (8 * k + i.val) / 8 = k := by omega
    have hmod : (8 * k + i.val) % 8 = i.val := by omega
    simp [evalSExpr, shiftIdx, evalLane, hdiv, hmod]
  | .spill0 _, h => by simp [noSpillVreg] at h
  | .vreg0 _, h => by simp [noSpillVreg] at h
  | .const _, _ => by simp [evalSExpr, shiftIdx, evalLane, lane16_dup8x16]
  | .add a b, h => by
    simp only [noSpillVreg, Bool.and_eq_true] at h
    simp [evalSExpr, shiftIdx, evalLane, lane16_simdAdd8h,
      lane16_evalSExpr_eq useSrc env i a h.1, lane16_evalSExpr_eq useSrc env i b h.2]
  | .sub a b, h => by
    simp only [noSpillVreg, Bool.and_eq_true] at h
    simp [evalSExpr, shiftIdx, evalLane, lane16_simdSub8h,
      lane16_evalSExpr_eq useSrc env i a h.1, lane16_evalSExpr_eq useSrc env i b h.2]
  | .mul a b, h => by
    simp only [noSpillVreg, Bool.and_eq_true] at h
    simp [evalSExpr, shiftIdx, evalLane, lane16_simdMul8h,
      lane16_evalSExpr_eq useSrc env i a h.1, lane16_evalSExpr_eq useSrc env i b h.2]
  | .mla d a b, h => by
    simp only [noSpillVreg, Bool.and_eq_true] at h
    simp [evalSExpr, shiftIdx, evalLane, lane16_simdMla8h,
      lane16_evalSExpr_eq useSrc env i d h.1.1,
      lane16_evalSExpr_eq useSrc env i a h.1.2,
      lane16_evalSExpr_eq useSrc env i b h.2]
  | .sqdmulh a b, h => by
    simp only [noSpillVreg, Bool.and_eq_true] at h
    simp [evalSExpr, shiftIdx, evalLane, lane16_simdSqdmulh8h,
      lane16_evalSExpr_eq useSrc env i a h.1, lane16_evalSExpr_eq useSrc env i b h.2]
  | .sshr a sh, h => by
    simp [evalSExpr, shiftIdx, evalLane, lane16_simdSshr8h, lane16_evalSExpr_eq useSrc env i a h]
  | .barrett a, h => by
    simp [evalSExpr, shiftIdx, evalLane, lane16_simdBarrett8h, lane16_evalSExpr_eq useSrc env i a h]
  | .montmul a z, h => by
    simp [evalSExpr, shiftIdx, evalLane, lane16_simdMontMul8h, lane16_dup8x16,
      lane16_evalSExpr_eq useSrc env i a h]

@[expose] def cmpNat (x y : Nat) : Ordering :=
  if Nat.beq x y then .eq else if Nat.ble x y then .lt else .gt
@[expose] def ordThen (o1 o2 : Ordering) : Ordering :=
  match o1 with | .eq => o2 | o => o

@[expose] def SExpr.cmp : SExpr → SExpr → Ordering
  | .poly x, .poly y | .src x, .src y | .spill0 x, .spill0 y | .vreg0 x, .vreg0 y => cmpNat x y
  | .poly _, _ => .lt | _, .poly _ => .gt
  | .src _, _ => .lt | _, .src _ => .gt
  | .spill0 _, _ => .lt | _, .spill0 _ => .gt
  | .vreg0 _, _ => .lt | _, .vreg0 _ => .gt
  | .const x, .const y => cmpNat x.toNat y.toNat
  | .const _, _ => .lt | _, .const _ => .gt
  | .add a1 b1, .add a2 b2 | .sub a1 b1, .sub a2 b2
  | .mul a1 b1, .mul a2 b2 | .sqdmulh a1 b1, .sqdmulh a2 b2 =>
      ordThen (SExpr.cmp a1 a2) (SExpr.cmp b1 b2)
  | .add _ _, _ => .lt | _, .add _ _ => .gt
  | .sub _ _, _ => .lt | _, .sub _ _ => .gt
  | .mul _ _, _ => .lt | _, .mul _ _ => .gt
  | .mla d1 a1 b1, .mla d2 a2 b2 =>
      ordThen (ordThen (SExpr.cmp d1 d2) (SExpr.cmp a1 a2)) (SExpr.cmp b1 b2)
  | .mla _ _ _, _ => .lt | _, .mla _ _ _ => .gt
  | .sqdmulh _ _, _ => .lt | _, .sqdmulh _ _ => .gt
  | .sshr a1 s1, .sshr a2 s2 => ordThen (SExpr.cmp a1 a2) (cmpNat s1 s2)
  | .sshr _ _, _ => .lt | _, .sshr _ _ => .gt
  | .barrett a1, .barrett a2 => SExpr.cmp a1 a2
  | .barrett _, _ => .lt | _, .barrett _ => .gt
  | .montmul a1 z1, .montmul a2 z2 => ordThen (SExpr.cmp a1 a2) (cmpNat z1.toNat z2.toNat)

@[expose] def canonExpr : SExpr → SExpr
  | .add a b =>
      let a' := canonExpr a
      let b' := canonExpr b
      match SExpr.cmp a' b' with | .gt => .add b' a' | _ => .add a' b'
  | .mul a b =>
      let a' := canonExpr a
      let b' := canonExpr b
      match SExpr.cmp a' b' with | .gt => .mul b' a' | _ => .mul a' b'
  | .sub a b => .sub (canonExpr a) (canonExpr b)
  | .mla d a b => .mla (canonExpr d) (canonExpr a) (canonExpr b)
  | .sqdmulh a b => .sqdmulh (canonExpr a) (canonExpr b)
  | .sshr a sh => .sshr (canonExpr a) sh
  | .barrett a => .barrett (canonExpr a)
  | .montmul a z => .montmul (canonExpr a) z
  | e => e

private theorem evalLane_canonExpr (f : Nat → BitVec 16) :
    ∀ e : SExpr, evalLane f (canonExpr e) = evalLane f e
  | .poly _ | .src _ | .spill0 _ | .vreg0 _ | .const _ => rfl
  | .add a b => by
    simp only [canonExpr]
    cases SExpr.cmp (canonExpr a) (canonExpr b) <;>
      simp [evalLane, evalLane_canonExpr f a, evalLane_canonExpr f b, BitVec.add_comm]
  | .mul a b => by
    simp only [canonExpr]
    cases SExpr.cmp (canonExpr a) (canonExpr b) <;>
      simp [evalLane, evalLane_canonExpr f a, evalLane_canonExpr f b, BitVec.mul_comm]
  | .sub a b => by simp [canonExpr, evalLane, evalLane_canonExpr f a, evalLane_canonExpr f b]
  | .mla d a b => by
    simp [canonExpr, evalLane, evalLane_canonExpr f d, evalLane_canonExpr f a, evalLane_canonExpr f b]
  | .sqdmulh a b => by simp [canonExpr, evalLane, evalLane_canonExpr f a, evalLane_canonExpr f b]
  | .sshr a sh => by simp [canonExpr, evalLane, evalLane_canonExpr f a]
  | .barrett a => by simp [canonExpr, evalLane, evalLane_canonExpr f a]
  | .montmul a z => by simp [canonExpr, evalLane, evalLane_canonExpr f a]

/-! ## 3. Symbolic Stage Reference Lists & Generic `Poly32Mem` Bridges -/

@[expose] def listGet : List SExpr → Nat → SExpr
  | [], _ => .const 0#16
  | x :: _, 0 => x
  | _ :: xs, n + 1 => listGet xs n

@[expose] def listSet : List SExpr → Nat → SExpr → List SExpr
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSet xs n v

private theorem listSet_eq_set : ∀ (ls : List SExpr) (j : Nat) (v : SExpr),
    listSet ls j v = ls.set j v
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | x :: xs, n + 1, v => congrArg (x :: ·) (listSet_eq_set xs n v)

@[expose] def symFwdStage (len kInit : Nat) (f : List SExpr) : List SExpr × Nat :=
  let nBlocks := 256 / (2 * len)
  (List.range nBlocks).foldl
    (fun (cur, k) blk =>
      let start := blk * 2 * len
      let zeta := zetaTableAt k
      let next := (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let a := listGet arr j
          let b := listGet arr (j + len)
          let t := SExpr.montmul b zeta
          listSet (listSet arr j (.add a t)) (j + len) (.sub a t))
        cur
      (next, k + 1))
    (f, kInit)

@[expose] def symBinomialStage (f : List SExpr) : List SExpr :=
  (List.range 128).foldl
    (fun arr j =>
      let a := listGet arr j
      let b := listGet arr (j + 128)
      let t := SExpr.mul b (.const 0xf9c0#16)
      listSet (listSet arr j (.add a t)) (j + 128) (.sub a t))
    f

@[expose] def symInvStage (len kInit : Nat) (barrettFirst : Bool) (f : List SExpr) :
    List SExpr × Nat :=
  let nBlocks := 256 / (2 * len)
  (List.range nBlocks).foldl
    (fun (cur, k) blk =>
      let start := blk * 2 * len
      let zeta := zetaTableAt k
      let next := (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let a := listGet arr j
          let b := listGet arr (j + len)
          let sum := SExpr.add a b
          let a' := if barrettFirst then SExpr.barrett sum else sum
          let b' := SExpr.montmul (SExpr.sub b a) zeta
          listSet (listSet arr j a') (j + len) b')
        cur
      (next, k - 1))
    (f, kInit)

@[expose] def symInitPolyList : List SExpr := (List.range 256).map SExpr.poly

@[expose] def symLowerNtt5 : List SExpr :=
  let (p, k) := symFwdStage 128 1 symInitPolyList
  let (p, k) := symFwdStage 64 k p
  let (p, k) := symFwdStage 32 k p
  let (p, k) := symFwdStage 16 k p
  (symFwdStage 8 k p).1

@[expose] def symLowerNttBinomial5 : List SExpr :=
  let p1 := symBinomialStage symInitPolyList
  let (p, k) := symFwdStage 64 2 p1
  let (p, k) := symFwdStage 32 k p
  let (p, k) := symFwdStage 16 k p
  (symFwdStage 8 k p).1

@[expose] def symBarrett : List SExpr :=
  symInitPolyList.map SExpr.barrett

@[expose] def symUpperInvNtt : List SExpr :=
  let (p, k) := symInvStage 8 31 false symInitPolyList
  let (p, k) := symInvStage 16 k true p
  let (p, k) := symInvStage 32 k true p
  let (p, k) := symInvStage 64 k true p
  let (p, _) := symInvStage 128 k true p
  p.map SExpr.barrett

private theorem toArray_map_getD_const0 (f : Nat → BitVec 16) :
    ∀ (ls : List SExpr) (j : Nat),
      (ls.map (evalLane f)).toArray.getD j 0#16 = evalLane f (listGet ls j)
  | [], _ => by simp [Array.getD, listGet, evalLane]
  | _ :: _, 0 => by simp [Array.getD, listGet]
  | _ :: xs, n + 1 => by
    simpa [Array.getD, listGet, Nat.succ_lt_succ_iff] using toArray_map_getD_const0 f xs n

private theorem toArray_map_listSet (f : Nat → BitVec 16) (ls : List SExpr) (j : Nat) (e : SExpr) :
    ((listSet ls j e).map (evalLane f)).toArray =
      (ls.map (evalLane f)).toArray.set! j (evalLane f e) := by
  rw [listSet_eq_set, List.map_set]; simp [Array.set!]

private theorem init_map_evalLane {p0 : Poly16} (hp0 : p0.size = 256)
    (f : Nat → BitVec 16) (hf : ∀ idx < 256, f idx = p0.getD idx 0#16) :
    (symInitPolyList.map (evalLane f)).toArray = p0 := by
  apply Array.ext
  · simp [symInitPolyList, hp0]
  · intro idx h1 h2
    simp only [symInitPolyList, List.size_toArray, List.length_map, List.length_range] at h1
    simp only [symInitPolyList, List.getElem_toArray, List.getElem_map, List.getElem_range, evalLane]
    rw [hf idx h1]; simp [Array.getD, h2]

private theorem symFwdStage_map_evalLane (f : Nat → BitVec 16) (len kInit : Nat)
    (hkEnd : kInit + 256 / (2 * len) ≤ 128) (ls0 : List SExpr) :
    (((symFwdStage len kInit ls0).1.map (evalLane f)).toArray,
      (symFwdStage len kInit ls0).2) =
      neonNttStage16 len kInit (ls0.map (evalLane f)).toArray := by
  dsimp only [symFwdStage, neonNttStage16]
  have hinner : ∀ (offs : List Nat) (k : Nat) (_hk : k < 128) (start : Nat) (cur : List SExpr),
      ((offs.foldl
        (fun a off =>
          let j := start + off
          let x := listGet a j
          let y := listGet a (j + len)
          let t := SExpr.montmul y (zetaTableAt k)
          listSet (listSet a j (.add x t)) (j + len) (.sub x t))
        cur).map (evalLane f)).toArray =
      offs.foldl
        (fun a off =>
          let j := start + off
          let x := a.getD j 0#16
          let y := a.getD (j + len) 0#16
          let t := neonMontgomeryMul16 y (zetasTimesMontgomeryR.getD k 0#16)
          (a.set! j (x + t)).set! (j + len) (x - t))
        (cur.map (evalLane f)).toArray := by
    intro offs k hk start
    induction offs with
    | nil => intro cur; rfl
    | cons _ rest ih =>
      intro cur; simp only [List.foldl_cons]; rw [ih]; congr 1
      rw [toArray_map_listSet, toArray_map_listSet]
      simp only [evalLane, ← toArray_map_getD_const0 f, ← zetaTableAt_eq_zetasTimesMontgomeryR hk]
  have houter : ∀ (blks : List Nat) (cur : List SExpr) (k : Nat), k + blks.length ≤ 128 →
      let r := blks.foldl
        (fun (c, k') blk =>
          let start := blk * 2 * len
          let next := (List.range len).foldl
            (fun a off =>
              let j := start + off
              let x := listGet a j
              let y := listGet a (j + len)
              let t := SExpr.montmul y (zetaTableAt k')
              listSet (listSet a j (.add x t)) (j + len) (.sub x t))
            c
          (next, k' + 1))
        (cur, k)
      ((r.1.map (evalLane f)).toArray, r.2) =
      blks.foldl
        (fun (c, k') blk =>
          let start := blk * 2 * len
          let next := (List.range len).foldl
            (fun a off =>
              let j := start + off
              let x := a.getD j 0#16
              let y := a.getD (j + len) 0#16
              let t := neonMontgomeryMul16 y (zetasTimesMontgomeryR.getD k' 0#16)
              (a.set! j (x + t)).set! (j + len) (x - t))
            c
          (next, k' + 1))
        ((cur.map (evalLane f)).toArray, k) := by
    intro blks
    induction blks with
    | nil => intro cur k _; rfl
    | cons _ rest ih =>
      intro cur k hk; simp only [List.length_cons] at hk
      dsimp only [List.foldl_cons]
      rw [ih _ (k + 1) (by omega), hinner _ k (by omega) _ cur]
  exact houter (List.range (256 / (2 * len))) ls0 kInit (by simpa using hkEnd)

private theorem symBinomialStage_map_evalLane (f : Nat → BitVec 16) (ls0 : List SExpr) :
    ((symBinomialStage ls0).map (evalLane f)).toArray =
      neonNttBinomialLayer7_16 (ls0.map (evalLane f)).toArray := by
  dsimp only [symBinomialStage, neonNttBinomialLayer7_16]
  have h : ∀ (js : List Nat) (cur : List SExpr),
      ((js.foldl
        (fun arr j =>
          let x := listGet arr j
          let y := listGet arr (j + 128)
          let t := SExpr.mul y (.const 0xf9c0#16)
          listSet (listSet arr j (.add x t)) (j + 128) (.sub x t))
        cur).map (evalLane f)).toArray =
      js.foldl
        (fun arr j =>
          let x := arr.getD j 0#16
          let y := arr.getD (j + 128) 0#16
          let t := y * 0xf9c0#16
          (arr.set! j (x + t)).set! (j + 128) (x - t))
        (cur.map (evalLane f)).toArray := by
    intro js
    induction js with
    | nil => intro cur; rfl
    | cons _ rest ih =>
      intro cur; simp only [List.foldl_cons]; rw [ih]; congr 1
      rw [toArray_map_listSet, toArray_map_listSet]
      simp only [evalLane, ← toArray_map_getD_const0 f]
  exact h _ ls0

private theorem symInvStage_map_evalLane (f : Nat → BitVec 16) (len kInit : Nat)
    (hkInit : kInit < 128) (bf : Bool) (ls0 : List SExpr) :
    (((symInvStage len kInit bf ls0).1.map (evalLane f)).toArray,
      (symInvStage len kInit bf ls0).2) =
      neonInvNttStage16 len kInit bf (ls0.map (evalLane f)).toArray := by
  dsimp only [symInvStage, neonInvNttStage16]
  have hinner : ∀ (offs : List Nat) (k : Nat) (_hk : k < 128) (start : Nat) (cur : List SExpr),
      ((offs.foldl
        (fun a off =>
          let j := start + off
          let x := listGet a j
          let y := listGet a (j + len)
          let sum := SExpr.add x y
          let a' := if bf then SExpr.barrett sum else sum
          let b' := SExpr.montmul (SExpr.sub y x) (zetaTableAt k)
          listSet (listSet a j a') (j + len) b')
        cur).map (evalLane f)).toArray =
      offs.foldl
        (fun a off =>
          let j := start + off
          let x := a.getD j 0#16
          let y := a.getD (j + len) 0#16
          let sum := x + y
          let a' := if bf then neonBarrettReduce16 sum else sum
          let b' := neonMontgomeryMul16 (y - x) (zetasTimesMontgomeryR.getD k 0#16)
          (a.set! j a').set! (j + len) b')
        (cur.map (evalLane f)).toArray := by
    intro offs k hk start
    induction offs with
    | nil => intro cur; rfl
    | cons _ rest ih =>
      intro cur; simp only [List.foldl_cons]; rw [ih]; congr 1
      rw [toArray_map_listSet, toArray_map_listSet]
      cases bf <;>
        simp only [Bool.false_eq_true, ↓reduceIte, evalLane,
          ← toArray_map_getD_const0 f, ← zetaTableAt_eq_zetasTimesMontgomeryR hk]
  have houter : ∀ (blks : List Nat) (cur : List SExpr) (k : Nat), k < 128 →
      let r := blks.foldl
        (fun (c, k') blk =>
          let start := blk * 2 * len
          let next := (List.range len).foldl
            (fun a off =>
              let j := start + off
              let x := listGet a j
              let y := listGet a (j + len)
              let sum := SExpr.add x y
              let a' := if bf then SExpr.barrett sum else sum
              let b' := SExpr.montmul (SExpr.sub y x) (zetaTableAt k')
              listSet (listSet a j a') (j + len) b')
            c
          (next, k' - 1))
        (cur, k)
      ((r.1.map (evalLane f)).toArray, r.2) =
      blks.foldl
        (fun (c, k') blk =>
          let start := blk * 2 * len
          let next := (List.range len).foldl
            (fun a off =>
              let j := start + off
              let x := a.getD j 0#16
              let y := a.getD (j + len) 0#16
              let sum := x + y
              let a' := if bf then neonBarrettReduce16 sum else sum
              let b' := neonMontgomeryMul16 (y - x) (zetasTimesMontgomeryR.getD k' 0#16)
              (a.set! j a').set! (j + len) b')
            c
          (next, k' - 1))
        ((cur.map (evalLane f)).toArray, k) := by
    intro blks
    induction blks with
    | nil => intro cur k _; rfl
    | cons _ rest ih =>
      intro cur k hk; dsimp only [List.foldl_cons]
      rw [ih _ (k - 1) (by omega), hinner _ k hk _ cur]
  exact houter (List.range (256 / (2 * len))) ls0 kInit hkInit

@[expose] def polyNoSpillVreg (useSrc : Bool) (t : SymVec32) : Bool :=
  (List.range 32).all (fun k => noSpillVreg useSrc (t.get k))

@[expose] def polyAstEq (useSrc : Bool) (t : SymVec32) (ref : List SExpr) : Bool :=
  (List.range 32).all (fun k =>
    (List.range 8).all (fun i =>
      SExpr.beq (canonExpr (shiftIdx useSrc i (t.get k)))
        (canonExpr (listGet ref (8 * k + i)))))

private theorem poly_eq_of_ref (useSrc : Bool) (ptr : BitVec 64) {p0 pOut : Poly16}
    (env : SymEnv) (t : SymVec32) (ref : List SExpr)
    (hin : (if useSrc then env.src0 else env.poly0) = Vec32.ofFn (polyVecNat p0))
    (hns : polyNoSpillVreg useSrc t = true)
    (hast : polyAstEq useSrc t ref = true)
    (href : ∀ f : Nat → BitVec 16, (∀ idx < 256, f idx = p0.getD idx 0#16) →
      (ref.map (evalLane f)).toArray = pOut) :
    Poly32Mem ptr (t.eval env) = PolyMem ptr (polyVecNat pOut) := by
  unfold Poly32Mem PolyMem
  apply vecRangeMem_congr
  intro k hk
  rw [symVec32_eval_get env t k hk]
  apply ext_lane16
  intro i
  have hns_k : noSpillVreg useSrc (t.get k) = true :=
    List.all_eq_true.mp hns k (List.mem_range.mpr hk)
  rw [lane16_evalSExpr_eq useSrc env i (t.get k) hns_k]
  let f : Nat → BitVec 16 := fun idx =>
    lane16 ((if useSrc then env.src0 else env.poly0).get (idx / 8)) ⟨idx % 8, by omega⟩
  change evalLane f (shiftIdx useSrc i.val (t.get k)) = _
  have hast_ki : canonExpr (shiftIdx useSrc i.val (t.get k)) =
      canonExpr (listGet ref (8 * k + i.val)) :=
    SExpr.beq_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp hast k (List.mem_range.mpr hk))
      i.val (List.mem_range.mpr i.isLt))
  rw [← evalLane_canonExpr f, hast_ki, evalLane_canonExpr f, ← toArray_map_getD_const0 f]
  have hf : ∀ idx < 256, f idx = p0.getD idx 0#16 := by
    intro idx hidx
    dsimp only [f]
    rw [hin, vec32_ofFn_get _ _ (by omega), polyVecNat, lane16_pack8x16]
    dsimp only; congr 1; omega
  rw [href f hf, polyVecNat, lane16_pack8x16]

theorem poly_eq_lowerNtt5 (ptr : BitVec 64) {p0 : Poly16} (hp0 : p0.size = 256)
    (env : SymEnv) (hpoly0 : env.poly0 = Vec32.ofFn (polyVecNat p0))
    (t : SymVec32) (hns : polyNoSpillVreg false t = true)
    (hast : polyAstEq false t symLowerNtt5 = true) :
    Poly32Mem ptr (t.eval env) = PolyMem ptr (polyVecNat (lowerNtt5_16 p0)) := by
  refine poly_eq_of_ref false ptr env t symLowerNtt5 hpoly0 hns hast (fun f hf => ?_)
  have hinit := init_map_evalLane hp0 f hf
  unfold symLowerNtt5 lowerNtt5_16; dsimp only
  generalize hs1 : symFwdStage 128 1 symInitPolyList = r1
  generalize hn1 : neonNttStage16 128 1 p0 = q1
  have m1 := symFwdStage_map_evalLane f 128 1 (by omega) symInitPolyList
  rw [hs1, hinit, hn1] at m1; rcases q1 with ⟨q1a, q1k⟩; obtain ⟨m1a, m1k⟩ := Prod.mk.inj m1
  have hq1 : q1k = 2 := by
    have hq := congrArg Prod.snd hn1; dsimp only at hq; rw [← hq, neonNttStage16_snd]
  have hk1 : r1.2 + 256 / (2 * 64) ≤ 128 := by rw [m1k, hq1]; omega
  generalize hs2 : symFwdStage 64 r1.2 r1.1 = r2
  generalize hn2 : neonNttStage16 64 q1k q1a = q2
  have m2 := symFwdStage_map_evalLane f 64 r1.2 hk1 r1.1
  rw [hs2, m1a, m1k, hn2] at m2; rcases q2 with ⟨q2a, q2k⟩; obtain ⟨m2a, m2k⟩ := Prod.mk.inj m2
  have hq2 : q2k = 4 := by
    have hq := congrArg Prod.snd hn2; dsimp only at hq; rw [← hq, neonNttStage16_snd, hq1]
  have hk2 : r2.2 + 256 / (2 * 32) ≤ 128 := by rw [m2k, hq2]; omega
  generalize hs3 : symFwdStage 32 r2.2 r2.1 = r3
  generalize hn3 : neonNttStage16 32 q2k q2a = q3
  have m3 := symFwdStage_map_evalLane f 32 r2.2 hk2 r2.1
  rw [hs3, m2a, m2k, hn3] at m3; rcases q3 with ⟨q3a, q3k⟩; obtain ⟨m3a, m3k⟩ := Prod.mk.inj m3
  have hq3 : q3k = 8 := by
    have hq := congrArg Prod.snd hn3; dsimp only at hq; rw [← hq, neonNttStage16_snd, hq2]
  have hk3 : r3.2 + 256 / (2 * 16) ≤ 128 := by rw [m3k, hq3]; omega
  generalize hs4 : symFwdStage 16 r3.2 r3.1 = r4
  generalize hn4 : neonNttStage16 16 q3k q3a = q4
  have m4 := symFwdStage_map_evalLane f 16 r3.2 hk3 r3.1
  rw [hs4, m3a, m3k, hn4] at m4; rcases q4 with ⟨q4a, q4k⟩; obtain ⟨m4a, m4k⟩ := Prod.mk.inj m4
  have hq4 : q4k = 16 := by
    have hq := congrArg Prod.snd hn4; dsimp only at hq; rw [← hq, neonNttStage16_snd, hq3]
  have hk4 : r4.2 + 256 / (2 * 8) ≤ 128 := by rw [m4k, hq4]; omega
  generalize hs5 : symFwdStage 8 r4.2 r4.1 = r5
  generalize hn5 : neonNttStage16 8 q4k q4a = q5
  have m5 := symFwdStage_map_evalLane f 8 r4.2 hk4 r4.1
  rw [hs5, m4a, m4k, hn5] at m5; exact (Prod.mk.inj m5).1

theorem poly_eq_lowerNttBinomial5_src (ptr : BitVec 64) {p0 : Poly16} (hp0 : p0.size = 256)
    (env : SymEnv) (hsrc0 : env.src0 = Vec32.ofFn (polyVecNat p0))
    (t : SymVec32) (hns : polyNoSpillVreg true t = true)
    (hast : polyAstEq true t symLowerNttBinomial5 = true) :
    Poly32Mem ptr (t.eval env) = PolyMem ptr (polyVecNat (lowerNttBinomial5_16 p0)) := by
  refine poly_eq_of_ref true ptr env t symLowerNttBinomial5 hsrc0 hns hast (fun f hf => ?_)
  have hinit := init_map_evalLane hp0 f hf
  unfold symLowerNttBinomial5 lowerNttBinomial5_16; dsimp only
  have mb := symBinomialStage_map_evalLane f symInitPolyList
  rw [hinit] at mb
  set s1 := symBinomialStage symInitPolyList
  set p1 := neonNttBinomialLayer7_16 p0
  generalize hs2 : symFwdStage 64 2 s1 = r2
  generalize hn2 : neonNttStage16 64 2 p1 = q2
  have m2 := symFwdStage_map_evalLane f 64 2 (by omega) s1
  rw [hs2, mb, hn2] at m2; rcases q2 with ⟨q2a, q2k⟩; obtain ⟨m2a, m2k⟩ := Prod.mk.inj m2
  have hq2 : q2k = 4 := by
    have hq := congrArg Prod.snd hn2; dsimp only at hq; rw [← hq, neonNttStage16_snd]
  have hk2 : r2.2 + 256 / (2 * 32) ≤ 128 := by rw [m2k, hq2]; omega
  generalize hs3 : symFwdStage 32 r2.2 r2.1 = r3
  generalize hn3 : neonNttStage16 32 q2k q2a = q3
  have m3 := symFwdStage_map_evalLane f 32 r2.2 hk2 r2.1
  rw [hs3, m2a, m2k, hn3] at m3; rcases q3 with ⟨q3a, q3k⟩; obtain ⟨m3a, m3k⟩ := Prod.mk.inj m3
  have hq3 : q3k = 8 := by
    have hq := congrArg Prod.snd hn3; dsimp only at hq; rw [← hq, neonNttStage16_snd, hq2]
  have hk3 : r3.2 + 256 / (2 * 16) ≤ 128 := by rw [m3k, hq3]; omega
  generalize hs4 : symFwdStage 16 r3.2 r3.1 = r4
  generalize hn4 : neonNttStage16 16 q3k q3a = q4
  have m4 := symFwdStage_map_evalLane f 16 r3.2 hk3 r3.1
  rw [hs4, m3a, m3k, hn4] at m4; rcases q4 with ⟨q4a, q4k⟩; obtain ⟨m4a, m4k⟩ := Prod.mk.inj m4
  have hq4 : q4k = 16 := by
    have hq := congrArg Prod.snd hn4; dsimp only at hq; rw [← hq, neonNttStage16_snd, hq3]
  have hk4 : r4.2 + 256 / (2 * 8) ≤ 128 := by rw [m4k, hq4]; omega
  generalize hs5 : symFwdStage 8 r4.2 r4.1 = r5
  generalize hn5 : neonNttStage16 8 q4k q4a = q5
  have m5 := symFwdStage_map_evalLane f 8 r4.2 hk4 r4.1
  rw [hs5, m4a, m4k, hn5] at m5; exact (Prod.mk.inj m5).1

theorem poly_eq_barrett (ptr : BitVec 64) {p0 : Poly16} (hp0 : p0.size = 256)
    (env : SymEnv) (hpoly0 : env.poly0 = Vec32.ofFn (polyVecNat p0))
    (t : SymVec32) (hns : polyNoSpillVreg false t = true)
    (hast : polyAstEq false t symBarrett = true) :
    Poly32Mem ptr (t.eval env) = PolyMem ptr (polyVecNat (p0.map neonBarrettReduce16)) := by
  refine poly_eq_of_ref false ptr env t symBarrett hpoly0 hns hast (fun f hf => ?_)
  have hinit : symInitPolyList.map (evalLane f) = p0.toList :=
    congrArg Array.toList (init_map_evalLane hp0 f hf)
  unfold symBarrett
  rw [List.map_map, show (evalLane f ∘ SExpr.barrett) = (neonBarrettReduce16 ∘ evalLane f) from rfl,
    ← List.map_map, hinit, List.map_toArray, Array.toArray_toList]

theorem poly_eq_upperInvNtt16 (ptr : BitVec 64) {p2 : Poly16} (hp2 : p2.size = 256)
    (env : SymEnv) (hpoly0 : env.poly0 = Vec32.ofFn (polyVecNat p2))
    (t : SymVec32) (hns : polyNoSpillVreg false t = true)
    (hast : polyAstEq false t symUpperInvNtt = true) :
    Poly32Mem ptr (t.eval env) = PolyMem ptr (polyVecNat (upperInvNtt16 p2)) := by
  refine poly_eq_of_ref false ptr env t symUpperInvNtt hpoly0 hns hast (fun f hf => ?_)
  have hinit := init_map_evalLane hp2 f hf
  unfold symUpperInvNtt upperInvNtt16; dsimp only
  generalize hs8 : symInvStage 8 31 false symInitPolyList = r8
  generalize hn8 : neonInvNttStage16 8 31 false p2 = q8
  have m8 := symInvStage_map_evalLane f 8 31 (by omega) false symInitPolyList
  rw [hs8, hinit, hn8] at m8; rcases q8 with ⟨q8a, q8k⟩; obtain ⟨m8a, m8k⟩ := Prod.mk.inj m8
  have hk8 : r8.2 < 128 := by
    have hq := congrArg Prod.snd hn8; dsimp only at hq; rw [m8k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs16 : symInvStage 16 r8.2 true r8.1 = r16
  generalize hn16 : neonInvNttStage16 16 q8k true q8a = q16
  have m16 := symInvStage_map_evalLane f 16 r8.2 hk8 true r8.1
  rw [hs16, m8a, m8k, hn16] at m16; rcases q16 with ⟨q16a, q16k⟩; obtain ⟨m16a, m16k⟩ := Prod.mk.inj m16
  have hk16 : r16.2 < 128 := by
    have hq := congrArg Prod.snd hn16; dsimp only at hq; rw [m16k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs32 : symInvStage 32 r16.2 true r16.1 = r32
  generalize hn32 : neonInvNttStage16 32 q16k true q16a = q32
  have m32 := symInvStage_map_evalLane f 32 r16.2 hk16 true r16.1
  rw [hs32, m16a, m16k, hn32] at m32; rcases q32 with ⟨q32a, q32k⟩; obtain ⟨m32a, m32k⟩ := Prod.mk.inj m32
  have hk32 : r32.2 < 128 := by
    have hq := congrArg Prod.snd hn32; dsimp only at hq; rw [m32k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs64 : symInvStage 64 r32.2 true r32.1 = r64
  generalize hn64 : neonInvNttStage16 64 q32k true q32a = q64
  have m64 := symInvStage_map_evalLane f 64 r32.2 hk32 true r32.1
  rw [hs64, m32a, m32k, hn64] at m64; rcases q64 with ⟨q64a, q64k⟩; obtain ⟨m64a, m64k⟩ := Prod.mk.inj m64
  have hk64 : r64.2 < 128 := by
    have hq := congrArg Prod.snd hn64; dsimp only at hq; rw [m64k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs128 : symInvStage 128 r64.2 true r64.1 = r128
  generalize hn128 : neonInvNttStage16 128 q64k true q64a = q128
  have m128 := symInvStage_map_evalLane f 128 r64.2 hk64 true r64.1
  rw [hs128, m64a, m64k, hn128] at m128; rcases q128 with ⟨q128a, _⟩; obtain ⟨m128a, _⟩ := Prod.mk.inj m128
  have hm128l : r128.1.map (evalLane f) = q128a.toList := congrArg Array.toList m128a
  rw [List.map_map, show (evalLane f ∘ SExpr.barrett) = (neonBarrettReduce16 ∘ evalLane f) from rfl,
    ← List.map_map, hm128l, List.map_toArray, Array.toArray_toList]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure

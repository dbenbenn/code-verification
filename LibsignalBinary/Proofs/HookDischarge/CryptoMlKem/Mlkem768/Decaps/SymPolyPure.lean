/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt

/-!
# `decapsulate_compressed_key` (`B04`) — Pure Stage Seams & Symbolic AST Models (`SymPolyPure`)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
  (zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
  (Poly16 zetasTimesMontgomeryR sqdmulh16 neonBarrettReduce16 neonMontgomeryMul16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
  (lane16 lane16_dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
  (lane16_simdAdd8h lane16_simdSub8h lane16_simdMul8h lane16_simdMla8h
   lane16_simdSqdmulh8h lane16_simdSshr8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
  (lane16_simdMontMul8h neonNttStage16 neonNttBinomialLayer7_16 neonPolyNtt16
   neonPolyNttBinomial16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
  (lane16_simdBarrett8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
  (SExpr SymVec32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval
  (SymEnv evalSExpr)

/-! ## 1. Upper 5-Stage Forward `NTT` Seams (`upperFwdNtt16` & `upperFwdNttBinomial16`) -/

@[expose] def upperFwdNtt16 (f : Poly16) : Poly16 :=
  let (f, k) := neonNttStage16 128 1 f
  let (f, k) := neonNttStage16 64 k f
  let (f, k) := neonNttStage16 32 k f
  let (f, k) := neonNttStage16 16 k f
  (neonNttStage16 8 k f).1

@[expose] def upperFwdNttBinomial16 (f : Poly16) : Poly16 :=
  let f := neonNttBinomialLayer7_16 f
  let (f, k) := neonNttStage16 64 2 f
  let (f, k) := neonNttStage16 32 k f
  let (f, k) := neonNttStage16 16 k f
  (neonNttStage16 8 k f).1

private theorem foldl_add1_snd {α : Type} (xs : List Nat) (g : α × Nat → Nat → α × Nat)
    (hg : ∀ x b, (g x b).2 = x.2 + 1) :
    ∀ (x0 : α × Nat), (xs.foldl g x0).2 = x0.2 + xs.length := by
  induction xs with
  | nil => intro x0; simp
  | cons _ rest ih => intro x0; simp only [List.foldl_cons, List.length_cons]; rw [ih, hg]; omega

theorem neonNttStage16_snd (len kInit : Nat) (p : Poly16) :
    (neonNttStage16 len kInit p).2 = kInit + 256 / (2 * len) := by
  dsimp only [neonNttStage16]
  rw [foldl_add1_snd _ _ (fun _ _ => rfl), List.length_range]

theorem neonNttStage16_size (len kInit : Nat) (p : Poly16) :
    (neonNttStage16 len kInit p).1.size = p.size := by
  unfold neonNttStage16
  have hinner : ∀ (ls : List Nat) (g : Poly16 → Nat → Poly16)
      (hg : ∀ a o, (g a o).size = a.size) (a : Poly16), (ls.foldl g a).size = a.size := by
    intro ls g hg; induction ls with
    | nil => intro a; rfl
    | cons _ rest ih => intro a; simp [List.foldl_cons, ih, hg]
  have houter : ∀ (ls : List Nat) (a : Poly16) (k : Nat),
      (ls.foldl
        (fun (cur, k) blk =>
          let start := blk * 2 * len
          let zeta := zetasTimesMontgomeryR.getD k 0#16
          let next := (List.range len).foldl
            (fun arr off =>
              let j := start + off
              let x := arr.getD j 0#16
              let y := arr.getD (j + len) 0#16
              let t := neonMontgomeryMul16 y zeta
              (arr.set! j (x + t)).set! (j + len) (x - t))
            cur
          (next, k + 1))
        (a, k)).1.size = a.size := by
    intro ls; induction ls with
    | nil => intro a k; rfl
    | cons _ rest ih =>
      intro a k; simp only [List.foldl_cons]; rw [ih]
      exact hinner _ _ (fun arr _ => by simp [Array.set!]) a
  exact houter _ p kInit

theorem neonNttBinomialLayer7_16_size (p : Poly16) :
    (neonNttBinomialLayer7_16 p).size = p.size := by
  unfold neonNttBinomialLayer7_16
  have hinner : ∀ (ls : List Nat) (a : Poly16),
      (ls.foldl
        (fun arr j =>
          let x := arr.getD j 0#16
          let y := arr.getD (j + 128) 0#16
          let t := y * 0xf9c0#16
          (arr.set! j (x + t)).set! (j + 128) (x - t))
        a).size = a.size := by
    intro ls; induction ls with
    | nil => intro a; rfl
    | cons _ rest ih =>
      intro a; simp only [List.foldl_cons]; rw [ih]; simp [Array.set!]
  exact hinner _ p

@[simp] theorem upperFwdNtt16_size (p : Poly16) : (upperFwdNtt16 p).size = p.size := by
  unfold upperFwdNtt16; simp only [neonNttStage16_size]

@[simp] theorem upperFwdNttBinomial16_size (p : Poly16) :
    (upperFwdNttBinomial16 p).size = p.size := by
  unfold upperFwdNttBinomial16; simp only [neonNttStage16_size, neonNttBinomialLayer7_16_size]

theorem neonPolyNtt16_of_upper (f : Poly16) :
    let (p, k) := neonNttStage16 4 32 (upperFwdNtt16 f)
    let (p, _) := neonNttStage16 2 k p
    p.map neonBarrettReduce16 = neonPolyNtt16 f := by
  dsimp only [neonPolyNtt16, upperFwdNtt16]
  have hk1 : (neonNttStage16 128 1 f).2 = 2 := by rw [neonNttStage16_snd]
  rw [hk1]
  generalize (neonNttStage16 128 1 f).1 = f1
  have hk2 : (neonNttStage16 64 2 f1).2 = 4 := by rw [neonNttStage16_snd]
  rw [hk2]
  generalize (neonNttStage16 64 2 f1).1 = f2
  have hk3 : (neonNttStage16 32 4 f2).2 = 8 := by rw [neonNttStage16_snd]
  rw [hk3]
  generalize (neonNttStage16 32 4 f2).1 = f3
  have hk4 : (neonNttStage16 16 8 f3).2 = 16 := by rw [neonNttStage16_snd]
  rw [hk4]
  generalize (neonNttStage16 16 8 f3).1 = f4
  have hk5 : (neonNttStage16 8 16 f4).2 = 32 := by rw [neonNttStage16_snd]
  rw [hk5]

theorem neonPolyNttBinomial16_of_upper (f : Poly16) :
    let (p, k) := neonNttStage16 4 32 (upperFwdNttBinomial16 f)
    let (p, _) := neonNttStage16 2 k p
    p.map neonBarrettReduce16 = neonPolyNttBinomial16 f := by
  dsimp only [neonPolyNttBinomial16, upperFwdNttBinomial16]
  generalize neonNttBinomialLayer7_16 f = f1
  have hk2 : (neonNttStage16 64 2 f1).2 = 4 := by rw [neonNttStage16_snd]
  rw [hk2]
  generalize (neonNttStage16 64 2 f1).1 = f2
  have hk3 : (neonNttStage16 32 4 f2).2 = 8 := by rw [neonNttStage16_snd]
  rw [hk3]
  generalize (neonNttStage16 32 4 f2).1 = f3
  have hk4 : (neonNttStage16 16 8 f3).2 = 16 := by rw [neonNttStage16_snd]
  rw [hk4]
  generalize (neonNttStage16 16 8 f3).1 = f4
  have hk5 : (neonNttStage16 8 16 f4).2 = 32 := by rw [neonNttStage16_snd]
  rw [hk5]

/-! ## 2. Per-Lane Symbolic Evaluation & Canonicalization -/

@[expose] def evalLane (fPoly fIn : Nat → BitVec 16) : SExpr → BitVec 16
  | .poly idx => fPoly idx
  | .inPoly idx => fIn idx
  | .spill13_0 _ | .spill6_0 _ | .spill21_0 _ | .vreg0 _ => 0#16
  | .const c => c
  | .add a b => evalLane fPoly fIn a + evalLane fPoly fIn b
  | .sub a b => evalLane fPoly fIn a - evalLane fPoly fIn b
  | .mul a b => evalLane fPoly fIn a * evalLane fPoly fIn b
  | .mla d a b => evalLane fPoly fIn d + evalLane fPoly fIn a * evalLane fPoly fIn b
  | .sqdmulh a b => sqdmulh16 (evalLane fPoly fIn a) (evalLane fPoly fIn b)
  | .sshr a sh => (evalLane fPoly fIn a).sshiftRight sh
  | .barrett a => neonBarrettReduce16 (evalLane fPoly fIn a)
  | .montmul a z => neonMontgomeryMul16 (evalLane fPoly fIn a) z

@[expose] def noSpillVreg : SExpr → Bool
  | .poly _ | .inPoly _ | .const _ => true
  | .spill13_0 _ | .spill6_0 _ | .spill21_0 _ | .vreg0 _ => false
  | .add a b | .sub a b | .mul a b | .sqdmulh a b => noSpillVreg a && noSpillVreg b
  | .mla d a b => noSpillVreg d && noSpillVreg a && noSpillVreg b
  | .sshr a _ | .barrett a | .montmul a _ => noSpillVreg a

@[expose] def shiftLeafIdx (lane : Nat) : SExpr → SExpr
  | .poly k => .poly (8 * k + lane)
  | .inPoly k => .inPoly (8 * k + lane)
  | .add a b => .add (shiftLeafIdx lane a) (shiftLeafIdx lane b)
  | .sub a b => .sub (shiftLeafIdx lane a) (shiftLeafIdx lane b)
  | .mul a b => .mul (shiftLeafIdx lane a) (shiftLeafIdx lane b)
  | .mla d a b => .mla (shiftLeafIdx lane d) (shiftLeafIdx lane a) (shiftLeafIdx lane b)
  | .sqdmulh a b => .sqdmulh (shiftLeafIdx lane a) (shiftLeafIdx lane b)
  | .sshr a sh => .sshr (shiftLeafIdx lane a) sh
  | .barrett a => .barrett (shiftLeafIdx lane a)
  | .montmul a z => .montmul (shiftLeafIdx lane a) z
  | e => e

theorem lane16_evalSExpr_eq (env : SymEnv) (i : Fin 8) :
    ∀ e : SExpr, noSpillVreg e = true →
      lane16 (evalSExpr env e) i =
        evalLane
          (fun idx => lane16 (env.poly0.get (idx / 8)) ⟨idx % 8, by omega⟩)
          (fun idx => lane16 (env.inPoly0.get (idx / 8)) ⟨idx % 8, by omega⟩)
          (shiftLeafIdx i.val e)
  | .poly k, _ => by
    have hdiv : (8 * k + i.val) / 8 = k := by omega
    have hmod : (8 * k + i.val) % 8 = i.val := by omega
    simp only [evalSExpr, shiftLeafIdx, evalLane, hdiv]
    congr 1; apply Fin.ext; exact hmod.symm
  | .inPoly k, _ => by
    have hdiv : (8 * k + i.val) / 8 = k := by omega
    have hmod : (8 * k + i.val) % 8 = i.val := by omega
    simp only [evalSExpr, shiftLeafIdx, evalLane, hdiv]
    congr 1; apply Fin.ext; exact hmod.symm
  | .spill13_0 _, h | .spill6_0 _, h | .spill21_0 _, h | .vreg0 _, h => by
    simp [noSpillVreg] at h
  | .const c, _ => by simp [evalSExpr, shiftLeafIdx, evalLane, lane16_dup8x16]
  | .add a b, h => by
    simp only [noSpillVreg, Bool.and_eq_true] at h
    simp [evalSExpr, shiftLeafIdx, evalLane, lane16_simdAdd8h,
      lane16_evalSExpr_eq env i a h.1, lane16_evalSExpr_eq env i b h.2]
  | .sub a b, h => by
    simp only [noSpillVreg, Bool.and_eq_true] at h
    simp [evalSExpr, shiftLeafIdx, evalLane, lane16_simdSub8h,
      lane16_evalSExpr_eq env i a h.1, lane16_evalSExpr_eq env i b h.2]
  | .mul a b, h => by
    simp only [noSpillVreg, Bool.and_eq_true] at h
    simp [evalSExpr, shiftLeafIdx, evalLane, lane16_simdMul8h,
      lane16_evalSExpr_eq env i a h.1, lane16_evalSExpr_eq env i b h.2]
  | .mla d a b, h => by
    simp only [noSpillVreg, Bool.and_eq_true] at h
    simp [evalSExpr, shiftLeafIdx, evalLane, lane16_simdMla8h,
      lane16_evalSExpr_eq env i d h.1.1, lane16_evalSExpr_eq env i a h.1.2,
      lane16_evalSExpr_eq env i b h.2]
  | .sqdmulh a b, h => by
    simp only [noSpillVreg, Bool.and_eq_true] at h
    simp [evalSExpr, shiftLeafIdx, evalLane, lane16_simdSqdmulh8h,
      lane16_evalSExpr_eq env i a h.1, lane16_evalSExpr_eq env i b h.2]
  | .sshr a sh, h => by
    simp [evalSExpr, shiftLeafIdx, evalLane, lane16_simdSshr8h, lane16_evalSExpr_eq env i a h]
  | .barrett a, h => by
    simp [evalSExpr, shiftLeafIdx, evalLane, lane16_simdBarrett8h, lane16_evalSExpr_eq env i a h]
  | .montmul a z, h => by
    simp [evalSExpr, shiftLeafIdx, evalLane, lane16_simdMontMul8h, lane16_dup8x16,
      lane16_evalSExpr_eq env i a h]

@[expose] def cmpNat (x y : Nat) : Ordering :=
  if Nat.beq x y then .eq else if Nat.ble x y then .lt else .gt

@[expose] def ordThen (o1 o2 : Ordering) : Ordering := match o1 with | .eq => o2 | o => o

@[expose] def SExpr.cmp : SExpr → SExpr → Ordering
  | .poly x, .poly y | .inPoly x, .inPoly y
  | .spill13_0 x, .spill13_0 y | .spill6_0 x, .spill6_0 y
  | .spill21_0 x, .spill21_0 y | .vreg0 x, .vreg0 y => cmpNat x y
  | .poly _, _ => .lt | _, .poly _ => .gt
  | .inPoly _, _ => .lt | _, .inPoly _ => .gt
  | .spill13_0 _, _ => .lt | _, .spill13_0 _ => .gt
  | .spill6_0 _, _ => .lt | _, .spill6_0 _ => .gt
  | .spill21_0 _, _ => .lt | _, .spill21_0 _ => .gt
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

@[expose] def canonAddMul : SExpr → SExpr
  | .add a b =>
    let a' := canonAddMul a
    let b' := canonAddMul b
    match SExpr.cmp a' b' with | .gt => .add b' a' | _ => .add a' b'
  | .sub a b => .sub (canonAddMul a) (canonAddMul b)
  | .mul a b =>
    let a' := canonAddMul a
    let b' := canonAddMul b
    match SExpr.cmp a' b' with | .gt => .mul b' a' | _ => .mul a' b'
  | .mla d a b => .mla (canonAddMul d) (canonAddMul a) (canonAddMul b)
  | .sqdmulh a b => .sqdmulh (canonAddMul a) (canonAddMul b)
  | .sshr a sh => .sshr (canonAddMul a) sh
  | .barrett a => .barrett (canonAddMul a)
  | .montmul a z => .montmul (canonAddMul a) z
  | e => e

theorem evalLane_canonAddMul (fp fi : Nat → BitVec 16) :
    ∀ e : SExpr, evalLane fp fi (canonAddMul e) = evalLane fp fi e
  | .poly _ | .inPoly _ | .spill13_0 _ | .spill6_0 _ | .spill21_0 _ | .vreg0 _ | .const _ => rfl
  | .add a b => by
    simp only [canonAddMul]
    cases SExpr.cmp (canonAddMul a) (canonAddMul b) <;>
      simp [evalLane, evalLane_canonAddMul fp fi a, evalLane_canonAddMul fp fi b, BitVec.add_comm]
  | .sub a b => by simp [canonAddMul, evalLane, evalLane_canonAddMul fp fi a, evalLane_canonAddMul fp fi b]
  | .mul a b => by
    simp only [canonAddMul]
    cases SExpr.cmp (canonAddMul a) (canonAddMul b) <;>
      simp [evalLane, evalLane_canonAddMul fp fi a, evalLane_canonAddMul fp fi b, BitVec.mul_comm]
  | .mla d a b => by
    simp [canonAddMul, evalLane, evalLane_canonAddMul fp fi d,
      evalLane_canonAddMul fp fi a, evalLane_canonAddMul fp fi b]
  | .sqdmulh a b => by
    simp [canonAddMul, evalLane, evalLane_canonAddMul fp fi a, evalLane_canonAddMul fp fi b]
  | .sshr a sh => by simp [canonAddMul, evalLane, evalLane_canonAddMul fp fi a]
  | .barrett a => by simp [canonAddMul, evalLane, evalLane_canonAddMul fp fi a]
  | .montmul a z => by simp [canonAddMul, evalLane, evalLane_canonAddMul fp fi a]

/-! ## 3. Symbolic Stage Models & `Poly32Mem` Bridges -/

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

theorem toArray_map_getD_const0 (fp fi : Nat → BitVec 16) :
    ∀ (ls : List SExpr) (j : Nat),
      (ls.map (evalLane fp fi)).toArray.getD j 0#16 = evalLane fp fi (listGet ls j)
  | [], _ => by simp [Array.getD, listGet, evalLane]
  | _ :: _, 0 => by simp [Array.getD, listGet]
  | _ :: xs, n + 1 => by
    simpa [Array.getD, listGet, Nat.succ_lt_succ_iff] using toArray_map_getD_const0 fp fi xs n

theorem toArray_map_listSet (fp fi : Nat → BitVec 16) (ls : List SExpr) (j : Nat) (e : SExpr) :
    ((listSet ls j e).map (evalLane fp fi)).toArray =
      (ls.map (evalLane fp fi)).toArray.set! j (evalLane fp fi e) := by
  rw [listSet_eq_set, List.map_set]; simp [Array.set!]

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

@[expose] def symBinomialLayer7 (f : List SExpr) : List SExpr :=
  (List.range 128).foldl
    (fun arr j =>
      let a := listGet arr j
      let b := listGet arr (j + 128)
      let t := SExpr.mul b (.const 0xf9c0#16)
      listSet (listSet arr j (.add a t)) (j + 128) (.sub a t))
    f

@[expose] def symInvStage (len kInit : Nat) (bf : Bool) (f : List SExpr) : List SExpr × Nat :=
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
          let a' := if bf then SExpr.barrett sum else sum
          let b' := SExpr.montmul (SExpr.sub b a) zeta
          listSet (listSet arr j a') (j + len) b')
        cur
      (next, k - 1))
    (f, kInit)

@[expose] def symUpperFwdNtt : List SExpr :=
  let init := (List.range 256).map SExpr.poly
  let (p, k) := symFwdStage 128 1 init
  let (p, k) := symFwdStage 64 k p
  let (p, k) := symFwdStage 32 k p
  let (p, k) := symFwdStage 16 k p
  (symFwdStage 8 k p).1

@[expose] def symUpperFwdNttBinomial : List SExpr :=
  let init := (List.range 256).map SExpr.inPoly
  let p := symBinomialLayer7 init
  let (p, k) := symFwdStage 64 2 p
  let (p, k) := symFwdStage 32 k p
  let (p, k) := symFwdStage 16 k p
  (symFwdStage 8 k p).1

@[expose] def symBarrettMap : List SExpr :=
  (List.range 256).map (fun idx => SExpr.barrett (.poly idx))

@[expose] def symUpperInvNtt : List SExpr :=
  let init := (List.range 256).map SExpr.poly
  let (p, k) := symInvStage 8 31 false init
  let (p, k) := symInvStage 16 k true p
  let (p, k) := symInvStage 32 k true p
  let (p, k) := symInvStage 64 k true p
  let (p, _) := symInvStage 128 k true p
  p.map SExpr.barrett

@[expose] def checkNoSpillVreg (v : SymVec32) : Bool :=
  (List.range 32).all fun k => noSpillVreg (v.get k)

@[expose] def checkAstEq (v : SymVec32) (target : List SExpr) : Bool :=
  (List.range 32).all fun k =>
    (List.range 8).all fun i =>
      SExpr.beq (canonAddMul (shiftLeafIdx i (v.get k))) (canonAddMul (listGet target (8 * k + i)))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4c -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt

/-!
# `encapsulate2` (`B20`) — Segment 4 Pure Symbolic-to-`upperInvNtt16` Equivalence (`Seg4Pure`)

Defines `upperInvNtt16` (the 5 upper `InvNTT` stages `8, 16, 32, 64, 128` starting at `k = 31`
followed by `Array.map neonBarrettReduce16`), proves `upperInvNtt16_of_lower`, and bridges the 32
symbolic output vectors in `symState4c.poly` to `polyVecNat (upperInvNtt16 p2)`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure

open Arm64 ProofLib SepProp
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
  (zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
  (zetaTableAt_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
  (Poly16 zetasTimesMontgomeryR sqdmulh16 neonBarrettReduce16 neonMontgomeryMul16
   neonInvNttStage16 neonInvNttMontgomery16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
  (lane16 ext_lane16 lane16_pack8x16 lane16_dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
  (lane16_simdAdd8h lane16_simdSub8h lane16_simdMul8h lane16_simdMla8h
   lane16_simdSqdmulh8h lane16_simdSshr8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
  (lane16_simdMontMul8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
  (lane16_simdBarrett8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (PolyMem Poly32Mem Vec32 polyVecNat vecRangeMem_congr vec32_ofFn_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
  (SExpr SymEnv evalSExpr symVec32_eval_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4c
  (symState4c)

/-! ## 1. Upper 5-Stage `InvNTT` + `Barrett` Specification Seam -/

/-- Upper 5 stages (`len = 8, 16, 32, 64, 128`, starting at `k = 31`) plus final Barrett map. -/
@[expose] def upperInvNtt16 (p2 : Poly16) : Poly16 :=
  let (p, k) := neonInvNttStage16 8 31 false p2
  let (p, k) := neonInvNttStage16 16 k true p
  let (p, k) := neonInvNttStage16 32 k true p
  let (p, k) := neonInvNttStage16 64 k true p
  let (p, _) := neonInvNttStage16 128 k true p
  p.map neonBarrettReduce16

private theorem foldl_sub1_snd {α : Type} (xs : List Nat) (g : α × Nat → Nat → α × Nat)
    (hg : ∀ x b, (g x b).2 = x.2 - 1) :
    ∀ (x0 : α × Nat), (xs.foldl g x0).2 = x0.2 - xs.length := by
  induction xs with
  | nil => intro x0; simp
  | cons _ rest ih =>
    intro x0
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, hg]; omega

private theorem neonInvNttStage16_snd (len kInit : Nat) (bf : Bool) (p : Poly16) :
    (neonInvNttStage16 len kInit bf p).2 = kInit - 256 / (2 * len) := by
  dsimp only [neonInvNttStage16]
  rw [foldl_sub1_snd _ _ (fun _ _ => rfl), List.length_range]

private theorem neonInvNttStage16_size (len kInit : Nat) (bf : Bool) (p : Poly16) :
    (neonInvNttStage16 len kInit bf p).1.size = p.size := by
  unfold neonInvNttStage16
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
              let sum := a + b
              let a' := if bf then neonBarrettReduce16 sum else sum
              let b' := neonMontgomeryMul16 (b - a) zeta
              (arr.set! j a').set! (j + len) b')
            cur
          (next, k - 1))
        (a, k)).1.size = a.size := by
    intro ls
    induction ls with
    | nil => intro a k; rfl
    | cons _ rest ih =>
      intro a k
      simp only [List.foldl_cons]
      rw [ih]
      exact hinner _ _ (fun arr _ => by simp [Array.set!]) a
  exact houter _ p kInit

@[simp] theorem upperInvNtt16_size (p2 : Poly16) :
    (upperInvNtt16 p2).size = p2.size := by
  unfold upperInvNtt16
  simp only [Array.size_map, neonInvNttStage16_size]

theorem upperInvNtt16_of_lower (dot : Poly16) :
    let s1 := neonInvNttStage16 2 127 true dot
    let s2 := neonInvNttStage16 4 s1.2 false s1.1
    upperInvNtt16 s2.1 = neonInvNttMontgomery16 dot := by
  dsimp only [neonInvNttMontgomery16, upperInvNtt16]
  have hk1 : (neonInvNttStage16 2 127 true dot).2 = 63 := by
    rw [neonInvNttStage16_snd]
  have hk2 : (neonInvNttStage16 4 63 false (neonInvNttStage16 2 127 true dot).1).2 = 31 := by
    rw [neonInvNttStage16_snd]
  rw [hk1, hk2]

/-! ## 2. Per-Lane Symbolic Equivalence with `upperInvNtt16` -/

@[expose] def evalLane (f : Nat → BitVec 16) : SExpr → BitVec 16
  | .poly idx => f idx
  | .spill0 _ | .vreg0 _ => 0#16
  | .const c => c
  | .add a b => evalLane f a + evalLane f b
  | .sub a b => evalLane f a - evalLane f b
  | .mul a b => evalLane f a * evalLane f b
  | .mla d a b => evalLane f d + evalLane f a * evalLane f b
  | .sqdmulh a b => sqdmulh16 (evalLane f a) (evalLane f b)
  | .sshr a sh => (evalLane f a).sshiftRight sh
  | .barrett a => neonBarrettReduce16 (evalLane f a)
  | .montmul a z => neonMontgomeryMul16 (evalLane f a) z

@[expose] def noSpillVreg : SExpr → Bool
  | .poly _ | .const _ => true
  | .spill0 _ | .vreg0 _ => false
  | .add a b | .sub a b | .mul a b | .sqdmulh a b => noSpillVreg a && noSpillVreg b
  | .mla d a b => noSpillVreg d && noSpillVreg a && noSpillVreg b
  | .sshr a _ | .barrett a | .montmul a _ => noSpillVreg a

@[expose] def shiftPolyIdx (lane : Nat) : SExpr → SExpr
  | .poly k => .poly (8 * k + lane)
  | .spill0 k => .spill0 k
  | .vreg0 r => .vreg0 r
  | .const c => .const c
  | .add a b => .add (shiftPolyIdx lane a) (shiftPolyIdx lane b)
  | .sub a b => .sub (shiftPolyIdx lane a) (shiftPolyIdx lane b)
  | .mul a b => .mul (shiftPolyIdx lane a) (shiftPolyIdx lane b)
  | .mla d a b => .mla (shiftPolyIdx lane d) (shiftPolyIdx lane a) (shiftPolyIdx lane b)
  | .sqdmulh a b => .sqdmulh (shiftPolyIdx lane a) (shiftPolyIdx lane b)
  | .sshr a sh => .sshr (shiftPolyIdx lane a) sh
  | .barrett a => .barrett (shiftPolyIdx lane a)
  | .montmul a z => .montmul (shiftPolyIdx lane a) z

private theorem lane16_evalSExpr_eq (env : SymEnv) (i : Fin 8) :
    ∀ e : SExpr, noSpillVreg e = true →
      lane16 (evalSExpr env e) i =
        evalLane (fun idx => lane16 (env.poly0.get (idx / 8)) ⟨idx % 8, by omega⟩)
          (shiftPolyIdx i.val e)
  | .poly k, _ => by
    have hdiv : (8 * k + i.val) / 8 = k := by omega
    have hmod : (8 * k + i.val) % 8 = i.val := by omega
    simp only [evalSExpr, shiftPolyIdx, evalLane, hdiv]
    congr 1; apply Fin.ext; exact hmod.symm
  | .spill0 _, h | .vreg0 _, h => by simp [noSpillVreg] at h
  | .const c, _ => by simp [evalSExpr, shiftPolyIdx, evalLane, lane16_dup8x16]
  | .add a b, h => by simp only [noSpillVreg, Bool.and_eq_true] at h; simp [evalSExpr, shiftPolyIdx, evalLane, lane16_simdAdd8h, lane16_evalSExpr_eq env i a h.1, lane16_evalSExpr_eq env i b h.2]
  | .sub a b, h => by simp only [noSpillVreg, Bool.and_eq_true] at h; simp [evalSExpr, shiftPolyIdx, evalLane, lane16_simdSub8h, lane16_evalSExpr_eq env i a h.1, lane16_evalSExpr_eq env i b h.2]
  | .mul a b, h => by simp only [noSpillVreg, Bool.and_eq_true] at h; simp [evalSExpr, shiftPolyIdx, evalLane, lane16_simdMul8h, lane16_evalSExpr_eq env i a h.1, lane16_evalSExpr_eq env i b h.2]
  | .mla d a b, h => by simp only [noSpillVreg, Bool.and_eq_true] at h; simp [evalSExpr, shiftPolyIdx, evalLane, lane16_simdMla8h, lane16_evalSExpr_eq env i d h.1.1, lane16_evalSExpr_eq env i a h.1.2, lane16_evalSExpr_eq env i b h.2]
  | .sqdmulh a b, h => by simp only [noSpillVreg, Bool.and_eq_true] at h; simp [evalSExpr, shiftPolyIdx, evalLane, lane16_simdSqdmulh8h, lane16_evalSExpr_eq env i a h.1, lane16_evalSExpr_eq env i b h.2]
  | .sshr a sh, h => by simp [evalSExpr, shiftPolyIdx, evalLane, lane16_simdSshr8h, lane16_evalSExpr_eq env i a h]
  | .barrett a, h => by simp [evalSExpr, shiftPolyIdx, evalLane, lane16_simdBarrett8h, lane16_evalSExpr_eq env i a h]
  | .montmul a z, h => by simp [evalSExpr, shiftPolyIdx, evalLane, lane16_simdMontMul8h, lane16_dup8x16, lane16_evalSExpr_eq env i a h]

@[expose] def cmpNat (x y : Nat) : Ordering := if Nat.beq x y then .eq else if Nat.ble x y then .lt else .gt
@[expose] def ordThen (o1 o2 : Ordering) : Ordering := match o1 with | .eq => o2 | o => o

@[expose] def SExpr.cmp : SExpr → SExpr → Ordering
  | .poly x, .poly y | .spill0 x, .spill0 y | .vreg0 x, .vreg0 y => cmpNat x y
  | .poly _, _ => .lt | _, .poly _ => .gt
  | .spill0 _, _ => .lt | _, .spill0 _ => .gt
  | .vreg0 _, _ => .lt | _, .vreg0 _ => .gt
  | .const x, .const y => cmpNat x.toNat y.toNat
  | .const _, _ => .lt | _, .const _ => .gt
  | .add a1 b1, .add a2 b2 | .sub a1 b1, .sub a2 b2
  | .mul a1 b1, .mul a2 b2 | .sqdmulh a1 b1, .sqdmulh a2 b2 => ordThen (SExpr.cmp a1 a2) (SExpr.cmp b1 b2)
  | .add _ _, _ => .lt | _, .add _ _ => .gt
  | .sub _ _, _ => .lt | _, .sub _ _ => .gt
  | .mul _ _, _ => .lt | _, .mul _ _ => .gt
  | .mla d1 a1 b1, .mla d2 a2 b2 => ordThen (ordThen (SExpr.cmp d1 d2) (SExpr.cmp a1 a2)) (SExpr.cmp b1 b2)
  | .mla _ _ _, _ => .lt | _, .mla _ _ _ => .gt
  | .sqdmulh _ _, _ => .lt | _, .sqdmulh _ _ => .gt
  | .sshr a1 s1, .sshr a2 s2 => ordThen (SExpr.cmp a1 a2) (cmpNat s1 s2)
  | .sshr _ _, _ => .lt | _, .sshr _ _ => .gt
  | .barrett a1, .barrett a2 => SExpr.cmp a1 a2
  | .barrett _, _ => .lt | _, .barrett _ => .gt
  | .montmul a1 z1, .montmul a2 z2 => ordThen (SExpr.cmp a1 a2) (cmpNat z1.toNat z2.toNat)

@[expose] def canonAdd : SExpr → SExpr
  | .add a b =>
    let a' := canonAdd a
    let b' := canonAdd b
    match SExpr.cmp a' b' with
    | .gt => .add b' a'
    | _ => .add a' b'
  | .sub a b => .sub (canonAdd a) (canonAdd b)
  | .mul a b => .mul (canonAdd a) (canonAdd b)
  | .mla d a b => .mla (canonAdd d) (canonAdd a) (canonAdd b)
  | .sqdmulh a b => .sqdmulh (canonAdd a) (canonAdd b)
  | .sshr a sh => .sshr (canonAdd a) sh
  | .barrett a => .barrett (canonAdd a)
  | .montmul a z => .montmul (canonAdd a) z
  | e => e

private theorem evalLane_canonAdd (f : Nat → BitVec 16) :
    ∀ e : SExpr, evalLane f (canonAdd e) = evalLane f e
  | .poly _ | .spill0 _ | .vreg0 _ | .const _ => rfl
  | .add a b => by
    simp only [canonAdd]
    cases SExpr.cmp (canonAdd a) (canonAdd b) <;>
      simp [evalLane, evalLane_canonAdd f a, evalLane_canonAdd f b, BitVec.add_comm]
  | .sub a b => by simp [canonAdd, evalLane, evalLane_canonAdd f a, evalLane_canonAdd f b]
  | .mul a b => by simp [canonAdd, evalLane, evalLane_canonAdd f a, evalLane_canonAdd f b]
  | .mla d a b => by
    simp [canonAdd, evalLane, evalLane_canonAdd f d, evalLane_canonAdd f a, evalLane_canonAdd f b]
  | .sqdmulh a b => by simp [canonAdd, evalLane, evalLane_canonAdd f a, evalLane_canonAdd f b]
  | .sshr a sh => by simp [canonAdd, evalLane, evalLane_canonAdd f a]
  | .barrett a => by simp [canonAdd, evalLane, evalLane_canonAdd f a]
  | .montmul a z => by simp [canonAdd, evalLane, evalLane_canonAdd f a]

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

@[expose] def symPolyStage (len kInit : Nat) (barrettFirst : Bool) (f : List SExpr) :
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

@[expose] def symUpperInvNtt : List SExpr :=
  let init : List SExpr := (List.range 256).map SExpr.poly
  let (p, k) := symPolyStage 8 31 false init
  let (p, k) := symPolyStage 16 k true p
  let (p, k) := symPolyStage 32 k true p
  let (p, k) := symPolyStage 64 k true p
  let (p, _) := symPolyStage 128 k true p
  p.map SExpr.barrett

private theorem toArray_map_getD_const0 (f : Nat → BitVec 16) :
    ∀ (ls : List SExpr) (j : Nat),
      (ls.map (evalLane f)).toArray.getD j 0#16 = evalLane f (listGet ls j)
  | [], _ => by simp [Array.getD, listGet, evalLane]
  | _ :: _, 0 => by simp [Array.getD, listGet]
  | _ :: xs, n + 1 => by
    have h := toArray_map_getD_const0 f xs n
    simpa [Array.getD, listGet, Nat.succ_lt_succ_iff] using h

private theorem toArray_map_listSet (f : Nat → BitVec 16) (ls : List SExpr) (j : Nat) (e : SExpr) :
    ((listSet ls j e).map (evalLane f)).toArray =
      (ls.map (evalLane f)).toArray.set! j (evalLane f e) := by
  rw [listSet_eq_set, List.map_set]
  simp [Array.set!]

private theorem symPolyStage_map_evalLane (f : Nat → BitVec 16) (len kInit : Nat)
    (hkInit : kInit < 128) (bf : Bool) (ls0 : List SExpr) :
    (((symPolyStage len kInit bf ls0).1.map (evalLane f)).toArray,
      (symPolyStage len kInit bf ls0).2) =
      neonInvNttStage16 len kInit bf (ls0.map (evalLane f)).toArray := by
  dsimp only [symPolyStage, neonInvNttStage16]
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
      intro cur
      simp only [List.foldl_cons]
      rw [ih]; congr 1
      rw [toArray_map_listSet, toArray_map_listSet]
      cases bf <;>
        simp only [Bool.false_eq_true, ↓reduceIte, evalLane,
          ← toArray_map_getD_const0 f, ← zetaTableAt_eq k hk]
  have houter : ∀ (blks : List Nat) (cur : List SExpr) (k : Nat), k < 128 →
      let r := blks.foldl
        (fun (c, k') blk =>
          let start := blk * 2 * len
          let zeta := zetaTableAt k'
          let next := (List.range len).foldl
            (fun a off =>
              let j := start + off
              let x := listGet a j
              let y := listGet a (j + len)
              let sum := SExpr.add x y
              let a' := if bf then SExpr.barrett sum else sum
              let b' := SExpr.montmul (SExpr.sub y x) zeta
              listSet (listSet a j a') (j + len) b')
            c
          (next, k' - 1))
        (cur, k)
      ((r.1.map (evalLane f)).toArray, r.2) =
      blks.foldl
        (fun (c, k') blk =>
          let start := blk * 2 * len
          let zeta := zetasTimesMontgomeryR.getD k' 0#16
          let next := (List.range len).foldl
            (fun a off =>
              let j := start + off
              let x := a.getD j 0#16
              let y := a.getD (j + len) 0#16
              let sum := x + y
              let a' := if bf then neonBarrettReduce16 sum else sum
              let b' := neonMontgomeryMul16 (y - x) zeta
              (a.set! j a').set! (j + len) b')
            c
          (next, k' - 1))
        ((cur.map (evalLane f)).toArray, k) := by
    intro blks
    induction blks with
    | nil => intro cur k _; rfl
    | cons _ rest ih =>
      intro cur k hk
      dsimp only [List.foldl_cons]
      rw [ih _ (k - 1) (by omega), hinner _ k hk]
  exact houter _ ls0 kInit hkInit

private theorem symUpperInvNtt_map_evalLane {p2 : Poly16} (hp2 : p2.size = 256)
    (f : Nat → BitVec 16) (hf : ∀ idx < 256, f idx = p2.getD idx 0#16) :
    (symUpperInvNtt.map (evalLane f)).toArray = upperInvNtt16 p2 := by
  have hinit : (((List.range 256).map SExpr.poly).map (evalLane f)).toArray = p2 := by
    apply Array.ext
    · simp [hp2]
    · intro idx h1 h2
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, evalLane]
      rw [hf idx (by simpa [hp2] using h2)]
      simp [Array.getD, h2]
  unfold symUpperInvNtt upperInvNtt16
  dsimp only
  generalize hs8 : symPolyStage 8 31 false ((List.range 256).map SExpr.poly) = r8
  generalize hn8 : neonInvNttStage16 8 31 false p2 = q8
  have m8 := symPolyStage_map_evalLane f 8 31 (by omega) false ((List.range 256).map SExpr.poly)
  rw [hs8, hinit, hn8] at m8; rcases q8 with ⟨q8a, q8k⟩; obtain ⟨m8a, m8k⟩ := Prod.mk.inj m8
  have hk8 : r8.2 < 128 := by
    have hq := congrArg Prod.snd hn8; dsimp only at hq; rw [m8k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs16 : symPolyStage 16 r8.2 true r8.1 = r16
  generalize hn16 : neonInvNttStage16 16 q8k true q8a = q16
  have m16 := symPolyStage_map_evalLane f 16 r8.2 hk8 true r8.1
  rw [hs16, m8a, m8k, hn16] at m16; rcases q16 with ⟨q16a, q16k⟩; obtain ⟨m16a, m16k⟩ := Prod.mk.inj m16
  have hk16 : r16.2 < 128 := by
    have hq := congrArg Prod.snd hn16; dsimp only at hq; rw [m16k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs32 : symPolyStage 32 r16.2 true r16.1 = r32
  generalize hn32 : neonInvNttStage16 32 q16k true q16a = q32
  have m32 := symPolyStage_map_evalLane f 32 r16.2 hk16 true r16.1
  rw [hs32, m16a, m16k, hn32] at m32; rcases q32 with ⟨q32a, q32k⟩; obtain ⟨m32a, m32k⟩ := Prod.mk.inj m32
  have hk32 : r32.2 < 128 := by
    have hq := congrArg Prod.snd hn32; dsimp only at hq; rw [m32k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs64 : symPolyStage 64 r32.2 true r32.1 = r64
  generalize hn64 : neonInvNttStage16 64 q32k true q32a = q64
  have m64 := symPolyStage_map_evalLane f 64 r32.2 hk32 true r32.1
  rw [hs64, m32a, m32k, hn64] at m64; rcases q64 with ⟨q64a, q64k⟩; obtain ⟨m64a, m64k⟩ := Prod.mk.inj m64
  have hk64 : r64.2 < 128 := by
    have hq := congrArg Prod.snd hn64; dsimp only at hq; rw [m64k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs128 : symPolyStage 128 r64.2 true r64.1 = r128
  generalize hn128 : neonInvNttStage16 128 q64k true q64a = q128
  have m128 := symPolyStage_map_evalLane f 128 r64.2 hk64 true r64.1
  rw [hs128, m64a, m64k, hn128] at m128; rcases q128 with ⟨q128a, _⟩; obtain ⟨m128a, _⟩ := Prod.mk.inj m128
  have hm128l : r128.1.map (evalLane f) = q128a.toList := congrArg Array.toList m128a
  rw [List.map_map, show (evalLane f ∘ SExpr.barrett) = (neonBarrettReduce16 ∘ evalLane f) from rfl,
    ← List.map_map, hm128l, List.map_toArray, Array.toArray_toList]

/-! ## 3. Kernel-Checked AST Equivalence (`symState4c.poly` = `symUpperInvNtt`) -/

private theorem seg4_noSpillVreg :
    (List.range 32).all (fun k => noSpillVreg (symState4c.poly.get k)) = true := by
  rfl_kernel

set_option maxRecDepth 40000 in
private theorem seg4_ast_eq :
    (List.range 32).all (fun k =>
      (List.range 8).all (fun i =>
        SExpr.beq (canonAdd (shiftPolyIdx i (symState4c.poly.get k)))
          (canonAdd (listGet symUpperInvNtt (8 * k + i))))) = true := by
  rfl_kernel

theorem symState4c_poly_eq (ptr : BitVec 64) {p2 : Poly16} (hp2 : p2.size = 256)
    (env : SymEnv) (hpoly0 : env.poly0 = Vec32.ofFn (polyVecNat p2)) :
    Poly32Mem ptr (symState4c.poly.eval env) =
      PolyMem ptr (polyVecNat (upperInvNtt16 p2)) := by
  unfold Poly32Mem PolyMem
  apply vecRangeMem_congr
  intro k hk
  rw [symVec32_eval_get env symState4c.poly k hk]
  apply ext_lane16
  intro i
  have hns : noSpillVreg (symState4c.poly.get k) = true :=
    List.all_eq_true.mp seg4_noSpillVreg k (List.mem_range.mpr hk)
  rw [lane16_evalSExpr_eq env i (symState4c.poly.get k) hns]
  let f : Nat → BitVec 16 := fun idx => lane16 (env.poly0.get (idx / 8)) ⟨idx % 8, by omega⟩
  change evalLane f (shiftPolyIdx i.val (symState4c.poly.get k)) = _
  have hast : canonAdd (shiftPolyIdx i.val (symState4c.poly.get k)) =
      canonAdd (listGet symUpperInvNtt (8 * k + i.val)) :=
    SExpr.beq_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp seg4_ast_eq k (List.mem_range.mpr hk))
      i.val (List.mem_range.mpr i.isLt))
  rw [← evalLane_canonAdd f, hast, evalLane_canonAdd f, ← toArray_map_getD_const0 f]
  have hf : ∀ idx < 256, f idx = p2.getD idx 0#16 := by
    intro idx hidx
    dsimp only [f]
    rw [hpoly0, vec32_ofFn_get _ _ (by omega), polyVecNat, lane16_pack8x16]
    dsimp only; congr 1; omega
  rw [symUpperInvNtt_map_evalLane hp2 f hf, polyVecNat, lane16_pack8x16]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure

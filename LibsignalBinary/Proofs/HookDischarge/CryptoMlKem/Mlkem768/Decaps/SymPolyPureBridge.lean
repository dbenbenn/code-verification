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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt

/-!
# `decapsulate_compressed_key` (`B04`) — `Poly32Mem` Bridges for Symbolic Outputs (`SymPolyPureBridge`)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
  (zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
  (zetaTableAt_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
  (Poly16 zetasTimesMontgomeryR neonBarrettReduce16 neonMontgomeryMul16 neonInvNttStage16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
  (lane16 ext_lane16 lane16_pack8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
  (neonNttStage16 neonNttBinomialLayer7_16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (PolyMem Poly32Mem Vec32 polyVecNat vecRangeMem_congr vec32_ofFn_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure
  (upperInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
  (SExpr SymVec32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval
  (SymEnv evalSymVec32 symVec32_eval_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure
  (upperFwdNtt16 upperFwdNttBinomial16 neonNttStage16_snd evalLane noSpillVreg shiftLeafIdx
   lane16_evalSExpr_eq canonAddMul evalLane_canonAddMul listGet listSet
   toArray_map_getD_const0 toArray_map_listSet symFwdStage symBinomialLayer7 symInvStage
   symUpperFwdNtt symUpperFwdNttBinomial symBarrettMap symUpperInvNtt
   checkNoSpillVreg checkAstEq)

/-! ## 1. Symbolic Stage-to-`Poly16` Equivalence -/

private theorem symFwdStage_map_evalLane (fp fi : Nat → BitVec 16) (len kInit : Nat)
    (hk : kInit + (256 / (2 * len)) ≤ 128) (ls0 : List SExpr) :
    (((symFwdStage len kInit ls0).1.map (evalLane fp fi)).toArray, (symFwdStage len kInit ls0).2) =
      neonNttStage16 len kInit (ls0.map (evalLane fp fi)).toArray := by
  dsimp only [symFwdStage, neonNttStage16]
  have hinner : ∀ (offs : List Nat) (k : Nat) (_hk : k < 128) (start : Nat) (cur : List SExpr),
      ((offs.foldl
        (fun a off =>
          let j := start + off
          let x := listGet a j
          let y := listGet a (j + len)
          let t := SExpr.montmul y (zetaTableAt k)
          listSet (listSet a j (.add x t)) (j + len) (.sub x t))
        cur).map (evalLane fp fi)).toArray =
      offs.foldl
        (fun a off =>
          let j := start + off
          let x := a.getD j 0#16
          let y := a.getD (j + len) 0#16
          let t := neonMontgomeryMul16 y (zetasTimesMontgomeryR.getD k 0#16)
          (a.set! j (x + t)).set! (j + len) (x - t))
        (cur.map (evalLane fp fi)).toArray := by
    intro offs k hk1 start; induction offs with
    | nil => intro cur; rfl
    | cons _ rest ih =>
      intro cur; simp only [List.foldl_cons]; rw [ih]; congr 1
      rw [toArray_map_listSet, toArray_map_listSet]
      simp only [evalLane, ← toArray_map_getD_const0 fp fi, ← zetaTableAt_eq k hk1]
  have houter : ∀ (blks : List Nat) (cur : List SExpr) (k : Nat), k + blks.length ≤ 128 →
      let r := blks.foldl
        (fun (c, k') blk =>
          let start := blk * 2 * len
          let zeta := zetaTableAt k'
          let next := (List.range len).foldl
            (fun a off =>
              let j := start + off
              let x := listGet a j
              let y := listGet a (j + len)
              let t := SExpr.montmul y zeta
              listSet (listSet a j (.add x t)) (j + len) (.sub x t))
            c
          (next, k' + 1))
        (cur, k)
      ((r.1.map (evalLane fp fi)).toArray, r.2) =
      blks.foldl
        (fun (c, k') blk =>
          let start := blk * 2 * len
          let zeta := zetasTimesMontgomeryR.getD k' 0#16
          let next := (List.range len).foldl
            (fun a off =>
              let j := start + off
              let x := a.getD j 0#16
              let y := a.getD (j + len) 0#16
              let t := neonMontgomeryMul16 y zeta
              (a.set! j (x + t)).set! (j + len) (x - t))
            c
          (next, k' + 1))
        ((cur.map (evalLane fp fi)).toArray, k) := by
    intro blks; induction blks with
    | nil => intro cur k _; rfl
    | cons _ rest ih =>
      intro cur k hkb; simp only [List.length_cons] at hkb
      dsimp only [List.foldl_cons]
      rw [ih _ (k + 1) (by omega), hinner _ k (by omega)]
  exact houter _ ls0 kInit (by simpa using hk)

private theorem symBinomialLayer7_map_evalLane (fp fi : Nat → BitVec 16) (ls0 : List SExpr) :
    ((symBinomialLayer7 ls0).map (evalLane fp fi)).toArray =
      neonNttBinomialLayer7_16 (ls0.map (evalLane fp fi)).toArray := by
  dsimp only [symBinomialLayer7, neonNttBinomialLayer7_16]
  have hinner : ∀ (offs : List Nat) (cur : List SExpr),
      ((offs.foldl
        (fun a j =>
          let x := listGet a j
          let y := listGet a (j + 128)
          let t := SExpr.mul y (.const 0xf9c0#16)
          listSet (listSet a j (.add x t)) (j + 128) (.sub x t))
        cur).map (evalLane fp fi)).toArray =
      offs.foldl
        (fun a j =>
          let x := a.getD j 0#16
          let y := a.getD (j + 128) 0#16
          let t := y * 0xf9c0#16
          (a.set! j (x + t)).set! (j + 128) (x - t))
        (cur.map (evalLane fp fi)).toArray := by
    intro offs; induction offs with
    | nil => intro cur; rfl
    | cons _ rest ih =>
      intro cur; simp only [List.foldl_cons]; rw [ih]; congr 1
      rw [toArray_map_listSet, toArray_map_listSet]
      simp only [evalLane, ← toArray_map_getD_const0 fp fi]
  exact hinner _ ls0

private theorem foldl_sub1_snd {α : Type} (xs : List Nat) (g : α × Nat → Nat → α × Nat)
    (hg : ∀ x b, (g x b).2 = x.2 - 1) :
    ∀ (x0 : α × Nat), (xs.foldl g x0).2 = x0.2 - xs.length := by
  induction xs with
  | nil => intro x0; simp
  | cons _ rest ih => intro x0; simp only [List.foldl_cons, List.length_cons]; rw [ih, hg]; omega

private theorem neonInvNttStage16_snd (len kInit : Nat) (bf : Bool) (p : Poly16) :
    (neonInvNttStage16 len kInit bf p).2 = kInit - 256 / (2 * len) := by
  dsimp only [neonInvNttStage16]
  rw [foldl_sub1_snd _ _ (fun _ _ => rfl), List.length_range]

private theorem symInvStage_map_evalLane (fp fi : Nat → BitVec 16) (len kInit : Nat)
    (hkInit : kInit < 128) (bf : Bool) (ls0 : List SExpr) :
    (((symInvStage len kInit bf ls0).1.map (evalLane fp fi)).toArray,
      (symInvStage len kInit bf ls0).2) =
      neonInvNttStage16 len kInit bf (ls0.map (evalLane fp fi)).toArray := by
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
        cur).map (evalLane fp fi)).toArray =
      offs.foldl
        (fun a off =>
          let j := start + off
          let x := a.getD j 0#16
          let y := a.getD (j + len) 0#16
          let sum := x + y
          let a' := if bf then neonBarrettReduce16 sum else sum
          let b' := neonMontgomeryMul16 (y - x) (zetasTimesMontgomeryR.getD k 0#16)
          (a.set! j a').set! (j + len) b')
        (cur.map (evalLane fp fi)).toArray := by
    intro offs k hk start; induction offs with
    | nil => intro cur; rfl
    | cons _ rest ih =>
      intro cur; simp only [List.foldl_cons]; rw [ih]; congr 1
      rw [toArray_map_listSet, toArray_map_listSet]
      cases bf <;>
        simp only [Bool.false_eq_true, ↓reduceIte, evalLane,
          ← toArray_map_getD_const0 fp fi, ← zetaTableAt_eq k hk]
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
      ((r.1.map (evalLane fp fi)).toArray, r.2) =
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
        ((cur.map (evalLane fp fi)).toArray, k) := by
    intro blks; induction blks with
    | nil => intro cur k _; rfl
    | cons _ rest ih =>
      intro cur k hk; dsimp only [List.foldl_cons]
      rw [ih _ (k - 1) (by omega), hinner _ k hk]
  exact houter _ ls0 kInit hkInit

private theorem symUpperFwdNtt_map_evalLane {p0 : Poly16} (hp0 : p0.size = 256)
    (fp fi : Nat → BitVec 16) (hfp : ∀ idx < 256, fp idx = p0.getD idx 0#16) :
    (symUpperFwdNtt.map (evalLane fp fi)).toArray = upperFwdNtt16 p0 := by
  have hinit : (((List.range 256).map SExpr.poly).map (evalLane fp fi)).toArray = p0 := by
    apply Array.ext
    · simp [hp0]
    · intro idx h1 h2
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, evalLane]
      rw [hfp idx (by simpa [hp0] using h2)]; simp [Array.getD, h2]
  unfold symUpperFwdNtt upperFwdNtt16; dsimp only
  generalize hs1 : symFwdStage 128 1 ((List.range 256).map SExpr.poly) = r1
  generalize hn1 : neonNttStage16 128 1 p0 = q1
  have m1 := symFwdStage_map_evalLane fp fi 128 1 (by omega) ((List.range 256).map SExpr.poly)
  rw [hs1, hinit, hn1] at m1; rcases q1 with ⟨q1a, q1k⟩; obtain ⟨m1a, m1k⟩ := Prod.mk.inj m1
  have hk1 : r1.2 = 2 := by
    have hq := congrArg Prod.snd hn1; dsimp only at hq; rw [m1k, ← hq, neonNttStage16_snd]
  generalize hs2 : symFwdStage 64 r1.2 r1.1 = r2
  generalize hn2 : neonNttStage16 64 q1k q1a = q2
  have m2 := symFwdStage_map_evalLane fp fi 64 r1.2 (by omega) r1.1
  rw [hs2, m1a, m1k, hn2] at m2; rcases q2 with ⟨q2a, q2k⟩; obtain ⟨m2a, m2k⟩ := Prod.mk.inj m2
  have hk2 : r2.2 = 4 := by
    have hq := congrArg Prod.snd hn2; dsimp only at hq; rw [m2k, ← hq, neonNttStage16_snd, ← m1k, hk1]
  generalize hs3 : symFwdStage 32 r2.2 r2.1 = r3
  generalize hn3 : neonNttStage16 32 q2k q2a = q3
  have m3 := symFwdStage_map_evalLane fp fi 32 r2.2 (by omega) r2.1
  rw [hs3, m2a, m2k, hn3] at m3; rcases q3 with ⟨q3a, q3k⟩; obtain ⟨m3a, m3k⟩ := Prod.mk.inj m3
  have hk3 : r3.2 = 8 := by
    have hq := congrArg Prod.snd hn3; dsimp only at hq; rw [m3k, ← hq, neonNttStage16_snd, ← m2k, hk2]
  generalize hs4 : symFwdStage 16 r3.2 r3.1 = r4
  generalize hn4 : neonNttStage16 16 q3k q3a = q4
  have m4 := symFwdStage_map_evalLane fp fi 16 r3.2 (by omega) r3.1
  rw [hs4, m3a, m3k, hn4] at m4; rcases q4 with ⟨q4a, q4k⟩; obtain ⟨m4a, m4k⟩ := Prod.mk.inj m4
  have hk4 : r4.2 = 16 := by
    have hq := congrArg Prod.snd hn4; dsimp only at hq; rw [m4k, ← hq, neonNttStage16_snd, ← m3k, hk3]
  generalize hs5 : symFwdStage 8 r4.2 r4.1 = r5
  generalize hn5 : neonNttStage16 8 q4k q4a = q5
  have m5 := symFwdStage_map_evalLane fp fi 8 r4.2 (by omega) r4.1
  rw [hs5, m4a, m4k, hn5] at m5
  exact congrArg Prod.fst m5

private theorem symUpperFwdNttBinomial_map_evalLane {pIn : Poly16} (hpIn : pIn.size = 256)
    (fp fi : Nat → BitVec 16) (hfi : ∀ idx < 256, fi idx = pIn.getD idx 0#16) :
    (symUpperFwdNttBinomial.map (evalLane fp fi)).toArray = upperFwdNttBinomial16 pIn := by
  have hinit : (((List.range 256).map SExpr.inPoly).map (evalLane fp fi)).toArray = pIn := by
    apply Array.ext
    · simp [hpIn]
    · intro idx h1 h2
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, evalLane]
      rw [hfi idx (by simpa [hpIn] using h2)]; simp [Array.getD, h2]
  unfold symUpperFwdNttBinomial upperFwdNttBinomial16; dsimp only
  have m1 := symBinomialLayer7_map_evalLane fp fi ((List.range 256).map SExpr.inPoly)
  rw [hinit] at m1
  generalize symBinomialLayer7 ((List.range 256).map SExpr.inPoly) = r1 at m1 ⊢
  generalize neonNttBinomialLayer7_16 pIn = q1a at m1 ⊢
  generalize hs2 : symFwdStage 64 2 r1 = r2
  generalize hn2 : neonNttStage16 64 2 q1a = q2
  have m2 := symFwdStage_map_evalLane fp fi 64 2 (by omega) r1
  rw [hs2, m1, hn2] at m2; rcases q2 with ⟨q2a, q2k⟩; obtain ⟨m2a, m2k⟩ := Prod.mk.inj m2
  have hk2 : r2.2 = 4 := by
    have hq := congrArg Prod.snd hn2; dsimp only at hq; rw [m2k, ← hq, neonNttStage16_snd]
  generalize hs3 : symFwdStage 32 r2.2 r2.1 = r3
  generalize hn3 : neonNttStage16 32 q2k q2a = q3
  have m3 := symFwdStage_map_evalLane fp fi 32 r2.2 (by omega) r2.1
  rw [hs3, m2a, m2k, hn3] at m3; rcases q3 with ⟨q3a, q3k⟩; obtain ⟨m3a, m3k⟩ := Prod.mk.inj m3
  have hk3 : r3.2 = 8 := by
    have hq := congrArg Prod.snd hn3; dsimp only at hq; rw [m3k, ← hq, neonNttStage16_snd, ← m2k, hk2]
  generalize hs4 : symFwdStage 16 r3.2 r3.1 = r4
  generalize hn4 : neonNttStage16 16 q3k q3a = q4
  have m4 := symFwdStage_map_evalLane fp fi 16 r3.2 (by omega) r3.1
  rw [hs4, m3a, m3k, hn4] at m4; rcases q4 with ⟨q4a, q4k⟩; obtain ⟨m4a, m4k⟩ := Prod.mk.inj m4
  have hk4 : r4.2 = 16 := by
    have hq := congrArg Prod.snd hn4; dsimp only at hq; rw [m4k, ← hq, neonNttStage16_snd, ← m3k, hk3]
  generalize hs5 : symFwdStage 8 r4.2 r4.1 = r5
  generalize hn5 : neonNttStage16 8 q4k q4a = q5
  have m5 := symFwdStage_map_evalLane fp fi 8 r4.2 (by omega) r4.1
  rw [hs5, m4a, m4k, hn5] at m5
  exact congrArg Prod.fst m5

private theorem symBarrettMap_map_evalLane {p0 : Poly16} (hp0 : p0.size = 256)
    (fp fi : Nat → BitVec 16) (hfp : ∀ idx < 256, fp idx = p0.getD idx 0#16) :
    (symBarrettMap.map (evalLane fp fi)).toArray = p0.map neonBarrettReduce16 := by
  apply Array.ext
  · simp [symBarrettMap, hp0]
  · intro idx h1 h2
    simp only [symBarrettMap, List.getElem_toArray, List.getElem_map, List.getElem_range,
      Array.getElem_map, evalLane]
    rw [hfp idx (by simpa [hp0] using h2)]
    simp [Array.getD, show idx < p0.size by simpa using h2]

private theorem symUpperInvNtt_map_evalLane {p2 : Poly16} (hp2 : p2.size = 256)
    (fp fi : Nat → BitVec 16) (hfp : ∀ idx < 256, fp idx = p2.getD idx 0#16) :
    (symUpperInvNtt.map (evalLane fp fi)).toArray = upperInvNtt16 p2 := by
  have hinit : (((List.range 256).map SExpr.poly).map (evalLane fp fi)).toArray = p2 := by
    apply Array.ext
    · simp [hp2]
    · intro idx h1 h2
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, evalLane]
      rw [hfp idx (by simpa [hp2] using h2)]; simp [Array.getD, h2]
  unfold symUpperInvNtt upperInvNtt16; dsimp only
  generalize hs8 : symInvStage 8 31 false ((List.range 256).map SExpr.poly) = r8
  generalize hn8 : neonInvNttStage16 8 31 false p2 = q8
  have m8 := symInvStage_map_evalLane fp fi 8 31 (by omega) false ((List.range 256).map SExpr.poly)
  rw [hs8, hinit, hn8] at m8; rcases q8 with ⟨q8a, q8k⟩; obtain ⟨m8a, m8k⟩ := Prod.mk.inj m8
  have hk8 : r8.2 < 128 := by
    have hq := congrArg Prod.snd hn8; dsimp only at hq; rw [m8k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs16 : symInvStage 16 r8.2 true r8.1 = r16
  generalize hn16 : neonInvNttStage16 16 q8k true q8a = q16
  have m16 := symInvStage_map_evalLane fp fi 16 r8.2 hk8 true r8.1
  rw [hs16, m8a, m8k, hn16] at m16; rcases q16 with ⟨q16a, q16k⟩; obtain ⟨m16a, m16k⟩ := Prod.mk.inj m16
  have hk16 : r16.2 < 128 := by
    have hq := congrArg Prod.snd hn16; dsimp only at hq; rw [m16k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs32 : symInvStage 32 r16.2 true r16.1 = r32
  generalize hn32 : neonInvNttStage16 32 q16k true q16a = q32
  have m32 := symInvStage_map_evalLane fp fi 32 r16.2 hk16 true r16.1
  rw [hs32, m16a, m16k, hn32] at m32; rcases q32 with ⟨q32a, q32k⟩; obtain ⟨m32a, m32k⟩ := Prod.mk.inj m32
  have hk32 : r32.2 < 128 := by
    have hq := congrArg Prod.snd hn32; dsimp only at hq; rw [m32k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs64 : symInvStage 64 r32.2 true r32.1 = r64
  generalize hn64 : neonInvNttStage16 64 q32k true q32a = q64
  have m64 := symInvStage_map_evalLane fp fi 64 r32.2 hk32 true r32.1
  rw [hs64, m32a, m32k, hn64] at m64; rcases q64 with ⟨q64a, q64k⟩; obtain ⟨m64a, m64k⟩ := Prod.mk.inj m64
  have hk64 : r64.2 < 128 := by
    have hq := congrArg Prod.snd hn64; dsimp only at hq; rw [m64k, ← hq, neonInvNttStage16_snd]; omega
  generalize hs128 : symInvStage 128 r64.2 true r64.1 = r128
  generalize hn128 : neonInvNttStage16 128 q64k true q64a = q128
  have m128 := symInvStage_map_evalLane fp fi 128 r64.2 hk64 true r64.1
  rw [hs128, m64a, m64k, hn128] at m128; rcases q128 with ⟨q128a, _⟩; obtain ⟨m128a, _⟩ := Prod.mk.inj m128
  have hm128l : r128.1.map (evalLane fp fi) = q128a.toList := congrArg Array.toList m128a
  rw [List.map_map, show (evalLane fp fi ∘ SExpr.barrett) = (neonBarrettReduce16 ∘ evalLane fp fi) from rfl,
    ← List.map_map, hm128l, List.map_toArray, Array.toArray_toList]

/-! ## 2. Generic `Poly32Mem` Output Equivalence Bridges -/

private theorem symPoly_eq_of_map (ptr : BitVec 64) (v : SymVec32) (target : List SExpr)
    (out : Poly16) (env : SymEnv) (hns : checkNoSpillVreg v = true)
    (hast : checkAstEq v target = true)
    (hmap :
      (target.map (evalLane
        (fun idx => lane16 (env.poly0.get (idx / 8)) ⟨idx % 8, by omega⟩)
        (fun idx => lane16 (env.inPoly0.get (idx / 8)) ⟨idx % 8, by omega⟩))).toArray = out) :
    Poly32Mem ptr (evalSymVec32 env v) = PolyMem ptr (polyVecNat out) := by
  unfold Poly32Mem PolyMem
  apply vecRangeMem_congr
  intro k hk
  rw [symVec32_eval_get env v k hk]
  apply ext_lane16
  intro i
  have hns_k : noSpillVreg (v.get k) = true :=
    List.all_eq_true.mp hns k (List.mem_range.mpr hk)
  rw [lane16_evalSExpr_eq env i (v.get k) hns_k]
  let fp : Nat → BitVec 16 := fun idx => lane16 (env.poly0.get (idx / 8)) ⟨idx % 8, by omega⟩
  let fi : Nat → BitVec 16 := fun idx => lane16 (env.inPoly0.get (idx / 8)) ⟨idx % 8, by omega⟩
  change evalLane fp fi (shiftLeafIdx i.val (v.get k)) = _
  have hast_ki : canonAddMul (shiftLeafIdx i.val (v.get k)) =
      canonAddMul (listGet target (8 * k + i.val)) :=
    SExpr.beq_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp hast k (List.mem_range.mpr hk))
      i.val (List.mem_range.mpr i.isLt))
  rw [← evalLane_canonAddMul fp fi, hast_ki, evalLane_canonAddMul fp fi,
    ← toArray_map_getD_const0 fp fi, hmap, polyVecNat, lane16_pack8x16]

private theorem lane_vec32_polyVecNat (v0 : Vec32) (p : Poly16)
    (hv0 : v0 = Vec32.ofFn (polyVecNat p)) :
    ∀ idx < 256, lane16 (v0.get (idx / 8)) ⟨idx % 8, by omega⟩ = p.getD idx 0#16 := by
  intro idx hidx
  rw [hv0, vec32_ofFn_get _ _ (by omega), polyVecNat, lane16_pack8x16]
  dsimp only; congr 1; omega

theorem symPoly_eq_upperFwdNtt (ptr : BitVec 64) (v : SymVec32) {p0 : Poly16}
    (hp0 : p0.size = 256) (env : SymEnv) (hpoly0 : env.poly0 = Vec32.ofFn (polyVecNat p0))
    (hns : checkNoSpillVreg v = true) (hast : checkAstEq v symUpperFwdNtt = true) :
    Poly32Mem ptr (evalSymVec32 env v) = PolyMem ptr (polyVecNat (upperFwdNtt16 p0)) :=
  symPoly_eq_of_map ptr v symUpperFwdNtt (upperFwdNtt16 p0) env hns hast
    (symUpperFwdNtt_map_evalLane hp0 _ _ (lane_vec32_polyVecNat env.poly0 p0 hpoly0))

theorem symPoly_eq_upperFwdNttBinomial (ptr : BitVec 64) (v : SymVec32) {pIn : Poly16}
    (hpIn : pIn.size = 256) (env : SymEnv) (hin0 : env.inPoly0 = Vec32.ofFn (polyVecNat pIn))
    (hns : checkNoSpillVreg v = true) (hast : checkAstEq v symUpperFwdNttBinomial = true) :
    Poly32Mem ptr (evalSymVec32 env v) = PolyMem ptr (polyVecNat (upperFwdNttBinomial16 pIn)) :=
  symPoly_eq_of_map ptr v symUpperFwdNttBinomial (upperFwdNttBinomial16 pIn) env hns hast
    (symUpperFwdNttBinomial_map_evalLane hpIn _ _ (lane_vec32_polyVecNat env.inPoly0 pIn hin0))

theorem symPoly_eq_barrettMap (ptr : BitVec 64) (v : SymVec32) {p0 : Poly16}
    (hp0 : p0.size = 256) (env : SymEnv) (hpoly0 : env.poly0 = Vec32.ofFn (polyVecNat p0))
    (hns : checkNoSpillVreg v = true) (hast : checkAstEq v symBarrettMap = true) :
    Poly32Mem ptr (evalSymVec32 env v) = PolyMem ptr (polyVecNat (p0.map neonBarrettReduce16)) :=
  symPoly_eq_of_map ptr v symBarrettMap (p0.map neonBarrettReduce16) env hns hast
    (symBarrettMap_map_evalLane hp0 _ _ (lane_vec32_polyVecNat env.poly0 p0 hpoly0))

theorem symPoly_eq_upperInvNtt (ptr : BitVec 64) (v : SymVec32) {p2 : Poly16}
    (hp2 : p2.size = 256) (env : SymEnv) (hpoly0 : env.poly0 = Vec32.ofFn (polyVecNat p2))
    (hns : checkNoSpillVreg v = true) (hast : checkAstEq v symUpperInvNtt = true) :
    Poly32Mem ptr (evalSymVec32 env v) = PolyMem ptr (polyVecNat (upperInvNtt16 p2)) :=
  symPoly_eq_of_map ptr v symUpperInvNtt (upperInvNtt16 p2) env hns hast
    (symUpperInvNtt_map_evalLane hp2 _ _ (lane_vec32_polyVecNat env.poly0 p2 hpoly0))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge

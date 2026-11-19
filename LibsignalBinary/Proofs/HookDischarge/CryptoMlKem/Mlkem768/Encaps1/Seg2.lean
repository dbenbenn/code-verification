/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowInit
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Row

/-!
# `encapsulate1_serialized` (`B03`) — 3-Row `SampleNTT` Matrix `aTrans` (`Seg2`)

Proves the `+0x026c..+0x0500` row-copy epilogue and composes 3 iterations of `Seg2Row`
(`+0x0504..+0x3280`) into `seg2_safeSepWP` (unconditional) and `seg2_sepWP` (under
`Shake128MatrixTerminates`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 Shake128MatrixTerminates Shake128SeedTerminates bytesToPoly16 keccakZeroState
  sampleMatrixWith sampleNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  Shake128MatrixTerminates_seed_len32 packHalfwordsLE packHalfwordsLE_length sampleNttClassical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSepFrom MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem Vec128At polyMem_bytesToPoly16 polyVecNat vec128At_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  MlkemBlk03Args blkPC03 blkPl03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  Seg2ConstsLo Seg2Preserved Seg2RegInv Seg2SeedConsts)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs (
  BTree KCfg KEnv KExpr KState evalKExpr fetchWordTree03 runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem (
  TreeMem btreeOfWords btreeOfWords_get btreeWords btreeWords_eq_of_get bytesToWords
  bytesToWords_length fetch_blk03_seg2a pointsToBytes_eq_treeMem
  seg2SeedConsts_eq_treeMem seedConstsWords sepWP_elim_treeMem treeMem_entails_memRegion
  treeMem_eq_pointsToBytes treeMem_join treeMem_split wordsToBytes wordsToBytes_bytesToWords
  zeroTree9)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge (
  KCfgWf KConstsLoOpt KSpatial evalMemTree matches_advancePC matches_setPC matches_writeGpr
  setPC_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step (
  sepWP_runKRange_seg2a)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog (
  kpflagOptBeq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init (
  Seg2RowExit entry_memA_join keccakRc_intro rowSeeds step_bCond_seg2a)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Runner (
  eval_checked_gpr eval_checked_memA eval_checked_memB eval_checked_pstate)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Clamp (
  checkSegRegGprs eq_some_getD extract_segRegInv mkSegBaseState mkSegEnv mkSegState
  mkSegState_matches sepWP_drop_left with_frozen_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2RowInit (
  pc_add_eq pc_of_eq setPC_disp_eq setPC_fall_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Row (
  seg2_row_safeSepWP seg2_row_sepWP)

attribute [local irreducible] blkPC03

/-! ## 1. Transposed `SampleNTT` Matrix Predicates (`ATransRowMem`, `ATransMem`) & Spatial Bridges -/

@[expose] noncomputable def aTransPoly (rho : List (BitVec 8)) (row col : Nat) : Poly :=
  sampleNtt (rho ++ [BitVec.ofNat 8 row, BitVec.ofNat 8 col])

@[expose] noncomputable def aTransPoly16 (rho : List (BitVec 8)) (row col : Nat) : Poly16 :=
  (aTransPoly rho row col).map (BitVec.ofNat 16)

private theorem sampleNttClassical_eq (seed34 : List (BitVec 8)) :
    sampleNttClassical seed34 = sampleNtt seed34 := by
  unfold sampleNttClassical sampleNtt
  by_cases h : Shake128SeedTerminates seed34 <;> simp [h]

theorem sampleMatrixWith_false_getD {rho : List (BitVec 8)} (hrho : rho.length = 32)
    {row col : Nat} (hr : row < 3) (hc : col < 3) :
    ((sampleMatrixWith sampleNtt 3 rho false).getD row #[]).getD col zeroPoly =
      aTransPoly rho row col := by
  have htake : rho.take 32 = rho := List.take_of_length_le (Nat.le_of_eq hrho)
  simp [sampleMatrixWith, aTransPoly, Array.getD, hr, hc, htake]

private theorem shake128MatrixTerminates_row {rho : List (BitVec 8)} (hrho : rho.length = 32)
    (hTerm : Shake128MatrixTerminates rho 3) {row col : Nat} (hr : row < 3) (hc : col < 3) :
    Shake128SeedTerminates (rowSeeds rho row col) := by
  have h := hTerm row col hr hc
  have htake : rho.take 32 = rho := List.take_of_length_le (Nat.le_of_eq hrho)
  rwa [htake] at h

attribute [local irreducible] sampleNtt

@[expose] noncomputable def ATransRowMem (sp : BitVec 64) (rho : List (BitVec 8)) (row : Nat) : SepProp :=
  PolyMem (sp + BitVec.ofNat 64 (6832 + 1536 * row)) (polyVecNat (aTransPoly16 rho row 0)) ∗
  PolyMem (sp + BitVec.ofNat 64 (6832 + 1536 * row + 512)) (polyVecNat (aTransPoly16 rho row 1)) ∗
  PolyMem (sp + BitVec.ofNat 64 (6832 + 1536 * row + 1024)) (polyVecNat (aTransPoly16 rho row 2))

@[expose] noncomputable def ATransMem (sp : BitVec 64) (rho : List (BitVec 8)) : SepProp :=
  ATransRowMem sp rho 0 ∗ ATransRowMem sp rho 1 ∗ ATransRowMem sp rho 2

private theorem getD_append_left {α : Type} (xs ys : List α) (d : α) {i : Nat} (hi : i < xs.length) :
    (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_right {α : Type} (xs ys : List α) (d : α) {i : Nat} (hi : xs.length ≤ i) :
    (xs ++ ys).getD i d = ys.getD (i - xs.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private theorem getD_take_lt {α : Type} (xs : List α) (n : Nat) (d : α) {i : Nat} (hi : i < n) :
    (xs.take n).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, hi]

private theorem packWordAt_slice3 {b0 b1 b2 : List (BitVec 8)}
    (h0 : b0.length = 544) (h1 : b1.length = 544) (_h2 : b2.length = 544) :
    (∀ i, i < 64 → Seg2Mem.packWordAt (b0 ++ (b1 ++ b2)) (8 * i) =
      Seg2Mem.packWordAt (b0.take 512) (8 * i)) ∧
    (∀ i, i < 64 → Seg2Mem.packWordAt (b0 ++ (b1 ++ b2)) (8 * (68 + i)) =
      Seg2Mem.packWordAt (b1.take 512) (8 * i)) ∧
    (∀ i, i < 64 → Seg2Mem.packWordAt (b0 ++ (b1 ++ b2)) (8 * (136 + i)) =
      Seg2Mem.packWordAt (b2.take 512) (8 * i)) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · unfold Seg2Mem.packWordAt
    have eqk : ∀ k, k < 8 → (b0 ++ (b1 ++ b2)).getD (8 * i + k) 0#8 = (b0.take 512).getD (8 * i + k) 0#8 :=
      fun k hk => by rw [getD_append_left _ _ _ (by omega), getD_take_lt _ _ _ (by omega)]
    rw [eqk 7 (by omega), eqk 6 (by omega), eqk 5 (by omega), eqk 4 (by omega),
        eqk 3 (by omega), eqk 2 (by omega), eqk 1 (by omega),
        show (b0 ++ (b1 ++ b2)).getD (8 * i) 0#8 = (b0.take 512).getD (8 * i) 0#8 from eqk 0 (by omega)]
  · unfold Seg2Mem.packWordAt
    have eqk : ∀ k, k < 8 → (b0 ++ (b1 ++ b2)).getD (8 * (68 + i) + k) 0#8 = (b1.take 512).getD (8 * i + k) 0#8 :=
      fun k hk => by
        rw [getD_append_right _ _ _ (by omega), show 8 * (68 + i) + k - b0.length = 8 * i + k by omega,
            getD_append_left _ _ _ (by omega), getD_take_lt _ _ _ (by omega)]
    rw [show 8 * (68 + i) = 8 * (68 + i) + 0 by omega, eqk 0 (by omega),
        show 8 * (68 + i) + 0 + 1 = 8 * (68 + i) + 1 by omega, eqk 1 (by omega),
        show 8 * (68 + i) + 0 + 2 = 8 * (68 + i) + 2 by omega, eqk 2 (by omega),
        show 8 * (68 + i) + 0 + 3 = 8 * (68 + i) + 3 by omega, eqk 3 (by omega),
        show 8 * (68 + i) + 0 + 4 = 8 * (68 + i) + 4 by omega, eqk 4 (by omega),
        show 8 * (68 + i) + 0 + 5 = 8 * (68 + i) + 5 by omega, eqk 5 (by omega),
        show 8 * (68 + i) + 0 + 6 = 8 * (68 + i) + 6 by omega, eqk 6 (by omega),
        show 8 * (68 + i) + 0 + 7 = 8 * (68 + i) + 7 by omega, eqk 7 (by omega)]
    simp only [Nat.add_zero]
  · unfold Seg2Mem.packWordAt
    have eqk : ∀ k, k < 8 → (b0 ++ (b1 ++ b2)).getD (8 * (136 + i) + k) 0#8 = (b2.take 512).getD (8 * i + k) 0#8 :=
      fun k hk => by
        rw [getD_append_right _ _ _ (by omega), show 8 * (136 + i) + k - b0.length = 544 + 8 * i + k by omega,
            getD_append_right _ _ _ (by omega), show 544 + 8 * i + k - b1.length = 8 * i + k by omega,
            getD_take_lt _ _ _ (by omega)]
    rw [show 8 * (136 + i) = 8 * (136 + i) + 0 by omega, eqk 0 (by omega),
        show 8 * (136 + i) + 0 + 1 = 8 * (136 + i) + 1 by omega, eqk 1 (by omega),
        show 8 * (136 + i) + 0 + 2 = 8 * (136 + i) + 2 by omega, eqk 2 (by omega),
        show 8 * (136 + i) + 0 + 3 = 8 * (136 + i) + 3 by omega, eqk 3 (by omega),
        show 8 * (136 + i) + 0 + 4 = 8 * (136 + i) + 4 by omega, eqk 4 (by omega),
        show 8 * (136 + i) + 0 + 5 = 8 * (136 + i) + 5 by omega, eqk 5 (by omega),
        show 8 * (136 + i) + 0 + 6 = 8 * (136 + i) + 6 by omega, eqk 6 (by omega),
        show 8 * (136 + i) + 0 + 7 = 8 * (136 + i) + 7 by omega, eqk 7 (by omega)]
    simp only [Nat.add_zero]

private theorem multiLaneSlots3_eq_treeMem (sp : BitVec 64) {hws : Nat → List (BitVec 16)}
    (hlen : ∀ c, c < 3 → (hws c).length = 272) :
    let bs := packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2))
    MultiLaneSlots (sp + 4272#64) 544 3 hws =
      TreeMem (sp + 4272#64) 204 (btreeOfWords 0 (bytesToWords 204 bs) zeroTree9) := by
  intro bs
  have h0 : (packHalfwordsLE (hws 0)).length = 544 := by rw [packHalfwordsLE_length, hlen 0 (by omega)]
  have h1 : (packHalfwordsLE (hws 1)).length = 544 := by rw [packHalfwordsLE_length, hlen 1 (by omega)]
  have h2 : (packHalfwordsLE (hws 2)).length = 544 := by rw [packHalfwordsLE_length, hlen 2 (by omega)]
  have hbs : bs.length = 8 * 204 := by simp [bs, h0, h1, h2]
  rw [← pointsToBytes_eq_treeMem hbs (by decide)]
  simp only [bs, pointsToBytes_append, h0, h1, MultiLaneSlots, MultiLaneSepFrom,
    sepConj_emp, BitVec.add_assoc]
  rfl

private theorem treeMem192_eq_aTransRowMem (sp : BitVec 64) (rho : List (BitVec 8)) (row : Nat)
    {extra : Nat} {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hd : allLanesDone 3 (rowSeeds rho row) extra = true)
    (hinv : MultiLaneXofInv 3 (rowSeeds rho row) extra sampled hws)
    (tB : BTree (BitVec 64) 9)
    (hB0 : ∀ i, i < 64 → tB.get i =
      (btreeOfWords 0 (bytesToWords 204
        (packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2)))) zeroTree9).get i)
    (hB1 : ∀ i, i < 64 → tB.get (64 + i) =
      (btreeOfWords 0 (bytesToWords 204
        (packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2)))) zeroTree9).get (68 + i))
    (hB2 : ∀ i, i < 64 → tB.get (128 + i) =
      (btreeOfWords 0 (bytesToWords 204
        (packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2)))) zeroTree9).get (136 + i)) :
    TreeMem (sp + BitVec.ofNat 64 (6832 + 1536 * row)) 192 tB = ATransRowMem sp rho row := by
  let b0 := packHalfwordsLE (hws 0)
  let b1 := packHalfwordsLE (hws 1)
  let b2 := packHalfwordsLE (hws 2)
  have hb0 : b0.length = 544 := by simp [b0, (hinv 0 (by omega)).1.1]
  have hb1 : b1.length = 544 := by simp [b1, (hinv 1 (by omega)).1.1]
  have hb2 : b2.length = 544 := by simp [b2, (hinv 2 (by omega)).1.1]
  rcases packWordAt_slice3 hb0 hb1 hb2 with ⟨hp0, hp1, hp2⟩
  let t12 := BTree.ofFn 9 fun i => tB.get (64 + i)
  let t2 := BTree.ofFn 9 fun i => t12.get (64 + i)
  have hgetS : ∀ j, j < 204 →
      (btreeOfWords 0 (bytesToWords 204 (b0 ++ (b1 ++ b2))) zeroTree9).get j =
        Seg2Mem.packWordAt (b0 ++ (b1 ++ b2)) (8 * j) := fun j hj => by
    have hg := btreeOfWords_get 0 (bytesToWords 204 (b0 ++ (b1 ++ b2))) zeroTree9 j
      (by rw [bytesToWords_length]; exact hj) (by rw [bytesToWords_length]; omega)
    rw [Nat.zero_add] at hg
    rw [hg, Seg2Mem.bytesToWords_getD 204 _ j hj]
  have ht0 : TreeMem (sp + BitVec.ofNat 64 (6832 + 1536 * row)) 64 tB =
      PolyMem (sp + BitVec.ofNat 64 (6832 + 1536 * row)) (polyVecNat (aTransPoly16 rho row 0)) := by
    have htake : (b0.take 512).length = 512 := by simp [hb0]
    rw [treeMem_eq_pointsToBytes (bs := b0.take 512) (by
      rw [btreeWords_eq_of_get (ws := bytesToWords 64 (b0.take 512)) (bytesToWords_length 64 _) fun i hi => by
        rw [Nat.zero_add, hB0 i hi, hgetS i (by omega), hp0 i hi, ← Seg2Mem.bytesToWords_getD 64 _ i hi]]
      exact wordsToBytes_bytesToWords 64 _ htake),
      polyMem_bytesToPoly16 _ htake, (hinv.exit_poly hd (by omega : 0 < 3)).2.2,
      sampleNttClassical_eq]
    rfl
  have ht1 : TreeMem (sp + BitVec.ofNat 64 (6832 + 1536 * row + 512)) 64 t12 =
      PolyMem (sp + BitVec.ofNat 64 (6832 + 1536 * row + 512)) (polyVecNat (aTransPoly16 rho row 1)) := by
    have htake : (b1.take 512).length = 512 := by simp [hb1]
    rw [treeMem_eq_pointsToBytes (bs := b1.take 512) (by
      rw [btreeWords_eq_of_get (ws := bytesToWords 64 (b1.take 512)) (bytesToWords_length 64 _) fun i hi => by
        rw [Nat.zero_add, BTree.get_ofFn 9 _ i (by omega), hB1 i hi, hgetS (68 + i) (by omega),
            hp1 i hi, ← Seg2Mem.bytesToWords_getD 64 _ i hi]]
      exact wordsToBytes_bytesToWords 64 _ htake),
      polyMem_bytesToPoly16 _ htake, (hinv.exit_poly hd (by omega : 1 < 3)).2.2,
      sampleNttClassical_eq]
    rfl
  have ht2 : TreeMem (sp + BitVec.ofNat 64 (6832 + 1536 * row + 1024)) 64 t2 =
      PolyMem (sp + BitVec.ofNat 64 (6832 + 1536 * row + 1024)) (polyVecNat (aTransPoly16 rho row 2)) := by
    have htake : (b2.take 512).length = 512 := by simp [hb2]
    rw [treeMem_eq_pointsToBytes (bs := b2.take 512) (by
      rw [btreeWords_eq_of_get (ws := bytesToWords 64 (b2.take 512)) (bytesToWords_length 64 _) fun i hi => by
        rw [Nat.zero_add, BTree.get_ofFn 9 _ i (by omega), BTree.get_ofFn 9 _ (64 + i) (by omega),
            show 64 + (64 + i) = 128 + i by omega, hB2 i hi, hgetS (136 + i) (by omega),
            hp2 i hi, ← Seg2Mem.bytesToWords_getD 64 _ i hi]]
      exact wordsToBytes_bytesToWords 64 _ htake),
      polyMem_bytesToPoly16 _ htake, (hinv.exit_poly hd (by omega : 2 < 3)).2.2,
      sampleNttClassical_eq]
    rfl
  rw [show (192 : Nat) = 64 + 128 from rfl,
      treeMem_split (n1 := 64) (n2 := 128) (t2 := t12) (fun i hi => BTree.get_ofFn 9 _ i (by omega)),
      show sp + BitVec.ofNat 64 (6832 + 1536 * row) + BitVec.ofNat 64 (8 * 64) =
        sp + BitVec.ofNat 64 (6832 + 1536 * row + 512) by clear *- ; bv_omega,
      show (128 : Nat) = 64 + 64 from rfl,
      treeMem_split (n1 := 64) (n2 := 64) (t2 := t2) (fun i hi => BTree.get_ofFn 9 _ i (by omega)),
      show sp + BitVec.ofNat 64 (6832 + 1536 * row + 512) + BitVec.ofNat 64 (8 * 64) =
        sp + BitVec.ofNat 64 (6832 + 1536 * row + 1024) by clear *- ; bv_omega,
      ht0, ht1, ht2]
  rfl

/-! ## 2. Row-Copy Epilogue (`+0x026c .. +0x0500`, `w = 155 .. 320`) -/

private def cfgCopy (row : Nat) : KCfg :=
  { offA := 4272, lenA := 204, offB := 6832 + 1536 * row, lenB := 192, hasConstsLo := false }

private theorem cfgCopy_wf {row : Nat} (hrow : row < 3) : KCfgWf (cfgCopy row) := by
  rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl <;> decide +kernel

private def stCopyPre (row : Nat) : KState :=
  (runKRange (cfgCopy row) 155 6 (mkSegBaseState false)).getD (mkSegBaseState false)

private def stCopyMid (row : Nat) : KState :=
  { stCopyPre row with gprs := (stCopyPre row).gprs.set 9 (.spAdd (BitVec.ofNat 64 (6832 + 1536 * row))) }

private def stCopyEnd (row : Nat) : KState :=
  (runKRange (cfgCopy row) 162 158 (stCopyMid row)).getD (stCopyMid row)

private def checkCopyPre (st : KState) : Bool :=
  (st.gprs.get 9).beq (.spAdd 6832#64) &&
  (st.gprs.get 10).beq (.const64 1536#64) &&
  (st.gprs.get 22).beq (.var 96)

private def checkCopyEnd (st : KState) : Bool :=
  checkSegRegGprs st (.var 101) &&
  kpflagOptBeq st.pstateFlag (some (.subs64 (.var 101) 3#64)) &&
  ((List.range 64).all fun i =>
    (st.memB.get i).beq (.var (300 + i)) &&
    (st.memB.get (64 + i)).beq (.var (368 + i)) &&
    (st.memB.get (128 + i)).beq (.var (436 + i)))

private theorem cert_copyPre {row : Nat} (hrow : row < 3) :
    runKRange (cfgCopy row) 155 6 (mkSegBaseState false) = some (stCopyPre row) ∧
    checkCopyPre (stCopyPre row) = true := by
  rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl <;>
    exact ⟨eq_some_getD (mkSegBaseState false) (by decide +kernel), by decide +kernel⟩

private theorem cert_copyEnd {row : Nat} (hrow : row < 3) :
    runKRange (cfgCopy row) 162 158 (stCopyMid row) = some (stCopyEnd row) ∧
    checkCopyEnd (stCopyEnd row) = true := by
  rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl <;>
    exact ⟨eq_some_getD (stCopyMid _) (by decide +kernel), by decide +kernel⟩

attribute [local irreducible] stCopyPre stCopyEnd

private theorem step_gpr_pure03 {prog : Program} {tgt pc : BitVec 64}
    {cfg : KCfg} {env : KEnv} {st : KState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop}
    {inst : Instr} {rd : BitVec 5} {e : KExpr} {res : BitVec 64}
    (hrd : rd ≠ 31#5) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = ((s.setPC pc).writeReg64 (.gpr rd) res).advancePC)
    (hres : res = evalKExpr env e) (hm : Seg2SymBridge.KStateMatches env st s)
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      Seg2SymBridge.KStateMatches env { st with gprs := st.gprs.set rd.toNat e } s' →
      SepWP prog tgt s' (KSpatial cfg env { st with gprs := st.gprs.set rd.toNat e } F) post) :
    SepWP prog tgt s (KSpatial cfg env st F) post :=
  SepWP.step_pure hpc hrun hfetch hexec rfl
    (hnext _ rfl hrun (matches_advancePC (matches_writeGpr (matches_setPC hm pc) hrd e hres)))

private theorem eval_madd_x9_x22_x10 {prog : Program} {pc v9 v10 v22 : BitVec 64} {s : State}
    (hx9 : s.readReg64 .x9 = v9) (hx10 : s.readReg64 .x10 = v10) (hx22 : s.readReg64 .x22 = v22) :
    prog.evalInst (.dataProc3 .W64 .MADD .x9 .x22 .x10 .x9) (s.setPC pc) =
      ((s.setPC pc).writeReg64 (.gpr 9#5) (v9 + v22 * v10)).advancePC := by
  simp [Program.evalInst, execInstWithSvc, execDataProc3,
    State.readReg64, RegFile.read] at hx9 hx10 hx22 ⊢
  simp [State.setPC, hx9, hx10, hx22]

private theorem step_madd_161 [MlKemPlacement] {b tgt sp : BitVec 64} {row : Nat} (hrow : row < 3)
    {env : KEnv} {F : SepProp} {post : State → SepProp → Prop} {s : State}
    (hsp : env.sp = sp) (hv96 : env.vars 96 = BitVec.ofNat 64 row)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 161)) (hrun : s.status = .Running)
    (hm : Seg2SymBridge.KStateMatches env (stCopyPre row) s)
    (hnext : ∀ s' : State, s'.pc = b + BitVec.ofNat 64 (4 * 162) → s'.status = .Running →
      Seg2SymBridge.KStateMatches env (stCopyMid row) s' →
      SepWP (blkPC03.rebase b (fun _ => none)) tgt s'
        (KSpatial (cfgCopy row) env (stCopyMid row) F) post) :
    SepWP (blkPC03.rebase b (fun _ => none)) tgt s
      (KSpatial (cfgCopy row) env (stCopyPre row) F) post := by
  have hc := (cert_copyPre hrow).2
  simp only [checkCopyPre, Bool.and_eq_true] at hc
  have hx9 : s.readReg64 .x9 = sp + 6832#64 := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 9#5 (by decide) (.spAdd 6832#64) hc.1.1 rfl
    simpa [evalKExpr, hsp] using h
  have hx10 : s.readReg64 .x10 = 1536#64 := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 10#5 (by decide) (.const64 1536#64) hc.1.2 rfl
    simpa [evalKExpr] using h
  have hx22 : s.readReg64 .x22 = BitVec.ofNat 64 row := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 22#5 (by decide) (.var 96) hc.2 rfl
    simpa [evalKExpr, hv96] using h
  have hfw : fetchWordTree03 161 = some (.dataProc3 .W64 .MADD .x9 .x22 .x10 .x9) := by decide +kernel
  have hres : (sp + 6832#64) + BitVec.ofNat 64 row * 1536#64 =
      evalKExpr env (.spAdd (BitVec.ofNat 64 (6832 + 1536 * row))) := by
    change (sp + 6832#64) + BitVec.ofNat 64 row * 1536#64 =
      env.sp + BitVec.ofNat 64 (6832 + 1536 * row)
    rw [hsp]
    rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl <;> bv_omega
  have hpc162 : (b + BitVec.ofNat 64 (4 * 161)) + 4#64 = b + BitVec.ofNat 64 (4 * 162) := by bv_omega
  exact step_gpr_pure03 (by decide) hpc hrun (fetch_blk03_seg2a (by omega) (by omega) hfw)
    (eval_madd_x9_x22_x10 hx9 hx10 hx22) hres hm
    (fun s' hs' hrun' hm' => hnext s' (hs'.trans hpc162) hrun' hm')

attribute [local irreducible] stCopyMid

private theorem mkSegEnv_vars_memA [MlKemPlacement] (sp : BitVec 64) (row : Nat)
    (rho : List (BitVec 8)) (s : State) (tA tB : BTree (BitVec 64) 9) {k : Nat} (hk : k < 512) :
    (mkSegEnv sp row rho keccakZeroState keccakZeroState keccakZeroState s tA tB).vars (300 + k) =
      tA.get k := by
  simp only [mkSegEnv, Bool.false_eq_true, ↓reduceIte,
    show ¬(300 + k < 25) by omega, show ¬(300 + k < 50) by omega, show ¬(300 + k < 75) by omega,
    beq_false_of_ne (show 300 + k ≠ 96 by omega), beq_false_of_ne (show 300 + k ≠ 97 by omega),
    beq_false_of_ne (show 300 + k ≠ 98 by omega), beq_false_of_ne (show 300 + k ≠ 99 by omega),
    beq_false_of_ne (show 300 + k ≠ 100 by omega), beq_false_of_ne (show 300 + k ≠ 101 by omega),
    show ¬(300 + k < 174) by omega, show ¬(300 + k < 232) by omega,
    show 300 + k < 812 by omega, show 300 + k - 300 = k by omega]

private theorem seg2_row_copy_wp [MlKemPlacement] {b sp : BitVec 64}
    {rho : List (BitVec 8)} {row : Nat} (hrow : row < 3) {F : SepProp}
    {s : State} {P : SepProp}
    (hexit : Seg2RowExit b sp rho row
      (memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * row)) 1536 ∗ F) s P) :
    let tgt := if row == 2 then b + 0x3280#64 else b + 0x0504#64
    SepWP (blkPC03.rebase b (fun _ => none)) tgt s P
      (fun sf Pf =>
        sf.pc = tgt ∧ sf.status = .Running ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg2RegInv sp sf ∧ sf.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧
        ∃ tA : BTree (BitVec 64) 9,
          (∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64) ∧
          (Pf ⊢ Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗
            memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
            memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 13984#64) 504 ∗
            ATransRowMem sp rho row ∗ F)) := by
  intro tgt
  rcases hexit with ⟨hpc, hrun, hcl, hro, hreg, hx8, hx22,
    extra, tA, sampled, hws, hdone, hinv, htA, hP⟩
  let tSlots := btreeOfWords 0 (bytesToWords 204
    (packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2)))) zeroTree9
  have hSlots : MultiLaneSlots (sp + 4272#64) 544 3 hws = TreeMem (sp + 4272#64) 204 tSlots :=
    multiLaneSlots3_eq_treeMem sp fun c hc => (hinv c hc).1.1
  let Rest0 := Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗
    memRegion (sp + 2192#64) 1512 ∗ TreeMem (sp + 4272#64) 204 tSlots ∗
    memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 13984#64) 504 ∗ F
  refine SepWP.weaken_pre (P' := memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * row)) (8 * 192) ∗ Rest0)
    (by
      rw [hSlots] at hP
      exact Entails.trans hP (by dsimp only [Rest0]; rw [show 8 * 192 = 1536 from rfl]; sep_frame)) ?_
  refine with_frozen_env hcl hro ?_
  refine sepWP_elim_treeMem (len := 192) (by decide) fun tB0 => ?_
  refine keccakRc_intro hro ?_
  let env := mkSegEnv sp row rho keccakZeroState keccakZeroState keccakZeroState s tSlots tB0
  have hmk : Seg2SymBridge.KStateMatches env (mkSegBaseState false) s ∧
      evalMemTree env (mkSegBaseState false).memA = tSlots ∧
      evalMemTree env (mkSegBaseState false).memB = tB0 := by
    simpa [mkSegState, Seg2Clamp.writeSlotsPair, Seg2Clamp.writeSlotsSingle] using
      mkSegState_matches (cfg := cfgCopy row) (hasSeedConsts := false) (slots01 := []) (slots2 := [])
        (k0 := keccakZeroState) (k1 := keccakZeroState) (k2 := keccakZeroState)
        (tA := tSlots) (tB := tB0) (by decide) (by decide) hreg hx22
        (fun h => Bool.noConfusion h) (fun _ h => by simp at h) (fun _ h => by simp at h)
  let FF := Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗
    memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 12448#64) 24 ∗
    memRegion (sp + 13984#64) 504 ∗ F
  refine SepWP.weaken_pre (P' := KSpatial (cfgCopy row) env (mkSegBaseState false) FF)
    (by
      dsimp only [KSpatial, KConstsLoOpt, cfgCopy, Rest0, FF]
      rw [hmk.2.1, hmk.2.2, show env.sp = sp from rfl,
          show env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
          show sp + BitVec.ofNat 64 4272 = sp + 4272#64 from rfl, emp_sepConj]
      sep_frame) ?_
  refine sepWP_runKRange_seg2a (cfgCopy_wf hrow) (by change 0 < 24; decide : env.rLoop < 24)
    (w := 155) (n := 6) (by omega) (by omega)
    (pc_of_eq hpc (by decide +kernel)) hrun hmk.1 (cert_copyPre hrow).1
    fun s1 hpc1 hrun1 hm1 => ?_
  refine step_madd_161 hrow (sp := sp) rfl rfl hpc1 hrun1 hm1 fun s2 hpc2 hrun2 hm2 => ?_
  refine sepWP_runKRange_seg2a (cfgCopy_wf hrow) (by change 0 < 24; decide : env.rLoop < 24)
    (w := 162) (n := 158) (by omega) (by omega) hpc2 hrun2 hm2 (cert_copyEnd hrow).1
    fun s3 hpc3 hrun3 hm3 => ?_
  have hcE := (cert_copyEnd hrow).2
  simp only [checkCopyEnd, Bool.and_eq_true] at hcE
  have hpst : s3.pstate = subsPState64 (BitVec.ofNat 64 (row + 1)) 3#64 := by
    have hp := eval_checked_pstate (ok := fun _ => true) hm3 (fun _ _ => rfl)
      (.var 101) 3#64 hcE.1.2 rfl
    simpa [evalKExpr, env, mkSegEnv, hx8] using hp
  have hB : TreeMem (sp + BitVec.ofNat 64 (6832 + 1536 * row)) 192
      (evalMemTree env (stCopyEnd row).memB) = ATransRowMem sp rho row := by
    refine treeMem192_eq_aTransRowMem sp rho row hdone hinv _
      (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
    · have hi' := (List.all_eq_true.mp hcE.2) i (List.mem_range.mpr hi)
      simp only [Bool.and_eq_true] at hi'
      rw [eval_checked_memB (ok := fun _ => true) (fun _ _ => rfl) i _ hi'.1.1 rfl]
      exact mkSegEnv_vars_memA sp row rho s tSlots tB0 (by omega)
    · have hi' := (List.all_eq_true.mp hcE.2) i (List.mem_range.mpr hi)
      simp only [Bool.and_eq_true] at hi'
      rw [eval_checked_memB (ok := fun _ => true) (fun _ _ => rfl) (64 + i) _ hi'.1.2 rfl,
          show 368 + i = 300 + (68 + i) by omega]
      exact mkSegEnv_vars_memA sp row rho s tSlots tB0 (by omega)
    · have hi' := (List.all_eq_true.mp hcE.2) i (List.mem_range.mpr hi)
      simp only [Bool.and_eq_true] at hi'
      rw [eval_checked_memB (ok := fun _ => true) (fun _ _ => rfl) (128 + i) _ hi'.2 rfl,
          show 436 + i = 300 + (136 + i) by omega]
      exact mkSegEnv_vars_memA sp row rho s tSlots tB0 (by omega)
  have hspOut : KConstsLoOpt env.sp (cfgCopy row).hasConstsLo ∗
      (TreeMem (env.sp + BitVec.ofNat 64 (cfgCopy row).offA) (cfgCopy row).lenA
        (evalMemTree env (stCopyEnd row).memA) ∗
        (TreeMem (env.sp + BitVec.ofNat 64 (cfgCopy row).offB) (cfgCopy row).lenB
          (evalMemTree env (stCopyEnd row).memB) ∗ FF)) ⊢
      Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗
        memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ ATransRowMem sp rho row ∗ F := by
    dsimp only [KConstsLoOpt, cfgCopy, FF]
    rw [emp_sepConj, show env.sp = sp from rfl,
        show sp + BitVec.ofNat 64 4272 = sp + 4272#64 from rfl, hB]
    have htmA := treeMem_entails_memRegion (ptr := sp + 4272#64)
      (evalMemTree env (stCopyEnd row).memA) (len := 204) (by decide)
    rw [show 8 * 204 = 1632 from rfl] at htmA
    exact Entails.trans (sepConj_mono_left htmA) (by sep_frame)
  refine step_bCond_seg2a (w := 320) (cond := .EQ) (disp := 0x2d80#64)
    (by omega) (by omega) (by decide +kernel) hpc3 hrun3 (fun hT => ?_) (fun hF => ?_)
  · have hr2 : row = 2 := by
      rw [hpst] at hT
      rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl
      · exact absurd hT (by decide +kernel)
      · exact absurd hT (by decide +kernel)
      · rfl
    subst hr2
    have hpcT : (s3.setPC (b + BitVec.ofNat 64 (4 * 320) + 0x2d80#64)).pc = tgt :=
      setPC_disp_eq s3 b 320 0x2d80#64 0x3280#64 (by decide +kernel)
    rcases extract_segRegInv (row := 2) (eX8 := .var 101)
      (matches_setPC hm3 _) rfl rfl rfl hcE.1.1 with ⟨hregT, hx8T, _⟩
    apply sepWP_drop_left
    refine SepWP.done hpcT (by simpa [State.setPC] using hrun3) fun hclT hroT =>
      ⟨hpcT, by simpa [State.setPC] using hrun3, hclT, hroT, hregT,
        by simpa [evalKExpr, env, mkSegEnv, hx8] using hx8T, tA, htA, hspOut⟩
  · have hrlt2 : (row == 2) = false := by
      rw [hpst] at hF
      rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl
      · rfl
      · rfl
      · exact absurd hF (by decide +kernel)
    have hpcF : (s3.setPC (b + BitVec.ofNat 64 (4 * (320 + 1)))).pc = tgt := by
      dsimp only [tgt]; rw [hrlt2]; exact setPC_fall_eq s3 b 320 0x0504#64 (by decide +kernel)
    rcases extract_segRegInv (row := row) (eX8 := .var 101)
      (matches_setPC hm3 _) rfl rfl rfl hcE.1.1 with ⟨hregF, hx8F, _⟩
    apply sepWP_drop_left
    refine SepWP.done hpcF (by simpa [State.setPC] using hrun3) fun hclF hroF =>
      ⟨hpcF, by simpa [State.setPC] using hrun3, hclF, hroF, hregF,
        by simpa [evalKExpr, env, mkSegEnv, hx8] using hx8F, tA, htA, hspOut⟩


/-! ## 3. Full 3-Row `Seg2` Composition (`+0x0504 .. +0x3280`) -/

private theorem memRegion_4608_split3 (sp : BitVec 64) :
    memRegion (sp + 6832#64) 4608 =
      memRegion (sp + 6832#64) 1536 ∗
      memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 1)) 1536 ∗
      memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 2)) 1536 := by
  rw [memRegion_split' (b := sp + 6832#64) (b' := sp + BitVec.ofNat 64 (6832 + 1536 * 1))
        (n := 1536) (k := (3072 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + BitVec.ofNat 64 (6832 + 1536 * 1))
        (b' := sp + BitVec.ofNat 64 (6832 + 1536 * 2))
        (n := 1536) (k := (1536 : Nat)) rfl (by bv_omega) (by decide)]

/-- Exit state and spatial layout of `Seg2` at `+0x3280`. -/
@[expose] def Seg2Exit [MlKemPlacement] (b sp : BitVec 64)
    (rho : List (BitVec 8)) (F : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  sf.pc = b + 0x3280#64 ∧ sf.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
  Seg2RegInv sp sf ∧ sf.readReg64 .x8 = 3#64 ∧
  (Pf ⊢ Seg2ConstsLo sp ∗ memRegion (sp + 96#64) 2096 ∗
    memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
    memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 13984#64) 504 ∗
    ATransMem sp rho ∗ F)

theorem seg2_safeSepWP [MlKemPlacement] {b sp : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {F : SepProp} {s : State}
    (hpc : s.pc = b + 0x0504#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg2RegInv sp s) (hx8 : s.readReg64 .x8 = 0#64) :
    SafeSepWP (blkPC03.rebase b (fun _ => none)) s
      (Seg2ConstsLo sp ∗ Seg2SeedConsts sp rho ∗
        memRegion (sp + 96#64) 240 ∗ memRegion (sp + 416#64) 1776 ∗
        memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
        memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ F)
      (Seg2Exit b sp rho F) := by
  refine SafeSepWP.of_sepWP (mid := s.pc) ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 96#64) (8 * 30) ∗
      (memRegion (sp + 416#64) (8 * 222) ∗
        (Seg2ConstsLo sp ∗ Seg2SeedConsts sp rho ∗
          memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
          memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
          memRegion (sp + 13984#64) 504 ∗ F)))
    (by rw [show 8 * 30 = 240 from rfl, show 8 * 222 = 1776 from rfl]; sep_frame) ?_
  refine sepWP_elim_treeMem (len := 30) (by decide) fun tLo => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 416#64) (8 * 222) ∗
      (TreeMem (sp + 96#64) 30 tLo ∗ Seg2ConstsLo sp ∗ Seg2SeedConsts sp rho ∗
        memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
        memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ F)) (by sep_frame) ?_
  refine sepWP_elim_treeMem (len := 222) (by decide) fun tHi => ?_
  rcases entry_memA_join sp rho tLo tHi with ⟨tA0, htA0, hjoin0⟩
  refine SepWP.done rfl hrun ?_
  have hpre0 : TreeMem (sp + 416#64) 222 tHi ∗
      (TreeMem (sp + 96#64) 30 tLo ∗ Seg2ConstsLo sp ∗ Seg2SeedConsts sp rho ∗
        memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
        memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ F) ⊢
      Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA0 ∗ memRegion (sp + 2192#64) 1512 ∗
        memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗
        (memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 0)) 1536 ∗
          (memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 1)) 1536 ∗
            memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 2)) 1536 ∗ F)) := by
    rw [memRegion_4608_split3 sp, ← hjoin0,
        show sp + BitVec.ofNat 64 (6832 + 1536 * 0) = sp + 6832#64 from rfl]
    sep_frame
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safeSepWP hb hbase hrho (row := 0) (by omega) hpc hrun hcl hro hreg hx8 htA0)
    fun sm0 Pm0 hex0 => SafeSepWP.of_sepWP <| SepWP.mono (seg2_row_copy_wp (by omega) hex0) ?_) hpre0
  rintro s1 P1 _ _ ⟨hpc1, hrun1, hcl1, hro1, hreg1, hx8_1, tA1, htA1, hP1⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safeSepWP hb hbase hrho (row := 1) (by omega) hpc1 hrun1 hcl1 hro1 hreg1 hx8_1 htA1)
    fun sm1 Pm1 hex1 => SafeSepWP.of_sepWP <| SepWP.mono (seg2_row_copy_wp (by omega) hex1) ?_)
    (Entails.trans hP1 (by sep_frame))
  rintro s2 P2 _ _ ⟨hpc2, hrun2, hcl2, hro2, hreg2, hx8_2, tA2, htA2, hP2⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safeSepWP hb hbase hrho (row := 2) (by omega) hpc2 hrun2 hcl2 hro2 hreg2 hx8_2 htA2)
    fun sm2 Pm2 hex2 => SafeSepWP.of_sepWP <| SepWP.mono (seg2_row_copy_wp (by omega) hex2) ?_)
    (Entails.trans hP2 (by sep_frame))
  rintro s3 P3 _ _ ⟨hpc3, hrun3, hcl3, hro3, hreg3, hx8_3, tA3, _, hP3⟩
  refine SafeSepWP.done ⟨hpc3, hrun3, hcl3, hro3, hreg3, hx8_3, Entails.trans hP3 ?_⟩
  have htm := treeMem_entails_memRegion (ptr := sp + 96#64) tA3 (len := 262) (by decide)
  rw [show 8 * 262 = 2096 from rfl] at htm
  unfold ATransMem
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left htm)) (by sep_frame)

theorem seg2_sepWP [MlKemPlacement] {b sp : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    {rho : List (BitVec 8)} (hrho : rho.length = 32)
    (hTerm : Shake128MatrixTerminates rho 3) {F : SepProp} {s : State}
    (hpc : s.pc = b + 0x0504#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg2RegInv sp s) (hx8 : s.readReg64 .x8 = 0#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x3280#64) s
      (Seg2ConstsLo sp ∗ Seg2SeedConsts sp rho ∗
        memRegion (sp + 96#64) 240 ∗ memRegion (sp + 416#64) 1776 ∗
        memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
        memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ F)
      (Seg2Exit b sp rho F) := by
  refine SepWP.weaken_pre (P' := memRegion (sp + 96#64) (8 * 30) ∗
      (memRegion (sp + 416#64) (8 * 222) ∗
        (Seg2ConstsLo sp ∗ Seg2SeedConsts sp rho ∗
          memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
          memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
          memRegion (sp + 13984#64) 504 ∗ F)))
    (by rw [show 8 * 30 = 240 from rfl, show 8 * 222 = 1776 from rfl]; sep_frame) ?_
  refine sepWP_elim_treeMem (len := 30) (by decide) fun tLo => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 416#64) (8 * 222) ∗
      (TreeMem (sp + 96#64) 30 tLo ∗ Seg2ConstsLo sp ∗ Seg2SeedConsts sp rho ∗
        memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
        memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
        memRegion (sp + 13984#64) 504 ∗ F)) (by sep_frame) ?_
  refine sepWP_elim_treeMem (len := 222) (by decide) fun tHi => ?_
  rcases entry_memA_join sp rho tLo tHi with ⟨tA0, htA0, hjoin0⟩
  refine SepWP.weaken_pre
    (P' := Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA0 ∗ memRegion (sp + 2192#64) 1512 ∗
      memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 12448#64) 24 ∗
      memRegion (sp + 13984#64) 504 ∗
      (memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 0)) 1536 ∗
        (memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 1)) 1536 ∗
          memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 2)) 1536 ∗ F)))
    (by
      rw [memRegion_4608_split3 sp, ← hjoin0,
          show sp + BitVec.ofNat 64 (6832 + 1536 * 0) = sp + 6832#64 from rfl]
      sep_frame) ?_
  refine SepWP.seq (seg2_row_sepWP hb hbase hrho (row := 0) (by omega)
    (fun c hc => shake128MatrixTerminates_row hrho hTerm (by omega) hc) hpc hrun hcl hro hreg hx8 htA0) ?_
  rintro sm0 Pm0 _ _ hex0
  refine SepWP.seq (seg2_row_copy_wp (by omega) hex0) ?_
  rintro s1 P1 _ _ ⟨hpc1, hrun1, hcl1, hro1, hreg1, hx8_1, tA1, htA1, hP1⟩
  refine SepWP.weaken_pre (P' := Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA1 ∗
      memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
      memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 13984#64) 504 ∗
      (memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 1)) 1536 ∗
        (ATransRowMem sp rho 0 ∗ memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 2)) 1536 ∗ F)))
    (Entails.trans hP1 (by sep_frame)) ?_
  refine SepWP.seq (seg2_row_sepWP hb hbase hrho (row := 1) (by omega)
    (fun c hc => shake128MatrixTerminates_row hrho hTerm (by omega) hc) hpc1 hrun1 hcl1 hro1 hreg1 hx8_1 htA1) ?_
  rintro sm1 Pm1 _ _ hex1
  refine SepWP.seq (seg2_row_copy_wp (row := 1) (by omega) hex1) ?_
  rintro s2 P2 _ _ ⟨hpc2, hrun2, hcl2, hro2, hreg2, hx8_2, tA2, htA2, hP2⟩
  refine SepWP.weaken_pre (P' := Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA2 ∗
      memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
      memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 13984#64) 504 ∗
      (memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * 2)) 1536 ∗
        (ATransRowMem sp rho 0 ∗ ATransRowMem sp rho 1 ∗ F)))
    (Entails.trans hP2 (by sep_frame)) ?_
  refine SepWP.seq (seg2_row_sepWP hb hbase hrho (row := 2) (by omega)
    (fun c hc => shake128MatrixTerminates_row hrho hTerm (by omega) hc) hpc2 hrun2 hcl2 hro2 hreg2 hx8_2 htA2) ?_
  rintro sm2 Pm2 _ _ hex2
  refine SepWP.mono (seg2_row_copy_wp (row := 2) (by omega) hex2) ?_
  rintro s3 P3 _ _ ⟨hpc3, hrun3, hcl3, hro3, hreg3, hx8_3, tA3, _, hP3⟩
  refine ⟨hpc3, hrun3, hcl3, hro3, hreg3, hx8_3, Entails.trans hP3 ?_⟩
  have htm := treeMem_entails_memRegion (ptr := sp + 96#64) tA3 (len := 262) (by decide)
  rw [show 8 * 262 = 2096 from rfl] at htm
  unfold ATransMem
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left htm)) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2

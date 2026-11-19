/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4 -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Row
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Clamp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5RowInit
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5RowLoop

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 5 `SampleNTT` `Âᵀ` & `memcpy` (`+0x4058 → +0x7134`)

Proves the `+0x40d8..+0x4368` row-copy epilogue, composes 3 rows of `SampleNTT` (`+0x4058..+0x7110`),
and proves the `+0x7110..+0x7134` `B28` `memcpy(sp + 5680, sp + 11856, 6176)` into both
`seg5_safe_ok` (`SafeSepWP`) and `seg5_ok` (`SepWP` under `Shake128MatrixTerminates`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl resolve_blk28 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 Shake128MatrixTerminates Shake128SeedTerminates bytesToPoly16 indCpaDecrypt
  keccakZeroState packLane64 sampleMatrixWith sampleNtt sha3_512List shake256List zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  packHalfwordsLE packHalfwordsLE_length sampleNttClassical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSepFrom MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2 (
  aTransPoly aTransPoly16 sampleMatrixWith_false_getD)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  sepWP_elim_cell8 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem Vec128At polyMem_bytesToPoly16 polyVecNat vec128At_eq_pointsToBytes
  vecRangeBytes vecRangeBytes_length vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KCfg KEnv KExpr KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (
  TreeMem btreeOfWords btreeOfWords_get btreeWords btreeWords_eq_of_get bytesToWords
  bytesToWords_getD bytesToWords_length memRegion_entails_exists_treeMem packWordAt
  pointsToBytes_eq_treeMem sepLoad64_treeMem treeMem_entails_memRegion
  treeMem_eq_pointsToBytes treeMem_split wordsToBytes wordsToBytes_bytesToWords zeroTree9)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KCfgWf KSpatial KStateMatches matches_advancePC matches_setPC matches_writeGpr setPC_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  eval_checked_gpr eval_checked_memB eval_checked_pstate rowSeed rowSeed_eq_of_len32 rowSeeds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (keccakRc_intro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp (
  eq_some_getD sepWP_drop_left)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit (
  checkPStateEq pc_add_eq setPC_disp_w_eq setPC_fall_w_eq status_setPC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Row (
  readReg64_setPC sepWP_mono_pre)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  SavedFrame04 blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  WordRangeMem modTHatPoly16 msgWordFn)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4b (offSeg4End)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4 (Seg4Spatial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (fetchWordTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Loop (
  fetch_blk04_seg5 runKRange04 sepWP_of_runKRange04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Init (
  Seg5ConstWordsInv Seg5RegInv Seg5RowDone entry_treeMem04_join exit_treeMem04_entails
  offSeg5Entry offSeg5Memset seg5_prologue step_bCond_seg5)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5Clamp (
  checkSegRegGprs04 extract_segRegInv04 mkSegBaseState04 mkSegEnv04 mkSegState04
  mkSegState04_matches with_frozen_env04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5RowLoop (
  offRowEntry04 seg5_row_ok seg5_row_safe_ok)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x7110 → 0x7134]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

private theorem blk28_memcpy_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk28_memcpy_ok

attribute [local irreducible] blkPC04

/-! ## 1. Transposed `SampleNTT` Matrix Predicates (`ATransRowMemAt`, `ATransMemAt`) & Spatial Bridges -/

private theorem sampleNttClassical_eq (seed34 : List (BitVec 8)) :
    sampleNttClassical seed34 = sampleNtt seed34 := by
  unfold sampleNttClassical sampleNtt
  by_cases h : Shake128SeedTerminates seed34 <;> simp [h]

private theorem shake128MatrixTerminates_row {rho : List (BitVec 8)} (hrho : rho.length = 32)
    (hTerm : Shake128MatrixTerminates rho 3) {row col : Nat} (hr : row < 3) (hc : col < 3) :
    Shake128SeedTerminates (rowSeeds rho row col) := by
  have h := hTerm row col hr hc
  have htake : rho.take 32 = rho := List.take_of_length_le (Nat.le_of_eq hrho)
  simpa [rowSeeds, rowSeed, htake] using h

attribute [local irreducible] sampleNtt

@[expose] noncomputable def ATransRowMemAt (sp : BitVec 64) (baseOff : Nat)
    (rho : List (BitVec 8)) (row : Nat) : SepProp :=
  PolyMem (sp + BitVec.ofNat 64 (baseOff + 1536 * row)) (polyVecNat (aTransPoly16 rho row 0)) ∗
  PolyMem (sp + BitVec.ofNat 64 (baseOff + 1536 * row + 512)) (polyVecNat (aTransPoly16 rho row 1)) ∗
  PolyMem (sp + BitVec.ofNat 64 (baseOff + 1536 * row + 1024)) (polyVecNat (aTransPoly16 rho row 2))

@[expose] noncomputable def ATransMemAt (sp : BitVec 64) (baseOff : Nat)
    (rho : List (BitVec 8)) : SepProp :=
  ATransRowMemAt sp baseOff rho 0 ∗
  ATransRowMemAt sp baseOff rho 1 ∗
  ATransRowMemAt sp baseOff rho 2

private theorem getD_append_left {α : Type} (xs ys : List α) (d : α) {i : Nat} (hi : i < xs.length) :
    (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_right {α : Type} (xs ys : List α) (d : α) {i : Nat} (hi : xs.length ≤ i) :
    (xs ++ ys).getD i d = ys.getD (i - xs.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private theorem getD_take_lt {α : Type} (xs : List α) (n : Nat) (d : α) {i : Nat} (hi : i < n) :
    (xs.take n).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, hi]

private theorem packWordAt_slice3_04 {b0 b1 b2 : List (BitVec 8)}
    (h0 : b0.length = 544) (h1 : b1.length = 544) (_h2 : b2.length = 544) :
    (∀ i, i < 64 → packWordAt (b0 ++ (b1 ++ b2)) (8 * i) =
      packWordAt (b0.take 512) (8 * i)) ∧
    (∀ i, i < 64 → packWordAt (b0 ++ (b1 ++ b2)) (8 * (68 + i)) =
      packWordAt (b1.take 512) (8 * i)) ∧
    (∀ i, i < 64 → packWordAt (b0 ++ (b1 ++ b2)) (8 * (136 + i)) =
      packWordAt (b2.take 512) (8 * i)) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · unfold packWordAt
    have eqk : ∀ k, k < 8 → (b0 ++ (b1 ++ b2)).getD (8 * i + k) 0#8 = (b0.take 512).getD (8 * i + k) 0#8 :=
      fun k hk => by rw [getD_append_left _ _ _ (by omega), getD_take_lt _ _ _ (by omega)]
    rw [eqk 7 (by omega), eqk 6 (by omega), eqk 5 (by omega), eqk 4 (by omega),
        eqk 3 (by omega), eqk 2 (by omega), eqk 1 (by omega),
        show (b0 ++ (b1 ++ b2)).getD (8 * i) 0#8 = (b0.take 512).getD (8 * i) 0#8 from eqk 0 (by omega)]
  · unfold packWordAt
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
  · unfold packWordAt
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

private theorem multiLaneSlots3_eq_treeMem04 (sp : BitVec 64) {hws : Nat → List (BitVec 16)}
    (hlen : ∀ c, c < 3 → (hws c).length = 272) :
    let bs := packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2))
    MultiLaneSlots (sp + 5680#64) 544 3 hws =
      TreeMem (sp + 5680#64) 204 (btreeOfWords 0 (bytesToWords 204 bs) zeroTree9) := by
  intro bs
  have h0 : (packHalfwordsLE (hws 0)).length = 544 := by rw [packHalfwordsLE_length, hlen 0 (by omega)]
  have h1 : (packHalfwordsLE (hws 1)).length = 544 := by rw [packHalfwordsLE_length, hlen 1 (by omega)]
  have h2 : (packHalfwordsLE (hws 2)).length = 544 := by rw [packHalfwordsLE_length, hlen 2 (by omega)]
  have hbs : bs.length = 8 * 204 := by simp [bs, h0, h1, h2]
  rw [← pointsToBytes_eq_treeMem hbs (by decide)]
  simp only [bs, pointsToBytes_append, h0, h1, MultiLaneSlots, MultiLaneSepFrom,
    sepConj_emp, BitVec.add_assoc]
  rfl

private theorem treeMem192_eq_aTransRowMemAt (sp : BitVec 64) {rho : List (BitVec 8)}
    (hrho : rho.length = 32) (row : Nat)
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
    TreeMem (sp + BitVec.ofNat 64 (13392 + 1536 * row)) 192 tB = ATransRowMemAt sp 13392 rho row := by
  let b0 := packHalfwordsLE (hws 0)
  let b1 := packHalfwordsLE (hws 1)
  let b2 := packHalfwordsLE (hws 2)
  have hb0 : b0.length = 544 := by simp [b0, (hinv 0 (by omega)).1.1]
  have hb1 : b1.length = 544 := by simp [b1, (hinv 1 (by omega)).1.1]
  have hb2 : b2.length = 544 := by simp [b2, (hinv 2 (by omega)).1.1]
  rcases packWordAt_slice3_04 hb0 hb1 hb2 with ⟨hp0, hp1, hp2⟩
  let t12 := BTree.ofFn 9 fun i => tB.get (64 + i)
  let t2 := BTree.ofFn 9 fun i => t12.get (64 + i)
  have hgetS : ∀ j, j < 204 →
      (btreeOfWords 0 (bytesToWords 204 (b0 ++ (b1 ++ b2))) zeroTree9).get j =
        packWordAt (b0 ++ (b1 ++ b2)) (8 * j) := fun j hj => by
    have hg := btreeOfWords_get 0 (bytesToWords 204 (b0 ++ (b1 ++ b2))) zeroTree9 j
      (by rw [bytesToWords_length]; exact hj) (by rw [bytesToWords_length]; omega)
    rw [Nat.zero_add] at hg
    rw [hg, bytesToWords_getD 204 _ j hj]
  have ht0 : TreeMem (sp + BitVec.ofNat 64 (13392 + 1536 * row)) 64 tB =
      PolyMem (sp + BitVec.ofNat 64 (13392 + 1536 * row)) (polyVecNat (aTransPoly16 rho row 0)) := by
    have htake : (b0.take 512).length = 512 := by simp [hb0]
    rw [treeMem_eq_pointsToBytes (bs := b0.take 512) (by
      rw [btreeWords_eq_of_get (ws := bytesToWords 64 (b0.take 512)) (bytesToWords_length 64 _) fun i hi => by
        rw [Nat.zero_add, hB0 i hi, hgetS i (by omega), hp0 i hi, ← bytesToWords_getD 64 _ i hi]]
      exact wordsToBytes_bytesToWords 64 _ htake),
      polyMem_bytesToPoly16 _ htake, (hinv.exit_poly hd (by omega : 0 < 3)).2.2,
      sampleNttClassical_eq, rowSeeds, rowSeed_eq_of_len32 hrho]; rfl
  have ht1 : TreeMem (sp + BitVec.ofNat 64 (13392 + 1536 * row + 512)) 64 t12 =
      PolyMem (sp + BitVec.ofNat 64 (13392 + 1536 * row + 512)) (polyVecNat (aTransPoly16 rho row 1)) := by
    have htake : (b1.take 512).length = 512 := by simp [hb1]
    rw [treeMem_eq_pointsToBytes (bs := b1.take 512) (by
      rw [btreeWords_eq_of_get (ws := bytesToWords 64 (b1.take 512)) (bytesToWords_length 64 _) fun i hi => by
        rw [Nat.zero_add, BTree.get_ofFn 9 _ i (by omega), hB1 i hi, hgetS (68 + i) (by omega),
            hp1 i hi, ← bytesToWords_getD 64 _ i hi]]
      exact wordsToBytes_bytesToWords 64 _ htake),
      polyMem_bytesToPoly16 _ htake, (hinv.exit_poly hd (by omega : 1 < 3)).2.2,
      sampleNttClassical_eq, rowSeeds, rowSeed_eq_of_len32 hrho]; rfl
  have ht2 : TreeMem (sp + BitVec.ofNat 64 (13392 + 1536 * row + 1024)) 64 t2 =
      PolyMem (sp + BitVec.ofNat 64 (13392 + 1536 * row + 1024)) (polyVecNat (aTransPoly16 rho row 2)) := by
    have htake : (b2.take 512).length = 512 := by simp [hb2]
    rw [treeMem_eq_pointsToBytes (bs := b2.take 512) (by
      rw [btreeWords_eq_of_get (ws := bytesToWords 64 (b2.take 512)) (bytesToWords_length 64 _) fun i hi => by
        rw [Nat.zero_add, BTree.get_ofFn 9 _ i (by omega), BTree.get_ofFn 9 _ (64 + i) (by omega),
            show 64 + (64 + i) = 128 + i by omega, hB2 i hi, hgetS (136 + i) (by omega),
            hp2 i hi, ← bytesToWords_getD 64 _ i hi]]
      exact wordsToBytes_bytesToWords 64 _ htake),
      polyMem_bytesToPoly16 _ htake, (hinv.exit_poly hd (by omega : 2 < 3)).2.2,
      sampleNttClassical_eq, rowSeeds, rowSeed_eq_of_len32 hrho]; rfl
  rw [show (192 : Nat) = 64 + 128 from rfl,
      treeMem_split (n1 := 64) (n2 := 128) (t2 := t12) (fun i hi => BTree.get_ofFn 9 _ i (by omega)),
      show sp + BitVec.ofNat 64 (13392 + 1536 * row) + BitVec.ofNat 64 (8 * 64) =
        sp + BitVec.ofNat 64 (13392 + 1536 * row + 512) by clear *- ; bv_omega,
      show (128 : Nat) = 64 + 64 from rfl,
      treeMem_split (n1 := 64) (n2 := 64) (t2 := t2) (fun i hi => BTree.get_ofFn 9 _ i (by omega)),
      show sp + BitVec.ofNat 64 (13392 + 1536 * row + 512) + BitVec.ofNat 64 (8 * 64) =
        sp + BitVec.ofNat 64 (13392 + 1536 * row + 1024) by clear *- ; bv_omega,
      ht0, ht1, ht2]
  rfl

/-! ## 2. Row-Copy Epilogue (`+0x40d8 .. +0x4368`, `w = 4150 .. 4314`) -/

private def cfgCopy04 (row : Nat) : KCfg :=
  { offA := 5680, lenA := 204, offB := 13392 + 1536 * row, lenB := 192 }

private theorem cfgCopy04_wf {row : Nat} (hrow : row < 3) : KCfgWf (cfgCopy04 row) := by
  unfold KCfgWf cfgCopy04
  rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl <;> decide

private def stCopy0_04 : KState :=
  { mkSegBaseState04 false with gprs := (mkSegBaseState04 false).gprs.set 9 (.spAdd 13392#64) }

private def stCopyPre04 (row : Nat) : KState :=
  (runKRange04 (cfgCopy04 row) 4151 2 stCopy0_04).getD stCopy0_04

private def stCopyMid04 (row : Nat) : KState :=
  { stCopyPre04 row with gprs := (stCopyPre04 row).gprs.set 9 (.spAdd (BitVec.ofNat 64 (13392 + 1536 * row))) }

private def stCopyEnd04 (row : Nat) : KState :=
  (runKRange04 (cfgCopy04 row) 4154 160 (stCopyMid04 row)).getD (stCopyMid04 row)

private def checkCopyPre04 (st : KState) : Bool :=
  (st.gprs.get 9).beq (.spAdd 13392#64) &&
  (st.gprs.get 10).beq (.const64 1536#64) &&
  (st.gprs.get 19).beq (.var 100)

private def checkCopyEnd04 (st : KState) : Bool :=
  checkSegRegGprs04 st (.var 101) &&
  checkPStateEq st (.var 101) (.const64 3#64) &&
  ((List.range 64).all fun i =>
    (st.memB.get i).beq (.var (300 + i)) &&
    (st.memB.get (64 + i)).beq (.var (368 + i)) &&
    (st.memB.get (128 + i)).beq (.var (436 + i)))

private theorem cert_copyPre04 {row : Nat} (hrow : row < 3) :
    runKRange04 (cfgCopy04 row) 4151 2 stCopy0_04 = some (stCopyPre04 row) ∧
    checkCopyPre04 (stCopyPre04 row) = true := by
  rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl <;>
    exact ⟨eq_some_getD stCopy0_04 (by decide +kernel), by decide +kernel⟩

private theorem cert_copyEnd04 {row : Nat} (hrow : row < 3) :
    runKRange04 (cfgCopy04 row) 4154 160 (stCopyMid04 row) = some (stCopyEnd04 row) ∧
    checkCopyEnd04 (stCopyEnd04 row) = true := by
  rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl <;>
    exact ⟨eq_some_getD (stCopyMid04 _) (by decide +kernel), by decide +kernel⟩

attribute [local irreducible] stCopyPre04 stCopyEnd04

private theorem step_gpr_pure04 {prog : Program} {tgt pc : BitVec 64}
    {cfg : KCfg} {env : KEnv} {st : KState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop}
    {inst : Instr} {rd : BitVec 5} {e : KExpr} {res : BitVec 64}
    (hrd : rd.toNat < 31) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = ((s.setPC pc).writeReg64 (.gpr rd) res).advancePC)
    (hres : res = evalKExpr env e) (hm : KStateMatches env st s)
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      KStateMatches env { st with gprs := st.gprs.set rd.toNat e } s' →
      SepWP prog tgt s' (KSpatial cfg env { st with gprs := st.gprs.set rd.toNat e } F) post) :
    SepWP prog tgt s (KSpatial cfg env st F) post :=
  SepWP.step_pure hpc hrun hfetch hexec rfl
    (hnext _ rfl hrun (matches_advancePC (matches_writeGpr (matches_setPC hm pc) hrd e hres)))

private theorem eval_madd_x9_x19_x10 {prog : Program} {pc v9 v10 v19 : BitVec 64} {s : State}
    (hx9 : s.readReg64 .x9 = v9) (hx10 : s.readReg64 .x10 = v10) (hx19 : s.readReg64 .x19 = v19) :
    prog.evalInst (.dataProc3 .W64 .MADD .x9 .x19 .x10 .x9) (s.setPC pc) =
      ((s.setPC pc).writeReg64 (.gpr 9#5) (v9 + v19 * v10)).advancePC := by
  simp [Program.evalInst, execInstWithSvc, execDataProc3,
    State.readReg64, RegFile.read] at hx9 hx10 hx19 ⊢
  simp [State.setPC, hx9, hx10, hx19]

private theorem step_ldr_4150 [MlKemPlacement] {b tgt sp : BitVec 64}
    {tA : BTree (BitVec 64) 9} {Rest : SepProp} {post : State → SepProp → Prop} {s : State}
    (htA6 : tA.get 6 = sp + 13392#64)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 4150)) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hnext : ∀ s1 : State, s1 = (s.writeReg64 (.gpr 9#5) (sp + 13392#64)).setPC (b + BitVec.ofNat 64 (4 * 4151)) →
      SepWP (blkPC04.rebase b (fun _ => none)) tgt s1 (TreeMem (sp + 144#64) 264 tA ∗ Rest) post) :
    SepWP (blkPC04.rebase b (fun _ => none)) tgt s (TreeMem (sp + 144#64) 264 tA ∗ Rest) post := by
  have hfw : fetchWordTree04 4150 = some (.ldr .W64 .X64 false .x9 (.Offset .sp 192#64)) := by decide +kernel
  have hfetch := fetch_blk04_seg5 (b := b) (Or.inl ⟨by omega, by omega⟩) hfw
  have hsp_chk : checkAddrSPAligned s (.Offset .sp 192#64) = true := by
    simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_al]
  have haddr : evalAddrMode s (.Offset .sp 192#64) = (sp + 192#64, none) := by
    simp [evalAddrMode, State.readReg64, hsp]
  have hl0 : SepLoad64 (sp + 192#64) (TreeMem (sp + 144#64) 264 tA ∗ Rest) (sp + 13392#64) := by
    rw [← htA6]
    exact sepLoad64_treeMem (idx := 6) (by decide) (by decide) rfl (by bv_omega)
  have hpc4151 : b + BitVec.ofNat 64 (4 * 4150) + 4#64 = b + BitVec.ofNat 64 (4 * 4151) := by
    bv_omega
  exact SepWP.step_ldr64 hpc hrun hfetch hsp_chk haddr hl0 rfl (by
    rw [hpc4151]; exact hnext _ rfl)

private theorem step_madd_4153 [MlKemPlacement] {b tgt sp : BitVec 64} {row : Nat} (hrow : row < 3)
    {env : KEnv} {F : SepProp} {post : State → SepProp → Prop} {s : State}
    (hsp : env.sp = sp) (hv100 : env.vars 100 = BitVec.ofNat 64 row)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 4153)) (hrun : s.status = .Running)
    (hm : KStateMatches env (stCopyPre04 row) s)
    (hnext : ∀ s' : State, s'.pc = b + BitVec.ofNat 64 (4 * 4154) → s'.status = .Running →
      KStateMatches env (stCopyMid04 row) s' →
      SepWP (blkPC04.rebase b (fun _ => none)) tgt s'
        (KSpatial (cfgCopy04 row) env (stCopyMid04 row) F) post) :
    SepWP (blkPC04.rebase b (fun _ => none)) tgt s
      (KSpatial (cfgCopy04 row) env (stCopyPre04 row) F) post := by
  have hc := (cert_copyPre04 hrow).2
  simp only [checkCopyPre04, Bool.and_eq_true] at hc
  have hx9 : s.readReg64 .x9 = sp + 13392#64 := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 9#5 (by decide) (.spAdd 13392#64) hc.1.1 rfl
    simpa [evalKExpr, hsp] using h
  have hx10 : s.readReg64 .x10 = 1536#64 := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 10#5 (by decide) (.const64 1536#64) hc.1.2 rfl
    simpa [evalKExpr] using h
  have hx19 : s.readReg64 .x19 = BitVec.ofNat 64 row := by
    have h := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 19#5 (by decide) (.var 100) hc.2 rfl
    simpa [evalKExpr, hv100] using h
  have hfw : fetchWordTree04 4153 = some (.dataProc3 .W64 .MADD .x9 .x19 .x10 .x9) := by decide +kernel
  have hres : (sp + 13392#64) + BitVec.ofNat 64 row * 1536#64 =
      evalKExpr env (.spAdd (BitVec.ofNat 64 (13392 + 1536 * row))) := by
    change (sp + 13392#64) + BitVec.ofNat 64 row * 1536#64 =
      env.sp + BitVec.ofNat 64 (13392 + 1536 * row)
    rw [hsp]
    rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl <;> (clear *- ; bv_omega)
  have hpc4154 : (b + BitVec.ofNat 64 (4 * 4153)) + 4#64 = b + BitVec.ofNat 64 (4 * 4154) := by
    bv_omega
  exact step_gpr_pure04 (by decide) hpc hrun (fetch_blk04_seg5 (Or.inl ⟨by omega, by omega⟩) hfw)
    (eval_madd_x9_x19_x10 hx9 hx10 hx19) hres hm
    (fun s' hs' hrun' hm' => hnext s' (hs'.trans hpc4154) hrun' hm')

attribute [local irreducible] stCopyMid04

private theorem mkSegEnv04_var101 [MlKemPlacement] (sp fpVal : BitVec 64) (row : Nat)
    (rho : List (BitVec 8)) (s : State) (tA tB : BTree (BitVec 64) 9) :
    (mkSegEnv04 sp fpVal row rho keccakZeroState keccakZeroState keccakZeroState
      (fun _ => 0#64) s tA tB).vars 101 = s.readReg64 .x8 := by
  simp only [mkSegEnv04, Bool.false_eq_true, ↓reduceIte,
    show ¬((101 : Nat) < 25) by decide, show ¬((101 : Nat) < 50) by decide,
    show ¬((101 : Nat) < 75) by decide, show ¬((101 : Nat) < 100) by decide,
    beq_false_of_ne (show (101 : Nat) ≠ 100 by decide), beq_self_eq_true]

private theorem mkSegEnv04_vars_memA [MlKemPlacement] (sp fpVal : BitVec 64) (row : Nat)
    (rho : List (BitVec 8)) (s : State) (tA tB : BTree (BitVec 64) 9) {k : Nat} (hk : k < 512) :
    (mkSegEnv04 sp fpVal row rho keccakZeroState keccakZeroState keccakZeroState
      (fun _ => 0#64) s tA tB).vars (300 + k) = tA.get k := by
  simp only [mkSegEnv04, Bool.false_eq_true, ↓reduceIte,
    show ¬(300 + k < 25) by omega, show ¬(300 + k < 50) by omega,
    show ¬(300 + k < 75) by omega, show ¬(300 + k < 100) by omega,
    beq_false_of_ne (show 300 + k ≠ 100 by omega), beq_false_of_ne (show 300 + k ≠ 101 by omega),
    beq_false_of_ne (show 300 + k ≠ 102 by omega), beq_false_of_ne (show 300 + k ≠ 103 by omega),
    beq_false_of_ne (show 300 + k ≠ 104 by omega), beq_false_of_ne (show 300 + k ≠ 105 by omega),
    beq_false_of_ne (show 300 + k ≠ 106 by omega),
    show ¬(300 + k < 174) by omega, show ¬(300 + k < 232) by omega,
    show 300 + k < 812 by omega, show 300 + k - 300 = k by omega]

private theorem seg5_row_copy_wp [MlKemPlacement] {b sp fpVal : BitVec 64}
    {rho : List (BitVec 8)} (hrho : rho.length = 32) {row : Nat} (hrow : row < 3) {F : SepProp}
    {s : State} {P : SepProp}
    (hexit : Seg5RowDone b sp fpVal rho row
      (memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * row)) 1536 ∗ F) s P) :
    let tgt := if row == 2 then b + BitVec.ofNat 64 (4 * 7236) else b + offRowEntry04
    SepWP (blkPC04.rebase b (fun _ => none)) tgt s P
      (fun sf Pf =>
        sf.pc = tgt ∧ sf.status = .Running ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg5RegInv sp fpVal sf ∧ sf.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧
        ∃ tA : BTree (BitVec 64) 9,
          Seg5ConstWordsInv sp rho tA ∧
          (Pf ⊢ TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
            memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
            memRegion (sp + 19168#64) 24 ∗ ATransRowMemAt sp 13392 rho row ∗ F)) := by
  intro tgt
  rcases hexit with ⟨hpc, hrun, hcl, hro, hreg, hx8, hx19,
    extra, tA, sampled, hws, hdone, hinv, htA, hP⟩
  let tSlots := btreeOfWords 0 (bytesToWords 204
    (packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2)))) zeroTree9
  have hSlots : MultiLaneSlots (sp + 5680#64) 544 3 hws = TreeMem (sp + 5680#64) 204 tSlots :=
    multiLaneSlots3_eq_treeMem04 sp fun c hc => (hinv c hc).1.1
  let Rest0 := TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
    TreeMem (sp + 5680#64) 204 tSlots ∗ memRegion (sp + 20704#64) 504 ∗
    memRegion (sp + 19168#64) 24 ∗ F
  refine sepWP_mono_pre (Entails.trans (by rw [hSlots] at hP; exact hP)
    (Entails.trans (by dsimp only [Rest0]; rw [show (1536 : Nat) = 8 * 192 from rfl]; sep_frame :
      _ ⊢ memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * row)) (8 * 192) ∗ Rest0)
      (sepConj_mono_left (memRegion_entails_exists_treeMem (len := 192) (by decide))))) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro tB0
  refine with_frozen_env04 hcl hro ?_
  refine SepWP.congr_pre (P1 := TreeMem (sp + 144#64) 264 tA ∗
      (TreeMem (sp + 5680#64) 204 tSlots ∗ TreeMem (sp + BitVec.ofNat 64 (13392 + 1536 * row)) 192 tB0 ∗
        memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
        memRegion (sp + 19168#64) 24 ∗ F))
    (by dsimp only [Rest0]; apply sepProp_ext <;> sep_frame) ?_
  refine step_ldr_4150 htA.2.2.2.2.2.1 hpc hrun hreg.1 hreg.2.1 fun sL hsL => ?_
  refine keccakRc_intro (by rw [hsL]; simpa [State.setPC, State.writeReg64] using hro) ?_
  let env := mkSegEnv04 sp fpVal row rho keccakZeroState keccakZeroState keccakZeroState
    (fun _ => 0#64) s tSlots tB0
  rcases mkSegState04_matches (cfg := cfgCopy04 row) (hasConsts := false) (slots01 := []) (slots2 := [])
    (rho := rho) (k0 := keccakZeroState) (k1 := keccakZeroState) (k2 := keccakZeroState)
    (k2Hi := fun _ => 0#64) (tA := tSlots) (tB := tB0) (by decide) (by decide) hreg hx19
    (fun h => Bool.noConfusion h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    with ⟨hmBase, htA_eq, htB_eq⟩
  have hm0 : KStateMatches env stCopy0_04 sL := by
    rw [hsL]; unfold stCopy0_04
    exact matches_setPC (matches_writeGpr (rd := 9#5) hmBase (by decide) (.spAdd 13392#64)
      (by simp [evalKExpr, mkSegEnv04])) _
  let FF := TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
    memRegion (sp + 20704#64) 504 ∗ memRegion (sp + 19168#64) 24 ∗ F
  refine SepWP.congr_pre (P1 := KSpatial (cfgCopy04 row) env stCopy0_04 FF)
    (by
      have hmA : (mkSegBaseState04 false).memA =
          (mkSegState04 (cfgCopy04 row) false [] []).memA := rfl
      have hmB : (mkSegBaseState04 false).memB =
          (mkSegState04 (cfgCopy04 row) false [] []).memB := rfl
      dsimp only [KSpatial, cfgCopy04, stCopy0_04, env, FF] at htA_eq htB_eq hmA hmB ⊢
      rw [hmA, hmB, htA_eq, htB_eq]
      change (mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" ↦ᵣ
          mlkemData01Bytes) ∗
        TreeMem (sp + 5680#64) 204 tSlots ∗
        TreeMem (sp + BitVec.ofNat 64 (13392 + 1536 * row)) 192 tB0 ∗
        TreeMem (sp + 144#64) 264 tA ∗
        memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
        memRegion (sp + 19168#64) 24 ∗ F = _
      apply sepProp_ext <;> sep_frame) ?_
  refine sepWP_of_runKRange04 (cfgCopy04_wf hrow) (show (0 : Nat) < 24 by decide)
    (fun k hk => Or.inl ⟨by omega, by omega⟩) (cert_copyPre04 hrow).1
    (by rw [hsL]; rfl) (by rw [hsL]; simpa [State.setPC, State.writeReg64] using hrun) hm0
    fun s1 hpc1 hrun1 hm1 => ?_
  refine step_madd_4153 hrow (sp := sp) rfl rfl hpc1 hrun1 hm1 fun s2 hpc2 hrun2 hm2 => ?_
  refine sepWP_of_runKRange04 (cfgCopy04_wf hrow) (show (0 : Nat) < 24 by decide)
    (fun k hk => Or.inl ⟨by omega, by omega⟩) (cert_copyEnd04 hrow).1
    hpc2 hrun2 hm2 fun s3 hpc3 hrun3 hm3 => ?_
  have hcE := (cert_copyEnd04 hrow).2
  simp only [checkCopyEnd04, Bool.and_eq_true] at hcE
  have hpst : s3.pstate = (AddWithCarry64 (BitVec.ofNat 64 (row + 1)) (~~~3#64) true).2 := by
    have hp := eval_checked_pstate (ok := fun _ => true) hm3 (fun _ _ => rfl)
      (.var 101) (.const64 3#64) hcE.1.2 rfl rfl
    dsimp only [evalKExpr, env] at hp
    rw [mkSegEnv04_var101, hx8] at hp
    exact hp
  have hB : TreeMem (sp + BitVec.ofNat 64 (13392 + 1536 * row)) 192
      ((stCopyEnd04 row).memB.map (evalKExpr env)) = ATransRowMemAt sp 13392 rho row := by
    refine treeMem192_eq_aTransRowMemAt sp hrho row hdone hinv _
      (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
    · have hi' := (List.all_eq_true.mp hcE.2) i (List.mem_range.mpr hi)
      simp only [Bool.and_eq_true] at hi'
      rw [eval_checked_memB (ok := fun _ => true) (fun _ _ => rfl) i _ hi'.1.1 rfl]
      exact mkSegEnv04_vars_memA sp fpVal row rho s tSlots tB0 (by omega)
    · have hi' := (List.all_eq_true.mp hcE.2) i (List.mem_range.mpr hi)
      simp only [Bool.and_eq_true] at hi'
      rw [eval_checked_memB (ok := fun _ => true) (fun _ _ => rfl) (64 + i) _ hi'.1.2 rfl,
          show 368 + i = 300 + (68 + i) by omega]
      exact mkSegEnv04_vars_memA sp fpVal row rho s tSlots tB0 (by omega)
    · have hi' := (List.all_eq_true.mp hcE.2) i (List.mem_range.mpr hi)
      simp only [Bool.and_eq_true] at hi'
      rw [eval_checked_memB (ok := fun _ => true) (fun _ _ => rfl) (128 + i) _ hi'.2 rfl,
          show 436 + i = 300 + (136 + i) by omega]
      exact mkSegEnv04_vars_memA sp fpVal row rho s tSlots tB0 (by omega)
  have hspOut : TreeMem (env.sp + BitVec.ofNat 64 (cfgCopy04 row).offA) (cfgCopy04 row).lenA
        ((stCopyEnd04 row).memA.map (evalKExpr env)) ∗
      TreeMem (env.sp + BitVec.ofNat 64 (cfgCopy04 row).offB) (cfgCopy04 row).lenB
        ((stCopyEnd04 row).memB.map (evalKExpr env)) ∗ FF ⊢
      TreeMem (sp + 144#64) 264 tA ∗ memRegion (sp + 22400#64) 1512 ∗
        memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
        memRegion (sp + 19168#64) 24 ∗ ATransRowMemAt sp 13392 rho row ∗ F := by
    dsimp only [cfgCopy04, FF]
    rw [show env.sp = sp from rfl, show sp + BitVec.ofNat 64 5680 = sp + 5680#64 from rfl, hB]
    have htmA := treeMem_entails_memRegion (ptr := sp + 5680#64)
      ((stCopyEnd04 row).memA.map (evalKExpr env)) (len := 204) (by decide)
    rw [show 8 * 204 = 1632 from rfl] at htmA
    exact Entails.trans (sepConj_mono_left htmA) (by sep_frame)
  refine step_bCond_seg5 (w := 4314) (cond := .EQ) (disp := BitVec.ofNat 64 11688)
    (Or.inl ⟨by omega, by omega⟩) (by decide +kernel) hpc3 hrun3 (fun hT => ?_) (fun hF => ?_)
  · have hr2 : row = 2 := by
      rw [hpst] at hT
      rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl
      · exact absurd hT (by decide +kernel)
      · exact absurd hT (by decide +kernel)
      · rfl
    subst hr2
    have hpcT : (s3.setPC (b + BitVec.ofNat 64 (4 * 4314) + BitVec.ofNat 64 11688)).pc = tgt :=
      setPC_disp_w_eq s3 b 4314 (BitVec.ofNat 64 11688) 7236 (by decide +kernel)
    rcases extract_segRegInv04 (row := 2) (eX8 := .var 101)
      (matches_setPC hm3 _) rfl rfl rfl rfl hcE.1.1 with ⟨hregT, hx8T, _⟩
    apply sepWP_drop_left
    refine SepWP.done hpcT (by simpa [State.setPC] using hrun3) fun hclT hroT =>
      ⟨hpcT, by simpa [State.setPC] using hrun3, hclT, hroT, hregT,
        by simpa [evalKExpr, env, mkSegEnv04, hx8] using hx8T, tA, htA, hspOut⟩
  · have hrlt2 : (row == 2) = false := by
      rw [hpst] at hF
      rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl
      · rfl
      · rfl
      · exact absurd hF (by decide +kernel)
    have hpcF : (s3.setPC (b + BitVec.ofNat 64 (4 * (4314 + 1)))).pc = tgt := by
      dsimp only [tgt, offRowEntry04]; rw [hrlt2]
      exact setPC_fall_w_eq s3 b 4314 4315 (by decide +kernel)
    rcases extract_segRegInv04 (row := row) (eX8 := .var 101)
      (matches_setPC hm3 _) rfl rfl rfl rfl hcE.1.1 with ⟨hregF, hx8F, _⟩
    apply sepWP_drop_left
    refine SepWP.done hpcF (by simpa [State.setPC] using hrun3) fun hclF hroF =>
      ⟨hpcF, by simpa [State.setPC] using hrun3, hclF, hroF, hregF,
        by simpa [evalKExpr, env, mkSegEnv04, hx8] using hx8F, tA, htA, hspOut⟩

/-! ## 3. `+0x4058 → +0x7134` Full `Seg5` Composition & `B28` `memcpy(sp + 5680, sp + 11856, 6176)` -/

@[expose] def offSeg5End : BitVec 64 := BitVec.ofNat 64 (4 * 7245)

@[expose] noncomputable def Seg5Spatial (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 25824#64
  let ct := ct1 ++ ct2
  let m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
  let rho := (dk.drop 2304).take 32
  let hPk := (dk.drop 2336).take 32
  let z := (dk.drop 2368).take 32
  let pk0 := (dk.drop 1152).take 384
  let pk1 := (dk.drop 1536).take 384
  let pk2 := (dk.drop 1920).take 384
  stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗
  memRegion sp 8 ∗ WordRangeMem 32 (sp + 8#64) (msgWordFn m') ∗
  ((sp + 136#64) ↦₆₄ ret) ∗ memRegion (sp + 144#64) 2112 ∗
  ((sp + 2256#64) ↦ₛ ct) ∗ ((sp + 3344#64) ↦ₛ ct) ∗ memRegion (sp + 4432#64) 64 ∗
  ((sp + 4496#64) ↦ₛ sha3_512List (m' ++ hPk)) ∗
  memRegion (sp + 4560#64) 1120 ∗
  PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk0)) ∗
  PolyMem (sp + 6192#64) (polyVecNat (modTHatPoly16 pk1)) ∗
  PolyMem (sp + 6704#64) (polyVecNat (modTHatPoly16 pk2)) ∗
  ATransMemAt sp 7216 rho ∗
  memRegion (sp + 11824#64) 13792 ∗
  ((sp + 25616#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
  memRegion (sp + 25648#64) 16 ∗
  (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F

private theorem sepWP_elim_cell8_04 {prog : Program} {tgt : BitVec 64} {s : State}
    {a : BitVec 64} {R : SepProp} {post : State → SepProp → Prop}
    (h : ∀ w : BitVec 64, SepWP prog tgt s ((a ↦₆₄ w) ∗ R) post) :
    SepWP prog tgt s (memRegion a 8 ∗ R) post :=
  sepWP_elim_cell8 h

private theorem sepWP_elim_treeMem_04 {prog : Program} {tgt : BitVec 64} {s : State}
    {ptr : BitVec 64} {len : Nat} (hlen : len ≤ 512) {R : SepProp} {post : State → SepProp → Prop}
    (h : ∀ t : BTree (BitVec 64) 9, SepWP prog tgt s (TreeMem ptr len t ∗ R) post) :
    SepWP prog tgt s (memRegion ptr (8 * len) ∗ R) post := by
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_entails_exists_treeMem hlen)) ?_
  rw [sepExists_sepConj_left]; exact SepWP.exists_left h

private theorem memRegion_entry_144_208_split (sp : BitVec 64) :
    memRegion (sp + 144#64) 48 ∗ memRegion (sp + 208#64) 2048 =
      (memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
        memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
        memRegion (sp + 496#64) 32) ∗
      (memRegion (sp + 176#64) 8 ∗ memRegion (sp + 208#64) (8 * 30) ∗
        memRegion (sp + 528#64) (8 * 216)) := by
  rw [memRegion_split' (b := sp + 144#64) (b' := sp + 176#64) (n := 32) (k := (16 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 176#64) (b' := sp + 184#64) (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 208#64) (b' := sp + 448#64) (n := 240) (k := (1808 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 448#64) (b' := sp + 464#64) (n := 16) (k := (1792 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 464#64) (b' := sp + 496#64) (n := 32) (k := (1760 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 496#64) (b' := sp + 528#64) (n := 32) (k := (1728 : Nat)) rfl (by bv_omega) (by decide),
    show (240 : Nat) = 8 * 30 from rfl, show (1728 : Nat) = 8 * 216 from rfl]
  apply sepProp_ext <;> sep_frame

private theorem memRegion_5680_split (sp : BitVec 64) :
    memRegion (sp + 5680#64) 6176 =
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 :=
  memRegion_split' (b := sp + 5680#64) (b' := sp + 7312#64) (n := 1632) (k := (4544 : Nat))
    rfl (by bv_omega) (by decide)

private theorem memRegion_entry_13392_split (sp : BitVec 64) :
    memRegion (sp + 13392#64) 12224 =
      memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 0)) 1536 ∗
      memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 1)) 1536 ∗
      memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 2)) 1536 ∗
      memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗ memRegion (sp + 18000#64) 32 ∗
      (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
        memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704) := by
  rw [memRegion_split' (b := sp + 13392#64) (b' := sp + 14928#64) (n := 1536) (k := (10688 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 14928#64) (b' := sp + 16464#64) (n := 1536) (k := (9152 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 16464#64) (b' := sp + 18000#64) (n := 1536) (k := (7616 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 18000#64) (b' := sp + 18032#64) (n := 32) (k := (7584 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 18032#64) (b' := sp + 19168#64) (n := 1136) (k := (6448 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 19168#64) (b' := sp + 19192#64) (n := 24) (k := (6424 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 19192#64) (b' := sp + 20704#64) (n := 1512) (k := (4912 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 20704#64) (b' := sp + 21208#64) (n := 504) (k := (4408 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 21208#64) (b' := sp + 22400#64) (n := 1192) (k := (3216 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22400#64) (b' := sp + 23912#64) (n := 1512) (k := (1704 : Nat)) rfl (by bv_omega) (by decide),
    show sp + BitVec.ofNat 64 (13392 + 1536 * 0) = sp + 13392#64 from rfl,
    show sp + BitVec.ofNat 64 (13392 + 1536 * 1) = sp + 14928#64 from rfl,
    show sp + BitVec.ofNat 64 (13392 + 1536 * 2) = sp + 16464#64 from rfl]
  apply sepProp_ext <;> sep_frame

private def poly3Bytes (f0 f1 f2 : Nat → BitVec 128) : List (BitVec 8) :=
  vecRangeBytes 32 f0 ++ vecRangeBytes 32 f1 ++ vecRangeBytes 32 f2

private theorem poly3Bytes_length (f0 f1 f2 : Nat → BitVec 128) :
    (poly3Bytes f0 f1 f2).length = 1536 := by
  simp [poly3Bytes, vecRangeBytes_length]

private theorem poly3Mem_eq_bytes (ptr : BitVec 64) (f0 f1 f2 : Nat → BitVec 128) :
    PolyMem ptr f0 ∗ PolyMem (ptr + 512#64) f1 ∗ PolyMem (ptr + 1024#64) f2 =
      (ptr ↦ₛ poly3Bytes f0 f1 f2) := by
  unfold PolyMem poly3Bytes
  rw [vecRangeMem_eq_pointsToBytes 32 ptr f0,
    vecRangeMem_eq_pointsToBytes 32 (ptr + 512#64) f1,
    vecRangeMem_eq_pointsToBytes 32 (ptr + 1024#64) f2,
    pointsToBytes_append, pointsToBytes_append]
  simp only [List.length_append, vecRangeBytes_length,
    show ptr + BitVec.ofNat 64 (16 * 32) = ptr + 512#64 by bv_omega,
    show ptr + BitVec.ofNat 64 (16 * 32 + 16 * 32) = ptr + 1024#64 by bv_omega, sepConj_assoc]

private theorem aTransRowMemAt_eq_bytes (sp : BitVec 64) (baseOff : Nat)
    (rho : List (BitVec 8)) (row : Nat) :
    ATransRowMemAt sp baseOff rho row =
      ((sp + BitVec.ofNat 64 (baseOff + 1536 * row)) ↦ₛ
        poly3Bytes (polyVecNat (aTransPoly16 rho row 0))
          (polyVecNat (aTransPoly16 rho row 1))
          (polyVecNat (aTransPoly16 rho row 2))) := by
  unfold ATransRowMemAt
  rw [show sp + BitVec.ofNat 64 (baseOff + 1536 * row + 512) =
        (sp + BitVec.ofNat 64 (baseOff + 1536 * row)) + 512#64 by clear *- ; bv_omega,
      show sp + BitVec.ofNat 64 (baseOff + 1536 * row + 1024) =
        (sp + BitVec.ofNat 64 (baseOff + 1536 * row)) + 1024#64 by clear *- ; bv_omega]
  exact poly3Mem_eq_bytes _ _ _ _

private noncomputable def seg5Src6176Bytes (pk0 pk1 pk2 rho bs32 : List (BitVec 8)) :
    List (BitVec 8) :=
  poly3Bytes (polyVecNat (modTHatPoly16 pk0))
    (polyVecNat (modTHatPoly16 pk1)) (polyVecNat (modTHatPoly16 pk2)) ++
  poly3Bytes (polyVecNat (aTransPoly16 rho 0 0))
    (polyVecNat (aTransPoly16 rho 0 1)) (polyVecNat (aTransPoly16 rho 0 2)) ++
  poly3Bytes (polyVecNat (aTransPoly16 rho 1 0))
    (polyVecNat (aTransPoly16 rho 1 1)) (polyVecNat (aTransPoly16 rho 1 2)) ++
  poly3Bytes (polyVecNat (aTransPoly16 rho 2 0))
    (polyVecNat (aTransPoly16 rho 2 1)) (polyVecNat (aTransPoly16 rho 2 2)) ++ bs32

private theorem seg5Src6176Bytes_length {pk0 pk1 pk2 rho bs32 : List (BitVec 8)}
    (hbs32 : bs32.length = 32) :
    (seg5Src6176Bytes pk0 pk1 pk2 rho bs32).length = 6176 := by
  simp [seg5Src6176Bytes, poly3Bytes_length, hbs32]

private theorem seg5_block6176_eq (sp : BitVec 64) (baseOff : Nat)
    (pk0 pk1 pk2 rho bs32 : List (BitVec 8)) :
    PolyMem (sp + BitVec.ofNat 64 baseOff) (polyVecNat (modTHatPoly16 pk0)) ∗
      PolyMem (sp + BitVec.ofNat 64 (baseOff + 512)) (polyVecNat (modTHatPoly16 pk1)) ∗
      PolyMem (sp + BitVec.ofNat 64 (baseOff + 1024)) (polyVecNat (modTHatPoly16 pk2)) ∗
      ATransMemAt sp (baseOff + 1536) rho ∗
      ((sp + BitVec.ofNat 64 (baseOff + 6144)) ↦ₛ bs32) =
      ((sp + BitVec.ofNat 64 baseOff) ↦ₛ seg5Src6176Bytes pk0 pk1 pk2 rho bs32) := by
  unfold ATransMemAt seg5Src6176Bytes
  have hp3 := poly3Mem_eq_bytes (sp + BitVec.ofNat 64 baseOff)
    (polyVecNat (modTHatPoly16 pk0)) (polyVecNat (modTHatPoly16 pk1)) (polyVecNat (modTHatPoly16 pk2))
  rw [show sp + BitVec.ofNat 64 (baseOff + 512) = (sp + BitVec.ofNat 64 baseOff) + 512#64 by bv_omega,
    show sp + BitVec.ofNat 64 (baseOff + 1024) = (sp + BitVec.ofNat 64 baseOff) + 1024#64 by bv_omega,
    ← sepConj_assoc (PolyMem _ (polyVecNat (modTHatPoly16 pk1))),
    ← sepConj_assoc (PolyMem _ (polyVecNat (modTHatPoly16 pk0))), hp3,
    aTransRowMemAt_eq_bytes sp (baseOff + 1536) rho 0,
    aTransRowMemAt_eq_bytes sp (baseOff + 1536) rho 1,
    aTransRowMemAt_eq_bytes sp (baseOff + 1536) rho 2]
  simp only [pointsToBytes_append, List.length_append, poly3Bytes_length,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one, sepConj_assoc]
  have o1 : (sp + BitVec.ofNat 64 baseOff) + BitVec.ofNat 64 1536 =
      sp + BitVec.ofNat 64 (baseOff + 1536) := by bv_omega
  have o2 : (sp + BitVec.ofNat 64 baseOff) + BitVec.ofNat 64 (1536 + 1536) =
      sp + BitVec.ofNat 64 (baseOff + 1536 + 1536) := by bv_omega
  have o3 : (sp + BitVec.ofNat 64 baseOff) + BitVec.ofNat 64 (1536 + 1536 + 1536) =
      sp + BitVec.ofNat 64 (baseOff + 1536 + 1536 * 2) := by bv_omega
  have o4 : (sp + BitVec.ofNat 64 baseOff) + BitVec.ofNat 64 (1536 + 1536 + 1536 + 1536) =
      sp + BitVec.ofNat 64 (baseOff + 6144) := by bv_omega
  rw [o1, o2, o3, o4]

private theorem sepWP_elim_bytes32_04 {prog : Program} {tgt : BitVec 64} {s : State}
    {a : BitVec 64} {R : SepProp} {post : State → SepProp → Prop}
    (h : ∀ bs : List (BitVec 8), bs.length = 32 → SepWP prog tgt s ((a ↦ₛ bs) ∗ R) post) :
    SepWP prog tgt s (memRegion a 32 ∗ R) post := by
  rw [memRegion_eq_exists_bytes a 32 (by decide)]
  apply SepWP.of_sepExists_left; intro bs
  rw [sepConj_assoc]; apply SepWP.pure_elim; exact h bs

private theorem memRegion_exit_11824_join (sp : BitVec 64) {bs32 src6176 : List (BitVec 8)}
    (hbs32 : bs32.length = 32) (hsrc : src6176.length = 6176) :
    ((sp + 11824#64) ↦ₛ bs32) ∗ ((sp + 11856#64) ↦ₛ src6176) ∗
      memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗
      (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
        memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704) ⊢
      memRegion (sp + 11824#64) 13792 := by
  have hb1 : ((sp + 11824#64) ↦ₛ bs32) ⊢ memRegion (sp + 11824#64) 32 := by
    have h := pointsToBytes_entails_memRegion (sp + 11824#64) bs32; rwa [hbs32] at h
  have hb2 : ((sp + 11856#64) ↦ₛ src6176) ⊢ memRegion (sp + 11856#64) 6176 := by
    have h := pointsToBytes_entails_memRegion (sp + 11856#64) src6176; rwa [hsrc] at h
  refine Entails.trans (sepConj_mono hb1 (sepConj_mono_left hb2)) ?_
  rw [memRegion_split' (b := sp + 11824#64) (b' := sp + 11856#64) (n := 32) (k := (13760 : Nat)) rfl (by clear *- ; bv_omega) (by decide),
    memRegion_split' (b := sp + 11856#64) (b' := sp + 18032#64) (n := 6176) (k := (7584 : Nat)) rfl (by clear *- ; bv_omega) (by decide),
    memRegion_split' (b := sp + 18032#64) (b' := sp + 19168#64) (n := 1136) (k := (6448 : Nat)) rfl (by clear *- ; bv_omega) (by decide),
    memRegion_split' (b := sp + 19168#64) (b' := sp + 19192#64) (n := 24) (k := (6424 : Nat)) rfl (by clear *- ; bv_omega) (by decide),
    memRegion_split' (b := sp + 19192#64) (b' := sp + 20704#64) (n := 1512) (k := (4912 : Nat)) rfl (by clear *- ; bv_omega) (by decide),
    memRegion_split' (b := sp + 20704#64) (b' := sp + 21208#64) (n := 504) (k := (4408 : Nat)) rfl (by clear *- ; bv_omega) (by decide),
    memRegion_split' (b := sp + 21208#64) (b' := sp + 22400#64) (n := 1192) (k := (3216 : Nat)) rfl (by clear *- ; bv_omega) (by decide),
    memRegion_split' (b := sp + 22400#64) (b' := sp + 23912#64) (n := 1512) (k := (1704 : Nat)) rfl (by clear *- ; bv_omega) (by decide)]
  sep_frame

private theorem seg5_memcpy_wp [MlKemPlacement] {b sp fpVal : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (pk0 pk1 pk2 rho : List (BitVec 8)) (tA : BTree (BitVec 64) 9) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 7236)) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hreg : Seg5RegInv sp fpVal s) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg5End) s
      (TreeMem (sp + 144#64) 264 tA ∗
        memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
        PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
        PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
        PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
        ATransMemAt sp 13392 rho ∗ memRegion (sp + 18000#64) 32 ∗
        memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
        memRegion (sp + 19168#64) 24 ∗
        (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
          memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 11856#64 ∧
        (Pf ⊢ memRegion (sp + 144#64) 2112 ∗
          PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk0)) ∗
          PolyMem (sp + 6192#64) (polyVecNat (modTHatPoly16 pk1)) ∗
          PolyMem (sp + 6704#64) (polyVecNat (modTHatPoly16 pk2)) ∗
          ATransMemAt sp 7216 rho ∗
          memRegion (sp + 11824#64) 13792 ∗ Rest)) := by
  subst hbase
  rcases hreg with ⟨hsp, hal, hfp, _, _, _, _, _, _, _, _, _⟩
  refine SepWP.weaken_pre (P' := memRegion (sp + 18000#64) 32 ∗
    (memRegion (sp + 5680#64) 6176 ∗
      (PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
        PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
        PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
        ATransMemAt sp 13392 rho) ∗
      TreeMem (sp + 144#64) 264 tA ∗
      memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗
      (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
        memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704) ∗ Rest))
    (by rw [memRegion_5680_split sp]; sep_frame) ?_
  refine sepWP_elim_bytes32_04 fun bs32 hbs32 => ?_
  have hsrc_len := seg5Src6176Bytes_length (pk0 := pk0) (pk1 := pk1) (pk2 := pk2) (rho := rho) hbs32
  have hsrc_eq := seg5_block6176_eq sp 11856 pk0 pk1 pk2 rho bs32
  have hdst_eq := seg5_block6176_eq sp 5680 pk0 pk1 pk2 rho bs32
  refine SepWP.weaken_pre (P' :=
    memRegion (sp + 5680#64) (seg5Src6176Bytes pk0 pk1 pk2 rho bs32).length ∗
    ((sp + 11856#64) ↦ₛ seg5Src6176Bytes pk0 pk1 pk2 rho bs32) ∗
    (TreeMem (sp + 144#64) 264 tA ∗
      memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗
      (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
        memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704) ∗ Rest))
    (by
      rw [hsrc_len, show sp + 11856#64 = sp + BitVec.ofNat 64 11856 from rfl, ← hsrc_eq]
      sep_frame) ?_
  wp_steps
  wp_call (blk28_memcpy_04 blkPl04.base)
    (sp + 5680#64, sp + 11856#64, seg5Src6176Bytes pk0 pk1 pk2 rho bs32)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by dsimp only [offSeg5End]; wp_norm_lhs) ‹_›
    ⟨hsp_sf, spAligned_of_sp_eq hal hsp hsp_sf,
      by simp [*], by simp [*],
      by simpa [hsp, BitVec.add_assoc] using (show sf.readReg64 .x20 = _ by simp [*]), ?_⟩
  rw [show sp + 5680#64 = sp + BitVec.ofNat 64 5680 from rfl, ← hdst_eq]
  have htm := exit_treeMem04_entails sp tA
  have hj11824 := memRegion_exit_11824_join sp hbs32 hsrc_len
  refine Entails.trans (show _ ⊢ TreeMem (sp + 144#64) 264 tA ∗
    (((sp + 11824#64) ↦ₛ bs32) ∗ ((sp + 11856#64) ↦ₛ seg5Src6176Bytes pk0 pk1 pk2 rho bs32) ∗
      memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗
      (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
        memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704)) ∗ _ by sep_frame) ?_
  refine Entails.trans (sepConj_mono htm (sepConj_mono_left hj11824)) ?_
  sep_frame

@[expose] def Seg5Post [MlKemPlacement] (b : BitVec 64) (s0 : State)
    (ret dkA ct1A ct2A : BitVec 64) (dk ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (sf : State) (Pf : SepProp) : Prop :=
  let sp := s0.sp - 25824#64
  sf.pc = b + offSeg5End ∧
  sf.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
  MlKemRoOk mlkemMpl sf.mem ∧
  sf.sp = sp ∧ sf.spAligned = true ∧
  sf.readReg64 .fp = s0.sp - 96#64 ∧
  sf.readReg64 .x19 = 0x55555555#64 ∧
  sf.readReg64 .x20 = sp + 11856#64 ∧
  (Pf ⊢ Seg5Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)

theorem seg5_safe_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s0 s : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (hdk : dk.length = 2400)
    (hpc : s.pc = b + offSeg4End) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hsp : s.sp = s0.sp - 25824#64) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = dkA) (hx10 : s.readReg64 .x10 = 11#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 25824#64) + 16384#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 25824#64) + 20704#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 25824#64) + 5680#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 25824#64) + 20968#64) :
    SafeSepWP (blkPC04.rebase b (fun _ => none)) s
      (Seg4Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)
      (Seg5Post b s0 ret dkA ct1A ct2A dk ct1 ct2 F) := by
  set sp := s0.sp - 25824#64
  set fpVal := s0.sp - 96#64
  set ct := ct1 ++ ct2
  set m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
  set rho := (dk.drop 2304).take 32
  set hPk := (dk.drop 2336).take 32
  set z := (dk.drop 2368).take 32
  set pk0 := (dk.drop 1152).take 384
  set pk1 := (dk.drop 1536).take 384
  set pk2 := (dk.drop 1920).take 384
  have hrho : rho.length = 32 := by simp [rho, hdk]
  set R_keep := stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗
    memRegion sp 8 ∗ WordRangeMem 32 (sp + 8#64) (msgWordFn m') ∗
    ((sp + 136#64) ↦₆₄ ret) ∗ ((sp + 2256#64) ↦ₛ ct) ∗
    ((sp + 3344#64) ↦ₛ ct) ∗ memRegion (sp + 4432#64) 64 ∗
    ((sp + 4496#64) ↦ₛ sha3_512List (m' ++ hPk)) ∗
    memRegion (sp + 4560#64) 1120 ∗ ((sp + 25616#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
    memRegion (sp + 25648#64) 16 ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F
  refine SafeSepWP.of_sepWP (mid := b + offSeg5Memset) ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 176#64) 8 ∗
    (memRegion (sp + 208#64) (8 * 30) ∗ (memRegion (sp + 528#64) (8 * 216) ∗
      ((memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
          memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
          memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk)) ∗
        ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
        memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
        PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
        PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
        PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
        memRegion (sp + 13392#64) 12224 ∗ R_keep))))
    (by
      refine Entails.trans (show _ ⊢
        (memRegion (sp + 144#64) 48 ∗ memRegion (sp + 208#64) 2048) ∗
          memRegion (sp + 5680#64) 6176 ∗
          (((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
            PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
            PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
            PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
            memRegion (sp + 13392#64) 12224 ∗ (dkA ↦ₛ dk) ∗ R_keep) by
        unfold Seg4Spatial; dsimp only [sp, ct, m', hPk, z, pk0, pk1, pk2]; sep_frame) ?_
      rw [memRegion_entry_144_208_split sp, memRegion_5680_split sp]; sep_frame) ?_
  refine sepWP_elim_cell8_04 fun w4 => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 208#64) (8 * 30) ∗
    (memRegion (sp + 528#64) (8 * 216) ∗ (((sp + 176#64) ↦₆₄ w4) ∗
      (memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
        memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
        memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk)) ∗
      ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
      PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
      PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
      PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
      memRegion (sp + 13392#64) 12224 ∗ R_keep))) (by sep_frame) ?_
  refine sepWP_elim_treeMem_04 (len := 30) (by decide) fun tMid => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 528#64) (8 * 216) ∗
    (TreeMem (sp + 208#64) 30 tMid ∗ ((sp + 176#64) ↦₆₄ w4) ∗
      (memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
        memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
        memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk)) ∗
      ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
      PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
      PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
      PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
      memRegion (sp + 13392#64) 12224 ∗ R_keep)) (by sep_frame) ?_
  refine sepWP_elim_treeMem_04 (len := 216) (by decide) fun tHi => ?_
  rcases entry_treeMem04_join sp w4 rho tMid tHi with ⟨tA0, htA0, hjoin0⟩
  let Tail0 := TreeMem (sp + 528#64) 216 tHi ∗ TreeMem (sp + 208#64) 30 tMid ∗
    ((sp + 176#64) ↦₆₄ w4) ∗ ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗
    ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
    memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
    PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
    PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
    PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
    memRegion (sp + 13392#64) 12224 ∗ R_keep
  refine with_frozen_env04 hcl hro ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
    memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
    memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk) ∗ Tail0)
    (by dsimp only [Tail0]; sep_frame) ?_
  refine SepWP.mono
    (seg5_prologue hb hbase s sp fpVal dkA dk Tail0 hdk hpc hrun hsp hspA
      hfp hx9 hx10 hx23 hx26 hx27 hx28 hro) ?_
  rintro sP PP hpcP hrunP ⟨hregP, hx8P, hPP⟩ hclP hroP
  let Fixed := memRegion (sp + 7312#64) 4544 ∗
    PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
    PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
    PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
    memRegion (sp + 18000#64) 32 ∗
    (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
      memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704) ∗
    (dkA ↦ₛ dk) ∗ R_keep
  have hpre0 : PP ⊢ TreeMem (sp + 144#64) 264 tA0 ∗ memRegion (sp + 22400#64) 1512 ∗
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗
      (memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 0)) 1536 ∗
        (memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 1)) 1536 ∗
          memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 2)) 1536 ∗ Fixed)) := by
    refine Entails.trans hPP ?_
    dsimp only [Tail0, Fixed, rho] at hjoin0 ⊢
    rw [memRegion_entry_13392_split sp, ← hjoin0]; sep_frame
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg5_row_safe_ok hb hbase hrho (row := 0) (by omega) htA0 hpcP hrunP hclP hroP hregP hx8P)
    fun sm0 Pm0 hex0 => SafeSepWP.of_sepWP <| SepWP.mono (seg5_row_copy_wp hrho (by omega) hex0) ?_) hpre0
  rintro s1 P1 _ _ ⟨hpc1, hrun1, hcl1, hro1, hreg1, hx8_1, tA1, htA1, hP1⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg5_row_safe_ok hb hbase hrho (row := 1) (by omega) htA1 hpc1 hrun1 hcl1 hro1 hreg1 hx8_1)
    fun sm1 Pm1 hex1 => SafeSepWP.of_sepWP <| SepWP.mono (seg5_row_copy_wp hrho (row := 1) (by omega) hex1) ?_)
    (Entails.trans hP1 (by sep_frame))
  rintro s2 P2 _ _ ⟨hpc2, hrun2, hcl2, hro2, hreg2, hx8_2, tA2, htA2, hP2⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg5_row_safe_ok hb hbase hrho (row := 2) (by omega) htA2 hpc2 hrun2 hcl2 hro2 hreg2 hx8_2)
    fun sm2 Pm2 hex2 => SafeSepWP.of_sepWP <| SepWP.mono (seg5_row_copy_wp hrho (row := 2) (by omega) hex2) ?_)
    (Entails.trans hP2 (by sep_frame))
  rintro s3 P3 _ _ ⟨hpc3, hrun3, hcl3, hro3, hreg3, _, tA3, _, hP3⟩
  refine SafeSepWP.of_sepWP (mid := b + offSeg5End) (with_frozen_env04 hcl3 hro3 ?_)
  refine SepWP.weaken_pre (P' := TreeMem (sp + 144#64) 264 tA3 ∗
    memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
    PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
    PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
    PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
    ATransMemAt sp 13392 rho ∗ memRegion (sp + 18000#64) 32 ∗
    memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
    memRegion (sp + 19168#64) 24 ∗
    (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
      memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704) ∗
    ((dkA ↦ₛ dk) ∗ R_keep))
    (Entails.trans hP3 (by unfold ATransMemAt; sep_frame)) ?_
  refine SepWP.mono (seg5_memcpy_wp hb hbase s3 pk0 pk1 pk2 rho tA3 ((dkA ↦ₛ dk) ∗ R_keep)
    hpc3 hrun3 hcl3 hreg3) ?_
  rintro sf Pf hpcF hrunF ⟨hspF, halF, hfpF, hx19F, hx20F, hPF⟩ hclF hroF
  refine SafeSepWP.done ⟨hpcF, hrunF, hclF, hroF, hspF, halF, hfpF, hx19F, hx20F,
    Entails.trans hPF ?_⟩
  unfold Seg5Spatial; dsimp only [R_keep, sp, ct, m', rho, hPk, z, pk0, pk1, pk2]; sep_frame

theorem seg5_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s0 s : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (hdk : dk.length = 2400)
    (hTerm : Shake128MatrixTerminates ((dk.drop 2304).take 32) 3)
    (hpc : s.pc = b + offSeg4End) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hsp : s.sp = s0.sp - 25824#64) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = dkA) (hx10 : s.readReg64 .x10 = 11#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 25824#64) + 16384#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 25824#64) + 20704#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 25824#64) + 5680#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 25824#64) + 20968#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg5End) s
      (Seg4Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)
      (Seg5Post b s0 ret dkA ct1A ct2A dk ct1 ct2 F) := by
  set sp := s0.sp - 25824#64; set fpVal := s0.sp - 96#64; set ct := ct1 ++ ct2
  set m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct; set rho := (dk.drop 2304).take 32
  set hPk := (dk.drop 2336).take 32; set z := (dk.drop 2368).take 32
  set pk0 := (dk.drop 1152).take 384; set pk1 := (dk.drop 1536).take 384
  set pk2 := (dk.drop 1920).take 384
  have hrho : rho.length = 32 := by simp [rho, hdk]
  set R_keep := stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗
    memRegion sp 8 ∗ WordRangeMem 32 (sp + 8#64) (msgWordFn m') ∗
    ((sp + 136#64) ↦₆₄ ret) ∗ ((sp + 2256#64) ↦ₛ ct) ∗
    ((sp + 3344#64) ↦ₛ ct) ∗ memRegion (sp + 4432#64) 64 ∗
    ((sp + 4496#64) ↦ₛ sha3_512List (m' ++ hPk)) ∗
    memRegion (sp + 4560#64) 1120 ∗ ((sp + 25616#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
    memRegion (sp + 25648#64) 16 ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F
  refine SepWP.weaken_pre (P' := memRegion (sp + 176#64) 8 ∗
    (memRegion (sp + 208#64) (8 * 30) ∗ (memRegion (sp + 528#64) (8 * 216) ∗
      ((memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
          memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
          memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk)) ∗
        ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
        memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
        PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
        PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
        PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
        memRegion (sp + 13392#64) 12224 ∗ R_keep))))
    (by
      refine Entails.trans (show _ ⊢
        (memRegion (sp + 144#64) 48 ∗ memRegion (sp + 208#64) 2048) ∗
          memRegion (sp + 5680#64) 6176 ∗
          (((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
            PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
            PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
            PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
            memRegion (sp + 13392#64) 12224 ∗ (dkA ↦ₛ dk) ∗ R_keep) by
        unfold Seg4Spatial; dsimp only [sp, ct, m', hPk, z, pk0, pk1, pk2]; sep_frame) ?_
      rw [memRegion_entry_144_208_split sp, memRegion_5680_split sp]; sep_frame) ?_
  refine sepWP_elim_cell8_04 fun w4 => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 208#64) (8 * 30) ∗
    (memRegion (sp + 528#64) (8 * 216) ∗ (((sp + 176#64) ↦₆₄ w4) ∗
      (memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
        memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
        memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk)) ∗
      ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
      PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
      PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
      PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
      memRegion (sp + 13392#64) 12224 ∗ R_keep))) (by sep_frame) ?_
  refine sepWP_elim_treeMem_04 (len := 30) (by decide) fun tMid => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 528#64) (8 * 216) ∗
    (TreeMem (sp + 208#64) 30 tMid ∗ ((sp + 176#64) ↦₆₄ w4) ∗
      (memRegion (sp + 144#64) 32 ∗ memRegion (sp + 184#64) 8 ∗
        memRegion (sp + 448#64) 16 ∗ memRegion (sp + 464#64) 32 ∗
        memRegion (sp + 496#64) 32 ∗ (dkA ↦ₛ dk)) ∗
      ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
      PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
      PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
      PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
      memRegion (sp + 13392#64) 12224 ∗ R_keep)) (by sep_frame) ?_
  refine sepWP_elim_treeMem_04 (len := 216) (by decide) fun tHi => ?_
  rcases entry_treeMem04_join sp w4 rho tMid tHi with ⟨tA0, htA0, hjoin0⟩
  let Tail0 := TreeMem (sp + 528#64) 216 tHi ∗ TreeMem (sp + 208#64) 30 tMid ∗
    ((sp + 176#64) ↦₆₄ w4) ∗ ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗
    ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
    memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
    PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
    PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
    PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
    memRegion (sp + 13392#64) 12224 ∗ R_keep
  refine sepWP_seq_env hcl hro (mid := b + offSeg5Memset)
    (post1 := fun sP PP => Seg5RegInv sp fpVal sP ∧ sP.readReg64 .x8 = 0#64 ∧
      (PP ⊢ Vec128At (sp + 144#64) 0x000000000000000000000000001f0200#128 ∗
        Vec128At (sp + 160#64) 0x000000000000000000000000001f0100#128 ∗
        ((sp + 184#64) ↦₆₄ (sp + 22411#64)) ∗
        Vec128At (sp + 448#64) 0xffffffffffffffffffffffffff0000ff#128 ∗
        Vec128At (sp + 464#64) (packLane64 rho 24 ++ packLane64 rho 24) ∗
        Vec128At (sp + 480#64) (packLane64 rho 16 ++ packLane64 rho 16) ∗
        Vec128At (sp + 496#64) (packLane64 rho 8 ++ packLane64 rho 8) ∗
        Vec128At (sp + 512#64) (packLane64 rho 0 ++ packLane64 rho 0) ∗
        (dkA ↦ₛ dk) ∗ Tail0))
    (SepWP.weaken_pre (by dsimp only [Tail0]; sep_frame)
      (seg5_prologue hb hbase s sp fpVal dkA dk Tail0 hdk hpc hrun hsp hspA
        hfp hx9 hx10 hx23 hx26 hx27 hx28 hro)) ?_
  rintro sP PP hpcP hrunP hclP hroP ⟨hregP, hx8P, hPP⟩
  let Fixed := memRegion (sp + 7312#64) 4544 ∗
    PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
    PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
    PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
    memRegion (sp + 18000#64) 32 ∗
    (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
      memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704) ∗
    (dkA ↦ₛ dk) ∗ R_keep
  refine SepWP.weaken_pre (P' := TreeMem (sp + 144#64) 264 tA0 ∗ memRegion (sp + 22400#64) 1512 ∗
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗
      (memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 0)) 1536 ∗
        (memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 1)) 1536 ∗
          memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 2)) 1536 ∗ Fixed)))
    (Entails.trans hPP (by dsimp only [Tail0, Fixed, rho] at hjoin0 ⊢
                           rw [memRegion_entry_13392_split sp, ← hjoin0]; sep_frame)) ?_
  refine SepWP.seq (seg5_row_ok hb hbase hrho (row := 0) (by omega)
    (fun c hc => shake128MatrixTerminates_row hrho hTerm (by omega) hc)
    htA0 hpcP hrunP hclP hroP hregP hx8P) fun sm0 Pm0 _ _ hex0 => ?_
  refine SepWP.seq (seg5_row_copy_wp hrho (by omega) hex0)
    fun s1 P1 _ _ ⟨hpc1, hrun1, hcl1, hro1, hreg1, hx8_1, tA1, htA1, hP1⟩ => ?_
  refine SepWP.weaken_pre (Entails.trans hP1 (by sep_frame :
    _ ⊢ TreeMem (sp + 144#64) 264 tA1 ∗ memRegion (sp + 22400#64) 1512 ∗
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗
      (memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 1)) 1536 ∗
        (ATransRowMemAt sp 13392 rho 0 ∗
          memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 2)) 1536 ∗ Fixed)))) ?_
  refine SepWP.seq (seg5_row_ok hb hbase hrho (row := 1) (by omega)
    (fun c hc => shake128MatrixTerminates_row hrho hTerm (by omega) hc)
    htA1 hpc1 hrun1 hcl1 hro1 hreg1 hx8_1) fun sm1 Pm1 _ _ hex1 => ?_
  refine SepWP.seq (seg5_row_copy_wp hrho (row := 1) (by omega) hex1)
    fun s2 P2 _ _ ⟨hpc2, hrun2, hcl2, hro2, hreg2, hx8_2, tA2, htA2, hP2⟩ => ?_
  refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame :
    _ ⊢ TreeMem (sp + 144#64) 264 tA2 ∗ memRegion (sp + 22400#64) 1512 ∗
      memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 20704#64) 504 ∗
      memRegion (sp + 19168#64) 24 ∗
      (memRegion (sp + BitVec.ofNat 64 (13392 + 1536 * 2)) 1536 ∗
        (ATransRowMemAt sp 13392 rho 0 ∗ ATransRowMemAt sp 13392 rho 1 ∗ Fixed)))) ?_
  refine SepWP.seq (seg5_row_ok hb hbase hrho (row := 2) (by omega)
    (fun c hc => shake128MatrixTerminates_row hrho hTerm (by omega) hc)
    htA2 hpc2 hrun2 hcl2 hro2 hreg2 hx8_2) fun sm2 Pm2 _ _ hex2 => ?_
  refine SepWP.seq (seg5_row_copy_wp hrho (row := 2) (by omega) hex2)
    fun s3 P3 _ _ ⟨hpc3, hrun3, hcl3, hro3, hreg3, _, tA3, _, hP3⟩ => ?_
  refine with_frozen_env04 hcl3 hro3 ?_
  refine SepWP.weaken_pre (P' := TreeMem (sp + 144#64) 264 tA3 ∗
    memRegion (sp + 5680#64) 1632 ∗ memRegion (sp + 7312#64) 4544 ∗
    PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
    PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
    PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
    ATransMemAt sp 13392 rho ∗ memRegion (sp + 18000#64) 32 ∗
    memRegion (sp + 22400#64) 1512 ∗ memRegion (sp + 20704#64) 504 ∗
    memRegion (sp + 19168#64) 24 ∗
    (memRegion (sp + 18032#64) 1136 ∗ memRegion (sp + 19192#64) 1512 ∗
      memRegion (sp + 21208#64) 1192 ∗ memRegion (sp + 23912#64) 1704) ∗
    ((dkA ↦ₛ dk) ∗ R_keep))
    (Entails.trans hP3 (by unfold ATransMemAt; dsimp only [Fixed]; sep_frame)) ?_
  refine SepWP.mono (seg5_memcpy_wp hb hbase s3 pk0 pk1 pk2 rho tA3 ((dkA ↦ₛ dk) ∗ R_keep)
    hpc3 hrun3 hcl3 hreg3) fun sf Pf hpcF hrunF ⟨hspF, halF, hfpF, hx19F, hx20F, hPF⟩ hclF hroF =>
    ⟨hpcF, hrunF, hclF, hroF, hspF, halF, hfpF, hx19F, hx20F,
      Entails.trans hPF (by unfold Seg5Spatial; dsimp only [R_keep, sp, ct, m', rho, hPk, z, pk0, pk1, pk2]; sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5

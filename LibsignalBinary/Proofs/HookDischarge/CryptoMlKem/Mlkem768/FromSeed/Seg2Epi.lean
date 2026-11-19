/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp

/-!
# `generate_keypair_compressed` (`B05`): Segment 2 row epilogue

Proves `seg2_epi_ok` (`+0x3048 → +0x02a8`), compacting the three `544`-byte `SampleNTT` lanes
into `[sp + 17392 .. sp + 18928)` on `cfgShift` and copying the three `512`-byte polynomials
into the transposed matrix `Â` slots `[sp + 3744 + 1536 * c + 512 * row .. + 512)` (`c = 0, 1, 2`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 20000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Epi

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl resolve_blk28 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sampleNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  packHalfwordsLE packHalfwordsLE_length sampleNttClassical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSepFrom MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem polyMem_bytesToPoly16 polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05
  cell_entails_memRegion8 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (
  entails_sub sepWP_elim_bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KEnv KExpr KState evalKExpr fetchWordTree05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (
  TreeMem TreeMemFrom TreeMem_eq_pointsToWords64 btreeOfWords btreeOfWords_get btreeWords
  btreeWords_eq_of_get bytesToWords bytesToWords_getD bytesToWords_length packWordAt
  pointsToBytes_eq_treeMem pointsToWords64_eq_pointsToBytes treeMem_entails_memRegion
  treeMem_eq_pointsToBytes treeMem_split wordsToBytes wordsToBytes_bytesToWords
  wordsToBytes_length zeroTree9)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KSpatial KStateMatches)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop (
  btree_ext_get vreg128_repack)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  KProgStep eval_checked_gpr eval_checked_memA eval_checked_pstate exprVarsOk progBases
  rowSeed runAndCheckKProg sepWP_of_runAndCheckKProg specEnvSteps validSpecVar)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (
  Seg2BaseRegInv Seg2ConstWordsInv Seg2RegInv Seg2RowDone cfgShift cfgShift_wf
  keccakRc_intro step_bCond_seg2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp (sepWP_drop_left)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05 [0x3360 → 0x3480]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

private theorem blk28_memcpy_05 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC05.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC05.rebase b (fun _ => none)) blk28_memcpy_ok

attribute [local irreducible] blkLib05

/-! ## 1. `TreeMem` 3-Lane Slot-Compaction Byte Bridges -/

@[expose] def slotBytes3 (hws : Nat → List (BitVec 16)) : List (BitVec 8) :=
  packHalfwordsLE (hws 0) ++ (packHalfwordsLE (hws 1) ++ packHalfwordsLE (hws 2))

private theorem slotBytes3_length {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272) (h2 : (hws 2).length = 272) :
    (slotBytes3 hws).length = 1632 := by
  simp [slotBytes3, packHalfwordsLE_length, h0, h1, h2]

private theorem multiLaneSlots3_eq_treeMem204 (sp : BitVec 64) {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272) (h2 : (hws 2).length = 272) :
    MultiLaneSlots (sp + 17376#64) 544 3 hws =
      TreeMem (sp + 17376#64) 204 (btreeOfWords 0 (bytesToWords 204 (slotBytes3 hws)) zeroTree9) := by
  have hl0 : (packHalfwordsLE (hws 0)).length = 544 := by simp [packHalfwordsLE_length, h0]
  have hl1 : (packHalfwordsLE (hws 1)).length = 544 := by simp [packHalfwordsLE_length, h1]
  have hpts : MultiLaneSlots (sp + 17376#64) 544 3 hws = ((sp + 17376#64) ↦ₛ slotBytes3 hws) := by
    unfold slotBytes3
    rw [pointsToBytes_append, pointsToBytes_append, hl0, hl1]
    unfold MultiLaneSlots
    simp only [MultiLaneSepFrom, sepConj_emp, BitVec.add_assoc]; rfl
  rw [hpts, pointsToBytes_eq_treeMem (n := 204) (slotBytes3_length h0 h1 h2) (by decide)]

private theorem slotBytes3_getD_col {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272) (h2 : (hws 2).length = 272)
    {c i : Nat} (hc : c < 3) (hi : i < 512) :
    (slotBytes3 hws).getD (544 * c + i) 0#8 =
      ((packHalfwordsLE (hws c)).take 512).getD i 0#8 := by
  have hl0 : (packHalfwordsLE (hws 0)).length = 544 := by simp [packHalfwordsLE_length, h0]
  have hl1 : (packHalfwordsLE (hws 1)).length = 544 := by simp [packHalfwordsLE_length, h1]
  have hl2 : (packHalfwordsLE (hws 2)).length = 544 := by simp [packHalfwordsLE_length, h2]
  unfold slotBytes3
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
  · rw [Nat.mul_zero, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      List.getElem?_append_left (by omega), show 544 * 1 + i - (packHalfwordsLE (hws 0)).length = i by omega,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega),
      show 544 * 2 + i - (packHalfwordsLE (hws 0)).length - (packHalfwordsLE (hws 1)).length = i by omega,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

private theorem packWordAt_slotBytes3_col {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272) (h2 : (hws 2).length = 272)
    {c k : Nat} (hc : c < 3) (hk : k < 64) :
    packWordAt (slotBytes3 hws) (8 * (68 * c + k)) =
      packWordAt ((packHalfwordsLE (hws c)).take 512) (8 * k) := by
  unfold packWordAt
  have hbyte : ∀ j, j < 8 →
      (slotBytes3 hws).getD (8 * (68 * c + k) + j) 0#8 =
        ((packHalfwordsLE (hws c)).take 512).getD (8 * k + j) 0#8 := fun j hj => by
    rw [show 8 * (68 * c + k) + j = 544 * c + (8 * k + j) by omega]
    exact slotBytes3_getD_col h0 h1 h2 hc (by omega)
  rw [hbyte 7 (by decide), hbyte 6 (by decide), hbyte 5 (by decide), hbyte 4 (by decide),
    hbyte 3 (by decide), hbyte 2 (by decide), hbyte 1 (by decide),
    show (slotBytes3 hws).getD (8 * (68 * c + k)) 0#8 =
      ((packHalfwordsLE (hws c)).take 512).getD (8 * k) 0#8 from by simpa using hbyte 0 (by decide)]

private theorem treeMem204_compacted_split (sp : BitVec 64) {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272) (h2 : (hws 2).length = 272)
    {tOut : BTree (BitVec 64) 9}
    (hcomp : ∀ c, c < 3 → ∀ k, k < 64 →
      tOut.get (2 + 64 * c + k) =
        (btreeOfWords 0 (bytesToWords 204 (slotBytes3 hws)) zeroTree9).get (68 * c + k)) :
    TreeMem (sp + 17376#64) 204 tOut ⊢
      memRegion (sp + 17376#64) 16 ∗
      ((sp + 17392#64) ↦ₛ (packHalfwordsLE (hws 0)).take 512) ∗
      ((sp + 17904#64) ↦ₛ (packHalfwordsLE (hws 1)).take 512) ∗
      ((sp + 18416#64) ↦ₛ (packHalfwordsLE (hws 2)).take 512) ∗
      ((sp + 18928#64) ↦₆₄ tOut.get 194) ∗
      memRegion (sp + 18936#64) 72 := by
  have hcol : ∀ c (hc : c < 3) (ptr : BitVec 64) (tc : BTree (BitVec 64) 9),
      (∀ k, k < 64 → tc.get k = tOut.get (2 + 64 * c + k)) →
      TreeMem ptr 64 tc = (ptr ↦ₛ (packHalfwordsLE (hws c)).take 512) := by
    intro c hc ptr tc htc
    have hlen_c : ((packHalfwordsLE (hws c)).take 512).length = 512 := by
      rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl <;>
        simp [packHalfwordsLE_length, h0, h1, h2]
    apply treeMem_eq_pointsToBytes
    have hbw : btreeWords 0 64 tc = bytesToWords 64 ((packHalfwordsLE (hws c)).take 512) := by
      apply btreeWords_eq_of_get (bytesToWords_length _ _)
      intro k hk
      rw [Nat.zero_add, htc k hk, hcomp c hc k hk]
      have hbw0 := btreeOfWords_get 0 (bytesToWords 204 (slotBytes3 hws)) zeroTree9 (68 * c + k)
        (by rw [bytesToWords_length]; omega) (by rw [bytesToWords_length]; decide)
      rw [Nat.zero_add] at hbw0
      rw [hbw0, bytesToWords_getD 204 _ _ (by omega), bytesToWords_getD 64 _ _ hk,
        packWordAt_slotBytes3_col h0 h1 h2 hc hk]
    rw [hbw, wordsToBytes_bytesToWords 64 _ hlen_c]
  let t2 := BTree.ofFn 9 fun i => tOut.get (2 + i)
  let t66 := BTree.ofFn 9 fun i => tOut.get (66 + i)
  let t130 := BTree.ofFn 9 fun i => tOut.get (130 + i)
  let t194 := BTree.ofFn 9 fun i => tOut.get (194 + i)
  let t195 := BTree.ofFn 9 fun i => tOut.get (195 + i)
  have hs0 := treeMem_split (ptr := sp + 17376#64) (n1 := 2) (n2 := 202) (t := tOut) (t2 := t2)
    (fun i hi => BTree.get_ofFn 9 _ i (by omega))
  have hs1 := treeMem_split (ptr := sp + 17392#64) (n1 := 64) (n2 := 138) (t := t2) (t2 := t66)
    (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega), BTree.get_ofFn 9 _ (64 + i) (by omega)]; congr 1; omega)
  have hs2 := treeMem_split (ptr := sp + 17904#64) (n1 := 64) (n2 := 74) (t := t66) (t2 := t130)
    (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega), BTree.get_ofFn 9 _ (64 + i) (by omega)]; congr 1; omega)
  have hs3 := treeMem_split (ptr := sp + 18416#64) (n1 := 64) (n2 := 10) (t := t130) (t2 := t194)
    (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega), BTree.get_ofFn 9 _ (64 + i) (by omega)]; congr 1; omega)
  have hs4 := treeMem_split (ptr := sp + 18928#64) (n1 := 1) (n2 := 9) (t := t194) (t2 := t195)
    (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega), BTree.get_ofFn 9 _ (1 + i) (by omega)]; congr 1; omega)
  rw [show sp + 17376#64 + BitVec.ofNat 64 (8 * 2) = sp + 17392#64 by bv_omega] at hs0
  rw [show sp + 17392#64 + BitVec.ofNat 64 (8 * 64) = sp + 17904#64 by bv_omega] at hs1
  rw [show sp + 17904#64 + BitVec.ofNat 64 (8 * 64) = sp + 18416#64 by bv_omega] at hs2
  rw [show sp + 18416#64 + BitVec.ofNat 64 (8 * 64) = sp + 18928#64 by bv_omega] at hs3
  rw [show sp + 18928#64 + BitVec.ofNat 64 (8 * 1) = sp + 18936#64 by bv_omega] at hs4
  have hc194 : TreeMem (sp + 18928#64) 1 t194 = ((sp + 18928#64) ↦₆₄ tOut.get 194) := by
    rw [TreeMem_eq_pointsToWords64]
    change pointsToWords64 (sp + 18928#64) [t194.get 0] = _
    rw [show t194.get 0 = tOut.get 194 from BTree.get_ofFn 9 _ 0 (by decide),
      pointsToWords64_cons, pointsToWords64_nil, sepConj_emp]
  rw [hs0, hs1, hs2, hs3, hs4, hc194,
    hcol 0 (by decide) (sp + 17392#64) t2 (fun k hk => BTree.get_ofFn 9 _ k (by omega)),
    hcol 1 (by decide) (sp + 17904#64) t66 (fun k hk => BTree.get_ofFn 9 _ k (by omega)),
    hcol 2 (by decide) (sp + 18416#64) t130 (fun k hk => BTree.get_ofFn 9 _ k (by omega))]
  exact Entails.trans (sepConj_mono
    (treeMem_entails_memRegion (ptr := sp + 17376#64) (len := 2) tOut (by decide))
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (treeMem_entails_memRegion (ptr := sp + 18936#64) (len := 9) t195 (by decide))))))) (by sep_frame)

/-! ## 2. Symbolic Compaction `+0x3048 → +0x3360` on `cfgShift` (`seg2_shift_ok`) -/

private theorem treeMem_zero (ptr : BitVec 64) (t : BTree (BitVec 64) 9) :
    TreeMem ptr 0 t = emp := rfl

private theorem pc_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).pc = pc := by
  cases s; rfl

private theorem status_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := by
  cases s; rfl

private theorem readReg64_setPC' (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := by
  cases s; rfl

private def stShift0 : KState :=
  { vregs := BTree.ofFn 5 (fun vr => (.var (2 * vr), .var (2 * vr + 1)))
    gprs := BTree.ofFn 5 (fun g => .var (64 + g))
    memA := BTree.ofFn 9 (fun i => .var (200 + i))
    memB := BTree.ofFn 9 (fun _ => .const64 0#64)
    pstate := none }

private def stepsShift : List KProgStep := [.range 3090 197]

private def chkShift (ok : Nat → Bool) (st : KState) : Bool :=
  (match st.pstate with
   | some (l, r) => l.beq (.const64 0#64) && r.beq (.const64 3#64)
   | none => false) &&
  (st.gprs.get 25).beq (.const64 0#64) &&
  ([1, 19, 21, 22, 24, 26, 27, 28, 29].all fun g =>
    (st.gprs.get g).beq (.var (64 + g)) && ok (64 + g)) &&
  ((List.range 3).all fun c =>
    (List.range 64).all fun k =>
      (st.memA.get (2 + 64 * c + k)).beq (.var (200 + 68 * c + k)) &&
      ok (200 + 68 * c + k))

set_option maxRecDepth 200000 in
private theorem cert_shift :
    runAndCheckKProg cfgShift 3090 3287 3090 3287 1000 stepsShift stShift0 chkShift = true := by
  decide +kernel

private def envShift (sp rcBase : BitVec 64) (s : State) (tSlots : BTree (BitVec 64) 9) : KEnv :=
  { sp := sp, rcBase := rcBase, rLoop := 0
    vars := fun id =>
      if id < 64 then
        let v := s.readVReg128 (BitVec.ofNat 5 (id / 2))
        if id % 2 == 0 then v.truncate 64 else (v >>> 64).truncate 64
      else if id < 96 then s.readReg64 (.gpr (BitVec.ofNat 5 (id - 64)))
      else if id < 712 then tSlots.get (id - 200)
      else 0#64 }

private theorem stShift0_matches {sp rcBase : BitVec 64} {s : State} {tSlots : BTree (BitVec 64) 9}
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    KStateMatches (envShift sp rcBase s tSlots) stShift0 s ∧
      stShift0.memA.map (evalKExpr (envShift sp rcBase s tSlots)) = tSlots := by
  refine ⟨⟨hsp, hspA, ?_, ?_, fun _ _ h => by cases h⟩, ?_⟩
  · intro r
    have hr : r.toNat < 32 := r.isLt
    have hget : stShift0.vregs.get r.toNat = (.var (2 * r.toNat), .var (2 * r.toNat + 1)) := by
      dsimp only [stShift0]; exact BTree.get_ofFn 5 _ r.toNat hr
    rw [hget]
    have hlo : evalKExpr (envShift sp rcBase s tSlots) (.var (2 * r.toNat)) =
        (s.readVReg128 r).truncate 64 := by
      simp [evalKExpr, envShift, show 2 * r.toNat < 64 by omega,
        show (2 * r.toNat) / 2 = r.toNat by omega]
    have hhi : evalKExpr (envShift sp rcBase s tSlots) (.var (2 * r.toNat + 1)) =
        ((s.readVReg128 r) >>> 64).truncate 64 := by
      simp [evalKExpr, envShift, show 2 * r.toNat + 1 < 64 by omega,
        show (2 * r.toNat + 1) / 2 = r.toNat by omega,
        show (2 * r.toNat + 1) % 2 = 1 by omega]
    rw [hlo, hhi, vreg128_repack]
  · intro r _
    have hlt : r.toNat < 32 := r.isLt
    have hget : stShift0.gprs.get r.toNat = .var (64 + r.toNat) := by
      dsimp only [stShift0]; exact BTree.get_ofFn 5 _ r.toNat hlt
    rw [hget]
    simp [evalKExpr, envShift, show ¬(64 + r.toNat < 64) by omega, show 64 + r.toNat < 96 by omega]
  · apply btree_ext_get
    intro i hi
    have hi512 : i < 512 := by simpa using hi
    simp [BTree.get_map, stShift0, BTree.get_ofFn 9 _ i hi512, evalKExpr, envShift,
      show ¬(200 + i < 64) by omega, show ¬(200 + i < 96) by omega, show 200 + i < 712 by omega]

@[simp, arm64_norm, wp_norm] abbrev offEpiCopy : BitVec 64 := 6576#64 + 6576#64

private theorem seg2_shift_ok [MlKemPlacement] {b sp fpVal : BitVec 64} {row : Nat}
    {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272) (h2 : (hws 2).length = 272)
    {s0 : State} {F : SepProp}
    (hpc0 : s0.pc = b + 0x3048#64) (hrun0 : s0.status = .Running)
    (hro0 : MlKemRoOk mlkemMpl s0.mem)
    (hreg0 : Seg2RegInv sp fpVal s0)
    (hx1_0 : s0.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hx22_0 : s0.readReg64 .x22 = BitVec.ofNat 64 row) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + offEpiCopy) s0
      (MultiLaneSlots (sp + 17376#64) 544 3 hws ∗ F)
      (fun sf Pf =>
        Seg2BaseRegInv sp fpVal sf ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 row ∧
        sf.readReg64 .x25 = 0#64 ∧
        ∃ v18928 : BitVec 64,
          Pf ⊢ memRegion (sp + 17376#64) 16 ∗
            ((sp + 17392#64) ↦ₛ (packHalfwordsLE (hws 0)).take 512) ∗
            ((sp + 17904#64) ↦ₛ (packHalfwordsLE (hws 1)).take 512) ∗
            ((sp + 18416#64) ↦ₛ (packHalfwordsLE (hws 2)).take 512) ∗
            ((sp + 18928#64) ↦₆₄ v18928) ∗
            memRegion (sp + 18936#64) 72 ∗ F) := by
  let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
  let tSlots := btreeOfWords 0 (bytesToWords 204 (slotBytes3 hws)) zeroTree9
  let env0 := envShift sp rcBase s0 tSlots
  rcases hreg0 with ⟨⟨hsp0, hspA0, hfp0, hx19_0, hx21_0, hx24_0, hx26_0, hx27_0, hx28_0⟩, _, _⟩
  obtain ⟨hm0, hmemEq0⟩ := stShift0_matches (rcBase := rcBase) (tSlots := tSlots) hsp0 hspA0
  refine keccakRc_intro hro0 ?_
  have hspEq : ((rcBase ↦ᵣ mlkemData01Bytes) ∗ (MultiLaneSlots (sp + 17376#64) 544 3 hws ∗ F)) =
      KSpatial cfgShift env0 stShift0 F := by
    rw [multiLaneSlots3_eq_treeMem204 sp h0 h1 h2]
    change ((rcBase ↦ᵣ mlkemData01Bytes) ∗ (TreeMem (sp + 17376#64) 204 tSlots ∗ F)) =
      (rcBase ↦ᵣ mlkemData01Bytes) ∗
        TreeMem (sp + 17376#64) 204 (stShift0.memA.map (evalKExpr (envShift sp rcBase s0 tSlots))) ∗
        TreeMem (sp + 0#64) 0 (stShift0.memB.map (evalKExpr (envShift sp rcBase s0 tSlots))) ∗ F
    rw [hmemEq0, treeMem_zero, emp_sepConj]
  rw [hspEq]
  have hpc0' : s0.pc = b + BitVec.ofNat 64 (4 * 3090) := hpc0
  refine sepWP_of_runAndCheckKProg cfgShift_wf (env0 := env0) (show 0 < 24 by decide) cert_shift hm0
    hpc0' hrun0 ?_
  intro sf envFinal stEnd hpcF hrunF hspF hrcF _hrlF heval hmF hchk
  simp only [chkShift, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨hpst_chk, hx25_chk⟩, hgpr_chk⟩, hmem_chk⟩
  have hpst := eval_checked_pstate hmF heval (.const64 0#64) (.const64 3#64) hpst_chk rfl rfl
  dsimp only [evalKExpr] at hpst
  have hx25 := eval_checked_gpr hmF heval 25#5 (by decide) (.const64 0#64) hx25_chk rfl
  dsimp only [evalKExpr] at hx25
  have hgprPres : ∀ g ∈ ([1, 19, 21, 22, 24, 26, 27, 28, 29] : List Nat),
      (hr : g < 31) → sf.readReg64 (.gpr (BitVec.ofNat 5 g)) = s0.readReg64 (.gpr (BitVec.ofNat 5 g)) := by
    intro g hg hr
    have hall := List.all_eq_true.mp hgpr_chk g hg
    simp only [Bool.and_eq_true] at hall
    have hval := eval_checked_gpr hmF heval (BitVec.ofNat 5 g)
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hr)
      (.var (64 + g)) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hall.1)
      (by simp [exprVarsOk, hall.2])
    rw [show evalKExpr (specEnvSteps env0 stepsShift) (.var (64 + g)) =
      s0.readReg64 (.gpr (BitVec.ofNat 5 g)) from by
        dsimp only [specEnvSteps, stepsShift, evalKExpr, env0, envShift]
        simp only [show ¬(64 + g < 64) by omega, show 64 + g < 96 by omega, ↓reduceIte,
          show 64 + g - 64 = g by omega]] at hval
    exact hval
  have hcomp : ∀ c, c < 3 → ∀ k, k < 64 →
      (stEnd.memA.map (evalKExpr envFinal)).get (2 + 64 * c + k) = tSlots.get (68 * c + k) := by
    intro c hc k hk
    have hc1 := List.all_eq_true.mp hmem_chk c (List.mem_range.mpr hc)
    have hk1 := List.all_eq_true.mp hc1 k (List.mem_range.mpr hk)
    simp only [Bool.and_eq_true] at hk1
    have hm := eval_checked_memA heval (2 + 64 * c + k) (.var (200 + 68 * c + k))
      hk1.1 (by simp [exprVarsOk, hk1.2])
    rw [show evalKExpr (specEnvSteps env0 stepsShift) (.var (200 + 68 * c + k)) =
      tSlots.get (68 * c + k) from by
        dsimp only [specEnvSteps, stepsShift, evalKExpr, env0, envShift]
        simp only [show ¬(200 + 68 * c + k < 64) by omega, show ¬(200 + 68 * c + k < 96) by omega,
          show 200 + 68 * c + k < 712 by omega, ↓reduceIte,
          show 200 + 68 * c + k - 200 = 68 * c + k by omega]] at hm
    exact hm
  have hcondF : ConditionHolds .EQ (AddWithCarry64 0#64 (~~~3#64) true).2 = false := by decide
  refine step_bCond_seg2 (w := 3287) (cond := .EQ) (disp := -12468#64)
    (by decide) (by decide) (by decide +kernel) hpcF hrunF
    (fun hT => by rw [hpst, hcondF] at hT; cases hT)
    (fun _ => ?_)
  dsimp only [KSpatial, cfgShift]
  apply sepWP_drop_left
  let pcNext := b + BitVec.ofNat 64 (4 * 3288)
  have hm1 := KeccakSymBridge.matches_setPC hmF pcNext
  refine SepWP.done
    (by rw [pc_setPC']; change b + BitVec.ofNat 64 (4 * 3288) = b + offEpiCopy
        exact congrArg (b + ·) (by decide))
    ((status_setPC' sf pcNext).trans hrunF)
    ⟨⟨hm1.hsp.trans hspF, hm1.hsp_al,
      (readReg64_setPC' sf pcNext .fp).trans ((hgprPres 29 (by decide) (by decide)).trans hfp0),
      (readReg64_setPC' sf pcNext .x19).trans ((hgprPres 19 (by decide) (by decide)).trans hx19_0),
      (readReg64_setPC' sf pcNext .x21).trans ((hgprPres 21 (by decide) (by decide)).trans hx21_0),
      (readReg64_setPC' sf pcNext .x24).trans ((hgprPres 24 (by decide) (by decide)).trans hx24_0),
      (readReg64_setPC' sf pcNext .x26).trans ((hgprPres 26 (by decide) (by decide)).trans hx26_0),
      (readReg64_setPC' sf pcNext .x27).trans ((hgprPres 27 (by decide) (by decide)).trans hx27_0),
      (readReg64_setPC' sf pcNext .x28).trans ((hgprPres 28 (by decide) (by decide)).trans hx28_0)⟩,
     (readReg64_setPC' sf pcNext .x1).trans ((hgprPres 1 (by decide) (by decide)).trans hx1_0),
     (readReg64_setPC' sf pcNext .x22).trans ((hgprPres 22 (by decide) (by decide)).trans hx22_0),
     (readReg64_setPC' sf pcNext .x25).trans hx25, (stEnd.memA.map (evalKExpr envFinal)).get 194, ?_⟩
  have htree := treeMem204_compacted_split sp h0 h1 h2 hcomp
  rw [hspF, show env0.sp + BitVec.ofNat 64 17376 = sp + 17376#64 from rfl, treeMem_zero, emp_sepConj]
  exact Entails.trans (sepConj_mono_left htree) (by sep_frame)


/-! ## 3. Transposed Row Output & `3 × B28(memcpy)` Column Helpers (`+0x3360 → +0x02a8`) -/

@[expose] noncomputable def RowPolyOut (sp : BitVec 64) (rho : List (BitVec 8)) (row : Nat) : SepProp :=
  PolyMem (sp + 3744#64 + BitVec.ofNat 64 (512 * row))
    (polyVecNat ((sampleNtt (rowSeed rho row 0)).map (BitVec.ofNat 16))) ∗
  PolyMem (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row))
    (polyVecNat ((sampleNtt (rowSeed rho row 1)).map (BitVec.ofNat 16))) ∗
  PolyMem (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row))
    (polyVecNat ((sampleNtt (rowSeed rho row 2)).map (BitVec.ofNat 16)))

private def CopyGprs [MlKemPlacement] (sp fpVal x20Val : BitVec 64) (row : Nat) (s : State) : Prop :=
  Seg2BaseRegInv sp fpVal s ∧
  s.readReg64 .x20 = x20Val ∧
  s.readReg64 .x22 = sp + 3744#64 + BitVec.ofNat 64 (512 * row) ∧
  s.readReg64 .x23 = BitVec.ofNat 64 (row + 1) ∧
  s.readReg64 .x25 = 0#64

private theorem sampleNttClassical_eq_sampleNtt (seed : List (BitVec 8)) :
    sampleNttClassical seed = sampleNtt seed := rfl

attribute [local irreducible] blkPC05 TreeMem MultiLaneSlots sampleNtt sampleNttClassical polyVecNat

private abbrev off3384 : BitVec 64 := BitVec.ofNat 64 13188
private abbrev off3388 : BitVec 64 := BitVec.ofNat 64 13192
private abbrev off33a0 : BitVec 64 := BitVec.ofNat 64 13216
private abbrev off33b8 : BitVec 64 := BitVec.ofNat 64 13240
private abbrev off33e4 : BitVec 64 := BitVec.ofNat 64 13284
private abbrev off33e8 : BitVec 64 := BitVec.ofNat 64 13288
private abbrev off3400 : BitVec 64 := BitVec.ofNat 64 13312
private abbrev off3418 : BitVec 64 := BitVec.ofNat 64 13336
private abbrev off3444 : BitVec 64 := BitVec.ofNat 64 13380
private abbrev off3448 : BitVec 64 := BitVec.ofNat 64 13384
private abbrev off3460 : BitVec 64 := BitVec.ofNat 64 13408
private abbrev off3478 : BitVec 64 := BitVec.ofNat 64 13432
abbrev off02a8 : BitVec 64 := BitVec.ofNat 64 680

private theorem dst_row_shl {sp : BitVec 64} {row : Nat} (hrow : row < 3) :
    sp + 3744#64 + (BitVec.ofNat 64 row <<< 9) =
      sp + 3744#64 + BitVec.ofNat 64 (512 * row) := by
  rcases (by omega : row = 0 ∨ row = 1 ∨ row = 2) with rfl | rfl | rfl <;> bv_omega

private theorem spAligned_of_chk {s : State} {sp : BitVec 64}
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true) : s.spAligned = true := by
  simpa [State.spAligned, hsp] using hchk

private theorem sepWP_seq_cl [MlKemPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {post1 post2 : State → SepProp → Prop}
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mlkemMpl sm.mem → post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧ post1 sm Pm)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mlkemMpl m)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl h1 (fun _ _ _ _ hc hp1 => ⟨hc, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hp1⟩ => h2 sm Pm hpc hrun hc hp1)

local macro "prove_col_calls " mid1:term:arg mid2:term:arg srcAddr:term:arg dstAddr:term:arg
    sp:term:arg fpVal:term:arg row:term:arg bs:term:arg pad8:term:arg hbs:term:arg hpad:term:arg
    hsp_chk:term:arg hcl1:term:arg hg1:term:arg s1:term:arg
    Rest:term:arg : tactic => `(tactic| (
  have hlen520 : ($pad8 ++ $bs).length = 520 := by simp [$hpad:term, $hbs:term]
  have hlt512 : ($bs).length < 2 ^ 64 := by rw [$hbs:term]; omega
  have hlt520 : ($pad8 ++ $bs).length < 2 ^ 64 := by rw [hlen520]; omega
  have h520Eq9984 : (($sp + 9984#64) ↦ₛ $pad8) ∗ (($sp + 9992#64) ↦ₛ $bs) =
      (($sp + 9984#64) ↦ₛ ($pad8 ++ $bs)) := by
    rw [pointsToBytes_append, $hpad:term,
      show $sp + 9984#64 + BitVec.ofNat 64 8 = $sp + 9992#64 by bv_omega]
  have h520Eq27840 : (($sp + 27840#64) ↦ₛ ($pad8 ++ $bs)) =
      (($sp + 27840#64) ↦ₛ $pad8) ∗ (($sp + 27848#64) ↦ₛ $bs) := by
    rw [pointsToBytes_append, $hpad:term,
      show $sp + 27840#64 + BitVec.ofNat 64 8 = $sp + 27848#64 by bv_omega]
  have hcall1 : SepWP (blkPC05.rebase blkPl05.base (fun _ => none)) (blkPl05.base + $mid1) $s1
      (($srcAddr ↦ₛ $bs) ∗ (($sp + 9984#64) ↦ₛ $pad8) ∗ memRegion ($sp + 9992#64) 512 ∗
        memRegion ($sp + 27840#64) 520 ∗ memRegion $dstAddr 512 ∗ $Rest)
      (fun s2 P2 =>
        CopyGprs $sp $fpVal 1#64 $row s2 ∧
        (P2 ⊢ memRegion ($sp + 27840#64) ($pad8 ++ $bs).length ∗
          (($sp + 9984#64) ↦ₛ ($pad8 ++ $bs)) ∗
          (memRegion $srcAddr 512 ∗ memRegion $dstAddr 512 ∗ $Rest))) := by
    rcases ($hg1 : CopyGprs _ _ _ _ _) with
      ⟨⟨hsp, _, gfp, g19, g21, g24, g26, g27, g28⟩, g20, g22, g23, g25⟩
    refine SepWP.weaken_pre (P' := memRegion ($sp + 9992#64) ($bs).length ∗ ($srcAddr ↦ₛ $bs) ∗
      ((($sp + 9984#64) ↦ₛ $pad8) ∗ memRegion ($sp + 27840#64) 520 ∗ memRegion $dstAddr 512 ∗ $Rest))
      (by rw [$hbs:term]; sep_frame) ?_
    wp_step
    refine seq_codeLoaded_lr $hcl1 ?_
    wp_call (blk28_memcpy_05 blkPl05.base) ($sp + 9992#64, $srcAddr, $bs)
    apply SepWP.done (by assumption) (by assumption); intro _hcl_c1
    refine SepWP.done (by first | assumption | wp_norm_lhs) ‹_›
      ⟨⟨⟨by simp [*], spAligned_of_chk (by simp [*]) $hsp_chk:term, by simp [*], by simp [*],
         by simp [*], by simp [*], by simp [*], by simp [*], by simp [*]⟩,
        by simp [*], by simp [*], by simp [*], by simp [*]⟩, ?_⟩
    have hsrcM : ($srcAddr ↦ₛ $bs) ⊢ memRegion $srcAddr 512 := by
      have hp := pointsToBytes_entails_memRegion $srcAddr $bs; rwa [$hbs:term] at hp
    rw [hlen520, ← h520Eq9984]; exact entails_sub hsrcM (by sep_frame) (by sep_frame)
  refine sepWP_seq_cl $hcl1 hcall1 fun s2 P2 hpc2 hrun2 hcl2 ⟨hg2, hP2⟩ => ?_
  have hcall2 : SepWP (blkPC05.rebase blkPl05.base (fun _ => none)) (blkPl05.base + $mid2) s2 P2
      (fun s3 P3 =>
        CopyGprs $sp $fpVal 1#64 $row s3 ∧
        (P3 ⊢ memRegion $dstAddr ($bs).length ∗ (($sp + 27848#64) ↦ₛ $bs) ∗
          ((($sp + 27840#64) ↦ₛ $pad8) ∗ (($sp + 9984#64) ↦ₛ $pad8) ∗
            memRegion ($sp + 9992#64) 512 ∗ memRegion $srcAddr 512 ∗ $Rest))) := by
    refine SepWP.weaken_pre hP2 ?_
    rcases hg2 with ⟨⟨hsp2, _, gfp, g19, g21, g24, g26, g27, g28⟩, g20, g22, g23, g25⟩
    wp_steps 6
    refine seq_codeLoaded_lr hcl2 ?_
    wp_call (blk28_memcpy_05 blkPl05.base) ($sp + 27840#64, $sp + 9984#64, $pad8 ++ $bs)
    apply SepWP.done (by assumption) (by assumption); intro _hcl_c2
    refine SepWP.done (by first | assumption | wp_norm_lhs) ‹_›
      ⟨⟨⟨by simp [*], spAligned_of_chk (by simp [*]) $hsp_chk:term, by simp [*], by simp [*],
         by simp [*], by simp [*], by simp [*], by simp [*], by simp [*]⟩,
        by simp [*], by simp [*], by simp [*], by simp [*]⟩, ?_⟩
    have hm9992 : (($sp + 9992#64) ↦ₛ $bs) ⊢ memRegion ($sp + 9992#64) 512 := by
      have hp := pointsToBytes_entails_memRegion ($sp + 9992#64) $bs; rwa [$hbs:term] at hp
    rw [$hbs:term, ← h520Eq9984, h520Eq27840]; exact entails_sub hm9992 (by sep_frame) (by sep_frame)
  refine sepWP_seq_cl hcl2 hcall2 fun s3 P3 hpc3 hrun3 hcl3 ⟨hg3, hP3⟩ => ?_
  refine SepWP.weaken_pre hP3 ?_
  rcases hg3 with ⟨⟨hsp3, _, gfp, g19, g21, g24, g26, g27, g28⟩, g20, g22, g23, g25⟩
  wp_steps 6
  refine seq_codeLoaded_lr hcl3 ?_
  wp_call (blk28_memcpy_05 blkPl05.base) ($dstAddr, $sp + 27848#64, $bs)
  apply SepWP.done (by assumption) (by assumption); intro _hcl_c3
  refine SepWP.done (by first | assumption | wp_norm_lhs) ‹_›
    ⟨⟨⟨by simp [*], spAligned_of_chk (by simp [*]) $hsp_chk:term, by simp [*], by simp [*],
       by simp [*], by simp [*], by simp [*], by simp [*], by simp [*]⟩,
      by simp [*], by simp [*], by simp [*], by simp [*]⟩, $pad8, $hpad, ?_⟩
  have h520M : (($sp + 27840#64) ↦ₛ $pad8) ∗ (($sp + 27848#64) ↦ₛ $bs) ⊢
      memRegion ($sp + 27840#64) 520 := by
    rw [← h520Eq27840]
    have hp := pointsToBytes_entails_memRegion ($sp + 27840#64) ($pad8 ++ $bs); rwa [hlen520] at hp
  exact entails_sub h520M (by sep_frame) (by sep_frame)))

private theorem step_pre_col0 [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat}
    (hrow : row < 3) {s : State} {F : SepProp}
    (hpc : s.pc = blkPl05.base + offEpiCopy) (hrun : s.status = .Running)
    (hg : Seg2BaseRegInv sp fpVal s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 row)
    (hx25 : s.readReg64 .x25 = 0#64) :
    SepWP (blkPC05.rebase blkPl05.base (fun _ => none)) (blkPl05.base + off3384) s
      (((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗ F)
      (fun s1 P1 =>
        CopyGprs sp fpVal 1#64 row s1 ∧
        s1.readReg64 .x0 = sp + 9992#64 ∧
        s1.readReg64 .x1 = sp + 17392#64 ∧
        s1.readReg64 .x2 = 512#64 ∧
        (P1 ⊢ ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗ F)) := by
  rcases hg with ⟨hsp, hspA, hfp, hx19, hx21, hx24, hx26, hx27, hx28⟩
  wp_steps 9
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨⟨⟨by simp [*], hspA, by simp [*], by simp [*], by simp [*], by simp [*],
       by simp [*], by simp [*], by simp [*]⟩,
      by simp [*], by simpa [BitVec.add_assoc, *] using dst_row_shl (sp := sp) hrow,
      by simp [*], by simp [*]⟩,
     by simp [*]; try bv_omega, by simp [*]; try bv_omega, by simp [*], Entails.refl _⟩

private theorem step_col0 [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat}
    {bs pad8 : List (BitVec 8)} {Rest : SepProp} {s1 : State}
    (hbs : bs.length = 512) (hpad : pad8.length = 8) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = blkPl05.base + off3384) (hrun1 : s1.status = .Running)
    (hcl1 : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem)
    (hg1 : CopyGprs sp fpVal 1#64 row s1)
    (hx0_1 : s1.readReg64 .x0 = sp + 9992#64) (hx1_1 : s1.readReg64 .x1 = sp + 17392#64)
    (hx2_1 : s1.readReg64 .x2 = 512#64) :
    SepWP (blkPC05.rebase blkPl05.base (fun _ => none)) (blkPl05.base + off33b8) s1
      (((sp + 17392#64) ↦ₛ bs) ∗ ((sp + 9984#64) ↦ₛ pad8) ∗ memRegion (sp + 9992#64) 512 ∗
        memRegion (sp + 27840#64) 520 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * row)) 512 ∗ Rest)
      (fun sf Pf =>
        CopyGprs sp fpVal 1#64 row sf ∧
        ∃ pad8' : List (BitVec 8), pad8'.length = 8 ∧
          (Pf ⊢ ((sp + 3744#64 + BitVec.ofNat 64 (512 * row)) ↦ₛ bs) ∗
            memRegion (sp + 17392#64) 512 ∗ ((sp + 9984#64) ↦ₛ pad8') ∗
            memRegion (sp + 9992#64) 512 ∗ memRegion (sp + 27840#64) 520 ∗ Rest)) := by
  prove_col_calls off3388 off33a0 (sp + 17392#64) (sp + 3744#64 + BitVec.ofNat 64 (512 * row))
    sp fpVal row bs pad8 hbs hpad hsp_chk hcl1 hg1 s1 Rest

private theorem step_inter_col1 [MlKemPlacement] {sp fpVal v18928 : BitVec 64} {row : Nat}
    {s : State} {F : SepProp}
    (hpc : s.pc = blkPl05.base + off33b8) (hrun : s.status = .Running)
    (hg : CopyGprs sp fpVal 1#64 row s) :
    SepWP (blkPC05.rebase blkPl05.base (fun _ => none)) (blkPl05.base + off33e4) s
      (((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗ ((sp + 18928#64) ↦₆₄ v18928) ∗ F)
      (fun s1 P1 =>
        CopyGprs sp fpVal 1#64 row s1 ∧
        s1.readReg64 .x0 = sp + 9992#64 ∧ s1.readReg64 .x1 = sp + 17904#64 ∧
        s1.readReg64 .x2 = 512#64 ∧
        (P1 ⊢ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗ ((sp + 18928#64) ↦₆₄ 2#64) ∗ F)) := by
  rcases hg with ⟨⟨hsp, hspA, gfp, g19, g21, g24, g26, g27, g28⟩, g20, g22, g23, g25⟩
  wp_steps 11
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨⟨⟨by simp [*], hspA, by simp [*], by simp [*], by simp [*], by simp [*],
       by simp [*], by simp [*], by simp [*]⟩,
      by simp [*], by simp [*], by simp [*], by simp [*]⟩,
     by simp [*]; try bv_omega, by simp [*]; try bv_omega, by simp [*], Entails.refl _⟩

private theorem step_col1 [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat}
    {bs pad8 : List (BitVec 8)} {Rest : SepProp} {s1 : State}
    (hbs : bs.length = 512) (hpad : pad8.length = 8) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = blkPl05.base + off33e4) (hrun1 : s1.status = .Running)
    (hcl1 : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem)
    (hg1 : CopyGprs sp fpVal 1#64 row s1)
    (hx0_1 : s1.readReg64 .x0 = sp + 9992#64) (hx1_1 : s1.readReg64 .x1 = sp + 17904#64)
    (hx2_1 : s1.readReg64 .x2 = 512#64) :
    SepWP (blkPC05.rebase blkPl05.base (fun _ => none)) (blkPl05.base + off3418) s1
      (((sp + 17904#64) ↦ₛ bs) ∗ ((sp + 9984#64) ↦ₛ pad8) ∗ memRegion (sp + 9992#64) 512 ∗
        memRegion (sp + 27840#64) 520 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row)) 512 ∗ Rest)
      (fun sf Pf =>
        CopyGprs sp fpVal 1#64 row sf ∧
        ∃ pad8' : List (BitVec 8), pad8'.length = 8 ∧
          (Pf ⊢ ((sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row)) ↦ₛ bs) ∗
            memRegion (sp + 17904#64) 512 ∗ ((sp + 9984#64) ↦ₛ pad8') ∗
            memRegion (sp + 9992#64) 512 ∗ memRegion (sp + 27840#64) 520 ∗ Rest)) := by
  have ha_dst : sp + 3744#64 + BitVec.ofNat 64 (512 * row) + 1536#64 =
      sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row) := by rw [BitVec.ofNat_add]; bv_omega
  rw [← ha_dst]
  prove_col_calls off33e8 off3400 (sp + 17904#64)
    (sp + 3744#64 + BitVec.ofNat 64 (512 * row) + 1536#64)
    sp fpVal row bs pad8 hbs hpad hsp_chk hcl1 hg1 s1 Rest

private theorem step_inter_col2 [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat}
    {s : State} {F : SepProp}
    (hpc : s.pc = blkPl05.base + off3418) (hrun : s.status = .Running)
    (hg : CopyGprs sp fpVal 1#64 row s) :
    SepWP (blkPC05.rebase blkPl05.base (fun _ => none)) (blkPl05.base + off3444) s
      (((sp + 18928#64) ↦₆₄ 2#64) ∗ F)
      (fun s1 P1 =>
        CopyGprs sp fpVal 1#64 row s1 ∧
        s1.readReg64 .x0 = sp + 9992#64 ∧ s1.readReg64 .x1 = sp + 18416#64 ∧
        s1.readReg64 .x2 = 512#64 ∧
        (P1 ⊢ ((sp + 18928#64) ↦₆₄ 3#64) ∗ F)) := by
  rcases hg with ⟨⟨hsp, hspA, gfp, g19, g21, g24, g26, g27, g28⟩, g20, g22, g23, g25⟩
  wp_steps 11
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨⟨⟨by simp [*], hspA, by simp [*], by simp [*], by simp [*], by simp [*],
       by simp [*], by simp [*], by simp [*]⟩,
      by simp [*], by simp [*], by simp [*], by simp [*]⟩,
     by simp [*]; try bv_omega, by simp [*]; try bv_omega, by simp [*], Entails.refl _⟩

private theorem step_col2 [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat}
    {bs pad8 : List (BitVec 8)} {Rest : SepProp} {s1 : State}
    (hbs : bs.length = 512) (hpad : pad8.length = 8) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = blkPl05.base + off3444) (hrun1 : s1.status = .Running)
    (hcl1 : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem)
    (hg1 : CopyGprs sp fpVal 1#64 row s1)
    (hx0_1 : s1.readReg64 .x0 = sp + 9992#64) (hx1_1 : s1.readReg64 .x1 = sp + 18416#64)
    (hx2_1 : s1.readReg64 .x2 = 512#64) :
    SepWP (blkPC05.rebase blkPl05.base (fun _ => none)) (blkPl05.base + off3478) s1
      (((sp + 18416#64) ↦ₛ bs) ∗ ((sp + 9984#64) ↦ₛ pad8) ∗ memRegion (sp + 9992#64) 512 ∗
        memRegion (sp + 27840#64) 520 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row)) 512 ∗ Rest)
      (fun sf Pf =>
        CopyGprs sp fpVal 1#64 row sf ∧
        ∃ pad8' : List (BitVec 8), pad8'.length = 8 ∧
          (Pf ⊢ ((sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row)) ↦ₛ bs) ∗
            memRegion (sp + 18416#64) 512 ∗ ((sp + 9984#64) ↦ₛ pad8') ∗
            memRegion (sp + 9992#64) 512 ∗ memRegion (sp + 27840#64) 520 ∗ Rest)) := by
  have ha_dst : sp + 3744#64 + BitVec.ofNat 64 (512 * row) + 3072#64 =
      sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row) := by rw [BitVec.ofNat_add]; bv_omega
  rw [← ha_dst]
  prove_col_calls off3448 off3460 (sp + 18416#64)
    (sp + 3744#64 + BitVec.ofNat 64 (512 * row) + 3072#64)
    sp fpVal row bs pad8 hbs hpad hsp_chk hcl1 hg1 s1 Rest

private theorem step_post_col2 [MlKemPlacement] {sp fpVal : BitVec 64} {row : Nat}
    {s : State} {F : SepProp}
    (hpc : s.pc = blkPl05.base + off3478) (hrun : s.status = .Running)
    (hg : CopyGprs sp fpVal 1#64 row s) :
    SepWP (blkPC05.rebase blkPl05.base (fun _ => none)) (blkPl05.base + off02a8) s F
      (fun sf Pf =>
        Seg2BaseRegInv sp fpVal sf ∧ sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧ (Pf ⊢ F)) := by
  rcases hg with ⟨⟨hsp, hspA, gfp, g19, g21, g24, g26, g27, g28⟩, _, _, g23, _⟩
  wp_steps 2
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨⟨by simp [*], hspA, by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*]⟩, by simp [*], Entails.refl _⟩

/-! ## 4. Composed Row Epilogue `seg2_epi_ok` (`+0x3048 → +0x02a8`) -/

private theorem slots_rejoin_1632 (sp : BitVec 64) :
    memRegion (sp + 17376#64) 16 ∗ memRegion (sp + 17392#64) 512 ∗
      memRegion (sp + 17904#64) 512 ∗ memRegion (sp + 18416#64) 512 ∗
      ((sp + 18928#64) ↦₆₄ 3#64) ∗ memRegion (sp + 18936#64) 72 ⊢
      memRegion (sp + 17376#64) 1632 := by
  have h8 : ((sp + 18928#64) ↦₆₄ 3#64) ⊢ memRegion (sp + 18928#64) 8 :=
    cell_entails_memRegion8 (sp + 18928#64) 3#64
  have hmr : memRegion (sp + 17376#64) 1632 =
      memRegion (sp + 17376#64) 16 ∗ memRegion (sp + 17392#64) 512 ∗
        memRegion (sp + 17904#64) 512 ∗ memRegion (sp + 18416#64) 512 ∗
        memRegion (sp + 18928#64) 8 ∗ memRegion (sp + 18936#64) 72 := by
    rw [memRegion_split' (b := sp + 17376#64) (b' := sp + 17392#64) (n := 16) (k := (1616 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 17392#64) (b' := sp + 17904#64) (n := 512) (k := (1104 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 17904#64) (b' := sp + 18416#64) (n := 512) (k := (592 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 18416#64) (b' := sp + 18928#64) (n := 512) (k := (80 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 18928#64) (b' := sp + 18936#64) (n := 8) (k := (72 : Nat)) rfl (by bv_omega) (by decide)]
  rw [hmr]
  exact entails_sub h8 (by sep_frame) (by sep_frame)

set_option maxRecDepth 4096 in
theorem seg2_epi_ok [MlKemPlacement] {b sp fpVal : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp} (hrow : row < 3)
    {s : State} {P : SepProp}
    (hexit : Seg2RowDone b sp fpVal rho row
      (((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
        memRegion (sp + 28344#64) 16 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * row)) 512 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row)) 512 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row)) 512 ∗ Rest) s P) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off02a8) s P
      (fun sf Pf =>
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg2BaseRegInv sp fpVal sf ∧ sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
        ∃ tA : BTree (BitVec 64) 9, Seg2ConstWordsInv sp rho tA ∧
          (Pf ⊢ RowPolyOut sp rho row ∗
            ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
            TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗
            memRegion (sp + 17376#64) 1632 ∗ memRegion (sp + 27840#64) 504 ∗
            memRegion (sp + 28344#64) 16 ∗ memRegion (sp + 29024#64) 24 ∗ Rest)) := by
  subst hbase
  rcases hexit with ⟨hpc0, hrun0, hcl0, hro0, hreg0, hx1_0, hx22_0,
    extra, tA, sampled, hws, hd, hinv, htA, hP0⟩
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hreg0.1.1] using hreg0.1.2.1
  have hl0 : (hws 0).length = 272 := (hinv 0 (by decide)).1.1
  have hl1 : (hws 1).length = 272 := (hinv 1 (by decide)).1.1
  have hl2 : (hws 2).length = 272 := (hinv 2 (by decide)).1.1
  have hb0 : ((packHalfwordsLE (hws 0)).take 512).length = 512 := by simp [packHalfwordsLE_length, hl0]
  have hb1 : ((packHalfwordsLE (hws 1)).take 512).length = 512 := by simp [packHalfwordsLE_length, hl1]
  have hb2 : ((packHalfwordsLE (hws 2)).take 512).length = 512 := by simp [packHalfwordsLE_length, hl2]
  refine SepWP.weaken_pre (Entails.trans hP0
    (show _ ⊢ MultiLaneSlots (sp + 17376#64) 544 3 hws ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl0 hro0
    (seg2_shift_ok hl0 hl1 hl2 hpc0 hrun0 hro0 hreg0 hx1_0 hx22_0) ?_
  rintro sS PS hpcS hrunS hclS hroS ⟨hgS, hx1S, hx22S, hx25S, v18928, hPS⟩
  have h9984 : memRegion (sp + 9984#64) 1512 =
      memRegion (sp + 9984#64) 8 ∗ memRegion (sp + 9992#64) 512 ∗ memRegion (sp + 10504#64) 992 := by
    rw [memRegion_split' (b := sp + 9984#64) (b' := sp + 9992#64) (n := 8) (k := (1504 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 9992#64) (b' := sp + 10504#64) (n := 512) (k := (992 : Nat)) rfl (by bv_omega) (by decide)]
  have h27840 : memRegion (sp + 27840#64) 520 =
      memRegion (sp + 27840#64) 504 ∗ memRegion (sp + 28344#64) 16 :=
    memRegion_split' (b := sp + 27840#64) (b' := sp + 28344#64) (n := 504) (k := (16 : Nat)) rfl (by bv_omega) (by decide)
  rw [h9984] at hPS
  refine SepWP.weaken_pre (Entails.trans hPS (entails_sub
    (show memRegion (sp + 27840#64) 504 ∗ memRegion (sp + 28344#64) 16 ⊢
        memRegion (sp + 27840#64) 520 by rw [h27840]; exact Entails.refl _)
    (by sep_frame)
    (show _ ⊢ memRegion (sp + 9984#64) 8 ∗ (((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗
      ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗ _) by sep_frame))) ?_
  sep_frame_apply (sepWP_elim_bytes (a := sp + 9984#64) 8); intro pad0 hpad0
  refine SepWP.weaken_pre
    (show _ ⊢ ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hclS hroS (step_pre_col0 hrow hpcS hrunS hgS hx1S hx22S hx25S) ?_
  rintro s0 P0 hpc0' hrun0' hcl0' hro0' ⟨hg0, hx0_0, hx1_0', hx2_0, hP0'⟩
  refine SepWP.weaken_pre (Entails.trans hP0' (show _ ⊢
    ((sp + 17392#64) ↦ₛ (packHalfwordsLE (hws 0)).take 512) ∗ ((sp + 9984#64) ↦ₛ pad0) ∗
    memRegion (sp + 9992#64) 512 ∗ memRegion (sp + 27840#64) 520 ∗
    memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * row)) 512 ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl0' hro0'
    (step_col0 hb0 hpad0 hsp_chk hpc0' hrun0' hcl0' hg0 hx0_0 hx1_0' hx2_0) ?_
  rintro s0' P0' hpc0'' hrun0'' hcl0'' hro0'' ⟨hg0', pad1, hpad1, hP0''⟩
  refine sepWP_seq_env hcl0'' hro0''
    (SepWP.weaken_pre (Entails.trans hP0'' (show _ ⊢
      ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗ ((sp + 18928#64) ↦₆₄ v18928) ∗ _ by sep_frame))
      (step_inter_col1 hpc0'' hrun0'' hg0')) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hg1, hx0_1, hx1_1, hx2_1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (show _ ⊢
    ((sp + 17904#64) ↦ₛ (packHalfwordsLE (hws 1)).take 512) ∗ ((sp + 9984#64) ↦ₛ pad1) ∗
    memRegion (sp + 9992#64) 512 ∗ memRegion (sp + 27840#64) 520 ∗
    memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row)) 512 ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (step_col1 hb1 hpad1 hsp_chk hpc1 hrun1 hcl1 hg1 hx0_1 hx1_1 hx2_1) ?_
  rintro s1' P1' hpc1' hrun1' hcl1' hro1' ⟨hg1', pad2, hpad2, hP1'⟩
  refine sepWP_seq_env hcl1' hro1'
    (SepWP.weaken_pre (Entails.trans hP1' (show _ ⊢ ((sp + 18928#64) ↦₆₄ 2#64) ∗ _ by sep_frame))
      (step_inter_col2 hpc1' hrun1' hg1')) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hg2, hx0_2, hx1_2, hx2_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (show _ ⊢
    ((sp + 18416#64) ↦ₛ (packHalfwordsLE (hws 2)).take 512) ∗ ((sp + 9984#64) ↦ₛ pad2) ∗
    memRegion (sp + 9992#64) 512 ∗ memRegion (sp + 27840#64) 520 ∗
    memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row)) 512 ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (step_col2 hb2 hpad2 hsp_chk hpc2 hrun2 hcl2 hg2 hx0_2 hx1_2 hx2_2) ?_
  rintro s2' P2' hpc2' hrun2' hcl2' hro2' ⟨hg2', pad3, hpad3, hP2'⟩
  refine sepWP_seq_env hcl2' hro2' (SepWP.weaken_pre hP2' (step_post_col2 hpc2' hrun2' hg2')) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hgf, hx1f, hPf⟩
  refine SepWP.done hpcf hrunf ⟨hclf, hrof, hgf, hx1f, tA, htA, ?_⟩
  have hp0 : ((sp + 3744#64 + BitVec.ofNat 64 (512 * row)) ↦ₛ (packHalfwordsLE (hws 0)).take 512) =
      PolyMem (sp + 3744#64 + BitVec.ofNat 64 (512 * row))
        (polyVecNat ((sampleNtt (rowSeed rho row 0)).map (BitVec.ofNat 16))) := by
    have he0 := (hinv.exit_poly hd (i := 0) (by decide)).2.2
    dsimp only [Seg2Base.rowSeeds] at he0
    rw [polyMem_bytesToPoly16 _ hb0, he0, sampleNttClassical_eq_sampleNtt]
  have hp1 : ((sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row)) ↦ₛ (packHalfwordsLE (hws 1)).take 512) =
      PolyMem (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row))
        (polyVecNat ((sampleNtt (rowSeed rho row 1)).map (BitVec.ofNat 16))) := by
    have he1 := (hinv.exit_poly hd (i := 1) (by decide)).2.2
    dsimp only [Seg2Base.rowSeeds] at he1
    rw [polyMem_bytesToPoly16 _ hb1, he1, sampleNttClassical_eq_sampleNtt]
  have hp2 : ((sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row)) ↦ₛ (packHalfwordsLE (hws 2)).take 512) =
      PolyMem (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row))
        (polyVecNat ((sampleNtt (rowSeed rho row 2)).map (BitVec.ofNat 16))) := by
    have he2 := (hinv.exit_poly hd (i := 2) (by decide)).2.2
    dsimp only [Seg2Base.rowSeeds] at he2
    rw [polyMem_bytesToPoly16 _ hb2, he2, sampleNttClassical_eq_sampleNtt]
  have hpad3M : ((sp + 9984#64) ↦ₛ pad3) ⊢ memRegion (sp + 9984#64) 8 := by
    have hp := pointsToBytes_entails_memRegion (sp + 9984#64) pad3; rwa [hpad3] at hp
  rw [hp0, hp1, hp2, h27840] at hPf
  refine Entails.trans hPf ?_
  rw [h9984]
  unfold RowPolyOut
  exact entails_sub (slots_rejoin_1632 sp) (by sep_frame)
    (entails_sub hpad3M (by sep_frame) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Epi

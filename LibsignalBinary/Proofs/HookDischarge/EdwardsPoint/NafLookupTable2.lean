/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
meta import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase
meta import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.NafLookupTable1
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `NafLookupTable5::from` Top-Level Machine-Code Proof

Prologue initialization, 7-iteration loop composition, and top-level proof
`naf_lookup_table5_from_ok_of` (`B20`) in `dalekCliMultiLib`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.NafLookupTable2

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (fpMul EdExtPoint)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase dalekCaller_ok dalekCall_of_blockOk
  seq_codeLoaded_lr goalIsSeqCodeLoaded clearOldCodeLoadedHyps)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51_edwards_d2 fe51EdwardsD2Bytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0 (memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  Fe51MulOk Fe51MulRoRightOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes edProjDouble
  edAsExtended edAsProjNiels nafTable5Points fe51NafTable5Bounded
  ProjectivePointDoubleOk EdwardsPointAddProjNielsOk NafLookupTable5FromOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe le_length_of_hasLenGe sub_ofNat64_add readLE_write64_self' readLE_write64_ne
  fe51LimbsBounded_slice_of_at sepWP_focus_bytes sepWP_unfocus_bytes sepWP_norm_stackFrame
  sepWP_abstract_bytes sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  edProjDouble_mod edAsExtended_of_append4 fe51_mul_post_props)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (
  fe51LimbsBoundedAt_mono sepWP_peel_stack_region sepWP_unpeel_stack_region
  sepWP_split4_stack sepWP_merge4_stack write64_5_len write64_1_len
  sepWP_merge2_stack fe51_mro_post_props fe51EdwardsD2Bytes_bounded54)
open scoped LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.NafLookupTable1 (
  dalekCliLib20 dalekCliPl20 dalekCliPC20 dalekCliPl20_eq dalekCliPC20_eq dalekCliPC20_block_eq
  sepWP_resize_callee_576_2640 sepWP_unresize_callee_576_2640
  sepWP_split4_completed_272 sepWP_merge4_stack_272 asProjNiels_post_core
  NafLoopRegs naf_table_iter)

local macro "clean_sf " prev:ident : tactic =>
  `(tactic| (clean_prev_sf; clear_dead_vars [$prev:ident]; try clear $prev:ident))

local syntax "wp_dalek_call20" ppSpace colGt term:max (ppSpace colGt wppCallOpt)* : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wp_dalek_call20 $hcall:term $[$opts:wppCallOpt]*) => do
    if ← goalIsSeqCodeLoaded (← getMainGoal) then
      let hclPre ← mkFreshUserName `hcl_pre
      let hclPreId := mkIdent hclPre
      evalTactic (← `(tactic| (
        apply SepWP.done
        · first | wp_norm_lhs | wp_norm_goal | rfl
        · first | assumption | wp_norm_lhs
        intro $hclPreId:ident)))
    let gCur ← getMainGoal
    let progStx ← gCur.withContext do
      let ty := (← instantiateMVars (← gCur.getType)).consumeMData
      unless ty.isAppOfArity ``SepWP 6 do
        throwError "wp_dalek_call20: expected `SepWP` goal, got `{ty}`"
      Term.exprToSyntax (ty.getArg! 0)
    let hclPost ← mkFreshUserName `hcl_post
    let hclPostId := mkIdent hclPost
    evalTactic (← `(tactic| (
      apply seq_codeLoaded_lr ‹_›
      wp_call (dalekCall_of_blockOk $progStx $hcall
        (lib := dalekCliLib20) (pl := dalekCliPl20)
        (hP := congrArg (fun p : Program => p.rebase _ (fun _ => none)) dalekCliPC20_eq)) $[$opts]*)))
    let postCallGoals ← getGoals
    let mut newGoals : List MVarId := []
    for g in postCallGoals do
      if ← goalIsSeqCodeLoaded g then
        setGoals [g]
        evalTactic (← `(tactic| (
          apply SepWP.done
          · first | assumption | wp_norm_lhs | wp_norm_goal | rfl
          · first | assumption | wp_norm_lhs)))
        clearOldCodeLoadedHyps
        evalTactic (← `(tactic| intro $hclPostId:ident))
        newGoals := newGoals ++ (← getGoals)
      else
        newGoals := newGoals ++ [g]
    setGoals newGoals

open Lean Elab Tactic in
/-- Close an active `wp_cut_codeLoaded` cut at the current symbolic state, replacing prior
    `CodeLoaded` hypotheses with a single fresh `hcl_cut` on the post-write memory. -/
local elab "close_cut_codeLoaded" : tactic => do
  evalTactic (← `(tactic| (
    apply SepWP.done
    · first | wp_norm_lhs | wp_norm_goal | rfl
    · first | assumption | wp_norm_lhs)))
  clearOldCodeLoadedHyps
  let hclId := mkIdent (← mkFreshUserName `hcl_cut)
  evalTactic (← `(tactic| intro $hclId:ident))

/-! ## 1. Prologue & Table-Chunk Helpers -/

private theorem asProj_post_core (src dst : List (BitVec 8))
    (hsrc : fe51Point4Bounded src (2 ^ 52)) (hdst_len : dst.length = 120)
    (hw : ByteSlice.readLE dst 0 8 = ByteSlice.readLE src 0 8 ∧ ByteSlice.readLE dst 8 8 = ByteSlice.readLE src 8 8 ∧
      ByteSlice.readLE dst 16 8 = ByteSlice.readLE src 16 8 ∧ ByteSlice.readLE dst 24 8 = ByteSlice.readLE src 24 8 ∧
      ByteSlice.readLE dst 32 8 = ByteSlice.readLE src 32 8 ∧ ByteSlice.readLE dst 40 8 = ByteSlice.readLE src 40 8 ∧
      ByteSlice.readLE dst 48 8 = ByteSlice.readLE src 48 8 ∧ ByteSlice.readLE dst 56 8 = ByteSlice.readLE src 56 8 ∧
      ByteSlice.readLE dst 64 8 = ByteSlice.readLE src 64 8 ∧ ByteSlice.readLE dst 72 8 = ByteSlice.readLE src 72 8 ∧
      ByteSlice.readLE dst 80 8 = ByteSlice.readLE src 80 8 ∧ ByteSlice.readLE dst 88 8 = ByteSlice.readLE src 88 8 ∧
      ByteSlice.readLE dst 96 8 = ByteSlice.readLE src 96 8 ∧ ByteSlice.readLE dst 104 8 = ByteSlice.readLE src 104 8 ∧
      ByteSlice.readLE dst 112 8 = ByteSlice.readLE src 112 8) :
    dst.length = 120 ∧ fe51LimbsBoundedAt dst 0 (2 ^ 53) ∧ fe51LimbsBoundedAt dst 40 (2 ^ 53) ∧
    fe51LimbsBoundedAt dst 80 (2 ^ 54) ∧
    edProjDouble (fe51ValAt dst 0) (fe51ValAt dst 40) (fe51ValAt dst 80) =
      edProjDouble (edExtOfBytes src).X (edExtOfBytes src).Y (edExtOfBytes src).Z := by
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13, hw14⟩ := hw
  obtain ⟨_, hs0, hs40, hs80, _⟩ := hsrc
  have hs0_53 := fe51LimbsBoundedAt_mono hs0 (b2 := 2 ^ 53)
  have hs40_53 := fe51LimbsBoundedAt_mono hs40 (b2 := 2 ^ 53)
  have hs80_54 := fe51LimbsBoundedAt_mono hs80 (b2 := 2 ^ 54)
  have hx : fe51ValAt dst 0 = fe51ValAt src 0 := by unfold fe51ValAt; simp only [Nat.zero_add]; rw [hw0, hw1, hw2, hw3, hw4]
  have hy : fe51ValAt dst 40 = fe51ValAt src 40 := by unfold fe51ValAt; simp only [Nat.reduceAdd]; rw [hw5, hw6, hw7, hw8, hw9]
  have hz : fe51ValAt dst 80 = fe51ValAt src 80 := by unfold fe51ValAt; simp only [Nat.reduceAdd]; rw [hw10, hw11, hw12, hw13, hw14]
  refine ⟨hdst_len, ?_, ?_, ?_, ?_⟩
  · dsimp only [fe51LimbsBoundedAt, Nat.zero_add]; rw [hw0, hw1, hw2, hw3, hw4]; exact hs0_53
  · dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd]; rw [hw5, hw6, hw7, hw8, hw9]; exact hs40_53
  · dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd]; rw [hw10, hw11, hw12, hw13, hw14]; exact hs80_54
  · rw [hx, hy, hz, edProjDouble_mod]; rfl

private theorem slice_append_left (a b : List (BitVec 8)) {n : Nat} (ha : a.length = n) :
    ProofLib.ByteSlice.slice (a ++ b) 0 n = a := by
  unfold ProofLib.ByteSlice.slice; rw [List.drop_zero, ← ha, List.take_left]

private theorem slice_append_right (a b : List (BitVec 8)) (m off n : Nat) {k : Nat}
    (ha : a.length = m) (hoff : m + off = k) :
    ProofLib.ByteSlice.slice (a ++ b) k n = ProofLib.ByteSlice.slice b off n := by
  unfold ProofLib.ByteSlice.slice
  rw [← hoff, ← ha, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

private theorem slice_zero_len (a : List (BitVec 8)) {n : Nat} (ha : a.length = n) :
    ProofLib.ByteSlice.slice a 0 n = a := by
  unfold ProofLib.ByteSlice.slice; rw [List.drop_zero, ← ha, List.take_length]

private theorem nafTable8_of_append8 (A : EdExtPoint) (b0 b1 b2 b3 b4 b5 b6 b7 : List (BitVec 8))
    (h0 : fe51Point4Bounded b0 (2 ^ 53) ∧ edExtOfBytes b0 = nafTable5Points A 0)
    (h1 : fe51Point4Bounded b1 (2 ^ 53) ∧ edExtOfBytes b1 = nafTable5Points A 1)
    (h2 : fe51Point4Bounded b2 (2 ^ 53) ∧ edExtOfBytes b2 = nafTable5Points A 2)
    (h3 : fe51Point4Bounded b3 (2 ^ 53) ∧ edExtOfBytes b3 = nafTable5Points A 3)
    (h4 : fe51Point4Bounded b4 (2 ^ 53) ∧ edExtOfBytes b4 = nafTable5Points A 4)
    (h5 : fe51Point4Bounded b5 (2 ^ 53) ∧ edExtOfBytes b5 = nafTable5Points A 5)
    (h6 : fe51Point4Bounded b6 (2 ^ 53) ∧ edExtOfBytes b6 = nafTable5Points A 6)
    (h7 : fe51Point4Bounded b7 (2 ^ 53) ∧ edExtOfBytes b7 = nafTable5Points A 7) :
    let res := b0 ++ (b1 ++ (b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7))))))
    fe51NafTable5Bounded res (2 ^ 53) ∧
    ∀ i < 8, edExtOfBytes (ProofLib.ByteSlice.slice res (160 * i) 160) = nafTable5Points A i := by
  intro res
  have l0 := h0.1.1; have l1 := h1.1.1; have l2 := h2.1.1; have l3 := h3.1.1
  have l4 := h4.1.1; have l5 := h5.1.1; have l6 := h6.1.1; have l7 := h7.1.1
  have l67 : (b6 ++ b7).length = 320 := by rw [List.length_append, l6, l7]
  have l57 : (b5 ++ (b6 ++ b7)).length = 480 := by rw [List.length_append, l5, l67]
  have l47 : (b4 ++ (b5 ++ (b6 ++ b7))).length = 640 := by rw [List.length_append, l4, l57]
  have l37 : (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7)))).length = 800 := by rw [List.length_append, l3, l47]
  have l27 : (b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7))))).length = 960 := by rw [List.length_append, l2, l37]
  have l17 : (b1 ++ (b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7)))))).length = 1120 := by rw [List.length_append, l1, l27]
  have l07 : res.length = 1280 := by change (b0 ++ _).length = 1280; rw [List.length_append, l0, l17]
  have s0 : ProofLib.ByteSlice.slice res 0 160 = b0 := slice_append_left b0 _ l0
  have s1 : ProofLib.ByteSlice.slice res 160 160 = b1 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 160 160 = b1; rw [slice_append_right b0 _ 160 0 160 l0 rfl, slice_append_left b1 _ l1]
  have s2 : ProofLib.ByteSlice.slice res 320 160 = b2 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 320 160 = b2
    rw [slice_append_right b0 _ 160 160 160 l0 rfl, slice_append_right b1 _ 160 0 160 l1 rfl, slice_append_left b2 _ l2]
  have s3 : ProofLib.ByteSlice.slice res 480 160 = b3 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 480 160 = b3
    rw [slice_append_right b0 _ 160 320 160 l0 rfl, slice_append_right b1 _ 160 160 160 l1 rfl, slice_append_right b2 _ 160 0 160 l2 rfl, slice_append_left b3 _ l3]
  have s4 : ProofLib.ByteSlice.slice res 640 160 = b4 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 640 160 = b4
    rw [slice_append_right b0 _ 160 480 160 l0 rfl, slice_append_right b1 _ 160 320 160 l1 rfl, slice_append_right b2 _ 160 160 160 l2 rfl, slice_append_right b3 _ 160 0 160 l3 rfl, slice_append_left b4 _ l4]
  have s5 : ProofLib.ByteSlice.slice res 800 160 = b5 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 800 160 = b5
    rw [slice_append_right b0 _ 160 640 160 l0 rfl, slice_append_right b1 _ 160 480 160 l1 rfl, slice_append_right b2 _ 160 320 160 l2 rfl, slice_append_right b3 _ 160 160 160 l3 rfl, slice_append_right b4 _ 160 0 160 l4 rfl, slice_append_left b5 _ l5]
  have s6 : ProofLib.ByteSlice.slice res 960 160 = b6 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 960 160 = b6
    rw [slice_append_right b0 _ 160 800 160 l0 rfl, slice_append_right b1 _ 160 640 160 l1 rfl, slice_append_right b2 _ 160 480 160 l2 rfl, slice_append_right b3 _ 160 320 160 l3 rfl, slice_append_right b4 _ 160 160 160 l4 rfl, slice_append_right b5 _ 160 0 160 l5 rfl, slice_append_left b6 _ l6]
  have s7 : ProofLib.ByteSlice.slice res 1120 160 = b7 := by
    change ProofLib.ByteSlice.slice (b0 ++ _) 1120 160 = b7
    rw [slice_append_right b0 _ 160 960 160 l0 rfl, slice_append_right b1 _ 160 800 160 l1 rfl, slice_append_right b2 _ 160 640 160 l2 rfl, slice_append_right b3 _ 160 480 160 l3 rfl, slice_append_right b4 _ 160 320 160 l4 rfl, slice_append_right b5 _ 160 160 160 l5 rfl, slice_append_right b6 _ 160 0 160 l6 rfl]
    exact slice_zero_len b7 l7
  refine ⟨⟨l07, ?_⟩, ?_⟩ <;> (
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · simp only [Nat.mul_zero]; rw [s0]; exact h0.1
  · simp only [Nat.reduceMul]; rw [s1]; exact h1.1
  · simp only [Nat.reduceMul]; rw [s2]; exact h2.1
  · simp only [Nat.reduceMul]; rw [s3]; exact h3.1
  · simp only [Nat.reduceMul]; rw [s4]; exact h4.1
  · simp only [Nat.reduceMul]; rw [s5]; exact h5.1
  · simp only [Nat.reduceMul]; rw [s6]; exact h6.1
  · simp only [Nat.reduceMul]; rw [s7]; exact h7.1
  · simp only [Nat.mul_zero]; rw [s0]; exact h0.2
  · simp only [Nat.reduceMul]; rw [s1]; exact h1.2
  · simp only [Nat.reduceMul]; rw [s2]; exact h2.2
  · simp only [Nat.reduceMul]; rw [s3]; exact h3.2
  · simp only [Nat.reduceMul]; rw [s4]; exact h4.2
  · simp only [Nat.reduceMul]; rw [s5]; exact h5.2
  · simp only [Nat.reduceMul]; rw [s6]; exact h6.2
  · simp only [Nat.reduceMul]; rw [s7]; exact h7.2

private theorem split_chunk_160 (sp : BitVec 64) (off0 off1 rem : Nat) (bs : List (BitVec 8))
    (hbs : bs.length = 160 + rem) (ho : off0 = off1 + 160 := by decide) (_hb : off0 ≤ 2 ^ 64 := by decide) :
    ((sp - BitVec.ofNat 64 off0) ↦ₛ bs) =
      ((sp - BitVec.ofNat 64 off0) ↦ₛ bs.take 160) ∗ ((sp - BitVec.ofNat 64 off1) ↦ₛ bs.drop 160) := by
  conv => lhs; rw [← List.take_append_drop 160 bs]
  rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by omega),
      sub_ofNat64_add sp off0 160 (by omega), show off0 - 160 = off1 by omega]

private theorem sepWP_split7_naf_table (sp : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 1872#64) ↦ₛ bs) ∗ P := by sep_frame)
    (hbs : bs.length = 1120 := by assumption)
    (hnext : ∀ b1 b2 b3 b4 b5 b6 b7 : List (BitVec 8),
      b1.length = 160 → b2.length = 160 → b3.length = 160 → b4.length = 160 →
      b5.length = 160 → b6.length = 160 → b7.length = 160 →
      SepWP prog target_pc s
        ((((sp - 1872#64) ↦ₛ b1) ∗ ((sp - 1712#64) ↦ₛ b2) ∗ ((sp - 1552#64) ↦ₛ b3) ∗
          ((sp - 1392#64) ↦ₛ b4) ∗ ((sp - 1232#64) ↦ₛ b5) ∗ ((sp - 1072#64) ↦ₛ b6) ∗
          ((sp - 912#64) ↦ₛ b7)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 160; have hd1 : d1.length = 160 + 800 := by simp [d1, hbs]
  let d2 := d1.drop 160; have hd2 : d2.length = 160 + 640 := by simp [d2, hd1]
  let d3 := d2.drop 160; have hd3 : d3.length = 160 + 480 := by simp [d3, hd2]
  let d4 := d3.drop 160; have hd4 : d4.length = 160 + 320 := by simp [d4, hd3]
  let d5 := d4.drop 160; have hd5 : d5.length = 160 + 160 := by simp [d5, hd4]
  rw [hf, split_chunk_160 sp 1872 1712 960 bs hbs, split_chunk_160 sp 1712 1552 800 d1 hd1,
      split_chunk_160 sp 1552 1392 640 d2 hd2, split_chunk_160 sp 1392 1232 480 d3 hd3,
      split_chunk_160 sp 1232 1072 320 d4 hd4, split_chunk_160 sp 1072 912 160 d5 hd5]
  exact hnext (bs.take 160) (d1.take 160) (d2.take 160) (d3.take 160)
    (d4.take 160) (d5.take 160) (d5.drop 160)
    (by simp [hbs]) (by simp [hd1]) (by simp [hd2]) (by simp [hd3])
    (by simp [hd4]) (by simp [hd5]) (by simp [hd5])

private theorem merge_chunk_160 (sp : BitVec 64) (off0 off1 : Nat) (b0 b1 : List (BitVec 8))
    (h0 : b0.length = 160) (ho : off0 = off1 + 160 := by decide) (_hb : off0 ≤ 2 ^ 64 := by decide) :
    ((sp - BitVec.ofNat 64 off0) ↦ₛ (b0 ++ b1)) =
      ((sp - BitVec.ofNat 64 off0) ↦ₛ b0) ∗ ((sp - BitVec.ofNat 64 off1) ↦ₛ b1) := by
  rw [pointsToBytes_append, h0, sub_ofNat64_add sp off0 160 (by omega), show off0 - 160 = off1 by omega]

private theorem sepWP_merge8_naf_table (sp : BitVec 64) (A : EdExtPoint)
    {b0 b1 b2 b3 b4 b5 b6 b7 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((((sp - 2032#64) ↦ₛ b0) ∗ ((sp - 1872#64) ↦ₛ b1) ∗ ((sp - 1712#64) ↦ₛ b2) ∗
                   ((sp - 1552#64) ↦ₛ b3) ∗ ((sp - 1392#64) ↦ₛ b4) ∗ ((sp - 1232#64) ↦ₛ b5) ∗
                   ((sp - 1072#64) ↦ₛ b6) ∗ ((sp - 912#64) ↦ₛ b7)) ∗ P) := by sep_frame)
    (h0 : fe51Point4Bounded b0 (2 ^ 53) ∧ edExtOfBytes b0 = nafTable5Points A 0)
    (h1 : fe51Point4Bounded b1 (2 ^ 53) ∧ edExtOfBytes b1 = nafTable5Points A 1)
    (h2 : fe51Point4Bounded b2 (2 ^ 53) ∧ edExtOfBytes b2 = nafTable5Points A 2)
    (h3 : fe51Point4Bounded b3 (2 ^ 53) ∧ edExtOfBytes b3 = nafTable5Points A 3)
    (h4 : fe51Point4Bounded b4 (2 ^ 53) ∧ edExtOfBytes b4 = nafTable5Points A 4)
    (h5 : fe51Point4Bounded b5 (2 ^ 53) ∧ edExtOfBytes b5 = nafTable5Points A 5)
    (h6 : fe51Point4Bounded b6 (2 ^ 53) ∧ edExtOfBytes b6 = nafTable5Points A 6)
    (h7 : fe51Point4Bounded b7 (2 ^ 53) ∧ edExtOfBytes b7 = nafTable5Points A 7)
    (hnext : ∀ table_bs : List (BitVec 8),
      table_bs.length = 1280 →
      (fe51NafTable5Bounded table_bs (2 ^ 53) ∧
       ∀ i < 8, edExtOfBytes (ProofLib.ByteSlice.slice table_bs (160 * i) 160) = nafTable5Points A i) →
      SepWP prog target_pc s (((sp - 2032#64) ↦ₛ table_bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let res := b0 ++ (b1 ++ (b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7))))))
  have hprop := nafTable8_of_append8 A b0 b1 b2 b3 b4 b5 b6 b7 h0 h1 h2 h3 h4 h5 h6 h7
  have hm : ((sp - 2032#64) ↦ₛ res) =
      ((sp - 2032#64) ↦ₛ b0) ∗ ((sp - 1872#64) ↦ₛ b1) ∗ ((sp - 1712#64) ↦ₛ b2) ∗
      ((sp - 1552#64) ↦ₛ b3) ∗ ((sp - 1392#64) ↦ₛ b4) ∗ ((sp - 1232#64) ↦ₛ b5) ∗
      ((sp - 1072#64) ↦ₛ b6) ∗ ((sp - 912#64) ↦ₛ b7) := by
    dsimp only [res]
    rw [merge_chunk_160 sp 2032 1872 b0 _ h0.1.1, merge_chunk_160 sp 1872 1712 b1 _ h1.1.1,
        merge_chunk_160 sp 1712 1552 b2 _ h2.1.1, merge_chunk_160 sp 1552 1392 b3 _ h3.1.1,
        merge_chunk_160 sp 1392 1232 b4 _ h4.1.1, merge_chunk_160 sp 1232 1072 b5 _ h5.1.1,
        merge_chunk_160 sp 1072 912 b6 b7 h6.1.1]
  rw [hf, ← hm]
  exact hnext res hprop.1.1 hprop

/-! ## 2. Prologue (`+0x030..+0x314`) and Top-Level Proof -/

private theorem point4_copy20_post (src dst : List (BitVec 8)) (P : EdExtPoint)
    (hsrc : fe51Point4Bounded src (2 ^ 53) ∧ edExtOfBytes src = P)
    (hdst_len : dst.length = 160)
    (hw :
      ByteSlice.readLE dst 0 8 = ByteSlice.readLE src 0 8 ∧
      ByteSlice.readLE dst 8 8 = ByteSlice.readLE src 8 8 ∧
      ByteSlice.readLE dst 16 8 = ByteSlice.readLE src 16 8 ∧
      ByteSlice.readLE dst 24 8 = ByteSlice.readLE src 24 8 ∧
      ByteSlice.readLE dst 32 8 = ByteSlice.readLE src 32 8 ∧
      ByteSlice.readLE dst 40 8 = ByteSlice.readLE src 40 8 ∧
      ByteSlice.readLE dst 48 8 = ByteSlice.readLE src 48 8 ∧
      ByteSlice.readLE dst 56 8 = ByteSlice.readLE src 56 8 ∧
      ByteSlice.readLE dst 64 8 = ByteSlice.readLE src 64 8 ∧
      ByteSlice.readLE dst 72 8 = ByteSlice.readLE src 72 8 ∧
      ByteSlice.readLE dst 80 8 = ByteSlice.readLE src 80 8 ∧
      ByteSlice.readLE dst 88 8 = ByteSlice.readLE src 88 8 ∧
      ByteSlice.readLE dst 96 8 = ByteSlice.readLE src 96 8 ∧
      ByteSlice.readLE dst 104 8 = ByteSlice.readLE src 104 8 ∧
      ByteSlice.readLE dst 112 8 = ByteSlice.readLE src 112 8 ∧
      ByteSlice.readLE dst 120 8 = ByteSlice.readLE src 120 8 ∧
      ByteSlice.readLE dst 128 8 = ByteSlice.readLE src 128 8 ∧
      ByteSlice.readLE dst 136 8 = ByteSlice.readLE src 136 8 ∧
      ByteSlice.readLE dst 144 8 = ByteSlice.readLE src 144 8 ∧
      ByteSlice.readLE dst 152 8 = ByteSlice.readLE src 152 8) :
    fe51Point4Bounded dst (2 ^ 53) ∧ edExtOfBytes dst = P := by
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9,
          hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19⟩ := hw
  obtain ⟨⟨_, hs0, hs40, hs80, hs120⟩, hval⟩ := hsrc
  have hx : fe51ValAt dst 0 = fe51ValAt src 0 := by
    unfold fe51ValAt; simp only [Nat.zero_add]; rw [hw0, hw1, hw2, hw3, hw4]
  have hy : fe51ValAt dst 40 = fe51ValAt src 40 := by
    unfold fe51ValAt; simp only [Nat.reduceAdd]; rw [hw5, hw6, hw7, hw8, hw9]
  have hz : fe51ValAt dst 80 = fe51ValAt src 80 := by
    unfold fe51ValAt; simp only [Nat.reduceAdd]; rw [hw10, hw11, hw12, hw13, hw14]
  have ht : fe51ValAt dst 120 = fe51ValAt src 120 := by
    unfold fe51ValAt; simp only [Nat.reduceAdd]; rw [hw15, hw16, hw17, hw18, hw19]
  refine ⟨⟨hdst_len, ?_, ?_, ?_, ?_⟩, ?_⟩
  · dsimp only [fe51LimbsBoundedAt, Nat.zero_add]; rw [hw0, hw1, hw2, hw3, hw4]; exact hs0
  · dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd]; rw [hw5, hw6, hw7, hw8, hw9]; exact hs40
  · dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd]; rw [hw10, hw11, hw12, hw13, hw14]; exact hs80
  · dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd]; rw [hw15, hw16, hw17, hw18, hw19]; exact hs120
  · unfold edExtOfBytes at hval ⊢; rw [hx, hy, hz, ht, hval]

set_option maxHeartbeats 600000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem naf_table_init_b0 [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl20 b) (_hbase : dalekCliPl20.base = b)
    (hMRo : Fe51MulRoRightOk)
    (s0 s : State) (a : BitVec 64) (a_bs : List (BitVec 8))
    (target_pc : BitVec 64) (post : State → SepProp → Prop)
    (w_s0 w_s10 w_s18 : BitVec 64)
    (b0_i r1120_i pa_i n120_i n40_i : List (BitVec 8))
    (Full F : SepProp)
    (hf : Full =
      (memRegion (s0.sp - 2640#64) 576 ∗
       ((s0.sp - 2064#64) ↦₆₄ w_s0) ∗ ((s0.sp - 2048#64) ↦₆₄ w_s10) ∗ ((s0.sp - 2040#64) ↦₆₄ w_s18) ∗
       ((s0.sp - 2032#64) ↦ₛ b0_i) ∗ ((s0.sp - 1872#64) ↦ₛ r1120_i) ∗
       ((s0.sp - 432#64) ↦ₛ pa_i) ∗
       ((s0.sp - 272#64) ↦ₛ n120_i) ∗ ((s0.sp - 152#64) ↦ₛ n40_i) ∗
       (a ↦ₛ a_bs) ∗ (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F := by sep_frame)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = b + 48#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2064#64)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = a)
    (hx18 : s.readReg64 (Reg.gpr 18#5) = 18446744073709551312#64)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = a)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem)
    (ha_b : fe51Point4Bounded a_bs (2 ^ 52))
    (hb0_i : b0_i.length = 160) (hr1120_i : r1120_i.length = 1120)
    (hpa_i : pa_i.length = 120) (hn120_i : n120_i.length = 120) (hn40_i : n40_i.length = 40)
    (hnext : ∀ (s1 : State) (w_s0' w_s10' w_s18' : BitVec 64)
      (b0 r1120_1 pa_1 niels0 : List (BitVec 8)),
      s1.pc = b + 392#64 → s1.status = .Running → s1.sp = s0.sp - 2064#64 →
      s1.readReg64 (Reg.gpr 0#5) = s0.sp - 432#64 →
      s1.readReg64 (Reg.gpr 8#5) = s0.sp - 272#64 →
      s1.readReg64 (Reg.gpr 20#5) = s0.sp - 272#64 →
      s1.readReg64 (Reg.gpr 21#5) = a →
      s1.readReg64 (Reg.gpr 23#5) = s0.sp - 432#64 →
      s1.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      dalekCliMultiLib.CodeLoaded dalekCliMpl s1.mem →
      (fe51Point4Bounded b0 (2 ^ 53) ∧ edExtOfBytes b0 = nafTable5Points (edExtOfBytes a_bs) 0) →
      r1120_1.length = 1120 →
      (pa_1.length = 120 ∧
       ByteSlice.readLE a_bs 32 8 = ByteSlice.readLE pa_1 32 8 ∧
       ByteSlice.readLE a_bs 72 8 = ByteSlice.readLE pa_1 72 8 ∧
       ByteSlice.readLE a_bs 112 8 = ByteSlice.readLE pa_1 112 8) →
      niels0.length = 160 →
      SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s1
        ((memRegion (s0.sp - 2640#64) 576 ∗
          ((s0.sp - 2064#64) ↦₆₄ w_s0') ∗ ((s0.sp - 2048#64) ↦₆₄ w_s10') ∗ ((s0.sp - 2040#64) ↦₆₄ w_s18') ∗
          ((s0.sp - 2032#64) ↦ₛ b0) ∗ ((s0.sp - 1872#64) ↦ₛ r1120_1) ∗
          ((s0.sp - 432#64) ↦ₛ pa_1) ∗ ((s0.sp - 272#64) ↦ₛ niels0) ∗
          (a ↦ₛ a_bs) ∗ (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F) post) :
    SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s Full post := by
  have ha_len : a_bs.length = 160 := ha_b.1
  haveI : HasLenGe a_bs 160 := ⟨by omega⟩
  haveI : HasLenGe n120_i 120 := ⟨by omega⟩
  rw [hf]
  wp_cut_codeLoaded hcl
  wp_sym_steps 49
  apply sepWP_resize_callee_576_2640 s0.sp 352 224 2288
  apply sepWP_focus_bytes a (a + 120#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ :=
    fe51LimbsBounded_slice_of_at (2 ^ 54) (fe51LimbsBoundedAt_mono ha_b.2.2.2.2 (b2 := 2 ^ 54))
  obtain ⟨_, _, _, _, _, _⟩ := fe51EdwardsD2Bytes_bounded54
  wp_dalek_call20 hMRo; clean_prev_sf; norm_sf 224
  obtain ⟨hw_t2d_len, hw_t2d_b, hw_t2d_v⟩ := fe51_mro_post_props w a_bs
  apply sepWP_unfocus_bytes a (a + 120#64) 120 40
  apply sepWP_unresize_callee_576_2640 s0.sp 352 224 2288
  haveI : HasLenGe b0_i 160 := ⟨by omega⟩
  haveI : HasLenGe r1120_i 1120 := ⟨by omega⟩
  haveI : HasLenGe pa_i 120 := ⟨by omega⟩
  apply sepWP_merge2_stack s0.sp 272 152 40
  intro m0_bs hm0_len hm80 hm88 hm96 hm104 hm112 hm120 hm128 hm136 hm144 hm152
  simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne] at hm80 hm88 hm96 hm104 hm112
  haveI : HasLenGe m0_bs 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 15
  close_cut_codeLoaded
  have hb0_eq : edAsProjNiels (edExtOfBytes a_bs) = nafTable5Points (edExtOfBytes a_bs) 0 := rfl
  apply sepWP_abstract_bytes (s0.sp - 272#64)
    (fun niels0 =>
      (fe51Point4Bounded niels0 (2 ^ 53) ∧ edExtOfBytes niels0 = nafTable5Points (edExtOfBytes a_bs) 0) ∧
      ByteSlice.readLE a_bs 96 8 = ByteSlice.readLE niels0 96 8 ∧
      ByteSlice.readLE a_bs 104 8 = ByteSlice.readLE niels0 104 8 ∧
      ByteSlice.readLE a_bs 112 8 = ByteSlice.readLE niels0 112 8 ∧
      ByteSlice.readLE w 0 8 = ByteSlice.readLE niels0 120 8 ∧
      ByteSlice.readLE w 8 8 = ByteSlice.readLE niels0 128 8 ∧
      ByteSlice.readLE w 16 8 = ByteSlice.readLE niels0 136 8 ∧
      ByteSlice.readLE w 24 8 = ByteSlice.readLE niels0 144 8 ∧
      ByteSlice.readLE w 32 8 = ByteSlice.readLE niels0 152 8)
  · refine ⟨?_, ?_⟩
    · rw [← hb0_eq]
      refine asProjNiels_post_core a_bs w _ ha_b hw_t2d_b hw_t2d_v (by prove_write64_len) ?_
      simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
        hm80, hm88, hm96, hm104, hm112, hm120, hm128, hm136, hm144, hm152, and_self]
    · simp (disch := decide) only [↓readLE_write64_ne,
        hm96, hm104, hm112, hm120, hm128, hm136, hm144, hm152, and_self]
  clear hm80 hm88 hm96 hm104 hm112 hm120 hm128 hm136
  intro niels0 ⟨hniels0, hn96, hn104, hn112, hn120, hn128, hn136, hn144, hn152⟩
  have hniels0_len : niels0.length = 160 := hniels0.1.1
  haveI : HasLenGe niels0 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 22
  close_cut_codeLoaded
  apply sepWP_abstract_bytes (s0.sp - 2032#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 53) ∧ edExtOfBytes buf = nafTable5Points (edExtOfBytes a_bs) 0)
  · refine point4_copy20_post niels0 _ _ hniels0 (by prove_write64_len) ?_
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
      hm144, hm152, hn96, hn104, hn112, hn120, hn144, hn152, and_self]
  clear hm144 hm152 hn96 hn104 hn120 hn128 hn136
  intro b0 hb0
  apply sepWP_abstract_bytes (s0.sp - 1872#64) (fun buf => buf.length = 1120)
  · prove_write64_len
  intro r1120_1 hr1120_1
  apply sepWP_abstract_bytes (s0.sp - 432#64)
    (fun buf => buf.length = 120 ∧
      ByteSlice.readLE a_bs 32 8 = ByteSlice.readLE buf 32 8 ∧
      ByteSlice.readLE a_bs 72 8 = ByteSlice.readLE buf 72 8 ∧
      ByteSlice.readLE a_bs 112 8 = ByteSlice.readLE buf 112 8)
  · refine ⟨by prove_write64_len, ?_⟩
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne, hn112, and_self]
  clear hn112
  intro pa_1 hpa_1
  have hperm :
      (((s0.sp - 432#64) ↦ₛ pa_1) ∗ ((s0.sp - 1872#64) ↦ₛ r1120_1) ∗
       ((s0.sp - 2032#64) ↦ₛ b0) ∗ ((s0.sp - 272#64) ↦ₛ niels0) ∗
       memRegion (s0.sp - 2640#64) 576 ∗ (a ↦ₛ a_bs) ∗ (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes) ∗
       ((s0.sp - 2064#64) ↦₆₄ (ByteSlice.readLE a_bs 24 8 + ByteSlice.readLE a_bs 64 8)) ∗
       ((s0.sp - 2048#64) ↦₆₄ (ByteSlice.readLE a_bs 16 8 + ByteSlice.readLE a_bs 56 8)) ∗
       ((s0.sp - 2040#64) ↦₆₄ (ByteSlice.readLE a_bs 8 8 + ByteSlice.readLE a_bs 48 8)) ∗ F) =
      ((memRegion (s0.sp - 2640#64) 576 ∗
        ((s0.sp - 2064#64) ↦₆₄ (ByteSlice.readLE a_bs 24 8 + ByteSlice.readLE a_bs 64 8)) ∗
        ((s0.sp - 2048#64) ↦₆₄ (ByteSlice.readLE a_bs 16 8 + ByteSlice.readLE a_bs 56 8)) ∗
        ((s0.sp - 2040#64) ↦₆₄ (ByteSlice.readLE a_bs 8 8 + ByteSlice.readLE a_bs 48 8)) ∗
        ((s0.sp - 2032#64) ↦ₛ b0) ∗ ((s0.sp - 1872#64) ↦ₛ r1120_1) ∗
        ((s0.sp - 432#64) ↦ₛ pa_1) ∗ ((s0.sp - 272#64) ↦ₛ niels0) ∗
        (a ↦ₛ a_bs) ∗ (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F) := by sep_ac_rfl
  rw [hperm]
  exact hnext _ (ByteSlice.readLE a_bs 24 8 + ByteSlice.readLE a_bs 64 8)
    (ByteSlice.readLE a_bs 16 8 + ByteSlice.readLE a_bs 56 8)
    (ByteSlice.readLE a_bs 8 8 + ByteSlice.readLE a_bs 48 8)
    b0 r1120_1 pa_1 niels0
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    ‹_› hb0 hr1120_1 hpa_1 hniels0_len

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem naf_table_init_r1 [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl20 b) (_hbase : dalekCliPl20.base = b)
    (s0 s : State) (a : BitVec 64)
    (target_pc : BitVec 64) (post : State → SepProp → Prop)
    (r1120_1 niels0 : List (BitVec 8))
    (Full F : SepProp)
    (hf : Full = ((((s0.sp - 1872#64) ↦ₛ r1120_1) ∗ ((s0.sp - 272#64) ↦ₛ niels0)) ∗ F) := by sep_frame)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = b + 392#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2064#64)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 432#64)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = s0.sp - 272#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = s0.sp - 272#64)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = a)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 432#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem)
    (hr1120_1 : r1120_1.length = 1120)
    (hniels0 : niels0.length = 160)
    (hnext : ∀ (s2 : State) (r1120_2 : List (BitVec 8)),
      s2.pc = b + 552#64 → s2.status = .Running → s2.sp = s0.sp - 2064#64 →
      s2.readReg64 (Reg.gpr 0#5) = s0.sp - 432#64 →
      s2.readReg64 (Reg.gpr 8#5) = s0.sp - 272#64 →
      s2.readReg64 (Reg.gpr 20#5) = s0.sp - 272#64 →
      s2.readReg64 (Reg.gpr 21#5) = a →
      s2.readReg64 (Reg.gpr 23#5) = s0.sp - 432#64 →
      s2.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      dalekCliMultiLib.CodeLoaded dalekCliMpl s2.mem →
      r1120_2.length = 1120 →
      SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s2
        ((((s0.sp - 1872#64) ↦ₛ r1120_2) ∗ ((s0.sp - 272#64) ↦ₛ niels0)) ∗ F) post) :
    SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s Full post := by
  haveI : HasLenGe r1120_1 1120 := ⟨by omega⟩
  haveI : HasLenGe niels0 160 := ⟨by omega⟩
  rw [hf]
  apply MultiPlacedLib.seq_codeLoaded (mid := b + 552#64) hcl
  generalize hpost_eq : (fun (sm : State) (Pm : SepProp) =>
    dalekCliMultiLib.CodeLoaded dalekCliMpl sm.mem →
      SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc sm Pm post) = post_cut
  wp_sym_steps 20
  apply sepWP_abstract_bytes (s0.sp - 1872#64) (fun buf => buf.length = 1120)
  · prove_write64_len
  intro r1120_a hr1120_a; haveI : HasLenGe r1120_a 1120 := ⟨by omega⟩
  wp_sym_steps 20
  apply sepWP_abstract_bytes (s0.sp - 1872#64) (fun buf => buf.length = 1120)
  · prove_write64_len
  intro r1120_2 hr1120_2
  subst hpost_eq
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_end
  have hperm :
      (((s0.sp - 1872#64) ↦ₛ r1120_2) ∗ ((s0.sp - 272#64) ↦ₛ niels0) ∗ F) =
      ((((s0.sp - 1872#64) ↦ₛ r1120_2) ∗ ((s0.sp - 272#64) ↦ₛ niels0)) ∗ F) := by sep_ac_rfl
  rw [hperm]
  exact hnext _ r1120_2
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    hcl_end hr1120_2

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem naf_table_init_r2 [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl20 b) (_hbase : dalekCliPl20.base = b)
    (s0 s : State) (a : BitVec 64) (a_bs : List (BitVec 8))
    (target_pc : BitVec 64) (post : State → SepProp → Prop)
    (r1120_2 pa_1 niels0 : List (BitVec 8))
    (Full F : SepProp)
    (hf : Full =
      ((((s0.sp - 1872#64) ↦ₛ r1120_2) ∗ ((s0.sp - 432#64) ↦ₛ pa_1) ∗
        ((s0.sp - 272#64) ↦ₛ niels0) ∗ (a ↦ₛ a_bs)) ∗ F) := by sep_frame)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = b + 552#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2064#64)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 432#64)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = s0.sp - 272#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = s0.sp - 272#64)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = a)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 432#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem)
    (ha_b : fe51Point4Bounded a_bs (2 ^ 52))
    (hr1120_2 : r1120_2.length = 1120)
    (hpa_1 : pa_1.length = 120 ∧
      ByteSlice.readLE a_bs 32 8 = ByteSlice.readLE pa_1 32 8 ∧
      ByteSlice.readLE a_bs 72 8 = ByteSlice.readLE pa_1 72 8 ∧
      ByteSlice.readLE a_bs 112 8 = ByteSlice.readLE pa_1 112 8)
    (hniels0 : niels0.length = 160)
    (hnext : ∀ (s_dbl : State) (b1 b2 b3 b4 b5 b6 b7 proja : List (BitVec 8)),
      s_dbl.pc = b + 716#64 → s_dbl.status = .Running → s_dbl.sp = s0.sp - 2064#64 →
      s_dbl.readReg64 (Reg.gpr 0#5) = s0.sp - 432#64 →
      s_dbl.readReg64 (Reg.gpr 8#5) = s0.sp - 272#64 →
      s_dbl.readReg64 (Reg.gpr 20#5) = s0.sp - 272#64 →
      s_dbl.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs s_dbl = calleeSavedVRegs s0 →
      dalekCliMultiLib.CodeLoaded dalekCliMpl s_dbl.mem →
      b1.length = 160 → b2.length = 160 → b3.length = 160 → b4.length = 160 →
      b5.length = 160 → b6.length = 160 → b7.length = 160 →
      (proja.length = 120 ∧ fe51LimbsBoundedAt proja 0 (2 ^ 53) ∧
       fe51LimbsBoundedAt proja 40 (2 ^ 53) ∧ fe51LimbsBoundedAt proja 80 (2 ^ 54) ∧
       edProjDouble (fe51ValAt proja 0) (fe51ValAt proja 40) (fe51ValAt proja 80) =
         edProjDouble (edExtOfBytes a_bs).X (edExtOfBytes a_bs).Y (edExtOfBytes a_bs).Z) →
      SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s_dbl
        ((((s0.sp - 1872#64) ↦ₛ b1) ∗ ((s0.sp - 1712#64) ↦ₛ b2) ∗ ((s0.sp - 1552#64) ↦ₛ b3) ∗
          ((s0.sp - 1392#64) ↦ₛ b4) ∗ ((s0.sp - 1232#64) ↦ₛ b5) ∗ ((s0.sp - 1072#64) ↦ₛ b6) ∗
          ((s0.sp - 912#64) ↦ₛ b7) ∗ ((s0.sp - 432#64) ↦ₛ proja) ∗
          ((s0.sp - 272#64) ↦ₛ niels0) ∗ (a ↦ₛ a_bs)) ∗ F) post) :
    SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s Full post := by
  have ha_len : a_bs.length = 160 := ha_b.1
  have hpa_len : pa_1.length = 120 := hpa_1.1
  haveI : HasLenGe a_bs 160 := ⟨by omega⟩
  haveI : HasLenGe r1120_2 1120 := ⟨by omega⟩
  haveI : HasLenGe pa_1 120 := ⟨by omega⟩
  haveI : HasLenGe niels0 160 := ⟨by omega⟩
  rw [hf]
  apply MultiPlacedLib.seq_codeLoaded (mid := b + 716#64) hcl
  generalize hpost_eq : (fun (sm : State) (Pm : SepProp) =>
    dalekCliMultiLib.CodeLoaded dalekCliMpl sm.mem →
      SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc sm Pm post) = post_cut
  wp_sym_steps 20
  apply sepWP_abstract_bytes (s0.sp - 1872#64) (fun buf => buf.length = 1120)
  · prove_write64_len
  intro r1120_b hr1120_b; haveI : HasLenGe r1120_b 1120 := ⟨by omega⟩
  wp_sym_steps 21
  apply sepWP_abstract_bytes (s0.sp - 1872#64) (fun buf => buf.length = 1120)
  · prove_write64_len
  intro r1120 hr1120
  apply sepWP_split7_naf_table s0.sp
  intro b1 b2 b3 b4 b5 b6 b7 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  rcases hpa_1 with ⟨_, hpa32, hpa72, hpa112⟩
  apply sepWP_abstract_bytes (s0.sp - 432#64)
    (fun dst => dst.length = 120 ∧ fe51LimbsBoundedAt dst 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt dst 40 (2 ^ 53) ∧ fe51LimbsBoundedAt dst 80 (2 ^ 54) ∧
      edProjDouble (fe51ValAt dst 0) (fe51ValAt dst 40) (fe51ValAt dst 80) =
        edProjDouble (edExtOfBytes a_bs).X (edExtOfBytes a_bs).Y (edExtOfBytes a_bs).Z)
  · refine asProj_post_core a_bs _ ha_b (by prove_write64_len) ?_
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne, hpa32, hpa72, hpa112, and_self]
  intro proja hpa
  subst hpost_eq
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_end
  have hperm :
      (((s0.sp - 432#64) ↦ₛ proja) ∗
       ((s0.sp - 1872#64) ↦ₛ b1) ∗ ((s0.sp - 1712#64) ↦ₛ b2) ∗ ((s0.sp - 1552#64) ↦ₛ b3) ∗
       ((s0.sp - 1392#64) ↦ₛ b4) ∗ ((s0.sp - 1232#64) ↦ₛ b5) ∗ ((s0.sp - 1072#64) ↦ₛ b6) ∗
       ((s0.sp - 912#64) ↦ₛ b7) ∗ ((s0.sp - 272#64) ↦ₛ niels0) ∗ (a ↦ₛ a_bs) ∗ F) =
      ((((s0.sp - 1872#64) ↦ₛ b1) ∗ ((s0.sp - 1712#64) ↦ₛ b2) ∗ ((s0.sp - 1552#64) ↦ₛ b3) ∗
        ((s0.sp - 1392#64) ↦ₛ b4) ∗ ((s0.sp - 1232#64) ↦ₛ b5) ∗ ((s0.sp - 1072#64) ↦ₛ b6) ∗
        ((s0.sp - 912#64) ↦ₛ b7) ∗ ((s0.sp - 432#64) ↦ₛ proja) ∗
        ((s0.sp - 272#64) ↦ₛ niels0) ∗ (a ↦ₛ a_bs)) ∗ F) := by sep_ac_rfl
  rw [hperm]
  exact hnext _ b1 b2 b3 b4 b5 b6 b7 proja
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    hcl_end hb1 hb2 hb3 hb4 hb5 hb6 hb7 hpa

set_option maxHeartbeats 400000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem naf_table_init_a2 [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl20 b) (_hbase : dalekCliPl20.base = b)
    (hDbl : ProjectivePointDoubleOk) (hMul : Fe51MulOk)
    (s0 s : State) (A : EdExtPoint)
    (target_pc : BitVec 64) (post : State → SepProp → Prop)
    (a2_i proja t6d8_i niels0 : List (BitVec 8))
    (Full F : SepProp)
    (hf : Full =
      (memRegion (s0.sp - 2640#64) 576 ∗
       ((s0.sp - 752#64) ↦ₛ a2_i) ∗ ((s0.sp - 432#64) ↦ₛ proja) ∗
       ((s0.sp - 312#64) ↦ₛ t6d8_i) ∗ ((s0.sp - 272#64) ↦ₛ niels0)) ∗ F := by sep_frame)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = b + 716#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2064#64)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 432#64)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = s0.sp - 272#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = s0.sp - 272#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem)
    (ha2_i : a2_i.length = 160)
    (hpa : proja.length = 120 ∧ fe51LimbsBoundedAt proja 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt proja 40 (2 ^ 53) ∧ fe51LimbsBoundedAt proja 80 (2 ^ 54) ∧
      edProjDouble (fe51ValAt proja 0) (fe51ValAt proja 40) (fe51ValAt proja 80) =
        edProjDouble A.X A.Y A.Z)
    (ht6d8_i : t6d8_i.length = 40) (hniels0 : niels0.length = 160)
    (hnext : ∀ (s' : State) (a2_bs tmp660_bs comp_bs : List (BitVec 8)),
      NafLoopRegs s0 s' (b + 792#64) (BitVec.ofNat 64 (160 * 0)) →
      fe51Point4Bounded a2_bs (2 ^ 52) →
      edExtOfBytes a2_bs = edAsExtended (edProjDouble A.X A.Y A.Z) →
      tmp660_bs.length = 160 → comp_bs.length = 160 →
      SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s'
        ((memRegion (s0.sp - 2640#64) 576 ∗
          ((s0.sp - 752#64) ↦ₛ a2_bs) ∗ ((s0.sp - 432#64) ↦ₛ tmp660_bs) ∗
          ((s0.sp - 272#64) ↦ₛ comp_bs)) ∗ F) post) :
    SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s Full post := by
  obtain ⟨hpa_len, hpa_0, hpa_40, hpa_80, hpa_v⟩ := hpa
  rw [hf]
  apply sepWP_resize_callee_576_2640 s0.sp 176 400 2464
  unpack_fe51_at hpa_0; unpack_fe51_at hpa_40; unpack_fe51_at hpa_80
  wp_sym_steps 1
  wp_dalek_call20 hDbl; clean_sf s; norm_sf 400
  apply sepWP_unresize_callee_576_2640 s0.sp 176 400 2464
  apply sepWP_merge2_stack s0.sp 432 312 40
  intro tmp660_bs ht660 _ _ _ _ _ _ _ _ _ _
  let D := edProjDouble A.X A.Y A.Z
  have hd_val : edExtOfBytes w = D := ‹edExtOfBytes w = _›.trans hpa_v
  apply sepWP_split4_completed_272 s0.sp D
    (h0 := fe51LimbsBoundedAt_mono ‹fe51LimbsBoundedAt w 0 _›)
    (h40 := fe51LimbsBoundedAt_mono ‹fe51LimbsBoundedAt w 40 _›)
    (h80 := fe51LimbsBoundedAt_mono ‹fe51LimbsBoundedAt w 80 _›)
    (h120 := fe51LimbsBoundedAt_mono ‹fe51LimbsBoundedAt w 120 _›)
    (hval := hd_val)
  intro c0 c1 c2 c3 hc0_l hc1_l hc2_l hc3_l hc0_b hc1_b hc2_b hc3_b hc0_v hc1_v hc2_v hc3_v
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_stack s0.sp 752 712 672 632
  intro e0 e1 e2 e3 he0_l he1_l he2_l he3_l
  apply sepWP_resize_callee_576_2640 s0.sp 352 224 2288
  wp_sym_steps 5; wp_dalek_call20 hMul; clean_sf sf; obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w_1 (fpMul D.X D.T)
  wp_sym_steps 4; wp_dalek_call20 hMul; clean_sf sf_1; obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_2 (fpMul D.Y D.Z)
  wp_sym_steps 4; wp_dalek_call20 hMul; clean_sf sf; obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_3 (fpMul D.Z D.T)
  wp_sym_steps 4; wp_dalek_call20 hMul; clean_sf sf_1; obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_4 (fpMul D.X D.Y)
  norm_sf 224; wp_sym_steps 1
  apply sepWP_unresize_callee_576_2640 s0.sp 352 224 2288
  apply sepWP_merge4_stack_272 s0.sp
  intro comp_bs hcomp
  apply sepWP_merge4_stack s0.sp 752 712 672 632
    (fun a2_bs => fe51Point4Bounded a2_bs (2 ^ 52) ∧ edExtOfBytes a2_bs = edAsExtended D)
  · obtain ⟨hl, hb0', hb1', hb2', hb3', hv⟩ :=
      edAsExtended_of_append4 w_1 w_2 w_3 w_4 D hr0_b hr1_b hr2_b hr3_b hr0_v hr1_v hr2_v hr3_v
    exact ⟨⟨hl, hb0', hb1', hb2', hb3'⟩, hv⟩
  intro a2_bs ⟨ha2_b, ha2_v⟩
  have hperm :
      (((s0.sp - 752#64) ↦ₛ a2_bs) ∗ ((s0.sp - 272#64) ↦ₛ comp_bs) ∗
       memRegion (s0.sp - 2640#64) 576 ∗ ((s0.sp - 432#64) ↦ₛ tmp660_bs) ∗ F) =
      ((memRegion (s0.sp - 2640#64) 576 ∗ ((s0.sp - 752#64) ↦ₛ a2_bs) ∗
        ((s0.sp - 432#64) ↦ₛ tmp660_bs) ∗ ((s0.sp - 272#64) ↦ₛ comp_bs)) ∗ F) := by sep_ac_rfl
  rw [hperm]
  exact hnext _ a2_bs tmp660_bs comp_bs
    ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ‹_›⟩
    ha2_b ha2_v ht660 hcomp

public section

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
theorem naf_lookup_table5_from_ok_of
    (hMul : Fe51MulOk) (hMulRo : Fe51MulRoRightOk)
    (hDbl : ProjectivePointDoubleOk) (hAddPN : EdwardsPointAddProjNielsOk) :
    NafLookupTable5FromOk := by
  intro _
  apply dalekCaller_ok dalekCliPC20 dalekCliPl20 dalekCliPl20_eq dalekCliPC20_block_eq
  intro b hb hbase
  wp_init
  apply sepWP_norm_stackFrame 2640 rfl
  apply sepWP_peel_stack_region s0.sp 2640 576 2064
  apply sepWP_peel_stack_region s0.sp 2064 32 2032
  open_cells (s0.sp - 2064#64) 32 4
  apply sepWP_peel_stack_bytes s0.sp 2032 160 1872; intro b0_i hb0_i
  apply sepWP_peel_stack_bytes s0.sp 1872 1120 752; intro r1120_i hr1120_i
  apply sepWP_peel_stack_bytes s0.sp 752 160 592; intro a2_i ha2_i
  apply sepWP_peel_stack_bytes s0.sp 592 120 472; intro t5c0_i ht5c0_i
  apply sepWP_peel_stack_bytes s0.sp 472 40 432; intro t638_i ht638_i
  apply sepWP_peel_stack_bytes s0.sp 432 120 312; intro pa_i hpa_i
  apply sepWP_peel_stack_bytes s0.sp 312 40 272; intro t6d8_i ht6d8_i
  apply sepWP_peel_stack_bytes s0.sp 272 120 152; intro n120_i hn120_i
  apply sepWP_peel_stack_bytes s0.sp 152 40 112; intro n40_i hn40_i
  apply sepWP_peel_stack_region s0.sp 112 16 96
  open_cells (s0.sp - 96#64) 96 12
  wp_cut_codeLoaded
  wp_sym_steps 12
  close_cut_codeLoaded
  have ha_b : fe51Point4Bounded a_rest (2 ^ 52) := ‹_›
  apply naf_table_init_b0 b hb hbase hMulRo s0 _ a a_rest _ _ _ _ _ b0_i r1120_i pa_i n120_i n40_i _ _
    (hsp0_align := hsp_align) (hpc := by wp_norm_lhs) (hrun := by wp_norm_lhs) (hsp := by wp_norm_lhs)
    (hx0 := by wp_norm_lhs) (hx18 := by wp_norm_lhs) (hx21 := by wp_norm_lhs) (hx29 := by wp_norm_lhs)
    (hvregs := by wp_norm_lhs) (hcl := ‹_›) (ha_b := ha_b) (hb0_i := hb0_i) (hr1120_i := hr1120_i)
    (hpa_i := hpa_i) (hn120_i := hn120_i) (hn40_i := hn40_i)
  intro s1 w_s0' w_s10' w_s18' b0 r1120_1 pa_1 niels0
    hpc1 hrun1 hsp1 hx0_1 hx8_1 hx20_1 hx21_1 hx23_1 hx29_1 hvregs1 hcl1 hb0 hr1120_1 hpa_1 hniels0
  apply naf_table_init_r1 b hb hbase s0 s1 a _ _ r1120_1 niels0 _ _
    (hsp0_align := hsp_align) (hpc := hpc1) (hrun := hrun1) (hsp := hsp1)
    (hx0 := hx0_1) (hx8 := hx8_1) (hx20 := hx20_1) (hx21 := hx21_1) (hx23 := hx23_1) (hx29 := hx29_1)
    (hvregs := hvregs1) (hcl := hcl1) (hr1120_1 := hr1120_1) (hniels0 := hniels0)
  intro s2 r1120_2 hpc2 hrun2 hsp2 hx0_2 hx8_2 hx20_2 hx21_2 hx23_2 hx29_2 hvregs2 hcl2 hr1120_2
  apply naf_table_init_r2 b hb hbase s0 s2 a a_rest _ _ r1120_2 pa_1 niels0 _ _
    (hsp0_align := hsp_align) (hpc := hpc2) (hrun := hrun2) (hsp := hsp2)
    (hx0 := hx0_2) (hx8 := hx8_2) (hx20 := hx20_2) (hx21 := hx21_2) (hx23 := hx23_2) (hx29 := hx29_2)
    (hvregs := hvregs2) (hcl := hcl2) (ha_b := ha_b) (hr1120_2 := hr1120_2) (hpa_1 := hpa_1) (hniels0 := hniels0)
  intro s_dbl b1_i b2_i b3_i b4_i b5_i b6_i b7_i proja
    hpc_d hrun_d hsp_d hx0_d hx8_d hx20_d hx29_d hvregs_d hcl_d hb1_i hb2_i hb3_i hb4_i hb5_i hb6_i hb7_i hpa
  apply naf_table_init_a2 b hb hbase hDbl hMul s0 s_dbl (edExtOfBytes a_rest) _ _ a2_i proja t6d8_i niels0 _ _
    (hsp0_align := hsp_align) (hpc := hpc_d) (hrun := hrun_d) (hsp := hsp_d)
    (hx0 := hx0_d) (hx8 := hx8_d) (hx20 := hx20_d) (hx29 := hx29_d) (hvregs := hvregs_d) (hcl := hcl_d)
    (ha2_i := ha2_i) (hpa := hpa) (ht6d8_i := ht6d8_i) (hniels0 := hniels0)
  intro s_l0 a2_bs ext_0 comp_0 hregs0 ha2_b ha2_v hext_0 hcomp_0
  apply naf_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l0 (edExtOfBytes a_rest) 0 2032 1872 (by decide) _ _
    w_s10' w_s18' b0 b1_i a2_bs t5c0_i t638_i ext_0 comp_0 _ _
    (hsp0_align := hsp_align) (hregs := hregs0) (hai_i := hb0) (hai_i1 := hb1_i)
    (ha2_b := ha2_b) (ha2_v := ha2_v) (ht5c0 := ht5c0_i) (ht638 := ht638_i) (ht660 := hext_0) (hcomp := hcomp_0)
  intro s_l1 w10_1 w18_1 b1 t5c0_1 t638_1 ext_1 comp_1 hregs1 hb1 ht5c0_1 ht638_1 hext_1 hcomp_1
  apply naf_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l1 (edExtOfBytes a_rest) 1 1872 1712 (by decide) _ _
    w10_1 w18_1 b1 b2_i a2_bs t5c0_1 t638_1 ext_1 comp_1 _ _
    (hsp0_align := hsp_align) (hregs := hregs1) (hai_i := hb1) (hai_i1 := hb2_i)
    (ha2_b := ha2_b) (ha2_v := ha2_v) (ht5c0 := ht5c0_1) (ht638 := ht638_1) (ht660 := hext_1) (hcomp := hcomp_1)
  intro s_l2 w10_2 w18_2 b2 t5c0_2 t638_2 ext_2 comp_2 hregs2 hb2 ht5c0_2 ht638_2 hext_2 hcomp_2
  apply naf_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l2 (edExtOfBytes a_rest) 2 1712 1552 (by decide) _ _
    w10_2 w18_2 b2 b3_i a2_bs t5c0_2 t638_2 ext_2 comp_2 _ _
    (hsp0_align := hsp_align) (hregs := hregs2) (hai_i := hb2) (hai_i1 := hb3_i)
    (ha2_b := ha2_b) (ha2_v := ha2_v) (ht5c0 := ht5c0_2) (ht638 := ht638_2) (ht660 := hext_2) (hcomp := hcomp_2)
  intro s_l3 w10_3 w18_3 b3 t5c0_3 t638_3 ext_3 comp_3 hregs3 hb3 ht5c0_3 ht638_3 hext_3 hcomp_3
  apply naf_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l3 (edExtOfBytes a_rest) 3 1552 1392 (by decide) _ _
    w10_3 w18_3 b3 b4_i a2_bs t5c0_3 t638_3 ext_3 comp_3 _ _
    (hsp0_align := hsp_align) (hregs := hregs3) (hai_i := hb3) (hai_i1 := hb4_i)
    (ha2_b := ha2_b) (ha2_v := ha2_v) (ht5c0 := ht5c0_3) (ht638 := ht638_3) (ht660 := hext_3) (hcomp := hcomp_3)
  intro s_l4 w10_4 w18_4 b4 t5c0_4 t638_4 ext_4 comp_4 hregs4 hb4 ht5c0_4 ht638_4 hext_4 hcomp_4
  apply naf_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l4 (edExtOfBytes a_rest) 4 1392 1232 (by decide) _ _
    w10_4 w18_4 b4 b5_i a2_bs t5c0_4 t638_4 ext_4 comp_4 _ _
    (hsp0_align := hsp_align) (hregs := hregs4) (hai_i := hb4) (hai_i1 := hb5_i)
    (ha2_b := ha2_b) (ha2_v := ha2_v) (ht5c0 := ht5c0_4) (ht638 := ht638_4) (ht660 := hext_4) (hcomp := hcomp_4)
  intro s_l5 w10_5 w18_5 b5 t5c0_5 t638_5 ext_5 comp_5 hregs5 hb5 ht5c0_5 ht638_5 hext_5 hcomp_5
  apply naf_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l5 (edExtOfBytes a_rest) 5 1232 1072 (by decide) _ _
    w10_5 w18_5 b5 b6_i a2_bs t5c0_5 t638_5 ext_5 comp_5 _ _
    (hsp0_align := hsp_align) (hregs := hregs5) (hai_i := hb5) (hai_i1 := hb6_i)
    (ha2_b := ha2_b) (ha2_v := ha2_v) (ht5c0 := ht5c0_5) (ht638 := ht638_5) (ht660 := hext_5) (hcomp := hcomp_5)
  intro s_l6 w10_6 w18_6 b6 t5c0_6 t638_6 ext_6 comp_6 hregs6 hb6 ht5c0_6 ht638_6 hext_6 hcomp_6
  apply naf_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l6 (edExtOfBytes a_rest) 6 1072 912 (by decide) _ _
    w10_6 w18_6 b6 b7_i a2_bs t5c0_6 t638_6 ext_6 comp_6 _ _
    (hsp0_align := hsp_align) (hregs := hregs6) (hai_i := hb6) (hai_i1 := hb7_i)
    (ha2_b := ha2_b) (ha2_v := ha2_v) (ht5c0 := ht5c0_6) (ht638 := ht638_6) (ht660 := hext_6) (hcomp := hcomp_6)
  intro s_l7 w10_7 w18_7 b7 t5c0_7 t638_7 ext_7 comp_7 hregs7 hb7 ht5c0_7 ht638_7 hext_7 hcomp_7
  rcases hregs7 with ⟨hpc7, hrun7, hsp, hx26_7, hx29_7, hvregs7, hcl7⟩
  apply sepWP_merge8_naf_table s0.sp (edExtOfBytes a_rest)
    (h0 := hb0) (h1 := hb1) (h2 := hb2) (h3 := hb3)
    (h4 := hb4) (h5 := hb5) (h6 := hb6) (h7 := hb7)
  intro table_bs htable_len ⟨htable_b, htable_v⟩
  clear hregs0 hregs1 hregs2 hregs3 hregs4 hregs5 hregs6
  clear_dead_vars [s1, s2, s_dbl, s_l0, s_l1, s_l2, s_l3, s_l4, s_l5, s_l6]
  try clear s1 s2 s_dbl s_l0 s_l1 s_l2 s_l3 s_l4 s_l5 s_l6
  wp_sym_steps 4
  wp_dalek_call20 memcpy_ok; clean_prev_sf
  wp_sym_steps 8
  have ha2_len : a2_bs.length = 160 := ha2_b.1
  close_cells (s0.sp - 96#64) 96 12
  apply sepWP_unpeel_stack_region s0.sp 112 16 96
  apply sepWP_unpeel_stack_bytes s0.sp 272 160 112
  apply sepWP_unpeel_stack_bytes s0.sp 432 160 272
  apply sepWP_unpeel_stack_bytes s0.sp 472 40 432
  apply sepWP_unpeel_stack_bytes s0.sp 592 120 472
  apply sepWP_unpeel_stack_bytes s0.sp 752 160 592
  apply sepWP_unpeel_stack_bytes s0.sp 2032 1280 752
  close_cells (s0.sp - 2064#64) 32 4
  apply sepWP_unpeel_stack_region s0.sp 2064 32 2032
  apply sepWP_unpeel_stack_region s0.sp 2640 576 2064
  have htable_pts : ∀ i < 8, fe51Point4Bounded (ProofLib.ByteSlice.slice table_bs (160 * i) 160) 9007199254740992 := htable_b.2
  wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.NafLookupTable2

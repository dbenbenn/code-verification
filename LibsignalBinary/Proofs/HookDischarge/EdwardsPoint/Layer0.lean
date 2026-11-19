/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs
import ProofLib.SepLogic.LoopTactics
import ProofLib.SepLogic.ByteRegion
import VerifiedLibraries.Musl.Proofs.MemOps
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Layer 0 Memory and Constant-Time Helpers

Proves the Layer 0 contracts of `dalekCliMultiLib`:
- `black_box_u8_ok : BlackBoxU8Ok` (`B00`, 5 insns)
- `memcpy_ok : MemcpyOk` and `memcpy_ro_ok : MemcpyRoOk` (`B36`, 99 insns, stock `musl` `memcpy`)
- `slice32_ct_eq_ok : Slice32CtEqOk` (`B24`, 210 insns, 32 `BL` + 1 `B` to `B00`)
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0

open Arm64 Arm64.Obj ProofLib
open VerifiedLibraries.Musl (
  memcpySymWords memcpySymSpec memcpyROSymSpec memcpy_codeAt_ok_sym memcpyRO_codeAt_ok_sym)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase DalekBlockConstOk
  dalekLeaf_ok dalekCaller_ok withCodeLoaded_of_subroutine_ok
  dalekBlockPlacement_ρ resolve_blk00)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  memcpySpec MemcpyOk memcpyRoSpec MemcpyRoOk
  blackBoxU8Spec BlackBoxU8Ok slice32CtEqSpec Slice32CtEqOk)

/-! ## 1. Per-Block Fetch Generation (`B00` & `B24`) -/

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 00 dalekCliMultiLib DalekCliPlacement 5 rebase rho sub

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 24 dalekCliMultiLib DalekCliPlacement 210 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl24_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl24.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

public section

/-! ## 2. `subtle::black_box::<u8>` (`B00`) -/

theorem black_box_u8_ok : BlackBoxU8Ok := by
  intro _
  apply dalekLeaf_ok dalekCliPC00 dalekCliPl00
  intro b hb hbase
  wp_init
  have hst : stackFrame s0 16 =
      ((∃∗ v : BitVec 8, (s0.sp - 4#64) ↦₈ v) ∗
        (memRegion (s0.sp - 16#64) 12 ∗ memRegion (s0.sp - 3#64) 3)) := by
    change memRegion (s0.sp - 16#64) 16 = _
    rw [memRegion_split3 (s0.sp - 16#64) 16 12 1 (by decide) (by decide), memRegion_one]
    have h1 : s0.sp - 16#64 + 12#64 = s0.sp - 4#64 := by bv_arith
    have h2 : s0.sp - 16#64 + 13#64 = s0.sp - 3#64 := by bv_arith
    rw [h1, h2]
  rw [hst]
  wp_pull_exists
  wp_steps
  refine SepWP.weaken_pre (P' := stackFrame s0 16)
    (by rw [hst]; exact sepConj_mono_left (Entails.sepExists_right _ (Entails.refl _))) ?_
  clear hst
  wp_done

/-! ## 3. Stock `musl` `memcpy` (`B36`, RW & RO) -/

private theorem dalekCliBlocks_36_lt : 36 < dalekCliMultiLib.blocks.length := by decide

private theorem dalekCliBlk36_checkSegment :
    (dalekCliMultiLib.blocks[36]'dalekCliBlocks_36_lt).checkSegment
      0 memcpySymWords [] = true := by
  decide +kernel

private theorem dalekCliBlk36_hasWords [DalekCliPlacement] :
    (dalekCliMultiLib.blockProgram dalekCliMpl 36).hasWords
      (dalekCliMpl.base 36) memcpySymWords := by
  have hseg := (Obj.MultiPlacedLib.hasWords_of_checkSegment
    (X := fun _ => none) (svc := Syscall.standard)
    dalekCliBlocks_36_lt DalekCliPlacement.placeable dalekCliBlk36_checkSegment).1
  simpa [Obj.patchRelocs] using hseg

theorem memcpy_ok : MemcpyOk := by
  intro _
  apply withCodeLoaded_of_subroutine_ok
  refine subroutine_ok_refine_entails
    (memcpy_codeAt_ok_sym (dalekCliMultiLib.blockProgram dalekCliMpl 36)
      (dalekCliMpl.base 36) dalekCliBlk36_hasWords) ?_
  rintro ⟨dst, src, n, dst_bs, src_bs⟩ R s0 hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hdst_len, hsrc_len⟩, hm⟩ := hpre
  refine ⟨(dst, src, n, src_bs), ?_, fun sf => ?_⟩
  · simp only [memcpySymSpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes, CType.SliceLen,
      CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, trivial, hsrc_len.symm⟩, ?_⟩
    have hm' : s0.mem ⊨ (dst ↦ₛ dst_bs) ∗ (src ↦ₛ src_bs) ∗ R := by
      rwa [show ((dst ↦ₛ dst_bs) ∗ (src ↦ₛ src_bs) ∗ R) =
        ((src ↦ₛ src_bs) ∗ (dst ↦ₛ dst_bs) ∗ R) by sep_ac_rfl]
    have hent : ((dst ↦ₛ dst_bs) ∗ (src ↦ₛ src_bs) ∗ R) ⊢
        (memRegion dst src_bs.length ∗ (src ↦ₛ src_bs) ∗ R) := by
      rw [hsrc_len, ← hdst_len]
      exact sepConj_mono_left (pointsToBytes_entails_memRegion dst dst_bs)
    exact Satisfies.mono hent hm'
  · simp only [memcpySymSpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes]
    rw [show (⌜True ∧ sf.readReg64 Reg.x0 = dst⌝ ∗ ((dst ↦ₛ src_bs) ∗ (src ↦ₛ src_bs))) =
      ((src ↦ₛ src_bs) ∗ (dst ↦ₛ src_bs) ∗ ⌜True ∧ sf.readReg64 Reg.x0 = dst⌝) by sep_ac_rfl]
    exact sepConj_mono_right (sepConj_mono_right (Entails.pure_mono And.right))

theorem memcpy_ro_ok : MemcpyRoOk := by
  intro _
  apply withCodeLoaded_of_subroutine_ok
  refine subroutine_ok_refine_entails
    (memcpyRO_codeAt_ok_sym (dalekCliMultiLib.blockProgram dalekCliMpl 36)
      (dalekCliMpl.base 36) dalekCliBlk36_hasWords) ?_
  rintro ⟨dst, src, n, dst_bs, src_bs⟩ R s0 hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hdst_len, hsrc_len⟩, hm⟩ := hpre
  refine ⟨(dst, src, n, src_bs), ?_, fun sf => ?_⟩
  · simp only [memcpyROSymSpec, CType.MutSlice8, CType.Bytes,
      CType.SliceLen, CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, trivial, hsrc_len.symm⟩, ?_⟩
    have hm' : s0.mem ⊨ (dst ↦ₛ dst_bs) ∗ (src ↦ᵣ src_bs) ∗ R := by
      rwa [show ((dst ↦ₛ dst_bs) ∗ (src ↦ᵣ src_bs) ∗ R) =
        ((src ↦ᵣ src_bs) ∗ (dst ↦ₛ dst_bs) ∗ R) by sep_ac_rfl]
    have hent : ((dst ↦ₛ dst_bs) ∗ (src ↦ᵣ src_bs) ∗ R) ⊢
        (memRegion dst src_bs.length ∗ (src ↦ᵣ src_bs) ∗ R) := by
      rw [hsrc_len, ← hdst_len]
      exact sepConj_mono_left (pointsToBytes_entails_memRegion dst dst_bs)
    exact Satisfies.mono hent hm'
  · simp only [memcpyROSymSpec, CType.MutSlice8, CType.Bytes]
    rw [show (⌜True ∧ sf.readReg64 Reg.x0 = dst⌝ ∗ ((dst ↦ₛ src_bs) ∗ (src ↦ᵣ src_bs))) =
      ((src ↦ᵣ src_bs) ∗ (dst ↦ₛ src_bs) ∗ ⌜True ∧ sf.readReg64 Reg.x0 = dst⌝) by sep_ac_rfl]
    exact sepConj_mono_right (sepConj_mono_right (Entails.pure_mono And.right))

/-! ## 4. `<[u8] as subtle::ConstantTimeEq>::ct_eq` (`B24`) -/

@[simp, arm64_norm]
private theorem cset_eq_byte (x y : BitVec 8) :
    (if (BitVec.zeroExtend 32 x != BitVec.zeroExtend 32 y) = true then (0#64 : BitVec 64) else 1#64) =
      if x == y then 1#64 else 0#64 := by
  by_cases h : x = y <;> simp [h] <;> revert h <;> bv_bits

@[simp, arm64_norm]
private theorem cset_eq_byte8 (x y : BitVec 8) :
    (if (BitVec.zeroExtend 32 x != BitVec.zeroExtend 32 y) = true then (0#8 : BitVec 8) else 1#8) =
      if x == y then 1#8 else 0#8 := by
  by_cases h : x = y <;> simp [h] <;> revert h <;> bv_bits

@[simp, arm64_norm]
private theorem and64_ite_one_zero (p q : Bool) :
    ((if p then (1#64 : BitVec 64) else 0#64) &&& (if q then (1#64 : BitVec 64) else 0#64)) =
      if (p && q) then (1#64 : BitVec 64) else 0#64 := by
  cases p <;> cases q <;> rfl

@[simp, arm64_norm]
private theorem ze32_ite_one_zero (p : Bool) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (if p then (1#64 : BitVec 64) else 0#64)) =
      if p then (1#64 : BitVec 64) else 0#64 := by
  cases p <;> rfl

@[simp, arm64_norm]
private theorem trunc8_ite_one_zero (p : Bool) :
    BitVec.truncate 8 (if p then (1#64 : BitVec 64) else 0#64) =
      if p then (1#8 : BitVec 8) else 0#8 := by
  cases p <;> rfl

@[simp, arm64_norm]
private theorem ze64_ite_one_zero8 (p : Bool) :
    BitVec.zeroExtend 64 (if p then (1#8 : BitVec 8) else 0#8) =
      if p then (1#64 : BitVec 64) else 0#64 := by
  cases p <;> rfl

@[simp, arm64_norm]
private theorem and64_ite_one_zero_mask1 (p : Bool) :
    ((if p then (1#64 : BitVec 64) else 0#64) &&& 4294967297#64) =
      if p then (1#64 : BitVec 64) else 0#64 := by
  cases p <;> rfl

private def prefixEq (xs ys : List (BitVec 8)) : Nat → Bool
  | 0 => xs.getD 0 0#8 == ys.getD 0 0#8
  | k + 1 => prefixEq xs ys k && (xs.getD (k + 1) 0#8 == ys.getD (k + 1) 0#8)

private theorem prefixEq_eq_true_iff (xs ys : List (BitVec 8)) (n : Nat) :
    prefixEq xs ys n = true ↔ ∀ i ≤ n, xs.getD i 0#8 = ys.getD i 0#8 := by
  induction n with
  | zero =>
    simp [prefixEq]
  | succ k ih =>
    simp only [prefixEq, Bool.and_eq_true, ih, beq_iff_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hik : i = k + 1
      · subst hik; exact h2
      · exact h1 i (by omega)
    · intro h
      exact ⟨fun i hi => h i (Nat.le_succ_of_le hi), h (k + 1) (Nat.le_refl _)⟩

private theorem prefixEq_31_eq_beq (xs ys : List (BitVec 8))
    (hxs : xs.length = 32) (hys : ys.length = 32) :
    prefixEq xs ys 31 = (xs == ys) := by
  rw [Bool.eq_iff_iff, prefixEq_eq_true_iff, beq_iff_eq]
  constructor
  · intro h
    apply List.ext_getElem
    · omega
    · intro i hi1 hi2
      have hle : i ≤ 31 := by omega
      have hi := h i hle
      simpa [List.getD_eq_getElem?_getD, hi1, hi2] using hi
  · rintro rfl _ _
    rfl

end

abbrev rust_spec blackBoxU8X0Spec (v : u8) : (ret : u64)
  stack   16
  ensures ⌜ret = BitVec.zeroExtend 64 v⌝

private theorem black_box_u8_x0_ok : DalekBlockConstOk 0 blackBoxU8X0Spec := by
  intro _
  apply dalekLeaf_ok dalekCliPC00 dalekCliPl00
  intro b hb hbase
  wp_init
  have hst : stackFrame s0 16 =
      ((∃∗ v : BitVec 8, (s0.sp - 4#64) ↦₈ v) ∗
        (memRegion (s0.sp - 16#64) 12 ∗ memRegion (s0.sp - 3#64) 3)) := by
    change memRegion (s0.sp - 16#64) 16 = _
    rw [memRegion_split3 (s0.sp - 16#64) 16 12 1 (by decide) (by decide), memRegion_one]
    have h1 : s0.sp - 16#64 + 12#64 = s0.sp - 4#64 := by bv_arith
    have h2 : s0.sp - 16#64 + 13#64 = s0.sp - 3#64 := by bv_arith
    rw [h1, h2]
  rw [hst]
  wp_pull_exists
  wp_steps
  refine SepWP.weaken_pre (P' := stackFrame s0 16)
    (by rw [hst]; exact sepConj_mono_left (Entails.sepExists_right _ (Entails.refl _))) ?_
  clear hst
  wp_done

open Lean Meta Elab Tactic in
local elab "clean_prev_sf" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut stateDecls : Array LocalDecl := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && decl.type.isConstOf ``Arm64.State && decl.userName != `s0 then
      stateDecls := stateDecls.push decl
  if stateDecls.size ≥ 2 then
    let (prevSf, currSf) := (stateDecls[stateDecls.size - 2]!, stateDecls[stateDecls.size - 1]!)
    let mut prevEqs : Array FVarId := #[]
    let mut prevHyps : Array FVarId := #[]
    let mut currHyps : Array FVarId := #[]
    for decl in lctx do
      if !decl.isImplementationDetail && decl.fvarId != prevSf.fvarId && decl.fvarId != currSf.fvarId then
        let ty ← instantiateMVars decl.type
        if ty.containsFVar prevSf.fvarId then
          prevHyps := prevHyps.push decl.fvarId
          if !ty.containsFVar currSf.fvarId then
            if let some (_, lhs, _) := ty.eq? then
              if lhs.containsFVar prevSf.fvarId then prevEqs := prevEqs.push decl.fvarId
          else currHyps := currHyps.push decl.fvarId
    for cId in currHyps do
      let cIdent := mkIdent (← cId.getUserName)
      for pId in prevEqs do
        let pIdent := mkIdent (← pId.getUserName)
        try evalTactic (← `(tactic| rw [$pIdent:term] at $cIdent:ident)) catch _ => pure ()
    let mut toClear : Array Ident := #[]
    for pId in prevHyps do
      if !currHyps.contains pId then toClear := toClear.push (mkIdent (← pId.getUserName))
    toClear := toClear.push (mkIdent prevSf.userName)
    for id in toClear do
      try evalTactic (← `(tactic| clear $id:ident)) catch _ => pure ()

public section

set_option maxHeartbeats 800000 in
theorem slice32_ct_eq_ok : Slice32CtEqOk := by
  intro _
  apply dalekCaller_ok dalekCliPC24 dalekCliPl24
  intro b hb hbase
  wp_init
  have hstack : stackFrame s0 64 =
      memRegion (s0.sp - 64#64) 16 ∗ cells (s0.sp - 48#64) 6 := by
    change stackAt s0.sp (16 + 8 * 6) = _
    rw [stackAt_split_cells s0.sp 16 6 (by decide)]
    change memRegion (s0.sp - 48#64 - 16#64) 16 ∗ cells (s0.sp - 48#64) 6 = _
    have h64 : s0.sp - 48#64 - 16#64 = s0.sp - 64#64 := by bv_arith
    rw [h64]
  rw [hstack]
  cells_unfold
  wp_pull_exists
  wp_cut_codeLoaded
  wp_steps
  wp_dalek_call black_box_u8_x0_ok
  iterate 31 (wp_steps; wp_dalek_call black_box_u8_x0_ok; clean_prev_sf)
  wp_steps
  have hst_cur : stackFrame sf_1 16 = memRegion (s0.sp - 64#64) 16 := by
    simp only [stackFrame, hsp_sf_1]
    congr 1; bv_omega
  rw [hst_cur]
  refine SepWP.weaken_pre (P' := a_1 ↦ₛ a_2 ∗ a ↦ₛ a_rest ∗ stackFrame s0 64) ?_ ?_
  · rw [hstack]
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_right (s0.readReg64 (Reg.gpr 29#5))
      (Entails.sepExists_right (s0.readReg64 (Reg.gpr 30#5))
      (Entails.sepExists_right (s0.readReg64 (Reg.gpr 22#5))
      (Entails.sepExists_right (s0.readReg64 (Reg.gpr 21#5))
      (Entails.sepExists_right (s0.readReg64 (Reg.gpr 20#5))
      (Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5))
        (Entails.of_eq ?_))))))
    sep_ac_rfl
  clear hstack
  have hst64 : stackFrame s0 64 =
      stackFrame s0 16 ∗ memRegion (s0.sp - 64#64) 48 := by
    change stackAt s0.sp (16 + 48) = stackAt s0.sp 16 ∗ memRegion (s0.sp - 64#64) 48
    rw [stackAt_split_bottom s0.sp 16 48 (by decide)]
    sep_ac_rfl
  rw [hst64]
  have heq32 := prefixEq_31_eq_beq a_2 a_rest h_4 h_1
  simp only [prefixEq, Nat.reduceAdd] at heq32
  simp only [← Bool.and_assoc, heq32]
  wp_dalek_tailcall black_box_u8_ok
  try simp only [stackFrame] at hst64 ⊢
  try rw [← hst64]
  wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `FieldElement51::pow22501` and `sqrt_ratio_i` Machine-Code Proofs

Machine-code proofs in `dalekCliMultiLib` for `FieldElement51::pow22501` (`B04`) and
`FieldElement51::sqrt_ratio_i` (`B03`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Pow

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 sqrtM1 fpMul fpNeg fpSq fpPow natToLeBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase DalekBlockOk DalekBlockConstOk
  dalekLeaf_ok dalekCaller_ok dalekBlockPlacement_ρ
  dalekCall_of_blockOk seq_codeLoaded_lr goalIsSeqCodeLoaded clearOldCodeLoadedHyps)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51Val fe51ValOfBytes fe51SqrtM1Bytes fe51_sqrt_m1)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  Fe51Pow22501Ok Fe51SqrtRatioIOk fe51LimbsBounded sqrtRatioM1)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (
  fe51SqrtM1Bytes_length fe51SqrtM1_readLE_0 fe51SqrtM1_readLE_8
  fe51SqrtM1_readLE_16 fe51SqrtM1_readLE_24 fe51SqrtM1_readLE_32 fe51SqrtM1_val)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe write64_length_eq readLE_write64_self' readLE_write64_ne sub_ofNat64_add
  fe51_canonical_mod2 sepWP_callee_shrink sepWP_callee_grow fpPow_mod_eq_pow_mod
  pointsToBytes40_eq_cells pointsToBytes32_eq_cells64
  sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes sepWP_abstract_bytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (
  sepWP_split32_sub sepWP_combine32_sub packFe51Bytes pointsToBytes_packFe51Bytes
  fe51ValOfBytes_packFe51Bytes fe51LimbsBounded_packFe51Bytes
  pointsToBytes_list32 pointsToBytes32_eq_cells8 packCanonical51Bytes
  natToLeBytes_32_beq_iff fe51_to_bytes_canonical_val fe51_to_bytes_math
  bv64_ushr51_toNat bv64_and_mask51_toNat bv64_add_toNat_of_lt
  bv64_mask51_add_ushr51_toNat fe51_carry1_nat)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0 (
  slice32_ct_eq_ok black_box_u8_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51 (
  fe51_to_bytes_ok fe51_mul_ok fe51_mul_ro_right_ok fe51_mul_ro_left_ok fe51_pow2k_nat_ok)

arm64_proof_prelude

attribute [local irreducible] MultiPlacedLib.CodeLoaded

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 03 dalekCliMultiLib DalekCliPlacement 653 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl03_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl03.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 04 dalekCliMultiLib DalekCliPlacement 101 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl04_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl04.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open Lean Meta Elab Tactic in
local elab "clean_prev_sf2" : tactic => withMainContext do
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

private theorem pc_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).pc = pc := rfl
private theorem pc_setMem' (s : State) (m : Memory) : (s.setMem m).pc = s.pc := rfl
private theorem pc_setPState' (s : State) (ps : PState) : (s.setPState ps).pc = s.pc := rfl
private theorem pc_writeVReg128' (s : State) (i : BitVec 5) (v : BitVec 128) : (s.writeVReg128 i v).pc = s.pc := rfl
private theorem pc_advancePC' (s : State) : s.advancePC.pc = s.pc + 4#64 := rfl
private theorem pc_writeReg64' (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).pc = s.pc := rfl
private theorem pc_writeReg32' (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).pc = s.pc := rfl
private theorem pc_writeReg' (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).pc = s.pc := rfl
private theorem status_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := rfl
private theorem status_setMem' (s : State) (m : Memory) : (s.setMem m).status = s.status := rfl
private theorem status_setPState' (s : State) (ps : PState) : (s.setPState ps).status = s.status := rfl
private theorem status_writeVReg128' (s : State) (i : BitVec 5) (v : BitVec 128) : (s.writeVReg128 i v).status = s.status := rfl
private theorem status_advancePC' (s : State) : s.advancePC.status = s.status := rfl
private theorem status_writeReg64' (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).status = s.status := rfl
private theorem status_writeReg32' (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).status = s.status := rfl
private theorem status_writeReg' (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).status = s.status := rfl
private theorem mem_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := rfl
private theorem mem_setPState' (s : State) (ps : PState) : (s.setPState ps).mem = s.mem := rfl
private theorem mem_writeVReg128' (s : State) (i : BitVec 5) (v : BitVec 128) : (s.writeVReg128 i v).mem = s.mem := rfl
private theorem mem_advancePC' (s : State) : s.advancePC.mem = s.mem := rfl
private theorem mem_writeReg64' (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).mem = s.mem := rfl
private theorem mem_writeReg32' (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).mem = s.mem := rfl
private theorem mem_writeReg' (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).mem = s.mem := rfl

open Lean Meta Elab Tactic in
local elab "close_cut_codeLoaded" : tactic => do
  evalTactic (← `(tactic| (
    apply SepWP.done
    · try simp only [pc_setPC', pc_setMem', pc_setPState', pc_writeVReg128', pc_advancePC',
        pc_writeReg64', pc_writeReg32', pc_writeReg']
      rfl
    · try simp only [status_setPC', status_setMem', status_setPState', status_writeVReg128', status_advancePC',
        status_writeReg64', status_writeReg32', status_writeReg']
      first | with_reducible assumption | assumption)))
  clearOldCodeLoadedHyps
  let hclId := mkIdent (← mkFreshUserName `hcl_cut)
  evalTactic (← `(tactic| intro $hclId:ident))

open Lean Meta Elab Tactic in
local elab "wp_dalek_call_fast " hcall:term : tactic => do
  if ← goalIsSeqCodeLoaded (← getMainGoal) then
    evalTactic (← `(tactic| close_cut_codeLoaded))
  let gCur ← getMainGoal
  let progStx ← gCur.withContext do
    let ty := (← instantiateMVars (← gCur.getType)).consumeMData
    Term.exprToSyntax (ty.getArg! 0)
  let hclPostId := mkIdent (← mkFreshUserName `hcl_post)
  evalTactic (← `(tactic| (
    apply seq_codeLoaded_lr (by
      try simp only [mem_setPC', mem_setPState', mem_writeVReg128', mem_advancePC',
        mem_writeReg64', mem_writeReg32', mem_writeReg']
      first | with_reducible assumption | assumption)
    wp_call (dalekCall_of_blockOk $progStx $hcall))))
  let postCallGoals ← getGoals
  let mut newGoals : List MVarId := []
  for g in postCallGoals do
    if ← goalIsSeqCodeLoaded g then
      setGoals [g]
      evalTactic (← `(tactic| (
        apply SepWP.done
        · first
            | with_reducible assumption
            | (conv => rhs; simp (config := { decide := true }) only [wp_norm, arm64_norm]
               with_reducible assumption)
            | (wp_norm_goal; rfl)
            | rfl
        · first | with_reducible assumption | wp_norm_lhs | assumption)))
      clearOldCodeLoadedHyps
      evalTactic (← `(tactic| intro $hclPostId:ident))
      newGoals := newGoals ++ (← getGoals)
    else
      newGoals := newGoals ++ [g]
  setGoals newGoals

private theorem sepWP_callee_224_to_96 (sp : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (sp - 816#64 - 224#64) 224 ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((memRegion (sp - 816#64 - 96#64) 96 ∗ stackAt (sp - 912#64) 128) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have h912 : sp - 816#64 - 96#64 = sp - 912#64 := by rw [BitVec.sub_sub]; rfl
  rw [hf]; change SepWP prog target_pc s (stackAt (sp - 816#64) (128 + 96) ∗ P) post oom
  rw [stackAt_region (sp - 816#64) 128 96 (by decide), sepConj_comm (stackAt _ _) (memRegion _ _)]; rw [← h912] at hnext; exact hnext

private theorem sepWP_callee_96_to_224 (sp : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp - 816#64 - 96#64) 96 ∗ stackAt (sp - 912#64) 128) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (memRegion (sp - 816#64 - 224#64) 224 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have h912 : sp - 912#64 = sp - 816#64 - 96#64 := by rw [BitVec.sub_sub]; rfl
  rw [hf, h912, sepConj_comm (memRegion _ _) (stackAt _ _), ← stackAt_region (sp - 816#64) 128 96 (by decide)]; exact hnext

private theorem sepWP_split2_80 (base : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (base ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 80 := by assumption)
    (hnext : ∀ b0 b1 : List (BitVec 8), b0.length = 40 → b1.length = 40 →
      SepWP prog target_pc s (((base ↦ₛ b0) ∗ ((base + 40#64) ↦ₛ b1)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hs0 := (congrArg (base ↦ₛ ·) (List.take_append_drop 40 bs).symm).trans (pointsToBytes_append base (bs.take 40) (bs.drop 40))
  rw [show (bs.take 40).length = 40 by simp [hbs]] at hs0; rw [hf, hs0]; exact hnext (bs.take 40) (bs.drop 40) (by simp [hbs]) (by simp [hbs])

private theorem sepWP_merge2_80 (base : BitVec 64) {b0 b1 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((base ↦ₛ b0) ∗ ((base + 40#64) ↦ₛ b1)) ∗ P) := by sep_frame) (h0 : b0.length = 40 := by assumption)
    (hnext : SepWP prog target_pc s (((base ↦ₛ (b0 ++ b1)) ∗ P)) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hm : (base ↦ₛ (b0 ++ b1)) = (base ↦ₛ b0) ∗ ((base + 40#64) ↦ₛ b1) := by rw [pointsToBytes_append, h0]
  rw [hf, ← hm]; exact hnext

private theorem pow_pow_mod_step (w_val src_val A E K E' m : Nat)
    (hw : w_val % m = src_val ^ K % m) (hsrc : src_val % m = A ^ E % m) (hE' : E * K = E') : w_val % m = A ^ E' % m := by
  rw [hw, Nat.pow_mod src_val K m, hsrc, ← Nat.pow_mod (A ^ E) K m, ← Nat.pow_mul, hE']

private theorem mul_pow_mod_step (w_val s1_val s2_val A E1 E2 E' m : Nat)
    (hw : w_val % m = (s1_val * s2_val) % m) (hs1 : s1_val % m = A ^ E1 % m) (hs2 : s2_val % m = A ^ E2 % m) (hE' : E1 + E2 = E') :
    w_val % m = A ^ E' % m := by
  rw [hw, Nat.mul_mod s1_val s2_val m, hs1, hs2, ← Nat.mul_mod (A ^ E1) (A ^ E2) m, ← Nat.pow_add, hE']

private theorem fe51_pow2k_chain_props (w : List (BitVec 8)) (E' : Nat) {src : List (BitVec 8)} {A E K : Nat}
    (hb : fe51LimbsBounded w (2 ^ 52) := by assumption)
    (hv : fe51ValOfBytes w % p25519 = (fe51ValOfBytes src) ^ K % p25519 := by assumption)
    (hsrc : fe51ValOfBytes src % p25519 = A ^ E % p25519 := by assumption) (hE' : E * K = E' := by decide) :
    w.length = 40 ∧ fe51LimbsBounded w (2 ^ 54) ∧ fe51LimbsBounded w (2 ^ 52) ∧ fe51ValOfBytes w % p25519 = A ^ E' % p25519 := by
  have ⟨hl, h0, h1, h2, h3, h4⟩ := hb
  exact ⟨hl, ⟨hl, by omega, by omega, by omega, by omega, by omega⟩, hb, pow_pow_mod_step _ _ A E K E' p25519 hv hsrc hE'⟩

private theorem fe51_mul_chain_props (w : List (BitVec 8)) (E' : Nat) {src1 src2 : List (BitVec 8)} {A E1 E2 : Nat}
    (hb : fe51LimbsBounded w (2 ^ 52) := by assumption)
    (hv : fe51ValOfBytes w % p25519 = (fe51ValOfBytes src1 * fe51ValOfBytes src2) % p25519 := by assumption)
    (hs1 : fe51ValOfBytes src1 % p25519 = A ^ E1 % p25519 := by assumption)
    (hs2 : fe51ValOfBytes src2 % p25519 = A ^ E2 % p25519 := by assumption) (hE' : E1 + E2 = E' := by decide) :
    w.length = 40 ∧ fe51LimbsBounded w (2 ^ 54) ∧ fe51LimbsBounded w (2 ^ 52) ∧ fe51ValOfBytes w % p25519 = A ^ E' % p25519 := by
  have ⟨hl, h0, h1, h2, h3, h4⟩ := hb
  exact ⟨hl, ⟨hl, by omega, by omega, by omega, by omega, by omega⟩, hb, mul_pow_mod_step _ _ _ A E1 E2 E' p25519 hv hs1 hs2 hE'⟩

private theorem fe51_mul_fpPow_props (w : List (BitVec 8)) (E' : Nat) {src1 src2 : List (BitVec 8)} {A E1 E2 : Nat}
    (hb : fe51LimbsBounded w (2 ^ 52) := by assumption)
    (hv : fe51ValOfBytes w % p25519 = (fe51ValOfBytes src1 * fe51ValOfBytes src2) % p25519 := by assumption)
    (hs1 : fe51ValOfBytes src1 % p25519 = A ^ E1 % p25519 := by assumption)
    (hs2 : fe51ValOfBytes src2 % p25519 = A ^ E2 % p25519 := by assumption)
    (hE' : E1 + E2 = E' := by decide) (hlt : E' < 2 ^ 256 := by decide) :
    w.length = 40 ∧ fe51LimbsBounded w (2 ^ 52) ∧ fe51ValOfBytes w % p25519 = fpPow (A % p25519) E' := by
  obtain ⟨hl, _, hb52, hpow⟩ := fe51_mul_chain_props w E' hb hv hs1 hs2 hE'
  exact ⟨hl, hb52, hpow.trans (fpPow_mod_eq_pow_mod A E' hlt).symm⟩

private theorem copy40_fe51_props (dst src : List (BitVec 8)) (V : Nat)
    (hdst : dst.length = 40) (hsrc_b : fe51LimbsBounded src (2 ^ 52)) (hsrc_v : fe51ValOfBytes src % p25519 = V) :
    let res := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      dst 32 (ByteSlice.readLE src 32 8)) 0 (ByteSlice.readLE src 0 8))
      8 (ByteSlice.readLE src 8 8)) 16 (ByteSlice.readLE src 16 8)) 24 (ByteSlice.readLE src 24 8)
    res.length = 40 ∧ fe51LimbsBounded res (2 ^ 52) ∧ fe51ValOfBytes res % p25519 = V := by
  haveI : HasLenGe dst 40 := ⟨by omega⟩; intro res
  have hlen : res.length = 40 := by simp (disch := decide) only [res, write64_length_eq, hdst, Nat.min_eq_left]
  have hb : fe51LimbsBounded res (2 ^ 52) := by
    unfold fe51LimbsBounded; simp (disch := decide) only [res, readLE_write64_self', readLE_write64_ne, write64_length_eq, hdst, Nat.min_eq_left]; exact ⟨trivial, hsrc_b.2⟩
  have hv : fe51ValOfBytes res % p25519 = V := by
    unfold fe51ValOfBytes; simp (disch := decide) only [res, readLE_write64_self', readLE_write64_ne]; exact hsrc_v
  exact ⟨hlen, hb, hv⟩

/-! ## `FieldElement51::sqrt_ratio_i` Helpers -/

private theorem fe51SqrtM1_limbsBounded : fe51LimbsBounded fe51SqrtM1Bytes (2 ^ 54) := by
  unfold fe51LimbsBounded
  rw [fe51SqrtM1Bytes_length, fe51SqrtM1_readLE_0, fe51SqrtM1_readLE_8,
      fe51SqrtM1_readLE_16, fe51SqrtM1_readLE_24, fe51SqrtM1_readLE_32]
  exact ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

private theorem bv64_zext32_mul19_toNat_16 (x : BitVec 64) (hx : x.toNat < 16) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 x) * 19#64).toNat = x.toNat * 19 := by bv_bits

private theorem bv64_mask51_add_mul19_toNat_55 (a b : BitVec 64) (hb : b.toNat < 2 ^ 55) :
    ((a &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (b >>> 51)) * 19#64).toNat =
      a.toNat % 2 ^ 51 + (b.toNat / 2 ^ 51) * 19 := by
  have hb8 : (b >>> 51).toNat < 16 := by rw [bv64_ushr51_toNat]; omega
  have h1 := bv64_and_mask51_toNat a; have h2 := bv64_zext32_mul19_toNat_16 (b >>> 51) hb8
  rw [bv64_ushr51_toNat] at h2; rw [bv64_add_toNat_of_lt _ _ (by omega), h1, h2]

private theorem bv64_sub_const_toNat (c x : BitVec 64) (hx : x.toNat ≤ c.toNat) :
    (c - x).toNat = c.toNat - x.toNat := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hx)

private theorem mod_16p_sub_eq_fpNeg (X : Nat) (hX : X < 16 * p25519) :
    (16 * p25519 - X) % p25519 = fpNeg (X % p25519) := by
  unfold VerifiedLibraries.Common.fpNeg
  have hdiv : X / p25519 ≤ 15 := by unfold p25519 at hX ⊢; omega
  have hmod : X % p25519 < p25519 := Nat.mod_lt X (by unfold p25519; decide)
  have hdecomp : 16 * p25519 - X = (p25519 - X % p25519) + (15 - X / p25519) * p25519 := by
    have hdm := Nat.div_add_mod X p25519
    have hmul : (15 - X / p25519) * p25519 = 15 * p25519 - p25519 * (X / p25519) := by rw [Nat.sub_mul, Nat.mul_comm (X / p25519) p25519]
    unfold p25519 at *; omega
  rw [hdecomp, Nat.add_mul_mod_self_right, Nat.mod_mod]

private theorem fe51_neg_nat (l0 l1 l2 l3 l4 d0 d1 d2 d3 d4 n0 n1 n2 n3 n4 : Nat)
    (hl0 : l0 < 2 ^ 54) (hl1 : l1 < 2 ^ 54) (hl2 : l2 < 2 ^ 54) (hl3 : l3 < 2 ^ 54) (hl4 : l4 < 2 ^ 54)
    (nd0 : d0 = 36028797018963664 - l0) (nd1 : d1 = 36028797018963952 - l1) (nd2 : d2 = 36028797018963952 - l2)
    (nd3 : d3 = 36028797018963952 - l3) (nd4 : d4 = 36028797018963952 - l4)
    (nn0 : n0 = d0 % 2 ^ 51 + (d4 / 2 ^ 51) * 19) (nn1 : n1 = d1 % 2 ^ 51 + d0 / 2 ^ 51)
    (nn2 : n2 = d2 % 2 ^ 51 + d1 / 2 ^ 51) (nn3 : n3 = d3 % 2 ^ 51 + d2 / 2 ^ 51) (nn4 : n4 = d4 % 2 ^ 51 + d3 / 2 ^ 51) :
    n0 < 2 ^ 52 ∧ n1 < 2 ^ 52 ∧ n2 < 2 ^ 52 ∧ n3 < 2 ^ 52 ∧ n4 < 2 ^ 52 ∧
    d0 + d1 * 2 ^ 51 + d2 * 2 ^ 102 + d3 * 2 ^ 153 + d4 * 2 ^ 204 =
      16 * p25519 - (l0 + l1 * 2 ^ 51 + l2 * 2 ^ 102 + l3 * 2 ^ 153 + l4 * 2 ^ 204) ∧
    l0 + l1 * 2 ^ 51 + l2 * 2 ^ 102 + l3 * 2 ^ 153 + l4 * 2 ^ 204 < 16 * p25519 := by unfold p25519; omega

private theorem fe51_neg_math (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0 : l0.toNat < 2 ^ 54) (hl1 : l1.toNat < 2 ^ 54) (hl2 : l2.toNat < 2 ^ 54) (hl3 : l3.toNat < 2 ^ 54) (hl4 : l4.toNat < 2 ^ 54)
    (d0 d1 d2 d3 d4 n0 n1 n2 n3 n4 : BitVec 64)
    (hd0 : d0 = 36028797018963664#64 - l0) (hd1 : d1 = 36028797018963952#64 - l1)
    (hd2 : d2 = 36028797018963952#64 - l2) (hd3 : d3 = 36028797018963952#64 - l3) (hd4 : d4 = 36028797018963952#64 - l4)
    (hn0 : n0 = (d0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (d4 >>> 51)) * 19#64)
    (hn1 : n1 = (d1 &&& 2251799813685247#64) + d0 >>> 51) (hn2 : n2 = (d2 &&& 2251799813685247#64) + d1 >>> 51)
    (hn3 : n3 = (d3 &&& 2251799813685247#64) + d2 >>> 51) (hn4 : n4 = (d4 &&& 2251799813685247#64) + d3 >>> 51) :
    n0.toNat < 2 ^ 52 ∧ n1.toNat < 2 ^ 52 ∧ n2.toNat < 2 ^ 52 ∧ n3.toNat < 2 ^ 52 ∧ n4.toNat < 2 ^ 52 ∧
    fe51Val n0 n1 n2 n3 n4 % p25519 = fpNeg (fe51Val l0 l1 l2 l3 l4 % p25519) := by
  have hle54 (x : Nat) (hx : x < 2 ^ 54) : x ≤ 36028797018963664 := Nat.le_of_lt (Nat.lt_trans hx (by decide))
  have hle54' (x : Nat) (hx : x < 2 ^ 54) : x ≤ 36028797018963952 := Nat.le_of_lt (Nat.lt_trans hx (by decide))
  have nd0 : d0.toNat = 36028797018963664 - l0.toNat := hd0 ▸ bv64_sub_const_toNat _ l0 (hle54 _ hl0)
  have nd1 : d1.toNat = 36028797018963952 - l1.toNat := hd1 ▸ bv64_sub_const_toNat _ l1 (hle54' _ hl1)
  have nd2 : d2.toNat = 36028797018963952 - l2.toNat := hd2 ▸ bv64_sub_const_toNat _ l2 (hle54' _ hl2)
  have nd3 : d3.toNat = 36028797018963952 - l3.toNat := hd3 ▸ bv64_sub_const_toNat _ l3 (hle54' _ hl3)
  have nd4 : d4.toNat = 36028797018963952 - l4.toNat := hd4 ▸ bv64_sub_const_toNat _ l4 (hle54' _ hl4)
  have hd4_lt : d4.toNat < 2 ^ 55 := by rw [nd4]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  have nn0 : n0.toNat = d0.toNat % 2 ^ 51 + (d4.toNat / 2 ^ 51) * 19 := hn0 ▸ bv64_mask51_add_mul19_toNat_55 d0 d4 hd4_lt
  have nn1 : n1.toNat = d1.toNat % 2 ^ 51 + d0.toNat / 2 ^ 51 := hn1 ▸ bv64_mask51_add_ushr51_toNat d1 d0
  have nn2 : n2.toNat = d2.toNat % 2 ^ 51 + d1.toNat / 2 ^ 51 := hn2 ▸ bv64_mask51_add_ushr51_toNat d2 d1
  have nn3 : n3.toNat = d3.toNat % 2 ^ 51 + d2.toNat / 2 ^ 51 := hn3 ▸ bv64_mask51_add_ushr51_toNat d3 d2
  have nn4 : n4.toNat = d4.toNat % 2 ^ 51 + d3.toNat / 2 ^ 51 := hn4 ▸ bv64_mask51_add_ushr51_toNat d4 d3
  have hcarry := fe51_carry1_nat d0.toNat d1.toNat d2.toNat d3.toNat d4.toNat n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat nn0 nn1 nn2 nn3 nn4
  obtain ⟨b0, b1, b2, b3, b4, hsum, hlt⟩ := fe51_neg_nat l0.toNat l1.toNat l2.toNat l3.toNat l4.toNat
    d0.toNat d1.toNat d2.toNat d3.toNat d4.toNat n0.toNat n1.toNat n2.toNat n3.toNat n4.toNat
    hl0 hl1 hl2 hl3 hl4 nd0 nd1 nd2 nd3 nd4 nn0 nn1 nn2 nn3 nn4
  have hmod : fe51Val n0 n1 n2 n3 n4 % p25519 = (16 * p25519 - fe51Val l0 l1 l2 l3 l4) % p25519 := by
    unfold fe51Val; rw [← hsum, hcarry, Nat.add_mul_mod_self_right]
  refine ⟨b0, b1, b2, b3, b4, ?_⟩; rw [hmod]; exact mod_16p_sub_eq_fpNeg _ hlt

private theorem sepWP_peel_memRegion (sp : BitVec 64) (off n rem : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (sp - BitVec.ofNat 64 off) off ∗ P := by sep_frame)
    (hoff : off = n + rem := by decide) (hb : off ≤ 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s ((memRegion (sp - BitVec.ofNat 64 off) n ∗ memRegion (sp - BitVec.ofNat 64 rem) rem) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have haddr : sp - BitVec.ofNat 64 off + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 rem := by rw [sub_ofNat64_add sp off n (by omega), show off - n = rem by omega]
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 off) n rem (hoff ▸ hb); rw [← hoff, haddr] at hsplit; rw [hf, hsplit]; exact hnext

private theorem sepWP_unpeel_memRegion (sp : BitVec 64) (off n rem : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp - BitVec.ofNat 64 off) n ∗ memRegion (sp - BitVec.ofNat 64 rem) rem) ∗ P := by sep_frame)
    (hoff : off = n + rem := by decide) (hb : off ≤ 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s (memRegion (sp - BitVec.ofNat 64 off) off ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have haddr : sp - BitVec.ofNat 64 off + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 rem := by rw [sub_ofNat64_add sp off n (by omega), show off - n = rem by omega]
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 off) n rem (hoff ▸ hb); rw [← hoff, haddr] at hsplit; rw [hf, ← hsplit]; exact hnext

private theorem sepWP_split_append_40 (base : BitVec 64) {b0 b1 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (base ↦ₛ (b0 ++ b1)) ∗ P := by sep_frame) (h0 : b0.length = 40 := by assumption)
    (hnext : SepWP prog target_pc s (((base ↦ₛ b0) ∗ ((base + 40#64) ↦ₛ b1)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hm : (base ↦ₛ (b0 ++ b1)) = (base ↦ₛ b0) ∗ ((base + 40#64) ↦ₛ b1) := by rw [pointsToBytes_append, h0]
  rw [hf, hm]; exact hnext

private theorem fe51_b52_props (w : List (BitVec 8)) (hb : fe51LimbsBounded w (2 ^ 52) := by assumption) :
    w.length = 40 ∧ fe51LimbsBounded w (2 ^ 54) ∧ fe51LimbsBounded w (2 ^ 52) := by
  rcases hb with ⟨hl, h0, h1, h2, h3, h4⟩
  exact ⟨hl, ⟨hl, by omega, by omega, by omega, by omega, by omega⟩, hl, h0, h1, h2, h3, h4⟩

private theorem sepWP_split_40_32_8 (base : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (base ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 40 := by assumption)
    (hnext : ∀ (b32 : List (BitVec 8)) (v8 : BitVec 64), b32.length = 32 →
      SepWP prog target_pc s (((base ↦ₛ b32) ∗ ((base + 32#64) ↦₆₄ v8)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hs : (base ↦ₛ bs) = (base ↦ₛ bs.take 32) ∗ ((base + 32#64) ↦₆₄ ByteSlice.readLE bs 32 8) := by
    rw [pointsToBytes_take_drop base 32 bs (by omega), show bs.drop 32 = (bs.drop 32).take 8 from (List.take_of_length_le (by simp [hbs])).symm,
        pointsToBytes_take8_eq_pointsTo64 _ bs 32 (by omega), ByteSlice.pack64_eq_readLE_8]
  rw [hf, hs]; exact hnext (bs.take 32) (ByteSlice.readLE bs 32 8) (by simp [hbs])

private theorem sepWP_open_bytes40_64 (base : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (base ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 40 := by assumption)
    (hnext : SepWP prog target_pc s (((base ↦₆₄ ByteSlice.readLE bs 0 8) ∗ ((base + 8#64) ↦₆₄ ByteSlice.readLE bs 8 8) ∗
      ((base + 16#64) ↦₆₄ ByteSlice.readLE bs 16 8) ∗ ((base + 24#64) ↦₆₄ ByteSlice.readLE bs 24 8) ∗
      ((base + 32#64) ↦₆₄ ByteSlice.readLE bs 32 8)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by rw [hf, pointsToBytes40_eq_cells base bs hbs]; exact hnext

private theorem sepWP_close_bytes40_64 (base : BitVec 64) (bs : List (BitVec 8))
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((base ↦₆₄ ByteSlice.readLE bs 0 8) ∗ ((base + 8#64) ↦₆₄ ByteSlice.readLE bs 8 8) ∗
      ((base + 16#64) ↦₆₄ ByteSlice.readLE bs 16 8) ∗ ((base + 24#64) ↦₆₄ ByteSlice.readLE bs 24 8) ∗
      ((base + 32#64) ↦₆₄ ByteSlice.readLE bs 32 8)) ∗ P) := by sep_frame) (hbs : bs.length = 40 := by assumption)
    (hnext : SepWP prog target_pc s ((base ↦ₛ bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by rw [hf, ← pointsToBytes40_eq_cells base bs hbs]; exact hnext

private theorem sepWP_open_bytes32_8_front (base : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbs : bs.length = 32 := by assumption)
    (hnext : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8,
      SepWP prog target_pc s
        (((base ↦₈ b0) ∗ ((base + 1#64) ↦₈ b1) ∗ ((base + 2#64) ↦₈ b2) ∗ ((base + 3#64) ↦₈ b3) ∗ ((base + 4#64) ↦₈ b4) ∗ ((base + 5#64) ↦₈ b5) ∗ ((base + 6#64) ↦₈ b6) ∗ ((base + 7#64) ↦₈ b7) ∗
          ((base + 8#64) ↦₈ b8) ∗ ((base + 9#64) ↦₈ b9) ∗ ((base + 10#64) ↦₈ b10) ∗ ((base + 11#64) ↦₈ b11) ∗ ((base + 12#64) ↦₈ b12) ∗ ((base + 13#64) ↦₈ b13) ∗ ((base + 14#64) ↦₈ b14) ∗ ((base + 15#64) ↦₈ b15) ∗
          ((base + 16#64) ↦₈ b16) ∗ ((base + 17#64) ↦₈ b17) ∗ ((base + 18#64) ↦₈ b18) ∗ ((base + 19#64) ↦₈ b19) ∗ ((base + 20#64) ↦₈ b20) ∗ ((base + 21#64) ↦₈ b21) ∗ ((base + 22#64) ↦₈ b22) ∗ ((base + 23#64) ↦₈ b23) ∗
          ((base + 24#64) ↦₈ b24) ∗ ((base + 25#64) ↦₈ b25) ∗ ((base + 26#64) ↦₈ b26) ∗ ((base + 27#64) ↦₈ b27) ∗ ((base + 28#64) ↦₈ b28) ∗ ((base + 29#64) ↦₈ b29) ∗ ((base + 30#64) ↦₈ b30) ∗ ((base + 31#64) ↦₈ b31)) ∗ P) post oom) :
    SepWP prog target_pc s ((base ↦ₛ bs) ∗ P) post oom := by
  rw [pointsToBytes32_eq_cells8 base bs hbs]; exact hnext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem sepWP_open_bytes32_8 (base : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (base ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 32 := by assumption)
    (hnext : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8,
      SepWP prog target_pc s
        (((base ↦₈ b0) ∗ ((base + 1#64) ↦₈ b1) ∗ ((base + 2#64) ↦₈ b2) ∗ ((base + 3#64) ↦₈ b3) ∗ ((base + 4#64) ↦₈ b4) ∗ ((base + 5#64) ↦₈ b5) ∗ ((base + 6#64) ↦₈ b6) ∗ ((base + 7#64) ↦₈ b7) ∗
          ((base + 8#64) ↦₈ b8) ∗ ((base + 9#64) ↦₈ b9) ∗ ((base + 10#64) ↦₈ b10) ∗ ((base + 11#64) ↦₈ b11) ∗ ((base + 12#64) ↦₈ b12) ∗ ((base + 13#64) ↦₈ b13) ∗ ((base + 14#64) ↦₈ b14) ∗ ((base + 15#64) ↦₈ b15) ∗
          ((base + 16#64) ↦₈ b16) ∗ ((base + 17#64) ↦₈ b17) ∗ ((base + 18#64) ↦₈ b18) ∗ ((base + 19#64) ↦₈ b19) ∗ ((base + 20#64) ↦₈ b20) ∗ ((base + 21#64) ↦₈ b21) ∗ ((base + 22#64) ↦₈ b22) ∗ ((base + 23#64) ↦₈ b23) ∗
          ((base + 24#64) ↦₈ b24) ∗ ((base + 25#64) ↦₈ b25) ∗ ((base + 26#64) ↦₈ b26) ∗ ((base + 27#64) ↦₈ b27) ∗ ((base + 28#64) ↦₈ b28) ∗ ((base + 29#64) ↦₈ b29) ∗ ((base + 30#64) ↦₈ b30) ∗ ((base + 31#64) ↦₈ b31)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by rw [hf]; exact sepWP_open_bytes32_8_front base hbs hnext

private theorem sepWP_focus2 (A B : SepProp)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (A ∗ B) ∗ P := by sep_frame) (hnext : SepWP prog target_pc s (A ∗ B ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by rw [hf, sepConj_assoc]; exact hnext

private theorem sepWP_open_bytes32_64 (base : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (base ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 32 := by assumption)
    (hnext : ∀ w0 w1 w2 w3 : BitVec 64, SepWP prog target_pc s
      (((base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by rw [hf, pointsToBytes32_eq_cells64 base bs hbs]; exact hnext _ _ _ _

private theorem sepWP_pack_fe51 (base : BitVec 64) (w0 w1 w2 w3 w4 : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) ∗ ((base + 32#64) ↦₆₄ w4)) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((base ↦ₛ packFe51Bytes w0 w1 w2 w3 w4) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by rw [hf, ← pointsToBytes_packFe51Bytes base w0 w1 w2 w3 w4]; exact hnext

private theorem sepWP_merge_32_8 (base : BitVec 64) {bs32 : List (BitVec 8)} {v8 : BitVec 64}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((base ↦ₛ bs32) ∗ ((base + 32#64) ↦₆₄ v8)) ∗ P := by sep_frame) (hbs : bs32.length = 32 := by assumption)
    (hnext : ∀ bs40 : List (BitVec 8), bs40.length = 40 → SepWP prog target_pc s ((base ↦ₛ bs40) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, pointsTo64_eq_pointsToBytes (base + 32#64) v8, ← show BitVec.ofNat 64 bs32.length = 32#64 by rw [hbs],
      ← pointsToBytes_append base bs32 (unpack64 v8)]
  exact hnext (bs32 ++ unpack64 v8) (by simp [hbs])

private theorem sepWP_head_region_sub (sp : BitVec 64) (off off' n m : Nat) {v : BitVec 64}
    {prog : Program} {tpc : BitVec 64} {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = (((sp - BitVec.ofNat 64 off) ↦₆₄ v) ∗ memRegion (sp - BitVec.ofNat 64 off') m) ∗ F := by sep_frame)
    (hoff : off = off' + 8 := by decide) (hnm : n = 8 + m := by decide) (hb : n ≤ 2 ^ 64 := by decide)
    (h : SepWP prog tpc s (memRegion (sp - BitVec.ofNat 64 off) n ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  have ha : sp - BitVec.ofNat 64 off + 8#64 = sp - BitVec.ofNat 64 off' := by
    change sp - BitVec.ofNat 64 off + BitVec.ofNat 64 8 = sp - BitVec.ofNat 64 off'
    rw [sub_ofNat64_add sp off 8 (by omega), show off - 8 = off' by omega]
  rw [← ha] at hP; exact SepWP.head_region (sp - BitVec.ofNat 64 off) n m hnm hb hP h

local syntax "close_cells_sub " term:max num num num : tactic
macro_rules
  | `(tactic| close_cells_sub $sp $off $n $k) => do
    let (off, n, k) := (off.getNat, n.getNat, k.getNat)
    if k == 0 then `(tactic| skip) else
    if n == 8 then
      let offLit := Lean.Syntax.mkNumLit (toString off)
      `(tactic| apply SepWP.last_region ($sp - BitVec.ofNat 64 $offLit))
    else
      let (offLit, off'Lit, nLit, n'Lit, k'Lit) := (Lean.Syntax.mkNumLit (toString off), Lean.Syntax.mkNumLit (toString (off - 8)),
        Lean.Syntax.mkNumLit (toString n), Lean.Syntax.mkNumLit (toString (n - 8)), Lean.Syntax.mkNumLit (toString (k - 1)))
      `(tactic| (close_cells_sub $sp $off'Lit $n'Lit $k'Lit; apply sepWP_head_region_sub $sp $offLit $off'Lit $nLit $n'Lit))

private theorem extract_ct_eq_ret {s : State} {b : BitVec 8}
    (h : BitVec.zeroExtend 8 (s.readReg64 (Reg.gpr 0#5)) = b := by assumption) :
    ∃ x0 : BitVec 64, s.readReg64 (Reg.gpr 0#5) = x0 ∧ BitVec.truncate 8 x0 = b := ⟨s.readReg64 (Reg.gpr 0#5), rfl, h⟩

private theorem truncate8_ze64_tr32 {x : BitVec 64} {b : BitVec 8} (h : BitVec.truncate 8 x = b) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 x)) = b := by
  rw [← h]; ext i hi; simp [BitVec.truncate, BitVec.zeroExtend]

private theorem truncate8_reg_of_ze64_tr32 {r x : BitVec 64} {b : BitVec 8}
    (hr : r = BitVec.zeroExtend 64 (BitVec.truncate 32 x) := by assumption)
    (hx : BitVec.truncate 8 x = b) :
    BitVec.truncate 8 r = b := by
  rw [hr]; exact truncate8_ze64_tr32 hx

private theorem fpNeg_mod' (x : Nat) : fpNeg x % p25519 = fpNeg x := Nat.mod_mod _ _

set_option maxHeartbeats 800000 in
private theorem sqrt_ratio_phaseB [DalekCliPlacement] (b sp u_ptr : BitVec 64)
    (w_12 r0_bs w_11 u_bs : List (BitVec 8)) (v_c4 : BitVec 32)
    {target_pc : BitVec 64} {s0 : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hb : DalekBase dalekCliPl03 b) (hbase : dalekCliPl03.base = b)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s0.mem)
    (hpc : s0.pc = b + 252#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp - 672#64) (h_sp_align : (sp &&& 15#64 == 0#64) = true)
    (hx29 : s0.readReg64 (Reg.gpr 29#5) = sp - 96#64) (hx21 : s0.readReg64 (Reg.gpr 21#5) = u_ptr)
    (hw12_b54 : fe51LimbsBounded w_12 (2 ^ 54)) (hr0_l : r0_bs.length = 40) (hw11_l : w_11.length = 40)
    (hu_b54 : fe51LimbsBounded u_bs (2 ^ 54))
    (hf : Full = (((sp - 264#64) ↦ₛ w_12) ∗ ((sp - 224#64) ↦ₛ r0_bs) ∗ ((sp - 184#64) ↦ₛ w_11) ∗
      (u_ptr ↦ₛ u_bs) ∗ ((fe51_sqrt_m1 dalekCliMpl) ↦ᵣ fe51SqrtM1Bytes) ∗ ((sp - 476#64) ↦₃₂ v_c4) ∗
      memRegion (sp - 672#64) 192 ∗ memRegion (sp - 672#64 - 224#64) 224) ∗ P := by sep_frame)
    (hnext : ∀ (sf : State) (ui_bs nu_fe51 : List (BitVec 8)) (x0_14 : BitVec 64),
      dalekCliMultiLib.CodeLoaded dalekCliMpl sf.mem →
      sf.pc = b + 1424#64 →
      sf.status = .Running → sf.sp = sp - 672#64 →
      sf.readReg64 (Reg.gpr 21#5) = 36028797018963952#64 → sf.readReg64 (Reg.gpr 22#5) = fe51_sqrt_m1 dalekCliMpl →
      sf.readReg64 (Reg.gpr 29#5) = sp - 96#64 → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      BitVec.truncate 8 (sf.readReg64 (Reg.gpr 19#5)) =
        (if natToLeBytes 32 (fe51ValOfBytes w_12 % p25519) == natToLeBytes 32 (fpNeg (fe51ValOfBytes u_bs % p25519)) then 1#8 else 0#8) →
      BitVec.truncate 8 x0_14 =
        (if natToLeBytes 32 (fe51ValOfBytes w_12 % p25519) == natToLeBytes 32 (fe51ValOfBytes u_bs % p25519) then 1#8 else 0#8) →
      fe51LimbsBounded ui_bs (2 ^ 52) →
      fe51ValOfBytes ui_bs % p25519 = (fpNeg (fe51ValOfBytes u_bs % p25519) * fe51ValOfBytes fe51SqrtM1Bytes) % p25519 →
      nu_fe51.length = 40 →
      SepWP (dalekCliPC03.rebase b (fun _ => none)) target_pc sf
        (memRegion (sp - 672#64 - 224#64) 224 ∗ ((sp - 184#64) ↦ₛ nu_fe51) ∗
          ((fe51_sqrt_m1 dalekCliMpl) ↦ᵣ fe51SqrtM1Bytes) ∗ ((sp - 224#64) ↦ₛ ui_bs) ∗
          ((sp - 264#64) ↦ₛ w_12) ∗ (u_ptr ↦ₛ u_bs) ∗ memRegion (sp - 672#64) 192 ∗
          ((sp - 476#64) ↦₃₂ BitVec.truncate 32 x0_14) ∗ P) post oom) :
    SepWP (dalekCliPC03.rebase b (fun _ => none)) target_pc s0 Full post oom := by
  rw [hf]
  have hsqrt_b54 : fe51LimbsBounded fe51SqrtM1Bytes (2 ^ 54) := fe51SqrtM1_limbsBounded
  obtain ⟨hw12_l, hcl0, hcl1, hcl2, hcl3, hcl4⟩ := hw12_b54
  rcases hu_b54 with ⟨hu_l, hul0, hul1, hul2, hul3, hul4⟩; have hu_b54 : fe51LimbsBounded u_bs (2 ^ 54) := ⟨hu_l, hul0, hul1, hul2, hul3, hul4⟩
  open_cells (sp - 672#64) 192 24; apply sepWP_split32_sub sp 648#64 644#64; apply sepWP_split32_sub sp 536#64 532#64
  apply sepWP_split_40_32_8 (sp - 224#64); intro r0_32 r0_v8 hr0_32; apply sepWP_open_bytes40_64 (sp - 264#64); apply sepWP_open_bytes32_8 (sp - 224#64)
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  generalize hcl0_eq : ByteSlice.readLE w_12 0 8 = cl0 at hcl0 ⊢; generalize hcl1_eq : ByteSlice.readLE w_12 8 8 = cl1 at hcl1 ⊢
  generalize hcl2_eq : ByteSlice.readLE w_12 16 8 = cl2 at hcl2 ⊢; generalize hcl3_eq : ByteSlice.readLE w_12 24 8 = cl3 at hcl3 ⊢
  generalize hcl4_eq : ByteSlice.readLE w_12 32 8 = cl4 at hcl4 ⊢
  wp_cut_codeLoaded; wp_sym_steps 24
  generalize hch0 : (cl0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (cl4 >>> 51)) * 19#64 = ch0
  generalize hch1 : (cl1 &&& 2251799813685247#64) + cl0 >>> 51 = ch1; generalize hch2 : (cl2 &&& 2251799813685247#64) + cl1 >>> 51 = ch2
  generalize hch3 : (cl3 &&& 2251799813685247#64) + cl2 >>> 51 = ch3; generalize hch4 : (cl4 &&& 2251799813685247#64) + cl3 >>> 51 = ch4
  generalize hcq : (ch4 + (ch3 + (ch2 + (ch1 + (ch0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = cq
  generalize hcu0 : ch0 + BitVec.setWidth 64 (BitVec.setWidth 32 cq) * 19#64 = cu0; wp_sym_steps 24
  generalize hcu1 : ch1 + cu0 >>> 51 = cu1; generalize hcu2 : ch2 + cu1 >>> 51 = cu2
  generalize hcu3 : ch3 + cu2 >>> 51 = cu3; generalize hcu4 : ch4 + cu3 >>> 51 = cu4; wp_sym_steps 64
  have hc_bytes : packCanonical51Bytes cu0 cu1 cu2 cu3 cu4 = natToLeBytes 32 (fe51ValOfBytes w_12 % p25519) := by
    rw [fe51ValOfBytes, hcl0_eq, hcl1_eq, hcl2_eq, hcl3_eq, hcl4_eq]
    exact fe51_to_bytes_math cl0 cl1 cl2 cl3 cl4 hcl0 hcl1 hcl2 hcl3 hcl4 ch0 ch1 ch2 ch3 ch4 cq cu0 cu1 cu2 cu3 cu4
      hch0.symm hch1.symm hch2.symm hch3.symm hch4.symm hcq.symm hcu0.symm hcu1.symm hcu2.symm hcu3.symm hcu4.symm
  generalize hc_bs_eq : natToLeBytes 32 (fe51ValOfBytes w_12 % p25519) = c_bs at hc_bytes; have h_c32 : c_bs.length = 32 := by rw [← hc_bs_eq]; rfl
  wp_conv_pre => rw [← pointsToBytes_list32 (sp - 224#64)]; change ((sp - 224#64) ↦ₛ packCanonical51Bytes cu0 cu1 cu2 cu3 cu4) ∗ _; rw [hc_bytes]
  apply sepWP_split_40_32_8 (sp - 184#64); intro w11_32 w11_v8 hw11_32; apply sepWP_callee_shrink (sp - 672#64) 224 96 128
  wp_steps; close_cut_codeLoaded; wp_dalek_call_fast fe51_to_bytes_ok; rw [hsp, hx29, hx21] at *; clean_prev_sf2; norm_sf 96; clear hu_b54
  generalize hu_bs_eq : natToLeBytes 32 (fe51ValOfBytes u_bs % p25519) = u_bytes; have h_u32 : u_bytes.length = 32 := by rw [← hu_bs_eq]; rfl
  apply sepWP_callee_grow (sp - 672#64) 224 96 128; apply sepWP_callee_shrink (sp - 672#64) 224 64 160
  wp_steps; wp_dalek_call_fast slice32_ct_eq_ok; clean_prev_sf2; norm_sf 64; obtain ⟨x0_14, hx0_14_eq, hx0_14⟩ := extract_ct_eq_ret; apply sepWP_open_bytes40_64 u_ptr
  generalize hul0_eq : ByteSlice.readLE u_bs 0 8 = ul0 at hul0 ⊢; generalize hul1_eq : ByteSlice.readLE u_bs 8 8 = ul1 at hul1 ⊢
  generalize hul2_eq : ByteSlice.readLE u_bs 16 8 = ul2 at hul2 ⊢; generalize hul3_eq : ByteSlice.readLE u_bs 24 8 = ul3 at hul3 ⊢
  generalize hul4_eq : ByteSlice.readLE u_bs 32 8 = ul4 at hul4 ⊢; apply sepWP_focus2 ((sp - 184#64) ↦ₛ u_bytes) ((sp - 224#64) ↦ₛ c_bs)
  apply sepWP_open_bytes32_8_front (sp - 184#64); intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  wp_conv_pre => rw [sepConj_left_comm]
  apply sepWP_open_bytes32_8_front (sp - 224#64); intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  wp_cut_codeLoaded; wp_sym_steps 45
  generalize hnl0 : ((36028797018963664#64 - ul0) &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 ((36028797018963952#64 - ul4) >>> 51)) * 19#64 = nl0
  generalize hnl1 : ((36028797018963952#64 - ul1) &&& 2251799813685247#64) + (36028797018963664#64 - ul0) >>> 51 = nl1
  generalize hnl2 : ((36028797018963952#64 - ul2) &&& 2251799813685247#64) + (36028797018963952#64 - ul1) >>> 51 = nl2
  generalize hnl3 : ((36028797018963952#64 - ul3) &&& 2251799813685247#64) + (36028797018963952#64 - ul2) >>> 51 = nl3
  generalize hnl4 : ((36028797018963952#64 - ul4) &&& 2251799813685247#64) + (36028797018963952#64 - ul3) >>> 51 = nl4; wp_sym_steps 45
  generalize hnh0 : (nl0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (nl4 >>> 51)) * 19#64 = nh0
  generalize hnh1 : (nl1 &&& 2251799813685247#64) + nl0 >>> 51 = nh1; generalize hnh2 : (nl2 &&& 2251799813685247#64) + nl1 >>> 51 = nh2
  generalize hnh3 : (nl3 &&& 2251799813685247#64) + nl2 >>> 51 = nh3; generalize hnh4 : (nl4 &&& 2251799813685247#64) + nl3 >>> 51 = nh4
  generalize hnq : (nh4 + (nh3 + (nh2 + (nh1 + (nh0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = nq
  generalize hnu0 : nh0 + BitVec.setWidth 64 (BitVec.setWidth 32 nq) * 19#64 = nu0; wp_sym_steps 27
  generalize hnu1 : nh1 + nu0 >>> 51 = nu1; generalize hnu2 : nh2 + nu1 >>> 51 = nu2
  generalize hnu3 : nh3 + nu2 >>> 51 = nu3; generalize hnu4 : nh4 + nu3 >>> 51 = nu4; wp_sym_steps 49
  have ⟨hnl0_b, hnl1_b, hnl2_b, hnl3_b, hnl4_b, hneg_val⟩ :=
    fe51_neg_math ul0 ul1 ul2 ul3 ul4 hul0 hul1 hul2 hul3 hul4 _ _ _ _ _ nl0 nl1 nl2 nl3 nl4 rfl rfl rfl rfl rfl hnl0.symm hnl1.symm hnl2.symm hnl3.symm hnl4.symm
  have hnu_bytes : packCanonical51Bytes nu0 nu1 nu2 nu3 nu4 = natToLeBytes 32 (fpNeg (fe51ValOfBytes u_bs % p25519)) := by
    rw [fe51ValOfBytes, hul0_eq, hul1_eq, hul2_eq, hul3_eq, hul4_eq, ← hneg_val]
    exact fe51_to_bytes_math nl0 nl1 nl2 nl3 nl4 (by omega) (by omega) (by omega) (by omega) (by omega)
      nh0 nh1 nh2 nh3 nh4 nq nu0 nu1 nu2 nu3 nu4 hnh0.symm hnh1.symm hnh2.symm hnh3.symm hnh4.symm hnq.symm hnu0.symm hnu1.symm hnu2.symm hnu3.symm hnu4.symm
  generalize hnu_bs_eq : natToLeBytes 32 (fpNeg (fe51ValOfBytes u_bs % p25519)) = nu_bytes at hnu_bytes; have h_nu32 : nu_bytes.length = 32 := by rw [← hnu_bs_eq]; rfl
  wp_conv_pre =>
    rw [← pointsToBytes_list32 (sp - 224#64), ← pointsToBytes_list32 (sp - 184#64)]
    change ((sp - 224#64) ↦ₛ packCanonical51Bytes cu0 cu1 cu2 cu3 cu4) ∗ ((sp - 184#64) ↦ₛ packCanonical51Bytes nu0 nu1 nu2 nu3 nu4) ∗ _; rw [hc_bytes, hnu_bytes]
  apply sepWP_combine32_sub sp 648#64 644#64; apply sepWP_combine32_sub sp 536#64 532#64; close_cells_sub sp 672 192 24
  rw [← hul0_eq, ← hul1_eq, ← hul2_eq, ← hul3_eq, ← hul4_eq]; apply sepWP_close_bytes40_64 u_ptr u_bs
  rw [← hcl0_eq, ← hcl1_eq, ← hcl2_eq, ← hcl3_eq, ← hcl4_eq]; apply sepWP_close_bytes40_64 (sp - 264#64) w_12
  wp_steps; close_cut_codeLoaded; wp_dalek_call_fast slice32_ct_eq_ok; clean_prev_sf2; norm_sf 64; obtain ⟨x0_15, hx0_15_eq, hx0_15⟩ := extract_ct_eq_ret
  apply sepWP_open_bytes32_64 (sp - 184#64); intro _ _ _ _
  wp_cut_codeLoaded; wp_steps; apply sepWP_pack_fe51 (sp - 184#64) nl0 nl1 nl2 nl3 nl4
  apply sepWP_merge_32_8 (sp - 224#64); intro c40_bs hc40_l; apply sepWP_callee_grow (sp - 672#64) 224 64 160
  have hnl_b54 : fe51LimbsBounded (packFe51Bytes nl0 nl1 nl2 nl3 nl4) (2 ^ 54) :=
    fe51LimbsBounded_packFe51Bytes nl0 nl1 nl2 nl3 nl4 (2 ^ 54) (by omega) (by omega) (by omega) (by omega) (by omega)
  unpack_fe51 hnl_b54; unpack_fe51 hsqrt_b54; close_cut_codeLoaded; wp_dalek_call_fast fe51_mul_ro_right_ok; clean_prev_sf2; norm_sf 224; rw [← hc_bs_eq, ← hu_bs_eq, ← hnu_bs_eq] at *
  have hui_val : fe51ValOfBytes w % p25519 = (fpNeg (fe51ValOfBytes u_bs % p25519) * fe51ValOfBytes fe51SqrtM1Bytes) % p25519 := by
    rw [hpost, Nat.mul_mod, fe51ValOfBytes_packFe51Bytes, hneg_val, ← fpNeg_mod', ← Nat.mul_mod, ← hul0_eq, ← hul1_eq, ← hul2_eq, ← hul3_eq, ← hul4_eq]; rfl
  exact hnext _ w (packFe51Bytes nl0 nl1 nl2 nl3 nl4) x0_14 (by assumption) (by assumption) (by assumption) (by assumption)
    (by assumption) (by assumption) (by assumption) (by assumption)
    (by exact truncate8_reg_of_ze64_tr32 (hx := hx0_15)) hx0_14
    (by assumption) hui_val (by simp [packFe51Bytes])

set_option maxHeartbeats 800000 in
private theorem sqrt_ratio_phaseC [DalekCliPlacement] (b sp : BitVec 64)
    (w_10 w_4 w_9 w_12 ui_bs nu_fe51 : List (BitVec 8))
    {target_pc : BitVec 64} {s0 : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (_hb : DalekBase dalekCliPl03 b) (hbase : dalekCliPl03.base = b)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s0.mem)
    (hpc : s0.pc = b + 1424#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp - 672#64) (h_sp_align : (sp &&& 15#64 == 0#64) = true)
    (hx21 : s0.readReg64 (Reg.gpr 21#5) = 36028797018963952#64) (hx22 : s0.readReg64 (Reg.gpr 22#5) = fe51_sqrt_m1 dalekCliMpl)
    (hx29 : s0.readReg64 (Reg.gpr 29#5) = sp - 96#64)
    (hw10_b54 : fe51LimbsBounded w_10 (2 ^ 54)) (hw4_l : w_4.length = 40) (hw9_l : w_9.length = 40)
    (hw12_b54 : fe51LimbsBounded w_12 (2 ^ 54)) (hui_b52 : fe51LimbsBounded ui_bs (2 ^ 52)) (hnu_l : nu_fe51.length = 40)
    (hf : Full = (((sp - 384#64) ↦ₛ w_10) ∗ ((sp - 344#64) ↦ₛ w_4) ∗ ((sp - 304#64) ↦ₛ w_9) ∗
      ((sp - 264#64) ↦ₛ w_12) ∗ ((sp - 224#64) ↦ₛ ui_bs) ∗ ((sp - 184#64) ↦ₛ nu_fe51) ∗
      ((fe51_sqrt_m1 dalekCliMpl) ↦ᵣ fe51SqrtM1Bytes) ∗ memRegion (sp - 672#64 - 224#64) 224) ∗ P := by sep_frame)
    (hnext : ∀ (sf : State) (r_prime c344_bs ui304_bs : List (BitVec 8)),
      dalekCliMultiLib.CodeLoaded dalekCliMpl sf.mem →
      sf.pc = b + 2204#64 →
      sf.status = .Running → sf.sp = sp - 672#64 →
      sf.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5) → sf.readReg64 (Reg.gpr 21#5) = 36028797018963952#64 →
      BitVec.truncate 8 (sf.readReg64 (Reg.gpr 23#5)) =
        (if natToLeBytes 32 (fe51ValOfBytes w_12 % p25519) == natToLeBytes 32 (fe51ValOfBytes ui_bs % p25519) then 1#8 else 0#8) →
      sf.readReg64 (Reg.gpr 26#5) = 19#64 → sf.readReg64 (Reg.gpr 29#5) = sp - 96#64 → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      fe51LimbsBounded r_prime (2 ^ 52) →
      fe51ValOfBytes r_prime % p25519 = (fe51ValOfBytes fe51SqrtM1Bytes * fe51ValOfBytes w_10) % p25519 →
      c344_bs.length = 40 → ui304_bs.length = 40 →
      SepWP (dalekCliPC03.rebase b (fun _ => none)) target_pc sf
        (memRegion (sp - 672#64 - 224#64) 224 ∗ ((fe51_sqrt_m1 dalekCliMpl) ↦ᵣ fe51SqrtM1Bytes) ∗
          ((sp - 384#64) ↦ₛ w_10) ∗ ((sp - 184#64) ↦ₛ r_prime) ∗ ((sp - 304#64) ↦ₛ ui304_bs) ∗
          ((sp - 344#64) ↦ₛ c344_bs) ∗ ((sp - 264#64) ↦ₛ w_12) ∗ ((sp - 224#64) ↦ₛ ui_bs) ∗ P) post oom) :
    SepWP (dalekCliPC03.rebase b (fun _ => none)) target_pc s0 Full post oom := by
  rw [hf]
  have hsqrt_b54 : fe51LimbsBounded fe51SqrtM1Bytes (2 ^ 54) := fe51SqrtM1_limbsBounded
  obtain ⟨hw12_l, hcl0, hcl1, hcl2, hcl3, hcl4⟩ := hw12_b54; obtain ⟨hui_l, hil0, hil1, hil2, hil3, hil4⟩ := hui_b52
  apply sepWP_split_40_32_8 (sp - 344#64); intro w4_32 w4_v8 hw4_32; apply sepWP_split_40_32_8 (sp - 304#64); intro w9_32 w9_v8 hw9_32
  apply sepWP_open_bytes40_64 (sp - 264#64); apply sepWP_open_bytes40_64 (sp - 224#64); apply sepWP_focus2 ((sp - 304#64) ↦ₛ w9_32) ((sp - 344#64) ↦ₛ w4_32)
  apply sepWP_open_bytes32_8_front (sp - 304#64); intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  wp_conv_pre => rw [sepConj_left_comm]
  apply sepWP_open_bytes32_8_front (sp - 344#64); intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  generalize hcl0_eq : ByteSlice.readLE w_12 0 8 = cl0 at hcl0 ⊢; generalize hcl1_eq : ByteSlice.readLE w_12 8 8 = cl1 at hcl1 ⊢
  generalize hcl2_eq : ByteSlice.readLE w_12 16 8 = cl2 at hcl2 ⊢; generalize hcl3_eq : ByteSlice.readLE w_12 24 8 = cl3 at hcl3 ⊢
  generalize hcl4_eq : ByteSlice.readLE w_12 32 8 = cl4 at hcl4 ⊢; generalize hil0_eq : ByteSlice.readLE ui_bs 0 8 = il0 at hil0 ⊢
  generalize hil1_eq : ByteSlice.readLE ui_bs 8 8 = il1 at hil1 ⊢; generalize hil2_eq : ByteSlice.readLE ui_bs 16 8 = il2 at hil2 ⊢
  generalize hil3_eq : ByteSlice.readLE ui_bs 24 8 = il3 at hil3 ⊢; generalize hil4_eq : ByteSlice.readLE ui_bs 32 8 = il4 at hil4 ⊢
  wp_cut_codeLoaded; wp_sym_steps 24
  generalize hch0 : (cl0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (cl4 >>> 51)) * 19#64 = ch0
  generalize hch1 : (cl1 &&& 2251799813685247#64) + cl0 >>> 51 = ch1; generalize hch2 : (cl2 &&& 2251799813685247#64) + cl1 >>> 51 = ch2
  generalize hch3 : (cl3 &&& 2251799813685247#64) + cl2 >>> 51 = ch3; generalize hch4 : (cl4 &&& 2251799813685247#64) + cl3 >>> 51 = ch4
  generalize hcq : (ch4 + (ch3 + (ch2 + (ch1 + (ch0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = cq
  generalize hcu0 : ch0 + BitVec.setWidth 64 (BitVec.setWidth 32 cq) * 19#64 = cu0; wp_sym_steps 15
  generalize hcu1 : ch1 + cu0 >>> 51 = cu1; generalize hcu2 : ch2 + cu1 >>> 51 = cu2; wp_sym_steps 23
  generalize hih0 : (il0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (il4 >>> 51)) * 19#64 = ih0
  generalize hih1 : (il1 &&& 2251799813685247#64) + il0 >>> 51 = ih1; generalize hcu3 : ch3 + cu2 >>> 51 = cu3; wp_sym_steps 30
  generalize hih2 : (il2 &&& 2251799813685247#64) + il1 >>> 51 = ih2; generalize hih3 : (il3 &&& 2251799813685247#64) + il2 >>> 51 = ih3
  generalize hcu4 : ch4 + cu3 >>> 51 = cu4; wp_sym_steps 18; generalize hih4 : (il4 &&& 2251799813685247#64) + il3 >>> 51 = ih4
  generalize hiq : (ih4 + (ih3 + (ih2 + (ih1 + (ih0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = iq
  generalize hiu0 : ih0 + BitVec.setWidth 64 (BitVec.setWidth 32 iq) * 19#64 = iu0; wp_sym_steps 35
  generalize hiu1 : ih1 + iu0 >>> 51 = iu1; generalize hiu2 : ih2 + iu1 >>> 51 = iu2
  generalize hiu3 : ih3 + iu2 >>> 51 = iu3; generalize hiu4 : ih4 + iu3 >>> 51 = iu4; wp_sym_steps 44
  have hc_bytes : packCanonical51Bytes cu0 cu1 cu2 cu3 cu4 = natToLeBytes 32 (fe51ValOfBytes w_12 % p25519) := by
    rw [fe51ValOfBytes, hcl0_eq, hcl1_eq, hcl2_eq, hcl3_eq, hcl4_eq]
    exact fe51_to_bytes_math cl0 cl1 cl2 cl3 cl4 hcl0 hcl1 hcl2 hcl3 hcl4 ch0 ch1 ch2 ch3 ch4 cq cu0 cu1 cu2 cu3 cu4
      hch0.symm hch1.symm hch2.symm hch3.symm hch4.symm hcq.symm hcu0.symm hcu1.symm hcu2.symm hcu3.symm hcu4.symm
  have hui_bytes : packCanonical51Bytes iu0 iu1 iu2 iu3 iu4 = natToLeBytes 32 (fe51ValOfBytes ui_bs % p25519) := by
    rw [fe51ValOfBytes, hil0_eq, hil1_eq, hil2_eq, hil3_eq, hil4_eq]
    exact fe51_to_bytes_math il0 il1 il2 il3 il4 (by omega) (by omega) (by omega) (by omega) (by omega)
      ih0 ih1 ih2 ih3 ih4 iq iu0 iu1 iu2 iu3 iu4 hih0.symm hih1.symm hih2.symm hih3.symm hih4.symm hiq.symm hiu0.symm hiu1.symm hiu2.symm hiu3.symm hiu4.symm
  generalize hc_bs_eq : natToLeBytes 32 (fe51ValOfBytes w_12 % p25519) = c_bs at hc_bytes; have h_c32 : c_bs.length = 32 := by rw [← hc_bs_eq]; rfl
  generalize hui_bs_eq : natToLeBytes 32 (fe51ValOfBytes ui_bs % p25519) = ui_bytes at hui_bytes; have h_ui32 : ui_bytes.length = 32 := by rw [← hui_bs_eq]; rfl
  wp_conv_pre =>
    rw [← pointsToBytes_list32 (sp - 344#64), ← pointsToBytes_list32 (sp - 304#64)]
    change ((sp - 344#64) ↦ₛ packCanonical51Bytes cu0 cu1 cu2 cu3 cu4) ∗ ((sp - 304#64) ↦ₛ packCanonical51Bytes iu0 iu1 iu2 iu3 iu4) ∗ _; rw [hc_bytes, hui_bytes]
  rw [← hil0_eq, ← hil1_eq, ← hil2_eq, ← hil3_eq, ← hil4_eq]; apply sepWP_close_bytes40_64 (sp - 224#64) ui_bs
  rw [← hcl0_eq, ← hcl1_eq, ← hcl2_eq, ← hcl3_eq, ← hcl4_eq]; apply sepWP_close_bytes40_64 (sp - 264#64) w_12
  apply sepWP_callee_shrink (sp - 672#64) 224 64 160; wp_steps; close_cut_codeLoaded; wp_dalek_call_fast slice32_ct_eq_ok; rw [hsp, hx21, hx22, hx29] at *; clean_prev_sf2; norm_sf 64
  obtain ⟨x0_17, hx0_17_eq, hx0_17⟩ := extract_ct_eq_ret; wp_steps
  apply sepWP_merge_32_8 (sp - 344#64); intro c344_bs hc344_l; apply sepWP_merge_32_8 (sp - 304#64); intro ui304_bs hui304_l
  apply sepWP_callee_grow (sp - 672#64) 224 64 160; unpack_fe51 hsqrt_b54; unpack_fe51 hw10_b54; wp_dalek_call_fast fe51_mul_ro_left_ok; clean_prev_sf2; norm_sf 224
  rw [← hc_bs_eq, ← hui_bs_eq] at *
  exact hnext _ w c344_bs ui304_bs (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    (by exact truncate8_reg_of_ze64_tr32 (hx := hx0_17)) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) hc344_l hui304_l

private theorem bv64_ze8_ze64_tr32_and1 (x : BitVec 64) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 x &&& 1#32)) = if x.toNat % 2 == 1 then 1#8 else 0#8 := by
  have h1 : BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 x &&& 1#32)) = BitVec.truncate 8 (x &&& 1#64) := by bv_bits
  have h2 : (x &&& 1#64).toNat = x.toNat % 2 := by bv_bits
  rw [h1]; rcases (by omega : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1) with h0 | h1'
  · have hx : x &&& 1#64 = 0#64 := BitVec.eq_of_toNat_eq (by rw [h2, h0]; rfl); rw [hx, h0]; rfl
  · have hx : x &&& 1#64 = 1#64 := BitVec.eq_of_toNat_eq (by rw [h2, h1']; rfl); rw [hx, h1']; rfl

private theorem h0_add_q_mod2 (h0 q : BitVec 64) :
    (h0 + q).toNat % 2 = (h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64).toNat % 2 := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

private theorem fe51_is_negative_math (l0 l1 l2 l3 l4 : BitVec 64)
    (hl0 : l0.toNat < 2 ^ 54) (hl1 : l1.toNat < 2 ^ 54) (hl2 : l2.toNat < 2 ^ 54) (hl3 : l3.toNat < 2 ^ 54) (hl4 : l4.toNat < 2 ^ 54)
    (h0 h1 h2 h3 h4 q : BitVec 64)
    (hh0 : h0 = (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64)
    (hh1 : h1 = (l1 &&& 2251799813685247#64) + l0 >>> 51) (hh2 : h2 = (l2 &&& 2251799813685247#64) + l1 >>> 51)
    (hh3 : h3 = (l3 &&& 2251799813685247#64) + l2 >>> 51) (hh4 : h4 = (l4 &&& 2251799813685247#64) + l3 >>> 51)
    (hq : q = (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (h0 + q) &&& 1#32)) =
      if (fe51Val l0 l1 l2 l3 l4 % p25519) % 2 == 1 then 1#8 else 0#8 := by
  let u0 := h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64; let u1 := h1 + u0 >>> 51
  let u2 := h2 + u1 >>> 51; let u3 := h3 + u2 >>> 51; let u4 := h4 + u3 >>> 51
  have hval := fe51_to_bytes_canonical_val l0 l1 l2 l3 l4 hl0 hl1 hl2 hl3 hl4 h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4 hh0 hh1 hh2 hh3 hh4 hq rfl rfl rfl rfl rfl
  rw [bv64_ze8_ze64_tr32_and1, h0_add_q_mod2, hval, fe51_canonical_mod2]

private theorem truncate8_ze64_or32_ite_comm {a b : BitVec 64} {c1 c2 : Bool}
    (ha : BitVec.truncate 8 a = if c1 then 1#8 else 0#8) (hb : BitVec.truncate 8 b = if c2 then 1#8 else 0#8) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 a ||| BitVec.truncate 32 b)) = if c2 || c1 then 1#8 else 0#8 := by
  have h1 : BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 a ||| BitVec.truncate 32 b)) = BitVec.truncate 8 a ||| BitVec.truncate 8 b := by
    ext i hi; simp [BitVec.truncate, BitVec.zeroExtend]
  rw [h1, ha, hb]; cases c1 <;> cases c2 <;> rfl

private theorem ct_select_from_x0 (a b x0 : BitVec 64) (c : Bool) (hx0 : BitVec.truncate 8 x0 = if c then 1#8 else 0#8) :
    (b &&& -(x0 &&& 255#64)) ||| (a &&& ((x0 &&& 255#64) - 1#64)) = if c then b else a := by
  have h1 : x0 &&& 255#64 = BitVec.zeroExtend 64 (BitVec.truncate 8 x0) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
      show 255 % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]; omega
  rw [h1, hx0]; cases c
  · change (b &&& 0#64) ||| (a &&& BitVec.allOnes 64) = a; rw [BitVec.and_zero, BitVec.and_allOnes, BitVec.zero_or]
  · change (b &&& BitVec.allOnes 64) ||| (a &&& 0#64) = b; rw [BitVec.and_allOnes, BitVec.and_zero, BitVec.or_zero]

private theorem sepWP_split_48_1_7_40 (a : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {bs : List (BitVec 8)}
    (hf : Full = (a ↦ₛ bs) ∗ P := by sep_frame) (hlen : bs.length = 48 := by omega)
    (hnext : ∀ (b0 : BitVec 8) (pad_bs out_40 : List (BitVec 8)), pad_bs.length = 7 → out_40.length = 40 →
      SepWP prog target_pc s (((a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ pad_bs) ∗ ((a + 8#64) ↦ₛ out_40)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have h8 : (bs.take 8).length = 8 := by simp [hlen]
  match hcons : bs.take 8 with
  | [] => simp [hcons] at h8
  | b0 :: pad_bs =>
    have hpad : pad_bs.length = 7 := by rw [hcons] at h8; simpa using h8
    have h40 : (bs.drop 8).length = 40 := by simp [hlen]
    have heq := (congrArg (a ↦ₛ ·) (List.take_append_drop 8 bs).symm).trans (pointsToBytes_append a (bs.take 8) (bs.drop 8))
    rw [h8, hcons, pointsToBytes_cons, sepConj_assoc] at heq; rw [hf, heq]; exact hnext b0 pad_bs (bs.drop 8) hpad h40

private theorem sepWP_merge_1_7_40 (a : BitVec 64) (b0 : BitVec 8) (pad_bs r_bs : List (BitVec 8))
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpad : pad_bs.length = 7) (hf : Full = ((a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ pad_bs) ∗ ((a + 8#64) ↦ₛ r_bs)) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((a ↦ₛ (b0 :: pad_bs ++ r_bs)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hlen : (b0 :: pad_bs).length = 8 := by simp [hpad]
  have heq : (a ↦ₛ ((b0 :: pad_bs) ++ r_bs)) = (a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ pad_bs) ∗ ((a + 8#64) ↦ₛ r_bs) := by
    rw [pointsToBytes_append, hlen, pointsToBytes_cons, sepConj_assoc]
  rw [hf, ← heq]; exact hnext

private theorem ite_limb_lt {c : Bool} {a b : BitVec 64} {n : Nat}
    (ha : a.toNat < n) (hb : b.toNat < n) (s : BitVec 64) (hs : (if c then b else a) = s) : s.toNat < n := by
  subst hs; cases c <;> assumption

private theorem fe51_select_val (c : Bool) (a b : List (BitVec 8))
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 s0 s1 s2 s3 s4 : BitVec 64)
    (ha0 : ByteSlice.readLE a 0 8 = a0) (ha1 : ByteSlice.readLE a 8 8 = a1) (ha2 : ByteSlice.readLE a 16 8 = a2)
    (ha3 : ByteSlice.readLE a 24 8 = a3) (ha4 : ByteSlice.readLE a 32 8 = a4)
    (hb0 : ByteSlice.readLE b 0 8 = b0) (hb1 : ByteSlice.readLE b 8 8 = b1) (hb2 : ByteSlice.readLE b 16 8 = b2)
    (hb3 : ByteSlice.readLE b 24 8 = b3) (hb4 : ByteSlice.readLE b 32 8 = b4)
    (hs0 : (if c then b0 else a0) = s0) (hs1 : (if c then b1 else a1) = s1) (hs2 : (if c then b2 else a2) = s2)
    (hs3 : (if c then b3 else a3) = s3) (hs4 : (if c then b4 else a4) = s4) :
    fe51Val s0 s1 s2 s3 s4 % p25519 = if c then fe51ValOfBytes b % p25519 else fe51ValOfBytes a % p25519 := by
  cases c <;> {
    simp only [Bool.false_eq_true, ↓reduceIte] at hs0 hs1 hs2 hs3 hs4 ⊢
    subst hs0 hs1 hs2 hs3 hs4 ha0 ha1 ha2 ha3 ha4 hb0 hb1 hb2 hb3 hb4; rfl
  }

private theorem fe51_select_neg_val (is_neg : Bool) (r1_val : Nat)
    (s0 s1 s2 s3 s4 sn0 sn1 sn2 sn3 sn4 rf0 rf1 rf2 rf3 rf4 : BitVec 64)
    (hs_val : fe51Val s0 s1 s2 s3 s4 % p25519 = r1_val) (his_neg : ((fe51Val s0 s1 s2 s3 s4 % p25519) % 2 == 1) = is_neg)
    (hsn_val : fe51Val sn0 sn1 sn2 sn3 sn4 % p25519 = fpNeg (fe51Val s0 s1 s2 s3 s4 % p25519))
    (hrf0 : (if is_neg then sn0 else s0) = rf0) (hrf1 : (if is_neg then sn1 else s1) = rf1)
    (hrf2 : (if is_neg then sn2 else s2) = rf2) (hrf3 : (if is_neg then sn3 else s3) = rf3) (hrf4 : (if is_neg then sn4 else s4) = rf4) :
    fe51ValOfBytes (packFe51Bytes rf0 rf1 rf2 rf3 rf4) % p25519 = if r1_val % 2 == 1 then fpNeg r1_val else r1_val := by
  rw [hs_val] at his_neg hsn_val; rw [fe51ValOfBytes_packFe51Bytes, his_neg]
  cases is_neg <;> {
    simp only [Bool.false_eq_true, ↓reduceIte] at hrf0 hrf1 hrf2 hrf3 hrf4 ⊢
    subst hrf0 hrf1 hrf2 hrf3 hrf4; assumption
  }

set_option maxHeartbeats 800000 in
private theorem sqrt_ratio_phaseD [DalekCliPlacement] (b sp : BitVec 64)
    (w_10 r_prime : List (BitVec 8)) (x0_14 : BitVec 64) (correctSign flippedSign flippedSignI : Bool)
    {target_pc : BitVec 64} {s0 : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (_hb : DalekBase dalekCliPl03 b) (hbase : dalekCliPl03.base = b)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s0.mem)
    (hpc : s0.pc = b + 2204#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp - 672#64) (h_sp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19 : BitVec.truncate 8 (s0.readReg64 (Reg.gpr 19#5)) = if flippedSign then 1#8 else 0#8)
    (hx21 : s0.readReg64 (Reg.gpr 21#5) = 36028797018963952#64)
    (hx23 : BitVec.truncate 8 (s0.readReg64 (Reg.gpr 23#5)) = if flippedSignI then 1#8 else 0#8)
    (hx26 : s0.readReg64 (Reg.gpr 26#5) = 19#64) (hx29 : s0.readReg64 (Reg.gpr 29#5) = sp - 96#64)
    (hx0_14 : BitVec.truncate 8 x0_14 = if correctSign then 1#8 else 0#8)
    (hw10_b52 : fe51LimbsBounded w_10 (2 ^ 52)) (hrp_b52 : fe51LimbsBounded r_prime (2 ^ 52))
    (hf : Full = (((sp - 384#64) ↦ₛ w_10) ∗ ((sp - 184#64) ↦ₛ r_prime) ∗
      ((sp - 476#64) ↦₃₂ BitVec.truncate 32 x0_14) ∗ memRegion (sp - 672#64 - 16#64) 16) ∗ P := by sep_frame)
    (hnext : ∀ (sf : State) (r_final : List (BitVec 8)),
      let r1_val := if flippedSign || flippedSignI then fe51ValOfBytes r_prime % p25519 else fe51ValOfBytes w_10 % p25519
      sf.pc = b + 2552#64 →
      sf.status = .Running → sf.sp = sp - 672#64 → sf.readReg64 (Reg.gpr 29#5) = sp - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      BitVec.truncate 8 (sf.readReg64 (Reg.gpr 0#5)) = (if correctSign || flippedSign then 1#8 else 0#8) →
      fe51LimbsBounded r_final (2 ^ 52) →
      fe51ValOfBytes r_final % p25519 = (if r1_val % 2 == 1 then fpNeg r1_val else r1_val) →
      SepWP (dalekCliPC03.rebase b (fun _ => none)) target_pc sf
        (memRegion (sp - 672#64 - 16#64) 16 ∗ ((sp - 184#64) ↦ₛ r_prime) ∗ ((sp - 384#64) ↦ₛ r_final) ∗
          ((sp - 476#64) ↦₃₂ BitVec.truncate 32 x0_14) ∗ P) post oom) :
    SepWP (dalekCliPC03.rebase b (fun _ => none)) target_pc s0 Full post oom := by
  rw [hf]
  obtain ⟨hw10_l, hr0_0, hr0_1, hr0_2, hr0_3, hr0_4⟩ := hw10_b52
  obtain ⟨hrp_l, hrp_0, hrp_1, hrp_2, hrp_3, hrp_4⟩ := hrp_b52
  wp_steps; wp_dalek_call_fast black_box_u8_ok; rw [hsp, hx21, hx26, hx29] at *; clean_prev_sf2; norm_sf 16
  obtain ⟨x0_19, hx0_19_eq, hx0_19⟩ := extract_ct_eq_ret
  have hx0_19_ite : BitVec.truncate 8 x0_19 = if flippedSign || flippedSignI then 1#8 else 0#8 :=
    hx0_19.trans (truncate8_ze64_or32_ite_comm hx23 hx19)
  apply sepWP_open_bytes40_64 (sp - 384#64); apply sepWP_open_bytes40_64 (sp - 184#64)
  generalize hr0_0_eq : ByteSlice.readLE w_10 0 8 = r0_0 at hr0_0 ⊢; generalize hr0_1_eq : ByteSlice.readLE w_10 8 8 = r0_1 at hr0_1 ⊢
  generalize hr0_2_eq : ByteSlice.readLE w_10 16 8 = r0_2 at hr0_2 ⊢; generalize hr0_3_eq : ByteSlice.readLE w_10 24 8 = r0_3 at hr0_3 ⊢
  generalize hr0_4_eq : ByteSlice.readLE w_10 32 8 = r0_4 at hr0_4 ⊢; generalize hrp_0_eq : ByteSlice.readLE r_prime 0 8 = rp_0 at hrp_0 ⊢
  generalize hrp_1_eq : ByteSlice.readLE r_prime 8 8 = rp_1 at hrp_1 ⊢; generalize hrp_2_eq : ByteSlice.readLE r_prime 16 8 = rp_2 at hrp_2 ⊢
  generalize hrp_3_eq : ByteSlice.readLE r_prime 24 8 = rp_3 at hrp_3 ⊢; generalize hrp_4_eq : ByteSlice.readLE r_prime 32 8 = rp_4 at hrp_4 ⊢
  wp_sym_steps 11; generalize hs1_4 : (rp_4 &&& -(x0_19 &&& 255#64)) ||| (r0_4 &&& ((x0_19 &&& 255#64) - 1#64)) = s1_4
  wp_sym_steps 3; generalize hs1_0 : (rp_0 &&& -(x0_19 &&& 255#64)) ||| (r0_0 &&& ((x0_19 &&& 255#64) - 1#64)) = s1_0
  wp_sym_steps 4; generalize hs1_1 : (rp_1 &&& -(x0_19 &&& 255#64)) ||| (r0_1 &&& ((x0_19 &&& 255#64) - 1#64)) = s1_1
  wp_sym_steps 7; generalize hs1_2 : (rp_2 &&& -(x0_19 &&& 255#64)) ||| (r0_2 &&& ((x0_19 &&& 255#64) - 1#64)) = s1_2
  generalize hsh0 : (s1_0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (s1_4 >>> 51)) * 19#64 = sh0
  wp_sym_steps 6; generalize hs1_3 : (rp_3 &&& -(x0_19 &&& 255#64)) ||| (r0_3 &&& ((x0_19 &&& 255#64) - 1#64)) = s1_3
  generalize hsh1 : (s1_1 &&& 2251799813685247#64) + s1_0 >>> 51 = sh1; wp_sym_steps 11
  generalize hsh2 : (s1_2 &&& 2251799813685247#64) + s1_1 >>> 51 = sh2
  generalize hsh3 : (s1_3 &&& 2251799813685247#64) + s1_2 >>> 51 = sh3
  generalize hsh4 : (s1_4 &&& 2251799813685247#64) + s1_3 >>> 51 = sh4
  generalize hsq : (sh4 + (sh3 + (sh2 + (sh1 + (sh0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = sq
  wp_steps; wp_dalek_call_fast black_box_u8_ok; clean_prev_sf2; norm_sf 16; obtain ⟨x0_20, hx0_20_eq, hx0_20⟩ := extract_ct_eq_ret
  rw [ct_select_from_x0 r0_0 rp_0 x0_19 (flippedSign || flippedSignI) hx0_19_ite] at hs1_0
  rw [ct_select_from_x0 r0_1 rp_1 x0_19 (flippedSign || flippedSignI) hx0_19_ite] at hs1_1
  rw [ct_select_from_x0 r0_2 rp_2 x0_19 (flippedSign || flippedSignI) hx0_19_ite] at hs1_2
  rw [ct_select_from_x0 r0_3 rp_3 x0_19 (flippedSign || flippedSignI) hx0_19_ite] at hs1_3
  rw [ct_select_from_x0 r0_4 rp_4 x0_19 (flippedSign || flippedSignI) hx0_19_ite] at hs1_4
  have hs1_0_b := ite_limb_lt hr0_0 hrp_0 s1_0 hs1_0; have hs1_1_b := ite_limb_lt hr0_1 hrp_1 s1_1 hs1_1
  have hs1_2_b := ite_limb_lt hr0_2 hrp_2 s1_2 hs1_2; have hs1_3_b := ite_limb_lt hr0_3 hrp_3 s1_3 hs1_3
  have hs1_4_b := ite_limb_lt hr0_4 hrp_4 s1_4 hs1_4
  have hx0_20_ite : BitVec.truncate 8 x0_20 =
      if (fe51Val s1_0 s1_1 s1_2 s1_3 s1_4 % p25519) % 2 == 1 then 1#8 else 0#8 :=
    hx0_20.trans (fe51_is_negative_math s1_0 s1_1 s1_2 s1_3 s1_4 (by omega) (by omega) (by omega) (by omega) (by omega)
      sh0 sh1 sh2 sh3 sh4 sq hsh0.symm hsh1.symm hsh2.symm hsh3.symm hsh4.symm hsq.symm)
  generalize his_neg : ((fe51Val s1_0 s1_1 s1_2 s1_3 s1_4 % p25519) % 2 == 1) = is_neg at hx0_20_ite
  wp_cut_codeLoaded; wp_sym_steps 21
  generalize hsn0 : ((36028797018963664#64 - s1_0) &&& 2251799813685247#64) +
    BitVec.setWidth 64 (BitVec.setWidth 32 ((36028797018963952#64 - s1_4) >>> 51)) * 19#64 = sn0
  generalize hsn1 : ((36028797018963952#64 - s1_1) &&& 2251799813685247#64) + (36028797018963664#64 - s1_0) >>> 51 = sn1
  generalize hsn2 : ((36028797018963952#64 - s1_2) &&& 2251799813685247#64) + (36028797018963952#64 - s1_1) >>> 51 = sn2
  generalize hsn3 : ((36028797018963952#64 - s1_3) &&& 2251799813685247#64) + (36028797018963952#64 - s1_2) >>> 51 = sn3
  generalize hsn4 : ((36028797018963952#64 - s1_4) &&& 2251799813685247#64) + (36028797018963952#64 - s1_3) >>> 51 = sn4
  wp_sym_steps 20
  have ⟨hsn0_b, hsn1_b, hsn2_b, hsn3_b, hsn4_b, hsn_val⟩ :=
    fe51_neg_math s1_0 s1_1 s1_2 s1_3 s1_4 (by omega) (by omega) (by omega) (by omega) (by omega)
      _ _ _ _ _ sn0 sn1 sn2 sn3 sn4 rfl rfl rfl rfl rfl hsn0.symm hsn1.symm hsn2.symm hsn3.symm hsn4.symm
  generalize hrf0 : (sn0 &&& -(x0_20 &&& 255#64)) ||| (s1_0 &&& ((x0_20 &&& 255#64) - 1#64)) = rf0
  generalize hrf1 : (sn1 &&& -(x0_20 &&& 255#64)) ||| (s1_1 &&& ((x0_20 &&& 255#64) - 1#64)) = rf1
  generalize hrf2 : (sn2 &&& -(x0_20 &&& 255#64)) ||| (s1_2 &&& ((x0_20 &&& 255#64) - 1#64)) = rf2
  generalize hrf3 : (sn3 &&& -(x0_20 &&& 255#64)) ||| (s1_3 &&& ((x0_20 &&& 255#64) - 1#64)) = rf3
  generalize hrf4 : (sn4 &&& -(x0_20 &&& 255#64)) ||| (s1_4 &&& ((x0_20 &&& 255#64) - 1#64)) = rf4
  rw [ct_select_from_x0 s1_0 sn0 x0_20 is_neg hx0_20_ite] at hrf0; rw [ct_select_from_x0 s1_1 sn1 x0_20 is_neg hx0_20_ite] at hrf1
  rw [ct_select_from_x0 s1_2 sn2 x0_20 is_neg hx0_20_ite] at hrf2; rw [ct_select_from_x0 s1_3 sn3 x0_20 is_neg hx0_20_ite] at hrf3
  rw [ct_select_from_x0 s1_4 sn4 x0_20 is_neg hx0_20_ite] at hrf4; apply sepWP_pack_fe51 (sp - 384#64) rf0 rf1 rf2 rf3 rf4
  rw [← hrp_0_eq, ← hrp_1_eq, ← hrp_2_eq, ← hrp_3_eq, ← hrp_4_eq]; apply sepWP_close_bytes40_64 (sp - 184#64) r_prime
  wp_steps; close_cut_codeLoaded; wp_dalek_call_fast black_box_u8_ok; clean_prev_sf2; norm_sf 16; obtain ⟨x0_21, hx0_21_eq, hx0_21⟩ := extract_ct_eq_ret
  have hrf_b52 : fe51LimbsBounded (packFe51Bytes rf0 rf1 rf2 rf3 rf4) (2 ^ 52) :=
    fe51LimbsBounded_packFe51Bytes rf0 rf1 rf2 rf3 rf4 (2 ^ 52)
      (ite_limb_lt hs1_0_b hsn0_b rf0 hrf0) (ite_limb_lt hs1_1_b hsn1_b rf1 hrf1)
      (ite_limb_lt hs1_2_b hsn2_b rf2 hrf2) (ite_limb_lt hs1_3_b hsn3_b rf3 hrf3) (ite_limb_lt hs1_4_b hsn4_b rf4 hrf4)
  have hs1_val := fe51_select_val (flippedSign || flippedSignI) w_10 r_prime
    r0_0 r0_1 r0_2 r0_3 r0_4 rp_0 rp_1 rp_2 rp_3 rp_4 s1_0 s1_1 s1_2 s1_3 s1_4
    hr0_0_eq hr0_1_eq hr0_2_eq hr0_3_eq hr0_4_eq hrp_0_eq hrp_1_eq hrp_2_eq hrp_3_eq hrp_4_eq hs1_0 hs1_1 hs1_2 hs1_3 hs1_4
  have hrf_val := fe51_select_neg_val is_neg _
    s1_0 s1_1 s1_2 s1_3 s1_4 sn0 sn1 sn2 sn3 sn4 rf0 rf1 rf2 rf3 rf4 hs1_val his_neg hsn_val hrf0 hrf1 hrf2 hrf3 hrf4
  have hx0_21_ite : BitVec.truncate 8 x0_21 = if correctSign || flippedSign then 1#8 else 0#8 :=
    hx0_21.trans (truncate8_ze64_or32_ite_comm hx19 hx0_14)
  exact hnext _ (packFe51Bytes rf0 rf1 rf2 rf3 rf4) (by assumption) (by assumption) (by assumption)
    (by assumption) (by assumption) (by rwa [hx0_21_eq]) hrf_b52 hrf_val

private theorem fpMul_mod' (a b : Nat) : fpMul (a % p25519) (b % p25519) = (a * b) % p25519 := by
  unfold VerifiedLibraries.Common.fpMul; rw [Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod]

private theorem fpSq_mod' (a : Nat) : fpSq (a % p25519) = a ^ 2 % p25519 := by
  unfold fpSq; rw [fpMul_mod', ← Nat.pow_two]

private theorem fpPow_p25519_sub5_div8 (x w6 w8 w9 : Nat)
    (hw6 : w6 % p25519 = fpPow (x % p25519) (2 ^ 250 - 1)) (hw8 : w8 % p25519 = w6 ^ (2 ^ (2#32).toNat) % p25519)
    (hw9 : w9 % p25519 = (x * w8) % p25519) : w9 % p25519 = fpPow (x % p25519) ((p25519 - 5) / 8) := by
  have he : 2 ^ 250 - 1 < 2 ^ 256 := by decide
  have hk : ((2 ^ 250 - 1) * 4).succ = (p25519 - 5) / 8 := by unfold p25519; decide
  have hp : (p25519 - 5) / 8 < 2 ^ 256 := by unfold p25519; decide
  generalize 2 ^ 250 - 1 = e at hw6 he hk; generalize (p25519 - 5) / 8 = m at hk hp ⊢
  rw [fpPow_mod_eq_pow_mod x e he] at hw6
  have hw8' : w8 % p25519 = x ^ (e * 4) % p25519 := by
    rw [hw8, show 2 ^ (2#32).toNat = 4 from rfl, Nat.pow_mod, hw6, ← Nat.pow_mod, ← Nat.pow_mul]
  rw [fpPow_mod_eq_pow_mod x m hp, hw9, Nat.mul_mod, hw8', ← Nat.mul_mod, ← Nat.pow_succ', hk]

private theorem sqrt_ratio_math_bridge
    (u_bs v_bs w_1 w_3 w_4 w_5 r0_bs w_8 w_9 w_10 w_11 w_12 ui_bs r_prime : List (BitVec 8)) (s_C : State) (x0_14 : BitVec 64)
    (hw1 : fe51ValOfBytes w_1 % p25519 = (fe51ValOfBytes v_bs) ^ 3 % p25519 := by assumption)
    (hw3 : fe51ValOfBytes w_3 % p25519 = (fe51ValOfBytes v_bs) ^ 7 % p25519 := by assumption)
    (hw4 : fe51ValOfBytes w_4 % p25519 = (fe51ValOfBytes u_bs * fe51ValOfBytes w_1) % p25519 := by assumption)
    (hw5 : fe51ValOfBytes w_5 % p25519 = (fe51ValOfBytes u_bs * fe51ValOfBytes w_3) % p25519 := by assumption)
    (hr0 : fe51ValOfBytes r0_bs % p25519 = fpPow (fe51ValOfBytes w_5 % p25519) (2 ^ 250 - 1) := by assumption)
    (hw8 : fe51ValOfBytes w_8 % p25519 = (fe51ValOfBytes r0_bs) ^ (2 ^ (2#32).toNat) % p25519 := by assumption)
    (hw9 : fe51ValOfBytes w_9 % p25519 = (fe51ValOfBytes w_5 * fe51ValOfBytes w_8) % p25519 := by assumption)
    (hw10 : fe51ValOfBytes w_10 % p25519 = (fe51ValOfBytes w_4 * fe51ValOfBytes w_9) % p25519 := by assumption)
    (hw11 : fe51ValOfBytes w_11 % p25519 = (fe51ValOfBytes w_10) ^ (2 ^ (1#32).toNat) % p25519 := by assumption)
    (hw12 : fe51ValOfBytes w_12 % p25519 = (fe51ValOfBytes v_bs * fe51ValOfBytes w_11) % p25519 := by assumption)
    (hx19 : BitVec.truncate 8 (s_C.readReg64 (Reg.gpr 19#5)) =
      (if natToLeBytes 32 (fe51ValOfBytes w_12 % p25519) == natToLeBytes 32 (fpNeg (fe51ValOfBytes u_bs % p25519))
       then 1#8 else 0#8) := by assumption)
    (hx0_14 : BitVec.truncate 8 x0_14 =
      (if natToLeBytes 32 (fe51ValOfBytes w_12 % p25519) == natToLeBytes 32 (fe51ValOfBytes u_bs % p25519)
       then 1#8 else 0#8) := by assumption)
    (hui : fe51ValOfBytes ui_bs % p25519 =
      (fpNeg (fe51ValOfBytes u_bs % p25519) * fe51ValOfBytes fe51SqrtM1Bytes) % p25519 := by assumption)
    (hx23 : BitVec.truncate 8 (s_C.readReg64 (Reg.gpr 23#5)) =
      (if natToLeBytes 32 (fe51ValOfBytes w_12 % p25519) == natToLeBytes 32 (fe51ValOfBytes ui_bs % p25519)
       then 1#8 else 0#8) := by assumption)
    (hrp : fe51ValOfBytes r_prime % p25519 =
      (fe51ValOfBytes fe51SqrtM1Bytes * fe51ValOfBytes w_10) % p25519 := by assumption) :
    ∃ correctSign flippedSign flippedSignI : Bool,
      BitVec.truncate 8 (s_C.readReg64 (Reg.gpr 19#5)) = (if flippedSign then 1#8 else 0#8) ∧
      BitVec.truncate 8 (s_C.readReg64 (Reg.gpr 23#5)) = (if flippedSignI then 1#8 else 0#8) ∧
      BitVec.truncate 8 x0_14 = (if correctSign then 1#8 else 0#8) ∧
      (correctSign || flippedSign) = (sqrtRatioM1 (fe51ValOfBytes u_bs % p25519) (fe51ValOfBytes v_bs % p25519)).1 ∧
      (let r1_val := if flippedSign || flippedSignI then fe51ValOfBytes r_prime % p25519 else fe51ValOfBytes w_10 % p25519
       (if r1_val % 2 == 1 then fpNeg r1_val else r1_val) =
         (sqrtRatioM1 (fe51ValOfBytes u_bs % p25519) (fe51ValOfBytes v_bs % p25519)).2) := by
  have hp : 0 < p25519 := by unfold p25519; decide
  have hv3 : fpMul (fpSq (fe51ValOfBytes v_bs % p25519)) (fe51ValOfBytes v_bs % p25519) = fe51ValOfBytes w_1 % p25519 := by
    rw [hw1, fpSq_mod', fpMul_mod', ← Nat.pow_succ]
  have hv7 : fpMul (fpSq (fe51ValOfBytes w_1 % p25519)) (fe51ValOfBytes v_bs % p25519) = fe51ValOfBytes w_3 % p25519 := by
    rw [hw3, hw1, fpSq_mod', fpMul_mod', ← Nat.pow_mul, ← Nat.pow_succ]
  have hr0' : fe51ValOfBytes w_10 % p25519 =
      fpMul (fpMul (fe51ValOfBytes u_bs % p25519) (fe51ValOfBytes w_1 % p25519))
        (fpPow (fpMul (fe51ValOfBytes u_bs % p25519) (fe51ValOfBytes w_3 % p25519)) ((p25519 - 5) / 8)) := by
    rw [hw10, ← fpMul_mod', hw4, ← fpMul_mod', fpPow_p25519_sub5_div8 _ _ _ _ hr0 hw8 hw9, hw5, ← fpMul_mod']
  have hchk : fe51ValOfBytes w_12 % p25519 =
      fpMul (fe51ValOfBytes v_bs % p25519) (fpSq (fe51ValOfBytes w_10 % p25519)) := by
    change fe51ValOfBytes w_11 % p25519 = (fe51ValOfBytes w_10) ^ 2 % p25519 at hw11
    rw [hw12, ← fpMul_mod', hw11, fpSq_mod']
  have hsqrt_mod : sqrtM1 % p25519 = sqrtM1 := Nat.mod_eq_of_lt (by unfold sqrtM1 p25519; decide)
  have hui' : fe51ValOfBytes ui_bs % p25519 = fpMul (fpNeg (fe51ValOfBytes u_bs % p25519)) sqrtM1 := by
    rw [hui, fe51SqrtM1_val, ← fpMul_mod', fpNeg_mod', hsqrt_mod]
  have hrp' : fe51ValOfBytes r_prime % p25519 = fpMul sqrtM1 (fe51ValOfBytes w_10 % p25519) := by
    rw [hrp, fe51SqrtM1_val, ← fpMul_mod', hsqrt_mod]
  rw [natToLeBytes_32_beq_iff _ _ (Nat.mod_lt _ hp) (by unfold VerifiedLibraries.Common.fpNeg; exact Nat.mod_lt _ hp)] at hx19
  rw [natToLeBytes_32_beq_iff _ _ (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)] at hx0_14 hx23
  refine ⟨_, _, _, hx19, hx23, hx0_14, ?_, ?_⟩
  · unfold sqrtRatioM1; dsimp only; rw [Nat.mod_mod, Nat.mod_mod, hv3, hv7, ← hr0', ← hchk]
  · unfold sqrtRatioM1; dsimp only; rw [Nat.mod_mod, Nat.mod_mod, hv3, hv7, ← hr0', ← hchk, ← hui', ← hrp']

private theorem copy40_fe51_props_01234 (dst src : List (BitVec 8)) (V : Nat)
    (hdst : dst.length = 40) (hsrc_b : fe51LimbsBounded src (2 ^ 52)) (hsrc_v : fe51ValOfBytes src % p25519 = V) :
    let res := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      dst 0 (ByteSlice.readLE src 0 8)) 8 (ByteSlice.readLE src 8 8)) 16 (ByteSlice.readLE src 16 8))
      24 (ByteSlice.readLE src 24 8)) 32 (ByteSlice.readLE src 32 8)
    res.length = 40 ∧ fe51LimbsBounded res (2 ^ 52) ∧ fe51ValOfBytes res % p25519 = V := by
  haveI : HasLenGe dst 40 := ⟨by omega⟩; intro res
  refine ⟨by simp (disch := decide) only [res, write64_length_eq, hdst, Nat.min_eq_left], ?_, ?_⟩
  · unfold fe51LimbsBounded; simp (disch := decide) only [res, readLE_write64_self', readLE_write64_ne, write64_length_eq, hdst, Nat.min_eq_left]; exact ⟨trivial, hsrc_b.2⟩
  · unfold fe51ValOfBytes; simp (disch := decide) only [res, readLE_write64_self', readLE_write64_ne]; exact hsrc_v

public section

set_option maxHeartbeats 800000 in
theorem fe51_pow22501_ok : Fe51Pow22501Ok := by
  intro _
  apply dalekCaller_ok dalekCliPC04 dalekCliPl04
  intro b hb hbase
  wp_init
  unpack_fe51 h_1
  have ha_pow1 : fe51ValOfBytes a_rest % p25519 = (fe51ValOfBytes a_rest) ^ 1 % p25519 := by rw [Nat.pow_one]
  apply sepWP_split2_80 a_1; intro out0 out1 hout0 hout1
  apply sepWP_split_stack_callee 224 816
  apply sepWP_peel_stack_bytes s0.sp 816 8 808; intro sp_816 h_816; apply sepWP_peel_stack_bytes s0.sp 808 40 768; intro sp_808 h_808
  apply sepWP_peel_stack_bytes s0.sp 768 40 728; intro sp_768 h_768; apply sepWP_peel_stack_bytes s0.sp 728 40 688; intro sp_728 h_728
  apply sepWP_peel_stack_bytes s0.sp 688 40 648; intro sp_688 h_688; apply sepWP_peel_stack_bytes s0.sp 648 40 608; intro sp_648 h_648
  apply sepWP_peel_stack_bytes s0.sp 608 40 568; intro sp_608 h_608; apply sepWP_peel_stack_bytes s0.sp 568 40 528; intro sp_568 h_568
  apply sepWP_peel_stack_bytes s0.sp 528 40 488; intro sp_528 h_528; apply sepWP_peel_stack_bytes s0.sp 488 40 448; intro sp_488 h_488
  apply sepWP_peel_stack_bytes s0.sp 448 40 408; intro sp_448 h_448; apply sepWP_peel_stack_bytes s0.sp 408 40 368; intro sp_408 h_408
  apply sepWP_peel_stack_bytes s0.sp 368 40 328; intro sp_368 h_368; apply sepWP_peel_stack_bytes s0.sp 328 40 288; intro sp_328 h_328
  apply sepWP_peel_stack_bytes s0.sp 288 40 248; intro sp_288 h_288; apply sepWP_peel_stack_bytes s0.sp 248 40 208; intro sp_248 h_248
  apply sepWP_peel_stack_bytes s0.sp 208 40 168; intro sp_208 h_208; apply sepWP_peel_stack_bytes s0.sp 168 40 128; intro sp_168 h_168
  apply sepWP_peel_stack_bytes s0.sp 128 40 88; intro sp_128 h_128; apply sepWP_peel_stack_bytes s0.sp 88 40 48; intro sp_88 h_88
  open_cells (s0.sp - 48#64) 48 6; apply sepWP_callee_224_to_96 s0.sp
  wp_cut_codeLoaded; wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; norm_sf 96; obtain ⟨hw_l, hw_b54, hw_b52, hw_v⟩ := fe51_pow2k_chain_props w 2; unpack_fe51 hw_b54
  wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96; obtain ⟨hw1_l, hw1_b54, hw1_b52, hw1_v⟩ := fe51_pow2k_chain_props w_1 4; unpack_fe51 hw1_b54
  wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96; obtain ⟨hw2_l, hw2_b54, hw2_b52, hw2_v⟩ := fe51_pow2k_chain_props w_2 8; unpack_fe51 hw2_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224; obtain ⟨hw3_l, hw3_b54, hw3_b52, hw3_v⟩ := fe51_mul_chain_props w_3 9; unpack_fe51 hw3_b54
  wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224; obtain ⟨hw4_l, hw4_b54, hw4_b52, hw4_v⟩ := fe51_mul_chain_props w_4 11; unpack_fe51 hw4_b54; clear ha_pow1
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96; obtain ⟨hw5_l, hw5_b54, hw5_b52, hw5_v⟩ := fe51_pow2k_chain_props w_5 22; unpack_fe51 hw5_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224; obtain ⟨hw6_l, hw6_b54, hw6_b52, hw6_v⟩ := fe51_mul_chain_props w_6 (2 ^ 5 - 1); unpack_fe51 hw6_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96; obtain ⟨hw7_l, hw7_b54, hw7_b52, hw7_v⟩ := fe51_pow2k_chain_props w_7 (2 ^ 10 - 2 ^ 5); unpack_fe51 hw7_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224; obtain ⟨hw8_l, hw8_b54, hw8_b52, hw8_v⟩ := fe51_mul_chain_props w_8 (2 ^ 10 - 1); unpack_fe51 hw8_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96; obtain ⟨hw9_l, hw9_b54, hw9_b52, hw9_v⟩ := fe51_pow2k_chain_props w_9 (2 ^ 20 - 2 ^ 10); unpack_fe51 hw9_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224; obtain ⟨hw10_l, hw10_b54, hw10_b52, hw10_v⟩ := fe51_mul_chain_props w_10 (2 ^ 20 - 1); unpack_fe51 hw10_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96; obtain ⟨hw11_l, hw11_b54, hw11_b52, hw11_v⟩ := fe51_pow2k_chain_props w_11 (2 ^ 40 - 2 ^ 20); unpack_fe51 hw11_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224; obtain ⟨hw12_l, hw12_b54, hw12_b52, hw12_v⟩ := fe51_mul_chain_props w_12 (2 ^ 40 - 1); unpack_fe51 hw12_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96; obtain ⟨hw13_l, hw13_b54, hw13_b52, hw13_v⟩ := fe51_pow2k_chain_props w_13 (2 ^ 50 - 2 ^ 10); unpack_fe51 hw13_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224; obtain ⟨hw14_l, hw14_b54, hw14_b52, hw14_v⟩ := fe51_mul_chain_props w_14 (2 ^ 50 - 1); unpack_fe51 hw14_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96; obtain ⟨hw15_l, hw15_b54, hw15_b52, hw15_v⟩ := fe51_pow2k_chain_props w_15 (2 ^ 100 - 2 ^ 50); unpack_fe51 hw15_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224; obtain ⟨hw16_l, hw16_b54, hw16_b52, hw16_v⟩ := fe51_mul_chain_props w_16 (2 ^ 100 - 1); unpack_fe51 hw16_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96; obtain ⟨hw17_l, hw17_b54, hw17_b52, hw17_v⟩ := fe51_pow2k_chain_props w_17 (2 ^ 200 - 2 ^ 100); unpack_fe51 hw17_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224; obtain ⟨hw18_l, hw18_b54, hw18_b52, hw18_v⟩ := fe51_mul_chain_props w_18 (2 ^ 200 - 1); unpack_fe51 hw18_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96; obtain ⟨hw19_l, hw19_b54, hw19_b52, hw19_v⟩ := fe51_pow2k_chain_props w_19 (2 ^ 250 - 2 ^ 50); unpack_fe51 hw19_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224; obtain ⟨hw20_l, hw20_b52, hw20_fp⟩ := fe51_mul_fpPow_props w_20 (2 ^ 250 - 1); try clear hpost_20
  haveI : HasLenGe out1 40 := ⟨by omega⟩; haveI : HasLenGe w_4 40 := ⟨by omega⟩; wp_steps
  apply sepWP_abstract_bytes (a_1 + 40#64)
    (fun t3_bs => t3_bs.length = 40 ∧ fe51LimbsBounded t3_bs (2 ^ 52) ∧ fe51ValOfBytes t3_bs % p25519 = fpPow (fe51ValOfBytes a_rest % p25519) 11)
    (hQ := copy40_fe51_props out1 w_4 (fpPow (fe51ValOfBytes a_rest % p25519) 11) hout1 hw4_b52 (hw4_v.trans (fpPow_mod_eq_pow_mod (fe51ValOfBytes a_rest) 11 (by decide)).symm))
  intro t3_bs ⟨ht3_l, ht3_b52, ht3_v⟩; unpack_fe51 hw20_b52; unpack_fe51 ht3_b52; apply sepWP_merge2_80 a_1; close_cells (s0.sp - 48#64) 48 6
  apply sepWP_unpeel_stack_bytes s0.sp 88 40 48; apply sepWP_unpeel_stack_bytes s0.sp 128 40 88
  apply sepWP_unpeel_stack_bytes s0.sp 168 40 128; apply sepWP_unpeel_stack_bytes s0.sp 208 40 168
  apply sepWP_unpeel_stack_bytes s0.sp 248 40 208; apply sepWP_unpeel_stack_bytes s0.sp 288 40 248
  apply sepWP_unpeel_stack_bytes s0.sp 328 40 288; apply sepWP_unpeel_stack_bytes s0.sp 368 40 328
  apply sepWP_unpeel_stack_bytes s0.sp 408 40 368; apply sepWP_unpeel_stack_bytes s0.sp 448 40 408
  apply sepWP_unpeel_stack_bytes s0.sp 488 40 448; apply sepWP_unpeel_stack_bytes s0.sp 528 40 488
  apply sepWP_unpeel_stack_bytes s0.sp 568 40 528; apply sepWP_unpeel_stack_bytes s0.sp 608 40 568
  apply sepWP_unpeel_stack_bytes s0.sp 648 40 608; apply sepWP_unpeel_stack_bytes s0.sp 688 40 648
  apply sepWP_unpeel_stack_bytes s0.sp 728 40 688; apply sepWP_unpeel_stack_bytes s0.sp 768 40 728
  apply sepWP_unpeel_stack_bytes s0.sp 808 40 768; apply sepWP_unpeel_stack_bytes s0.sp 816 8 808
  apply sepWP_merge_stack_callee 224 816; wp_done

set_option maxHeartbeats 800000 in
theorem fe51_sqrt_ratio_i_ok : Fe51SqrtRatioIOk := by
  intro _
  apply dalekCaller_ok dalekCliPC03 dalekCliPl03
  intro b hb hbase
  wp_init
  have hsqrt_b54 : fe51LimbsBounded fe51SqrtM1Bytes (2 ^ 54) := fe51SqrtM1_limbsBounded
  have hu_b54 := h_6; unpack_fe51 h_6; unpack_fe51 h_1; unpack_fe51 hsqrt_b54
  have hv_pow1 : fe51ValOfBytes a_rest % p25519 = (fe51ValOfBytes a_rest) ^ 1 % p25519 := by rw [Nat.pow_one]
  apply sepWP_split_stack_callee 1040 672
  apply sepWP_peel_memRegion s0.sp 672 192 480; apply sepWP_peel_memRegion s0.sp 480 16 464
  open_cells (s0.sp - 480#64) 16 2; apply sepWP_split32_sub s0.sp 480#64 476#64
  apply sepWP_peel_stack_bytes s0.sp 464 40 424; intro sp_464 h_464
  apply sepWP_peel_stack_bytes s0.sp 424 40 384; intro sp_424 h_424
  apply sepWP_peel_stack_bytes s0.sp 384 40 344; intro sp_384 h_384
  apply sepWP_peel_stack_bytes s0.sp 344 40 304; intro sp_344 h_344
  apply sepWP_peel_stack_bytes s0.sp 304 40 264; intro sp_304 h_304
  apply sepWP_peel_stack_bytes s0.sp 264 40 224; intro sp_264 h_264
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro sp_224 h_224
  apply sepWP_peel_stack_bytes s0.sp 184 40 144; intro sp_184 h_184
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro sp_144 h_144
  apply sepWP_peel_stack_bytes s0.sp 104 8 96; intro sp_104 h_104
  open_cells (s0.sp - 96#64) 96 12
  apply sepWP_callee_shrink (s0.sp - 672#64) 1040 96 944
  wp_cut_codeLoaded; wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; norm_sf 96
  obtain ⟨hw_l, hw_b54, hw_b52, hw_v⟩ := fe51_pow2k_chain_props w 2; unpack_fe51 hw_b54
  apply sepWP_callee_grow (s0.sp - 672#64) 1040 96 944; apply sepWP_callee_shrink (s0.sp - 672#64) 1040 224 816
  wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224
  obtain ⟨hw1_l, hw1_b54, hw1_b52, hw1_v⟩ := fe51_mul_chain_props w_1 3; unpack_fe51 hw1_b54
  apply sepWP_callee_grow (s0.sp - 672#64) 1040 224 816; apply sepWP_callee_shrink (s0.sp - 672#64) 1040 96 944
  wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96
  obtain ⟨hw2_l, hw2_b54, hw2_b52, hw2_v⟩ := fe51_pow2k_chain_props w_2 6; unpack_fe51 hw2_b54
  apply sepWP_callee_grow (s0.sp - 672#64) 1040 96 944; apply sepWP_callee_shrink (s0.sp - 672#64) 1040 224 816
  wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224
  obtain ⟨hw3_l, hw3_b54, hw3_b52, hw3_v⟩ := fe51_mul_chain_props w_3 7; clear hv_pow1; unpack_fe51 hw3_b54
  wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224
  obtain ⟨hw4_l, hw4_b54, hw4_b52⟩ := fe51_b52_props w_4; unpack_fe51 hw4_b54
  wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224
  obtain ⟨hw5_l, hw5_b54, hw5_b52⟩ := fe51_b52_props w_5; unpack_fe51 hw5_b54
  apply sepWP_callee_grow (s0.sp - 672#64) 1040 224 816; apply sepWP_merge2_80 (s0.sp - 184#64)
  have h_80 : (w_2 ++ sp_144).length = 80 := by simp [hw2_l, h_144]
  wp_steps; wp_dalek_call_fast fe51_pow22501_ok; clean_prev_sf2; norm_sf 1040
  obtain ⟨hw6_l, hw6_b54, hw6_b52⟩ := fe51_b52_props w_6; obtain ⟨hw7_l, _, _⟩ := fe51_b52_props w_7
  apply sepWP_split_append_40 (s0.sp - 184#64)
  haveI : HasLenGe sp_224 40 := ⟨by omega⟩; haveI : HasLenGe w_6 40 := ⟨by omega⟩
  apply sepWP_callee_shrink (s0.sp - 672#64) 1040 96 944
  wp_cut_codeLoaded; wp_steps
  apply sepWP_abstract_bytes (s0.sp - 224#64)
    (fun r0_bs => r0_bs.length = 40 ∧ fe51LimbsBounded r0_bs (2 ^ 52) ∧
      fe51ValOfBytes r0_bs % p25519 = fpPow (fe51ValOfBytes w_5 % p25519) (2 ^ 250 - 1))
    (hQ := copy40_fe51_props sp_224 w_6 (fpPow (fe51ValOfBytes w_5 % p25519) (2 ^ 250 - 1)) h_224 hw6_b52 (by assumption))
  intro r0_bs ⟨hr0_l, hr0_b52, hr0_v⟩; obtain ⟨_, hr0_b54, _⟩ := fe51_b52_props r0_bs; unpack_fe51 hr0_b54
  close_cut_codeLoaded; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96
  obtain ⟨hw8_l, hw8_b54, hw8_b52⟩ := fe51_b52_props w_8; unpack_fe51 hw8_b54
  apply sepWP_callee_grow (s0.sp - 672#64) 1040 96 944; apply sepWP_callee_shrink (s0.sp - 672#64) 1040 224 816
  wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224
  obtain ⟨hw9_l, hw9_b54, hw9_b52⟩ := fe51_b52_props w_9; unpack_fe51 hw9_b54
  wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224
  obtain ⟨hw10_l, hw10_b54, hw10_b52⟩ := fe51_b52_props w_10; have hw10_b54' := hw10_b54; unpack_fe51 hw10_b54'
  apply sepWP_callee_grow (s0.sp - 672#64) 1040 224 816; apply sepWP_callee_shrink (s0.sp - 672#64) 1040 96 944
  wp_steps; wp_dalek_call_fast fe51_pow2k_nat_ok; clean_prev_sf2; norm_sf 96
  obtain ⟨hw11_l, hw11_b54, hw11_b52⟩ := fe51_b52_props w_11; unpack_fe51 hw11_b54
  apply sepWP_callee_grow (s0.sp - 672#64) 1040 96 944; apply sepWP_callee_shrink (s0.sp - 672#64) 1040 224 816
  wp_steps; wp_dalek_call_fast fe51_mul_ok; clean_prev_sf2; norm_sf 224
  obtain ⟨hw12_l, hw12_b54, hw12_b52⟩ := fe51_b52_props w_12
  apply sqrt_ratio_phaseB b s0.sp a w_12 r0_bs w_11 a_4 _ hb hbase
    (by assumption) (by assumption) (by assumption) (by assumption) hsp_align (by assumption) (by assumption) hw12_b54 hr0_l hw11_l hu_b54
  intro sf_B ui_bs nu_fe51 x0_14 hcl_B hpc_B hrun_B hsp_B hx21_B hx22_B hx29_B hvregs_B hx19_B hx0_14_B hui_b52 hui_v hnu_l
  apply sqrt_ratio_phaseC b s0.sp w_10 w_4 w_9 w_12 ui_bs nu_fe51 hb hbase hcl_B
    hpc_B hrun_B hsp_B hsp_align hx21_B hx22_B hx29_B hw10_b54 hw4_l hw9_l hw12_b54 hui_b52 hnu_l
  intro sf_C r_prime c344_bs ui304_bs hcl_C hpc_C hrun_C hsp_C hx19_C hx21_C hx23_C hx26_C hx29_C hvregs_C hrp_b52 hrp_v hc344_l hui304_l
  rw [← hx19_C] at hx19_B
  obtain ⟨correctSign, flippedSign, flippedSignI, hx19_b, hx23_b, hx0_14_b, hsr1, hsr2⟩ :=
    sqrt_ratio_math_bridge a_4 a_rest w_1 w_3 w_4 w_5 r0_bs w_8 w_9 w_10 w_11 w_12 ui_bs r_prime sf_C x0_14
  apply sepWP_callee_shrink (s0.sp - 672#64) 224 16 208
  apply sqrt_ratio_phaseD b s0.sp w_10 r_prime x0_14 correctSign flippedSign flippedSignI hb hbase hcl_C
    hpc_C hrun_C hsp_C hsp_align hx19_b hx21_C hx23_b hx26_C hx29_C hx0_14_b hw10_b52 hrp_b52
  intro sf_D r_final r1_val hpc_D hrun_D hsp_D hx29_D hvregs_D hx0_D hrf_b52 hrf_v
  have hvregs_all : calleeSavedVRegs sf_D = calleeSavedVRegs s0 := by rw [hvregs_D, hvregs_C, hvregs_B]; assumption
  generalize hsr_eq : sqrtRatioM1 (fe51ValOfBytes a_4 % p25519) (fe51ValOfBytes a_rest % p25519) = sr at hsr1 hsr2 ⊢
  clear hsr_eq; rw [hsr1] at hx0_D; rw [hsr2] at hrf_v
  apply sepWP_split_48_1_7_40 a_1; intro out_b0 pad_bs out_40 hpad hout40
  have hrf_l := hrf_b52.1; have hrp_l := hrp_b52.1; have hui_l := hui_b52.1
  haveI : HasLenGe out_40 40 := ⟨by omega⟩; haveI : HasLenGe r_final 40 := ⟨by omega⟩
  wp_steps
  apply sepWP_abstract_bytes (a_1 + 8#64)
    (fun r_bs => r_bs.length = 40 ∧ fe51LimbsBounded r_bs (2 ^ 52) ∧ fe51ValOfBytes r_bs % p25519 = sr.2)
    (hQ := copy40_fe51_props_01234 out_40 r_final sr.2 hout40 hrf_b52 hrf_v)
  intro r_bs ⟨hr_l, hr_b52, hr_v⟩; unpack_fe51 hr_b52
  apply sepWP_merge_1_7_40 a_1 _ pad_bs r_bs hpad
  apply sepWP_callee_grow (s0.sp - 672#64) 224 16 208; apply sepWP_callee_grow (s0.sp - 672#64) 1040 224 816
  close_cells (s0.sp - 96#64) 96 12
  apply sepWP_unpeel_stack_bytes s0.sp 104 8 96; apply sepWP_unpeel_stack_bytes s0.sp 144 40 104
  apply sepWP_unpeel_stack_bytes s0.sp 184 40 144; apply sepWP_unpeel_stack_bytes s0.sp 224 40 184
  apply sepWP_unpeel_stack_bytes s0.sp 264 40 224; apply sepWP_unpeel_stack_bytes s0.sp 304 40 264
  apply sepWP_unpeel_stack_bytes s0.sp 344 40 304; apply sepWP_unpeel_stack_bytes s0.sp 384 40 344
  apply sepWP_unpeel_stack_bytes s0.sp 424 40 384; apply sepWP_unpeel_stack_bytes s0.sp 464 40 424
  apply sepWP_combine32_sub s0.sp 480#64 476#64; close_cells_sub s0.sp 480 16 2
  apply sepWP_unpeel_memRegion s0.sp 480 16 464; apply sepWP_unpeel_memRegion s0.sp 672 192 480
  apply sepWP_merge_stack_callee 1040 672; wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Pow

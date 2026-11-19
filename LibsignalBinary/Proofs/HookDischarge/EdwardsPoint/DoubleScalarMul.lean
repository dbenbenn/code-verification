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
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DoubleScalarMulNaf
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `EdwardsPoint::vartime_double_scalar_mul_basepoint` Machine-Code Proof

Machine-code verification of `B17` (`vartime_double_scalar_mul_basepoint_ok_of`) in
`dalekCliMultiLib`: Straus interleaved Horner loop, NAF setup and lookup-table initialization,
and final projective-to-extended conversion.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DoubleScalarMul

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpMul fpPow EdExtPoint)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase dalekCaller_ok dalekCall_of_blockOk
  seq_codeLoaded_lr goalIsSeqCodeLoaded clearOldCodeLoadedHyps)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51ValOfBytes fe51_one fe51OneBytes fe51_edwards_d2 fe51EdwardsD2Bytes
  odd_multiples_basepoint oddMultiplesBasepointBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (
  oddMultiplesBasepointBytes_length
  fe51One_readLE_0 fe51One_readLE_8 fe51One_readLE_16 fe51One_readLE_24 fe51One_readLE_32)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded Fe51MulOk Fe51MulRoRightOk Fe51Pow2kOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  fpPow_two_eq_fpSq fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded fe51Point3Bounded
  edExtOfBytes edProjOfBytes edProjDouble edAsExtended edAsProjective
  nafTable5Points fe51NafTable5Bounded naf5Loop naf5ByteValid naf8Loop findMaxNafIdx
  edStrausStepA edAffineBasepointEntry edStrausStepB edStrausStep edStrausLoop
  edProjectiveToExtended edDoubleScalarMulBasepoint
  ProjectivePointDoubleOk EdwardsPointAddProjNielsOk EdwardsPointSubProjNielsOk
  EdwardsPointAddAffineNielsRoOk EdwardsPointSubAffineNielsRoOk
  NafLookupTable5FromOk VartimeDoubleScalarMulBasepointOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe sub_ofNat64_add write64_length_eq readLE_write64_self' readLE_write64_ne
  readLE_append_left readLE_append_right fold_fe51ValOfBytes
  fe51LimbsBounded_slice_of_at fe51ValOfBytes_slice
  sepWP_focus_bytes sepWP_unfocus_bytes sepWP_abstract_bytes
  sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_split4_160 sepWP_merge4_160 edAsExtended_of_append4)
open scoped LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DoubleScalarMulNaf (
  dalekCliLib17 dalekCliPl17 dalekCliPC17 dalekCliPl17_eq dalekCliPC17_eq dalekCliPC17_block_eq
  dalekCliPl17_rho_norm oddMultiplesBasepointBytes_slice_bounded
  NafLoopRegs naf5_loop_ok naf5Loop_length_valid naf8_loop_ok naf8Loop_length_valid
  ofNat_sub_1 ofNat_succ_beq_zero find_max_naf_loop_ok
  sepWP_dsmb_callee_to sepWP_dsmb_callee_from fe51Point4Bounded_of_bounds
  sepWP_split4_completed_432 sepWP_split4_stack_272 sepWP_merge4_432_272_ext
  sepWP_focus_ro_slice sepWP_unfocus_ro_slice)

attribute [local simp, local arm64_norm, local wp_norm] dalekCliPl17_rho_norm
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8
  fe51One_readLE_0 fe51One_readLE_8 fe51One_readLE_16 fe51One_readLE_24 fe51One_readLE_32

local syntax "wp_dalek_call17" ppSpace colGt term:max (ppSpace colGt wppCallOpt)* : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wp_dalek_call17 $hcall:term $[$opts:wppCallOpt]*) => do
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
        throwError "wp_dalek_call17: expected `SepWP` goal, got `{ty}`"
      Term.exprToSyntax (ty.getArg! 0)
    let hclPost ← mkFreshUserName `hcl_post
    let hclPostId := mkIdent hclPost
    evalTactic (← `(tactic| (
      apply seq_codeLoaded_lr ‹_›
      wp_call (dalekCall_of_blockOk $progStx $hcall
        (lib := dalekCliLib17) (pl := dalekCliPl17)
        (hP := congrArg (fun p : Program => p.rebase _ (fun _ => none)) dalekCliPC17_eq)) $[$opts]*)))
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

/-! ## 1. Projective Buffer & Signed NAF Digit Helpers -/

private theorem dsmb_init_proj_post (dst : List (BitVec 8)) (hdst : dst.length = 120) :
    let buf := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        dst 32 0#64) 16 0#64) 24 0#64) 0 0#64) 8 0#64) 72 0#64) 112 0#64)
        40 1#64) 48 0#64) 56 0#64) 64 0#64)
        80 1#64) 88 0#64) 96 0#64) 104 0#64
    fe51Point3Bounded buf (2 ^ 52) ∧ edProjOfBytes buf = ⟨0, 1, 1, 0⟩ := by
  haveI : HasLenGe dst 120 := ⟨by omega⟩
  unfold fe51Point3Bounded fe51LimbsBoundedAt edProjOfBytes
  simp (disch := decide) only [fe51ValAt, ↓readLE_write64_self', ↓readLE_write64_ne,
    write64_length_eq, hdst]; decide

private theorem dsmb_copy120_proj_post (dst src b0 b1 b2 b3 : List (BitVec 8)) (C : EdExtPoint)
    (hdst : dst.length = 120) (hsrc : src = b0 ++ (b1 ++ (b2 ++ b3)))
    (hb0 : fe51LimbsBounded b0 (2 ^ 52)) (hb1 : fe51LimbsBounded b1 (2 ^ 52))
    (hb2 : fe51LimbsBounded b2 (2 ^ 52))
    (hv0 : fe51ValOfBytes b0 % p25519 = fpMul C.X C.T) (hv1 : fe51ValOfBytes b1 % p25519 = fpMul C.Y C.Z)
    (hv2 : fe51ValOfBytes b2 % p25519 = fpMul C.Z C.T) :
    let buf := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        dst 96 (ByteSlice.readLE src 96 8)) 104 (ByteSlice.readLE src 104 8))
        64 (ByteSlice.readLE src 64 8)) 72 (ByteSlice.readLE src 72 8))
        80 (ByteSlice.readLE src 80 8)) 88 (ByteSlice.readLE src 88 8))
        112 (ByteSlice.readLE src 112 8)) 0 (ByteSlice.readLE src 0 8)) 8 (ByteSlice.readLE src 8 8))
        16 (ByteSlice.readLE src 16 8)) 24 (ByteSlice.readLE src 24 8))
        32 (ByteSlice.readLE src 32 8)) 40 (ByteSlice.readLE src 40 8))
        48 (ByteSlice.readLE src 48 8)) 56 (ByteSlice.readLE src 56 8)
    fe51Point3Bounded buf (2 ^ 52) ∧ edProjOfBytes buf = edAsProjective C := by
  haveI : HasLenGe dst 120 := ⟨by omega⟩
  obtain ⟨h0_l, h0_b⟩ := hb0; obtain ⟨h1_l, h1_b⟩ := hb1; obtain ⟨h2_l, h2_b⟩ := hb2
  have hr0 (off : Nat) (ho : off + 8 ≤ 40) : ByteSlice.readLE src off 8 = ByteSlice.readLE b0 off 8 := by
    rw [hsrc]; exact readLE_append_left b0 _ off 8 (by omega)
  have hr1 (off : Nat) (ho1 : 40 ≤ off) (ho2 : off + 8 ≤ 80) : ByteSlice.readLE src off 8 = ByteSlice.readLE b1 (off - 40) 8 := by
    rw [hsrc, readLE_append_right b0 _ off 8 (by omega), h0_l, readLE_append_left b1 _ (off - 40) 8 (by omega)]
  have hr2 (off : Nat) (ho1 : 80 ≤ off) (ho2 : off + 8 ≤ 120) : ByteSlice.readLE src off 8 = ByteSlice.readLE b2 (off - 80) 8 := by
    rw [hsrc, readLE_append_right b0 _ off 8 (by omega), h0_l, readLE_append_right b1 _ (off - 40) 8 (by omega),
        h1_l, show off - 40 - 40 = off - 80 by omega, readLE_append_left b2 _ (off - 80) 8 (by omega)]
  unfold fe51Point3Bounded fe51LimbsBoundedAt edProjOfBytes edAsProjective
  simp (disch := decide) only [fe51ValAt, ↓readLE_write64_self', ↓readLE_write64_ne, write64_length_eq, hdst]
  simp (disch := omega) only [hr0, hr1, hr2, Nat.reduceAdd, Nat.reduceSub,
    fold_fe51ValOfBytes b0, fold_fe51ValOfBytes b1, fold_fe51ValOfBytes b2, hv0, hv1, hv2]
  exact ⟨⟨rfl, h0_b, h1_b, h2_b⟩, trivial⟩

private def strausLoopPre [DalekCliPlacement] (sp0 : BitVec 64)
    (naf_a naf_b tab_bs p_bs c_bs ext_bs : List (BitVec 8)) (F : SepProp) : SepProp :=
  memRegion (sp0 - 2368#64 - 2640#64) 2640 ∗
  (odd_multiples_basepoint dalekCliMpl ↦ᵣ oddMultiplesBasepointBytes) ∗
  ((sp0 - 2352#64) ↦ₛ naf_a) ∗ ((sp0 - 2096#64) ↦ₛ naf_b) ∗ ((sp0 - 1840#64) ↦ₛ tab_bs) ∗
  ((sp0 - 560#64) ↦ₛ p_bs) ∗ ((sp0 - 432#64) ↦ₛ c_bs) ∗ ((sp0 - 272#64) ↦ₛ ext_bs) ∗ F

private structure StrausLoopRegs [DalekCliPlacement] (s0 s : State) (i : Nat) (pc_val : BitVec 64) : Prop where
  hpc : s.pc = pc_val
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 2368#64
  hx19 : s.readReg64 (.gpr 19#5) = 160#64
  hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 i
  hx22 : s.readReg64 (.gpr 22#5) = s0.sp - 1840#64
  hx23 : s.readReg64 (.gpr 23#5) = s0.sp - 432#64
  hx24 : s.readReg64 (.gpr 24#5) = s0.sp - 272#64
  hx25 : s.readReg64 (.gpr 25#5) = s0.sp - 2352#64
  hx26 : s.readReg64 (.gpr 26#5) = s0.sp - 2096#64
  hx27 : s.readReg64 (.gpr 27#5) = odd_multiples_basepoint dalekCliMpl
  hx28 : s.readReg64 (.gpr 28#5) = 120#64
  hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64
  hvregs : calleeSavedVRegs s = calleeSavedVRegs s0
  hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem

private theorem naf_sgn_w8 (d : BitVec 8) :
    BitVec.setWidth 32
      ((if ¬(BitVec.setWidth 32 (BitVec.signExtend 64 d) - 0#32).msb = true then
          if (BitVec.setWidth 32 (BitVec.signExtend 64 d)).sle 0#32 = true then 0#64 else 1#64
        else 4294967295#64) &&& 1095216660735#64) =
      if d == 0#8 then 0#32 else if !d.msb then 1#32 else 255#32 := by
  revert d; decide +kernel

private theorem naf5_pos_ule16 (d : BitVec 8) (hv : naf5ByteValid d = true) (hmsb : d.msb = false) :
    (16#32).ule (BitVec.setWidth 32 (BitVec.signExtend 64 d)) = false := by
  revert hv hmsb; unfold naf5ByteValid; revert d; decide +kernel

private theorem naf5_pos_off (d : BitVec 8) (hv : naf5ByteValid d = true) (hmsb : d.msb = false) :
    (BitVec.signExtend 64 d >>> 1) * 160#64 = BitVec.ofNat 64 (160 * (d.toNat / 2)) ∧ d.toNat / 2 < 8 := by
  revert hv hmsb; unfold naf5ByteValid; revert d; decide +kernel

private theorem naf5_neg_ule16 (d : BitVec 8) (hv : naf5ByteValid d = true) (hmsb : d.msb = true) :
    (16#32).ule (BitVec.setWidth 32
      (BitVec.setWidth 64 (0#32 - BitVec.setWidth 32 (BitVec.signExtend 64 d)) &&& 1095216660735#64)) = false := by
  revert hv hmsb; unfold naf5ByteValid; revert d; decide +kernel

private theorem naf5_neg_off (d : BitVec 8) (hv : naf5ByteValid d = true) (hmsb : d.msb = true) :
    ((BitVec.setWidth 64 (0#32 - BitVec.setWidth 32 (BitVec.signExtend 64 d)) >>> 0 &&& 255#64 |||
      (if (BitVec.setWidth 64 (0#32 - BitVec.setWidth 32 (BitVec.signExtend 64 d))).getLsbD 7 = true then
          18446744073709551615#64 else 0#64) &&& 18446744073709551360#64) >>> 1) * 160#64 =
      BitVec.ofNat 64 (160 * ((256 - d.toNat) / 2)) ∧ (256 - d.toNat) / 2 < 8 := by
  revert hv hmsb; unfold naf5ByteValid; revert d; decide +kernel

private theorem naf8_pos_lsb31 (d : BitVec 8) (hmsb : d.msb = false) :
    (BitVec.signExtend 64 d).getLsbD 31 = false := by revert hmsb; revert d; decide +kernel

private theorem naf8_pos_off (d : BitVec 8) (hmsb : d.msb = false) :
    (BitVec.signExtend 64 d >>> 1) * 120#64 = BitVec.ofNat 64 (120 * (d.toNat / 2)) ∧ d.toNat / 2 < 64 := by
  revert hmsb; revert d; decide +kernel

private theorem naf8_neg_lsb7 (d : BitVec 8) (hv : (d != 128#8) = true) (hmsb : d.msb = true) :
    (BitVec.setWidth 64 (0#32 - BitVec.setWidth 32 (BitVec.signExtend 64 d))).getLsbD 7 = false := by
  revert hv hmsb; revert d; decide +kernel

private theorem naf8_neg_off (d : BitVec 8) (hv : (d != 128#8) = true) (hmsb : d.msb = true) :
    ((BitVec.setWidth 64 (0#32 - BitVec.setWidth 32 (BitVec.signExtend 64 d)) >>> 0 &&& 255#64 ||| 0#64) >>> 1) * 120#64 =
      BitVec.ofNat 64 (120 * ((256 - d.toNat) / 2)) ∧ (256 - d.toNat) / 2 < 64 := by
  revert hv hmsb; revert d; decide +kernel

/-! ## 2. Straus Interleaved Horner Step & Loop (`+0x210..+0x468`) -/

private theorem straus_b_dispatch_ok [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl17 b) (_hbase : dalekCliPl17.base = b)
    (i : Nat) (_hi : i < 256) (s0 s : State) (target_pc : BitVec 64) (from_ccc0 : Bool)
    (naf_a naf_b tab_bs p_bs c_bs ext_bs : List (BitVec 8)) (F : SepProp) (post : State → SepProp → Prop)
    (hregs : StrausLoopRegs s0 s i (if from_ccc0 then b + 796#64 else b + 664#64))
    (hb_len : naf_b.length = 256)
    (hnext : ∀ s' : State,
      StrausLoopRegs s0 s' i
        (if naf_b.getD i 0#8 == 0#8 then b + 1016#64 else if !(naf_b.getD i 0#8).msb then b + 828#64 else b + 920#64) →
      s'.readReg64 (.gpr 21#5) = BitVec.signExtend 64 (naf_b.getD i 0#8) →
      SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s'
        (strausLoopPre s0.sp naf_a naf_b tab_bs p_bs c_bs ext_bs F) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s
      (strausLoopPre s0.sp naf_a naf_b tab_bs p_bs c_bs ext_bs F) post := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
  unfold strausLoopPre
  cases from_ccc0
  · simp only [Bool.false_eq_true, ↓ite_false] at hpc
    wp_sym_steps 6; simp only [naf_sgn_w8]
    cases hdb0 : (naf_b.getD i 0#8 == 0#8)
    · simp only [Bool.false_eq_true, ↓ite_false]
      cases hmsb : (naf_b.getD i 0#8).msb <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓ite_true, ↓ite_false] <;>
        (wp_sym_steps 2; exact hnext _
          ⟨by simp only [hdb0, hmsb, Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓ite_true, ↓ite_false]; wp_norm_lhs,
           by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
           by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
           by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
          (by wp_norm_lhs))
    · simp only [↓ite_true]; wp_sym_steps 1
      exact hnext _
        ⟨by simp only [hdb0, ↓ite_true]; wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
         by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
         by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by wp_norm_lhs)
  · simp only [↓ite_true] at hpc
    wp_sym_steps 6; simp only [naf_sgn_w8]
    cases hdb0 : (naf_b.getD i 0#8 == 0#8)
    · simp only [Bool.false_eq_true, ↓ite_false]
      cases hmsb : (naf_b.getD i 0#8).msb <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓ite_true, ↓ite_false] <;>
        (wp_sym_steps 2; exact hnext _
          ⟨by simp only [hdb0, hmsb, Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓ite_true, ↓ite_false]; wp_norm_lhs,
           by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
           by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
           by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
          (by wp_norm_lhs))
    · simp only [↓ite_true, beq_self_eq_true]
      exact hnext _
        ⟨by simp only [hdb0, ↓ite_true]; wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
         by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
         by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by wp_norm_lhs)

private theorem sepWP_fold_strausLoopPre [DalekCliPlacement] (sp0 : BitVec 64)
    {naf_a naf_b tab_bs p_bs c_bs ext_bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp0 - 2368#64 - 2640#64) 2640 ∗
      (odd_multiples_basepoint dalekCliMpl ↦ᵣ oddMultiplesBasepointBytes) ∗
      ((sp0 - 2352#64) ↦ₛ naf_a) ∗ ((sp0 - 2096#64) ↦ₛ naf_b) ∗ ((sp0 - 1840#64) ↦ₛ tab_bs) ∗
      ((sp0 - 560#64) ↦ₛ p_bs) ∗ ((sp0 - 432#64) ↦ₛ c_bs) ∗ ((sp0 - 272#64) ↦ₛ ext_bs)) ∗ F := by sep_frame)
    (hnext : SepWP prog target_pc s (strausLoopPre sp0 naf_a naf_b tab_bs p_bs c_bs ext_bs F) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hm : strausLoopPre sp0 naf_a naf_b tab_bs p_bs c_bs ext_bs F =
      (memRegion (sp0 - 2368#64 - 2640#64) 2640 ∗
      (odd_multiples_basepoint dalekCliMpl ↦ᵣ oddMultiplesBasepointBytes) ∗
      ((sp0 - 2352#64) ↦ₛ naf_a) ∗ ((sp0 - 2096#64) ↦ₛ naf_b) ∗ ((sp0 - 1840#64) ↦ₛ tab_bs) ∗
      ((sp0 - 560#64) ↦ₛ p_bs) ∗ ((sp0 - 432#64) ↦ₛ c_bs) ∗ ((sp0 - 272#64) ↦ₛ ext_bs)) ∗ F := by
    unfold strausLoopPre; sep_ac_rfl
  rw [hf, ← hm]; exact hnext

private theorem edProjDouble_of_edProjOfBytes {p_bs : List (BitVec 8)} {P : EdExtPoint}
    (hp : edProjOfBytes p_bs = P) :
    edProjDouble (fe51ValAt p_bs 0) (fe51ValAt p_bs 40) (fe51ValAt p_bs 80) = edProjDouble P.X P.Y P.Z := by
  rw [← hp]; simp only [edProjOfBytes, edProjDouble, Nat.mod_mod]

private theorem fe51Point3Bounded_weaken {bs : List (BitVec 8)} (h : fe51Point3Bounded bs (2 ^ 52)) :
    bs.length = 120 ∧ fe51LimbsBoundedAt bs 0 (2 ^ 53) ∧ fe51LimbsBoundedAt bs 40 (2 ^ 53) ∧ fe51LimbsBoundedAt bs 80 (2 ^ 54) := by
  rcases h with ⟨hl, ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩⟩
  exact ⟨hl, ⟨by omega, by omega, by omega, by omega, by omega⟩,
         ⟨by omega, by omega, by omega, by omega, by omega⟩,
         ⟨by omega, by omega, by omega, by omega, by omega⟩⟩

private theorem projNiels_slice_bounds {sl : List (BitVec 8)} (h : fe51Point4Bounded sl (2 ^ 53)) :
    fe51LimbsBoundedAt sl 0 (2 ^ 54) ∧ fe51LimbsBoundedAt sl 40 (2 ^ 54) ∧
    fe51LimbsBoundedAt sl 80 (2 ^ 54) ∧ fe51LimbsBoundedAt sl 120 (2 ^ 54) := by
  have h54 := fe51Point4Bounded_of_bounds h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  exact h54.2

open Lean Meta Elab Tactic in
local elab "clean_sf" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut stateDecls : Array LocalDecl := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && decl.type.isConstOf ``Arm64.State && decl.userName != `s0 then
      stateDecls := stateDecls.push decl
  if stateDecls.size ≥ 2 then
    let prevSf := stateDecls[stateDecls.size - 2]!
    let currSf := stateDecls[stateDecls.size - 1]!
    let mut prevEqs : Array FVarId := #[]
    let mut currHyps : Array FVarId := #[]
    for decl in lctx do
      if !decl.isImplementationDetail && decl.fvarId != prevSf.fvarId && decl.fvarId != currSf.fvarId then
        let ty ← instantiateMVars decl.type
        if ty.containsFVar prevSf.fvarId then
          if !ty.containsFVar currSf.fvarId then
            if let some (_, lhs, _) := ty.eq? then
              if lhs.containsFVar prevSf.fvarId then prevEqs := prevEqs.push decl.fvarId
          else currHyps := currHyps.push decl.fvarId
    for cId in currHyps do
      let cIdent := mkIdent (← cId.getUserName)
      for pId in prevEqs do
        let pIdent := mkIdent (← pId.getUserName)
        try evalTactic (← `(tactic| rw [$pIdent:term] at $cIdent:ident))
        catch _ => pure ()
    withMainContext do
      for decl in (← getLCtx) do
        if !decl.isImplementationDetail && decl.fvarId != prevSf.fvarId then
          if (← instantiateMVars decl.type).containsFVar prevSf.fvarId then
            let id := mkIdent decl.userName
            try evalTactic (← `(tactic| clear $id:ident))
            catch _ => pure ()
      let prevId := mkIdent prevSf.userName
      try evalTactic (← `(tactic| clear $prevId:ident))
      catch _ => pure ()

local macro "wp_4mul_to_ext " sp0:term:max C:term:max b80:term:max hM:ident : tactic => `(tactic| (
  apply sepWP_split4_completed_432 $sp0 $C
  intro c0 c1 c2 c3 _ _ _ _ hc0_b hc1_b hc2_b hc3_b _ _ _ _
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_stack_272 $sp0; intro e0 e1 e2 e3 _ _ _ _
  apply sepWP_dsmb_callee_to $sp0 224
  wp_sym_steps 4; wp_dalek_call17 $hM; clean_sf; norm_sf 224
  wp_sym_steps 4; wp_dalek_call17 $hM; clean_sf; norm_sf 224
  wp_sym_steps 4; wp_dalek_call17 $hM; clean_sf; norm_sf 224
  wp_sym_steps 4; wp_dalek_call17 $hM; clean_sf; norm_sf 224
  apply sepWP_dsmb_callee_from $sp0 224
  apply sepWP_merge4_432_272_ext $sp0 $C $b80))

set_option maxHeartbeats 800000 in
private theorem straus_step_a_ok [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl17 b) (_hbase : dalekCliPl17.base = b)
    (hDouble : ProjectivePointDoubleOk) (hMul : Fe51MulOk)
    (hAddP : EdwardsPointAddProjNielsOk) (hSubP : EdwardsPointSubProjNielsOk)
    (i : Nat) (_hi : i < 256) (s0 s : State) (target_pc : BitVec 64)
    (naf_a naf_b tab_bs p_bs c_bs ext_bs : List (BitVec 8))
    (P : EdExtPoint) (table_A : Nat → EdExtPoint) (F : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : s0.spAligned = true) (hregs : StrausLoopRegs s0 s i (b + 528#64))
    (hna_len : naf_a.length = 256) (hna_val : naf5ByteValid (naf_a.getD i 0#8) = true)
    (htab_b : fe51NafTable5Bounded tab_bs (2 ^ 53))
    (htab_v : ∀ j < 8, edExtOfBytes (ProofLib.ByteSlice.slice tab_bs (160 * j) 160) = table_A j)
    (hp_b : fe51Point3Bounded p_bs (2 ^ 52)) (hp_v : edProjOfBytes p_bs = P)
    (hc_len : c_bs.length = 160) (hext_len : ext_bs.length = 160)
    (hnext : ∀ (s' : State) (c_bs' ext_bs' : List (BitVec 8)) (from_ccc0 : Bool),
      StrausLoopRegs s0 s' i (if from_ccc0 then b + 796#64 else b + 664#64) →
      fe51Point4Bounded c_bs' (2 ^ 54) →
      edExtOfBytes c_bs' = edStrausStepA (edProjDouble P.X P.Y P.Z) table_A (naf_a.getD i 0#8) →
      ext_bs'.length = 160 →
      SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s'
        (strausLoopPre s0.sp naf_a naf_b tab_bs p_bs c_bs' ext_bs' F) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s
      (strausLoopPre s0.sp naf_a naf_b tab_bs p_bs c_bs ext_bs F) post := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
  unfold strausLoopPre
  have hp_w := fe51Point3Bounded_weaken hp_b
  have hp_len : p_bs.length = 120 := hp_w.1
  have hp_0' : fe51LimbsBoundedAt p_bs 0 (2 ^ 53) := hp_w.2.1
  have hp_40' : fe51LimbsBoundedAt p_bs 40 (2 ^ 53) := hp_w.2.2.1
  have hp_80' : fe51LimbsBoundedAt p_bs 80 (2 ^ 54) := hp_w.2.2.2
  unpack_fe51_at hp_0'; unpack_fe51_at hp_40'; unpack_fe51_at hp_80'
  wp_sym_steps 3; apply sepWP_dsmb_callee_to s0.sp 400
  wp_dalek_call17 hDouble; clean_sf; norm_sf 400; apply sepWP_dsmb_callee_from s0.sp 400
  let C0 := edProjDouble P.X P.Y P.Z
  have hc0_b : fe51Point4Bounded w (2 ^ 54) :=
    fe51Point4Bounded_of_bounds (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  have hc0_v : edExtOfBytes w = C0 := by rw [‹edExtOfBytes w = _›, edProjDouble_of_edProjOfBytes hp_v]
  have htab_len : tab_bs.length = 1280 := htab_b.1
  wp_sym_steps 6; simp only [naf_sgn_w8]
  cases hda0 : (naf_a.getD i 0#8 == 0#8)
  · simp only [Bool.false_eq_true, ↓ite_false]
    cases hmsb : (naf_a.getD i 0#8).msb
    · simp only [Bool.not_false, ↓ite_true]; wp_sym_steps 2
      wp_4mul_to_ext s0.sp C0 (2 ^ 54) hMul
      intro c_tmp ext_tmp hc_tmp_l hext_tmp_l hext_0 hext_40 hext_80 hext_120 hext_v
      unpack_fe51_at hext_0; unpack_fe51_at hext_40; unpack_fe51_at hext_80; unpack_fe51_at hext_120
      wp_sym_steps 3; simp only [naf5_pos_ule16 _ hna_val hmsb, Bool.false_eq_true, ↓ite_false]
      wp_sym_steps 4; obtain ⟨hoff, hidx⟩ := naf5_pos_off _ hna_val hmsb; rw [hoff]
      obtain ⟨ht0, ht40, ht80, ht120⟩ := projNiels_slice_bounds (htab_b.2 _ hidx)
      unpack_fe51_at ht0; unpack_fe51_at ht40; unpack_fe51_at ht80; unpack_fe51_at ht120
      apply sepWP_focus_bytes (s0.sp - 1840#64) _ (160 * ((naf_a.getD i 0#8).toNat / 2)) 160 (hlen := by omega) (hptr := rfl); intro _
      apply sepWP_dsmb_callee_to s0.sp 576; wp_dalek_call17 hAddP; clean_sf; norm_sf 576; apply sepWP_dsmb_callee_from s0.sp 576
      apply sepWP_unfocus_bytes (s0.sp - 1840#64) _ (160 * ((naf_a.getD i 0#8).toNat / 2)) 160 (hlen := by omega) (hptr := rfl)
      apply sepWP_fold_strausLoopPre s0.sp
      exact hnext _ _ ext_tmp false
        ⟨by simp only [Bool.false_eq_true, ↓ite_false]; wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
         by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ‹_›⟩
        (fe51Point4Bounded_of_bounds (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
        (by unfold edStrausStepA; simp only [hda0, hmsb, Bool.false_eq_true, Bool.not_false, ↓ite_false, ↓ite_true]; rw [← hext_v, ← htab_v _ hidx]; assumption)
        hext_tmp_l
    · simp only [Bool.not_true, Bool.false_eq_true, ↓ite_false]; wp_sym_steps 2
      wp_4mul_to_ext s0.sp C0 (2 ^ 54) hMul
      intro c_tmp ext_tmp hc_tmp_l hext_tmp_l hext_0 hext_40 hext_80 hext_120 hext_v
      unpack_fe51_at hext_0; unpack_fe51_at hext_40; unpack_fe51_at hext_80; unpack_fe51_at hext_120
      wp_sym_steps 6; simp only [naf5_neg_ule16 _ hna_val hmsb, Bool.false_eq_true, ↓ite_false]
      wp_sym_steps 4; obtain ⟨hoff, hidx⟩ := naf5_neg_off _ hna_val hmsb; rw [hoff]
      obtain ⟨ht0, ht40, ht80, ht120⟩ := projNiels_slice_bounds (htab_b.2 _ hidx)
      unpack_fe51_at ht0; unpack_fe51_at ht40; unpack_fe51_at ht80; unpack_fe51_at ht120
      apply sepWP_focus_bytes (s0.sp - 1840#64) _ (160 * ((256 - (naf_a.getD i 0#8).toNat) / 2)) 160 (hlen := by omega) (hptr := rfl); intro _
      apply sepWP_dsmb_callee_to s0.sp 576; wp_dalek_call17 hSubP; clean_sf; norm_sf 576; apply sepWP_dsmb_callee_from s0.sp 576
      apply sepWP_unfocus_bytes (s0.sp - 1840#64) _ (160 * ((256 - (naf_a.getD i 0#8).toNat) / 2)) 160 (hlen := by omega) (hptr := rfl)
      apply sepWP_fold_strausLoopPre s0.sp
      exact hnext _ _ ext_tmp true
        ⟨by simp only [↓ite_true]; wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
         by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ‹_›⟩
        (fe51Point4Bounded_of_bounds (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
        (by unfold edStrausStepA; simp only [hda0, hmsb, Bool.false_eq_true, Bool.not_true, ↓ite_false]; rw [← hext_v, ← htab_v _ hidx]; assumption)
        hext_tmp_l
  · simp only [↓ite_true, beq_self_eq_true]
    apply sepWP_fold_strausLoopPre s0.sp
    exact hnext _ w ext_bs false
      ⟨by simp only [Bool.false_eq_true, ↓ite_false]; wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
       by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
       by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
      hc0_b (by unfold edStrausStepA; simp only [hda0, ↓ite_true]; exact hc0_v) hext_len

set_option maxHeartbeats 800000 in
private theorem straus_step_b_ok [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl17 b) (_hbase : dalekCliPl17.base = b)
    (hMul : Fe51MulOk) (hAddA : EdwardsPointAddAffineNielsRoOk) (hSubA : EdwardsPointSubAffineNielsRoOk)
    (i : Nat) (_hi : i < 256) (s0 s : State) (target_pc : BitVec 64)
    (naf_a naf_b tab_bs p_bs c_bs ext_bs : List (BitVec 8))
    (C1 : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : s0.spAligned = true)
    (hregs : StrausLoopRegs s0 s i
      (if naf_b.getD i 0#8 == 0#8 then b + 1016#64 else if !(naf_b.getD i 0#8).msb then b + 828#64 else b + 920#64))
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.signExtend 64 (naf_b.getD i 0#8))
    (_hnb_len : naf_b.length = 256) (hnb_val : (naf_b.getD i 0#8 != 128#8) = true)
    (hc_b : fe51Point4Bounded c_bs (2 ^ 54)) (hc_v : edExtOfBytes c_bs = C1)
    (hext_len : ext_bs.length = 160)
    (hnext : ∀ (s' : State) (c_bs' ext_bs' : List (BitVec 8)),
      StrausLoopRegs s0 s' i (b + 1016#64) →
      fe51Point4Bounded c_bs' (2 ^ 54) →
      edExtOfBytes c_bs' = edStrausStepB C1 (naf_b.getD i 0#8) →
      ext_bs'.length = 160 →
      SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s'
        (strausLoopPre s0.sp naf_a naf_b tab_bs p_bs c_bs' ext_bs' F) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s
      (strausLoopPre s0.sp naf_a naf_b tab_bs p_bs c_bs ext_bs F) post := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
  cases hdb0 : (naf_b.getD i 0#8 == 0#8)
  · cases hmsb : (naf_b.getD i 0#8).msb
    · simp only [hdb0, hmsb, Bool.false_eq_true, Bool.not_false, ↓ite_false, ↓ite_true] at hpc
      unfold strausLoopPre
      wp_4mul_to_ext s0.sp C1 (2 ^ 52) hMul
      intro c_tmp ext_tmp hc_tmp_l hext_tmp_l hext_0 hext_40 hext_80 hext_120 hext_v
      unpack_fe51_at hext_0; unpack_fe51_at hext_40; unpack_fe51_at hext_80; unpack_fe51_at hext_120
      wp_sym_steps 2; simp only [naf8_pos_lsb31 _ hmsb]
      wp_sym_steps 4; obtain ⟨hoff, hidx⟩ := naf8_pos_off _ hmsb; rw [hoff]
      obtain ⟨hsl_l, ht0, ht40, ht80⟩ := oddMultiplesBasepointBytes_slice_bounded hidx
      unpack_fe51_at ht0; unpack_fe51_at ht40; unpack_fe51_at ht80
      apply sepWP_focus_ro_slice (odd_multiples_basepoint dalekCliMpl) _
        (120 * ((naf_b.getD i 0#8).toNat / 2)) 120 (hlen := by rw [oddMultiplesBasepointBytes_length]; omega) (hptr := rfl); intro _
      apply sepWP_dsmb_callee_to s0.sp 528; wp_dalek_call17 hAddA; clean_sf; norm_sf 528; apply sepWP_dsmb_callee_from s0.sp 528
      apply sepWP_unfocus_ro_slice (odd_multiples_basepoint dalekCliMpl) _
        (120 * ((naf_b.getD i 0#8).toNat / 2)) 120 (hlen := by rw [oddMultiplesBasepointBytes_length]; omega) (hptr := rfl)
      wp_sym_steps 1; apply sepWP_fold_strausLoopPre s0.sp
      exact hnext _ _ ext_tmp
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
         by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
         by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (fe51Point4Bounded_of_bounds (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
        (by unfold edStrausStepB edAffineBasepointEntry; simp only [hdb0, hmsb, Bool.false_eq_true, Bool.not_false, ↓ite_false, ↓ite_true]; rw [← hext_v]; assumption)
        hext_tmp_l
    · simp only [hdb0, hmsb, Bool.false_eq_true, Bool.not_true, ↓ite_false] at hpc
      unfold strausLoopPre
      wp_4mul_to_ext s0.sp C1 (2 ^ 52) hMul
      intro c_tmp ext_tmp hc_tmp_l hext_tmp_l hext_0 hext_40 hext_80 hext_120 hext_v
      unpack_fe51_at hext_0; unpack_fe51_at hext_40; unpack_fe51_at hext_80; unpack_fe51_at hext_120
      wp_sym_steps 4; simp only [naf8_neg_lsb7 _ hnb_val hmsb, Bool.false_eq_true, ↓ite_false]
      wp_sym_steps 4; obtain ⟨hoff, hidx⟩ := naf8_neg_off _ hnb_val hmsb; rw [hoff]
      obtain ⟨hsl_l, ht0, ht40, ht80⟩ := oddMultiplesBasepointBytes_slice_bounded hidx
      unpack_fe51_at ht0; unpack_fe51_at ht40; unpack_fe51_at ht80
      apply sepWP_focus_ro_slice (odd_multiples_basepoint dalekCliMpl) _
        (120 * ((256 - (naf_b.getD i 0#8).toNat) / 2)) 120 (hlen := by rw [oddMultiplesBasepointBytes_length]; omega) (hptr := rfl); intro _
      apply sepWP_dsmb_callee_to s0.sp 528; wp_dalek_call17 hSubA; clean_sf; norm_sf 528; apply sepWP_dsmb_callee_from s0.sp 528
      apply sepWP_unfocus_ro_slice (odd_multiples_basepoint dalekCliMpl) _
        (120 * ((256 - (naf_b.getD i 0#8).toNat) / 2)) 120 (hlen := by rw [oddMultiplesBasepointBytes_length]; omega) (hptr := rfl)
      apply sepWP_fold_strausLoopPre s0.sp
      exact hnext _ _ ext_tmp
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
         by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ‹_›⟩
        (fe51Point4Bounded_of_bounds (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
        (by unfold edStrausStepB edAffineBasepointEntry; simp only [hdb0, hmsb, Bool.false_eq_true, Bool.not_true, ↓ite_false]; rw [← hext_v]; assumption)
        hext_tmp_l
  · simp only [hdb0, ↓ite_true] at hpc
    exact hnext s c_bs ext_bs
      ⟨hpc, hrun, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
      hc_b (by unfold edStrausStepB; simp only [hdb0, ↓ite_true, hc_v]) hext_len

private theorem sepWP_merge4_432_272_proj (sp : BitVec 64) (C : EdExtPoint)
    {c0 c1 c2 c3 b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 432#64) ↦ₛ c0) ∗ ((sp - 392#64) ↦ₛ c1) ∗ ((sp - 352#64) ↦ₛ c2) ∗ ((sp - 312#64) ↦ₛ c3) ∗
                  ((sp - 272#64) ↦ₛ b0) ∗ ((sp - 232#64) ↦ₛ b1) ∗ ((sp - 192#64) ↦ₛ b2) ∗ ((sp - 152#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (hc0 : c0.length = 40 := by assumption) (hc1 : c1.length = 40 := by assumption)
    (hc2 : c2.length = 40 := by assumption) (hc3 : c3.length = 40 := by assumption)
    (hcv0 : fe51ValOfBytes c0 % p25519 = C.X := by assumption)
    (hcv1 : fe51ValOfBytes c1 % p25519 = C.Y := by assumption)
    (hcv2 : fe51ValOfBytes c2 % p25519 = C.Z := by assumption)
    (hcv3 : fe51ValOfBytes c3 % p25519 = C.T := by assumption)
    (hb0 : fe51LimbsBounded b0 (2 ^ 52) := by assumption) (hb1 : fe51LimbsBounded b1 (2 ^ 52) := by assumption)
    (hb2 : fe51LimbsBounded b2 (2 ^ 52) := by assumption) (hb3_l : b3.length = 40 := by assumption)
    (hp0 : fe51ValOfBytes b0 % p25519 = (fe51ValOfBytes c0 * fe51ValOfBytes c3) % p25519 := by assumption)
    (hp1 : fe51ValOfBytes b1 % p25519 = (fe51ValOfBytes c1 * fe51ValOfBytes c2) % p25519 := by assumption)
    (hp2 : fe51ValOfBytes b2 % p25519 = (fe51ValOfBytes c2 * fe51ValOfBytes c3) % p25519 := by assumption)
    (hnext : ∀ c_bs ext_bs : List (BitVec 8),
      c_bs.length = 160 → ext_bs.length = 160 →
      (∀ dst : List (BitVec 8), dst.length = 120 →
        let buf := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
          (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
          (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
            dst 96 (ByteSlice.readLE ext_bs 96 8)) 104 (ByteSlice.readLE ext_bs 104 8))
            64 (ByteSlice.readLE ext_bs 64 8)) 72 (ByteSlice.readLE ext_bs 72 8))
            80 (ByteSlice.readLE ext_bs 80 8)) 88 (ByteSlice.readLE ext_bs 88 8))
            112 (ByteSlice.readLE ext_bs 112 8)) 0 (ByteSlice.readLE ext_bs 0 8)) 8 (ByteSlice.readLE ext_bs 8 8))
            16 (ByteSlice.readLE ext_bs 16 8)) 24 (ByteSlice.readLE ext_bs 24 8))
            32 (ByteSlice.readLE ext_bs 32 8)) 40 (ByteSlice.readLE ext_bs 40 8))
            48 (ByteSlice.readLE ext_bs 48 8)) 56 (ByteSlice.readLE ext_bs 56 8)
        fe51Point3Bounded buf (2 ^ 52) ∧ edProjOfBytes buf = edAsProjective C) →
      SepWP prog target_pc s ((((sp - 432#64) ↦ₛ c_bs) ∗ ((sp - 272#64) ↦ₛ ext_bs)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hc2' : sp - 352#64 + BitVec.ofNat 64 c2.length = sp - 312#64 := by rw [hc2]; exact sub_ofNat64_add sp 352 40
  have hc1' : sp - 392#64 + BitVec.ofNat 64 c1.length = sp - 352#64 := by rw [hc1]; exact sub_ofNat64_add sp 392 40
  have hc0' : sp - 432#64 + BitVec.ofNat 64 c0.length = sp - 392#64 := by rw [hc0]; exact sub_ofNat64_add sp 432 40
  have ha2 : sp - 192#64 + BitVec.ofNat 64 b2.length = sp - 152#64 := by rw [hb2.1]; exact sub_ofNat64_add sp 192 40
  have ha1 : sp - 232#64 + BitVec.ofNat 64 b1.length = sp - 192#64 := by rw [hb1.1]; exact sub_ofNat64_add sp 232 40
  have ha0 : sp - 272#64 + BitVec.ofNat 64 b0.length = sp - 232#64 := by rw [hb0.1]; exact sub_ofNat64_add sp 272 40
  have hmc : ((sp - 432#64) ↦ₛ (c0 ++ (c1 ++ (c2 ++ c3)))) ∗ ((sp - 272#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 432#64) ↦ₛ c0) ∗ ((sp - 392#64) ↦ₛ c1) ∗ ((sp - 352#64) ↦ₛ c2) ∗ ((sp - 312#64) ↦ₛ c3) ∗
      ((sp - 272#64) ↦ₛ b0) ∗ ((sp - 232#64) ↦ₛ b1) ∗ ((sp - 192#64) ↦ₛ b2) ∗ ((sp - 152#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, hc0', pointsToBytes_append, hc1', pointsToBytes_append, hc2',
        pointsToBytes_append, ha0, pointsToBytes_append, ha1, pointsToBytes_append, ha2]; sep_ac_rfl
  rw [hf, ← hmc]
  have hv0 : fe51ValOfBytes b0 % p25519 = fpMul C.X C.T := by unfold fpMul; rw [hp0, Nat.mul_mod, hcv0, hcv3, ← Nat.mul_mod]
  have hv1 : fe51ValOfBytes b1 % p25519 = fpMul C.Y C.Z := by unfold fpMul; rw [hp1, Nat.mul_mod, hcv1, hcv2, ← Nat.mul_mod]
  have hv2 : fe51ValOfBytes b2 % p25519 = fpMul C.Z C.T := by unfold fpMul; rw [hp2, Nat.mul_mod, hcv2, hcv3, ← Nat.mul_mod]
  exact hnext (c0 ++ (c1 ++ (c2 ++ c3))) (b0 ++ (b1 ++ (b2 ++ b3)))
    (by simp [List.length_append, hc0, hc1, hc2, hc3])
    (by simp [List.length_append, hb0.1, hb1.1, hb2.1, hb3_l])
    (fun dst hdst => dsmb_copy120_proj_post dst (b0 ++ (b1 ++ (b2 ++ b3))) b0 b1 b2 b3 C hdst rfl hb0 hb1 hb2 hv0 hv1 hv2)

set_option maxHeartbeats 800000 in
private theorem straus_step_end_ok [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl17 b) (_hbase : dalekCliPl17.base = b)
    (hMul : Fe51MulOk) (i : Nat) (s0 s : State) (target_pc : BitVec 64)
    (naf_a naf_b tab_bs p_bs c_bs ext_bs : List (BitVec 8))
    (C2 : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : s0.spAligned = true) (hregs : StrausLoopRegs s0 s i (b + 1016#64))
    (hp_len : p_bs.length = 120) (hc_b : fe51Point4Bounded c_bs (2 ^ 54))
    (hc_v : edExtOfBytes c_bs = C2) (hext_len : ext_bs.length = 160)
    (hnext : ∀ (s' : State) (p_bs' c_bs' ext_bs' : List (BitVec 8)),
      StrausLoopRegs s0 s' i (b + 1116#64) →
      fe51Point3Bounded p_bs' (2 ^ 52) →
      edProjOfBytes p_bs' = edAsProjective C2 →
      c_bs'.length = 160 → ext_bs'.length = 160 →
      SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s'
        (strausLoopPre s0.sp naf_a naf_b tab_bs p_bs' c_bs' ext_bs' F) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s
      (strausLoopPre s0.sp naf_a naf_b tab_bs p_bs c_bs ext_bs F) post := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
  unfold strausLoopPre
  apply sepWP_split4_completed_432 s0.sp C2
  intro c0 c1 c2 c3 _ _ _ _ hc0_b hc1_b hc2_b hc3_b _ _ _ _
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_stack_272 s0.sp; intro e0 e1 e2 e3 _ _ _ _
  apply sepWP_dsmb_callee_to s0.sp 224
  wp_sym_steps 4; wp_dalek_call17 hMul; clean_sf; norm_sf 224
  wp_sym_steps 4; wp_dalek_call17 hMul; clean_sf; norm_sf 224
  wp_sym_steps 4; wp_dalek_call17 hMul; clean_sf; norm_sf 224
  apply sepWP_dsmb_callee_from s0.sp 224
  apply sepWP_merge4_432_272_proj s0.sp C2
  intro c_tmp ext_tmp hc_tmp_l hext_tmp_l hcopy
  haveI : HasLenGe ext_tmp 160 := ⟨by omega⟩; haveI : HasLenGe p_bs 120 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 13
  apply sepWP_abstract_bytes (s0.sp - 560#64)
    (Q := fun bs => fe51Point3Bounded bs (2 ^ 52) ∧ edProjOfBytes bs = edAsProjective C2)
    (hQ := hcopy p_bs hp_len)
  intro p_bs' ⟨hp'_b, hp'_v⟩
  close_cut_codeLoaded
  apply sepWP_fold_strausLoopPre s0.sp
  exact hnext _ p_bs' c_tmp ext_tmp
    ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ‹_›⟩
    hp'_b hp'_v hc_tmp_l hext_tmp_l

private theorem straus_loop_ok [DalekCliPlacement] (b : BitVec 64)
    (hb : DalekBase dalekCliPl17 b) (hbase : dalekCliPl17.base = b)
    (hDouble : ProjectivePointDoubleOk) (hMul : Fe51MulOk)
    (hAddP : EdwardsPointAddProjNielsOk) (hSubP : EdwardsPointSubProjNielsOk)
    (hAddA : EdwardsPointAddAffineNielsRoOk) (hSubA : EdwardsPointSubAffineNielsRoOk)
    (i : Nat) (hi : i < 256) (s0 s : State) (target_pc : BitVec 64)
    (naf_a naf_b tab_bs p_bs c_bs ext_bs : List (BitVec 8))
    (P : EdExtPoint) (table_A : Nat → EdExtPoint) (F : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : s0.spAligned = true) (hregs : StrausLoopRegs s0 s i (b + 528#64))
    (hna_len : naf_a.length = 256) (hna_val : ∀ j < 256, naf5ByteValid (naf_a.getD j 0#8) = true)
    (hnb_len : naf_b.length = 256) (hnb_val : ∀ j < 256, (naf_b.getD j 0#8 != 128#8) = true)
    (htab_b : fe51NafTable5Bounded tab_bs (2 ^ 53))
    (htab_v : ∀ j < 8, edExtOfBytes (ProofLib.ByteSlice.slice tab_bs (160 * j) 160) = table_A j)
    (hp_b : fe51Point3Bounded p_bs (2 ^ 52)) (hp_v : edProjOfBytes p_bs = P)
    (hc_len : c_bs.length = 160) (hext_len : ext_bs.length = 160)
    (hnext : ∀ (s' : State) (p_bs' c_bs' ext_bs' : List (BitVec 8)),
      StrausLoopRegs s0 s' 0 (b + 1128#64) →
      fe51Point3Bounded p_bs' (2 ^ 52) →
      edProjOfBytes p_bs' = edStrausLoop naf_a naf_b table_A i P →
      c_bs'.length = 160 → ext_bs'.length = 160 →
      SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s'
        (strausLoopPre s0.sp naf_a naf_b tab_bs p_bs' c_bs' ext_bs' F) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s
      (strausLoopPre s0.sp naf_a naf_b tab_bs p_bs c_bs ext_bs F) post := by
  induction i generalizing s p_bs c_bs ext_bs P with
  | zero =>
    apply straus_step_a_ok b hb hbase hDouble hMul hAddP hSubP 0 hi s0 s target_pc naf_a naf_b tab_bs p_bs c_bs ext_bs P table_A F post
      hsp0_align hregs hna_len (hna_val 0 hi) htab_b htab_v hp_b hp_v hc_len hext_len
    intro s1 c1 ext1 from_ccc0 hr1 hc1_b hc1_v hext1_l
    apply straus_b_dispatch_ok b hb hbase 0 hi s0 s1 target_pc from_ccc0 naf_a naf_b tab_bs p_bs c1 ext1 F post hr1 hnb_len
    intro s2 hr2 hx21
    apply straus_step_b_ok b hb hbase hMul hAddA hSubA 0 hi s0 s2 target_pc naf_a naf_b tab_bs p_bs c1 ext1 _ F post
      hsp0_align hr2 hx21 hnb_len (hnb_val 0 hi) hc1_b hc1_v hext1_l
    intro s3 c2 ext2 hr3 hc2_b hc2_v hext2_l
    apply straus_step_end_ok b hb hbase hMul 0 s0 s3 target_pc naf_a naf_b tab_bs p_bs c2 ext2 _ F post
      hsp0_align hr3 hp_b.1 hc2_b hc2_v hext2_l
    intro s4 p_bs' c_bs' ext_bs' hr4 hp'_b hp'_v hc'_l hext'_l
    rcases hr4 with ⟨hpc, hrun, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
    wp_sym_steps 1
    exact hnext _ p_bs' c_bs' ext_bs'
      ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
       by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
       by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
      hp'_b (by unfold edStrausLoop edStrausStep; rw [hp'_v]) hc'_l hext'_l
  | succ k ih =>
    apply straus_step_a_ok b hb hbase hDouble hMul hAddP hSubP (k + 1) hi s0 s target_pc naf_a naf_b tab_bs p_bs c_bs ext_bs P table_A F post
      hsp0_align hregs hna_len (hna_val (k + 1) hi) htab_b htab_v hp_b hp_v hc_len hext_len
    intro s1 c1 ext1 from_ccc0 hr1 hc1_b hc1_v hext1_l
    apply straus_b_dispatch_ok b hb hbase (k + 1) hi s0 s1 target_pc from_ccc0 naf_a naf_b tab_bs p_bs c1 ext1 F post hr1 hnb_len
    intro s2 hr2 hx21
    apply straus_step_b_ok b hb hbase hMul hAddA hSubA (k + 1) hi s0 s2 target_pc naf_a naf_b tab_bs p_bs c1 ext1 _ F post
      hsp0_align hr2 hx21 hnb_len (hnb_val (k + 1) hi) hc1_b hc1_v hext1_l
    intro s3 c2 ext2 hr3 hc2_b hc2_v hext2_l
    apply straus_step_end_ok b hb hbase hMul (k + 1) s0 s3 target_pc naf_a naf_b tab_bs p_bs c2 ext2 _ F post
      hsp0_align hr3 hp_b.1 hc2_b hc2_v hext2_l
    intro s4 p_bs' c_bs' ext_bs' hr4 hp'_b hp'_v hc'_l hext'_l
    rcases hr4 with ⟨hpc, hrun, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
    wp_sym_steps 1; simp only [ofNat_succ_beq_zero hi, Bool.false_eq_true, ↓ite_false]; wp_sym_steps 2
    exact ih (by omega) _ p_bs' c_bs' ext_bs' (edStrausStep P table_A (naf_a.getD (k + 1) 0#8) (naf_b.getD (k + 1) 0#8))
      ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
       by simp only [State.readReg64_setPC]; exact ofNat_sub_1 (by omega),
       by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
       by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
      hp'_b (by unfold edStrausStep; exact hp'_v) hc'_l hext'_l hnext

/-! ## 3. NAF Setup, Table Construction, Final Extended Conversion & Top-Level Proof (`B17`) -/

private theorem write64_zero_32_eq_replicate (bs : List (BitVec 8)) (h : bs.length = 256) :
    ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 bs
      0 0#64) 8 0#64) 16 0#64) 24 0#64) 32 0#64) 40 0#64) 48 0#64) 56 0#64)
      64 0#64) 72 0#64) 80 0#64) 88 0#64) 96 0#64) 104 0#64) 112 0#64) 120 0#64)
      128 0#64) 136 0#64) 144 0#64) 152 0#64) 160 0#64) 168 0#64) 176 0#64) 184 0#64)
      192 0#64) 200 0#64) 208 0#64) 216 0#64) 224 0#64) 232 0#64) 240 0#64) 248 0#64 =
    List.replicate 256 0#8 := by
  rw [ByteSlice.write64_zero bs 0 (by omega)]
  repeat (rw [ByteSlice.write64_fillSet_range_zero bs 0 _ (by decide) (by omega)]; simp only [Nat.reduceAdd])
  exact ByteSlice.fillSet_all h (fun i hi => by simp [hi])

private theorem write64_pad40_eq (sc40 src : List (BitVec 8)) (hsc : sc40.length = 40) (hsrc : src.length = 32) :
    ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 sc40 32 0#64)
      0 (ByteSlice.readLE src 0 8)) 8 (ByteSlice.readLE src 8 8))
      16 (ByteSlice.readLE src 16 8)) 24 (ByteSlice.readLE src 24 8) =
    src ++ List.replicate 8 0#8 := by
  haveI : HasLenGe sc40 40 := ⟨by omega⟩
  have hlen_lhs : (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 sc40 32 0#64) 0 (ByteSlice.readLE src 0 8)) 8 (ByteSlice.readLE src 8 8))
      16 (ByteSlice.readLE src 16 8)) 24 (ByteSlice.readLE src 24 8)).length = 40 := by
    simp only [write64_length_eq, hsc]; decide
  apply ByteSlice.ext_getD (by simp [hlen_lhs, hsrc])
  intro i hi; rw [hlen_lhs] at hi
  simp (disch := byte_region_len) only [ByteSlice.getD_write64, ByteSlice.extractLsb'_readLE, BitVec.extractLsb'_zero]
  by_cases h32 : i < 32
  · have hlt : i < src.length := by omega
    conv => rhs; rw [List.getD_eq_getElem?_getD, List.getElem?_append]
    simp only [hlt, ↓ite_true, ← List.getD_eq_getElem?_getD]
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals first | rfl | omega | (congr 2; omega)
  · have hnlt : ¬ i < src.length := by omega
    have hrep : i - src.length < 8 := by omega
    conv => rhs; rw [List.getD_eq_getElem?_getD, List.getElem?_append]
    simp only [hnlt, ↓ite_false, ← List.getD_eq_getElem?_getD, ByteSlice.getD_replicate', hrep, ↓ite_true]
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals first | rfl | omega

private theorem sepWP_congr_pre {prog : Program} {t : BitVec 64} {s : State} {P Q : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hnext : SepWP prog t s Q post oom) (h : P = Q := by (try dsimp +zetaDelta only); sep_ac_rfl) : SepWP prog t s P post oom :=
  h ▸ hnext

set_option maxHeartbeats 800000 in
private theorem dsmb_naf_setup_ok [DalekCliPlacement] (b : BitVec 64)
    (hb : DalekBase dalekCliPl17 b) (hbase : dalekCliPl17.base = b)
    (s0 s : State) (target_pc out a A b_sc : BitVec 64)
    (slot16 na0 nb0 sc40 a_bs b_bs : List (BitVec 8)) (F : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = b + 32#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2368#64)
    (hx8 : s.readReg64 (.gpr 8#5) = out) (hx0 : s.readReg64 (.gpr 0#5) = a)
    (hx1 : s.readReg64 (.gpr 1#5) = A) (hx2 : s.readReg64 (.gpr 2#5) = b_sc)
    (hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem)
    (hslot16 : slot16.length = 16) (hna0 : na0.length = 256) (hnb0 : nb0.length = 256)
    (hsc40 : sc40.length = 40) (ha_len : a_bs.length = 32) (hb_len : b_bs.length = 32)
    (hnext : ∀ s' : State,
      let naf_a := naf5Loop (a_bs ++ List.replicate 8 0#8) 256 0 0#64 (List.replicate 256 0#8)
      let naf_b := naf8Loop (b_bs ++ List.replicate 8 0#8) 256 0 0#64 (List.replicate 256 0#8)
      NafLoopRegs s0 s' A b_sc (b + 428#64) →
      s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (findMaxNafIdx naf_a naf_b 255) →
      naf_a.length = 256 → (∀ j < 256, naf5ByteValid (naf_a.getD j 0#8) = true) →
      naf_b.length = 256 → (∀ j < 256, (naf_b.getD j 0#8 != 128#8) = true) →
      SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s'
        (((s0.sp - 2368#64) ↦ₛ ByteSlice.write64 (ByteSlice.write64 slot16 0 0#64) 8 out) ∗
         ((s0.sp - 2352#64) ↦ₛ naf_a) ∗ ((s0.sp - 2096#64) ↦ₛ naf_b) ∗
         ((s0.sp - 1840#64) ↦ₛ (b_bs ++ List.replicate 8 0#8)) ∗
         (a ↦ₛ a_bs) ∗ (b_sc ↦ₛ b_bs) ∗ F) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s
      (((s0.sp - 2368#64) ↦ₛ slot16) ∗ ((s0.sp - 2352#64) ↦ₛ na0) ∗ ((s0.sp - 2096#64) ↦ₛ nb0) ∗
       ((s0.sp - 1840#64) ↦ₛ sc40) ∗ (a ↦ₛ a_bs) ∗ (b_sc ↦ₛ b_bs) ∗ F) post := by
  haveI : HasLenGe slot16 16 := ⟨by omega⟩; haveI : HasLenGe na0 256 := ⟨by omega⟩
  haveI : HasLenGe nb0 256 := ⟨by omega⟩; haveI : HasLenGe sc40 40 := ⟨by omega⟩
  haveI : HasLenGe a_bs 32 := ⟨by omega⟩; haveI : HasLenGe b_bs 32 := ⟨by omega⟩
  wp_cut_codeLoaded hcl
  wp_sym_steps 21
  wp_conv_pre => rw [write64_zero_32_eq_replicate na0 hna0, write64_pad40_eq sc40 a_bs hsc40 ha_len]
  close_cut_codeLoaded
  have hxa_len : (a_bs ++ List.replicate 8 0#8).length = 40 := by simp [ha_len]
  let slot16' := ByteSlice.write64 (ByteSlice.write64 slot16 0 0#64) 8 out
  let naf_a := naf5Loop (a_bs ++ List.replicate 8 0#8) 256 0 0#64 (List.replicate 256 0#8)
  let naf_b := naf8Loop (b_bs ++ List.replicate 8 0#8) 256 0 0#64 (List.replicate 256 0#8)
  refine sepWP_congr_pre (naf5_loop_ok b hb hbase 255 0 rfl 0#64 s0 _ target_pc A b_sc
    (a_bs ++ List.replicate 8 0#8) (List.replicate 256 0#8)
    (((s0.sp - 2368#64) ↦ₛ slot16') ∗ ((s0.sp - 2096#64) ↦ₛ nb0) ∗ (a ↦ₛ a_bs) ∗ (b_sc ↦ₛ b_bs) ∗ F) post
    ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ‹_›⟩
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) hxa_len List.length_replicate ?_)
  intro s1 hr1
  rcases hr1 with ⟨hpc, hrun, hsp, hx1, hx2, hx19, hx29, hvregs, hcl1⟩
  haveI : HasLenGe (a_bs ++ List.replicate 8 0#8) 40 := ⟨by omega⟩
  wp_cut_codeLoaded hcl1
  wp_sym_steps 17
  wp_conv_pre => rw [write64_zero_32_eq_replicate nb0 hnb0, write64_pad40_eq (a_bs ++ List.replicate 8 0#8) b_bs hxa_len hb_len]
  close_cut_codeLoaded
  have hxb_len : (b_bs ++ List.replicate 8 0#8).length = 40 := by simp [hb_len]
  refine sepWP_congr_pre (naf8_loop_ok b hb hbase 255 0 rfl 0#64 s0 _ target_pc A b_sc
    (b_bs ++ List.replicate 8 0#8) (List.replicate 256 0#8)
    (((s0.sp - 2368#64) ↦ₛ slot16') ∗ ((s0.sp - 2352#64) ↦ₛ naf_a) ∗ (a ↦ₛ a_bs) ∗ (b_sc ↦ₛ b_bs) ∗ F) post
    ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ‹_›⟩
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) hxb_len List.length_replicate ?_)
  intro s2 hr2
  rcases hr2 with ⟨hpc, hrun, hsp, hx1, hx2, hx19, hx29, hvregs, hcl2⟩
  wp_sym_steps 3
  obtain ⟨hna_l, hna_v⟩ := naf5Loop_length_valid (a_bs ++ List.replicate 8 0#8) 256 0 (by decide) 0#64 (Or.inl rfl)
    (List.replicate 256 0#8) List.length_replicate (fun i hi => by simp only [ByteSlice.getD_replicate', hi, ↓ite_true]; decide)
  obtain ⟨hnb_l, hnb_v⟩ := naf8Loop_length_valid (b_bs ++ List.replicate 8 0#8) 256 0 (by decide) 0#64
    (List.replicate 256 0#8) List.length_replicate (fun i hi => by simp only [ByteSlice.getD_replicate', hi, ↓ite_true]; decide)
  refine sepWP_congr_pre (find_max_naf_loop_ok b hb hbase naf_a naf_b hna_l hnb_l 255 (by decide) s0 _ target_pc A b_sc
    (((s0.sp - 2368#64) ↦ₛ slot16') ∗ ((s0.sp - 1840#64) ↦ₛ (b_bs ++ List.replicate 8 0#8)) ∗ (a ↦ₛ a_bs) ∗ (b_sc ↦ₛ b_bs) ∗ F) post
    ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) ?_)
  intro s3 hr3 hx20
  exact sepWP_congr_pre (hnext s3 hr3 hx20 hna_l hna_v hnb_l hnb_v)

private theorem sepWP_merge_stack_40_1240 (sp : BitVec 64) {b0 b1 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 1840#64) ↦ₛ b0) ∗ ((sp - 1800#64) ↦ₛ b1)) ∗ R := by sep_frame)
    (h0 : b0.length = 40 := by assumption) (h1 : b1.length = 1240 := by assumption)
    (hnext : ∀ b1280 : List (BitVec 8), b1280.length = 1280 →
      SepWP prog target_pc s (((sp - 1840#64) ↦ₛ b1280) ∗ R) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha0 : sp - 1840#64 + BitVec.ofNat 64 b0.length = sp - 1800#64 := by rw [h0]; exact sub_ofNat64_add sp 1840 40
  have hm : ((sp - 1840#64) ↦ₛ (b0 ++ b1)) = ((sp - 1840#64) ↦ₛ b0) ∗ ((sp - 1800#64) ↦ₛ b1) := by
    rw [pointsToBytes_append, ha0]
  rw [hf, ← hm]; exact hnext (b0 ++ b1) (by simp [List.length_append, h0, h1])

set_option maxHeartbeats 800000 in
private theorem dsmb_table_and_init_ok [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl17 b) (_hbase : dalekCliPl17.base = b)
    (hNafFrom : NafLookupTable5FromOk)
    (s0 s : State) (target_pc A b_sc : BitVec 64) (max_i : Nat)
    (naf_a naf_b sc40 tab_rest p_init c_init ext_init A_bs : List (BitVec 8))
    (F : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : s0.spAligned = true)
    (hregs : NafLoopRegs s0 s A b_sc (b + 428#64))
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 max_i)
    (hsc40 : sc40.length = 40) (htab_rest : tab_rest.length = 1240)
    (hp_init : p_init.length = 120) (_hc_init : c_init.length = 160) (_hext_init : ext_init.length = 160)
    (hA_b : fe51Point4Bounded A_bs (2 ^ 52))
    (hnext : ∀ (s' : State) (tab_bs p_bs : List (BitVec 8)),
      StrausLoopRegs s0 s' max_i (b + 528#64) →
      fe51NafTable5Bounded tab_bs (2 ^ 53) →
      (∀ j < 8, edExtOfBytes (ProofLib.ByteSlice.slice tab_bs (160 * j) 160) = nafTable5Points (edExtOfBytes A_bs) j) →
      fe51Point3Bounded p_bs (2 ^ 52) →
      edProjOfBytes p_bs = ⟨0, 1, 1, 0⟩ →
      SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s'
        (strausLoopPre s0.sp naf_a naf_b tab_bs p_bs c_init ext_init
          ((fe51_one dalekCliMpl ↦ᵣ fe51OneBytes) ∗
           (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes) ∗
           (A ↦ₛ A_bs) ∗ F)) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s
      (memRegion (s0.sp - 2368#64 - 2640#64) 2640 ∗
       (odd_multiples_basepoint dalekCliMpl ↦ᵣ oddMultiplesBasepointBytes) ∗
       (fe51_one dalekCliMpl ↦ᵣ fe51OneBytes) ∗
       (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes) ∗
       (A ↦ₛ A_bs) ∗ ((s0.sp - 2352#64) ↦ₛ naf_a) ∗ ((s0.sp - 2096#64) ↦ₛ naf_b) ∗
       ((s0.sp - 1840#64) ↦ₛ sc40) ∗ ((s0.sp - 1800#64) ↦ₛ tab_rest) ∗
       ((s0.sp - 560#64) ↦ₛ p_init) ∗ ((s0.sp - 432#64) ↦ₛ c_init) ∗
       ((s0.sp - 272#64) ↦ₛ ext_init) ∗ F) post := by
  rcases hregs with ⟨hpc, hrun, hsp, hx1, _hx2, hx19, hx29, hvregs, hcl⟩
  obtain ⟨hA_len, hA_0, hA_40, hA_80, hA_120⟩ := hA_b
  unpack_fe51_at hA_0; unpack_fe51_at hA_40; unpack_fe51_at hA_80; unpack_fe51_at hA_120
  apply sepWP_merge_stack_40_1240 s0.sp; intro tab_init htab_init
  wp_sym_steps 4
  apply sepWP_dsmb_callee_to s0.sp 2640
  wp_dalek_call17 hNafFrom; clean_sf; norm_sf 2640
  apply sepWP_dsmb_callee_from s0.sp 2640
  have htab_b : fe51NafTable5Bounded w (2 ^ 53) := ‹_›
  have htab_v : ∀ j < 8, edExtOfBytes (ProofLib.ByteSlice.slice w (160 * j) 160) =
      nafTable5Points (edExtOfBytes A_bs) j := ‹_›
  haveI : HasLenGe p_init 120 := ⟨by omega⟩; haveI : HasLenGe fe51OneBytes 40 := ⟨by decide⟩
  wp_cut_codeLoaded
  wp_sym_steps 21
  apply sepWP_abstract_bytes (s0.sp - 560#64)
    (Q := fun bs => fe51Point3Bounded bs (2 ^ 52) ∧ edProjOfBytes bs = ⟨0, 1, 1, 0⟩)
    (hQ := dsmb_init_proj_post p_init hp_init)
  intro p_bs ⟨hp_b, hp_v⟩
  close_cut_codeLoaded
  apply sepWP_fold_strausLoopPre s0.sp
  have hF_eq : ((A ↦ₛ A_bs) ∗ (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes) ∗
      (fe51_one dalekCliMpl ↦ᵣ fe51OneBytes) ∗ F) =
      ((fe51_one dalekCliMpl ↦ᵣ fe51OneBytes) ∗
       (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes) ∗ (A ↦ₛ A_bs) ∗ F) := by sep_ac_rfl
  rw [hF_eq]
  exact hnext _ w p_bs
    ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ‹_›⟩
    htab_b htab_v hp_b hp_v

private theorem sepWP_split3_proj_560 (sp : BitVec 64) (P : EdExtPoint) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 560#64) ↦ₛ bs) ∗ R := by sep_frame)
    (hpt : fe51Point3Bounded bs (2 ^ 52) := by assumption) (hval : edProjOfBytes bs = P := by assumption)
    (hnext : ∀ b0 b1 b2 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 →
      fe51LimbsBounded b0 (2 ^ 54) → fe51LimbsBounded b1 (2 ^ 54) → fe51LimbsBounded b2 (2 ^ 54) →
      fe51ValOfBytes b0 % p25519 = P.X → fe51ValOfBytes b1 % p25519 = P.Y → fe51ValOfBytes b2 % p25519 = P.Z →
      SepWP prog target_pc s ((((sp - 560#64) ↦ₛ b0) ∗ ((sp - 520#64) ↦ₛ b1) ∗ ((sp - 480#64) ↦ₛ b2)) ∗ R) post oom) :
    SepWP prog target_pc s Full post oom := by
  obtain ⟨hbs, h0, h40, h80⟩ := hpt
  haveI : HasLenGe bs 120 := ⟨by omega⟩
  have hb0 := fe51LimbsBounded_slice_of_at (2 ^ 54) h0
  have hb1 := fe51LimbsBounded_slice_of_at (2 ^ 54) h40
  have hb2 := fe51LimbsBounded_slice_of_at (2 ^ 54) h80
  have hs0 : ((sp - 560#64) ↦ₛ bs) = ((sp - 560#64) ↦ₛ ProofLib.ByteSlice.slice bs 0 40) ∗ ((sp - 520#64) ↦ₛ bs.drop 40) := by
    have hs0_sl : bs.take 40 = ProofLib.ByteSlice.slice bs 0 40 := by simp [ProofLib.ByteSlice.slice]
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide), sub_ofNat64_add sp 560 40, hs0_sl]
  have hs1 : ((sp - 520#64) ↦ₛ bs.drop 40) =
      ((sp - 520#64) ↦ₛ ProofLib.ByteSlice.slice bs 40 40) ∗ ((sp - 480#64) ↦ₛ ProofLib.ByteSlice.slice bs 80 40) := by
    have hd1 : (bs.drop 40).length = 80 := by simp [hbs]
    have hs1_sl : (bs.drop 40).take 40 = ProofLib.ByteSlice.slice bs 40 40 := by rw [ProofLib.ByteSlice.slice]
    have hd2 : (bs.drop 40).drop 40 = ProofLib.ByteSlice.slice bs 80 40 := by
      rw [List.drop_drop, show 40 + 40 = 80 by decide, ProofLib.ByteSlice.slice, List.take_of_length_le (by simp [hbs])]
    conv => lhs; rw [← List.take_append_drop 40 (bs.drop 40)]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide), sub_ofNat64_add sp 520 40, hs1_sl, hd2]
  rw [hf, hs0, hs1]
  have hv : edProjOfBytes bs = ⟨fe51ValAt bs 0 % p25519, fe51ValAt bs 40 % p25519, fe51ValAt bs 80 % p25519, 0⟩ := rfl
  rw [hval] at hv
  exact hnext _ _ _ hb0.1 hb1.1 hb2.1 hb0 hb1 hb2
    (by rw [fe51ValOfBytes_slice]; exact (congrArg EdExtPoint.X hv).symm)
    (by rw [fe51ValOfBytes_slice]; exact (congrArg EdExtPoint.Y hv).symm)
    (by rw [fe51ValOfBytes_slice]; exact (congrArg EdExtPoint.Z hv).symm)

private theorem sepWP_merge3_proj_560 (sp : BitVec 64) {b0 b1 b2 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 560#64) ↦ₛ b0) ∗ ((sp - 520#64) ↦ₛ b1) ∗ ((sp - 480#64) ↦ₛ b2)) ∗ R := by sep_frame)
    (h0 : b0.length = 40 := by assumption) (h1 : b1.length = 40 := by assumption) (h2 : b2.length = 40 := by assumption)
    (hnext : ∀ b120 : List (BitVec 8), b120.length = 120 →
      SepWP prog target_pc s (((sp - 560#64) ↦ₛ b120) ∗ R) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha1 : sp - 520#64 + BitVec.ofNat 64 b1.length = sp - 480#64 := by rw [h1]; exact sub_ofNat64_add sp 520 40
  have ha0 : sp - 560#64 + BitVec.ofNat 64 b0.length = sp - 520#64 := by rw [h0]; exact sub_ofNat64_add sp 560 40
  have hm : ((sp - 560#64) ↦ₛ (b0 ++ (b1 ++ b2))) = ((sp - 560#64) ↦ₛ b0) ∗ ((sp - 520#64) ↦ₛ b1) ∗ ((sp - 480#64) ↦ₛ b2) := by
    rw [pointsToBytes_append, ha0, pointsToBytes_append, ha1]
  rw [hf, ← hm]; exact hnext (b0 ++ (b1 ++ b2)) (by simp [List.length_append, h0, h1, h2])

set_option maxHeartbeats 800000 in
private theorem dsmb_as_extended_ok [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl17 b) (_hbase : dalekCliPl17.base = b)
    (hMul : Fe51MulOk) (hPow2k : Fe51Pow2kOk)
    (s0 s : State) (target_pc out : BitVec 64) (P : EdExtPoint)
    (slot16 p_bs out_bs : List (BitVec 8)) (F : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : s0.spAligned = true)
    (hregs : StrausLoopRegs s0 s 0 (b + 1128#64))
    (hslot16 : slot16.length = 16) (hout_slot : ByteSlice.readLE slot16 8 8 = out)
    (hp_b : fe51Point3Bounded p_bs (2 ^ 52)) (hp_v : edProjOfBytes p_bs = P)
    (hout_len : out_bs.length = 160)
    (hnext : ∀ (s' : State) (p_bs' res_bs : List (BitVec 8)),
      s'.pc = b + 1200#64 → s'.status = .Running → s'.sp = s0.sp - 2368#64 →
      s'.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs s' = calleeSavedVRegs s0 →
      dalekCliMultiLib.CodeLoaded dalekCliMpl s'.mem →
      p_bs'.length = 120 → fe51Point4Bounded res_bs (2 ^ 52) →
      edExtOfBytes res_bs = edProjectiveToExtended P →
      SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s'
        (memRegion (s0.sp - 2368#64 - 2640#64) 2640 ∗
         ((s0.sp - 2368#64) ↦ₛ slot16) ∗ ((s0.sp - 560#64) ↦ₛ p_bs') ∗
         (out ↦ₛ res_bs) ∗ F) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s
      (memRegion (s0.sp - 2368#64 - 2640#64) 2640 ∗
       ((s0.sp - 2368#64) ↦ₛ slot16) ∗ ((s0.sp - 560#64) ↦ₛ p_bs) ∗
       (out ↦ₛ out_bs) ∗ F) post := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
  haveI : HasLenGe slot16 16 := ⟨by omega⟩
  apply sepWP_split3_proj_560 s0.sp P
  intro p0 p1 p2 hp0_l hp1_l hp2_l hp0_b hp1_b hp2_b hp0_v hp1_v hp2_v
  unpack_fe51 hp0_b; unpack_fe51 hp1_b; unpack_fe51 hp2_b
  apply sepWP_split4_160 out; intro o0 o1 o2 o3 ho0 ho1 ho2 ho3
  wp_sym_steps 6
  apply sepWP_dsmb_callee_to s0.sp 224
  wp_dalek_call17 hMul; clean_sf; norm_sf 224
  have hb_w0 : fe51LimbsBounded w (2 ^ 52) := ‹_›
  have hp_w0 : fe51ValOfBytes w % p25519 = (fe51ValOfBytes p0 * fe51ValOfBytes p2) % p25519 := ‹_›
  wp_sym_steps 4; wp_dalek_call17 hMul; clean_sf; norm_sf 224
  have hb_w1 : fe51LimbsBounded w_1 (2 ^ 52) := ‹_›
  have hp_w1 : fe51ValOfBytes w_1 % p25519 = (fe51ValOfBytes p1 * fe51ValOfBytes p2) % p25519 := ‹_›
  apply sepWP_dsmb_callee_from s0.sp 224
  wp_sym_steps 4; apply sepWP_dsmb_callee_to s0.sp 96
  wp_dalek_call17 hPow2k; clean_sf; norm_sf 96; apply sepWP_dsmb_callee_from s0.sp 96
  have hb_w2 : fe51LimbsBounded w_2 (2 ^ 52) := ‹_›
  have hp_w2 : fe51ValOfBytes w_2 % p25519 = fpPow (fe51ValOfBytes p2 % p25519) (2 ^ (1#32).toNat) := ‹_›
  wp_sym_steps 4; apply sepWP_dsmb_callee_to s0.sp 224
  wp_dalek_call17 hMul; clean_sf; norm_sf 224; apply sepWP_dsmb_callee_from s0.sp 224
  have hb_w3 : fe51LimbsBounded w_3 (2 ^ 52) := ‹_›
  have hp_w3 : fe51ValOfBytes w_3 % p25519 = (fe51ValOfBytes p0 * fe51ValOfBytes p1) % p25519 := ‹_›
  apply sepWP_merge3_proj_560 s0.sp; intro p_bs' hp'_l
  have hv0 : fe51ValOfBytes w % p25519 = fpMul P.X P.Z := by unfold fpMul; rw [hp_w0, Nat.mul_mod, hp0_v, hp2_v, ← Nat.mul_mod]
  have hv1 : fe51ValOfBytes w_1 % p25519 = fpMul P.Y P.Z := by unfold fpMul; rw [hp_w1, Nat.mul_mod, hp1_v, hp2_v, ← Nat.mul_mod]
  have hv2 : fe51ValOfBytes w_2 % p25519 = fpMul P.Z P.Z := by rw [hp_w2, hp2_v]; exact fpPow_two_eq_fpSq P.Z
  have hv3 : fe51ValOfBytes w_3 % p25519 = fpMul P.X P.Y := by unfold fpMul; rw [hp_w3, Nat.mul_mod, hp0_v, hp1_v, ← Nat.mul_mod]
  have hQ : fe51Point4Bounded (w ++ (w_1 ++ (w_2 ++ w_3))) (2 ^ 52) ∧
      edExtOfBytes (w ++ (w_1 ++ (w_2 ++ w_3))) = edProjectiveToExtended P := by
    obtain ⟨hl, hb0', hb1', hb2', hb3', hv⟩ :=
      edAsExtended_of_append4 w w_1 w_2 w_3 ⟨P.X, P.Y, P.Z, P.Z⟩
        hb_w0 hb_w1 hb_w2 hb_w3 hv0 hv1 hv2 hv3
    refine ⟨⟨hl, hb0', hb1', hb2', hb3'⟩, hv.trans ?_⟩
    unfold edAsExtended edProjectiveToExtended
    rw [fpPow_two_eq_fpSq]; rfl
  apply sepWP_merge4_160 out
    (Q := fun res => fe51Point4Bounded res (2 ^ 52) ∧ edExtOfBytes res = edProjectiveToExtended P)
    (h0 := hb_w0.1) (h1 := hb_w1.1) (h2 := hb_w2.1) (hQ := hQ)
  intro res_bs ⟨hres_b, hres_v⟩
  exact sepWP_congr_pre (hnext _ p_bs' res_bs
    ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› hp'_l hres_b hres_v)

private theorem findMaxNafIdx_le' (naf_a naf_b : List (BitVec 8)) :
    ∀ i : Nat, findMaxNafIdx naf_a naf_b i ≤ i
  | 0 => Nat.le_refl 0
  | k + 1 => by
    unfold findMaxNafIdx; split
    · split
      · exact Nat.le_trans (findMaxNafIdx_le' naf_a naf_b k) (Nat.le_succ k)
      · exact Nat.le_refl (k + 1)
    · exact Nat.le_refl (k + 1)

public section

set_option maxHeartbeats 800000 in
theorem vartime_double_scalar_mul_basepoint_ok_of
    (hMul : Fe51MulOk) (_hMulRo : Fe51MulRoRightOk) (hPow2k : Fe51Pow2kOk)
    (hDbl : ProjectivePointDoubleOk)
    (hAddPN : EdwardsPointAddProjNielsOk) (hSubPN : EdwardsPointSubProjNielsOk)
    (hAddANRo : EdwardsPointAddAffineNielsRoOk) (hSubANRo : EdwardsPointSubAffineNielsRoOk)
    (hNafFrom : NafLookupTable5FromOk) :
    VartimeDoubleScalarMulBasepointOk := by
  intro _
  apply dalekCaller_ok dalekCliPC17 dalekCliPl17 dalekCliPl17_eq dalekCliPC17_block_eq
  intro b hb hbase
  wp_init
  apply sepWP_split_stack_callee 2640 2368
  apply sepWP_peel_stack_bytes s0.sp 2368 16 2352; intro slot16 hslot16
  apply sepWP_peel_stack_bytes s0.sp 2352 256 2096; intro na0 hna0
  apply sepWP_peel_stack_bytes s0.sp 2096 256 1840; intro nb0 hnb0
  apply sepWP_peel_stack_bytes s0.sp 1840 40 1800; intro sc40 hsc40
  apply sepWP_peel_stack_bytes s0.sp 1800 1240 560; intro tab_rest htab_rest
  apply sepWP_peel_stack_bytes s0.sp 560 120 440; intro p_init hp_init
  apply sepWP_peel_stack_bytes s0.sp 440 8 432; intro pad8 hpad8
  apply sepWP_peel_stack_bytes s0.sp 432 160 272; intro c_init hc_init
  apply sepWP_peel_stack_bytes s0.sp 272 160 112; intro ext_init hext_init
  apply sepWP_peel_stack_bytes s0.sp 112 16 96; intro pad16 hpad16
  open_cells (s0.sp - 96#64) 96 12
  wp_cut_codeLoaded
  wp_sym_steps 8
  close_cut_codeLoaded
  have hout_len : a_4.length = 160 := ‹_›
  have ha_len : a_5.length = 32 := ‹_›
  have hA_b : fe51Point4Bounded a_6 (2 ^ 52) := ‹_›
  have hb_len : a_rest.length = 32 := ‹_›
  let cs_cells : SepProp :=
    ((s0.sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
    ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
    ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
    ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
    ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5))
  let F_setup : SepProp :=
    memRegion (s0.sp - 2368#64 - 2640#64) 2640 ∗
    (odd_multiples_basepoint dalekCliMpl ↦ᵣ oddMultiplesBasepointBytes) ∗
    (fe51_one dalekCliMpl ↦ᵣ fe51OneBytes) ∗
    (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes) ∗
    (a_2 ↦ₛ a_6) ∗ (a_1 ↦ₛ a_4) ∗
    ((s0.sp - 1800#64) ↦ₛ tab_rest) ∗ ((s0.sp - 560#64) ↦ₛ p_init) ∗
    ((s0.sp - 440#64) ↦ₛ pad8) ∗ ((s0.sp - 432#64) ↦ₛ c_init) ∗
    ((s0.sp - 272#64) ↦ₛ ext_init) ∗ ((s0.sp - 112#64) ↦ₛ pad16) ∗ cs_cells
  refine sepWP_congr_pre (dsmb_naf_setup_ok b hb hbase s0 _ _ a_1 a a_2 a_3
    slot16 na0 nb0 sc40 a_5 a_rest F_setup _ hsp_align
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) rfl ‹_› hslot16 hna0 hnb0 hsc40 ha_len hb_len ?_)
  intro s1 naf_a naf_b hr1 hx20 hna_len hna_val hnb_len hnb_val
  let slot16' := ByteSlice.write64 (ByteSlice.write64 slot16 0 0#64) 8 a_1
  let max_i := findMaxNafIdx naf_a naf_b 255
  have hxb_len : (a_rest ++ List.replicate 8 0#8).length = 40 := by simp [hb_len]
  let F_init : SepProp :=
    ((s0.sp - 2368#64) ↦ₛ slot16') ∗ (a ↦ₛ a_5) ∗ (a_3 ↦ₛ a_rest) ∗ (a_1 ↦ₛ a_4) ∗
    ((s0.sp - 440#64) ↦ₛ pad8) ∗ ((s0.sp - 112#64) ↦ₛ pad16) ∗ cs_cells
  refine sepWP_congr_pre (dsmb_table_and_init_ok b hb hbase hNafFrom s0 s1 _ a_2 a_3 max_i
    naf_a naf_b (a_rest ++ List.replicate 8 0#8) tab_rest p_init c_init ext_init a_6 F_init _
    hsp_align hr1 hx20 hxb_len htab_rest hp_init hc_init hext_init hA_b ?_)
  intro s2 tab_bs p_bs hr2 htab_b htab_v hp_b hp_v
  have hmax_lt : max_i < 256 := Nat.lt_succ_of_le (findMaxNafIdx_le' naf_a naf_b 255)
  apply straus_loop_ok b hb hbase hDbl hMul hAddPN hSubPN hAddANRo hSubANRo
    max_i hmax_lt s0 s2 _ naf_a naf_b tab_bs p_bs c_init ext_init
    ⟨0, 1, 1, 0⟩ (nafTable5Points (edExtOfBytes a_6)) _ _
    hsp_align hr2 hna_len hna_val hnb_len hnb_val htab_b htab_v hp_b hp_v hc_init hext_init
  intro s3 p_bs' c_bs' ext_bs' hr3 hp'_b hp'_v hc'_len hext'_len
  unfold strausLoopPre; dsimp only [F_init]
  haveI : HasLenGe slot16 16 := ⟨by omega⟩
  have hslot16' : slot16'.length = 16 := by simp only [slot16', write64_length_eq, hslot16]; decide
  haveI : HasLenGe (ByteSlice.write64 slot16 0 0#64) 16 := ⟨by simp only [write64_length_eq, hslot16]; decide⟩
  have hout_slot : ByteSlice.readLE slot16' 8 8 = a_1 := readLE_write64_self' _ 8 16 a_1 (by decide)
  clear hr1 hr2
  clear_dead_vars [s1, s2]
  try clear s1 s2
  let F_ext : SepProp :=
    (odd_multiples_basepoint dalekCliMpl ↦ᵣ oddMultiplesBasepointBytes) ∗
    ((s0.sp - 2352#64) ↦ₛ naf_a) ∗ ((s0.sp - 2096#64) ↦ₛ naf_b) ∗ ((s0.sp - 1840#64) ↦ₛ tab_bs) ∗
    ((s0.sp - 432#64) ↦ₛ c_bs') ∗ ((s0.sp - 272#64) ↦ₛ ext_bs') ∗
    (fe51_one dalekCliMpl ↦ᵣ fe51OneBytes) ∗
    (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes) ∗
    (a_2 ↦ₛ a_6) ∗ (a ↦ₛ a_5) ∗ (a_3 ↦ₛ a_rest) ∗
    ((s0.sp - 440#64) ↦ₛ pad8) ∗ ((s0.sp - 112#64) ↦ₛ pad16) ∗ cs_cells
  refine sepWP_congr_pre (dsmb_as_extended_ok b hb hbase hMul hPow2k s0 s3 _ a_1
    (edStrausLoop naf_a naf_b (nafTable5Points (edExtOfBytes a_6)) max_i ⟨0, 1, 1, 0⟩)
    slot16' p_bs' a_4 F_ext _ hsp_align hr3 hslot16' hout_slot hp'_b hp'_v hout_len ?_)
  intro s4 p_bs'' res_bs hpc4 hrun4 hsp4 hx29_4 hvregs4 _hcl4 hp''_len hres_b hres_v
  dsimp only [F_ext, cs_cells]
  wp_steps
  close_cells (s0.sp - 96#64) 96 12
  apply sepWP_unpeel_stack_bytes s0.sp 112 16 96 (hbs := hpad16)
  apply sepWP_unpeel_stack_bytes s0.sp 272 160 112 (hbs := hext'_len)
  apply sepWP_unpeel_stack_bytes s0.sp 432 160 272 (hbs := hc'_len)
  apply sepWP_unpeel_stack_bytes s0.sp 440 8 432 (hbs := hpad8)
  apply sepWP_unpeel_stack_bytes s0.sp 560 120 440 (hbs := hp''_len)
  apply sepWP_unpeel_stack_bytes s0.sp 1840 1280 560 (hbs := htab_b.1)
  apply sepWP_unpeel_stack_bytes s0.sp 2096 256 1840 (hbs := hnb_len)
  apply sepWP_unpeel_stack_bytes s0.sp 2352 256 2096 (hbs := hna_len)
  apply sepWP_unpeel_stack_bytes s0.sp 2368 16 2352 (hbs := hslot16')
  apply sepWP_merge_stack_callee 2640 2368
  have hres_eq : edExtOfBytes res_bs = edDoubleScalarMulBasepoint a_5 a_6 a_rest := hres_v
  obtain ⟨hres_len, hw0', hw40', hw80', hw120'⟩ := hres_b
  unpack_fe51_at hw0'; unpack_fe51_at hw40'; unpack_fe51_at hw80'; unpack_fe51_at hw120'
  wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DoubleScalarMul

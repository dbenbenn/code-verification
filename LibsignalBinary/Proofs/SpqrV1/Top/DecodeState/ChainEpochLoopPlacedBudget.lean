/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudgetAux2
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainEpochPB` Merge Loop

Budget-threaded relocatable `[LibsignalPlacement]` proofs of the inductive `ChainEpochPB` merge loop
(`+984`) and length-delimited entry (`+600`), re-exporting dispatch and body helpers.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join suffix_trans)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Prost.MessageMerge (mergeLoopBin protoPrefixStep_chainEpochPB_mergeField)
open CryptoVerification.LibsignalSpqrV1 (ChainEpochPB PqRatchetState spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred bv_len_sub_limit chainEpochPBCapOkAt chainEpochPBCapOkAt_eq_placed chainEpochPBCapOkAt_mono cmp_len_limit_bne_of_lt cmp_len_limit_of_eq cmp_len_limit_of_gt cmp_len_limit_of_lt decodeStatePlacedEntry decodeStatePlacedProg len_ult_of_ge len_ult_of_lt mergeLoopBin_eq_limit mergeLoopBin_lt_limit mergeMessage_toOption_of_decodeVarint_none mergeMessage_toOption_of_ge mergeMessage_toOption_of_lt optEpochDirectionPBCapOkAt protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_mono sp_sub_1392_aligned suffix_eq_drop_of_len_eq truncate32_zeroExtend64_lsr3)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv FitsEnv.decodeStateLoop_mono FitsEnv.decodeStateLoop_tail)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux (fitsEnv_decodeErrorFrom_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget (decodeStateEpochErrFramePlaced decodeStateEpochErrTailFramePlaced decodeStateEnv_of_loop_epochDrop_push2_free decodeStateEnv_of_loop_from_epochDrop_push2_free fitsEnv_epochDrop_push1_of_loop fitsEnv_epochDrop_push2_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced SepWPpIPlaced.call_decodeVarint2 decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget (epochLoop_cursor_to_epochErrFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux (after_decodeVarint2_err_to_epochErrFrame_placed decodeVarint2Env_eq_nil_of_some fitsEnv_decodeVarint2_of_loop fitsEnv_from_epochDrop_push1_of_loop fitsEnv_from_epochDrop_push2_of_loop lift_postEnv stepEvents_nil_of_acc)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux (lift_postEnv stepEvents_nil_of_acc decodeVarint2Env_eq_nil_of_some fitsEnv_decodeVarint2_of_loop fitsEnv_from_epochDrop_push1_of_loop)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux (fitsEnv_from_epochDrop_push2_of_loop after_decodeVarint2_to_epochErrFrame_placed after_decodeVarint2_err_to_epochErrFrame_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] truncate32_zeroExtend64_lsr3

local macro "pool_reg_norm" : tactic =>
  `(tactic| try simp only [RustCliAllocBudget.pool_setPC_norm,
    RustCliAllocBudget.pool_advancePC_norm, RustCliAllocBudget.pool_setPState_norm,
    RustCliAllocBudget.pool_writeReg64_norm, RustCliAllocBudget.pool_writeReg32_norm,
    RustCliAllocBudget.pool_writeReg_norm, RustCliAllocBudget.pool_writeVReg128_norm,
    RustCliAllocBudget.pool_writeVReg64_norm])

/-! ## Full `ChainEpochPB` Merge Loop (`+984`) -/

/-! ## Delimited `ChainEpochPB::merge` Entry (`+600`) -/

private theorem epoch_scratch_split_recv_240 (sp : BitVec 64) :
    memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ⊢
      ∃∗ w_recv : BitVec 64,
        memRegion (sp - 680#64) 48 ∗
        ((sp - 632#64) ↦₆₄ w_recv) ∗
        memRegion (sp - 624#64) 48 ∗
        memRegion (sp - 576#64) 240 := by
  have hs1 := ProofLib.memRegion_split' (b := sp - 640#64) (n := 8) (k := 296)
    (b' := sp - 632#64) rfl (by bv_omega) (by decide)
  have hs2 := ProofLib.memRegion_split' (b := sp - 632#64) (n := 8) (k := 288)
    (b' := sp - 624#64) rfl (by bv_omega) (by decide)
  have hs3 := ProofLib.memRegion_split' (b := sp - 624#64) (n := 48) (k := 240)
    (b' := sp - 576#64) rfl (by bv_omega) (by decide)
  have hj := ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 8)
    (b' := sp - 640#64) rfl (by bv_omega) (by decide)
  rw [hs1, hs2, hs3, ProofLib.memRegion_eight (sp - 632#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w_recv
  refine Entails.sepExists_right w_recv ?_
  rw [hj]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem chainEpochPBCapOkAt_default_init (A : CryptoVerification.RustHeap.RustAlloc)
    (sp : BitVec 64) (remLen : Nat) :
    ((sp - 688#64) ↦₆₄ -1#64) ∗ memRegion (sp - 680#64) 48 ∗
      ((sp - 632#64) ↦₆₄ -1#64) ∗ memRegion (sp - 624#64) 48 ⊢
      chainEpochPBCapOkAt A (sp - 688#64) remLen default := by
  rw [show (default : ChainEpochPB) = { send := none, recv := none } from rfl,
    chainEpochPBCapOkAt_eq_placed]
  unfold optEpochDirectionPBCapOkAt
  dsimp only
  have ha1 : sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega
  have ha2 : sp - 632#64 + 8#64 = sp - 624#64 := by bv_omega
  have hnc : (-1#64 : BitVec 64) = noneCap := rfl
  rw [ha1, ha2, hnc]
  exact Entails.of_eq (by sep_ac_rfl)

attribute [local irreducible] mergeMessage mergeLoopBin
  CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudget

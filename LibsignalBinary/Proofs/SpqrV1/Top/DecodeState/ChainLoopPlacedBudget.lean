/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudgetAux1
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainPB` Merge Loop & Tag-2 Handler

Budget-threaded relocatable `[LibsignalPlacement]` proofs of the inductive `ChainPB` merge loop (`+508`),
length-delimited entry (`+284`), and outer tag-2 handler (`+244`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc vecAt vecBuf vecHeader vecOf)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join suffix_trans)
open CryptoVerification.SpqrV1.ProtoRepr (chainEpochPBAt chainEpochPBSize chainLinksVecAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto mergeLoopBin protoPrefixStep_chainPB_mergeField)
open CryptoVerification.LibsignalSpqrV1 (ChainEpochPB ChainPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred bv_len_sub_limit cap_add_one_beq_zero_false chainPBCapOkAt_default_init cmp_len_limit_bne_of_lt cmp_len_limit_of_eq cmp_len_limit_of_gt cmp_len_limit_of_lt decodeStatePlacedEntry decodeStatePlacedProg errFrame_parts_fold len_ult_of_ge len_ult_of_lt memRegion_56_eq_quads7At mergeLoopBin_eq_limit mergeLoopBin_lt_limit mergeMessage_toOption_of_decodeVarint_none mergeMessage_toOption_of_ge mergeMessage_toOption_of_lt mergeMessage_toOption_of_ne_lengthDelimited optChainPBCapOkAt protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt protoPqRatchetStateCapOkAt_mono quads7At sp_sub_1392_aligned suffix_eq_drop_of_len_eq truncate32_zeroExtend64_lsr3 wt64_ne_two_of_ne_lengthDelimited)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced decodeStateLoopCommonPlaced loopCommon_cursor_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudget (protoPqRatchetStateCapOkAt_some_ch_eq_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux (decodeState_codecWireTypeToProto_eq err3_env err3_fits1 err3_fits2)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudgetAux (acc_henv_err decodeErrorFromEnv_iter decodeVarint2Env_eq_nil_of_some)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero truncate32_zeroExtend64_lsr3
attribute [local simp] truncate32_zeroExtend64_lsr3

/-! ## Full `ChainPB` Merge Loop (`+508`) -/

/-! ## Outer Loop Tag-2 (`PqRatchetState::chain`, `+284` & `+244`) -/

private theorem optChainPB_none_split72 (a : BitVec 64) :
    memRegion (a + 8#64) 72 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 32, ∃∗ w9 : BitVec 32,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
        ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₃₂ w8) ∗
        memRegion (a + 68#64) 8 ∗ ((a + 76#64) ↦₃₂ w9) := by
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 56) (k := 16)
      (b' := a + 64#64) rfl (by bv_omega) (by decide),
    memRegion_56_eq_quads7At (a + 8#64),
    ProofLib.memRegion_split' (b := a + 64#64) (n := 4) (k := 12)
      (b' := a + 68#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 68#64) (n := 8) (k := 4)
      (b' := a + 76#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_four (a + 64#64),
    ProofLib.memRegion_four (a + 76#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w9
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; rintro ⟨w1, w2, w3, w4, w5, w6, w7⟩
  dsimp only [quads7At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right w6
        (Entails.sepExists_right w7 (Entails.sepExists_right w8
          (Entails.sepExists_right w9 ?_))))))))
  exact Entails.of_eq (by sep_ac_rfl)

private theorem chainLinksVecAt_cap_lt (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List ChainEpochPB) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs := by
  unfold vecBuf
  apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
  exact Entails.pure_right (by omega) (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))

private theorem chainLinksVecAt_header_fold (A : RustAlloc) (a cap ptr : BitVec 64)
    (xs : List ChainEpochPB) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
    chainLinksVecAt A a xs := by
  unfold chainLinksVecAt chainEpochPBSize vecOf vecAt vecHeader
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by sep_ac_rfl)

attribute [local irreducible]
  mergeMessage mergeLoopBin CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudget

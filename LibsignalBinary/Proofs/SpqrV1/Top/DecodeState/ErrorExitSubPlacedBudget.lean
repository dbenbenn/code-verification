/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DefsPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub
public meta import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable Outer Loop & `ChainPB` Error Exit Paths for `spqr::decode_state` (Block `325`)

Re-exports `ErrorExitSubPlacedBudgetAux` and proves the remaining budget-threaded relocatable
`ChainPB` error-exit paths (`+1596`, `+1776..+1824`, `+2092..+2108`, `+2660..+2868`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg decodeStateSavedAt protoPqRatchetStateAt sp_sub_1392_aligned)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (bv_sub_688_add_8 decodeStateErrFramePlaced scratch_680_fold_1_1 scratch_680_fold_8 scratch_680_split_1_1 scratch_680_split_8)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux (SepWPp.exists_left)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux (decodeStateErrFramePlaced decodeStateIterEnv_of_decodeErrorFrom fitsEnv_decodeErrorFrom_of_loop fitsEnv_decodeErrorPush_of_loop decodeStateEnv_of_loop_from_free decodeStateEnv_of_loop_push2_free decodeStateEnv_of_loop_from_push_free decodeStateEnv_of_loop_from_push2_free)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem sepWPp_seg_325_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {mid ret pc0 : BitVec 64} {s : State} {Pre : SepProp}
    {post Qp : State → SepProp → Prop}
    (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hseg : ∀ m_strip : Memory,
      (s.setMem m_strip).pc = pc0 →
      (s.setMem m_strip).status = .Running →
      SepWP ((blkPC_325).rebase (blkPl_325).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
        mid (s.setMem m_strip) Pre (fun sm' Pm =>
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            SepWPp ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
              ret (sm'.setMem m_real) Pm post Qp)) :
    SepWPp ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext)) ret s Pre post Qp :=
  LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWPp_seg_ls_vm
    (Q := (blkPC_325).rebase (blkPl_325).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    blkLib_eq_325 (mid := mid) (hseg := fun m_strip => hseg m_strip hpc hrun)

meta section
macro "wp_steps_sync_325 " hpc:ident hrun:ident mid:term : tactic =>
  `(tactic| (
    apply sepWPp_seg_325_vm $hpc $hrun (mid := $mid)
    intro _m_strip _hpc_strip _hrun_strip
    wp_steps
    refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine ProofLib.SepWPp.transport_budgetPool
      (_hnsp.toVmPreserved (by first | rfl | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
  ))
end

/-! ## 5. Remaining `ChainPB` Error Exits (`0x53f00..0x53fd0`, `0x53ad8`, `0x53b8c..0x53bbc`, `0x53cc8..0x53cd8`) -/

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefs
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExit -- proof-setup: allow-public-import
public import Arm64.Trusted.Object.Labels
public import ProofLib.BV
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.Hoare.SubroutineHook
public import ProofLib.MallocngBridge
public import ProofLib.Placed
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.SharedCode
public import ProofLib.Process.FsLemmas
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.WP.SyscallsMmap
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.Strlen
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Spec.Cost
public import VerifiedLibraries.Musl.Spec.Top
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Spec.AllocFormatInner
public import VerifiedLibraries.RustStd.Spec.AllocFormatInnerBudget
public import VerifiedLibraries.RustStd.Spec.AllocStringClone
public import VerifiedLibraries.RustStd.Spec.CoreFmtDisplay
public import VerifiedLibraries.RustStd.Spec.CoreFmtWrite
public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import VerifiedLibraries.RustStd.Spec.CoreMemrchr
public import VerifiedLibraries.RustStd.Spec.FsRead
public import VerifiedLibraries.RustStd.Spec.FsWrite
public import VerifiedLibraries.RustStd.Spec.Stdio
public import VerifiedLibraries.RustStd.Spec.TimeAdd
public import VerifiedLibraries.RustStd.Spec.TimeDurationSince
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedLibcFreeStage1
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Error Precondition Frame & Scratch Helpers for `spqr::decode_state`

Re-exports `[sp + 0x2c8]` scratch-splitting lemmas and defines the budget-threaded
`decodeStateErrFrame` and relocatable `decodeStateErrFramePlaced` error precondition frames.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (v1StateJumpTablesAt v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred decodeStateSavedAt protoPqRatchetStateAt)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)

export CryptoVerification.SpqrV1.Top.DecodeState
  (bv_sub_688_add_8 scratch_680_split_8 scratch_680_fold_8 scratch_680_split_1_1 scratch_680_fold_1_1)

/-- Budget-threaded separation-logic frame for error exit blocks when `protoPqRatchetStateAt` is
intact at `s0.sp - 1040#64` and `[sp + 0x2c0]` (`s0.sp - 688#64`) is split out. -/
abbrev decodeStateErrFrame {M : AllocCostModel} (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 s : State) : SepProp :=
  v1StateJumpTablesAt b ∗
  x.st.at A.repAlloc ∗
  memRegion x.outPtr 352 ∗
  A.pool lim st s ∗
  stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
  memRegion (s0.sp - 1392#64) 352 ∗
  protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
  memRegion (s0.sp - 680#64) 40 ∗
  memRegion (s0.sp - 640#64) 304 ∗
  memRegion (s0.sp - 336#64) 240 ∗
  decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

/-- Relocatable `[LibsignalPlacement]` budget-threaded separation-logic frame for error exit blocks
when `protoPqRatchetStateAt` is intact at `s0.sp - 1040#64` and `[sp + 0x2c0]` (`s0.sp - 688#64`)
is split out. -/
abbrev decodeStateErrFramePlaced [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 s : State) : SepProp :=
  v1StateJumpTablesPlacedAt ∗
  x.st.at A.repAlloc ∗
  memRegion x.outPtr 352 ∗
  A.pool lim st s ∗
  stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
  memRegion (s0.sp - 1392#64) 352 ∗
  protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
  memRegion (s0.sp - 680#64) 40 ∗
  memRegion (s0.sp - 640#64) 304 ∗
  memRegion (s0.sp - 336#64) 240 ∗
  decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudget
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegsBudget
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Proof
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep -- proof-setup: allow-public-import
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import ProofLib.ProgramReflection.SortedFresh
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275 -- proof-setup: allow-public-import
meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275 -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
public import ProofLib.SepLogic.WPp
public import Arm64.Trusted.Object.Labels
public import ProofLib.BV
public import ProofLib.BV.MaskLemmas
public import ProofLib.BV.PolyMul
public import ProofLib.GenPlacedFetches
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.Hoare.SubroutineHook
public import ProofLib.MallocngBridge
public import ProofLib.Placed
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.Multi
public import ProofLib.Placed.SharedCode
public import ProofLib.Process.FsLemmas
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.Strlen
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Spec.Cost
public import VerifiedLibraries.Mallocng.Spec.Top
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
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux -- proof-setup: allow-public-import

/-!
# Budget-Threaded `<Ct1SentEkReceived>::send_ct2`: Fixed-Base Loops and Segment 2

Defines Segment 5b deallocation events (`sendCt2Seg5bEvents`), lifts the fixed-base
Issue-1275 loops with `VmPreserved`, and proves fixed-base Segment 2 (`+136 → +552`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2ProofBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes flipEndiannessOfEncapsulationStateBytes issue1275NeedsFlip swapAdjacentPairs
)
open CryptoVerification.SpqrV1.States.Leaves (UnchunkedSendCt2Ghost unchunkedCt1SentEkReceivedSendCt2Name)
open CryptoVerification.SpqrV1.Unchunked (
  ScanLoopSaved SwapLoopSaved es_scan_split es_swap_join es_swap_split
  issue1275NeedsFlip_cons_cont issue1275NeedsFlip_cons_false_not_be
  issue1275NeedsFlip_cons_true_be issue1275_word_eq
  pointsToBytes_pair_pointsTo16 pointsToBytes_pair_split sendCt2EsWorkAt
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)

open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  SendCt2Reserve128Env UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
  fitsEvents_flipAlloc_of_preEnv
  sendCt2ConcatHmacEvents sendCt2FlipAllocEvents sendCt2Seg23Events
  sepWPp_weaken_pre
)

open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux (
  freeOnlyEvs_rustDeallocEvents freeOnlyEvs_sendCt2MdDeallocEvents
  sendCt2MdDeallocEvents sendCt2Seg5aEvents
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setMem_setPC_pre

/-! ## Segment 5b Deallocation Events -/

/-- Deallocation events of Segment 5b (`ct1`, `es`, and `ek` heap buffers). -/
@[expose] def sendCt2Seg5bEvents (cap_ct1' esCap ekCap : BitVec 64) : List AllocEvent :=
  rustDeallocEvents cap_ct1'.toNat 1 ++
    rustDeallocEvents esCap.toNat 1 ++
    rustDeallocEvents ekCap.toNat 1

theorem freeOnlyEvs_sendCt2Seg5bEvents (cap_ct1' esCap ekCap : BitVec 64) :
    FreeOnlyEvs (sendCt2Seg5bEvents cap_ct1' esCap ekCap) :=
  FreeOnlyEvs.append
    (FreeOnlyEvs.append
      (freeOnlyEvs_rustDeallocEvents _ _)
      (freeOnlyEvs_rustDeallocEvents _ _))
    (freeOnlyEvs_rustDeallocEvents _ _)

/-- Appending `sendCt2Seg5bEvents cap_ct1' esCap ekCap` after Segments 2–5a satisfies
    `UnchunkedSendCt2PostEnv x`. -/
theorem unchunkedSendCt2PostEnv_of_seg5b {F : ShaCompress} {x : UnchunkedSendCt2Ghost F}
    {evsRes : List AllocEvent} (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes)
    (cap_ct1' esCap ekCap : BitVec 64) :
    UnchunkedSendCt2PostEnv x
      ((sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) ++
        sendCt2Seg5bEvents cap_ct1' esCap ekCap) := by
  refine ⟨sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2ConcatHmacEvents x.st.ct1.length,
    sendCt2MdDeallocEvents x.st.ct1.length ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap,
    ⟨evsRes, hRes, rfl⟩,
    FreeOnlyEvs.append
      (freeOnlyEvs_sendCt2MdDeallocEvents x.st.ct1.length)
      (freeOnlyEvs_sendCt2Seg5bEvents cap_ct1' esCap ekCap),
    ?_⟩
  unfold sendCt2Seg5aEvents
  simp only [List.append_assoc]

/-! ## Fixed-Base `swapAdjacentPairs` Loop with `VmPreserved` -/

end LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2ProofBudgetAux

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs
public import LibsignalBinary.Heap.Fine.CreditInst
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit -- proof-setup: allow-public-import
public import Arm64.Trusted.Object.Labels
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.MallocngBridge
public import ProofLib.Placed
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.SharedCode
public import ProofLib.Process.FsLemmas
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.SepLogic.WP.SyscallsMmap
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.Strlen
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

/-!
# Budget-Threaded `OutgoingTripleRatchet` Raw Apply Contract

Defines the allocation envelope `OtrApplyEnv`, the `RustCliAllocBudget` specification
`otrApplyRawSpec`, and its `PhaseCreditSpec` and `FitsEnv` non-vacuity lemmas.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv FreeOnlyEvs SeqEnv
   rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel FineStepBound)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineStepReserveOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineMaxGroupsOfCum)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open CryptoVerification.LibsignalTripleRatchet (OtrApplyGhost)

/-- Exact binary allocation envelope of
    `<OutgoingTripleRatchet>::apply_to_session_state`:
    one `32`-byte `Vec<u8>` allocation (`ChainKey::to_pb`) followed by optional
    sender-chain / PQ-ratchet buffer deallocations (`FreeOnlyEvs`). -/
@[expose] def OtrApplyEnv : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs

/-- Budget-threaded image-independent specification of
    `<OutgoingTripleRatchet>::apply_to_session_state` (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
@[expose] def otrApplyRawSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (OtrApplyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st OtrApplyEnv⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyRawSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜OtrApplyEnv evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyRawSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- `OtrApplyEnv` exercises its `32`-byte `Vec<u8>` allocation (`[.alloc 32]`). -/
theorem otrApplyEnv_alloc_mem : OtrApplyEnv (rustAllocEvents 32 1) :=
  Or.inl rfl

/-- Parametric `PhaseCreditSpec` for `OtrApplyEnv` under `ModelHyps M`. -/
theorem otrApplyEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M OtrApplyEnv 9603 8227 8227 32 := by
  have h32 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
  have hfr := PhaseCreditSpec.freeOnly_of_hyps hM
  exact (h32.seq hfr).mono (by decide) (by decide) (by decide) (by decide)

end LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget

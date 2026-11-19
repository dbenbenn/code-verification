/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Defs
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
import LibsignalBinary.Proofs.CodeLayout

/-!
# Budget-Threaded `TripleRatchet::apply_to_session_state` Specifications

Bounded allocator-event envelopes (`TrApplySenderAllocEnv`, `TrApplyEnv`), `RustCliAllocBudget`-threaded
specifications (`trApplySpec`, `trApplySpecX`), and `PhaseCreditSpec` / `FitsEnv` witnesses for
`<TripleRatchet>::apply_to_session_state`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
   SeqEnv FreeOnlyEvs rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineStepBound fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineMaxGroupsOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineStepReserveOfCum)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open CryptoVerification.LibsignalTripleRatchet (TrApplyGhost)

/-- Deterministic allocation sequence of the `senderChain.isSome` arm of
    `<TripleRatchet>::apply_to_session_state`:
    `senderRatchetKey.public` (`33` B), `senderRatchetKey.private` (`33` B),
    `senderChainKey` (`32` B), and two temporary `32` B key clones, all at `align = 1`. -/
@[expose] def TrApplySenderAllocEnv : List AllocEvent → Prop :=
  SeqEnv (fun evs => evs = rustAllocEvents 33 1)
    (SeqEnv (fun evs => evs = rustAllocEvents 33 1)
      (SeqEnv (fun evs => evs = rustAllocEvents 32 1)
        (SeqEnv (fun evs => evs = rustAllocEvents 32 1)
          (fun evs => evs = rustAllocEvents 32 1))))

/-- Bounded allocation-event envelope of `<TripleRatchet>::apply_to_session_state`:
    1. `rootKey` clone (`rustAllocEvents 32 1`);
    2. Old `rootKey` / receiver-chain drops (`FreeOnlyEvs`);
    3. Optional `senderChain` allocations (`evs = [] ∨ TrApplySenderAllocEnv evs`);
    4. Epilogue drops (`FreeOnlyEvs`). -/
@[expose] def TrApplyEnv : List AllocEvent → Prop :=
  SeqEnv (fun evs => evs = rustAllocEvents 32 1)
    (SeqEnv FreeOnlyEvs
      (SeqEnv (fun evs => evs = [] ∨ TrApplySenderAllocEnv evs) FreeOnlyEvs))

/-- Budget-threaded specification of `<TripleRatchet>::apply_to_session_state`
    at `trApplyStack` (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
@[expose] def trApplySpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (TrApplyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st TrApplyEnv⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.trApplySpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜TrApplyEnv evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.trApplySpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Budget-threaded specification of `<TripleRatchet>::apply_to_session_state`
    at `trApplyStackX` (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
@[expose] def trApplySpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (TrApplyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st TrApplyEnv⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.trApplySpecX
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜TrApplyEnv evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.trApplySpecX
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Non-empty 6-allocation witness trace (`senderChain.isSome` arm) belongs to `TrApplyEnv`. -/
theorem trApplyEnv_senderSome_mem :
    TrApplyEnv
      (rustAllocEvents 32 1 ++
        (rustAllocEvents 33 1 ++
          (rustAllocEvents 33 1 ++
            (rustAllocEvents 32 1 ++
              (rustAllocEvents 32 1 ++ rustAllocEvents 32 1))))) := by
  have hsnd : TrApplySenderAllocEnv
      (rustAllocEvents 33 1 ++
        (rustAllocEvents 33 1 ++
          (rustAllocEvents 32 1 ++
            (rustAllocEvents 32 1 ++ rustAllocEvents 32 1)))) :=
    SeqEnv.append rfl (SeqEnv.append rfl (SeqEnv.append rfl (SeqEnv.append rfl rfl)))
  have hmid : SeqEnv (fun evs => evs = [] ∨ TrApplySenderAllocEnv evs) FreeOnlyEvs
      (rustAllocEvents 33 1 ++
        (rustAllocEvents 33 1 ++
          (rustAllocEvents 32 1 ++
            (rustAllocEvents 32 1 ++ rustAllocEvents 32 1)))) := by
    simpa using SeqEnv.append (Or.inr hsnd) FreeOnlyEvs.nil
  have hfree : SeqEnv FreeOnlyEvs
      (SeqEnv (fun evs => evs = [] ∨ TrApplySenderAllocEnv evs) FreeOnlyEvs)
      (rustAllocEvents 33 1 ++
        (rustAllocEvents 33 1 ++
          (rustAllocEvents 32 1 ++
            (rustAllocEvents 32 1 ++ rustAllocEvents 32 1)))) := by
    simpa using SeqEnv.append FreeOnlyEvs.nil hmid
  exact SeqEnv.append rfl hfree

end LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget

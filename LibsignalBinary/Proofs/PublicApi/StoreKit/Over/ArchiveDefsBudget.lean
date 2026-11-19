/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Pure
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
# Budget-Threaded `archive_current_state_inner` and `promote_state` Specifications

Bounded allocation-event envelopes (`ArchiveCoreEnv`, `ArchiveOverGenEnv`, `PromoteOverGenEnv`,
`ArchiveOverEnvX`, `PromoteOverEnvX`), total-correctness `RustCliAllocBudget M` contracts
(`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`), and `PhaseCreditSpec` / `fineCostModel` `FitsEnv`
witnesses for `archive_current_state_inner` and `promote_state`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (PublicKey IdentityKey SessionState)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.E2E.Record.Serialization.SessionLenAux
  (bytesField_rootKey_length encSessionMem_length_eq chainsTotalLen_nil)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (clearPendingGhost clearPending
   ArchiveOverGenGhost PromoteOverGenGhost ArchiveOverGhost PromoteOverGhost)
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

/-- Allocation-event envelope of `archive_current_state_inner` and `promote_state` on
`(prevCap, G, sess)` with empty `previous_sessions`: optional pending-key deallocations
(`FreeOnlyEvs`), `Vec::with_capacity(encLen)` (`rustAllocEvents encLen 1`), optional `grow_one`
(`rustAllocEvents 96 8` when `prevCap = 0#64`), and stack-copy `drop_glue<SessionStructure>`
(`FreeOnlyEvs`). -/
@[expose] def ArchiveCoreEnv (prevCap : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) : List AllocEvent → Prop :=
  let encLen := (encSessionMem (clearPendingGhost G) (clearPending sess)).length
  SeqEnv FreeOnlyEvs
    (SeqEnv (fun evs => evs = rustAllocEvents encLen 1)
      (SeqEnv (fun evs => if prevCap = 0#64 then evs = rustAllocEvents 96 8 else evs = [])
        FreeOnlyEvs))

/-- Allocation envelope of `archiveOverGenSpec`. -/
abbrev ArchiveOverGenEnv (x : ArchiveOverGenGhost) : List AllocEvent → Prop :=
  ArchiveCoreEnv x.prevCap x.G x.sess

/-- Allocation envelope of `promoteOverGenSpec`. -/
abbrev PromoteOverGenEnv (x : PromoteOverGenGhost) : List AllocEvent → Prop :=
  ArchiveCoreEnv x.prevCap x.G x.sess

/-- Allocation envelope of `archiveOverSpecX` (`prevCap = 0#64`). -/
abbrev ArchiveOverEnvX (x : ArchiveOverGhost) : List AllocEvent → Prop :=
  ArchiveCoreEnv 0#64 x.G x.sess

/-- Allocation envelope of `promoteOverSpecX` (`prevCap = 0#64`). -/
abbrev PromoteOverEnvX (x : PromoteOverGhost) : List AllocEvent → Prop :=
  ArchiveCoreEnv 0#64 x.G x.sess

/-- Budget-threaded `archive_current_state_inner(recPtr)` contract with empty `previous_sessions`
    (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
@[expose] def archiveOverGenSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ArchiveOverGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (ArchiveOverGenEnv x)⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverGenSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ArchiveOverGenEnv x evs⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverGenSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Budget-threaded `promote_state(recPtr, src)` contract with empty `previous_sessions`
    (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
@[expose] def promoteOverGenSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PromoteOverGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (PromoteOverGenEnv x)⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverGenSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜PromoteOverGenEnv x evs⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverGenSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Budget-threaded zero-capacity (`prevCap = 0#64`) `archive_current_state_inner` contract
    (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
@[expose] def archiveOverSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ArchiveOverGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (ArchiveOverEnvX x)⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverSpecX
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ArchiveOverEnvX x evs⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverSpecX
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Budget-threaded zero-capacity (`prevCap = 0#64`) `promote_state` contract
    (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
@[expose] def promoteOverSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PromoteOverGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (PromoteOverEnvX x)⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverSpecX
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜PromoteOverEnvX x evs⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverSpecX
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-! ## `PhaseCreditSpec` and `fineCostModel` Non-Vacuity Witnesses -/

/-- Parametric `PhaseCreditSpec` for `ArchiveCoreEnv prevCap G sess` under `ModelHyps M`. -/
theorem archiveCoreEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (prevCap : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) :
    let encLen := (encSessionMem (clearPendingGhost G) (clearPending sess)).length
    PhaseCreditSpec M (ArchiveCoreEnv prevCap G sess)
      (2 * encLen + 19270)
      (encLen + 16486)
      (encLen + 16486)
      (max encLen 96) := by
  dsimp only
  set encLen := (encSessionMem (clearPendingGhost G) (clearPending sess)).length
  have hfr := PhaseCreditSpec.freeOnly_of_hyps hM
  have henc := PhaseCreditSpec.rustAlloc_aff hM (req := encLen) (al := 1) (by decide)
  have hgrow : PhaseCreditSpec M
      (fun evs => if prevCap = 0#64 then evs = rustAllocEvents 96 8 else evs = [])
      9731 8291 8291 96 := by
    by_cases h0 : prevCap = 0#64
    · simp only [h0, ↓reduceIte]
      exact (PhaseCreditSpec.rustAlloc_aff hM (req := 96) (al := 8) (by decide)).mono
        (by decide) (by decide) (by decide) (by decide)
    · simp only [h0, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono (by decide) (by decide) (by decide) (by decide)
  exact (hfr.seq (henc.seq (hgrow.seq hfr))).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Concrete `SessionGhost` witness for `ArchiveCoreEnv` non-vacuity. -/
def witnessSessionGhost : SessionGhost where
  localIk := ⟨33#64, 8#64, List.replicate 33 0x05#8⟩
  remoteIk := ⟨0#64, 1#64, []⟩
  root := ⟨32#64, 128#64⟩
  chainsCap := 0#64
  chainsPtr := 8#64
  chains := []
  alice := ⟨0#64, 1#64, []⟩
  pq := ⟨0#64, 1#64⟩
  sender := none
  pending := none
  kyber := none
  regIds := List.replicate 8 0#8

/-- Concrete `Session` witness for `ArchiveCoreEnv` non-vacuity. -/
def witnessSession : Session (List (BitVec 8)) where
  state := {
    sessionVersion := 4#32
    localIdentity := ⟨⟨List.replicate 32 0#8, by decide⟩⟩
    remoteIdentity := none
    rootKey := 0#256
    previousCounter := 0#32
    senderChain := none
    receiverChains := []
    pendingPreKey := false
    pqRatchetState := [1#8, 2#8, 3#8, 4#8]
  }
  pendingPreKey := none
  pendingKyberPreKey := none
  localRegistrationId := 1#32
  remoteRegistrationId := 2#32
  aliceBaseKey := []

end LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget

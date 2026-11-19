/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrBPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrPlaced
import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.HelpersBudget
public import Arm64.Trusted.Object.Labels
public import ProofLib.BV
public import ProofLib.BV.MaskLemmas
public import ProofLib.BV.PolyMul
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
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon

/-!
# Budget-Threaded Relocatable Stage P3 Error Spatial Bundles

Threads `RustCliAllocBudget M` (`A.pool lim st s` and `A.repAlloc`) through the `[LibsignalPlacement]`
Stage P3 error spatial bundles `stageP3ErrPrePrevEmptyPlacedBudget` and
`stageP3ErrPostPrevEmptyPlacedBudget`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrBPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (SessionState SignalProtocolError)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt vecResultAt)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (recordResultAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeySavedRegsAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)

@[expose] def stageP3ErrPrePrevEmptyPlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (coroPtr outPtr initErrsPtr : BitVec 64) (g : RecordGhost)
    (e : SignalProtocolError) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ vecResultAt A.repAlloc (s.sp + 0x270#64) (.error e) ∗
  sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
  prevSessionsEmptyAt A.repAlloc coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  memRegion outPtr 48 ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x930#64) 48 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  A.pool lim st s ∗ stackAt s.sp growOneSpeStack

abbrev stageP3ErrPrePrevEmptyPlaced := @stageP3ErrPrePrevEmptyPlacedBudget

@[expose] def stageP3ErrPostPrevEmptyPlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (coroPtr outPtr : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
  (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
    ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
    ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  recordResultAt A.repAlloc outPtr (.error (SessionState.recordError .preKey e)) ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  A.pool lim st s ∗ stackAt s.sp growOneSpeStack

abbrev stageP3ErrPostPrevEmptyPlaced := @stageP3ErrPostPrevEmptyPlacedBudget

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrBPlacedBudget

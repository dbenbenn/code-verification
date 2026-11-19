/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.IfaceSimp
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPack -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
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
# Budget-Threaded DH Commit Packing & `ReachesOrPanicOom` Combinators

Provides `RustCliAllocBudget M` layout-packing lemmas (`vecU8Buf_33_of_live`,
`chainAt_newChain_of_cells`) and relocatable `[LibsignalPlacement]` `ReachesOrPanicOom` stepping
and call combinators threading `VmPreserved` and `OomPreserved`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPackBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoGames.LibsignalSession (PublicKey ChainKey)
open CryptoVerification.RustHeap (vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (chainAt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (
  optChainKeyTailBytes optChainKeyHeap pack64 newChainGhost newReceiverChain
)
open LibsignalBinary.Heap (
  AllocCostModel RustCliAllocBudget VmPreserved OomPreserved
)
open LibsignalBinary.Heap.IfaceSimp (ReachesOrPanicOom)

/-! ## 1. Budget-Form Layout Packing Helpers -/

/-- Budget-form counterpart of `DhCommit.vecU8Buf_33_of_live` for `(A : RustCliAllocBudget M)`. -/
theorem vecU8Buf_33_of_live {M : AllocCostModel} (A : RustCliAllocBudget M)
    (ptr : BitVec 64) (bs : List (BitVec 8))
    (hptr : ptr ≠ 0) (hlen : bs.length = 33) :
    (A.live ptr 33 1 ∗ (ptr ↦ₛ bs)) ⊢ vecU8Buf A.repAlloc 33#64 ptr bs := by
  rw [← A.repAlloc_live_norm]
  exact CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.vecU8Buf_33_of_live
    A.repAlloc ptr bs hptr hlen

/-- Budget-form counterpart of `DhCommit.chainAt_newChain_of_cells` for `(A : RustCliAllocBudget M)`. -/
theorem chainAt_newChain_of_cells {M : AllocCostModel} (A : RustCliAllocBudget M)
    (slot srkPtr ckPtr : BitVec 64) (srk : PublicKey) (rck : ChainKey)
    {pad : List (BitVec 8)} (hpad : pad.length = 4) (hsrk_ne : srkPtr ≠ 0) :
    let tail := optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad
    ((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
     ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
     ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
     ((slot + 72#64) ↦₆₄ pack64 (tail.take 8)) ∗ ((slot + 80#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
     ((slot + 88#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗ ((slot + 96#64) ↦₆₄ pack64 (tail.drop 24)) ∗
     (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
     optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck)) ⊢
      chainAt A.repAlloc (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck) slot := by
  intro tail
  rw [← A.repAlloc_live_norm]
  exact CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.chainAt_newChain_of_cells
    A.repAlloc slot srkPtr ckPtr srk rck hpad hsrk_ne

/-! ## 2. `OomPreserved` Step Composition -/

/-! ## 3. Placed `[LibsignalPlacement]` `ReachesOrPanicOom` Combinators -/

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPackBudget

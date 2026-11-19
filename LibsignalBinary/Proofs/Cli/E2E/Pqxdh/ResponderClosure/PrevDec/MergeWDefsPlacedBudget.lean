/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym -- proof-setup: allow-public-import
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
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable Handshake `bytes::merge [local#5]` W-Mode Definitions

Budget-threaded (`RustCliAllocBudget M`) relocatable W-mode specification (`bytesMerge3PlacedSpecW`)
and contract proposition (`BytesMerge6PlacedOkExtW`, `x.bs.length < 2 ^ 62`) on `lsProg_518 ext`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement lsmpl withLsCl)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeGhost)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsBudget (
  bytesMerge3RawSpecW
)

/-- Relocatable `[LibsignalPlacement]` budget-threaded W-spec (`x.bs.length < 2 ^ 62`) of
`prost::encoding::bytes::merge [local#5]` on `lsProg_518 ext`. -/
abbrev bytesMerge3PlacedSpecW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) :=
  withLsCl lsmpl (bytesMerge3RawSpecW A lim)

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract for
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]`
(Block `508`, `(blkPl_507).base = lsmpl.base 507`) against `bytesMerge3PlacedSpecW A lim`. -/
@[expose] def BytesMerge6PlacedOkExtW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 507)
    (bytesMerge3PlacedSpecW A lim)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsPlacedBudget

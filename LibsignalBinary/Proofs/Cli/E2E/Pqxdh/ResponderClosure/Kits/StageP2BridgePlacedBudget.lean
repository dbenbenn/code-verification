/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BridgePlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
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
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable Stage P2 Error Frame

Defines `p2ErrFrameAtPlaced` over `A : RustCliAllocBudget M` (`A.pool lim st sf`) and bridges it
to `Poll.p2ErrFrameAtPlaced (A.atState lim st)`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BridgePlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.E2E.Pqxdh.Initiator (HandshakeHdr)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)

/-- Budget-threaded placed common coroutine, stack, message, address, and allocator spatial frame
delivered uniformly at `s0.readReg64 .x30` on all 6 Stage-P2 error exits (Arms 1–6), with
allocator pool `A.pool lim st sf`. -/
@[expose] def p2ErrFrameAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 sf : State)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2ErrFrameAtPlaced
    (A.atState lim st sf) s0
    sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388
    hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
    gMe gPeer stk Frame

theorem p2ErrFrameAtPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 sf : State)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    p2ErrFrameAtPlaced A lim st s0 sf
      sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388
      hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      gMe gPeer stk Frame =
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2ErrFrameAtPlaced
      (A.atState lim st sf) s0
      sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388
      hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      gMe gPeer stk Frame := rfl

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BridgePlacedBudget

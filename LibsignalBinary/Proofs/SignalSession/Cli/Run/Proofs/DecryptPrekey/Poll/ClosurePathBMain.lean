/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP
import LibsignalBinary.Proofs.E2E.HooksE.Common
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunFixed
import Arm64.Trusted.Object.Labels
import ProofLib.BV
import ProofLib.BV.MaskLemmas
import ProofLib.BV.PolyMul
import ProofLib.Hoare.MultiCodeROHook
import ProofLib.MallocngBridge
import ProofLib.Placed
import ProofLib.Placed.LabelsCheck
import ProofLib.Placed.LabelsCoverage
import ProofLib.Placed.LabelsInterned
import ProofLib.Placed.SharedCode
import ProofLib.Process.FsLemmas
import ProofLib.SepLogic.LoopTactics
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WP.StepsProcess
import ProofLib.StdStartup.Layout
import ProofLib.StdStartup.MemOps
import ProofLib.StdStartup.OutlineAtomics
import ProofLib.StdStartup.Strlen
import VerifiedLibraries.Mallocng.Spec
import VerifiedLibraries.Musl.Spec.Top
import VerifiedLibraries.RustStd.Spec
import VerifiedLibraries.RustStd.Spec.AllocFormatInner
import VerifiedLibraries.RustStd.Spec.AllocFormatInnerBudget
import VerifiedLibraries.RustStd.Spec.AllocStringClone
import VerifiedLibraries.RustStd.Spec.CoreFmtDisplay
import VerifiedLibraries.RustStd.Spec.CoreFmtWrite
import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
import VerifiedLibraries.RustStd.Spec.CoreMemrchr
import VerifiedLibraries.RustStd.Spec.FsRead
import VerifiedLibraries.RustStd.Spec.FsWrite
import VerifiedLibraries.RustStd.Spec.Stdio
import VerifiedLibraries.RustStd.Spec.TimeAdd
import VerifiedLibraries.RustStd.Spec.TimeDurationSince
import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullProof
import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Poll Matched-Session Path B Top-Level Branch

Combines `StageP2MatchedFramedExtAt` (`+0x0868 -> +0x1778` or mismatch exit),
`StageP3GenPathBExtAt` (`+0x1778 -> +0x34dc` or reject/panic exit), and Stage P4 continuation
(`+0x34dc -> s0.readReg64 .x30`) to prove `closure_pathB_ok_of_stages`, `closure_pathB_ok_ext`, and
`closure_pathB_ok`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `SepWPp` Outer-Frame Adapter for `P3P4.PanicOomProp` -/

/-- Allocator-polymorphic counterpart of `storesAt_opened_entails_cliPollStoresKitsAt`. -/
theorem storesAt_opened_entails_cliPollStoresKitsAt_ext
    {A : RustAlloc} (b : BitVec 64) {P : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {me : AddrVal} {pm : PreKeySignalMessage}
    {pid sid kid : BitVec 32} {kbk : PublicKey} (σ : DpKitStk) (a : BitVec 64)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOk₀ P Scope F peer.val me pm) :
    storesAt A a StoresGhost.opened ⊢
      cliPollStoresKitsAt A b F Slots.scopeKit peer pid sid kid kbk σ a StoresGhost.opened :=
  storesAt_entails_cliPollStoresKitsAt b σ a StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hf) (cliIdOwnInv_opened hd) (cliIdInv_opened_peer hf)
    (cliPkInv_opened hd pid) (cliSpkInv_opened hd sid) (cliKpkInvFull_opened hd kid sid kbk)

/-- Unpacks `storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened` into `cliPollStoresKitsAt`
under `Scope ⊆ Slots.scopeIn`, `Slots.FilesOkPeer`, and `DecPkOk₀`. -/
theorem storesAt_opened_entails_cliPollStoresKitsAt
    (b : BitVec 64) {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {me : AddrVal} {pm : PreKeySignalMessage}
    {pid sid kid : BitVec 32} {kbk : PublicKey} (σ : DpKitStk) (a : BitVec 64)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOk₀ W Scope F peer.val me pm) :
    storesAt E2E.HooksE.A0 a StoresGhost.opened ⊢
      cliPollStoresKitsAt E2E.HooksE.A0 b F Slots.scopeKit peer pid sid kid kbk σ a
        StoresGhost.opened :=
  storesAt_opened_entails_cliPollStoresKitsAt_ext b σ a hsub hf hd

/-- Precondition monotonicity for `SepWPp`. -/
theorem sepWPp_conseq_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qpan : State → SepProp → Prop}
    (hent : P ⊢ P') (hwp : SepWPp prog target s P' Q Qpan) :
    SepWPp prog target s P Q Qpan :=
  fun R' hm hL => hwp R' (Arm64.Satisfies.mono (sepConj_mono_left hent) hm) hL

end CryptoVerification.SignalSession.Cli.RunProofs.Poll

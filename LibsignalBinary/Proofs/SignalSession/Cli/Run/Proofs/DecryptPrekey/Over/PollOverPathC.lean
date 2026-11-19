/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCErr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4Cont -- proof-setup: allow-public-import
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
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# CLI Poll Overwrite-Path (`Path C`) Top-Level Branch

Combines `StageP2OverQpanCliStmt` (`+0x0868 → +0x1778`), `Over.StageP3Prev1VRegsStmt`
(`+0x1778 → +0x34dc`), and `closure_pathC_p4_cont` (`+0x34dc → s0.readReg64 .x30`) to prove
`closure_pathC_ok` when `load_session` yields a non-matching current session (`¬ SessMatchesPm`)
and `is_trusted_identity` returns `.ok true`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
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

private theorem x29_eq_sp_add_c70_pathC {s0 s2 : State}
    (hx29 : s2.readReg64 .x29 = s0.sp - 0x60#64)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64) :
    s2.readReg64 .x29 = s2.sp + 0xc70#64 := by
  rw [hx29, hs2_sp]; bv_omega

end CryptoVerification.SignalSession.Cli.RunProofs.Poll

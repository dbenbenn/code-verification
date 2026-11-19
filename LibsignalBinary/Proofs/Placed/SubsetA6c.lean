/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemPollRejectAuxPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBMainPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPollPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAFullPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchUntrustedPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsSelfPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage2PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage4PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.Stage4KitsPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAtFd
import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFdsStrClone
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostReplays
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtPeakCreditBridges
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress512GhostReplays
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.X25519CallerBridges
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsInstPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySelfKitFdsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberPreKeyKitFdsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeyKitFdsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitFdsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SignedPreKeyKitFdsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetOkFd
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetAuxFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAuxFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMidFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudgetAuxFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetAuxFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudgetAuxFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetAuxFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAuxFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.CliPubCalleesInstPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAP4PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAUntrustedPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathBP4PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathBPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathCP4PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathCPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathsPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverBPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverRegErrPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2PathAPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2V1RegErrPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptSlotWithFds
import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FmtWriteRowSpec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FormatInnerRowSpec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteFileRowSpec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteStdoutRowSpec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInst
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInst
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInst
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SessDeserStoreWithFds
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreKitWithFds
import LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1aFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1bFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2aFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2bFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAuxFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import Arm64.Trusted.Object.Labels
public import ProofLib.BV
public import ProofLib.Disproof.Basic
public import ProofLib.GenPlacedFetches
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.MallocngBridge
public import ProofLib.Placed
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.Multi
public import ProofLib.Placed.OpcodeExclusion
public import ProofLib.Placed.SharedCode
public import ProofLib.Process.FsLemmas
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.RegChain
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.SepLogic.WP.Apply
public import ProofLib.SepLogic.WP.SyscallsMmap
public import ProofLib.SepLogic.WPp
public import ProofLib.StdStartup.MuslStage1Init
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.Strlen
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Musl.Spec
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
public import VerifiedLibraries.Musl.Proofs.CryptoHooks
public import VerifiedLibraries.Musl.Proofs.MemmoveProof
public import VerifiedLibraries.Musl.Proofs.MemsetProof
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAuxBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget

/-!
# Relocatable `Subset A6c` Proof Barrel

Umbrella module rooting `Subset A6` relocatable proof modules (part C) under `[LibsignalPlacement]`.
-/

public section

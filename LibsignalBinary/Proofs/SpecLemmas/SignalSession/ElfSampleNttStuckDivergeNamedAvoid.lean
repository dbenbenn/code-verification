/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst -- proof-setup: allow-public-import
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection
public meta import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie -- proof-setup: allow-public-import
meta import ProofLib
meta import VerifiedLibraries.Musl.Proofs.SyscallProof
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.IfaceBudgetBaseBridges
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
import LibsignalBinary.Proofs.HookDischarge.Libc.Strlen
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.PlacedCallSym
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinCliIoInst
import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.Startup
import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec
import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TlsZero
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
import LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose
import LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic
import LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin
import LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
import LibsignalBinary.Proofs.SignalSession.CliIo.Sym
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Inst
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2CodeLoadedInv
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopDealloc -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReads
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsHelper
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopRealloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHooksUnfetchedPerPc
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStockStubResolve
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
import LibsignalBinary.Proofs.SpecLemmas.SymtabGhost
import ProofLib.Process
import ProofLib.Process.FastParse
import ProofLib.Process.FsLemmas
import ProofLib.SepLogic.WP.StepsProcess
import VerifiedLibraries.Musl.Proofs.SyscallProof

/-!
# Below-`0x4b0000` Guarded Startup Harness & Named-Ghost Replay (`ElfSampleNttStuckDivergeNamedAvoid`)

Provides the two `hextBelow` (`pc.toNat < 0x4b0000`) helper theorems for `ElfSampleNttStuckDiverge`
using the `5,606`-word prefix program `pRxSub` (`[0x474000, 0x479798) ⊂ [0x474000, 0x4b0000) ⊂ seg[2]`):
1. `cliElf_f3MuslHarness_c2EntryGuard_of_below4b0000`: whole-process guarded `musl` startup/exit
   harness at `F3C2EntryGuard mpl mmpl` for any `Syscall.standard` program `P` agreeing with
   `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` on `pc.toNat < 0x4b0000`.
2. `namedGhost_steps_of_below4b0000_of_ghFixed` (and `h2k_namedGhost_steps_of_below4b0000`): 10-way
   `GhostSymActiveNamed` replay on `P` under `hextBelow`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeNamedAvoid

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open ProofLib.SepLogic SepProp
open CryptoVerification (LibsignalPlacement lsLogFilterSym signalSessionIoMultiLib)
open CryptoVerification.LibsignalSpqrV1 (tokenName tokenStorageName)
open CryptoVerification.LibsignalTripleRatchet (extHookStack lsMemcpySym)
open CryptoVerification.SignalSession
  (ArgvFitsInitialStack CliHooks Inputs PathOk blockingAncestor? cliDehookedSymsPlaced cliElfBytes
   cliElfImage cliElf_staticOk cliExternsPlaced cliNonPanicDehookedSyms cliProcessInputs
   libsignalSessionLib lsBlackBoxSym lsFromUtf8Sym lsMemsetSym lsReadFileSym lsReadStdinSym
   lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
   lsRustReallocSymCli lsSharedSecretDropSym lsStaticSecretDropSym lsStringCloneSym patchElfByte
   pathComps processInputs)
open CryptoVerification.SignalSession.Cli (CliInputsOk InputsLoadable ReadRule cliInputs)
open CryptoVerification.SignalSession.Cli.MainHops (IoModel ReadStdinGhost cliIo cliMainStk)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC)
open CryptoVerification.SignalSession.CliExt (ReadFileCall)
open CryptoVerification.SignalSession.Coins (coinsLeftSym coinsNextSym)
open CryptoVerification.SignalSession.InitStack
  (cliStackSize cliStrs loadState_cli_layout sp0 stackBase toNat_sp0)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget RustCliAllocBudgetEntries
   RustCliAllocBudgetEntriesBase allocMemcpyVmSpec allocMemcpyVm_ok_of_wordTree
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
   subroutine_ok_rustCliAllocBudget_of_base)
open LibsignalBinary.Heap.Fine
  (CliElfMallocngLayout StartupVmPreserved allocMemsetVmSpec allocMemsetVm_ok_of_wordTree
   f3MallocngMpl f3NoShimV2Addr f3RdlAddrs f3RdlAzAddr f3RxWordCount f3StdLayout f3StubAddrs
   f3StubAzAddr fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec rustAllocShimVm_ret_ok)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRdlAllocZeroed_budget_placed_ok fineHookRustCliAllocBudgetEntries
   fineHookRustCliAllocBudgetEntries_thunks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (aesStorageCell fineHookRustCliAllocBudget_mapped_lt_userVa)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (StrlenSwarPadBound)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealRun ExecFrozen keepFsTrace real_subroutine_run_of_stripS specPreservesFsTrace_alloc
   specPreservesFsTrace_dealloc specPreservesFsTrace_realloc)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (ActiveF3ReadFileRun F3ReadFileFixedCallGuard f3ReadFileFallback
   fineHookRustCliAllocBudget_pool_stripS readFileAnyBudgetCondSpec readFileAnySpecPlaced
   real_f3ReadFileFixed_run_of_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst
  (cliIoReadFileAnyBudgetCond_ok_of_entries_of_readsCodeLoaded fineHookPoolErrnoSplit)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
  (ActiveReadStdinLinkedRun CompiledReadStdinEnv compiledReadStdinEnv_sub_bounded
   fitsEnv_compiled_of_sub keepFilesTrace readStdinBudgetCondSpec real_readStdin_run_of_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinCliIoInst
  (cliIoReadStdin_budgetCond_ok_of_readsCodeLoaded)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MuslHarnessFineNeedLocksGuardedPerInput StdMainEntryLr argvAtRO cStrAtRO cliBudgetLimits
   muslHarnessFineNeedLocksGuardedPerInput_of_startup
   muslHarnessFineNeedLocksGuardedPerInput_of_startup_ro)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3AllocFallback f3DeallocFallback f3LinkedCallHook f3ReadStdinFallback
   f3ReallocFallback specStripSInvariant_fine_alloc specStripSInvariant_fine_dealloc
   specStripSInvariant_fine_realloc)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliElfMallocngLayout_iff_patchElfTokensPlacedAt cliProgExtPlacedAt cliStackShape_cliProcessInputs
   cliStaticsPlacedAt coinsStaticsPlacedAt loadState_patchElfTokensPlacedAt lsLogOffAt
   patchElfTokensPlacedAt tokenInitPlacedAtMpl)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (StubReachesTargetOn stubReachesTargetOn_of_directOrBranchStub)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.Startup
  (F3StartupCode checkF3StartupCode f3StartupCode_of_wordTree f3StartupExtraChunks f3StartupResidual
   steps_lift_setTidOnly)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec
  (F3Seg5ShimBundle checkF3Seg5ShimBundle codeLoaded_of_checkProgSliceInWordTree
   f3Seg5ShimBundle_of_wordTree progContainsMultiLib_of_wordTree)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TlsZero
  (F3BssGlobals F3DataGlobals F3InitGlobals F3LayoutImageFacts F3RoConstants F3TlsState
   extractF3LayoutImageFacts f3AllRwAtoms f3AllRwAtoms_sep_eq f3BssAtoms f3CheckRwSegment
   f3DataNoStderrAtoms f3MatchesImage_codeLoaded f3MatchesImage_satisfies_roConstants
   f3MatchesImage_segments f3SetTidOnlySvc f3StaticInitTlsSpec f3StaticInitTls_setTidOnly_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode (memcmpByteLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap (BcmpEntryGuard keepBcmpHull)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxLrTrap
  (BlackBoxEntryGuard keepBlackBox)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard (F3C2EntryGuard c2GuardOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostSymActiveNamed)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Ghost (keepFromUtf8Block)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8LrTrap (FromUtf8EntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode
  (mallocngBlockProg20_externAt_none mallocngBlockProg20_hasWords masterMemcpySpec
   subroutine_ok_masterMemcpy_of_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost
  (keepCoversBlk20_keepMemcpyBlk20 keepMemcpyBlk20 masterMemcpy_outcome_setPC
   masterMemcpy_pre_setPC specPreservesFsTrace_masterMemcpy specStripSInvariant_masterMemcpy)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn
  (codeLoaded_stripExecOutside_blk20 f3EmptyMemcpyGhostHook f3EmptyMemcpyGhostHook_stepsUntil
   mallocngBlockProg20_svc_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost (keepBPreHull)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode
  (mallocngBlockProg21_externAt_none mallocngBlockProg21_hasWords masterMemsetSpec
   subroutine_ok_masterMemset_of_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost
  (keepCoversBlk21_keepMemsetBlk21 keepMemsetBlk21 masterMemset_outcome_setPC
   masterMemset_pre_setPC specPreservesFsTrace_masterMemset specStripSInvariant_masterMemset)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (activeF3CallPre_const_iff emptyStdProg f3EmptyMemsetGhostHook f3EmptyMemsetGhostHook_stepsUntil)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays
  (codeLoaded_stripExecOutside_blk21 mallocngBlockProg21_svc_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
  (f3EmptyMemcpyGhostHookNarrow f3EmptyMemsetGhostHookNarrow)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost (keepStrlenRange)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenLrTrap (StrlenEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost (sharedSecretDropEntryOff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap
  (SharedSecretDropEntryGuard StaticSecretDropEntryGuard
   keepSharedSecretDropHull keepStaticSecretDrop)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose
  (OpenatLocalExecSpec OpenatLocalOutcome dirReadErrno32 dirReadErrno32_cases
   dirReadErrno32_ne_eintr dirReadErrnoNat dirReadErrnoNat_bounds execOpenat_rdonly_cloexec_dir
   muslClose48LocalSpec muslOpenNoCreatCloexecLocalExecSpec muslReadDir32Spec
   step_svc_close_fd_local)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic
  (GoodComp ancestorWalkErrno?_eq_of_pathOk blockingAncestor?_ne_some_dir classifyOpenRdonly
   classifyOpenRdonly_err_cases classifyOpenRdonly_ok_spec goodComp_of_mem_pathComps
   hasDotDot_strOfComps hasLeadingSlash_strOfComps isEmpty_false_of_pathOk muslOpenRdonlyDetSpec
   normalizePath_ne_nil_of_pathOk pathComps_ne_nil strOfComps_pathComps trailingDir_false_of_pathOk
   validRelCPath_of_pathOk)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin
  (muslReadFileOrStdio32Spec muslReadStdin32Spec)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (ExternPreservesOracleSymtab)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym
  (CliIoReadsCodeLoaded cliIoReadFileSym cliIoReadStdinSym cliIoReadsCodeLoaded_of_blocks)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (cliNonPanicDehookedSyms_eq_entries f3DehookedEntries f3LsBlocksLen f3LsSymAddrs f3MngCodeHi
   f3MngCodeLo libsignalBlocks_len lsInternedMultiLib lsPlacedStubPairs lsPlacedStubPairs_eq
   lsSharedExterns ls_idsOk ls_names_nodup ls_sharedExterns_lt ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_libsignal_linkedAt_unique f3CliElf_mallocng_code_bounds_of_inElf
   f3CliElf_mallocng_linkedAt_unique f3CliElf_statics_rho_eq_of_linkedAt f3LsMpl f3TrialElf
   f3TrialElfSymChars f3TrialElfSyms_eq f3TrialElf_parse mallocngLib_in_f3TrialElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture (f3TrialElf_seg_count)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Inst
  (f3MAddrs_libc f3MallocngRoPad)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv F3CodeOk F3PanicFrame cliElf_f3MallocngLayout
   cliElf_f3StartupWithPanicFrame_of_linkedAt cliElf_tokenCellsPlacedAt_of_linkedAt
   f3CodeOk_of_keepsFrozen_and_perm f3CodeOk_of_patchedLoadState f3PatchedElf
   f3PatchedElf_eq_of_linkedAt f3PatchedElf_matchesImage f3PatchedElf_rxProgram_eq
   f3StartupRxSub f3StdExtra_entails_mallocngDataInit_of_linkedAt
   keepsFrozen_cliTokenPatchPlacedAt mallocngAddrsOfPlacement_eq_f3_of_linkedAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree f3TrialRxWordTree_eq
   f3TrialRxWordTree_size f3Trial_rustStdThunkCode f3Trial_seg5ShimBundle f3Trial_stubAz_hasInstrs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard
  (f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2CodeLoadedInv
  (h2cl_f3CodeInv_rxProg_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc
  (h2fsalloc_alloc_activeRealRun_keepSub h2fsalloc_allocZeroed_activeRealRun_keepSub
   h2fsalloc_mng_cAddrs_eq h2fsalloc_mng_fnAddr_eq h2fsalloc_mng_inElf h2fsalloc_mng_placeable
   h2fsalloc_progContainsMallocng h2fsalloc_spec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopDealloc
  (h2fsdealloc_activeRealRun_keepSub h2fsdealloc_spec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn h2fsgen_real_subroutine_run_visitedIn_of_stripS h2fsgen_stepsUntil_det
   h2fsgen_steps_lift_of_visitedIn_noExtern)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReads
  (h2fsreads_readFile_activeRealRun_keepSub h2fsreads_readStdin_activeRealRun_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopRealloc
  (h2fsrealloc_activeRealRun h2fsrealloc_spec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2
  (h2sl_emptyProg_externAt h2sl_emptyProg_svc h2sl_keepLoSub h2sl_realW_dehooked_witness
   h2sl_realW_noExtern_keepLoSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHooksUnfetchedPerPc
  (stepsUntil_noExtern_lift_of_visitedIn stepsVisitedIn_of_allProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_emptyProg hole2_hookStack hole2_keep hole2_keepSub hole2_targets)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStockStubResolve
  (h2b2_stockResolve_memcpy_eq_base h2b2_stockResolve_memset_eq_base)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (MallocngAuxvAt mallocngAddrsOfPlacement mallocngBlockProg)
open VerifiedLibraries.Mallocng.Proofs
  (ProgContainsMallocng ProgContainsMultiLib memcpySymWords)
open VerifiedLibraries.Musl
  (MuslSysPlacement ValidCPath memsetWords muslBlk00_errno_location muslBlk01_syscall_ret
   muslBlk02_sccp muslBlk03_syscall_cp muslBlk04_aio_close muslBlk05_close muslBlk06_read
   muslBlk07_write muslBlk08_open muslBlk09_fstat muslBlk10_fstatat muslErrnoLocationSpec
   muslSysLib00 muslSysLib01 muslSysLib02 muslSysLib03 muslSysLib04 muslSysLib05 muslSysLib06
   muslSysLib08 muslSysPC00 muslSysPC01 muslSysPC02 muslSysPC03 muslSysPC04 muslSysPC05
   muslSysPC06 muslSysPC08 muslSysPl00 muslSysPl01 muslSysPl02 muslSysPl03 muslSysPl04
   muslSysPl05 muslSysPl06 muslSysPl08 muslSysPlacedLib ofNat64_le_maxSyscallOk
   placed_program_rebase_self stdMemcpy_ok_of_hasWords step_stp64_perm step_str32_perm
   step_str64_perm_c sxtw64_truncate32)
open VerifiedLibraries.RustStd
  (RustStdThunkCode checkRustStdThunkCode mallocngPlacedCAddrs rustStdThunkCode_of_wordTree)

/-! ## 1. `pRxSub` (`[0x474000, 0x479798)`) and `keepRxSub` -/

/-- Word count of the `[0x474000, 0x479798)` prefix of `f3TrialRxProg` (`5,606` words = `0x5798` bytes). -/
private def rxSubWords : Nat := 5606

/-- Hook-free `Syscall.standard` `Program` covering `[0x474000, 0x479798)` (`< 0x479798`). -/
private def pRxSub : Program :=
  { base := f3RxSegBase
    code := f3TrialRxWordTree.toBytes.take (4 * rxSubWords)
    svc := Syscall.standard }

set_option maxHeartbeats 800000 in
private def wtRxSub : WordTree :=
  word_tree_of% pRxSub

set_option maxRecDepth 4000000 in
private theorem wtRxSub_eq : pRxSub.code = wtRxSub.toBytes := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem wtRxSub_size : wtRxSub.checkSize? = some rxSubWords := by
  rfl_kernel

private theorem pRxSub_base : pRxSub.base = f3RxSegBase := rfl
private theorem pRxSub_svc : pRxSub.svc = Syscall.standard := rfl
private theorem pRxSub_stubs : pRxSub.stubs = [] := rfl
private theorem pRxSub_symbols : pRxSub.symbols = [] := rfl
private theorem pRxSub_no_ext (pc : BitVec 64) : pRxSub.externAt? pc = none := rfl
private theorem pRxSub_externs_none (s : String) : (pRxSub.externs s).isNone = true := rfl
private theorem pRxSub_overrides_none (s : String) : (pRxSub.overrides s).isNone = true := rfl

private theorem pRxSub_code_len : pRxSub.code.length = 4 * rxSubWords := by
  rw [wtRxSub_eq]
  exact WordTree.length_toBytes_of_checkSize? wtRxSub_size

private abbrev keepRxSub (pc : BitVec 64) : Bool :=
  progKeep pRxSub pc

private theorem toNat_add_ofNat_of_lt {b : BitVec 64} {k : Nat}
    (hlt : b.toNat + k < 18446744073709551616) :
    (b + BitVec.ofNat 64 k).toNat = b.toNat + k := by
  have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hk : k < 2 ^ 64 := by omega
  have hlt' : b.toNat + k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt']

private theorem keepRxSub_iff (pc : BitVec 64) :
    keepRxSub pc = true ↔ 0x474000 ≤ pc.toNat ∧ pc.toNat < 0x479798 := by
  have hbase_nat : f3RxSegBase.toNat = 0x474000 := by decide
  have hlen : pRxSub.code.length = 0x5798 := by
    rw [pRxSub_code_len]; rfl
  simp only [keepRxSub, progKeep, pRxSub_base, hlen, decide_eq_true_eq]
  constructor
  · intro hlt
    have hadd : f3RxSegBase + (pc - f3RxSegBase) = pc := by bv_omega
    have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
    have hsum : f3RxSegBase.toNat + (pc - f3RxSegBase).toNat < 2 ^ 64 := by omega
    have htn : pc.toNat = f3RxSegBase.toNat + (pc - f3RxSegBase).toNat := by
      have h := congrArg BitVec.toNat hadd
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum] at h
      exact h.symm
    omega
  · rintro ⟨hlo, hhi⟩
    have hle : f3RxSegBase ≤ pc := by
      show f3RxSegBase.toNat ≤ pc.toNat
      omega
    rw [BitVec.toNat_sub_of_le hle]
    omega

private theorem keepRxSub_lt_4b0000 {pc : BitVec 64} (h : keepRxSub pc = true) :
    pc.toNat < 0x4b0000 := by
  have hhi := ((keepRxSub_iff pc).mp h).2
  omega

private theorem keepRxSub_imp_h2sl_keepLoSub {pc : BitVec 64} (h : keepRxSub pc = true) :
    h2sl_keepLoSub pc = true := by
  unfold h2sl_keepLoSub
  exact decide_eq_true ((keepRxSub_iff pc).mp h)

private theorem keepRxSub_imp_hole2_keepSub {pc : BitVec 64} (h : keepRxSub pc = true) :
    hole2_keepSub pc = true := by
  obtain ⟨hlo, hhi⟩ := (keepRxSub_iff pc).mp h
  have hlo' : Wp4LayoutGen.hole2_keepSubLo = 0x474000 := by decide
  have hhi' : 0x479798 ≤ Wp4LayoutGen.hole2_keepSubHi := by decide
  unfold hole2_keepSub
  exact decide_eq_true ⟨by omega, by omega⟩

private theorem keepRxSub_imp_hole2_keep {pc : BitVec 64} (h : keepRxSub pc = true) :
    hole2_keep pc = true := by
  have hs := keepRxSub_imp_hole2_keepSub h
  unfold hole2_keepSub at hs
  unfold hole2_keep
  exact decide_eq_true (Or.inr (of_decide_eq_true hs))

private theorem keepRxSub_false_of_hole2_keepSub_false {pc : BitVec 64}
    (h : hole2_keepSub pc = false) :
    keepRxSub pc = false := by
  cases hk : keepRxSub pc with
  | false => rfl
  | true =>
    rw [keepRxSub_imp_hole2_keepSub hk] at h
    cases h

private theorem noExtern_keepRxSub {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) {P : Program}
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    (pc : BitVec 64) (hkp : keepRxSub pc = true) :
    P.externAt? pc = none := by
  rw [hextBelow pc (keepRxSub_lt_4b0000 hkp)]
  exact h2sl_realW_noExtern_keepLoSub hLs mmpl W pc (keepRxSub_imp_h2sl_keepLoSub hkp)

private theorem list_getElem_of_eq_take {α : Type} {l1 l2 : List α} {n i : Nat}
    (heq : l1 = l2.take n) (hi1 : i < l1.length) (hi2 : i < l2.length) :
    l1[i]'hi1 = l2[i]'hi2 := by
  subst heq
  exact List.getElem_take

private theorem pRxSub_code_eq_take :
    pRxSub.code = f3TrialRxProg.code.take (4 * rxSubWords) :=
  let h1 : pRxSub.code = f3TrialRxWordTree.toBytes.take (4 * rxSubWords) := rfl
  h1.trans (congrArg (List.take (4 * rxSubWords)) f3TrialRxWordTree_eq.symm)

private theorem pRxSub_code_getElem_eq {idx : Nat}
    (h1 : idx < pRxSub.code.length) (h2 : idx < f3TrialRxProg.code.length) :
    pRxSub.code[idx]'h1 = f3TrialRxProg.code[idx]'h2 :=
  list_getElem_of_eq_take pRxSub_code_eq_take h1 h2

private theorem pRxSub_codeLoaded_of_f3TrialRxProg {m : Memory}
    (hL : f3TrialRxProg.CodeLoaded m) :
    pRxSub.CodeLoaded m := by
  have hlen_full : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
    rw [f3TrialRxWordTree_eq]
    exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size
  have hle_len : pRxSub.code.length ≤ f3TrialRxProg.code.length := by
    have h1 : rxSubWords = 5606 := rfl
    have h2 : f3RxWordCount = 90112 := rfl
    rw [pRxSub_code_len, hlen_full, h1, h2]
    omega
  have hal : pRxSub.base.toNat % 4 = 0 := by
    rw [pRxSub_base, ← f3TrialRxProg_base]
    exact hL.aligned
  have hnw : pRxSub.base.toNat + pRxSub.code.length ≤ 2 ^ 64 := by
    have h0 := hL.no_wrap
    rw [pRxSub_base, ← f3TrialRxProg_base]
    omega
  have hbase_eq : pRxSub.base = f3TrialRxProg.base := by
    rw [pRxSub_base, f3TrialRxProg_base]
  refine Program.CodeLoaded.intro hal hnw fun i hi => ?_
  have hi_full : i < f3TrialRxProg.code.length := Nat.lt_of_lt_of_le hi hle_len
  have hbyte_prog : pRxSub.code[i]'hi = f3TrialRxProg.code[i]'hi_full :=
    list_getElem_of_eq_take pRxSub_code_eq_take hi hi_full
  have hb := hL.byte_eq i hi_full
  have hp := hL.perm_eq i hi_full
  have hlf := hL.isLazyFree_eq i hi_full
  rw [← hbase_eq] at hb hp hlf
  exact ⟨hb.trans hbyte_prog.symm, hp, hlf⟩

set_option maxRecDepth 4000000 in
private theorem pRxSub_startupCode_chk :
    checkF3StartupCode f3StdLayout f3RxSegBase wtRxSub = true := by
  rfl_kernel

private theorem pRxSub_startupCode : F3StartupCode pRxSub f3StdLayout :=
  f3StartupCode_of_wordTree rxSubWords wtRxSub_eq wtRxSub_size
    pRxSub_svc pRxSub_stubs pRxSub_symbols pRxSub_externs_none pRxSub_overrides_none
    pRxSub_startupCode_chk

/-! ## 2. Startup / Exit Framing and `cliElf_f3MuslHarness_c2EntryGuard_of_below4b0000` -/

private theorem strip_codeLoaded_f3 {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (stripExecOutside (progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hin : progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    simp only [progKeep, decide_eq_true_eq, hsub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hi
  rw [strip_read8, strip_perm_of_keep hin, strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem cliElf_f3MuslHarnessLr_of_below4b0000
    {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (P : Program)
    (hsvc : P.svc = Arm64.Syscall.standard)
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc) :
    MuslHarnessFineNeedLocksGuardedPerInput 80
      (mallocngAddrsOfPlacement mmpl).libc
      cliElfImage
      P
      (mpl.base 617)
      cliProcessInputs
      mmpl cliBudgetLimits fineCostModel.init cliMainStk
      (F3CodeOk mpl mmpl)
      (cliStaticsPlacedAt mpl) (StdMainEntryLr f3StdLayout) := by
  have hHookFree : ∀ pc, progKeep f3StartupRxSub pc = true → (P.externAt? pc).isNone = true :=
    fun pc hkp => Option.isNone_iff_eq_none.mpr (noExtern_keepRxSub hls W hextBelow pc hkp)
  refine muslHarnessFineNeedLocksGuardedPerInput_of_startup_ro
    cliStackShape_cliProcessInputs cliElf_f3MallocngLayout rfl ?_
  intro _hE i hok
  obtain ⟨s0, sm, R_rest, auxvPtr, hload, hsteps, hpc, hrun, hal, hfs, htr, hlr,
    _htp, _hsm, _hsp_sig, _hsa, hx0, hvm, htpLo, htpHi, hCO, hCL, hsp, hmem, hexit⟩ :=
    cliElf_f3StartupWithPanicFrame_of_linkedAt hls hmng hsvc hHookFree hok
  exact ⟨s0, sm, F3PanicFrame f3StdLayout ∗ R_rest, auxvPtr, 0#32,
    hload, hsteps, hpc, hrun, hal, hfs, htr, hlr, hx0, hvm, htpLo, htpHi,
    hCO, hCL, hsp, hmem, hexit⟩

noncomputable section AvoidC2LrPriv

private def avoidC2_findStubPosAux (target : String) : List (String × BitVec 64) → Nat → Nat
  | [], acc => acc
  | (nm, _) :: rest, acc =>
    if nm == target then acc else avoidC2_findStubPosAux target rest (acc + 1)

private def avoidC2_stubPosOf (s : String) : Nat :=
  avoidC2_findStubPosAux s lsPlacedStubPairs 0

private def avoidC2_stubAddrOf (s : String) : BitVec 64 :=
  (lsPlacedStubPairs.getD (avoidC2_stubPosOf s) ("", 0#64)).2

private def avoidC2_f3StartupLrVal : BitVec 64 :=
  f3StdLayout.libcStartMainStage2Addr + 56#64

private def avoidC2_checkStubSymB (s : String) : Bool :=
  let pos := avoidC2_stubPosOf s
  let idx := lsSharedExterns.getD pos 0
  let pair := lsPlacedStubPairs.getD pos ("", 0#64)
  Nat.blt pos lsSharedExterns.length &&
  (pair.1 == s) &&
  (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none)

private def avoidC2_checkC2PinsB : Bool :=
  avoidC2_checkStubSymB "memcpy" &&
  avoidC2_checkStubSymB "memmove" &&
  avoidC2_checkStubSymB "bcmp" &&
  avoidC2_checkStubSymB "strlen" &&
  avoidC2_checkStubSymB lsFromUtf8Sym &&
  avoidC2_checkStubSymB lsBlackBoxSym &&
  avoidC2_checkStubSymB lsStaticSecretDropSym &&
  avoidC2_checkStubSymB lsSharedSecretDropSym

private def avoidC2_checkC2LrDisjointB : Bool :=
  (!keepBPreHull (avoidC2_stubAddrOf "memcpy") avoidC2_f3StartupLrVal) &&
  !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf "memmove") &&
  (!keepBcmpHull (avoidC2_stubAddrOf "bcmp" - memcmpByteLen) avoidC2_f3StartupLrVal) &&
  !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf "bcmp") &&
  (!keepStrlenRange (avoidC2_stubAddrOf "strlen") avoidC2_f3StartupLrVal) &&
  !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf "strlen") &&
  (!keepFromUtf8Block (avoidC2_stubAddrOf lsFromUtf8Sym) avoidC2_f3StartupLrVal) &&
  !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf lsFromUtf8Sym) &&
  (!keepBlackBox (avoidC2_stubAddrOf lsBlackBoxSym) avoidC2_f3StartupLrVal) &&
  !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf lsBlackBoxSym) &&
  (!keepStaticSecretDrop (avoidC2_stubAddrOf lsStaticSecretDropSym) avoidC2_f3StartupLrVal) &&
  !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf lsStaticSecretDropSym) &&
  (!keepSharedSecretDropHull (avoidC2_stubAddrOf lsSharedSecretDropSym - sharedSecretDropEntryOff) avoidC2_f3StartupLrVal) &&
  !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf lsSharedSecretDropSym)

set_option maxRecDepth 400000 in
private theorem avoidC2_checkC2PinsB_ok : avoidC2_checkC2PinsB = true := by
  rfl_kernel

set_option maxRecDepth 400000 in
private theorem avoidC2_checkC2LrDisjointB_ok : avoidC2_checkC2LrDisjointB = true := by
  rfl_kernel

private theorem avoidC2_avoidC2_stubAddrOf_def (s : String) :
    avoidC2_stubAddrOf s = (lsPlacedStubPairs.getD (avoidC2_stubPosOf s) ("", 0#64)).2 :=
  rfl

private theorem avoidC2_toMultiPlacement_rho_eq (mly : Obj.Interned.MultiLayout) (names : List String)
    (s : String) :
    (mly.toMultiPlacement names).ρ s = mly.addrs.getD (names.idxOf s) 0#64 :=
  rfl

private theorem avoidC2_resolve_eq_avoidC2_stubAddrOf {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s : String} (hok : avoidC2_checkStubSymB s = true) :
    libsignalSessionLib.resolve mpl s = avoidC2_stubAddrOf s := by
  have hc :
      (Nat.blt (avoidC2_stubPosOf s) lsSharedExterns.length &&
       ((lsPlacedStubPairs.getD (avoidC2_stubPosOf s) ("", 0#64)).1 == s) &&
       (Obj.Interned.lookupBlockSymId (lsSharedExterns.getD (avoidC2_stubPosOf s) 0)
          lsInternedMultiLib.blocks == none)) = true :=
    hok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
  rcases hc with ⟨⟨hpos_lt, hpair_fst⟩, hblk_none⟩
  set pos := avoidC2_stubPosOf s
  set idx := lsSharedExterns.getD pos 0
  have hidx_eq : idx = lsSharedExterns[pos]'hpos_lt :=
    Obj.Interned.getD_of_lt hpos_lt
  have hidx_lt : idx < lsInternedMultiLib.names.length := by
    have hmem_ext : idx ∈ lsSharedExterns := by
      rw [hidx_eq]
      exact List.getElem_mem hpos_lt
    exact Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hmem_ext)
  have hplen : pos < lsPlacedStubPairs.length := by
    rw [lsPlacedStubPairs_eq, List.length_map]
    exact hpos_lt
  have hpair :
      lsPlacedStubPairs.getD pos ("", 0#64) =
        (lsInternedMultiLib.names.getD idx "", f3LsSymAddrs.getD idx 0#64) := by
    rw [Obj.Interned.getD_of_lt hplen]
    simp only [lsPlacedStubPairs_eq, List.getElem_map, ← hidx_eq]
  have hname_eq : lsInternedMultiLib.names.getD idx "" = s :=
    (congrArg Prod.fst hpair).symm.trans hpair_fst
  have haddr_eq : f3LsSymAddrs.getD idx 0#64 = avoidC2_stubAddrOf s := by
    rw [avoidC2_avoidC2_stubAddrOf_def]
    exact (congrArg Prod.snd hpair).symm
  have hs_mem : s ∈ lsInternedMultiLib.names := by
    rw [← hname_eq, Obj.Interned.getD_of_lt hidx_lt]
    exact List.getElem_mem hidx_lt
  have hnone : Obj.lookupBlockSym s libsignalSessionLib.blocks = none := by
    rw [← hname_eq, ls_toMultiPlacedLib_eq,
      Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hidx_lt]
    exact hblk_none
  have hres_mpl : libsignalSessionLib.resolve mpl s = mpl.ρ s := by
    unfold Obj.MultiPlacedLib.resolve
    rw [hnone]
  have hρ_eq : mpl.ρ s = f3LsMpl.ρ s :=
    (f3CliElf_libsignal_linkedAt_unique hLs).2.2.1 s hs_mem hnone
  have hidxOf : lsInternedMultiLib.names.idxOf s = idx := by
    rw [← hname_eq]
    exact Obj.Interned.idxOf_getD ls_names_nodup hidx_lt
  have hρ_f3 : f3LsMpl.ρ s = f3LsSymAddrs.getD idx 0#64 := by
    unfold f3LsMpl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsMpl
    rw [avoidC2_toMultiPlacement_rho_eq, hidxOf]
    rfl
  exact hres_mpl.trans (hρ_eq.trans (hρ_f3.trans haddr_eq))

private theorem avoidC2_c2Pins_parts :
    avoidC2_checkStubSymB "memcpy" = true ∧
    avoidC2_checkStubSymB "memmove" = true ∧
    avoidC2_checkStubSymB "bcmp" = true ∧
    avoidC2_checkStubSymB "strlen" = true ∧
    avoidC2_checkStubSymB lsFromUtf8Sym = true ∧
    avoidC2_checkStubSymB lsBlackBoxSym = true ∧
    avoidC2_checkStubSymB lsStaticSecretDropSym = true ∧
    avoidC2_checkStubSymB lsSharedSecretDropSym = true := by
  have h :
      (avoidC2_checkStubSymB "memcpy" &&
       avoidC2_checkStubSymB "memmove" &&
       avoidC2_checkStubSymB "bcmp" &&
       avoidC2_checkStubSymB "strlen" &&
       avoidC2_checkStubSymB lsFromUtf8Sym &&
       avoidC2_checkStubSymB lsBlackBoxSym &&
       avoidC2_checkStubSymB lsStaticSecretDropSym &&
       avoidC2_checkStubSymB lsSharedSecretDropSym) = true :=
    avoidC2_checkC2PinsB_ok
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem avoidC2_c2LrDisjoint_parts :
    (keepBPreHull (avoidC2_stubAddrOf "memcpy") avoidC2_f3StartupLrVal = false ∧
      avoidC2_f3StartupLrVal ≠ avoidC2_stubAddrOf "memmove") ∧
    (keepBcmpHull (avoidC2_stubAddrOf "bcmp" - memcmpByteLen) avoidC2_f3StartupLrVal = false ∧
      avoidC2_f3StartupLrVal ≠ avoidC2_stubAddrOf "bcmp") ∧
    (keepStrlenRange (avoidC2_stubAddrOf "strlen") avoidC2_f3StartupLrVal = false ∧
      avoidC2_f3StartupLrVal ≠ avoidC2_stubAddrOf "strlen") ∧
    (keepFromUtf8Block (avoidC2_stubAddrOf lsFromUtf8Sym) avoidC2_f3StartupLrVal = false ∧
      avoidC2_f3StartupLrVal ≠ avoidC2_stubAddrOf lsFromUtf8Sym) ∧
    (keepBlackBox (avoidC2_stubAddrOf lsBlackBoxSym) avoidC2_f3StartupLrVal = false ∧
      avoidC2_f3StartupLrVal ≠ avoidC2_stubAddrOf lsBlackBoxSym) ∧
    (keepStaticSecretDrop (avoidC2_stubAddrOf lsStaticSecretDropSym) avoidC2_f3StartupLrVal = false ∧
      avoidC2_f3StartupLrVal ≠ avoidC2_stubAddrOf lsStaticSecretDropSym) ∧
    (keepSharedSecretDropHull (avoidC2_stubAddrOf lsSharedSecretDropSym - sharedSecretDropEntryOff) avoidC2_f3StartupLrVal = false ∧
      avoidC2_f3StartupLrVal ≠ avoidC2_stubAddrOf lsSharedSecretDropSym) := by
  have h :
      ((!keepBPreHull (avoidC2_stubAddrOf "memcpy") avoidC2_f3StartupLrVal) &&
       !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf "memmove") &&
       (!keepBcmpHull (avoidC2_stubAddrOf "bcmp" - memcmpByteLen) avoidC2_f3StartupLrVal) &&
       !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf "bcmp") &&
       (!keepStrlenRange (avoidC2_stubAddrOf "strlen") avoidC2_f3StartupLrVal) &&
       !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf "strlen") &&
       (!keepFromUtf8Block (avoidC2_stubAddrOf lsFromUtf8Sym) avoidC2_f3StartupLrVal) &&
       !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf lsFromUtf8Sym) &&
       (!keepBlackBox (avoidC2_stubAddrOf lsBlackBoxSym) avoidC2_f3StartupLrVal) &&
       !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf lsBlackBoxSym) &&
       (!keepStaticSecretDrop (avoidC2_stubAddrOf lsStaticSecretDropSym) avoidC2_f3StartupLrVal) &&
       !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf lsStaticSecretDropSym) &&
       (!keepSharedSecretDropHull (avoidC2_stubAddrOf lsSharedSecretDropSym - sharedSecretDropEntryOff) avoidC2_f3StartupLrVal) &&
       !(avoidC2_f3StartupLrVal == avoidC2_stubAddrOf lsSharedSecretDropSym)) = true :=
    avoidC2_checkC2LrDisjointB_ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact ⟨⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    ⟨h.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.2⟩,
    ⟨h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2⟩,
    ⟨h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2⟩,
    ⟨h.1.1.1.1.1.2, h.1.1.1.1.2⟩,
    ⟨h.1.1.1.2, h.1.1.2⟩,
    ⟨h.1.2, h.2⟩⟩

attribute [local irreducible] avoidC2_stubPosOf avoidC2_stubAddrOf

private theorem avoidC2_hlr_eq_startupLrVal {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    s0.readReg64 .lr = avoidC2_f3StartupLrVal :=
  hlr

/-- Derives `libsignalSessionLib.resolve mpl lsFromUtf8Sym = avoidC2_stubAddrOf lsFromUtf8Sym`
    from `hLs` (`f3CliElf_libsignal_linkedAt_unique`) and `s0.readReg64 .lr = stage2 + 56#64`
    from `hlr : StdMainEntryLr f3StdLayout s0`, closing `FromUtf8GhostReplays.fromUtf8EntryGuard`. -/
private theorem avoidC2_f3FromUtf8EntryGuard_of_stdMainEntryLr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays.fromUtf8EntryGuard
      mpl s0 := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays.fromUtf8EntryGuard
    FromUtf8EntryGuard
  rw [avoidC2_resolve_eq_avoidC2_stubAddrOf hLs avoidC2_c2Pins_parts.2.2.2.2.1, avoidC2_hlr_eq_startupLrVal hlr]
  exact avoidC2_c2LrDisjoint_parts.2.2.2.1

private theorem avoidC2_ite_bool_intro {c : Bool} {P Q : Prop}
    (hT : c = true → P) (hF : c = false → Q) :
    (if c = true then P else Q) := by
  cases c with
  | true => exact hT rfl
  | false => exact hF rfl

/-- Every `cliExtraGhostSyms` entry guard holds at `StdMainEntryLr f3StdLayout s0`. -/
private theorem avoidC2_c2GuardOf_of_stdMainEntryLr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {sym : String} {s0 : State}
    (hlr : StdMainEntryLr f3StdLayout s0) :
    c2GuardOf mpl sym s0 := by
  unfold c2GuardOf
  refine avoidC2_ite_bool_intro (fun _ => ?_) fun _ => ?_
  · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays.memmoveEntryGuard
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays.keepR_memmove
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays.memcpyEntry
    rw [avoidC2_resolve_eq_avoidC2_stubAddrOf hLs avoidC2_c2Pins_parts.1,
      avoidC2_resolve_eq_avoidC2_stubAddrOf hLs avoidC2_c2Pins_parts.2.1,
      avoidC2_hlr_eq_startupLrVal hlr]
    exact avoidC2_c2LrDisjoint_parts.1
  · refine avoidC2_ite_bool_intro (fun _ => ?_) fun _ => ?_
    · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays.bcmpEntryGuard
        LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays.bcmpHullBase
        BcmpEntryGuard
      rw [avoidC2_resolve_eq_avoidC2_stubAddrOf hLs avoidC2_c2Pins_parts.2.2.1, avoidC2_hlr_eq_startupLrVal hlr]
      exact avoidC2_c2LrDisjoint_parts.2.1
    · refine avoidC2_ite_bool_intro (fun _ => ?_) fun _ => ?_
      · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays.strlenEntryGuard
          LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays.strlenEntry
          StrlenEntryGuard
        rw [avoidC2_resolve_eq_avoidC2_stubAddrOf hLs avoidC2_c2Pins_parts.2.2.2.1, avoidC2_hlr_eq_startupLrVal hlr]
        exact avoidC2_c2LrDisjoint_parts.2.2.1
      · refine avoidC2_ite_bool_intro (fun _ => trivial) fun _ => ?_
        refine avoidC2_ite_bool_intro (fun _ => avoidC2_f3FromUtf8EntryGuard_of_stdMainEntryLr hLs hlr) fun _ => ?_
        refine avoidC2_ite_bool_intro (fun _ => trivial) fun _ => ?_
        refine avoidC2_ite_bool_intro (fun _ => trivial) fun _ => ?_
        refine avoidC2_ite_bool_intro (fun _ => ?_) fun _ => ?_
        · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays.blackBoxEntryGuard
            BlackBoxEntryGuard
          rw [avoidC2_resolve_eq_avoidC2_stubAddrOf hLs avoidC2_c2Pins_parts.2.2.2.2.2.1, avoidC2_hlr_eq_startupLrVal hlr]
          exact avoidC2_c2LrDisjoint_parts.2.2.2.2.1
        · refine avoidC2_ite_bool_intro (fun _ => ?_) fun _ => ?_
          · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays.staticSecretDropEntryGuard
              StaticSecretDropEntryGuard
            rw [avoidC2_resolve_eq_avoidC2_stubAddrOf hLs avoidC2_c2Pins_parts.2.2.2.2.2.2.1, avoidC2_hlr_eq_startupLrVal hlr]
            exact avoidC2_c2LrDisjoint_parts.2.2.2.2.2.1
          · refine avoidC2_ite_bool_intro (fun _ => ?_) fun _ => ?_
            · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays.sharedSecretDropEntryGuard
                LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays.sharedSecretDropHullBase
                SharedSecretDropEntryGuard
              rw [avoidC2_resolve_eq_avoidC2_stubAddrOf hLs avoidC2_c2Pins_parts.2.2.2.2.2.2.2, avoidC2_hlr_eq_startupLrVal hlr]
              exact avoidC2_c2LrDisjoint_parts.2.2.2.2.2.2
            · refine avoidC2_ite_bool_intro (fun _ => trivial) fun _ => ?_
              refine avoidC2_ite_bool_intro (fun _ => trivial) fun _ => ?_
              refine avoidC2_ite_bool_intro (fun _ => trivial) fun _ => ?_
              exact avoidC2_ite_bool_intro (fun _ => trivial) fun _ => trivial

private theorem avoid_f3C2EntryGuard_of_stdMainEntryLr {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    F3C2EntryGuard mpl mmpl s0 :=
  ⟨f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr hMm hlr,
   fun _sym _hDom => avoidC2_c2GuardOf_of_stdMainEntryLr hLs hlr⟩

end AvoidC2LrPriv

/-- Guarded `musl` startup/exit harness at `F3C2EntryGuard mpl mmpl` for any `Syscall.standard`
program `P` agreeing with `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` on `pc < 0x4b0000`. -/
theorem cliElf_f3MuslHarness_c2EntryGuard_of_below4b0000
    {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (P : Program)
    (hsvc : P.svc = Arm64.Syscall.standard)
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc) :
    MuslHarnessFineNeedLocksGuardedPerInput 80
      (mallocngAddrsOfPlacement mmpl).libc
      cliElfImage
      P
      (mpl.base 617) cliProcessInputs mmpl cliBudgetLimits fineCostModel.init cliMainStk
      (F3CodeOk mpl mmpl) (cliStaticsPlacedAt mpl)
      (F3C2EntryGuard mpl mmpl) :=
  (cliElf_f3MuslHarnessLr_of_below4b0000 hls hmng W P hsvc hextBelow).mono_guard
    (fun _ hlr => avoid_f3C2EntryGuard_of_stdMainEntryLr hls hmng hlr)


/-! ## 3. Below-`0x4b0000` Linked Stubs and `shim` / `memset` / `memcpy` Replays -/

private theorem avoid_unpatched_load {mpl mmpl : MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    ∃ (inputs : ProcessInputs) (sRaw : State),
      cliElfImage.loadState inputs = .ok sRaw ∧ sRaw.mem.KeepsFrozen m := by
  obtain ⟨inputs, sLoad, hload, hkfLoad⟩ := hInv.fromLoad
  have htok := cliElf_tokenCellsPlacedAt_of_linkedAt hLs
  have hmap := loadState_patchElfTokensPlacedAt cliElf_staticOk htok inputs
  rw [hmap] at hload
  cases hraw : cliElfImage.loadState inputs with
  | error _ =>
    rw [hraw] at hload
    cases hload
  | ok sRaw =>
    rw [hraw] at hload
    simp only [Except.map, Except.ok.injEq] at hload
    have hkf0 : sRaw.mem.KeepsFrozen sLoad.mem := by
      rw [← hload]
      exact keepsFrozen_cliTokenPatchPlacedAt cliElf_staticOk htok hraw
    exact ⟨inputs, sRaw, hraw, hkf0.trans hkfLoad⟩

private noncomputable def namedDehookedEntries : List (Nat × List Char × BitVec 64 × BitVec 64) :=
  f3DehookedEntries.take 7

private def namedDehookedPairs : List (String × BitVec 64) :=
  [ (lsRustNoAllocShimSymCli, f3NoShimV2Addr),
    (lsRustAllocSymCli, f3StubAddrs.alloc),
    (lsRustDeallocSymCli, f3StubAddrs.dealloc),
    (lsRustReallocSymCli, f3StubAddrs.realloc),
    (lsRustAllocZeroedSymCli, f3StubAzAddr),
    (lsReadFileSym, 0x4741b4#64),
    (lsReadStdinSym, 0x474000#64) ]

private theorem namedDehookedEntries_pairs_eq :
    (namedDehookedEntries.map fun e => (String.ofList e.2.1, e.2.2.2)) = namedDehookedPairs := by
  rfl_kernel

private noncomputable def checkNamedDehookedMetaB : Bool :=
  Obj.Interned.buildEncSymTable f3TrialElfSymChars fun enc =>
    namedDehookedEntries.all fun (idx, cs, _, targetVa) =>
      Nat.blt idx lsInternedMultiLib.names.length &&
      (lsInternedMultiLib.names.getD idx "" == String.ofList cs) &&
      (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none) &&
      Nat.blt (f3LsSymAddrs.getD idx 0#64).toNat 0x4b0000 &&
      (Obj.Interned.withEncodeCharKey cs fun key =>
        ProofLib.ObjectLoad.lookupUniqueEnc key enc == some targetVa)

set_option maxRecDepth 4000000 in
private theorem checkNamedDehookedMeta_ok : checkNamedDehookedMetaB = true := by
  rfl_kernel

private theorem avoid_lookupBlockSym_none_of_idx {idx : Nat} {s : String}
    (hlt : idx < lsInternedMultiLib.names.length)
    (heq : lsInternedMultiLib.names.getD idx "" = s)
    (hid : Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks = none) :
    Obj.lookupBlockSym s libsignalSessionLib.blocks = none := by
  rw [← heq, ls_toMultiPlacedLib_eq,
    Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hlt]
  exact hid

private theorem avoid_f3LsMpl_rho_of_idx {s : String} {idx : Nat}
    (hidx : lsInternedMultiLib.names.idxOf s = idx) :
    f3LsMpl.ρ s = f3LsSymAddrs.getD idx 0#64 := by
  have h : f3LsMpl.ρ s =
      f3LsSymAddrs.getD (lsInternedMultiLib.names.idxOf s) 0#64 := rfl
  rw [h, hidx]

private theorem namedDehooked_pair_facts {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {sym : String} {tgt : BitVec 64}
    (hmem : (sym, tgt) ∈ namedDehookedPairs) :
    sym ∈ cliNonPanicDehookedSyms ∧
    libsignalSessionLib.resolve mpl sym = mpl.ρ sym ∧
    (mpl.ρ sym).toNat < 0x4b0000 ∧
    Obj.lookupUnique sym cliElfImage.symbols = some tgt := by
  rw [← namedDehookedEntries_pairs_eq, List.mem_map] at hmem
  obtain ⟨⟨idx, cs, stubVa, targetVa⟩, hmem_e, heq_pair⟩ := hmem
  dsimp only at heq_pair
  injection heq_pair with hsym_eq htgt_eq
  subst hsym_eq htgt_eq
  have hchk := checkNamedDehookedMeta_ok
  unfold checkNamedDehookedMetaB at hchk
  rw [Obj.Interned.buildEncSymTable_eq] at hchk
  have he := List.all_eq_true.mp hchk (idx, cs, stubVa, targetVa) hmem_e
  simp only [Obj.Interned.withEncodeCharKey_eq, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at he
  obtain ⟨⟨⟨⟨hlt, hname⟩, hid⟩, hrho_lt⟩, hlu_enc⟩ := he
  have hmem_full : (idx, cs, stubVa, targetVa) ∈ f3DehookedEntries :=
    (List.take_sublist 7 f3DehookedEntries).subset hmem_e
  have hmem_dehook : String.ofList cs ∈ cliNonPanicDehookedSyms := by
    rw [cliNonPanicDehookedSyms_eq_entries, List.mem_map]
    exact ⟨(idx, cs, stubVa, targetVa), hmem_full, rfl⟩
  have hnone := avoid_lookupBlockSym_none_of_idx hlt hname hid
  have hres : libsignalSessionLib.resolve mpl (String.ofList cs) = mpl.ρ (String.ofList cs) := by
    unfold MultiPlacedLib.resolve
    rw [hnone]
  have hmem_names : String.ofList cs ∈ lsInternedMultiLib.names := by
    rw [← hname, Obj.Interned.getD_of_lt hlt]
    exact List.getElem_mem hlt
  have hrho_eq : mpl.ρ (String.ofList cs) = f3LsMpl.ρ (String.ofList cs) :=
    (f3CliElf_libsignal_linkedAt_unique hLs).2.2.1 _ hmem_names hnone
  have hidx : lsInternedMultiLib.names.idxOf (String.ofList cs) = idx := by
    rw [← hname]
    exact Obj.Interned.idxOf_getD ls_names_nodup hlt
  have hstub_lt : (mpl.ρ (String.ofList cs)).toNat < 0x4b0000 := by
    rw [hrho_eq, avoid_f3LsMpl_rho_of_idx hidx]
    exact hrho_lt
  have hlu : Obj.lookupUnique (String.ofList cs) cliElfImage.symbols = some targetVa := by
    change Obj.lookupUnique (String.ofList cs)
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced.f3TrialElf.symbols =
      some targetVa
    rw [ProofLib.ObjectLoad.lookupUnique_eq_lookupUniqueEnc f3TrialElfSyms_eq rfl rfl]
    exact hlu_enc
  exact ⟨hmem_dehook, hres, hstub_lt, hlu⟩

private theorem namedDehooked_stubReachesTargetOn {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) {P : Program}
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    {sym : String} {tgt : BitVec 64}
    (hmem : (sym, tgt) ∈ namedDehookedPairs) :
    StubReachesTargetOn (F3CodeInv mpl mmpl) P (libsignalSessionLib.resolve mpl sym) tgt := by
  obtain ⟨hsym, hres, hstub_lt, hlu_tgt⟩ := namedDehooked_pair_facts hLs hmem
  obtain ⟨hstub_none, targetVa, hlu_wit, hdir, _⟩ :=
    h2sl_realW_dehooked_witness (mmpl := mmpl) hLs hsym
  have htgt_eq : targetVa = tgt := Option.some.inj (hlu_wit.symm.trans hlu_tgt)
  subst htgt_eq
  rw [hres]
  have hP_none : P.externAt? (mpl.ρ sym) = none := by
    rw [hextBelow (mpl.ρ sym) hstub_lt]
    exact hstub_none W
  exact stubReachesTargetOn_of_directOrBranchStub hP_none hdir
    (fun _ hInv => avoid_unpatched_load hLs hInv)

private theorem thunk_reachesTarget_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) {P : Program}
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    {stubPc stubVa rdlVa : BitVec 64}
    (h0 : StubReachesTargetOn (F3CodeInv mpl mmpl) P stubPc stubVa)
    (hInstr : ProofLib.StdStartup.hasInstrs f3TrialRxProg stubVa [ .b (rdlVa - stubVa) ])
    (hks : keepRxSub stubVa = true) :
    StubReachesTargetOn (F3CodeInv mpl mmpl) P stubPc rdlVa := by
  intro u hpc hrun hfr hInv
  have hsteps0 := h0 u hpc hrun hfr hInv
  have hfetch_rx : f3TrialRxProg.fetch stubVa = some (.b (rdlVa - stubVa)) :=
    ProofLib.StdStartup.hasInstrs.fetch_at_zero hInstr
  have hfm_rx : f3TrialRxProg.fetchMem u.mem stubVa = some (.b (rdlVa - stubVa)) :=
    Program.fetchMem_of_fetch hInv.rxCode hfetch_rx
  have hno_P : P.externAt? stubVa = none :=
    noExtern_keepRxSub hLs W hextBelow stubVa hks
  have hno_rx : f3TrialRxProg.externAt? stubVa = none :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext stubVa
  have hfm : P.fetchMem (u.setPC stubVa).mem (u.setPC stubVa).pc = some (.b (rdlVa - stubVa)) := by
    change P.fetchMem u.mem stubVa = some (.b (rdlVa - stubVa))
    unfold Program.fetchMem at hfm_rx ⊢
    rw [hno_P]
    rw [hno_rx] at hfm_rx
    exact hfm_rx
  have hrun1 : (u.setPC stubVa).status = .Running := hrun
  have hstep1 : Step P (u.setPC stubVa) (P.evalInst (.b (rdlVa - stubVa)) (u.setPC stubVa)) :=
    Step.exec hrun1 hfm
  have heval : P.evalInst (.b (rdlVa - stubVa)) (u.setPC stubVa) = u.setPC rdlVa := by
    have h1 : P.evalInst (.b (rdlVa - stubVa)) (u.setPC stubVa) =
        (u.setPC stubVa).setPC (stubVa + (rdlVa - stubVa)) := rfl
    rw [h1, show stubVa + (rdlVa - stubVa) = rdlVa by bv_omega]
    cases u
    rfl
  rw [heval] at hstep1
  exact hsteps0.trans (Steps.step hstep1 (Steps.refl _))

private theorem stub_shim_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) {P : Program}
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc) :
    StubReachesTargetOn (F3CodeInv mpl mmpl) P
      (libsignalSessionLib.resolve mpl lsRustNoAllocShimSymCli) f3NoShimV2Addr :=
  namedDehooked_stubReachesTargetOn hLs W hextBelow (by simp [namedDehookedPairs])

private theorem stub_alloc_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) {P : Program}
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc) :
    StubReachesTargetOn (F3CodeInv mpl mmpl) P
      (libsignalSessionLib.resolve mpl lsRustAllocSymCli) (hole2_targets mpl).alloc :=
  thunk_reachesTarget_below4b0000 hLs W hextBelow
    (namedDehooked_stubReachesTargetOn hLs W hextBelow (tgt := f3StubAddrs.alloc)
      (by simp [namedDehookedPairs]))
    f3Trial_rustStdThunkCode.alloc_thunk ((keepRxSub_iff _).mpr (by decide))

private theorem stub_dealloc_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) {P : Program}
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc) :
    StubReachesTargetOn (F3CodeInv mpl mmpl) P
      (libsignalSessionLib.resolve mpl lsRustDeallocSymCli) (hole2_targets mpl).dealloc :=
  thunk_reachesTarget_below4b0000 hLs W hextBelow
    (namedDehooked_stubReachesTargetOn hLs W hextBelow (tgt := f3StubAddrs.dealloc)
      (by simp [namedDehookedPairs]))
    f3Trial_rustStdThunkCode.dealloc_thunk ((keepRxSub_iff _).mpr (by decide))

private theorem stub_realloc_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) {P : Program}
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc) :
    StubReachesTargetOn (F3CodeInv mpl mmpl) P
      (libsignalSessionLib.resolve mpl lsRustReallocSymCli) (hole2_targets mpl).realloc :=
  thunk_reachesTarget_below4b0000 hLs W hextBelow
    (namedDehooked_stubReachesTargetOn hLs W hextBelow (tgt := f3StubAddrs.realloc)
      (by simp [namedDehookedPairs]))
    f3Trial_rustStdThunkCode.realloc_thunk ((keepRxSub_iff _).mpr (by decide))

private theorem stub_allocZeroed_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) {P : Program}
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc) :
    StubReachesTargetOn (F3CodeInv mpl mmpl) P
      (libsignalSessionLib.resolve mpl lsRustAllocZeroedSymCli) (hole2_targets mpl).allocZeroed :=
  thunk_reachesTarget_below4b0000 hLs W hextBelow
    (namedDehooked_stubReachesTargetOn hLs W hextBelow (tgt := f3StubAzAddr)
      (by simp [namedDehookedPairs]))
    f3Trial_stubAz_hasInstrs ((keepRxSub_iff _).mpr (by decide))

private theorem stub_readFile_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) {P : Program}
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc) :
    StubReachesTargetOn (F3CodeInv mpl mmpl) P
      (libsignalSessionLib.resolve mpl lsReadFileSym) (hole2_targets mpl).readFile :=
  namedDehooked_stubReachesTargetOn hLs W hextBelow (tgt := 0x4741b4#64)
    (by simp [namedDehookedPairs])

private theorem stub_readStdin_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) {P : Program}
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc) :
    StubReachesTargetOn (F3CodeInv mpl mmpl) P
      (libsignalSessionLib.resolve mpl lsReadStdinSym) (hole2_targets mpl).readStdin :=
  namedDehooked_stubReachesTargetOn hLs W hextBelow (tgt := 0x474000#64)
    (by simp [namedDehookedPairs])

private theorem replay_shim_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) {P : Program}
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsRustNoAllocShimSymCli)
    (hrun : u.status = .Running)
    (hFr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps P u (hookNoop u) := by
  have hsteps0 := stub_shim_below4b0000 hLs W hextBelow u hpc hrun hFr hInv
  have hfetch_rx : f3TrialRxProg.fetch f3NoShimV2Addr = some (.ret .lr) :=
    ProofLib.StdStartup.hasInstrs.fetch_at_zero f3Trial_seg5ShimBundle.noAllocShimV2
  have hfm_rx : f3TrialRxProg.fetchMem u.mem f3NoShimV2Addr = some (.ret .lr) :=
    Program.fetchMem_of_fetch hInv.rxCode hfetch_rx
  have hno_P : P.externAt? f3NoShimV2Addr = none :=
    noExtern_keepRxSub hLs W hextBelow f3NoShimV2Addr ((keepRxSub_iff _).mpr (by decide))
  have hno_rx : f3TrialRxProg.externAt? f3NoShimV2Addr = none :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
      f3NoShimV2Addr
  have hfm :
      P.fetchMem (u.setPC f3NoShimV2Addr).mem (u.setPC f3NoShimV2Addr).pc = some (.ret .lr) := by
    change P.fetchMem u.mem f3NoShimV2Addr = some (.ret .lr)
    unfold Program.fetchMem at hfm_rx ⊢
    rw [hno_P]
    rw [hno_rx] at hfm_rx
    exact hfm_rx
  have hrun1 : (u.setPC f3NoShimV2Addr).status = .Running := hrun
  have hstep1 : Step P (u.setPC f3NoShimV2Addr) (P.evalInst (.ret .lr) (u.setPC f3NoShimV2Addr)) :=
    Step.exec hrun1 hfm
  have heval : P.evalInst (.ret .lr) (u.setPC f3NoShimV2Addr) = hookNoop u := by
    cases u
    rfl
  rw [heval] at hstep1
  exact hsteps0.trans (Steps.step hstep1 (Steps.refl _))

private theorem keepMemsetBlk21_imp_keepRxSub {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) {pc : BitVec 64}
    (hk : keepMemsetBlk21 mmpl pc = true) :
    keepRxSub pc = true := by
  have hb21 : mmpl.base 21 = 0x4747e0#64 :=
    ((f3CliElf_mallocng_linkedAt_unique hMm).1 21 (by decide)).trans (by decide)
  unfold keepMemsetBlk21 at hk
  rw [hb21, decide_eq_true_eq] at hk
  have heq_pc : 0x4747e0#64 + BitVec.ofNat 64 (pc - 0x4747e0#64).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  have hb_tn : (0x4747e0#64 : BitVec 64).toNat = 0x4747e0 := by decide
  have ht : (0x4747e0#64 + BitVec.ofNat 64 (pc - 0x4747e0#64).toNat).toNat =
      0x4747e0 + (pc - 0x4747e0#64).toNat := by
    rw [toNat_add_ofNat_of_lt (by rw [hb_tn]; omega), hb_tn]
  rw [heq_pc] at ht
  exact (keepRxSub_iff pc).mpr ⟨by omega, by omega⟩

private theorem keepMemcpyBlk20_imp_keepRxSub {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) {pc : BitVec 64}
    (hk : keepMemcpyBlk20 mmpl pc = true) :
    keepRxSub pc = true := by
  have hb20 : mmpl.base 20 = 0x474650#64 :=
    ((f3CliElf_mallocng_linkedAt_unique hMm).1 20 (by decide)).trans (by decide)
  unfold keepMemcpyBlk20 at hk
  rw [hb20, decide_eq_true_eq] at hk
  have heq_pc : 0x474650#64 + BitVec.ofNat 64 (pc - 0x474650#64).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  have hb_tn : (0x474650#64 : BitVec 64).toNat = 0x474650 := by decide
  have ht : (0x474650#64 + BitVec.ofNat 64 (pc - 0x474650#64).toNat).toNat =
      0x474650 + (pc - 0x474650#64).toNat := by
    rw [toNat_add_ofNat_of_lt (by rw [hb_tn]; omega), hb_tn]
  rw [heq_pc] at ht
  exact (keepRxSub_iff pc).mpr ⟨by omega, by omega⟩

private theorem replay_memset_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMemsetSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyMemsetGhostHookNarrow mmpl u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr21 : keepMemsetBlk21 mmpl (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps P u (f3EmptyMemsetGhostHookNarrow mmpl u) := by
  classical
  have hres : libsignalSessionLib.resolve mpl lsMemsetSym = mmpl.base 21 :=
    h2b2_stockResolve_memset_eq_base hLs hMm
  have hsetPC : u.setPC (mmpl.base 21) = u := by
    have hpc_eq : mmpl.base 21 = u.pc := (hpc.trans hres).symm
    rw [hpc_eq]
    cases u
    rfl
  have hCode21 :
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded
        (stripExecOutside (keepMemsetBlk21 mmpl) u.mem) :=
    codeLoaded_stripExecOutside_blk21 (keepCoversBlk21_keepMemsetBlk21 mmpl)
      (hInv.mngCode 21 (by decide))
  obtain ⟨huntil, hstop, _, _⟩ :=
    f3EmptyMemsetGhostHook_stepsUntil (mallocngBlockProg21_svc_eq mmpl)
      (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
      (mallocngBlockProg21_hasWords mmpl Syscall.standard)
      hrun hnoex hFr hlr21 hCode21
  have hActPre : ActiveF3CallPre (fun _ _ => masterMemsetSpec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3EmptyMemsetGhostHookNarrow f3EmptyMemsetGhostHook f3LinkedCallHook
    simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ := (activeF3CallPre_const_iff masterMemsetSpec u).mp hActPre
  have hAllP : ∀ (Q : Program), Q.svc = emptyStdProg.svc →
      (∀ pc : BitVec 64, keepMemsetBlk21 mmpl pc = true → Q.externAt? pc = none) →
      ∃ sf : State, StepsUntil Q (SubroutineStop u) (u.setPC (mmpl.base 21)) sf ∧
        SubroutineStop u sf := by
    intro Q hsvcQ hnoQ
    obtain ⟨sf, huQ, hsQ, _⟩ :=
      real_subroutine_run_of_stripS (P_real := Q) hsvcQ (mallocngBlockProg21_svc_eq mmpl) hnoQ
        (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
        (subroutine_ok_masterMemset_of_hasWords
          (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
          (mallocngBlockProg21_hasWords mmpl Syscall.standard))
        (specStripSInvariant_masterMemset (keepMemsetBlk21 mmpl))
        specPreservesFsTrace_masterMemset
        masterMemset_pre_setPC
        masterMemset_outcome_setPC
        hrun hsp hpre hFr hlr21 hCode21
    exact ⟨sf, huQ, hsQ⟩
  have hvis := stepsVisitedIn_of_allProg (D := keepMemsetBlk21 mmpl)
    (fun _ _ => rfl) hAllP huntil
  have hSteps := stepsUntil_noExtern_lift_of_visitedIn
    (D := keepMemsetBlk21 mmpl) (P1 := emptyStdProg) (P2 := P)
    hsvc.symm (fun _ _ => rfl)
    (fun pc hk => noExtern_keepRxSub hLs W hextBelow pc (keepMemsetBlk21_imp_keepRxSub hMm hk))
    hvis hstop
  rwa [hsetPC] at hSteps

private theorem replay_memcpy_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMemcpySym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyMemcpyGhostHookNarrow mmpl u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr20 : keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps P u (f3EmptyMemcpyGhostHookNarrow mmpl u) := by
  classical
  have hres : libsignalSessionLib.resolve mpl lsMemcpySym = mmpl.base 20 :=
    h2b2_stockResolve_memcpy_eq_base hLs hMm
  have hsetPC : u.setPC (mmpl.base 20) = u := by
    have hpc_eq : mmpl.base 20 = u.pc := (hpc.trans hres).symm
    rw [hpc_eq]
    cases u
    rfl
  have hCode20 :
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded
        (stripExecOutside (keepMemcpyBlk20 mmpl) u.mem) :=
    codeLoaded_stripExecOutside_blk20 (keepCoversBlk20_keepMemcpyBlk20 mmpl)
      (hInv.mngCode 20 (by decide))
  obtain ⟨huntil, hstop, _, _⟩ :=
    f3EmptyMemcpyGhostHook_stepsUntil (mallocngBlockProg20_svc_eq mmpl)
      (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
      (mallocngBlockProg20_hasWords mmpl Syscall.standard)
      hrun hnoex hFr hlr20 hCode20
  have hActPre : ActiveF3CallPre (fun _ _ => masterMemcpySpec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3EmptyMemcpyGhostHookNarrow f3EmptyMemcpyGhostHook f3LinkedCallHook
    simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ := (activeF3CallPre_const_iff masterMemcpySpec u).mp hActPre
  have hAllP : ∀ (Q : Program), Q.svc = emptyStdProg.svc →
      (∀ pc : BitVec 64, keepMemcpyBlk20 mmpl pc = true → Q.externAt? pc = none) →
      ∃ sf : State, StepsUntil Q (SubroutineStop u) (u.setPC (mmpl.base 20)) sf ∧
        SubroutineStop u sf := by
    intro Q hsvcQ hnoQ
    obtain ⟨sf, huQ, hsQ, _⟩ :=
      real_subroutine_run_of_stripS (P_real := Q) hsvcQ (mallocngBlockProg20_svc_eq mmpl) hnoQ
        (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
        (subroutine_ok_masterMemcpy_of_hasWords
          (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
          (mallocngBlockProg20_hasWords mmpl Syscall.standard))
        (specStripSInvariant_masterMemcpy (keepMemcpyBlk20 mmpl))
        specPreservesFsTrace_masterMemcpy
        masterMemcpy_pre_setPC
        masterMemcpy_outcome_setPC
        hrun hsp hpre hFr hlr20 hCode20
    exact ⟨sf, huQ, hsQ⟩
  have hvis := stepsVisitedIn_of_allProg (D := keepMemcpyBlk20 mmpl)
    (fun _ _ => rfl) hAllP huntil
  have hSteps := stepsUntil_noExtern_lift_of_visitedIn
    (D := keepMemcpyBlk20 mmpl) (P1 := emptyStdProg) (P2 := P)
    hsvc.symm (fun _ _ => rfl)
    (fun pc hk => noExtern_keepRxSub hLs W hextBelow pc (keepMemcpyBlk20_imp_keepRxSub hMm hk))
    hvis hstop
  rwa [hsetPC] at hSteps

/-! ## 4. `pRxSub` Allocator `subroutine_ok` and Arms 1–4 (`alloc`, `dealloc`, `realloc`, `allocZeroed`) -/

private theorem keepRxSub_mallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, (mallocngLib.findCodeBlock mmpl a).isSome = true → keepRxSub a = true := by
  intro a hsome
  cases hf : mallocngLib.findCodeBlock mmpl a with
  | none => simp [hf] at hsome
  | some k =>
    have hk : k < mallocngLib.blocks.length := ProofLib.findCodeBlock_lt hf
    have hin : Arm64.InRegion (mmpl.base k) (mallocngLib.blockPatched mmpl k).length a :=
      ProofLib.findCodeBlock_inRegion hf
    have hlen : (mallocngLib.blockPatched mmpl k).length = mallocngLib.blocks[k].code.length := by
      unfold MultiPlacedLib.blockPatched
      rw [mallocngLib.blockLib_text hk]
      exact CodeBlock.length_patched_of_aligned _
        ((h2fsalloc_mng_placeable mmpl hMm).blocks_ok k hk).len_aligned
    rw [hlen] at hin
    obtain ⟨_, hhi64, hm_lo, hm_hi⟩ :=
      f3CliElf_mallocng_code_bounds_of_inElf
        (h2fsalloc_mng_placeable mmpl hMm) (h2fsalloc_mng_inElf mmpl hMm) k hk
    have hk_off : (a - mmpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    have heq_a : mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_omega
    have hlo : 0x474000 ≤ f3MngCodeLo := by decide
    have hhi : f3MngCodeHi ≤ 0x479798 := by decide
    have ht : (mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat).toNat =
        (mmpl.base k).toNat + (a - mmpl.base k).toNat :=
      toNat_add_ofNat_of_lt (by omega)
    rw [heq_a] at ht
    exact (keepRxSub_iff a).mpr ⟨by omega, by omega⟩

private theorem exists_f3TrialRxProg_codeLoaded : ∃ m0 : Memory, f3TrialRxProg.CodeLoaded m0 := by
  let p0 : ProcessInputs := processInputs ["libsignal-cli"] [] [] []
  have hinit : p0.init.Valid :=
    show ({ stackSize := 8388608, auxv := { hwcap := 0x1b#64 } } : ProcessInit).Valid from
      (ProcessInit.check_iff_valid _).mp (by decide)
  have hfs : FsValid p0 := (FsValid.check_iff p0).mp rfl
  have hargs : ArgsValid p0 := by
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp [p0, processInputs]
    · intro s hs
      simp only [p0, processInputs, List.map_cons, List.map_nil, List.mem_singleton] at hs
      subst hs
      exact of_decide_eq_true (by decide)
    · intro s hs
      simp [p0, processInputs] at hs
    · simp [p0, processInputs]
    · intro s hs
      simp only [p0, processInputs, List.append_nil, List.map_cons, List.map_nil,
        List.mem_singleton] at hs
      subst hs
      exact of_decide_eq_true (by decide)
    · simp only [p0, processInputs]
      decide
    · unfold argBytes argLimit STK_LIM ARG_MAX
      simp only [p0, processInputs, List.map_cons, List.map_nil,
        List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil]
      have hbin : (bytesOfString "libsignal-cli").length = 13 := by decide
      rw [hbin]
      omega
  have hvalid0 : p0.Valid := ⟨hargs, hinit, hfs⟩
  obtain ⟨hwf, _, _, _, hbrk_eq, _⟩ := f3MatchesImage_segments f3PatchedElf_matchesImage
  have hbrk_sbm : f3PatchedElf.brkStart.toNat ≤ STACK_BASE_MIN := by
    rw [hbrk_eq]; unfold STACK_BASE_MIN; omega
  obtain ⟨s0, hload0, _⟩ := loadState_ok_initialStackInfo f3PatchedElf hwf hvalid0 hbrk_sbm
  have hL : (f3StdLayout.rxProgram f3PatchedElf).CodeLoaded s0.mem :=
    f3MatchesImage_codeLoaded f3PatchedElf_matchesImage hload0
  rw [f3PatchedElf_rxProgram_eq] at hL
  exact ⟨s0.mem, hL⟩

section PrxMngPriv
attribute [local irreducible] pRxSub

private theorem pRxSub_progContainsMallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ProgContainsMallocng pRxSub mmpl := by
  obtain ⟨m0, hm0⟩ := exists_f3TrialRxProg_codeLoaded
  have hPl := h2fsalloc_mng_placeable mmpl hMm
  have hIn := h2fsalloc_mng_inElf mmpl hMm
  have hFull := h2fsalloc_progContainsMallocng mmpl hMm
  refine ProgContainsMultiLib.of_noExterns hPl pRxSub_svc
    (fun m hPm i hi => ?_) pRxSub_no_ext
  have hcl0 := hFull.codeLoaded m0 hm0 i hi
  have hbase_blk : (mallocngLib.blockProgram mmpl i).base = mmpl.base i := rfl
  have hlen_blk : (mallocngLib.blockProgram mmpl i).code.length =
      mallocngLib.blocks[i].code.length := by
    simp only [MultiPlacedLib.blockProgram, PlacedLib.program, mallocngLib.blockLib_text hi]
    exact CodeBlock.length_patched_of_aligned _ (hPl.blocks_ok i hi).len_aligned
  obtain ⟨_, _, hm_lo, hm_hi⟩ :=
    f3CliElf_mallocng_code_bounds_of_inElf hPl hIn i hi
  have hlo : 0x474000 ≤ f3MngCodeLo := by decide
  have hhi : f3MngCodeHi ≤ 0x479798 := by decide
  have hbase_nat : f3RxSegBase.toNat = 0x474000 := by decide
  have hlen_sub : pRxSub.code.length = 0x5798 := by rw [pRxSub_code_len]; rfl
  have hlen_full : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
    rw [f3TrialRxWordTree_eq]
    exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size
  have hwc : f3RxWordCount = 90112 := rfl
  refine Program.CodeLoaded.intro hcl0.aligned hcl0.no_wrap fun k hk => ?_
  have hk_raw : k < mallocngLib.blocks[i].code.length := by rwa [hlen_blk] at hk
  generalize hidx_def : ((mmpl.base i).toNat - 0x474000) + k = idx
  have hidx_sub : idx < pRxSub.code.length := by rw [hlen_sub]; omega
  have hidx_full : idx < f3TrialRxProg.code.length := by rw [hlen_full, hwc]; omega
  have haddr_sub : pRxSub.base + BitVec.ofNat 64 idx =
      (mallocngLib.blockProgram mmpl i).base + BitVec.ofNat 64 k := by
    rw [pRxSub_base, hbase_blk]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_ofNat_of_lt (by rw [hbase_nat]; omega),
        toNat_add_ofNat_of_lt (by omega), hbase_nat]
    omega
  have haddr_full : f3TrialRxProg.base + BitVec.ofNat 64 idx =
      (mallocngLib.blockProgram mmpl i).base + BitVec.ofNat 64 k := by
    rw [f3TrialRxProg_base, ← pRxSub_base]
    exact haddr_sub
  have hbyte_take := pRxSub_code_getElem_eq hidx_sub hidx_full
  have hb_m := hPm.byte_eq idx hidx_sub
  have hp_m := hPm.perm_eq idx hidx_sub
  have hlf_m := hPm.isLazyFree_eq idx hidx_sub
  have hb_0 := hm0.byte_eq idx hidx_full
  have hp_0 := hm0.perm_eq idx hidx_full
  have hb_blk := hcl0.byte_eq k hk
  have hp_blk := hcl0.perm_eq k hk
  rw [haddr_sub] at hb_m hp_m hlf_m
  rw [haddr_full] at hb_0 hp_0
  exact ⟨hb_m.trans (hbyte_take.trans (hb_0.symm.trans hb_blk)),
         hp_m.trans (hp_0.symm.trans hp_blk),
         hlf_m⟩

end PrxMngPriv

set_option maxRecDepth 4000000 in
private theorem pRxSub_seg5ShimBundle_chk :
    checkF3Seg5ShimBundle f3RxSegBase wtRxSub
      f3RdlAddrs f3RdlAzAddr f3NoShimV2Addr
      (mallocngPlacedCAddrs f3MallocngMpl)
      (VerifiedLibraries.mallocngLib.fnAddr f3MallocngMpl "calloc")
      f3StdLayout.memcpyAddr f3StdLayout.memsetAddr = true := by
  rfl_kernel

private theorem pRxSub_seg5ShimBundle :
    F3Seg5ShimBundle pRxSub
      f3RdlAddrs f3RdlAzAddr f3NoShimV2Addr
      (mallocngPlacedCAddrs f3MallocngMpl)
      (VerifiedLibraries.mallocngLib.fnAddr f3MallocngMpl "calloc")
      f3StdLayout.memcpyAddr f3StdLayout.memsetAddr :=
  f3Seg5ShimBundle_of_wordTree rxSubWords wtRxSub_eq wtRxSub_size
    pRxSub_externs_none pRxSub_overrides_none
    (by rw [pRxSub_base]; exact pRxSub_seg5ShimBundle_chk)

set_option maxRecDepth 4000000 in
private theorem pRxSub_memcpy_chk :
    checkWordsAt wtRxSub (f3StdLayout.memcpyAddr - f3RxSegBase).toNat memcpySymWords = true := by
  rfl_kernel

private theorem pRxSub_allocMemcpyVm_ok :
    subroutine_ok pRxSub f3StdLayout.memcpyAddr allocMemcpyVmSpec := by
  have hoff_lt : (f3StdLayout.memcpyAddr - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen : memcpySymWords.length ≤ 1024 :=
    Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble memcpySymWords.length 1024 = true)
  exact allocMemcpyVm_ok_of_wordTree rxSubWords wtRxSub_eq wtRxSub_size pRxSub_no_ext
    (by rw [pRxSub_base]) (by omega) pRxSub_stubs pRxSub_symbols pRxSub_memcpy_chk

set_option maxRecDepth 4000000 in
private theorem pRxSub_memset_chk :
    checkWordsAt wtRxSub (f3StdLayout.memsetAddr - f3RxSegBase).toNat memsetWords = true := by
  rfl_kernel

private theorem pRxSub_allocMemsetVm_ok :
    subroutine_ok pRxSub f3StdLayout.memsetAddr allocMemsetVmSpec := by
  have hoff_lt : (f3StdLayout.memsetAddr - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen : memsetWords.length ≤ 1024 :=
    Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble memsetWords.length 1024 = true)
  exact allocMemsetVm_ok_of_wordTree rxSubWords wtRxSub_eq wtRxSub_size pRxSub_no_ext
    (by rw [pRxSub_base]) (by omega) pRxSub_stubs pRxSub_symbols pRxSub_memset_chk

private theorem pRxSub_rdlEntries [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    RustCliAllocBudgetEntries fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      pRxSub f3RdlAddrs := by
  have hShims := pRxSub_seg5ShimBundle.rdlShims
  rw [← h2fsalloc_mng_cAddrs_eq mmpl hMm] at hShims
  exact (fineHookRustCliAllocBudgetEntries
    (pRxSub_progContainsMallocng mmpl hMm) γ tp cliElfImage.brkStart hShims
    pRxSub_allocMemcpyVm_ok).toPlaced

private theorem pRxSub_rdlAlloc_ok [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok pRxSub f3RdlAddrs.alloc (h2fsalloc_spec mmpl false γ tp) :=
  (pRxSub_rdlEntries mmpl hMm γ tp).alloc cliBudgetLimits

private theorem pRxSub_rdlAllocZeroed_ok [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok pRxSub f3RdlAzAddr (h2fsalloc_spec mmpl true γ tp) := by
  have hZero := pRxSub_seg5ShimBundle.allocZeroedInstrs
  rw [← h2fsalloc_mng_fnAddr_eq mmpl hMm "calloc", ← h2fsalloc_mng_cAddrs_eq mmpl hMm] at hZero
  exact subroutine_ok_rustCliAllocBudget_of_base
    (fineHookRdlAllocZeroed_budget_placed_ok
      (pRxSub_progContainsMallocng mmpl hMm) γ tp cliElfImage.brkStart
      f3RdlAzAddr f3StdLayout.memsetAddr cliBudgetLimits
      hZero pRxSub_allocMemsetVm_ok)

private def avoid_allocTarget (zeroed : Bool) : BitVec 64 :=
  if zeroed then f3RdlAzAddr else f3RdlAddrs.alloc

private theorem pRxSub_rdl_ok [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (zeroed : Bool) (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok pRxSub (avoid_allocTarget zeroed) (h2fsalloc_spec mmpl zeroed γ tp) := by
  cases zeroed
  · exact pRxSub_rdlAlloc_ok mmpl hMm γ tp
  · exact pRxSub_rdlAllocZeroed_ok mmpl hMm γ tp

private theorem pRxSub_rdlDealloc_ok [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok pRxSub f3RdlAddrs.dealloc (h2fsdealloc_spec mmpl γ tp) :=
  (pRxSub_rdlEntries mmpl hMm γ tp).dealloc cliBudgetLimits

private theorem pRxSub_rdlRealloc_ok [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok pRxSub f3RdlAddrs.realloc (h2fsrealloc_spec mmpl γ tp) :=
  (pRxSub_rdlEntries mmpl hMm γ tp).realloc cliBudgetLimits

private theorem pRxSub_alloc_firstStop_keepRxSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (zeroed : Bool)
    {Q : Program}
    (hsvcQ : Q.svc = Syscall.standard)
    (hnoQ : ∀ pc : BitVec 64, keepRxSub pc = true → Q.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsalloc_spec mmpl zeroed) s0)
    (hLr : keepRxSub (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : pRxSub.CodeLoaded (stripExecOutside keepRxSub s0.mem)) :
    ∃ sf : State,
      StepsUntil Q (SubroutineStop s0) (s0.setPC (avoid_allocTarget zeroed)) sf ∧
      SubroutineStop s0 sf := by
  obtain ⟨hRun, hSp, γ, tp, x, R, hSat⟩ := hPre
  obtain ⟨sf, huntil, hstop, _⟩ :=
    real_subroutine_run_of_stripS hsvcQ pRxSub_svc hnoQ pRxSub_no_ext
      (pRxSub_rdl_ok mmpl hMm zeroed γ tp)
      (specStripSInvariant_fine_alloc γ mmpl tp cliElfImage.brkStart (keepRxSub_mallocng mmpl hMm)
        cliBudgetLimits zeroed)
      (specPreservesFsTrace_alloc _ cliBudgetLimits zeroed)
      (fun _ s _ => by cases s; rfl)
      (fun _ _ s0 _ _ => by cases s0; exact id)
      hRun hSp hSat hFr hLr hCode
  exact ⟨sf, huntil, hstop⟩

private theorem pRxSub_dealloc_firstStop_keepRxSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {Q : Program}
    (hsvcQ : Q.svc = Syscall.standard)
    (hnoQ : ∀ pc : BitVec 64, keepRxSub pc = true → Q.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsdealloc_spec mmpl) s0)
    (hLr : keepRxSub (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : pRxSub.CodeLoaded (stripExecOutside keepRxSub s0.mem)) :
    ∃ sf : State,
      StepsUntil Q (SubroutineStop s0) (s0.setPC f3RdlAddrs.dealloc) sf ∧
      SubroutineStop s0 sf := by
  obtain ⟨hRun, hSp, γ, tp, x, R, hSat⟩ := hPre
  obtain ⟨sf, huntil, hstop, _⟩ :=
    real_subroutine_run_of_stripS hsvcQ pRxSub_svc hnoQ pRxSub_no_ext
      (pRxSub_rdlDealloc_ok mmpl hMm γ tp)
      (specStripSInvariant_fine_dealloc γ mmpl tp cliElfImage.brkStart (keepRxSub_mallocng mmpl hMm)
        cliBudgetLimits)
      (specPreservesFsTrace_dealloc _ cliBudgetLimits)
      (fun _ s _ => by cases s; rfl)
      (fun _ _ s0 _ _ => by cases s0; exact id)
      hRun hSp hSat hFr hLr hCode
  exact ⟨sf, huntil, hstop⟩

private theorem pRxSub_realloc_firstStop_keepRxSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {Q : Program}
    (hsvcQ : Q.svc = Syscall.standard)
    (hnoQ : ∀ pc : BitVec 64, keepRxSub pc = true → Q.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsrealloc_spec mmpl) s0)
    (hLr : keepRxSub (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : pRxSub.CodeLoaded (stripExecOutside keepRxSub s0.mem)) :
    ∃ sf : State,
      StepsUntil Q (SubroutineStop s0) (s0.setPC f3RdlAddrs.realloc) sf ∧
      SubroutineStop s0 sf := by
  obtain ⟨hRun, hSp, γ, tp, x, R, hSat⟩ := hPre
  obtain ⟨sf, huntil, hstop, _⟩ :=
    real_subroutine_run_of_stripS hsvcQ pRxSub_svc hnoQ pRxSub_no_ext
      (pRxSub_rdlRealloc_ok mmpl hMm γ tp)
      (specStripSInvariant_fine_realloc γ mmpl tp cliElfImage.brkStart (keepRxSub_mallocng mmpl hMm)
        cliBudgetLimits)
      (specPreservesFsTrace_realloc _ cliBudgetLimits)
      (fun _ s _ => by cases s; rfl)
      (fun _ _ s0 _ _ => by cases s0; exact id)
      hRun hSp hSat hFr hLr hCode
  exact ⟨sf, huntil, hstop⟩

/-- Local `rfl` mirror of `ElfSlicesPqOomH2KHooks.h2k_withKeepLrFalse`. -/
@[expose] def avoid_withKeepLrFalse {α : Type} (keepSet : BitVec 64 → Bool) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜keepSet (s.readReg64 .lr) = false⌝ ∗ spec.pre x s }

/-- Local `rfl` mirror of `ElfSlicesPqOomH2KHooks.h2k_withKeepLrAndFds`. -/
@[expose] def avoid_withKeepLrAndFds {α : Type} (keepSet : BitVec 64 → Bool) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s => ⌜keepSet (s.readReg64 .lr) = false ∧ FdsGe3Closed s.fs⌝ ∗ spec.pre x s }

private theorem avoid_activeF3CallPre_withKeepLrFalse {α : Type}
    {keepSet : BitVec 64 → Bool} {specOf : GhostName → BitVec 64 → Spec α} {s : State}
    (h : ActiveF3CallPre (fun γ tp => avoid_withKeepLrFalse keepSet (specOf γ tp)) s) :
    ActiveF3CallPre specOf s := by
  obtain ⟨hrun, hsp, γ, tp, x, R, hSat⟩ := h
  dsimp only [avoid_withKeepLrFalse] at hSat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hSat
  exact ⟨hrun, hsp, γ, tp, x, R, hSat.2⟩

private theorem avoid_activeF3CallPre_withKeepLrAndFds {α : Type}
    {keepSet : BitVec 64 → Bool} {specOf : GhostName → BitVec 64 → Spec α} {s : State}
    (h : ActiveF3CallPre (fun γ tp => avoid_withKeepLrAndFds keepSet (specOf γ tp)) s) :
    ActiveF3CallPre specOf s := by
  obtain ⟨hrun, hsp, γ, tp, x, R, hSat⟩ := h
  dsimp only [avoid_withKeepLrAndFds] at hSat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hSat
  exact ⟨hrun, hsp, γ, tp, x, R, hSat.2⟩

private theorem avoid_activeF3CallPre_of_f3LinkedCallHook_noException {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α} {fallback : State → State} {a : State}
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback a).status ≠ .Exception msg) :
    ActiveF3CallPre specOf a := by
  classical
  by_contra hn
  apply hnoex "ghost-hook precondition violated"
  unfold f3LinkedCallHook
  simp [hn]

private theorem replay_f3LinkedCallHook_below4b0000 {α β : Type}
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    {stubPc entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α}
    {specOf' : GhostName → BitVec 64 → Spec β}
    {fallback : State → State}
    (hStub : StubReachesTargetOn (F3CodeInv mpl mmpl) P stubPc entryTarget)
    (hPreImp : ∀ s : State, ActiveF3CallPre specOf' s → ActiveF3CallPre specOf s)
    (hActiveSub : ∀ {s0 : State},
      ActiveF3CallPre specOf s0 →
      ExecFrozen s0.mem →
      hole2_keepSub (s0.readReg64 .lr) = false →
      f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem) →
      ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg entryTarget s0)
    (hAllRxSub : ∀ {s0 : State},
      ActiveF3CallPre specOf s0 →
      ExecFrozen s0.mem →
      keepRxSub (s0.readReg64 .lr) = false →
      pRxSub.CodeLoaded (stripExecOutside keepRxSub s0.mem) →
      ∀ (Q : Program), Q.svc = Syscall.standard →
        (∀ pc : BitVec 64, keepRxSub pc = true → Q.externAt? pc = none) →
        ∃ sf : State,
          StepsUntil Q (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
          SubroutineStop s0 sf)
    {u : State}
    (hpc : u.pc = stubPc)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg entryTarget specOf' fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps P u
      (f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg entryTarget specOf' fallback u) := by
  classical
  have hActPre' : ActiveF3CallPre specOf' u :=
    avoid_activeF3CallPre_of_f3LinkedCallHook_noException hnoex
  have hActPre : ActiveF3CallPre specOf u := hPreImp u hActPre'
  have hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub u.mem) :=
    h2cl_f3CodeInv_rxProg_keepSub hInv
  have hReal : ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg entryTarget u :=
    hActiveSub hActPre hFr hlr hCodeSub
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hfu :
      f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg entryTarget specOf' fallback u =
        Classical.choose hReal.2.2.2 := by
    unfold f3LinkedCallHook
    simp only [hActPre', hReal, ↓reduceDIte]
  have hCodeRxSub : pRxSub.CodeLoaded (stripExecOutside keepRxSub u.mem) :=
    strip_codeLoaded_f3 (pRxSub_codeLoaded_of_f3TrialRxProg hInv.rxCode)
  have hlrRxSub : keepRxSub (u.readReg64 .lr) = false :=
    keepRxSub_false_of_hole2_keepSub_false hlr
  have hvis := stepsVisitedIn_of_allProg (D := keepRxSub) (P1 := hole2_emptyProg)
    (fun pc _ => h2sl_emptyProg_externAt pc)
    (fun Q hsvcQ hnoQ =>
      hAllRxSub hActPre hFr hlrRxSub hCodeRxSub Q (hsvcQ.trans h2sl_emptyProg_svc) hnoQ)
    hchoose.1
  have hBody : Steps P (u.setPC entryTarget) (Classical.choose hReal.2.2.2) :=
    stepsUntil_noExtern_lift_of_visitedIn
      (D := keepRxSub) (P1 := hole2_emptyProg) (P2 := P)
      (h2sl_emptyProg_svc.trans hsvc.symm)
      (fun pc _ => h2sl_emptyProg_externAt pc)
      (fun pc hk => noExtern_keepRxSub hLs W hextBelow pc hk)
      hvis hchoose.2.1
  rw [hfu]
  exact (hStub u hpc hrun hFr hInv).trans hBody

/-! ## 5. `pRxSub` 9-Block `musl` Syscalls + `readFile` / `readStdin` Replays and Main Theorem -/

section PRxSubMuslPriv

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

private def prx_musl_muslFullMpl : MultiPlacement where
  base i :=
    [0x476a94#64, 0x476c3c#64, 0x479348#64, 0x47936c#64, 0x47937c#64,
     0x479380#64, 0x4793c4#64, 0x4793f8#64, 0x476ba0#64, 0x4b0000#64, 0x4b1000#64].getD i 0#64
  ρ s :=
    if s == "muslEmptyCStr" then 0x4b2000#64
    else if s == "__procfdname" then 0x4b3000#64
    else if s == "fstat" then 0x4b0000#64
    else if s == "fstatat" then 0x4b1000#64
    else 0#64

private theorem prx_musl_muslFullMpl_placeable :
    muslSysPlacedLib.Placeable prx_musl_muslFullMpl :=
  muslSysPlacedLib.placeable_of_checkPlaceable (by rfl_kernel)

@[reducible] private local instance prx_musl_instMuslSysPlacement : MuslSysPlacement where
  mpl := prx_musl_muslFullMpl
  placeable := prx_musl_muslFullMpl_placeable

private def prx_musl_musl9Lib : MultiPlacedLib where
  name := "musl_sys"
  blocks := [
    muslBlk00_errno_location, muslBlk01_syscall_ret, muslBlk02_sccp,
    muslBlk03_syscall_cp, muslBlk04_aio_close, muslBlk05_close,
    muslBlk06_read, muslBlk07_write, muslBlk08_open]
  data := []
  exports := [
    "___errno_location", "__errno_location", "__syscall_ret",
    "__syscall_cp", "__aio_close", "close", "read", "write", "open"]

private theorem prx_musl_musl9_placeable :
    prx_musl_musl9Lib.Placeable prx_musl_muslFullMpl :=
  prx_musl_musl9Lib.placeable_of_checkPlaceable (by rfl_kernel)

private theorem prx_musl_progContainsMusl9 :
    ProgContainsMultiLib prx_musl_musl9Lib pRxSub prx_musl_muslFullMpl :=
  progContainsMultiLib_of_wordTree rxSubWords wtRxSub_eq wtRxSub_size
    prx_musl_musl9_placeable pRxSub_svc pRxSub_no_ext
    (by rw [pRxSub_base]; rfl_kernel)

private theorem prx_musl_musl9_resolve_eq :
    prx_musl_musl9Lib.resolve prx_musl_muslFullMpl =
      muslSysPlacedLib.resolve prx_musl_muslFullMpl := by
  funext sym
  unfold MultiPlacedLib.resolve lookupBlockSym prx_musl_musl9Lib muslSysPlacedLib
  dsimp only [lookupBlockSymAux]
  cases lookup sym muslBlk00_errno_location.symbols <;> try rfl
  cases lookup sym muslBlk01_syscall_ret.symbols <;> try rfl
  cases lookup sym muslBlk02_sccp.symbols <;> try rfl
  cases lookup sym muslBlk03_syscall_cp.symbols <;> try rfl
  cases lookup sym muslBlk04_aio_close.symbols <;> try rfl
  cases lookup sym muslBlk05_close.symbols <;> try rfl
  cases lookup sym muslBlk06_read.symbols <;> try rfl
  cases lookup sym muslBlk07_write.symbols <;> try rfl
  cases lookup sym muslBlk08_open.symbols <;> try rfl
  dsimp only [prx_musl_muslFullMpl, muslBlk09_fstat, muslBlk10_fstatat, lookup]
  by_cases h9 : (sym == "fstat") = true
  · rcases beq_iff_eq.mp h9 with rfl; decide
  · by_cases h10 : (sym == "fstatat") = true
    · rcases beq_iff_eq.mp h10 with rfl; decide
    · have h9f : ("fstat" == sym) = false :=
        beq_eq_false_iff_ne.mpr (fun h => h9 (beq_iff_eq.mpr h.symm))
      have h10f : ("fstatat" == sym) = false :=
        beq_eq_false_iff_ne.mpr (fun h => h10 (beq_iff_eq.mpr h.symm))
      have h9f' : (sym == "fstat") = false := Bool.eq_false_iff.mpr h9
      have h10f' : (sym == "fstatat") = false := Bool.eq_false_iff.mpr h10
      simp only [List.find?, h9f, h10f, h9f', h10f', Option.map]

private theorem prx_musl_musl9_blockPlacement_eq (i : Nat) :
    prx_musl_musl9Lib.blockPlacement prx_musl_muslFullMpl i =
      muslSysPlacedLib.blockPlacement prx_musl_muslFullMpl i := by
  simp only [MultiPlacedLib.blockPlacement, prx_musl_musl9_resolve_eq]

private theorem prx_musl_musl9_blockProgram_eq (i : Nat) (lib : PlacedLib) (pl : Placement)
    (ht : (prx_musl_musl9Lib.blockLib i).text = lib.text)
    (hpl : muslSysPlacedLib.blockPlacement prx_musl_muslFullMpl i = pl) :
    prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl i =
      (lib.program pl).rebase pl.base (fun _ => none) := by
  rw [← placed_program_rebase_self lib pl]
  unfold MultiPlacedLib.blockProgram PlacedLib.program Program.rebase
  rw [ht, prx_musl_musl9_blockPlacement_eq i, hpl]

@[local simp] private theorem prx_musl_lk_errno :
    lookupBlockSymAux "___errno_location" 0 muslSysPlacedLib.blocks = some (0, 0) := by decide
@[local simp] private theorem prx_musl_lk_sysret :
    lookupBlockSymAux "__syscall_ret" 0 muslSysPlacedLib.blocks = some (1, 0) := by decide
@[local simp] private theorem prx_musl_lk_sccp :
    lookupBlockSymAux "__syscall_cp" 0 muslSysPlacedLib.blocks = some (3, 0) := by decide
@[local simp] private theorem prx_musl_lk_aioclose :
    lookupBlockSymAux "__aio_close" 0 muslSysPlacedLib.blocks = some (4, 0) := by decide
@[local simp] private theorem prx_musl_muslSysMpl_eq :
    MuslSysPlacement.mpl = prx_musl_muslFullMpl := rfl
@[local simp] private theorem prx_musl_muslFullMpl_base0 :
    prx_musl_muslFullMpl.base 0 = 0x476a94#64 := rfl
@[local simp] private theorem prx_musl_muslFullMpl_base1 :
    prx_musl_muslFullMpl.base 1 = 0x476c3c#64 := rfl
@[local simp] private theorem prx_musl_muslFullMpl_base2 :
    prx_musl_muslFullMpl.base 2 = 0x479348#64 := rfl
@[local simp] private theorem prx_musl_muslFullMpl_base3 :
    prx_musl_muslFullMpl.base 3 = 0x47936c#64 := rfl
@[local simp] private theorem prx_musl_muslFullMpl_base4 :
    prx_musl_muslFullMpl.base 4 = 0x47937c#64 := rfl
@[local simp] private theorem prx_musl_muslFullMpl_base5 :
    prx_musl_muslFullMpl.base 5 = 0x479380#64 := rfl
@[local simp] private theorem prx_musl_muslFullMpl_base6 :
    prx_musl_muslFullMpl.base 6 = 0x4793c4#64 := rfl
@[local simp] private theorem prx_musl_muslFullMpl_base7 :
    prx_musl_muslFullMpl.base 7 = 0x4793f8#64 := rfl
@[local simp] private theorem prx_musl_muslFullMpl_base8 :
    prx_musl_muslFullMpl.base 8 = 0x476ba0#64 := rfl

private theorem prx_musl_condHI_adds_4096_false {a : BitVec 64} (ha : a.toNat ≤ 2 ^ 64 - 4096) :
    ConditionHolds .HI (addsPState64 a 4096#64) = false := by
  rw [conditionHolds_hi_addsPState64]
  by_cases heq : a = -4096#64
  · subst heq; decide
  · have hlt_strict : a.toNat < 2 ^ 64 - 4096 := by
      refine Nat.lt_of_le_of_ne ha fun h => heq (BitVec.eq_of_toNat_eq ?_)
      have : (-4096#64 : BitVec 64).toNat = 2 ^ 64 - 4096 := by decide
      omega
    have hadd : (a + 4096#64).toNat = a.toNat + 4096 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : 4096 % 2 ^ 64 = 4096 := by decide
      rw [this, Nat.mod_eq_of_lt (by omega)]
    have hult : BitVec.ult (a + 4096#64) a = false := by
      simp only [BitVec.ult, hadd, decide_eq_false_iff_not]; omega
    rw [hult, Bool.false_and]

private theorem prx_musl_condHI_adds_4096_true {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ConditionHolds .HI (addsPState64 (-BitVec.ofNat 64 err) 4096#64) = true := by
  rw [conditionHolds_hi_addsPState64]
  have herr_mod : err % 2 ^ 64 = err := Nat.mod_eq_of_lt (by omega)
  have h4096_mod : 4096 % 2 ^ 64 = 4096 := by decide
  have hneg : (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
    rw [BitVec.toNat_neg, BitVec.toNat_ofNat, herr_mod, Nat.mod_eq_of_lt (by omega)]
  have hsum : (-BitVec.ofNat 64 err + 4096#64).toNat = 4096 - err := by
    rw [BitVec.toNat_add, hneg, BitVec.toNat_ofNat, h4096_mod]
    have : 2 ^ 64 - err + 4096 = 2 ^ 64 + (4096 - err) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hult : BitVec.ult (-BitVec.ofNat 64 err + 4096#64) (-BitVec.ofNat 64 err) = true := by
    simp only [BitVec.ult, hneg, hsum, decide_eq_true_eq]; omega
  have hne : (-BitVec.ofNat 64 err + 4096#64 != 0#64) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro heq
    have := congrArg BitVec.toNat heq
    simp only [hsum, BitVec.toNat_ofNat] at this
    omega
  rw [hult, hne]; rfl

private theorem prx_musl_neg_truncate32_neg_ofNat (err : Nat) :
    0#32 - (-BitVec.ofNat 64 err).truncate 32 = BitVec.ofNat 32 err := by bv_omega

private def prx_musl_muslSyscallRetOkSpec : Spec (BitVec 64) where
  pre := fun retVal s0 =>
    ⌜s0.readReg64 .x0 = retVal ∧ retVal.toNat ≤ 2 ^ 64 - 4096⌝ ∗ stackAt s0.sp 32
  post := fun retVal s0 sf =>
    ⌜sf.readReg64 .x0 = retVal ∧ StdStatePreserved s0 sf⌝ ∗ stackAt s0.sp 32
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private def prx_musl_muslSyscallRetErrSpec : Spec (Nat × BitVec 32) where
  pre := fun (err, e0) s0 =>
    ⌜s0.readReg64 .x0 = -BitVec.ofNat 64 err ∧ 1 ≤ err ∧ err ≤ 4095⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (err, _) s0 sf =>
    ⌜sf.readReg64 .x0 = -1#64 ∧ StdStatePreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ BitVec.ofNat 32 err))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private def prx_musl_muslAioCloseSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = s0.readReg64 .x0 ∧ sf.mem = s0.mem ∧ StdStatePreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem prx_musl_muslErrnoLocation_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 0)
      (prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "___errno_location")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl muslErrnoLocationSpec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 0 =
    muslSysPC00.rebase muslSysPl00.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 0 muslSysLib00 muslSysPl00 rfl rfl]
  rw [show prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "___errno_location" = muslSysPl00.base from rfl]
  wp_entry; wp_sym_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm],
    by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp only [wp_norm, arm64_norm, muslErrnoAddr], rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩

private theorem prx_musl_muslAioClose_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 4)
      (prx_musl_musl9Lib.resolve prx_musl_muslFullMpl "__aio_close")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl prx_musl_muslAioCloseSpec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 4 =
    muslSysPC04.rebase muslSysPl04.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 4 muslSysLib04 muslSysPl04 rfl rfl]
  rw [show prx_musl_musl9Lib.resolve prx_musl_muslFullMpl "__aio_close" = muslSysPl04.base from rfl]
  wp_entry; wp_sym_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm],
    by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp only [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    by simpa using hmem⟩

private theorem prx_musl_muslSyscallRetOk_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 1)
      (prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "__syscall_ret")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl prx_musl_muslSyscallRetOkSpec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 1 =
    muslSysPC01.rebase muslSysPl01.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 1 muslSysLib01 muslSysPl01 rfl rfl]
  rw [show prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "__syscall_ret" = muslSysPl01.base from rfl]
  wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepConj_assoc]; repeat (apply SepWP.exists_left; intro)
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps 2
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm2
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm2
  wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = false := prx_musl_condHI_adds_4096_false ‹_›
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]; wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp_all [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp only [wp_norm, arm64_norm, hm2, hm1]⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [wp_norm, arm64_norm]

private theorem prx_musl_muslSyscallRetErr_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 1)
      (prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "__syscall_ret")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl prx_musl_muslSyscallRetErrSpec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 1 =
    muslSysPC01.rebase muslSysPl01.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 1 muslSysLib01 muslSysPl01 rfl rfl]
  rw [show prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "__syscall_ret" = muslSysPl01.base from rfl]
  wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps 2
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm2
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm2
  wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = true := prx_musl_condHI_adds_4096_true ‹_› ‹_›
  simp only [hcond, ↓reduceIte]; wp_sym_steps
  wp_call_block prx_musl_muslErrnoLocation_blk_ok ()
  rcases ‹StdStatePreserved _ sf› with ⟨hbrk_sf, hfs_sf, htpidr_sf, htr_sf, hoidx_sf, horacle_sf, hphys_sf, _⟩
  simp only [wp_norm, arm64_norm] at hbrk_sf hfs_sf htpidr_sf htr_sf hoidx_sf horacle_sf hphys_sf
  simp only [muslErrnoAddr] at *; wp_sym_steps 3
  apply step_str32_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm3
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm3
  wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, ‹sf.status = .Running›])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp only [wp_norm, arm64_norm]; rfl, by simp only [wp_norm, arm64_norm, hbrk_sf.symm],
      by simp only [wp_norm, arm64_norm, hfs_sf.symm], by simp only [wp_norm, arm64_norm, htpidr_sf.symm],
      by simp only [wp_norm, arm64_norm, htr_sf.symm], by simp only [wp_norm, arm64_norm, hoidx_sf.symm],
      by simp only [wp_norm, arm64_norm, horacle_sf.symm], by simp only [wp_norm, arm64_norm, hphys_sf.symm],
      fun _ => by simp only [wp_norm, arm64_norm, hm3, ‹sf.mem = _›, hm2, hm1]⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm, htpidr_sf.symm, prx_musl_neg_truncate32_neg_ofNat]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem prx_musl_muslSyscallCp_step {s0 : State} {target_pc : BitVec 64}
    {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s0.pc = muslSysPl03.base) (hrun : s0.status = .Running)
    (hcl : prx_musl_musl9Lib.CodeLoaded prx_musl_muslFullMpl s0.mem)
    (hnext : SepWP (muslSysPC02.rebase muslSysPl02.base (fun _ => none)) target_pc
      ((((((((s0.writeReg64 .x8 (s0.readReg64 .x0)).writeReg64 .x0 (s0.readReg64 .x1)).writeReg64
        .x1 (s0.readReg64 .x2)).writeReg64 .x2 (s0.readReg64 .x3)).writeReg64
        .x3 (s0.readReg64 .x4)).writeReg64 .x4 (s0.readReg64 .x5)).writeReg64
        .x5 (s0.readReg64 .x6)).setPC (muslSysPl02.base + 28#64)) P post) :
    SepWP (muslSysPC03.rebase muslSysPl03.base (fun _ => none)) target_pc s0 P post := by
  wp_sym_steps
  have hsccp : muslSysPl03.base + (muslSysPl03.ρ "sccp" - muslSysPl03.base) = muslSysPl02.base := rfl
  rw [hsccp]
  refine SepWP.of_sameHooks (P := muslSysPC03.rebase muslSysPl03.base (fun _ => none))
    (Q := muslSysPC02.rebase muslSysPl02.base (fun _ => none))
    (by intro pc
        change ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 2).rebase muslSysPl02.base (fun _ => none)).externAt? pc =
          ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 3).rebase muslSysPl03.base (fun _ => none)).externAt? pc
        simp only [MultiPlacedLib.externAt?_blockProgram_rebase_none])
    rfl (prx_musl_musl9_blockProgram_eq 2 muslSysLib02 muslSysPl02 rfl rfl ▸ hcl 2 (by decide)) ?_
  wp_sym_steps
  simpa only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8] using hnext

private def prx_musl_muslSccpCloseLocalSpec : Spec (BitVec 64 × FdEntry) where
  pre := fun (fd, desc) s0 =>
    ⌜s0.readReg64 .x0 = 57#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind = .localFile ∨ desc.kind = .localDir)⌝
  post := fun (fd, _) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.fs = s0.fs.setFd fd none ∧
      sf.mem = s0.mem ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem prx_musl_muslSccpCloseLocal_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 3)
      (prx_musl_musl9Lib.resolve prx_musl_muslFullMpl "__syscall_cp")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl prx_musl_muslSccpCloseLocalSpec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show prx_musl_musl9Lib.resolve prx_musl_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  refine prx_musl_muslSyscallCp_step hpc hrun h ?_
  refine step_svc_close_fd_local (fd := a_1) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4 h_5 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      rfl, by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem prx_musl_muslClose48Local_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 5)
      (prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "close")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl muslClose48LocalSpec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 5 =
    muslSysPC05.rebase muslSysPl05.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 5 muslSysLib05 muslSysPl05 rfl rfl]
  rw [show prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "close" = muslSysPl05.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 32 2 (by decide)]
  cells_unfold; simp only [sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps
  wp_call_block_keep prx_musl_muslAioClose_blk_ok ()
  rcases ‹StdStatePreserved _ _› with ⟨hfs1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at hfs1 htr1 htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block_keep prx_musl_muslSccpCloseLocal_blk_ok (a_1, a_rest)
  rcases ‹SyscallPreserved _ _› with ⟨htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at htp2 hsig2 hb2 hbs2 hp2 hmp2
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block prx_musl_muslSyscallRetOk_blk_ok 0#64
  rcases ‹StdStatePreserved _ _› with ⟨hfs3, htr3, htp3, hsig3, hb3, hbs3, hp3, hmp3⟩
  simp only [wp_norm, arm64_norm, htp2, hsig2, hb2, hbs2, hp2, hmp2] at hfs3 htr3 htp3 hsig3 hb3 hbs3 hp3 hmp3
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
      by simp [wp_norm, arm64_norm, *], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
        stackAt_split_cells s0.sp 32 2 (by decide)]
      cells_unfold; simp only [wp_norm, arm64_norm, *]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem prx_musl_readReg32_slt_zero_false {w : BitVec 32} {fd : BitVec 64}
    (hfd : w.zeroExtend 64 = fd) (hlt : fd.toNat < 2 ^ 31) :
    w.slt 0#32 = false := by
  subst hfd
  have hw : w.toNat < 2 ^ 31 := by
    have := w.isLt
    simp only [BitVec.zeroExtend, BitVec.toNat_setWidth] at hlt
    omega
  unfold BitVec.slt BitVec.toInt
  simp; omega

private theorem prx_musl_step_svc_read_dir {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd buf count : BitVec 64} {desc : FdEntry} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 63#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localDir)
    (hrd : desc.accMode.canRead = true)
    (hnext :
      let s' := (s.writeReg64 .x0 (-BitVec.ofNat 64 (dirReadErrnoNat buf count desc.offset))).setPC (pc + 4#64)
      SepWP prog target_pc s' P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execRead s) :
    SepWP prog target_pc s P post oom :=
  LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose.step_svc_read_dir
    hpc hrun hfetch hx8 hfd hfd_lt hbuf hcnt hopen hkind hrd hnext hsvc

private def prx_musl_muslSccpReadDirSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry) where
  pre := fun (fd, buf, count, desc) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧
      s0.fs.fds fd = some desc ∧
      desc.kind = .localDir ∧
      desc.accMode.canRead = true⌝
  post := fun (_, buf, count, desc) s0 sf =>
    ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 (dirReadErrnoNat buf count desc.offset) ∧
      sf.fs = s0.fs ∧
      sf.mem = s0.mem ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem prx_musl_muslSccpReadDir_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 3)
      (prx_musl_musl9Lib.resolve prx_musl_muslFullMpl "__syscall_cp")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl prx_musl_muslSccpReadDirSpec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show prx_musl_musl9Lib.resolve prx_musl_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  refine prx_musl_muslSyscallCp_step hpc hrun h ?_
  refine prx_musl_step_svc_read_dir (fd := a_1) (buf := a) (count := a_2) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4
    (by simp [wp_norm, arm64_norm, h_5]) (by simp [wp_norm, arm64_norm, h_6])
    h_7 h_8 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      rfl, by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
      by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem prx_musl_muslReadDir32_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 6)
      (prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "read")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl muslReadDir32Spec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 6 =
    muslSysPC06.rebase muslSysPl06.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 6 muslSysLib06 muslSysPl06 rfl rfl]
  rw [show prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "read" = muslSysPl06.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps
  wp_call_block_keep prx_musl_muslSccpReadDir_blk_ok (a_1, a, a_2, a_3)
  rcases ‹SyscallPreserved _ sf› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  have htp_e : muslErrnoAddr s0 = muslErrnoAddr sf := by unfold muslErrnoAddr; rw [htp1]
  wp_conv_pre => rw [htp_e]
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ a_rest_1))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have ⟨h1_err, h2_err⟩ := dirReadErrnoNat_bounds a a_2 a_3.offset
  wp_call_block prx_musl_muslSyscallRetErr_blk_ok (dirReadErrnoNat a a_2 a_3.offset, a_rest_1)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], dirReadErrno32_cases a a_2 a_3.offset,
      dirReadErrno32_ne_eintr a a_2 a_3.offset, by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [dirReadErrno32, muslErrnoAddr, wp_norm, arm64_norm, *] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private def prx_musl_muslSccpReadFileOrStdioSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, oldBuf) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧
      count.toNat ≤ Arm64.MAX_RW_COUNT ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      (desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE) ∧
      oldBuf.length = count.toNat ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind == .localFile || desc.kind == .stdio) = true ∧
      desc.accMode.canRead = true⌝ ∗
    (buf ↦ₛ oldBuf)
  post := fun (fd, buf, count, desc, oldBuf) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take count.toNat
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝ ∗
    (buf ↦ₛ (chunk ++ oldBuf.drop chunk.length))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem prx_musl_muslSccpReadFileOrStdio_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 3)
      (prx_musl_musl9Lib.resolve prx_musl_muslFullMpl "__syscall_cp")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl prx_musl_muslSccpReadFileOrStdioSpec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show prx_musl_musl9Lib.resolve prx_musl_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  refine prx_musl_muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine SepWP.step_svc_read (fd := a_1) (buf := a) (count := a_2) (desc := a_3) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x0 = 63#64›])
    (by simpa [wp_norm, arm64_norm] using ‹(s0.readReg32 .x1).zeroExtend 64 = a_1›)
    ‹a_1.toNat < 2 ^ 31›
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x2 = a›])
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x3 = a_2›])
    ‹a_rest_1.length = a_2.toNat›
    ‹s0.fs.fds a_1 = some a_3›
    ‹(a_3.kind == .localFile || a_3.kind == .stdio) = true›
    ‹a_3.accMode.canRead = true› ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, ‹s0.readReg64 .x0 = 63#64›])
    ‹a_2.toNat ≤ Arm64.MAX_RW_COUNT›
    ‹a.toNat + a_2.toNat ≤ Arm64.USER_VA_LIMIT›
    ‹a_3.kind = .localFile → a_3.offset + a_2.toNat ≤ Arm64.MAX_LFS_FILESIZE›
  dsimp only; rw [sepConj_emp]
  (conv => arg 3; simp only [wp_norm, arm64_norm])
  (conv => arg 4; simp only [wp_norm, arm64_norm, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8])
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by cases a_3; simp_all [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp [wp_norm, arm64_norm]⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem prx_musl_muslReadFileOrStdio32_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 6)
      (prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "read")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl muslReadFileOrStdio32Spec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 6 =
    muslSysPC06.rebase muslSysPl06.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 6 muslSysLib06 muslSysPl06 rfl rfl]
  rw [show prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "read" = muslSysPl06.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps
  wp_call_block_keep prx_musl_muslSccpReadFileOrStdio_blk_ok (a_1, a, a_2, a_3, a_rest_1)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗
    (a ↦ₛ (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat ++
      a_rest_1.drop (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hchunk_lt : (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length < 2 ^ 63 := by
    simp only [List.length_take]
    have := ‹a_2.toNat ≤ Arm64.MAX_RW_COUNT›
    simp only [Arm64.MAX_RW_COUNT] at this
    omega
  have hchunk_ok := ofNat64_le_maxSyscallOk hchunk_lt
  wp_call_block prx_musl_muslSyscallRetOk_blk_ok
    (BitVec.ofNat 64 (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1]
    at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], ?_, by simp [wp_norm, arm64_norm, *], ?_⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    · simp_all [wp_norm, arm64_norm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private def prx_musl_muslSccpOpenatLocalExecSpec :
    Spec (BitVec 64 × String × BitVec 32 × FsState × List TraceEvent × OpenatLocalOutcome) where
  pre := fun (cstr, path, flags, fs0, tr0, out) s0 =>
    ⌜s0.readReg64 .x0 = 56#64 ∧
      s0.readReg32 .x1 = AT_FDCWD_W32 ∧
      s0.readReg64 .x2 = cstr ∧
      s0.readReg32 .x3 = flags ||| O_LARGEFILE_W32 ∧
      s0.fs = fs0 ∧
      s0.trace = tr0 ∧
      ValidCPath path ∧
      OpenatLocalExecSpec fs0 tr0 path flags out⌝ ∗
    (cstr ↦ₛ cstrBytes path)
  post := fun (cstr, path, _, fs0, tr0, out) s0 sf =>
    match out with
    | .ok fd desc fs' traceExtra =>
      ⌜sf.readReg64 .x0 = fd ∧
        fd.toNat < 2 ^ 31 ∧
        fs'.fds fd = some desc ∧
        (desc.kind = .localFile ∨ desc.kind = .localDir) ∧
        desc.cloexec = true ∧
        sf.fs = fs' ∧
        sf.mem = s0.mem ∧
        sf.trace = tr0 ++ traceExtra ∧
        SyscallPreserved s0 sf⌝ ∗
      (cstr ↦ₛ cstrBytes path)
    | .err errPred =>
      ∃∗ errno : Nat,
        ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 errno ∧
          1 ≤ errno ∧ errno ≤ 4095 ∧ errPred errno ∧
          sf.fs = fs0 ∧
          sf.mem = s0.mem ∧
          sf.trace = tr0 ∧
          SyscallPreserved s0 sf⌝ ∗
        (cstr ↦ₛ cstrBytes path)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem prx_musl_muslSccpOpenatLocalExec_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 3)
      (prx_musl_musl9Lib.resolve prx_musl_muslFullMpl "__syscall_cp")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl prx_musl_muslSccpOpenatLocalExecSpec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show prx_musl_musl9Lib.resolve prx_musl_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  obtain ⟨hlen_p, hval_p⟩ := h_8
  refine prx_musl_muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine step_svc_openat_rw (path := a) (fname := a_1) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simp [wp_norm, arm64_norm, h_4])
    hlen_p hval_p (fun hcs => ?_)
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  rw [sepConj_emp]
  have hexec := h_1 hcs (by simp [wp_norm, arm64_norm, h_6]) (by simp [wp_norm, arm64_norm, h_7])
    (by simpa [wp_norm, arm64_norm] using h_3) (by simpa [wp_norm, arm64_norm] using h_5)
  cases a_rest with
  | ok fd desc fs' traceExtra =>
    dsimp only [OpenatLocalExecSpec] at hexec
    rcases hexec with ⟨hfd_lt, hfds, hkind, hclo, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [prx_musl_muslSccpOpenatLocalExecSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], hfd_lt, hfds, hkind, hclo,
        by simp [wp_norm, arm64_norm, State.appendTrace], rfl,
        by simp [wp_norm, arm64_norm, State.appendTrace, h_7], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [wp_norm, arm64_norm, State.appendTrace, Arm64.calleeSavedVRegs]
  | err errPred =>
    dsimp only [OpenatLocalExecSpec] at hexec
    rcases hexec with ⟨errno, h1, h2, hpred, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [prx_musl_muslSccpOpenatLocalExecSpec]
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], h1, h2, hpred,
        by simp [wp_norm, arm64_norm, h_6], rfl,
        by simp [wp_norm, arm64_norm, h_7], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem prx_musl_truncate32_and64 (x y : BitVec 64) :
    (x &&& y).truncate 32 = x.truncate 32 &&& y.truncate 32 := by ext i hi; simp

private theorem prx_musl_getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    fd.getLsbD 31 = false := by
  rw [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow hfd

private theorem prx_musl_truncate32_getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd.truncate 32).getLsbD 31 = false := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, prx_musl_getLsbD_31_false_of_lt hfd]; decide

private theorem prx_musl_mask32_or_zero_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 ||| 0#64) = fd := by
  simp only [BitVec.ushiftRight_zero, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem prx_musl_setWidth64_setWidth32_and_mask_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.setWidth 32 fd) &&& 4294967295#64 = fd := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
  rw [h1]
  simpa [BitVec.ushiftRight_zero, BitVec.or_zero] using prx_musl_mask32_or_zero_of_lt31 hfd

private theorem prx_musl_sxtw64_eq_self_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 |||
      (if fd.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = fd := by
  rw [prx_musl_getLsbD_31_false_of_lt hfd]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.or_zero, BitVec.ushiftRight_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem prx_musl_neg_ofNat_toNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
  rw [BitVec.toNat_neg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem prx_musl_getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).getLsbD 31 = true := by
  rw [BitVec.getLsbD, prx_musl_neg_ofNat_toNat h1 h2, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hdiv : (2 ^ 64 - err) / 2 ^ 31 = 2 ^ 33 - 1 := by omega
  rw [hdiv]; decide

private theorem prx_musl_truncate32_getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err).truncate 32).getLsbD 31 = true := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, prx_musl_getLsbD_31_neg_ofNat h1 h2]; decide

private theorem prx_musl_sxtw_neg_of_hi_ones {v : BitVec 64} (h : v >>> 32 = 0xffffffff#64) :
    (v >>> 0 &&& 4294967295#64 ||| 0xffffffffffffffff#64 &&& 0xffffffff00000000#64) = v := by
  bv_robdd

private theorem prx_musl_sxtw64_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err) >>> 0 &&& 4294967295#64 |||
      (if (-BitVec.ofNat 64 err).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = -BitVec.ofNat 64 err := by
  rw [prx_musl_getLsbD_31_neg_ofNat h1 h2]
  simp only [↓reduceIte]
  refine prx_musl_sxtw_neg_of_hi_ones (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_ushiftRight, prx_musl_neg_ofNat_toNat h1 h2, Nat.shiftRight_eq_div_pow]
  have hmax : (4294967295#64 : BitVec 64).toNat = 2 ^ 32 - 1 := by decide
  rw [hmax]; omega

private theorem prx_musl_zeroExtend64_getLsbD_6 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 6 = flags.getLsbD 6 := by simp

private theorem prx_musl_zeroExtend64_getLsbD_19 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 19 = flags.getLsbD 19 := by simp

private theorem prx_musl_tmpfile_mask_eq_zero {flags : BitVec 32} (h : flags &&& 0x00404000#32 = 0#32) :
    (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = 0#32 := by
  have heq : (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = flags &&& 0x00404000#32 := by bv_bits
  rw [heq, h]

private theorem prx_musl_or_largefile_sxtw_truncate32 (flags : BitVec 32) :
    (((flags.zeroExtend 64 ||| 131072#64) >>> 0 &&& 4294967295#64 |||
      (if (flags.zeroExtend 64 ||| 131072#64).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64).truncate 32) = flags ||| O_LARGEFILE_W32 := by
  rw [sxtw64_truncate32]
  change (flags.zeroExtend 64 ||| 131072#64).truncate 32 = flags ||| 0x00020000#32
  bv_bits

set_option maxHeartbeats 400000 in
private theorem prx_musl_muslOpenNoCreatCloexecLocalExec_blk_ok :
    subroutine_ok (prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 8)
      (prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "open")
      (prx_musl_musl9Lib.withCodeLoaded prx_musl_muslFullMpl muslOpenNoCreatCloexecLocalExecSpec) := by
  rw [show prx_musl_musl9Lib.blockProgram prx_musl_muslFullMpl 8 =
    muslSysPC08.rebase muslSysPl08.base (fun _ => none) from prx_musl_musl9_blockProgram_eq 8 muslSysLib08 muslSysPl08 rfl rfl]
  rw [show prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "open" = muslSysPl08.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 112 = stackAt (s0.sp - 80#64) 32 ∗ cells (s0.sp - 80#64) 10 from
      stackAt_split_cells s0.sp 32 10 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps 1
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm2
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm2
  wp_sym_steps 1
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm3
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm3
  (conv => arg 3; simp only [wp_norm, arm64_norm, h_3, prx_musl_zeroExtend64_getLsbD_6, h_4])
  wp_sym_steps 3
  have htmp := prx_musl_tmpfile_mask_eq_zero h_5
  (conv => arg 3; simp only [wp_norm, arm64_norm, prx_musl_truncate32_and64, h_3, htmp])
  wp_sym_steps
  have hcwd : (-100#32 : BitVec 32) = AT_FDCWD_W32 := by decide
  have hflg := prx_musl_or_largefile_sxtw_truncate32 a_2
  have ⟨_, _⟩ := ‹ValidCPath a›
  wp_call_block_keep prx_musl_muslSccpOpenatLocalExec_blk_ok (a_1, a, a_2, s0.fs, s0.trace, a_rest_1)
  cases a_rest_1 with
  | ok fd desc fs' traceExtra =>
    wp_conv_pre => try dsimp only [prx_musl_muslSccpOpenatLocalExecSpec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hx0, hfd_lt, hfds, hkind, hclo, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsvc08 : muslSysPC08.svc = Syscall.standard := rfl
    have hsxtw := prx_musl_sxtw64_eq_self_of_lt31 hfd_lt
    have hmask0 := prx_musl_mask32_or_zero_of_lt31 hfd_lt
    have hfd_ze_mask := prx_musl_setWidth64_setWidth32_and_mask_of_lt31 hfd_lt
    have hfd_ze : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
    have htbnz := prx_musl_getLsbD_31_false_of_lt hfd_lt
    have htbnz32 := prx_musl_truncate32_getLsbD_31_false_of_lt hfd_lt
    wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, hmask0, htbnz, htbnz32])
    wp_sym_steps 2
    simp only [wp_norm, arm64_norm, prx_musl_zeroExtend64_getLsbD_19, h_6]
    have hdesc_eq : ({ desc with cloexec := true } : FdEntry) = desc := by
      cases desc; simp at hclo; subst hclo; rfl
    have hsetfd_eq : fs'.setFd fd (some { desc with cloexec := true }) = fs' := by
      rw [hdesc_eq]; exact FsState.setFd_eq_self hfds
    have h1_clo : (1#64 &&& 1#64 != 0#64) = true := by decide
    wp_sym_steps
    refine step_svc_fcntl_setfd_local (fd := fd) (arg := 1#64) rfl
      (by simp [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hfd_ze]) hfd_lt
      (by simp [wp_norm, arm64_norm, F_SETFD_W32]) (by simp [wp_norm, arm64_norm])
      (by simpa [wp_norm, arm64_norm, hfs1] using hfds) hkind ?_
      (by simp [wp_norm, arm64_norm, *])
    dsimp only
    (conv => arg 3; simp only [wp_norm, arm64_norm, hfs1, h1_clo, hsetfd_eq])
    wp_sym_steps
    have hfd_ok : fd.toNat ≤ 2 ^ 64 - 4096 := by omega
    wp_cut_codeLoaded
    wp_call_block prx_musl_muslSyscallRetOk_blk_ok fd
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecLocalExecSpec]
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp_all [wp_norm, arm64_norm],
        by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt (State.sp s0) 112 =
            stackAt (State.sp s0 - 80#64) 32 ∗ cells (State.sp s0 - 80#64) 10 from
          stackAt_split_cells (State.sp s0) 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]
  | err errPred =>
    wp_conv_pre => try dsimp only [prx_musl_muslSccpOpenatLocalExecSpec]; simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_left; intro errno
    apply SepWP.pure_elim
    rintro ⟨hx0, h1, h2, hpred, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsxtw := prx_musl_sxtw64_neg_ofNat h1 h2
    have htbnz := prx_musl_getLsbD_31_neg_ofNat h1 h2
    have htbnz32 := prx_musl_truncate32_getLsbD_31_neg_ofNat h1 h2
    have htp_e : muslErrnoAddr s0 = muslErrnoAddr sf := by unfold muslErrnoAddr; rw [htp1]
    wp_conv_pre => rw [htp_e]
    wp_cut_codeLoaded; wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, htbnz, htbnz32])
    wp_sym_steps
    wp_call_block prx_musl_muslSyscallRetErr_blk_ok (errno, a_3)
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecLocalExecSpec]
      try rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨h1, h2, hpred, by simp [wp_norm, arm64_norm, *],
        by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *], ?_⟩,
        ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt (State.sp s0) 112 =
            stackAt (State.sp s0 - 80#64) 32 ∗ cells (State.sp s0 - 80#64) 10 from
          stackAt_split_cells (State.sp s0) 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem prx_musl_f3Rx_hooksUnfetched (m : Memory) (_ : pRxSub.CodeLoaded m) :
    pRxSub.HooksUnfetched m :=
  fun _ pc _ he => False.elim (he (pRxSub_no_ext pc))

private theorem prx_musl_muslErrnoLocation_ok :
    subroutine_ok pRxSub 0x476a94#64 muslErrnoLocationSpec := by
  have hfn : prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "___errno_location" = 0x476a94#64 := by decide
  rw [← hfn]
  exact prx_musl_musl9Lib.subroutine_ok_of_pureMem (j := 0) (by decide) prx_musl_muslErrnoLocation_blk_ok
    prx_musl_progContainsMusl9.codeLoaded prx_musl_f3Rx_hooksUnfetched pRxSub_svc

private theorem prx_musl_muslClose48Local_ok :
    subroutine_ok pRxSub 0x479380#64 muslClose48LocalSpec := by
  have hfn : prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "close" = 0x479380#64 := by decide
  rw [← hfn]
  exact prx_musl_musl9Lib.subroutine_ok_of_pureMem (j := 5) (by decide) prx_musl_muslClose48Local_blk_ok
    prx_musl_progContainsMusl9.codeLoaded prx_musl_f3Rx_hooksUnfetched pRxSub_svc

private theorem prx_musl_muslReadDir32_ok :
    subroutine_ok pRxSub 0x4793c4#64 muslReadDir32Spec := by
  have hfn : prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "read" = 0x4793c4#64 := by decide
  rw [← hfn]
  exact prx_musl_musl9Lib.subroutine_ok_of_pureMem (j := 6) (by decide) prx_musl_muslReadDir32_blk_ok
    prx_musl_progContainsMusl9.codeLoaded prx_musl_f3Rx_hooksUnfetched pRxSub_svc

private theorem prx_musl_muslReadFileOrStdio32_ok :
    subroutine_ok pRxSub 0x4793c4#64 muslReadFileOrStdio32Spec := by
  have hfn : prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "read" = 0x4793c4#64 := by decide
  rw [← hfn]
  exact prx_musl_musl9Lib.subroutine_ok_of_pureMem (j := 6) (by decide) prx_musl_muslReadFileOrStdio32_blk_ok
    prx_musl_progContainsMusl9.codeLoaded prx_musl_f3Rx_hooksUnfetched pRxSub_svc

private theorem prx_musl_muslOpenNoCreatCloexecLocalExec_ok :
    subroutine_ok pRxSub 0x476ba0#64 muslOpenNoCreatCloexecLocalExecSpec := by
  have hfn : prx_musl_musl9Lib.fnAddr prx_musl_muslFullMpl "open" = 0x476ba0#64 := by decide
  rw [← hfn]
  exact prx_musl_musl9Lib.subroutine_ok_of_pureMem (j := 8) (by decide)
    prx_musl_muslOpenNoCreatCloexecLocalExec_blk_ok
    prx_musl_progContainsMusl9.codeLoaded prx_musl_f3Rx_hooksUnfetched pRxSub_svc

private theorem prx_musl_muslReadStdin32_ok :
    subroutine_ok pRxSub 0x4793c4#64 muslReadStdin32Spec := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨buf, count, desc, oldBuf⟩ R s0 hpc hrun hpre hsp _hL
  simp only [muslReadStdin32Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hcnt_le, hva_le, hlen, hfds0, hkind, hrd⟩, hm⟩
  have hx0_ze : (s0.readReg32 .x0).zeroExtend 64 = 0#64 := by rw [hx0]; rfl
  have h0_lt : (0#64 : BitVec 64).toNat < 2 ^ 31 := by decide
  have hk_or : (desc.kind == .localFile || desc.kind == .stdio) = true := by rw [hkind]; rfl
  have hlfs : desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE := by
    rw [hkind]; intro h; cases h
  have hfdbytes : s0.fs.fdBytes desc = s0.fs.stdin := by simp only [FsState.fdBytes, hkind]
  refine prx_musl_muslReadFileOrStdio32_ok.mono_outcome (0#64, buf, count, desc, oldBuf) R s0 hpc hrun
    ?_ hsp (fun sf hout => ?_)
  · simp only [muslReadFileOrStdio32Spec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_ze, h0_lt, hx1, hx2, hcnt_le, hva_le, hlfs, hlen, hfds0, hk_or, hrd⟩, hm⟩
  · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [muslReadFileOrStdio32Spec, muslReadStdin32Spec, hfdbytes] using hq
    · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))


end PRxSubMuslPriv

section PRxSubReadsPriv

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

private theorem pRxSub_fineHookAllocEntries_thunks (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      pRxSub f3StubAddrs := by
  have hThunks : RustStdThunkCode pRxSub f3StubAddrs.toRustStd f3RdlAddrs.toRustStd :=
    rustStdThunkCode_of_wordTree rxSubWords wtRxSub_eq wtRxSub_size
      pRxSub_externs_none pRxSub_overrides_none (by rw [pRxSub_base]; rfl_kernel)
  have hShims := pRxSub_seg5ShimBundle.rdlShims
  rw [← h2fsalloc_mng_cAddrs_eq mmpl hMm] at hShims
  exact fineHookRustCliAllocBudgetEntries_thunks
    (pRxSub_progContainsMallocng mmpl hMm) γ tp cliElfImage.brkStart hThunks hShims
    pRxSub_allocMemcpyVm_ok

private theorem pRxSub_stdMemcpy_ok :
    subroutine_ok pRxSub 0x474650#64 stdMemcpySpec :=
  stdMemcpy_ok_of_hasWords pRxSub f3StdLayout.memcpyAddr pRxSub_no_ext
    (hasWords_of_wordTree rxSubWords wtRxSub_eq wtRxSub_size
      (by rw [pRxSub_base]) (by decide) pRxSub_stubs pRxSub_symbols
      (by rfl_kernel))

private theorem pRxSub_noAllocShim_ok :
    subroutine_ok pRxSub 0x474640#64 rustAllocShimVmSpec :=
  rustAllocShimVm_ret_ok pRxSub_seg5ShimBundle.noAllocShimV2

private theorem prx_setFs_appendTrace_nil (s : State) (fs' : FsState) :
    (s.setFs fs').appendTrace [] = s.setFs fs' := by
  cases s; simp only [State.setFs, State.appendTrace, List.append_nil]

private theorem prx_execOpenat_rdonly_cloexec_file_or_emfile {s : State} {path : String}
    {bs : List (BitVec 8)}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (htd : trailingDir path = false)
    (hnorm_ne : normalizePath path ≠ [])
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hfile : s.fs.files path = some (.file bs)) :
    execOpenat s =
      match s.fs.allocFd with
      | none => (s.writeReg64 .x0 (-EMFILE)).advancePC
      | some fd =>
        ((s.setFs (s.fs.setFd fd (some
            { path := path, accMode := .rdonly, append := false, cloexec := true,
              offset := 0, kind := .localFile }))).writeReg64 .x0 fd).advancePC :=
  LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic.execOpenat_rdonly_cloexec_file_or_emfile
    hdfd hflags hcs hne hlead hdot htd hnorm_ne hanc hfile

private theorem prx_execOpenat_of_classifyOpenRdonly_err {s : State} {path : String} {errno : Nat}
    (hpok : PathOk path = true)
    (hmax : ((pathComps path).all fun c => decide (c.length ≤ NAME_MAX)) = true)
    (hcl : classifyOpenRdonly s.fs path = .err errno)
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path) :
    execOpenat s = (s.writeReg64 .x0 (-BitVec.ofNat 64 errno)).advancePC :=
  LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic.execOpenat_of_classifyOpenRdonly_err
    hpok hmax hcl hdfd hflags hcs

private theorem pRxSub_muslOpenRdonlyDet_ok :
    subroutine_ok pRxSub 0x476ba0#64 muslOpenRdonlyDetSpec := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨cstr, path, e0⟩ R s0 hpc hrun hpre hsp _hL
  simp only [muslOpenRdonlyDetSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpok, hmax, hlen, hlat⟩, hm⟩
  obtain ⟨hcp, hlead, hdot⟩ := validRelCPath_of_pathOk hpok hlen hlat
  have hne := isEmpty_false_of_pathOk hpok
  have htd := trailingDir_false_of_pathOk hpok
  have hnorm_ne := normalizePath_ne_nil_of_pathOk hpok
  have hb6 : O_CLOEXEC_W32.getLsbD 6 = false := by decide
  have htmp : O_CLOEXEC_W32 &&& 0x00404000#32 = 0#32 := by decide
  have hb19 : O_CLOEXEC_W32.getLsbD 19 = true := by decide
  have hfl_eq : O_CLOEXEC_W32 ||| O_LARGEFILE_W32 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32 := by decide
  cases hcl : classifyOpenRdonly s0.fs path with
  | ok fd kind =>
    obtain ⟨hb_none, halloc, _, hfd_max, _, hkind_cases⟩ := classifyOpenRdonly_ok_spec hcl
    have hfd_lt : fd.toNat < 2 ^ 31 := by
      have hmmax : FsState.maxOpenFds = 1024 := rfl
      rw [hmmax] at hfd_max
      have h1024_lt : (1024 : Nat) < 2 ^ 31 := by decide
      exact Nat.lt_trans hfd_max h1024_lt
    have hanc_none : ancestorWalkErrno? s0.fs path = none := by
      rw [ancestorWalkErrno?_eq_of_pathOk s0.fs hpok hmax, hb_none]
    let desc : FdEntry :=
      { path := path, accMode := .rdonly, append := false, cloexec := true,
        offset := 0, kind := kind }
    let fs' : FsState := s0.fs.setFd fd (some desc)
    refine prx_musl_muslOpenNoCreatCloexecLocalExec_ok.mono_outcome
      (cstr, path, O_CLOEXEC_W32, e0, .ok fd desc fs' []) R s0 hpc hrun ?_ hsp (fun sf hout => ?_)
    · simp only [muslOpenNoCreatCloexecLocalExecSpec, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2
      rcases hkind_cases with ⟨rfl, hdir⟩ | ⟨rfl, bs, hfile⟩
      · have hexec := execOpenat_rdonly_cloexec_dir hs_x0 (hfl_eq ▸ hs_x2) hcs hne hlead hdot
          (hs_fs.symm ▸ hanc_none) (hs_fs.symm ▸ hdir) (hs_fs.symm ▸ halloc)
        rw [hs_fs] at hexec
        refine ⟨hfd_lt, by simp only [fs', FsState.setFd, beq_self_eq_true, ↓reduceIte], Or.inr rfl, rfl, ?_⟩
        rw [prx_setFs_appendTrace_nil]; exact hexec
      · have hexec := prx_execOpenat_rdonly_cloexec_file_or_emfile hs_x0 (hfl_eq ▸ hs_x2) hcs hne
          hlead hdot htd hnorm_ne (hs_fs.symm ▸ hanc_none) (hs_fs.symm ▸ hfile)
        rw [hs_fs, halloc] at hexec
        refine ⟨hfd_lt, by simp only [fs', FsState.setFd, beq_self_eq_true, ↓reduceIte], Or.inl rfl, rfl, ?_⟩
        rw [prx_setFs_appendTrace_nil]; exact hexec
    · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        simpa only [muslOpenNoCreatCloexecLocalExecSpec, muslOpenRdonlyDetSpec, hcl,
          List.append_nil] using hq
      · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))
  | err errno =>
    have herr_cases := classifyOpenRdonly_err_cases hcl
    have herr_bounds : 1 ≤ errno ∧ errno ≤ 4095 := by
      rcases herr_cases with rfl | rfl | rfl <;> decide
    refine prx_musl_muslOpenNoCreatCloexecLocalExec_ok.mono_outcome
      (cstr, path, O_CLOEXEC_W32, e0, .err (· = errno)) R s0 hpc hrun ?_ hsp (fun sf hout => ?_)
    · simp only [muslOpenNoCreatCloexecLocalExecSpec, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2
      refine ⟨errno, herr_bounds.1, herr_bounds.2, rfl, ?_⟩
      exact prx_execOpenat_of_classifyOpenRdonly_err hpok hmax (hs_fs.symm ▸ hcl) hs_x0
        (hfl_eq ▸ hs_x2) hcs
    · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        simp only [muslOpenNoCreatCloexecLocalExecSpec, muslOpenRdonlyDetSpec, hcl,
          sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
        rcases hq with ⟨errno', ⟨_, _, rfl, hx0', hfs', htr', hpres'⟩, hm_cells⟩
        exact ⟨⟨hx0', hfs', htr', hpres'⟩, hm_cells⟩
      · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))

private def prx_ioMpl : MultiPlacement where
  base i := [0x474000#64, 0x473724#64, 0x473854#64, 0x4741b4#64, 0x4743f0#64].getD i 0#64
  ρ s :=
    if s == "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" then 0x474630#64
    else if s == "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" then 0x474634#64
    else if s == "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc" then 0x474638#64
    else if s == "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" then 0x474640#64
    else if s == "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" then 0x4cb088#64
    else if s == "__errno_location" then 0x476a94#64
    else if s == "close" then 0x479380#64
    else if s == "memcpy" then 0x474650#64
    else if s == "open" then 0x476ba0#64
    else if s == "read" then 0x4793c4#64
    else if s == "write" then 0x4793f8#64
    else 0#64

private theorem prx_ioMpl_placeable :
    signalSessionIoMultiLib.Placeable prx_ioMpl :=
  signalSessionIoMultiLib.placeable_of_checkPlaceable (by rfl_kernel)

set_option maxRecDepth 4000000 in
private theorem pRxSub_readsCodeLoaded (m : Memory)
    (hCL : pRxSub.CodeLoaded m) :
    CliIoReadsCodeLoaded prx_ioMpl m :=
  cliIoReadsCodeLoaded_of_blocks
    (codeLoaded_of_checkProgSliceInWordTree wtRxSub_eq wtRxSub_size
      (by rw [pRxSub_base]; rfl_kernel) hCL)
    (codeLoaded_of_checkProgSliceInWordTree wtRxSub_eq wtRxSub_size
      (by rw [pRxSub_base]; rfl_kernel) hCL)
    (codeLoaded_of_checkProgSliceInWordTree wtRxSub_eq wtRxSub_size
      (by rw [pRxSub_base]; rfl_kernel) hCL)

private theorem pRxSub_readFileCond_ok
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok pRxSub 0x4741b4#64
      (readFileAnyBudgetCondSpec
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits extHookStack) := by
  have hres : Arm64.Obj.MultiPlacedLib.resolve
      CryptoVerification.signalSessionIoMultiLib prx_ioMpl
      cliIoReadFileSym = 0x4741b4#64 := rfl
  rw [← hres]
  exact cliIoReadFileAnyBudgetCond_ok_of_entries_of_readsCodeLoaded
    (fineHookPoolErrnoSplit γ mmpl tp cliElfImage.brkStart)
    cliBudgetLimits prx_ioMpl_placeable pRxSub_readsCodeLoaded (by decide)
    pRxSub_svc
    (ExternPreservesOracleSymtab.of_no_extern pRxSub_no_ext)
    (fun _ _ => pRxSub_no_ext _)
    (fun _ _ => pRxSub_no_ext _)
    pRxSub_muslOpenRdonlyDet_ok prx_musl_muslErrnoLocation_ok prx_musl_muslReadDir32_ok
    prx_musl_muslReadFileOrStdio32_ok prx_musl_muslClose48Local_ok pRxSub_stdMemcpy_ok
    pRxSub_noAllocShim_ok (pRxSub_fineHookAllocEntries_thunks mmpl hMm γ tp)

private theorem pRxSub_readStdinCond_ok
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok pRxSub 0x474000#64
      (readStdinBudgetCondSpec
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits extHookStack) := by
  have hres : Arm64.Obj.MultiPlacedLib.resolve
      CryptoVerification.signalSessionIoMultiLib prx_ioMpl
      cliIoReadStdinSym = 0x474000#64 := rfl
  rw [← hres]
  have hEntries := pRxSub_fineHookAllocEntries_thunks mmpl hMm γ tp
  exact cliIoReadStdin_budgetCond_ok_of_readsCodeLoaded
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
    prx_ioMpl_placeable (Nat.le_refl _) pRxSub_readsCodeLoaded
    (fun _ _ => pRxSub_no_ext _)
    (fun _ _ => pRxSub_no_ext _)
    prx_musl_muslReadStdin32_ok
    pRxSub_allocMemcpyVm_ok
    pRxSub_noAllocShim_ok
    (hEntries.alloc cliBudgetLimits) (hEntries.realloc cliBudgetLimits)
    (hEntries.dealloc cliBudgetLimits)
    (fun hsat hmap => fineHookRustCliAllocBudget_mapped_lt_userVa (by decide) hsat hmap)

private theorem prx_pre_compiled_of_bounded [LibsignalPlacement]
    {γ : GhostName} {mmpl : MultiPlacement} {tp : BitVec 64}
    {y : ReadStdinGhost × fineCostModel.σ}
    {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack ReadStdinBoundedEnv).pre y s0 ∗ R) :
    s0.mem ⊨
      (readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack CompiledReadStdinEnv).pre y s0 ∗ R := by
  rcases y with ⟨x, st⟩
  dsimp only [readStdinSpecOfPlaced] at hpre ⊢
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨hpre.1.1, hpre.1.2.1,
    fitsEnv_compiled_of_sub (fun _ => compiledReadStdinEnv_sub_bounded) hpre.1.2.2.1,
    hpre.1.2.2.2⟩, hpre.2⟩

end PRxSubReadsPriv

open Classical in
/-- Local `rfl` mirror of `ElfSlicesPqOomH2KHooks.h2k_readFileFixedGhostHookFineK`. -/
@[expose] noncomputable def avoid_readFileFixedGhostHookFineK
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) (s0 : State) : State :=
  if _ : ActiveF3CallPre
      (fun γ tp => avoid_withKeepLrAndFds hole2_keepSub
        (readFileAnySpecPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk
          (ReadFileRuleEnvFixed cliIo.rd))) s0 then
    if hReal : ActiveF3ReadFileRun keep P_real P_sub entry_io F3ReadFileFixedCallGuard s0 then
      Classical.choose hReal.2.2.2.2
    else
      keepFsTrace (f3ReadFileFallback mmpl) s0
  else
    { s0 with status := .Exception "read_file ghost-hook precondition violated" }

open Classical in
/-- Local `rfl` mirror of `ElfSlicesPqOomH2KHooks.h2k_readStdinGhostHookFineK`. -/
@[expose] noncomputable def avoid_readStdinGhostHookFineK [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) (s0 : State) : State :=
  if _ : ActiveF3CallPre
      (fun γ tp => avoid_withKeepLrFalse hole2_keepSub
        (readStdinSpecOfPlaced cliIo
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk ReadStdinBoundedEnv)) s0 then
    if hReal : ActiveReadStdinLinkedRun keep P_real P_sub entry_io s0 then
      Classical.choose hReal.2.2.2
    else
      keepFilesTrace (f3ReadStdinFallback mmpl) s0
  else
    { s0 with status := .Exception "read_stdin ghost-hook precondition violated" }

private theorem replay_readFile_below4b0000 {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsReadFileSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (avoid_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hFds : FdsGe3Closed u.fs)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps P u
      (avoid_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u) := by
  classical
  have hActPre' : ActiveF3CallPre
      (fun γ tp => avoid_withKeepLrAndFds hole2_keepSub
        (readFileAnySpecPlaced
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd))) u := by
    by_contra hn
    apply hnoex "read_file ghost-hook precondition violated"
    unfold avoid_readFileFixedGhostHookFineK
    simp [hn]
  have hActPre := avoid_activeF3CallPre_withKeepLrAndFds hActPre'
  have hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub u.mem) :=
    h2cl_f3CodeInv_rxProg_keepSub hInv
  have hReal :
      ActiveF3ReadFileRun hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readFile F3ReadFileFixedCallGuard u :=
    h2fsreads_readFile_activeRealRun_keepSub mmpl hMm hActPre hFr hlr hCodeSub hFds
  have hchoose := Classical.choose_spec hReal.2.2.2.2
  have hfu :
      avoid_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
          (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u =
        Classical.choose hReal.2.2.2.2 := by
    unfold avoid_readFileFixedGhostHookFineK
    simp only [hActPre', hReal, ↓reduceDIte]
  have hCodeRxSub : pRxSub.CodeLoaded (stripExecOutside keepRxSub u.mem) :=
    strip_codeLoaded_f3 (pRxSub_codeLoaded_of_f3TrialRxProg hInv.rxCode)
  have hlrRxSub : keepRxSub (u.readReg64 .lr) = false :=
    keepRxSub_false_of_hole2_keepSub_false hlr
  have hKeepMng := keepRxSub_mallocng mmpl hMm
  have hAllRxSub : ∀ (Q : Program), Q.svc = hole2_emptyProg.svc →
      (∀ pc : BitVec 64, keepRxSub pc = true → Q.externAt? pc = none) →
      ∃ sf : State,
        StepsUntil Q (SubroutineStop u) (u.setPC (hole2_targets mpl).readFile) sf ∧
        SubroutineStop u sf := by
    intro Q hsvcQ hnoQ
    obtain ⟨hRun, hSp, γ, tp, ⟨x, st⟩, R, hSat⟩ := hActPre
    obtain ⟨sf, huQ, hsQ, _⟩ :=
      real_f3ReadFileFixed_run_of_stripS
        (hsvcQ.trans h2sl_emptyProg_svc) pRxSub_svc hnoQ pRxSub_no_ext
        (fun st' s' => fineHookRustCliAllocBudget_pool_stripS
          γ mmpl tp cliElfImage.brkStart hKeepMng cliBudgetLimits st' s')
        (pRxSub_readFileCond_ok mmpl hMm γ tp)
        hRun hSp hSat hFr hlrRxSub hFds hCodeRxSub
    exact ⟨sf, huQ, hsQ⟩
  have hvis := stepsVisitedIn_of_allProg (D := keepRxSub) (P1 := hole2_emptyProg)
    (fun pc _ => h2sl_emptyProg_externAt pc) hAllRxSub hchoose.1
  have hBody : Steps P (u.setPC (hole2_targets mpl).readFile) (Classical.choose hReal.2.2.2.2) :=
    stepsUntil_noExtern_lift_of_visitedIn
      (D := keepRxSub) (P1 := hole2_emptyProg) (P2 := P)
      (h2sl_emptyProg_svc.trans hsvc.symm)
      (fun pc _ => h2sl_emptyProg_externAt pc)
      (fun pc hk => noExtern_keepRxSub hLs W hextBelow pc hk)
      hvis hchoose.2.1
  rw [hfu]
  exact (stub_readFile_below4b0000 hLs W hextBelow u hpc hrun hFr hInv).trans hBody

private theorem replay_readStdin_below4b0000 [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsReadStdinSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (avoid_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    Steps P u
      (avoid_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u) := by
  classical
  have hActPre' : ActiveF3CallPre
      (fun γ tp => avoid_withKeepLrFalse hole2_keepSub
        (readStdinSpecOfPlaced cliIo
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits hole2_hookStack ReadStdinBoundedEnv)) u := by
    by_contra hn
    apply hnoex "read_stdin ghost-hook precondition violated"
    unfold avoid_readStdinGhostHookFineK
    simp [hn]
  have hActPre := avoid_activeF3CallPre_withKeepLrFalse hActPre'
  have hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub u.mem) :=
    h2cl_f3CodeInv_rxProg_keepSub hInv
  have hReal :
      ActiveReadStdinLinkedRun hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readStdin u :=
    h2fsreads_readStdin_activeRealRun_keepSub mmpl hMm hActPre hFr hlr hCodeSub
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hfu :
      avoid_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
          (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack u =
        Classical.choose hReal.2.2.2 := by
    unfold avoid_readStdinGhostHookFineK
    simp only [hActPre', hReal, ↓reduceDIte]
  have hCodeRxSub : pRxSub.CodeLoaded (stripExecOutside keepRxSub u.mem) :=
    strip_codeLoaded_f3 (pRxSub_codeLoaded_of_f3TrialRxProg hInv.rxCode)
  have hlrRxSub : keepRxSub (u.readReg64 .lr) = false :=
    keepRxSub_false_of_hole2_keepSub_false hlr
  have hKeepMng := keepRxSub_mallocng mmpl hMm
  have hAllRxSub : ∀ (Q : Program), Q.svc = hole2_emptyProg.svc →
      (∀ pc : BitVec 64, keepRxSub pc = true → Q.externAt? pc = none) →
      ∃ sf : State,
        StepsUntil Q (SubroutineStop u) (u.setPC (hole2_targets mpl).readStdin) sf ∧
        SubroutineStop u sf := by
    intro Q hsvcQ hnoQ
    obtain ⟨hRun, hSp, γ, tp, ⟨x, st⟩, R, hSatB⟩ := hActPre
    have hSatC := prx_pre_compiled_of_bounded hSatB
    obtain ⟨sf, huQ, hsQ, _⟩ :=
      real_readStdin_run_of_stripS
        (hsvcQ.trans h2sl_emptyProg_svc) pRxSub_svc hnoQ pRxSub_no_ext
        (fun st' s' => fineHookRustCliAllocBudget_pool_stripS
          γ mmpl tp cliElfImage.brkStart hKeepMng cliBudgetLimits st' s')
        (pRxSub_readStdinCond_ok mmpl hMm γ tp)
        hRun hSp hSatC hFr hlrRxSub hCodeRxSub
    exact ⟨sf, huQ, hsQ⟩
  have hvis := stepsVisitedIn_of_allProg (D := keepRxSub) (P1 := hole2_emptyProg)
    (fun pc _ => h2sl_emptyProg_externAt pc) hAllRxSub hchoose.1
  have hBody : Steps P (u.setPC (hole2_targets mpl).readStdin) (Classical.choose hReal.2.2.2) :=
    stepsUntil_noExtern_lift_of_visitedIn
      (D := keepRxSub) (P1 := hole2_emptyProg) (P2 := P)
      (h2sl_emptyProg_svc.trans hsvc.symm)
      (fun pc _ => h2sl_emptyProg_externAt pc)
      (fun pc hk => noExtern_keepRxSub hLs W hextBelow pc hk)
      hvis hchoose.2.1
  rw [hfu]
  exact (stub_readStdin_below4b0000 hLs W hextBelow u hpc hrun hFr hInv).trans hBody

/-- `ElfSlicesPqOomH2KHooks`-free parametric 10-way `GhostSymActiveNamed ghFixed` replay on any
`Syscall.standard` program `P` agreeing with `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`
below `0x4b0000`. All 9 non-`stringClone` field equations hold by `rfl` on `h2k_ghFixedK mpl mmpl`. -/
theorem namedGhost_steps_of_below4b0000_of_ghFixed [LibsignalPlacement]
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (P : Program)
    (hsvc : P.svc = Arm64.Syscall.standard)
    (hextBelow : ∀ pc : BitVec 64, pc.toNat < 0x4b0000 →
      P.externAt? pc = (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    (ghFixed : CliGhostHooks)
    (hAlloc : ghFixed.alloc =
      f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).alloc
        (fun γ tp => avoid_withKeepLrFalse hole2_keepSub
          (rustCliAllocBudgetSpec fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits false))
        (f3AllocFallback mmpl false))
    (hDealloc : ghFixed.dealloc =
      f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).dealloc
        (fun γ tp => avoid_withKeepLrFalse hole2_keepSub
          (rustCliDeallocBudgetSpec fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits))
        (f3DeallocFallback mmpl))
    (hRealloc : ghFixed.realloc =
      f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).realloc
        (fun γ tp => avoid_withKeepLrFalse hole2_keepSub
          (rustCliReallocBudgetSpec fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits))
        (f3ReallocFallback mmpl))
    (hAz : ghFixed.allocZeroed =
      f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).allocZeroed
        (fun γ tp => avoid_withKeepLrFalse hole2_keepSub
          (rustAllocZeroedBudgetSpec fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits))
        (f3AllocFallback mmpl true))
    (hShim : ghFixed.shim = hookNoop)
    (hReadFile : ∀ f h, ghFixed.readFile = some ⟨f, h⟩ →
      f = avoid_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
    (hReadStdin : ∀ f h, ghFixed.readStdin = some ⟨f, h⟩ →
      f = avoid_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
    (hMemset : ghFixed.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hMemcpy : ghFixed.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (sym : String) (f : State → State)
    (_hExt617 : sym ∈ (libsignalSessionLib.blockLib 617).text.externs)
    (hneSc : sym ≠ CryptoVerification.SignalSession.lsStringCloneSym)
    (hActNamed : GhostSymActiveNamed ghFixed sym f)
    (u : State)
    (hpc : u.pc = libsignalSessionLib.resolve mpl sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f u).status ≠ .Exception msg)
    (_hkf : u.mem.KeepsFrozen (f u).mem)
    (hFr : ExecFrozen u.mem)
    (hlr_sub : sym ≠ CryptoVerification.SignalSession.lsRustNoAllocShimSymCli →
      sym ≠ CryptoVerification.SignalSession.lsMemsetSym →
      sym ≠ CryptoVerification.SignalSession.lsMemcpySym →
      hole2_keepSub (u.readReg64 .lr) = false)
    (hlr_blk21 : sym = CryptoVerification.SignalSession.lsMemsetSym →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false)
    (hlr_blk20 : sym = CryptoVerification.SignalSession.lsMemcpySym →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (hread_fds : sym = CryptoVerification.SignalSession.lsReadFileSym → FdsGe3Closed u.fs) :
    Steps P u (f u) := by
  rcases hActNamed with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨hSc, _⟩ | ⟨rfl, hSub, hRf⟩ | ⟨rfl, hSub, hRs⟩ | ⟨rfl, hMs⟩ | ⟨rfl, hMc⟩
  · -- Arm 1: alloc
    rw [hAlloc] at hnoex ⊢
    exact replay_f3LinkedCallHook_below4b0000 hLs W hsvc hextBelow
      (stub_alloc_below4b0000 hLs W hextBelow)
      (fun _ => avoid_activeF3CallPre_withKeepLrFalse)
      (fun hPre hFr' hLr' hCode' =>
        h2fsalloc_alloc_activeRealRun_keepSub mmpl hMm hPre hFr' hLr' hCode')
      (fun hPre hFr' hLr' hCode' _Q hsvcQ hnoQ =>
        pRxSub_alloc_firstStop_keepRxSub mmpl hMm false hsvcQ hnoQ hPre hLr' hFr' hCode')
      hpc hrun hnoex hFr (hlr_sub (by decide) (by decide) (by decide)) hInv
  · -- Arm 2: dealloc
    rw [hDealloc] at hnoex ⊢
    exact replay_f3LinkedCallHook_below4b0000 hLs W hsvc hextBelow
      (stub_dealloc_below4b0000 hLs W hextBelow)
      (fun _ => avoid_activeF3CallPre_withKeepLrFalse)
      (fun hPre hFr' hLr' hCode' =>
        h2fsdealloc_activeRealRun_keepSub mmpl hMm hPre hFr' hLr' hCode')
      (fun hPre hFr' hLr' hCode' _Q hsvcQ hnoQ =>
        pRxSub_dealloc_firstStop_keepRxSub mmpl hMm hsvcQ hnoQ hPre hLr' hFr' hCode')
      hpc hrun hnoex hFr (hlr_sub (by decide) (by decide) (by decide)) hInv
  · -- Arm 3: realloc
    rw [hRealloc] at hnoex ⊢
    exact replay_f3LinkedCallHook_below4b0000 hLs W hsvc hextBelow
      (stub_realloc_below4b0000 hLs W hextBelow)
      (fun _ => avoid_activeF3CallPre_withKeepLrFalse)
      (fun hPre hFr' hLr' hCode' =>
        h2fsrealloc_activeRealRun mmpl hMm hPre hFr' hLr' hCode')
      (fun hPre hFr' hLr' hCode' _Q hsvcQ hnoQ =>
        pRxSub_realloc_firstStop_keepRxSub mmpl hMm hsvcQ hnoQ hPre hLr' hFr' hCode')
      hpc hrun hnoex hFr (hlr_sub (by decide) (by decide) (by decide)) hInv
  · -- Arm 4: allocZeroed
    rw [hAz] at hnoex ⊢
    exact replay_f3LinkedCallHook_below4b0000 hLs W hsvc hextBelow
      (stub_allocZeroed_below4b0000 hLs W hextBelow)
      (fun _ => avoid_activeF3CallPre_withKeepLrFalse)
      (fun hPre hFr' hLr' hCode' =>
        h2fsalloc_allocZeroed_activeRealRun_keepSub mmpl hMm hPre hFr' hLr' hCode')
      (fun hPre hFr' hLr' hCode' _Q hsvcQ hnoQ =>
        pRxSub_alloc_firstStop_keepRxSub mmpl hMm true hsvcQ hnoQ hPre hLr' hFr' hCode')
      hpc hrun hnoex hFr (hlr_sub (by decide) (by decide) (by decide)) hInv
  · -- Arm 5: shim
    rw [hShim]
    exact replay_shim_below4b0000 hLs W hextBelow hpc hrun hFr hInv
  · -- Arm 6: stringClone (excluded by hneSc)
    exact False.elim (hneSc hSc)
  · -- Arm 7: readFile
    have hf_eq := hReadFile f hSub hRf
    subst hf_eq
    exact replay_readFile_below4b0000 hLs hMm W hsvc hextBelow hpc hrun hnoex hFr
      (hlr_sub (by decide) (by decide) (by decide)) (hread_fds rfl) hInv
  · -- Arm 8: readStdin
    have hf_eq := hReadStdin f hSub hRs
    subst hf_eq
    exact replay_readStdin_below4b0000 hLs hMm W hsvc hextBelow hpc hrun hnoex hFr
      (hlr_sub (by decide) (by decide) (by decide)) hInv
  · -- Arm 9: memset
    have hf_eq : f = f3EmptyMemsetGhostHookNarrow mmpl := Option.some.inj (hMs.symm.trans hMemset)
    subst hf_eq
    exact replay_memset_below4b0000 hLs hMm W hsvc hextBelow hpc hrun hnoex hFr
      (hlr_blk21 rfl) hInv
  · -- Arm 10: memcpy
    have hf_eq : f = f3EmptyMemcpyGhostHookNarrow mmpl := Option.some.inj (hMc.symm.trans hMemcpy)
    subst hf_eq
    exact replay_memcpy_below4b0000 hLs hMm W hsvc hextBelow hpc hrun hnoex hFr
      (hlr_blk20 rfl) hInv

/-! ## 6. Public `h2sl_keepLoSub` (`[0x474000, 0x479798)`) First-Stop Corollaries for `H2Branch2` -/

theorem pRxSub_alloc_allProg_lo [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hActPre : ActiveF3CallPre (h2fsalloc_spec mmpl false) u)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (Q : Program) (hsvcQ : Q.svc = Syscall.standard)
    (hnoQ : ∀ pc : BitVec 64, h2sl_keepLoSub pc = true → Q.externAt? pc = none) :
    ∃ sf : State,
      StepsUntil Q (SubroutineStop u) (u.setPC f3RdlAddrs.alloc) sf ∧
      SubroutineStop u sf :=
  pRxSub_alloc_firstStop_keepRxSub mmpl hMm false hsvcQ
    (fun pc hk => hnoQ pc (keepRxSub_imp_h2sl_keepLoSub hk))
    hActPre
    (keepRxSub_false_of_hole2_keepSub_false hlr)
    hFr
    (strip_codeLoaded_f3 (pRxSub_codeLoaded_of_f3TrialRxProg hInv.rxCode))

theorem pRxSub_allocZeroed_allProg_lo [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hActPre : ActiveF3CallPre (h2fsalloc_spec mmpl true) u)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (Q : Program) (hsvcQ : Q.svc = Syscall.standard)
    (hnoQ : ∀ pc : BitVec 64, h2sl_keepLoSub pc = true → Q.externAt? pc = none) :
    ∃ sf : State,
      StepsUntil Q (SubroutineStop u) (u.setPC f3RdlAzAddr) sf ∧
      SubroutineStop u sf :=
  pRxSub_alloc_firstStop_keepRxSub mmpl hMm true hsvcQ
    (fun pc hk => hnoQ pc (keepRxSub_imp_h2sl_keepLoSub hk))
    hActPre
    (keepRxSub_false_of_hole2_keepSub_false hlr)
    hFr
    (strip_codeLoaded_f3 (pRxSub_codeLoaded_of_f3TrialRxProg hInv.rxCode))

theorem pRxSub_dealloc_allProg_lo [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hActPre : ActiveF3CallPre (h2fsdealloc_spec mmpl) u)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (Q : Program) (hsvcQ : Q.svc = Syscall.standard)
    (hnoQ : ∀ pc : BitVec 64, h2sl_keepLoSub pc = true → Q.externAt? pc = none) :
    ∃ sf : State,
      StepsUntil Q (SubroutineStop u) (u.setPC f3RdlAddrs.dealloc) sf ∧
      SubroutineStop u sf :=
  pRxSub_dealloc_firstStop_keepRxSub mmpl hMm hsvcQ
    (fun pc hk => hnoQ pc (keepRxSub_imp_h2sl_keepLoSub hk))
    hActPre
    (keepRxSub_false_of_hole2_keepSub_false hlr)
    hFr
    (strip_codeLoaded_f3 (pRxSub_codeLoaded_of_f3TrialRxProg hInv.rxCode))

theorem pRxSub_realloc_allProg_lo [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hActPre : ActiveF3CallPre (h2fsrealloc_spec mmpl) u)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (Q : Program) (hsvcQ : Q.svc = Syscall.standard)
    (hnoQ : ∀ pc : BitVec 64, h2sl_keepLoSub pc = true → Q.externAt? pc = none) :
    ∃ sf : State,
      StepsUntil Q (SubroutineStop u) (u.setPC f3RdlAddrs.realloc) sf ∧
      SubroutineStop u sf :=
  pRxSub_realloc_firstStop_keepRxSub mmpl hMm hsvcQ
    (fun pc hk => hnoQ pc (keepRxSub_imp_h2sl_keepLoSub hk))
    hActPre
    (keepRxSub_false_of_hole2_keepSub_false hlr)
    hFr
    (strip_codeLoaded_f3 (pRxSub_codeLoaded_of_f3TrialRxProg hInv.rxCode))

theorem pRxSub_readFile_allProg_lo
    {mpl mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hActPre : ActiveF3CallPre
      (fun γ tp => readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) u)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hFds : FdsGe3Closed u.fs)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (Q : Program) (hsvcQ : Q.svc = Syscall.standard)
    (hnoQ : ∀ pc : BitVec 64, h2sl_keepLoSub pc = true → Q.externAt? pc = none) :
    ∃ sf : State,
      StepsUntil Q (SubroutineStop u) (u.setPC (hole2_targets mpl).readFile) sf ∧
      SubroutineStop u sf := by
  obtain ⟨hRun, hSp, γ, tp, ⟨x, st⟩, R, hSat⟩ := hActPre
  obtain ⟨sf, huQ, hsQ, _⟩ :=
    real_f3ReadFileFixed_run_of_stripS
      hsvcQ pRxSub_svc
      (fun pc hk => hnoQ pc (keepRxSub_imp_h2sl_keepLoSub hk))
      pRxSub_no_ext
      (fun st' s' => fineHookRustCliAllocBudget_pool_stripS
        γ mmpl tp cliElfImage.brkStart (keepRxSub_mallocng mmpl hMm) cliBudgetLimits st' s')
      (pRxSub_readFileCond_ok mmpl hMm γ tp)
      hRun hSp hSat hFr
      (keepRxSub_false_of_hole2_keepSub_false hlr)
      hFds
      (strip_codeLoaded_f3 (pRxSub_codeLoaded_of_f3TrialRxProg hInv.rxCode))
  exact ⟨sf, huQ, hsQ⟩

theorem pRxSub_readStdin_allProg_lo [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {u : State}
    (hActPre : ActiveF3CallPre
      (fun γ tp => readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack ReadStdinBoundedEnv) u)
    (hFr : ExecFrozen u.mem)
    (hlr : hole2_keepSub (u.readReg64 .lr) = false)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (Q : Program) (hsvcQ : Q.svc = Syscall.standard)
    (hnoQ : ∀ pc : BitVec 64, h2sl_keepLoSub pc = true → Q.externAt? pc = none) :
    ∃ sf : State,
      StepsUntil Q (SubroutineStop u) (u.setPC (hole2_targets mpl).readStdin) sf ∧
      SubroutineStop u sf := by
  obtain ⟨hRun, hSp, γ, tp, ⟨x, st⟩, R, hSatB⟩ := hActPre
  have hSatC := prx_pre_compiled_of_bounded hSatB
  obtain ⟨sf, huQ, hsQ, _⟩ :=
    real_readStdin_run_of_stripS
      hsvcQ pRxSub_svc
      (fun pc hk => hnoQ pc (keepRxSub_imp_h2sl_keepLoSub hk))
      pRxSub_no_ext
      (fun st' s' => fineHookRustCliAllocBudget_pool_stripS
        γ mmpl tp cliElfImage.brkStart (keepRxSub_mallocng mmpl hMm) cliBudgetLimits st' s')
      (pRxSub_readStdinCond_ok mmpl hMm γ tp)
      hRun hSp hSatC hFr
      (keepRxSub_false_of_hole2_keepSub_false hlr)
      (strip_codeLoaded_f3 (pRxSub_codeLoaded_of_f3TrialRxProg hInv.rxCode))
  exact ⟨sf, huQ, hsQ⟩

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeNamedAvoid

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bCut -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinCanonPrime
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget

/-!
# Spine-B (`signal_session::run`, Block `579`) Bridge (`ElfSlicesPqOomH2KSpineB`)

**Checked by Lean.**

Bridges `RunOkNoMatchPlacedBudgetFd.hrun_cli_sem_full_placed_fd` and
`hrun_cli_d2c_tight_full_placed_fd` to the Spine-B and Spine-C interfaces in
`ElfSlicesPqOomH2KIfaces`:
1. Closes `CliRunHooksBundleFd` unconditionally at `ghFixed := h2k_ghFixedK mpl mmpl`
   (`h2ksb_hole2_hHooksBundleFd`).
2. Reduces `h2ki_RunTightAt579PreFd`, `h2ki_SpineBCanonSlice{At,K}` (`hmain` and `hinitSem`), and
   `h2ki_SpineBRunTightOfSem{At,K}` (`huntyped`, `hoverD3`, `hpathB`, `hvalidMatch`) to
   `CliPubCalleesFrozenPlacedFd`, `SpineBPureFsCallees`, and the four Spine-C slot contracts
   (`464`, `463`, `521`, `520`).
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB

open Arm64
  (GhostName HookOk HookSat Memory Program SepProp Spec State satisfies_pure_sepConj sepConj_assoc
   subroutine_ok subroutine_ok_mono)
open ProofLib (satisfies_sepExists sepExists_sepConj_left)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoVerification
  (ExternsDistinctOnHooked LibsignalFrozen LibsignalFullPlacement
   LibsignalHooks LibsignalPlacement blkPl_111 libsignalMutatedBlocks lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym)
open CryptoVerification.SignalSession.Cli (RunAnswer)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliResStack cliRunBudgets cliRunBudgets_placed cliRunNeeds cliWrOk mProgPlaced)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_590)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecSigGhost EncGhost PksmGhost RunSem mkSlot runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom (cliDecPkCanonSlotEnvExact')
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnvOf PqxdhAcceptBadKemErrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (defaultExtrasF3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (hookSat_withLsRetAddr624AndFds_of_withFds_keepLrAndFds withLsRetAddr624AndFds withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (pksmSlotSpecPlacedOkFs tryFromPlacedSpecOkFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
  (CliPubCalleesFrozenPlacedFd CliRunHooksBundleFd hrun_cli_sem_full_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudgetFd (RunArmEnvs RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decSigSlotSpecFrozenPlaced encSlotSpecPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced runSpecPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bCut
  (g5ba_decSigSlotSpecFrozenPlaced_d2c_eq_d3 g5ba_encSlotSpecPlaced_d2c_eq_d3)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_Branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
  (h2kb_alloc_pre_keepSub_false h2kb_dealloc_pre_keepSub_false h2kb_hookOk_of_withKeepLrFalse
   h2kb_hole2_runHooksPlaced h2kb_realloc_pre_keepSub_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
  (h2k_hole2_hReadSatK_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (CliInitSlotOkPlacedPreFd DecPkD2cSlotOkFrozenPlacedAtPreFd h2ki_DecryptSignalSlot463OkAtPreFd
   h2ki_EncryptSlot464OkAtPreFd h2ki_RunTightAt579Fd h2ki_RunTightAt579PreFd
   h2ki_SpineBCanonSliceAt h2ki_SpineBCanonSliceAtFd h2ki_SpineBCanonSliceFdK
   h2ki_SpineBCanonSliceK h2ki_SpineBRunTightOfSemAt h2ki_SpineBRunTightOfSemAtFd
   h2ki_SpineBRunTightOfSemFdK h2ki_SpineBRunTightOfSemK h2ki_UntypedDecPkSlot520OkK
   h2ki_UntypedDecPkSlot520OkWfK h2ki_W1EncryptSlot464OkK h2ki_W1EncryptSlot464OkWfK
   h2ki_W2DecryptSignalSlot463OkK h2ki_W2DecryptSignalSlot463OkWfK h2ki_W3InitSlot521OkK
   h2ki_W3InitSlot521OkWfK h2ki_W4DecPkCanonSlot520OkK h2ki_W4DecPkCanonSlot520OkWfK
   runSpecTightPlacedFd slotWithFdsGe3Closed slotWithPreFdsGe3Closed withPreFdsGe3Closed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
  (h2kb_runHooksPlaced_withFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK mkF3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
  (h2lr_lsRetAddr624_keepSub_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact
   libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinCanonPrime
  (canonOrFallbackRunEnvExact')

/-! ## Plain Allocator Bridges and `CliRunHooksBundleFd` -/

/-- Lift `w.hGSpqrK` (`h2k_CliGhostSpqrAllocHooksK`) to plain `CliGhostSpqrAllocHooks` via
`h2lr_lsRetAddr624_keepSub_false`. -/
theorem h2ksb_witness_hGSpqr {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits w.ghFixed := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  intro γ tp
  have hGK := w.hGSpqrK γ tp
  exact
    { alloc := h2kb_hookOk_of_withKeepLrFalse hGK.alloc (h2kb_alloc_pre_keepSub_false hLs)
      dealloc := h2kb_hookOk_of_withKeepLrFalse hGK.dealloc (h2kb_dealloc_pre_keepSub_false hLs)
      realloc := h2kb_hookOk_of_withKeepLrFalse hGK.realloc (h2kb_realloc_pre_keepSub_false hLs)
      allocZeroed :=
        h2kb_hookOk_of_withKeepLrFalse hGK.allocZeroed
          (h2kb_alloc_pre_keepSub_false (zeroed := true) hLs)
      alloc_fs := hGK.alloc_fs
      dealloc_fs := hGK.dealloc_fs
      realloc_fs := hGK.realloc_fs
      allocZeroed_fs := hGK.allocZeroed_fs
      alloc_fsT := hGK.alloc_fsT
      dealloc_fsT := hGK.dealloc_fsT
      realloc_fsT := hGK.realloc_fsT
      allocZeroed_fsT := hGK.allocZeroed_fsT
      shim_eq := hGK.shim_eq
      memset := hGK.memset
      memcpy := hGK.memcpy
      memcpy_exact := hGK.memcpy_exact
      memset_acp := hGK.memset_acp
      extraOk := hGK.extraOk
      onceCall := hGK.onceCall
      onceCall_unique := hGK.onceCall_unique }

/-- Lift `w.hGK` (`h2k_CliGhostAllocHooksK`) to plain `CliGhostAllocHooks`. -/
theorem h2ksb_witness_hG {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits w.ghFixed :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  fun γ tp => (h2ksb_witness_hGSpqr w hLs γ tp).toCliGhostAllocHooks

/-- `HookSat` on `lsReadFileSym` at `h2k_ghFixedK mpl mmpl` (`0` `hBranch2`) for
`withLsRetAddr624AndFds (readFileSpecPlaced …)` at `cliRunBudgets.readFile`. -/
theorem h2ksb_hole2_readFile_hookSat_lsRetAddr624AndFds
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat
      (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      lsReadFileSym
      (withLsRetAddr624AndFds
        (readFileSpecPlaced cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  exact hookSat_withLsRetAddr624AndFds_of_withFds_keepLrAndFds
    (fun _ hlr => h2lr_lsRetAddr624_keepSub_false hLs hlr)
    (h2k_hole2_hReadSatK_withFds mpl mmpl hLs hMm W γ tp)

/-- Closes `CliRunHooksBundleFd` at `ghFixed := h2k_ghFixedK mpl mmpl` from
`h2kb_hole2_runHooksPlaced` and `h2ksb_hole2_readFile_hookSat_lsRetAddr624AndFds`. -/
theorem h2ksb_hole2_hHooksBundleFd
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundleFd
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
        mmpl (h2k_ghFixedK mpl mmpl) W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun W γ tp =>
    { runHooks := h2kb_hole2_runHooksPlaced mpl mmpl hLs hMm W γ tp
      readFileSat := h2ksb_hole2_readFile_hookSat_lsRetAddr624AndFds mpl mmpl hLs hMm W γ tp }

/-- Witness-packaged `CliRunHooksBundleFd` predicate for `w : F3CliElfGhostWitnessK mpl mmpl`. -/
@[expose] def F3WitnessRunHooksBundleFd {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    @CliRunHooksBundleFd (libsignalPlacementOf mpl w.hblk w.hext_nodup)
      mmpl w.ghFixed W fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd)

theorem f3WitnessRunHooksBundleFd_mkF3CliElfGhostWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    F3WitnessRunHooksBundleFd (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2ksb_hole2_hHooksBundleFd mpl mmpl hLs hMm

/-! ## Pure-Callee `fs`-Preservation Bundle (`SpineBPureFsCallees`) -/

/-- Bundle of pure-callee `fs`-preservation contracts called from `signal_session::run`
(Block `579`): `kemDeserialize` (Block `590`), `tryFrom` (Block `85`), and `pksmTryFrom`
(Block `111`). -/
structure SpineBPureFsCallees [LibsignalPlacement]
    {M : AllocCostModel} (H : LibsignalHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (sEnvs : RunSlotEnvs) (PksmEnv : PksmGhost → List AllocEvent → Prop)
    (S : RunSem) (decPkNeed : Nat) : Prop where
  kemDeserialize :
    (slotWithFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).kemDeserialize).OkPlaced
      (lsProg_579 H) (blkPl_590).base
  tryFrom :
    subroutine_ok (lsProg_579 H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim))
  pksmTryFrom :
    subroutine_ok (lsProg_579 H) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim PksmEnv S)

/-! ## Core `h2ki_RunTightAt579PreFd` Discharger -/

/-- Discharges `h2ki_RunTightAt579PreFd` via
`RunOkNoMatchPlacedBudgetFd.hrun_cli_sem_full_placed_fd` for any `S : RunSem` and
`aEnvs : RunSem → RunArmEnvs`. -/
theorem h2ksb_runTightAt579PreFd_of_slots
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (ghFixed : CliGhostHooks)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (W : CliHooks)
    (sEnvs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      RunSlotEnvs)
    (aEnvs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      RunSem → RunArmEnvs)
    (S : RunSem) {decPkNeed : Nat}
    (h547 : mpl.base 547 ≠ 0#64)
    (hHooks :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliRunHooksBundleFd mmpl ghFixed W A lim (ReadFileRuleEnvFixed cliIo.rd))
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliPubCalleesFrozenPlacedFd mmpl ghFixed A lim
        (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) sEnvs aEnvs W)
    (henc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).encrypt).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).initiate).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      SpineBPureFsCallees (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
        A lim sEnvs (aEnvs S).pksmTryFrom S decPkNeed) :
    h2ki_RunTightAt579PreFd hblk hext_nodup
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
      A lim
      (letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
       RunEnv (aEnvs S))
      S := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  exact hrun_cli_sem_full_placed_fd mmpl ghFixed W S h547 hHooks hpub
    henc hdecSig hinit hdecPkNeed hdecPk
    hpureFs.kemDeserialize hpureFs.tryFrom hpureFs.pksmTryFrom

/-! ## `h2ki_SpineBCanonSliceAt` and `h2ki_SpineBCanonSliceK` (`hmain` and `hinitSem`) -/

/-- Reduces `h2ki_SpineBCanonSliceAt` to the four Spine-C slot contracts (`464`, `463`, `521`,
`520` at `cliDecPkCanonSlotEnvExact'`), `CliPubCalleesFrozenPlacedFd`, and `SpineBPureFsCallees`. -/
theorem h2ksb_spineBCanonSliceAt_of_slots
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (ghFixed : CliGhostHooks)
    (hHooks :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliRunHooksBundleFd mmpl ghFixed W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (ReadFileRuleEnvFixed cliIo.rd))
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
          (cliRunSemD2c_placed X W)
          (cliDecryptPrekeyNeed cliRunBudgets))
    (hW1 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.E = CryptoGames.AES256.aes256Enc →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        h2ki_EncryptSlot464OkAtPreFd
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          X W)
    (hW2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        h2ki_DecryptSignalSlot463OkAtPreFd
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          X W)
    (hW3 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
        ∀ (γ : GhostName) (tp : BitVec 64),
        CliInitSlotOkPlacedPreFd mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (realCliInitBinarySlotEnvFixed W) X W)
    (hW4 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        DecPkD2cSlotOkFrozenPlacedAtPreFd
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) X W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliDecPkCanonSlotEnvExact' X W)) :
    h2ki_SpineBCanonSliceAt (mmpl := mmpl) hblk hext_nodup ghFixed := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  intro h547 X W hF hE hD hX hPub hF512 hEnc hDec hK γ tp
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let S := cliRunSemD2c_placed X W
  let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
    (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W)
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  exact h2ksb_runTightAt579PreFd_of_slots hLs hblk hext_nodup ghFixed
    A cliBudgetLimits W sEnvs
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      sEnvs (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
    S
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets)
    h547 (hHooks W γ tp) (hpub X W γ tp)
    (hW1 h547 X W hF hE hK γ tp)
    (hW2 h547 X W hF hD hX hPub hK γ tp)
    (hW3 h547 X W hF hX hPub hF512 hEnc γ tp S sEnvs needs rfl rfl rfl rfl rfl)
    (by decide)
    (hW4 h547 X W hF hD hX hPub hF512 hDec hK γ tp S needs sEnvs rfl rfl rfl rfl rfl)
    (hpureFs X W γ tp)

/-- Witness-packaged `h2ki_SpineBCanonSliceK w` closer from the four Spine-C slot contracts. -/
theorem h2ksb_spineBCanonSlice_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hHooksFd : F3WitnessRunHooksBundleFd w)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl w.ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
          (cliRunSemD2c_placed X W)
          (cliDecryptPrekeyNeed cliRunBudgets))
    (hW1 : h2ki_W1EncryptSlot464OkK w)
    (hW2 : h2ki_W2DecryptSignalSlot463OkK w)
    (hW3 : h2ki_W3InitSlot521OkK w)
    (hW4 : h2ki_W4DecPkCanonSlot520OkK w) :
    h2ki_SpineBCanonSliceK w :=
  h2ksb_spineBCanonSliceAt_of_slots hLs w.hblk w.hext_nodup w.ghFixed
    hHooksFd hpub hpureFs hW1 hW2 hW3 hW4

/-- Concrete `h2ki_SpineBCanonSliceK` closer at `mkF3CliElfGhostWitnessK`. -/
theorem h2ksb_spineBCanonSlice_mkWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
          (cliRunSemD2c_placed X W)
          (cliDecryptPrekeyNeed cliRunBudgets))
    (hW1 : h2ki_W1EncryptSlot464OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW2 : h2ki_W2DecryptSignalSlot463OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW3 : h2ki_W3InitSlot521OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW4 : h2ki_W4DecPkCanonSlot520OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)) :
    h2ki_SpineBCanonSliceK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2ksb_spineBCanonSlice_of_witnessK
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hLs
    (f3WitnessRunHooksBundleFd_mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hpub hpureFs hW1 hW2 hW3 hW4

/-! ## `h2ki_SpineBRunTightOfSemAt` and `h2ki_SpineBRunTightOfSemK` (D3 `RunSem` Slices) -/

/-- Discharges `h2ki_SpineBRunTightOfSemAt` for any `SemOf : CliHooks → RunSem` and
`sEnvsOf` / `PksmEnvOf`. -/
theorem h2ksb_spineBRunTightOfSemAt_of_slots
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (ghFixed : CliGhostHooks)
    (brkStart : BitVec 64)
    (SemOf : CliHooks → RunSem)
    (sEnvsOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliHooks → GhostName → BitVec 64 → RunSlotEnvs)
    (PksmEnvOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliHooks → GhostName → BitVec 64 → PksmGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hHooks :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliRunHooksBundleFd mmpl ghFixed W
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (ReadFileRuleEnvFixed cliIo.rd))
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (sEnvsOf W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W) decPkNeed)
    (henc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.E = CryptoGames.AES256.aes256Enc →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).initiate).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPk :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks), W.C.F = sha256Compress → ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)) :
    h2ki_SpineBRunTightOfSemAt (mmpl := mmpl) hblk hext_nodup ghFixed brkStart SemOf
      (fun W γ tp =>
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W))) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  intro h547 W hF hE hD hX hPub hF512 hEnc hDec hK γ tp
  exact h2ksb_runTightAt579PreFd_of_slots hLs hblk hext_nodup ghFixed
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits W
    (sEnvsOf W γ tp)
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (sEnvsOf W γ tp) (PksmEnvOf W γ tp))
    (SemOf W)
    (decPkNeed := decPkNeed)
    h547 (hHooks W γ tp) (hpub W γ tp)
    (henc h547 W hF hE hK γ tp)
    (hdecSig h547 W hF hD hX hPub hK γ tp)
    (hinit h547 W hF hX hPub hF512 hEnc γ tp)
    hdecPkNeed (hdecPk h547 W hF γ tp) (hpureFs W γ tp)

/-- Witness-packaged `h2ki_SpineBRunTightOfSemK w` closer for D3 `RunSem` slices. -/
theorem h2ksb_spineBRunTightOfSem_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hHooksFd : F3WitnessRunHooksBundleFd w)
    (SemOf : CliHooks → RunSem)
    (sEnvsOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      CliHooks → GhostName → BitVec 64 → RunSlotEnvs)
    (PksmEnvOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      CliHooks → GhostName → BitVec 64 → PksmGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl w.ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (sEnvsOf W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W) decPkNeed)
    (henc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.E = CryptoGames.AES256.aes256Enc →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).initiate).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPk :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks), W.C.F = sha256Compress → ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)) :
    h2ki_SpineBRunTightOfSemK w SemOf
      (fun W γ tp =>
        letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W))) :=
  h2ksb_spineBRunTightOfSemAt_of_slots hLs w.hblk w.hext_nodup w.ghFixed cliElfImage.brkStart
    SemOf sEnvsOf PksmEnvOf hdecPkNeed hHooksFd hpub hpureFs henc hdecSig hinit hdecPk

/-! ## D3 Untyped (`cliRunSemD3`) Specialization (`huntyped`) -/

/-- Transport `slotWithPreFdsGe3Closed` on `encSlotSpecPlaced` from `cliRunSemD2c_placed X W` to
`cliRunSemD3 W` (`g5ba_encSlotSpecPlaced_d2c_eq_d3`). -/
theorem h2ksb_encSlot464_d3_of_d2c [LibsignalPlacement]
    {M : AllocCostModel} {H : LibsignalHooks}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (EncEnv : EncGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h : (slotWithPreFdsGe3Closed
      (mkSlot (encSlotSpecPlaced A lim EncEnv (cliRunSemD2c_placed X W))
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt)).OkPlaced
      (lsProg_579 H) (lsmpl.base 464)) :
    (slotWithPreFdsGe3Closed
      (mkSlot (encSlotSpecPlaced A lim EncEnv (cliRunSemD3 W))
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed)).encrypt)).OkPlaced
      (lsProg_579 H) (lsmpl.base 464) := by
  change (slotWithPreFdsGe3Closed
    (mkSlot (encSlotSpecPlaced A lim EncEnv (cliRunSemD3 W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt)).OkPlaced
    (lsProg_579 H) (lsmpl.base 464)
  rw [← g5ba_encSlotSpecPlaced_d2c_eq_d3 A lim EncEnv X W]
  exact h

/-- Transport `slotWithPreFdsGe3Closed` on `decSigSlotSpecFrozenPlaced` from
`cliRunSemD2c_placed X W` to `cliRunSemD3 W` (`g5ba_decSigSlotSpecFrozenPlaced_d2c_eq_d3`). -/
theorem h2ksb_decSigSlot463_d3_of_d2c [LibsignalPlacement]
    {M : AllocCostModel} {H : LibsignalHooks}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h : (slotWithPreFdsGe3Closed
      (mkSlot (decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemD2c_placed X W))
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal)).OkPlaced
      (lsProg_579 H) (lsmpl.base 463)) :
    (slotWithPreFdsGe3Closed
      (mkSlot (decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemD3 W))
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed)).decryptSignal)).OkPlaced
      (lsProg_579 H) (lsmpl.base 463) := by
  change (slotWithPreFdsGe3Closed
    (mkSlot (decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemD3 W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal)).OkPlaced
    (lsProg_579 H) (lsmpl.base 463)
  rw [← g5ba_decSigSlotSpecFrozenPlaced_d2c_eq_d3 A lim DecSigEnv X W]
  exact h

/-- Untyped D3 `RunSlotEnvs` family at `[LibsignalPlacement]`, matching
`ElfSlicesPqOomH2KIfaces.h2ki_UntypedDecPkSlot520OkK` and `ElfSlicesPqOomH2KSpineA.h2k_untypedRunEnvAt`. -/
noncomputable abbrev h2ksb_untypedSlotEnvs [LibsignalPlacement] {mmpl : MultiPlacement}
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) : RunSlotEnvs :=
  binaryKitRunSlotEnvsExact W
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
    cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
    (DecPkD3UntypedEnvOf
      (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
      cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
      SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv)

/-- Witness-packaged Spine-B `huntyped` (`cliRunSemD3`) closer at `w : F3CliElfGhostWitnessK`
from Slots `464`, `463`, `521`, and `h2ki_UntypedDecPkSlot520OkK w`. -/
theorem h2ksb_spineBUntyped_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hHooksFd : F3WitnessRunHooksBundleFd w)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl w.ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv)
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
          (cliRunSemD3 W)
          (cliDecryptPrekeyNeed cliRunBudgets_placed))
    (hW1 : h2ki_W1EncryptSlot464OkK w)
    (hW2 : h2ki_W2DecryptSignalSlot463OkK w)
    (hW3 : h2ki_W3InitSlot521OkK w)
    (hSlot520 : h2ki_UntypedDecPkSlot520OkK w) :
    h2ki_SpineBRunTightOfSemK w cliRunSemD3
      (fun W γ tp =>
        letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
            (cliRunSemD3 W))) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  exact h2ksb_spineBRunTightOfSem_of_witnessK w hLs hHooksFd cliRunSemD3
    (h2ksb_untypedSlotEnvs (mmpl := mmpl))
    (fun _ _ _ => PksmTryFromEnv)
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets_placed)
    (by decide)
    hpub hpureFs
    (fun h547 W hF hE hK γ tp =>
      h2ksb_encSlot464_d3_of_d2c
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliEncryptBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        defaultExtrasF3 W
        (hW1 h547 defaultExtrasF3 W hF hE hK γ tp))
    (fun h547 W hF hD hX hPub hK γ tp =>
      h2ksb_decSigSlot463_d3_of_d2c
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        defaultExtrasF3 W
        (hW2 h547 defaultExtrasF3 W hF hD hX hPub hK γ tp))
    (fun h547 W hF hX hPub hF512 hEnc γ tp =>
      hW3 h547 defaultExtrasF3 W hF hX hPub hF512 hEnc γ tp (cliRunSemD3 W)
        (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))
        rfl rfl rfl rfl rfl)
    hSlot520

/-- Concrete Spine-B `huntyped` closer at `mkF3CliElfGhostWitnessK`. -/
theorem h2ksb_spineBUntyped_mkWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv)
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
          (cliRunSemD3 W)
          (cliDecryptPrekeyNeed cliRunBudgets_placed))
    (hW1 : h2ki_W1EncryptSlot464OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW2 : h2ki_W2DecryptSignalSlot463OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW3 : h2ki_W3InitSlot521OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hSlot520 : h2ki_UntypedDecPkSlot520OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)) :
    h2ki_SpineBRunTightOfSemK
      (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
      cliRunSemD3
      (fun W γ tp =>
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
            (cliRunSemD3 W))) :=
  h2ksb_spineBUntyped_of_witnessK
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hLs
    (f3WitnessRunHooksBundleFd_mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hpub hpureFs hW1 hW2 hW3 hSlot520

/-! ## Two-Sided `FdsGe3Closed` Spine-B (`runSpecTightPlacedFd`) via `withFds` -/

private theorem hookOk_of_pre_post {α : Type} {f : State → State} {spec1 spec2 : Spec α}
    (hok : HookOk f spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec1.post x s0 sf ∗ R) → (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    HookOk f spec2 := by
  intro x R s0 hrun hpre2 hsp
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun (hpre x R s0 hpre2) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩
  · exact Or.inl ⟨hret, hcc, hpost x R s0 (f s0) hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

/-- Lift `HookSat` on `withPreGuard P (withFdsGe3Closed (readFileSpecPlaced … A …))` to `withFds A`
when `lim.enforced = true`. -/
theorem hookSat_withPreGuard_withFdsGe3Closed_readFile_withFds
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {P : State → Prop} {rd : _} {pathOk : List (BitVec 8) → Prop} {stk : Nat}
    {ReadEnv : _} {hooks : String → Option (State → State)} {sym : String}
    (hsat : HookSat hooks sym
      (withPreGuard P (withFdsGe3Closed (readFileSpecPlaced rd pathOk A lim stk ReadEnv)))) :
    HookSat hooks sym
      (withPreGuard P
        (withFdsGe3Closed (readFileSpecPlaced rd pathOk (withFds A) lim stk ReadEnv))) := by
  rcases hsat with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, hookOk_of_pre_post hok rfl rfl rfl ?_ ?_⟩
  · rintro ⟨x, st⟩ R s0 hpre
    dsimp only [withPreGuard, withFdsGe3Closed, readFileSpecPlaced] at hpre ⊢
    rw [withFds_pool_enforced A henf] at hpre
    have hEq :
        (⌜P s0⌝ ∗ ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜s0.readReg64 .x0 = x.pathA ∧ (s0.readReg64 .x1).toNat = x.path.length ∧
            s0.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ pathOk x.path ∧
            LibsignalBinary.Heap.FitsEnv M lim st (ReadEnv s0.fs.files x.path)⌝ ∗
            (x.pathA ↦ₛ x.path) ∗ Arm64.memRegion x.ret 24 ∗
            ProofLib.stackAt s0.sp stk ∗
            (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0))) ∗ R =
        ⌜FdsGe3Closed s0.fs⌝ ∗
          ((⌜P s0⌝ ∗ ⌜FdsGe3Closed s0.fs⌝ ∗
            (⌜s0.readReg64 .x0 = x.pathA ∧ (s0.readReg64 .x1).toNat = x.path.length ∧
              s0.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ pathOk x.path ∧
              LibsignalBinary.Heap.FitsEnv M lim st (ReadEnv s0.fs.files x.path)⌝ ∗
              (x.pathA ↦ₛ x.path) ∗ Arm64.memRegion x.ret 24 ∗
              ProofLib.stackAt s0.sp stk ∗ A.pool lim st s0)) ∗ R) := by
      sep_ac_rfl
    rw [hEq, satisfies_pure_sepConj] at hpre
    exact hpre.2
  · rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withPreGuard, withFdsGe3Closed, readFileSpecPlaced, withFds_repAlloc] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hClosedF, hpost⟩
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [withFds_pool_enforced A henf]
    have hEq :
        (⌜ReadEnv s0.fs.files x.path evs⌝ ∗
          (∃∗ r : Except Unit (List (BitVec 8)),
            ⌜r = rd s0.fs.files x.path ∧ sf.trace = s0.trace⌝ ∗
              CryptoVerification.SignalSession.Cli.ioVecAt
                A.repAlloc x.ret r) ∗
          (x.pathA ↦ₛ x.path) ∗ ProofLib.stackAt s0.sp stk ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf)) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜ReadEnv s0.fs.files x.path evs⌝ ∗
            (∃∗ r : Except Unit (List (BitVec 8)),
              ⌜r = rd s0.fs.files x.path ∧ sf.trace = s0.trace⌝ ∗
                CryptoVerification.SignalSession.Cli.ioVecAt
                  A.repAlloc x.ret r) ∗
            (x.pathA ↦ₛ x.path) ∗ ProofLib.stackAt s0.sp stk ∗
            A.pool lim (M.stepEvents evs st) sf) ∗ R) := by
      sep_ac_rfl
    rw [hEq, satisfies_pure_sepConj]
    exact ⟨hClosedF, hpost⟩

/-- `HookSat` on `lsReadFileSym` at `h2k_ghFixedK mpl mmpl` for
`withLsRetAddr624AndFds (readFileSpecPlaced … (withFds (fineHookRustCliAllocBudget …)) …)`. -/
theorem h2ksb_hole2_readFile_hookSat_lsRetAddr624AndFds_withFds
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    HookSat
      (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      lsReadFileSym
      (withLsRetAddr624AndFds
        (readFileSpecPlaced cliIo.rd cliWrOk
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  exact hookSat_withPreGuard_withFdsGe3Closed_readFile_withFds rfl
    (h2ksb_hole2_readFile_hookSat_lsRetAddr624AndFds mpl mmpl hLs hMm W γ tp)

/-- Closes `CliRunHooksBundleFd` over `withFds (fineHookRustCliAllocBudget …)` at
`ghFixed := h2k_ghFixedK mpl mmpl`. -/
theorem h2ksb_hole2_hHooksBundleFd_withFds
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundleFd
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
        mmpl (h2k_ghFixedK mpl mmpl) W fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd) :=
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun W γ tp =>
    { runHooks := h2kb_runHooksPlaced_withFds mpl mmpl hLs hMm W γ tp
      readFileSat := h2ksb_hole2_readFile_hookSat_lsRetAddr624AndFds_withFds mpl mmpl hLs hMm W γ tp }

/-- Witness-packaged `CliRunHooksBundleFd` over `withFds` for `w : F3CliElfGhostWitnessK mpl mmpl`. -/
@[expose] def F3WitnessRunHooksBundleFdWf {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    @CliRunHooksBundleFd (libsignalPlacementOf mpl w.hblk w.hext_nodup)
      mmpl w.ghFixed W fineCostModel
      (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd)

theorem f3WitnessRunHooksBundleFdWf_mkF3CliElfGhostWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    F3WitnessRunHooksBundleFdWf (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2ksb_hole2_hHooksBundleFd_withFds mpl mmpl hLs hMm

/-- Converts `withPreFdsGe3Closed (runSpecTightPlaced … (withFds A) …)` to two-sided
`runSpecTightPlacedFd … A …` when `lim.enforced = true`, extracting `FdsGe3Closed sf.fs` from
`(withFds A).pool` in `post`. -/
theorem subroutine_ok_runSpecTightPlacedFd_of_preFd_withFds [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {CodeOk : Memory → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {RunEnvPred : RunCall → List AllocEvent → Prop}
    {uuidParse : UuidParser} {Run : Inputs → RunAnswer → Prop}
    {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    (h : subroutine_ok prog entry
      (withPreFdsGe3Closed
        (runSpecTightPlaced CodeOk (withFds A) lim RunEnvPred uuidParse Run wrOk resStack))) :
    subroutine_ok prog entry
      (runSpecTightPlacedFd CodeOk A lim RunEnvPred uuidParse Run wrOk resStack) := by
  refine subroutine_ok_mono h ?_ ?_
  · rintro ⟨g, st⟩ R s0 hp
    dsimp only [runSpecTightPlacedFd, withFdsGe3Closed, withPreFdsGe3Closed,
      runSpecTightPlaced, runSpecPlaced, withFds_repAlloc] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨hClosed0, hp⟩
    refine ⟨hClosed0, ?_⟩
    rw [withFds_pool_enforced A henf]
    let Pure0 : SepProp :=
      ⌜CodeOk s0.mem ∧ Run g.i g.a ∧
        CryptoVerification.SignalSession.Cli.MainHops.parseArgs uuidParse
          (g.i.argv.map Arm64.Process.bytesOfString) = some g.c ∧
        s0.readReg64 .x0 = g.res ∧ s0.readReg64 .x1 = g.call ∧ s0.readReg64 .x2 = g.stores ∧
        s0.readReg64 .x3 = g.inp ∧
        s0.readReg64 .x4 =
          BitVec.ofNat 64 (CryptoVerification.SignalSession.Cli.MainHops.inputOf g.i g.c).length ∧
        s0.fs.files =
          (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs g.i)).files ∧
        Arm64.Process.ProcessOutcome.traceStreamBytes .stdout s0.trace = [] ∧ resStack ≤ s0.sp.toNat ∧
        LibsignalBinary.Heap.FitsEnv M lim st (RunEnvPred g) ∧
        LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624
          (s0.readReg64 .x30)⌝
    change s0.mem ⊨
      (Pure0 ∗
        Arm64.memRegion g.res CryptoVerification.SignalSession.Cli.MainHops.runResSize ∗
        CryptoVerification.SignalSession.Cli.MainHops.callAt A.repAlloc g.call g.c ∗
        CryptoVerification.SignalSession.Cli.MainHops.storesAt A.repAlloc g.stores
          CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
        (g.inp ↦ₛ CryptoVerification.SignalSession.Cli.MainHops.inputOf g.i g.c) ∗
        CryptoVerification.SignalSession.Cli.MainHops.coinsInstalledPlaced
          g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
        CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        CryptoVerification.LibsignalTripleRatchet.lsLogOff ∗
        (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗
        ProofLib.stackAt s0.sp resStack) ∗ R
    have hEq :
        (Pure0 ∗
          Arm64.memRegion g.res CryptoVerification.SignalSession.Cli.MainHops.runResSize ∗
          CryptoVerification.SignalSession.Cli.MainHops.callAt A.repAlloc g.call g.c ∗
          CryptoVerification.SignalSession.Cli.MainHops.storesAt A.repAlloc g.stores
            CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
          (g.inp ↦ₛ CryptoVerification.SignalSession.Cli.MainHops.inputOf g.i g.c) ∗
          CryptoVerification.SignalSession.Cli.MainHops.coinsInstalledPlaced
            g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
          CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
          CryptoVerification.LibsignalTripleRatchet.lsLogOff ∗
          (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗
          ProofLib.stackAt s0.sp resStack) ∗ R =
        ⌜FdsGe3Closed s0.fs⌝ ∗
          ((Pure0 ∗
            Arm64.memRegion g.res CryptoVerification.SignalSession.Cli.MainHops.runResSize ∗
            CryptoVerification.SignalSession.Cli.MainHops.callAt A.repAlloc g.call g.c ∗
            CryptoVerification.SignalSession.Cli.MainHops.storesAt A.repAlloc g.stores
              CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
            (g.inp ↦ₛ CryptoVerification.SignalSession.Cli.MainHops.inputOf g.i g.c) ∗
            CryptoVerification.SignalSession.Cli.MainHops.coinsInstalledPlaced
              g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
            CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
            CryptoVerification.LibsignalTripleRatchet.lsLogOff ∗
            A.pool lim st s0 ∗
            ProofLib.stackAt s0.sp resStack) ∗ R) := by
      sep_ac_rfl
    rw [hEq, satisfies_pure_sepConj]
    exact ⟨hClosed0, hp⟩
  · rintro ⟨g, st⟩ R s0 sf hq
    dsimp only [runSpecTightPlacedFd, withFdsGe3Closed, withPreFdsGe3Closed,
      runSpecTightPlaced, runSpecPlaced, withFds_repAlloc] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨evs, hq⟩
    rw [withFds_pool_enforced A henf] at hq
    let PureF : SepProp :=
      ⌜RunEnvPred g evs ∧ s0.trace <+: sf.trace ∧
        sf.fs.files = s0.fs.files ∧
        Arm64.Process.ProcessOutcome.traceStreamBytes .stdout sf.trace =
          Arm64.Process.ProcessOutcome.traceStreamBytes .stdout s0.trace⌝
    let TailF : SepProp :=
      ProofLib.stackAt s0.sp resStack ∗
        (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = g.a⌝ ∗
          CryptoVerification.SignalSession.Cli.MainHops.runResAt A.repAlloc wrOk g.res a') ∗
        Arm64.anyHeap
    change sf.mem ⊨
      (PureF ∗
        Arm64.memRegion g.call 56 ∗ Arm64.memRegion g.stores 320 ∗
        (g.inp ↦ₛ CryptoVerification.SignalSession.Cli.MainHops.inputOf g.i g.c) ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        TailF) ∗ R at hq
    have hEq :
        (PureF ∗
          Arm64.memRegion g.call 56 ∗ Arm64.memRegion g.stores 320 ∗
          (g.inp ↦ₛ CryptoVerification.SignalSession.Cli.MainHops.inputOf g.i g.c) ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          TailF) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((PureF ∗
            Arm64.memRegion g.call 56 ∗ Arm64.memRegion g.stores 320 ∗
            (g.inp ↦ₛ CryptoVerification.SignalSession.Cli.MainHops.inputOf g.i g.c) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            TailF) ∗ R) := by
      sep_ac_rfl
    rw [hEq, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hClosedF, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hq⟩

/-- Discharges two-sided `h2ki_RunTightAt579Fd` at `A` from `withFds A` slot obligations when
`lim.enforced = true`. -/
theorem h2ksb_runTightAt579Fd_of_slots
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (ghFixed : CliGhostHooks)
    {M : AllocCostModel} (A : RustCliAllocBudget M) {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (W : CliHooks)
    (sEnvs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      RunSlotEnvs)
    (aEnvs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      RunSem → RunArmEnvs)
    (S : RunSem) {decPkNeed : Nat}
    (h547 : mpl.base 547 ≠ 0#64)
    (hHooks :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliRunHooksBundleFd mmpl ghFixed W (withFds A) lim (ReadFileRuleEnvFixed cliIo.rd))
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliPubCalleesFrozenPlacedFd mmpl ghFixed (withFds A) lim
        (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) sEnvs aEnvs W)
    (henc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced (withFds A) lim sEnvs S (cliRunNeeds decPkNeed)).encrypt).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced (withFds A) lim sEnvs S
          (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced (withFds A) lim sEnvs S
          (cliRunNeeds decPkNeed)).initiate).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced (withFds A) lim sEnvs S
          (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      SpineBPureFsCallees (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
        (withFds A) lim sEnvs (aEnvs S).pksmTryFrom S decPkNeed) :
    h2ki_RunTightAt579Fd hblk hext_nodup
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
      A lim
      (letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
       RunEnv (aEnvs S))
      S := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  exact subroutine_ok_runSpecTightPlacedFd_of_preFd_withFds henf
    (h2ksb_runTightAt579PreFd_of_slots hLs hblk hext_nodup ghFixed (withFds A) lim W
      sEnvs aEnvs S h547 hHooks hpub henc hdecSig hinit hdecPkNeed hdecPk hpureFs)

/-- Reduces `h2ki_SpineBCanonSliceAtFd` to the four `withFds` Spine-C slot contracts (`464`, `463`,
`521`, `520` at `cliDecPkCanonSlotEnvExact'`), `CliPubCalleesFrozenPlacedFd`, and
`SpineBPureFsCallees`. -/
theorem h2ksb_spineBCanonSliceAtFd_of_slots
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (ghFixed : CliGhostHooks)
    (hHooks :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliRunHooksBundleFd mmpl ghFixed W
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (ReadFileRuleEnvFixed cliIo.rd))
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl ghFixed
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
          (cliRunSemD2c_placed X W)
          (cliDecryptPrekeyNeed cliRunBudgets))
    (hW1 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.E = CryptoGames.AES256.aes256Enc →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        h2ki_EncryptSlot464OkAtPreFd
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          X W)
    (hW2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        h2ki_DecryptSignalSlot463OkAtPreFd
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          X W)
    (hW3 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
        ∀ (γ : GhostName) (tp : BitVec 64),
        CliInitSlotOkPlacedPreFd mmpl ghFixed
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (realCliInitBinarySlotEnvFixed W) X W)
    (hW4 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        DecPkD2cSlotOkFrozenPlacedAtPreFd
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) X W
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (cliDecPkCanonSlotEnvExact' X W)) :
    h2ki_SpineBCanonSliceAtFd (mmpl := mmpl) hblk hext_nodup ghFixed := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  intro h547 X W hF hE hD hX hPub hF512 hEnc hDec hK γ tp
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let S := cliRunSemD2c_placed X W
  let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
    (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W)
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  exact h2ksb_runTightAt579Fd_of_slots hLs hblk hext_nodup ghFixed
    A (lim := cliBudgetLimits) rfl W sEnvs
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      sEnvs (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
    S
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets)
    h547 (hHooks W γ tp) (hpub X W γ tp)
    (hW1 h547 X W hF hE hK γ tp)
    (hW2 h547 X W hF hD hX hPub hK γ tp)
    (hW3 h547 X W hF hX hPub hF512 hEnc γ tp S sEnvs needs rfl rfl rfl rfl rfl)
    (by decide)
    (hW4 h547 X W hF hD hX hPub hF512 hDec hK γ tp S needs sEnvs rfl rfl rfl rfl rfl)
    (hpureFs X W γ tp)

/-- Witness-packaged `h2ki_SpineBCanonSliceFdK w` closer from the four `withFds` Spine-C slots. -/
theorem h2ksb_spineBCanonSliceFd_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hHooksFd : F3WitnessRunHooksBundleFdWf w)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl w.ghFixed
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
          (cliRunSemD2c_placed X W)
          (cliDecryptPrekeyNeed cliRunBudgets))
    (hW1 : h2ki_W1EncryptSlot464OkWfK w)
    (hW2 : h2ki_W2DecryptSignalSlot463OkWfK w)
    (hW3 : h2ki_W3InitSlot521OkWfK w)
    (hW4 : h2ki_W4DecPkCanonSlot520OkWfK w) :
    h2ki_SpineBCanonSliceFdK w :=
  h2ksb_spineBCanonSliceAtFd_of_slots hLs w.hblk w.hext_nodup w.ghFixed
    hHooksFd hpub hpureFs hW1 hW2 hW3 hW4

/-- Concrete `h2ki_SpineBCanonSliceFdK` closer at `mkF3CliElfGhostWitnessK`. -/
theorem h2ksb_spineBCanonSliceFd_mkWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hpub :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
              (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
          W)
    (hpureFs :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
          (cliRunSemD2c_placed X W)
          (cliDecryptPrekeyNeed cliRunBudgets))
    (hW1 : h2ki_W1EncryptSlot464OkWfK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW2 : h2ki_W2DecryptSignalSlot463OkWfK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW3 : h2ki_W3InitSlot521OkWfK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW4 : h2ki_W4DecPkCanonSlot520OkWfK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)) :
    h2ki_SpineBCanonSliceFdK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2ksb_spineBCanonSliceFd_of_witnessK
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hLs
    (f3WitnessRunHooksBundleFdWf_mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hpub hpureFs hW1 hW2 hW3 hW4

/-- Discharges `h2ki_SpineBRunTightOfSemAtFd` for any `SemOf : CliHooks → RunSem` and
`sEnvsOf` / `PksmEnvOf` from `withFds` slot contracts. -/
theorem h2ksb_spineBRunTightOfSemAtFd_of_slots
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (ghFixed : CliGhostHooks)
    (brkStart : BitVec 64)
    (SemOf : CliHooks → RunSem)
    (sEnvsOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliHooks → GhostName → BitVec 64 → RunSlotEnvs)
    (PksmEnvOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliHooks → GhostName → BitVec 64 → PksmGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hHooks :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliRunHooksBundleFd mmpl ghFixed W
          (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) cliBudgetLimits
          (ReadFileRuleEnvFixed cliIo.rd))
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl ghFixed
          (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (sEnvsOf W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) cliBudgetLimits
          (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W) decPkNeed)
    (henc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.E = CryptoGames.AES256.aes256Enc →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).initiate).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPk :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks), W.C.F = sha256Compress → ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)) :
    h2ki_SpineBRunTightOfSemAtFd (mmpl := mmpl) hblk hext_nodup ghFixed brkStart SemOf
      (fun W γ tp =>
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W))) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  intro h547 W hF hE hD hX hPub hF512 hEnc hDec hK γ tp
  exact h2ksb_runTightAt579Fd_of_slots hLs hblk hext_nodup ghFixed
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) (lim := cliBudgetLimits) rfl W
    (sEnvsOf W γ tp)
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (sEnvsOf W γ tp) (PksmEnvOf W γ tp))
    (SemOf W)
    (decPkNeed := decPkNeed)
    h547 (hHooks W γ tp) (hpub W γ tp)
    (henc h547 W hF hE hK γ tp)
    (hdecSig h547 W hF hD hX hPub hK γ tp)
    (hinit h547 W hF hX hPub hF512 hEnc γ tp)
    hdecPkNeed (hdecPk h547 W hF γ tp) (hpureFs W γ tp)

/-- Witness-packaged `h2ki_SpineBRunTightOfSemFdK w` closer for D3 `RunSem` slices. -/
theorem h2ksb_spineBRunTightOfSemFd_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hHooksFd : F3WitnessRunHooksBundleFdWf w)
    (SemOf : CliHooks → RunSem)
    (sEnvsOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      CliHooks → GhostName → BitVec 64 → RunSlotEnvs)
    (PksmEnvOf :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      CliHooks → GhostName → BitVec 64 → PksmGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl w.ghFixed
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (sEnvsOf W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp))
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W) decPkNeed)
    (henc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.E = CryptoGames.AES256.aes256Enc →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
        ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).initiate).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPk :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks), W.C.F = sha256Compress → ∀ (γ : GhostName) (tp : BitVec 64),
        (slotWithPreFdsGe3Closed
          (slotsOfSigPkFrozenPlaced
            (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
            (sEnvsOf W γ tp) (SemOf W) (cliRunNeeds decPkNeed)).decryptPrekey).OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)) :
    h2ki_SpineBRunTightOfSemFdK w SemOf
      (fun W γ tp =>
        letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (sEnvsOf W γ tp) (PksmEnvOf W γ tp) (SemOf W))) :=
  h2ksb_spineBRunTightOfSemAtFd_of_slots hLs w.hblk w.hext_nodup w.ghFixed cliElfImage.brkStart
    SemOf sEnvsOf PksmEnvOf hdecPkNeed hHooksFd hpub hpureFs henc hdecSig hinit hdecPk

/-- Witness-packaged two-sided Spine-B `huntyped` (`cliRunSemD3`) closer at
`w : F3CliElfGhostWitnessK` from `withFds` Slots `464`, `463`, `521`, and `520`. -/
theorem h2ksb_spineBUntypedFd_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hHooksFd : F3WitnessRunHooksBundleFdWf w)
    (hpub :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl w.ghFixed
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv)
          W)
    (hpureFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
          (cliRunSemD3 W)
          (cliDecryptPrekeyNeed cliRunBudgets_placed))
    (hW1 : h2ki_W1EncryptSlot464OkWfK w)
    (hW2 : h2ki_W2DecryptSignalSlot463OkWfK w)
    (hW3 : h2ki_W3InitSlot521OkWfK w)
    (hSlot520 : h2ki_UntypedDecPkSlot520OkWfK w) :
    h2ki_SpineBRunTightOfSemFdK w cliRunSemD3
      (fun W γ tp =>
        letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
            (cliRunSemD3 W))) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  exact h2ksb_spineBRunTightOfSemFd_of_witnessK w hLs hHooksFd cliRunSemD3
    (h2ksb_untypedSlotEnvs (mmpl := mmpl))
    (fun _ _ _ => PksmTryFromEnv)
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets_placed)
    (by decide)
    hpub hpureFs
    (fun h547 W hF hE hK γ tp =>
      h2ksb_encSlot464_d3_of_d2c
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
        (cliEncryptBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        defaultExtrasF3 W
        (hW1 h547 defaultExtrasF3 W hF hE hK γ tp))
    (fun h547 W hF hD hX hPub hK γ tp =>
      h2ksb_decSigSlot463_d3_of_d2c
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
        (cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        defaultExtrasF3 W
        (hW2 h547 defaultExtrasF3 W hF hD hX hPub hK γ tp))
    (fun h547 W hF hX hPub hF512 hEnc γ tp =>
      hW3 h547 defaultExtrasF3 W hF hX hPub hF512 hEnc γ tp (cliRunSemD3 W)
        (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))
        rfl rfl rfl rfl rfl)
    hSlot520

/-- Concrete two-sided Spine-B `huntyped` closer at `mkF3CliElfGhostWitnessK`. -/
theorem h2ksb_spineBUntypedFd_mkWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hpub :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        CliPubCalleesFrozenPlacedFd mmpl (h2k_ghFixedK mpl mmpl)
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp)
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv)
          W)
    (hpureFs :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        SpineBPureFsCallees
          (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)) cliBudgetLimits
          (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
          (cliRunSemD3 W)
          (cliDecryptPrekeyNeed cliRunBudgets_placed))
    (hW1 : h2ki_W1EncryptSlot464OkWfK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW2 : h2ki_W2DecryptSignalSlot463OkWfK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hW3 : h2ki_W3InitSlot521OkWfK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2))
    (hSlot520 : h2ki_UntypedDecPkSlot520OkWfK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)) :
    h2ki_SpineBRunTightOfSemFdK
      (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
      cliRunSemD3
      (fun W γ tp =>
        letI : LibsignalPlacement :=
          libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2ksb_untypedSlotEnvs (mmpl := mmpl) W γ tp) PksmTryFromEnv
            (cliRunSemD3 W))) :=
  h2ksb_spineBUntypedFd_of_witnessK
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hLs
    (f3WitnessRunHooksBundleFdWf_mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hpub hpureFs hW1 hW2 hW3 hSlot520

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineB

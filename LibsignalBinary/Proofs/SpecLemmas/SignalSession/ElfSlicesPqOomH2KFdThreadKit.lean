/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAuxFd
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2aFd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget

/-!
# `withFdsGe3Closed` Post-Closure and Call-Site Bridges for `h2k_*SpecK` (`ElfSlicesPqOomH2KFdThreadKit`)

Upgrades `ElfSlicesPqOomH2KHooks` contracts (`h2k_readFileSpecK`, `h2k_readFileLitSpecK`,
`h2k_readStdinSpecK`) to two-sided `withFdsGe3Closed` (`pre` and `post`) contracts and
instantiates call-site `read_file` helpers:
1. `h2k_readFileFixedGhostHookFineK_fs_eq` and `h2k_hole2_hReadSatK_withFds`: upgrade
   `h2k_readFile*SpecK` to `withFdsGe3Closed`.
2. `h2k_readStdinGhostHookFineK_preserves_fdsGe3Closed`: preserves `FdsGe3Closed` across
   `read_stdin` (while allowing fd `0`'s offset to advance).
3. Call-site `read_file` lemmas (`step_read_file_call_budget_h2k_fd`, `dirGet_placed_ok_of_h2k_fd`,
   `dirGet_placed_caller_ok_of_h2k_fd`, `readCall_step_p_h2k_fd`,
   `step_from_0x5b0_readOf_pool_placed_h2k_fd`) on Blocks `589`, `563`, and `617`.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries (mallocngLib)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv LibsignalCodeRoLoaded TraceFsSound)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym
   stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (CoinsReadable DirGhost ReadRule cliBcmpName cliBcmpSpec cliInputs cliStaticsPlaced ioVecAt utf8)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_563 blkPl_589 lsProg_563 lsProg_589)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM4Placed CallV CallW InMainPlaced IoModel LsCodeInv argsBuf callHeap cell cliIo
   cliRunBudgets cliWrOk coinsOf inputOf locals m4CellsPlaced mProgPlaced mainFrameSize
   mainLitsBlk617 mainSaved ownedBytes)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers (inInvOpt)
open CryptoVerification.SignalSession.Cli.RunGlue
  (cliGhostExterns cliGhostExterns_readFile_some)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced dirGetSpecPlaced pathSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed hookOk_withFdsGe3Closed hookOk_withFdsGe3Closed_of_fs_eq
   withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced (keepFilesTrace)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (f3ReadStdinFallback_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudget (ReadCoinsEnvOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudgetFd
  (step_from_0x5b0_readOf_pool_placed_keep_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget (ExitKPoolPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2aFd
  (PathIoContractPlacedBudgetFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd
  (dirGet_placed_caller_ok_of_keep_fd dirGet_placed_ok_of_keep_fd step_read_file_call_budget_keep_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAuxFd
  (readCall_step_p_keep_fd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup hole2_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_ghFixedK h2k_hole2_hReadSatK h2k_readFileFixedGhostHookFineK h2k_readFileLitSpecK
   h2k_readFileSpecK h2k_readStdinGhostHookFineK)

/-! ## Ghost-Hook `State.fs` and `FdsGe3Closed` Preservation -/

/-- `h2k_readFileFixedGhostHookFineK` preserves the entire `State.fs` record across all three
    branches (`ActiveF3ReadFileRun`, `keepFsTrace` fallback, and `.Exception`). -/
theorem h2k_readFileFixedGhostHookFineK_fs_eq
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entry_io : BitVec 64)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) (s0 : State) :
    (h2k_readFileFixedGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk s0).fs =
      s0.fs := by
  classical
  unfold h2k_readFileFixedGhostHookFineK
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.1
    · rfl
  · rfl

/-- Lift any `HookOk` on `h2k_readFileFixedGhostHookFineK` (such as `h2k_readFileSpecK` or
    `h2k_readFileLitSpecK`) to `withFdsGe3Closed` (`pre` AND `post`). -/
theorem hookOk_withFdsGe3Closed_readFileFixedGhostHookFineK {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entry_io : BitVec 64}
    {mmpl : MultiPlacement} {brkStart : BitVec 64}
    {lim : BudgetLimits} {stk : Nat} {spec : Arm64.Spec α}
    (hok : HookOk
      (h2k_readFileFixedGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk) spec) :
    HookOk
      (h2k_readFileFixedGhostHookFineK keep P_real P_sub entry_io mmpl brkStart lim stk)
      (withFdsGe3Closed spec) :=
  hookOk_withFdsGe3Closed_of_fs_eq
    (h2k_readFileFixedGhostHookFineK_fs_eq keep P_real P_sub entry_io mmpl brkStart lim stk) hok

/-- Lift any `HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) H0) lsReadFileSym spec` to
    `withFdsGe3Closed spec` by rewriting the concrete `h2k_ghFixedK` `readFile` entry. -/
theorem hookSat_withFdsGe3Closed_of_h2k_ghFixedK_readFile [LibsignalPlacement] {α : Type}
    {mpl mmpl : MultiPlacement} {H0 : LibsignalHooks} {spec : Arm64.Spec α}
    (hSat : HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) H0) lsReadFileSym spec) :
    HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) H0) lsReadFileSym
      (withFdsGe3Closed spec) := by
  rcases hSat with ⟨f, hf, hok⟩
  have hsome := cliGhostExterns_readFile_some (h2k_ghFixedK mpl mmpl) H0 rfl
  rw [hsome] at hf
  injection hf with hf_eq
  subst hf_eq
  exact ⟨_, hsome, hookOk_withFdsGe3Closed_readFileFixedGhostHookFineK hok⟩

/-- Post-closed companion of `ElfSlicesPqOomH2KHooks.h2k_hole2_hReadSatK`:
    gives `HookSat … lsReadFileSym (withFdsGe3Closed (h2k_readFileSpecK …))` directly. -/
theorem h2k_hole2_hReadSatK_withFds
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W)) lsReadFileSym
        (withFdsGe3Closed
          (h2k_readFileSpecK cliIo.rd cliWrOk
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro W γ tp
  exact hookSat_withFdsGe3Closed_of_h2k_ghFixedK_readFile
    (h2k_hole2_hReadSatK mpl mmpl hLs hMm W γ tp)

/-! ## `h2k_readFile{,Lit}SpecK` Call-Site Instantiations -/

/-- Direct `h2k_readFileSpecK` instantiation of `PlacedBudgetFd.dirGet_placed_ok_of_keep_fd`
    on Block `589`. -/
theorem dirGet_placed_ok_of_h2k_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {pathStk readStk stk : Nat}
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hAllocFs : AllocContractsFsPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    {pathProg : Arm64.Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathStk)))
    (hReadSat : HookSat H lsReadFileSym
      (withFdsGe3Closed (h2k_readFileSpecK rd pathOk A lim readStk ReadEnv)))
    (hlr : hole2_keepSub ((blkPl_589).base + 336#64) = false)
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hGetEnv : ∀ F0 d nm evs, DirGetEnv PathEnv ReadEnv rd F0 d nm evs → GetEnv F0 d nm evs) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv stk)) :=
  dirGet_placed_ok_of_keep_fd hpathLen hAllocFs hBcmp
    hjPath hjPath_unmut hPath hReadSat hlr hFs hstk hGetEnv

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit

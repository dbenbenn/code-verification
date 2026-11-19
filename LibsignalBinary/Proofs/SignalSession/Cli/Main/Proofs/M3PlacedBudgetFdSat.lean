/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Honest-Write-Spec `FdsGe3Closed`-Threaded `MainIoOfPlacedFdSat` (`M3PlacedBudgetFdSat`)

Honest-write-spec twin of `M3PlacedBudgetFd.MainIoOfPlacedFd` and its write-only projection
`MainIoOfPlacedFd.toWriteOnlyMainIo`, keeping `readStdin` and `readFile` unchanged while replacing
`writeFile` and `writeStdout` with `writeFileSpecPlacedSat` and `writeStdoutSpecPlacedSat` plus
the stack-floor bounds `hWriteFileStack` and `hWriteStdoutStack`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFdSat

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession
  (Inputs lsReadFileSym lsReadStdinSym lsWriteFileSym lsWriteStdoutSym stdinCapBytes)
open CryptoVerification.SignalSession.Cli (CoinsReadable cliInputs cliStaticsPlaced utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtCallPlaced AtM4Placed CallV CallW IoModel LsCodeInv argsBuf callCellsPlaced callHeap
   coinsOf inputOf locals m4CellsPlaced mProgPlaced mainFrameSize mainLitsBlk617 mainSaved
   ownedBytes parseArgs)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (withLsRetAddr624AndFds)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlacedSat (MainIoOfPlacedSat)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileSpecPlacedSat writeFileStackFloor writeStdoutSpecPlacedSat writeStdoutStackFloor)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudget (M3EnvReadOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd
  (VacuousIoAllocEnv main_m3_readOf_pool_placed_subroutine_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget (ExitKPoolPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv readFileLitSpecPlaced)

/-- Honest-write-spec twin of `M3PlacedBudgetFd.MainIoOfPlacedFd` on Block `617` (`lsProg_617 H`). -/
structure MainIoOfPlacedFdSat [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    (StdinEnv : List (BitVec 8) → List AllocEvent → Prop := ReadStdinBoundedEnv)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv io.rd) :
    Prop where
  readStdin : subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
    (withLsRoCl lsmpl (withFdsGe3Closed (readStdinSpecOfPlaced io A lim hookStack StdinEnv)))
  readFile : subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
    (withLsRoCl lsmpl (withLsRetAddr624AndFds (readFileLitSpecPlaced io A lim hookStack ReadEnv)))
  writeFile : subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
    (withLsRoCl lsmpl (withLsRet (writeFileSpecPlacedSat io A lim hookStack)))
  writeStdout : subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
    (withLsRoCl lsmpl (withLsRet (writeStdoutSpecPlacedSat A lim hookStack)))
  hWriteFileStack : writeFileStackFloor ≤ hookStack
  hWriteStdoutStack : writeStdoutStackFloor ≤ hookStack

private theorem not_fitsEnv_vacuousIoAllocEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (h : FitsEnv M lim st VacuousIoAllocEnv) : False := by
  have hev := (h [.alloc (2 ^ 64)] rfl).1.1
  exact absurd hev (by decide)

/-- Project `MainIoOfPlacedFdSat` to a write-only `MainIoOfPlacedSat` at `VacuousIoAllocEnv` for
    hops `M5` and `M6` (which never invoke `readStdin` or `readFile`). -/
theorem MainIoOfPlacedFdSat.toWriteOnlyMainIoSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoOfPlacedFdSat A lim H io hookStack StdinEnv ReadEnv) :
    MainIoOfPlacedSat A lim H io hookStack
      (fun _ => VacuousIoAllocEnv) (fun _ _ => VacuousIoAllocEnv) where
  readStdin := by
    refine subroutine_ok_intro fun (x, st) s0 R _ _ hpre => False.elim ?_
    dsimp only [withLsRoCl, readStdinSpecOfPlaced] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact not_fitsEnv_vacuousIoAllocEnv hpre.1.2.2.1
  readFile := by
    refine subroutine_ok_intro fun (x, st) s0 R _ _ hpre => False.elim ?_
    dsimp only [withLsRoCl, readFileLitSpecPlaced] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact not_fitsEnv_vacuousIoAllocEnv hpre.1.2.2.2.2.2
  writeFile := hio.writeFile
  writeStdout := hio.writeStdout
  hWriteFileStack := hio.hWriteFileStack
  hWriteStdoutStack := hio.hWriteStdoutStack

/-- Honest-write-spec `FdsGe3Closed`-threaded Hop M3 (`M+0x568 → M+0x5dc`, Block `617`):
    shares `main_m3_readOf_pool_placed_subroutine_fd` with `MainIoOfPlacedFd`. -/
theorem main_m3_readOf_pool_placed_proof_fd_sat [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlacedFdSat A lim H io hookStack StdinEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3EnvReadOf StdinEnv ReadEnv i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      M3EnvReadOf StdinEnv ReadEnv i c evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      FdsGe3Closed s'.fs →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs ms) s' ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  main_m3_readOf_pool_placed_subroutine_fd hc hio.readStdin hio.readFile hstk hstk64 hs0fs hs0tr
    hstdin hcoinsOk hcoins hparse hfit hs hexit hnext

theorem main_m3_bounded_readOf_pool_placed_proof_fd_sat [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ms : M.σ}
    {uuidParse : UuidParser} {io : IoModel}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {ArgvFrame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hio : MainIoOfPlacedFdSat A lim H io hookStack ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim ms (M3EnvReadOf ReadStdinBoundedEnv ReadEnv i c))
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64)
        (evs : List AllocEvent),
      M3EnvReadOf ReadStdinBoundedEnv ReadEnv i c evs →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      FdsGe3Closed s'.fs →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs ms) s' ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim ms s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom :=
  main_m3_readOf_pool_placed_proof_fd_sat hc hio hstk hstk64 hs0fs hs0tr hstdin hcoinsOk hcoins
    hparse hfit hs hexit hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFdSat

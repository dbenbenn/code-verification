/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.IoSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SymtabGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.GenLsBlockFast
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Bounded-Stdin Relocatable `MainIo` Contracts

Defines `ReadStdinBoundedEnv` (capping hook-side `read_stdin` allocations at `1 MiB` while
retaining the compiled 9-step `4 KiB .. 1 MiB` doubling schedule), `StdinEnv`-parameterized
`read_stdin` specs, and the Block-`617` I/O contract bundles `MainIoOfPlaced` and
`MainIoBoundedPlaced`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Process ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_rocl_of_plain withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession
  (lsReadFileSym lsReadStdinSym lsWriteFileSym lsWriteStdoutSym)
open CryptoVerification.SignalSession.CliExt
  (ReadStdinCall bytesAt cliPathOk readFileResult stdinBytes writeFileResult)
open CryptoVerification.SignalSession.Cli (ioVecAt)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (IoModel ReadFileLitGhost ReadStdinGhost WriteFileGhost WriteStdoutGhost cliIo)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (ReadStdinEnv allocBytes1Events cliIoCap cliIoCapIdx cliIoCapsEvents cliIoReadScheduleCaps
   readStdinBudgetCoreSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (MainIoPlaced ReadFileRuleEnv readFileLitSpecPlaced readStdinSpecPlaced
   writeFileSpecPlaced writeStdoutSpecPlaced)

/-! ## `ReadStdinBoundedEnv` -/

/-- Bounded-stdin allocator event envelope for `signal_session_io::read_stdin`: either the hook
branch (`allocBytes1Events bs` for `bs.length ≤ 1 MiB`, `[]` above `1 MiB`) or the compiled 9-cap
doubling schedule `4 KiB .. 1 MiB` (with `rustDeallocEvents 1048576 1` above `1 MiB`). -/
@[expose] def ReadStdinBoundedEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  (if bs.length ≤ 1048576 then evs = allocBytes1Events bs else evs = []) ∨
  (bs.length ≤ 1048576 ∧ evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 bs.length)) ∨
  (1048576 < bs.length ∧
    evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 1048576) ++ rustDeallocEvents 1048576 1)

theorem readStdinBoundedEnv_of_hook_le {bs : List (BitVec 8)} {evs : List AllocEvent}
    (hle : bs.length ≤ 1048576) (hevs : evs = allocBytes1Events bs) :
    ReadStdinBoundedEnv bs evs := by
  unfold ReadStdinBoundedEnv
  simp only [hle, ↓reduceIte]
  exact Or.inl hevs

theorem readStdinBoundedEnv_of_hook_gt {bs : List (BitVec 8)} {evs : List AllocEvent}
    (hgt : ¬ bs.length ≤ 1048576) (hevs : evs = []) :
    ReadStdinBoundedEnv bs evs := by
  unfold ReadStdinBoundedEnv
  simp only [hgt, ↓reduceIte]
  exact Or.inl hevs

theorem readStdinBoundedEnv_cliIoCaps8_ok {bs : List (BitVec 8)} (hle : bs.length ≤ 1048576) :
    ReadStdinBoundedEnv bs (cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 bs.length)) :=
  Or.inr (Or.inl ⟨hle, rfl⟩)

theorem readStdinBoundedEnv_cliIoCaps8_overCap {bs : List (BitVec 8)} (hgt : 1048576 < bs.length) :
    ReadStdinBoundedEnv bs
      (cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 bs.length) ++ rustDeallocEvents 1048576 1) := by
  have h8 : cliIoCapIdx 8 bs.length = 8 := by
    unfold cliIoCapIdx
    simp only [show ¬ bs.length ≤ cliIoCap 7 by change ¬ bs.length ≤ 524288; omega, ↓reduceIte]
  have hcap : cliIoReadScheduleCaps 8 bs.length = cliIoReadScheduleCaps 8 1048576 := by
    unfold cliIoReadScheduleCaps; simp only [show bs.length ≠ 0 by omega, h8, ↓reduceIte]; rfl
  rw [hcap]; exact Or.inr (Or.inr ⟨hgt, rfl⟩)

theorem readStdinBoundedEnv_iff_readStdinEnv_of_le {bs : List (BitVec 8)} {evs : List AllocEvent}
    (hle : bs.length ≤ 1048576) :
    ReadStdinBoundedEnv bs evs ↔ ReadStdinEnv bs evs := by
  unfold ReadStdinBoundedEnv ReadStdinEnv
  simp only [hle, ↓reduceIte]

/-! ## `StdinEnv`-parameterized `read_stdin` specifications -/

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-- `StdinEnv`-parameterized `read_stdin` specification (agrees with `readStdinSpecPlaced` at
`StdinEnv := ReadStdinEnv`). -/
@[expose] def readStdinSpecOfPlaced [LibsignalPlacement] {M : AllocCostModel} (io : IoModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (StdinEnv : List (BitVec 8) → List AllocEvent → Prop := ReadStdinBoundedEnv) :
    Spec (ReadStdinGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.ret ∧ io.stdin s.fs = some x.bs ∧
      FitsEnv M lim st (StdinEnv x.bs) ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜StdinEnv x.bs evs⌝ ∗
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜sf.fs.files = s0.fs.files ∧
            r = CryptoVerification.SignalSession.readStdinResult x.bs ∧
            sf.trace = s0.trace⌝ ∗
            ioVecAt A.repAlloc x.ret r) ∗
        stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

theorem readStdinSpecOfPlaced_eq_readStdinSpecPlaced [LibsignalPlacement]
    {M : AllocCostModel} (io : IoModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    readStdinSpecOfPlaced io A lim stk ReadStdinEnv = readStdinSpecPlaced io A lim stk :=
  rfl

theorem readStdinSpecOfPlaced_congr_env [LibsignalPlacement]
    {M : AllocCostModel} (io : IoModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    {StdinEnv₁ StdinEnv₂ : List (BitVec 8) → List AllocEvent → Prop}
    (henv : ∀ bs evs, StdinEnv₁ bs evs ↔ StdinEnv₂ bs evs) :
    readStdinSpecOfPlaced io A lim stk StdinEnv₁ =
      readStdinSpecOfPlaced io A lim stk StdinEnv₂ := by
  have heq : StdinEnv₁ = StdinEnv₂ := funext fun bs => funext fun evs => propext (henv bs evs)
  subst heq
  rfl

@[expose] def readStdinBudgetCoreOfSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (StdinEnv : List (BitVec 8) → List AllocEvent → Prop := ReadStdinBoundedEnv) :
    Spec (ReadStdinCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.ret ∧ stdinBytes s.fs = some x.bs ∧
      FitsEnv M lim st (StdinEnv x.bs) ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.ret 24 ∗ stackAt s.sp extHookStack ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜StdinEnv x.bs evs⌝ ∗
      (∃∗ r : Except Unit (List (BitVec 8)),
        ⌜sf.fs.files = s0.fs.files ∧
          r = CryptoVerification.SignalSession.readStdinResult x.bs ∧
          sf.trace = s0.trace⌝ ∗
          CryptoVerification.SignalSession.CliExt.ioVecAt A.repAlloc x.ret r) ∗
      stackAt s0.sp extHookStack ∗ A.pool lim (M.stepEvents evs st) sf

theorem readStdinBudgetCoreOfSpec_eq_readStdinBudgetCoreSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    readStdinBudgetCoreOfSpec M A lim ReadStdinEnv = readStdinBudgetCoreSpec M A lim :=
  rfl

/-! ## `MainIoOfPlaced` and `MainIoBoundedPlaced` -/

/-- Envelope-parameterized relocatable `MainIo` on Block `617` (`lsProg_617 H`). -/
structure MainIoOfPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    (StdinEnv : List (BitVec 8) → List AllocEvent → Prop := ReadStdinBoundedEnv)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv io.rd) :
    Prop where
  readStdin : subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
    (withLsRoCl lsmpl (readStdinSpecOfPlaced io A lim hookStack StdinEnv))
  readFile : subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
    (withLsRoCl lsmpl (readFileLitSpecPlaced io A lim hookStack ReadEnv))
  writeFile : subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
    (withLsRoCl lsmpl (writeFileSpecPlaced io A lim hookStack))
  writeStdout : subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
    (withLsRoCl lsmpl (writeStdoutSpecPlaced A lim hookStack))

/-- `StdinEnv`-parameterized `MainIoOfPlaced` at `ReadEnv := ReadFileRuleEnv io.rd`. -/
abbrev MainIoBoundedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    (StdinEnv : List (BitVec 8) → List AllocEvent → Prop := ReadStdinBoundedEnv) : Prop :=
  MainIoOfPlaced A lim H io hookStack StdinEnv (ReadFileRuleEnv io.rd)

theorem mainIoBoundedPlaced_iff_mainIoPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat) :
    MainIoBoundedPlaced A lim H io hookStack ReadStdinEnv ↔
      MainIoPlaced A lim H io hookStack :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

theorem mainIoBoundedPlaced_eq_mainIoPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat) :
    MainIoBoundedPlaced A lim H io hookStack ReadStdinEnv =
      MainIoPlaced A lim H io hookStack :=
  propext (mainIoBoundedPlaced_iff_mainIoPlaced A lim H io hookStack)

theorem mainIoOfPlaced_eq_of_env [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    {StdinEnv₁ StdinEnv₂ : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv₁ ReadEnv₂ : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hstdin : ∀ bs evs, StdinEnv₁ bs evs ↔ StdinEnv₂ bs evs)
    (hread : ∀ fs p evs, ReadEnv₁ fs p evs ↔ ReadEnv₂ fs p evs) :
    MainIoOfPlaced A lim H io hookStack StdinEnv₁ ReadEnv₁ =
      MainIoOfPlaced A lim H io hookStack StdinEnv₂ ReadEnv₂ := by
  have hs : StdinEnv₁ = StdinEnv₂ := funext fun bs => funext fun evs => propext (hstdin bs evs)
  have hr : ReadEnv₁ = ReadEnv₂ :=
    funext fun fs => funext fun p => funext fun evs => propext (hread fs p evs)
  subst hs; subst hr; rfl

theorem mainIoOfPlaced_iff_of_env [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    {StdinEnv₁ StdinEnv₂ : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv₁ ReadEnv₂ : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hstdin : ∀ bs evs, StdinEnv₁ bs evs ↔ StdinEnv₂ bs evs)
    (hread : ∀ fs p evs, ReadEnv₁ fs p evs ↔ ReadEnv₂ fs p evs) :
    MainIoOfPlaced A lim H io hookStack StdinEnv₁ ReadEnv₁ ↔
      MainIoOfPlaced A lim H io hookStack StdinEnv₂ ReadEnv₂ := by
  rw [mainIoOfPlaced_eq_of_env A lim H io hookStack hstdin hread]

theorem mainIoBoundedPlaced_eq_of_env [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    {StdinEnv₁ StdinEnv₂ : List (BitVec 8) → List AllocEvent → Prop}
    (hstdin : ∀ bs evs, StdinEnv₁ bs evs ↔ StdinEnv₂ bs evs) :
    MainIoBoundedPlaced A lim H io hookStack StdinEnv₁ =
      MainIoBoundedPlaced A lim H io hookStack StdinEnv₂ :=
  mainIoOfPlaced_eq_of_env A lim H io hookStack hstdin (fun _ _ _ => Iff.rfl)

theorem mainIoBoundedPlaced_iff_of_env [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (io : IoModel) (hookStack : Nat)
    {StdinEnv₁ StdinEnv₂ : List (BitVec 8) → List AllocEvent → Prop}
    (hstdin : ∀ bs evs, StdinEnv₁ bs evs ↔ StdinEnv₂ bs evs) :
    MainIoBoundedPlaced A lim H io hookStack StdinEnv₁ ↔
      MainIoBoundedPlaced A lim H io hookStack StdinEnv₂ := by
  rw [mainIoBoundedPlaced_eq_of_env A lim H io hookStack hstdin]

/-! ## Block `617` call-site projections -/

theorem main_readStdin_of_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecOfPlaced io A lim hookStack StdinEnv)) :=
  hio.readStdin

theorem main_readStdin_bounded_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoBoundedPlaced A lim H io hookStack StdinEnv) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecOfPlaced io A lim hookStack StdinEnv)) :=
  hio.readStdin

theorem main_readFile_of_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced io A lim hookStack ReadEnv)) :=
  hio.readFile

theorem main_writeFile_of_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteFileSym)
      (withLsRoCl lsmpl (writeFileSpecPlaced io A lim hookStack)) :=
  hio.writeFile

theorem main_writeStdout_of_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoOfPlaced A lim H io hookStack StdinEnv ReadEnv) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlaced A lim hookStack)) :=
  hio.writeStdout

/-! ## Constructors from `read_stdin` contracts -/

theorem mainIoBoundedPlaced_of_mainIoPlaced_and_readStdin [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hio : MainIoPlaced A lim H io hookStack)
    (hstdin : subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecOfPlaced io A lim hookStack StdinEnv))) :
    MainIoBoundedPlaced A lim H io hookStack StdinEnv where
  readStdin := hstdin
  readFile := hio.readFile
  writeFile := hio.writeFile
  writeStdout := hio.writeStdout

theorem mainIoBoundedPlaced_of_mainIoPlaced_and_hook [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {f : State → State}
    (hio : MainIoPlaced A lim H io hookStack)
    (hrow : H lsReadStdinSym = some f)
    (hhook : HookOk f (readStdinSpecOfPlaced io A lim hookStack StdinEnv)) :
    MainIoBoundedPlaced A lim H io hookStack StdinEnv :=
  mainIoBoundedPlaced_of_mainIoPlaced_and_readStdin hio <|
    subroutine_ok_rocl_of_plain <|
      ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) ⟨f, hrow, hhook⟩ (by decide)

end LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced

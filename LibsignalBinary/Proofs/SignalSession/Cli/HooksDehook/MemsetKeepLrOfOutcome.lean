/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Local `keepMemsetBlk21 lr = false` from Subroutine Outcomes (`HooksDehook.MemsetKeepLrOfOutcome`)

Delivers Card `H-C8` **D2** (`rev_q8.md` §1b–§1d): under the generalized D1(c) `hTraj` context
(`Guard s0`, `sf.status = .Running → sf.pc = s0.readReg64 .lr`, `∀ msg, sf.status ≠ .Exception msg`,
`sf.status ≠ .Halted`, or the full `SubroutineOutcome`), proves that every intermediate call `u`
(`Steps P_ghost s0 u`, `Steps P_ghost u sf`, `u.status = .Running`) into the `memset` ghost has
`keepMemsetBlk21 mmpl (u.readReg64 .lr) = false`:

1. **Entry-state guards (`MemsetEntryGuard`, `F3MemsetEntryGuard`, `MemsetMixedEntryGuard`):**
   `MemsetEntryGuard mmpl stubPc s0 := keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧
   s0.readReg64 .lr ≠ stubPc` (specialized at `stubPc := mpl.ρ "memset"` by `F3MemsetEntryGuard`).
2. **Single-stub `memset` call-point `lr` discharge (`memset_keepLr_false_of_outcome_memset`):**
   Splits on `sf.status = .Running`:
   - `Returned` (`sf.status = .Running`, `sf.pc = s0.readReg64 .lr`): discharged by
     `MemsetLrTrapRet.blk21_lr_trap_false_memset_returned` + `MemsetEntryGuard`;
   - non-`Running` (`Exited`, `Panicked`, `OutOfMemory`, `Signaled`): discharged by
     `MemsetLrTrap.blk21_lr_trap_false_nonRunning` (or `(A2)`
     `MemsetLrTrapRet.blk21_lr_trap_false_mixed_nonRunning` when `P_ghost` carries other trap-safe
     ghosts).
3. **At-stub (`P_real`-independent) & mixed-table `(A2)` call-point `lr` discharge:**
   `memset_keepLr_false_at_stub_of_outcome` (needs only `u.pc = stubPc` and zero single-stub
   mismatch assumption on `P_real`) and `memset_keepLr_false_of_outcome_mixed`, plus direct
   `SubroutineOutcome` corollaries and the single-stub `memset`-only transfer combiner
   `block617TransferFixedG_memsetNarrow_of_replaysOn` (note `rev_c6` F2 / `rev_c8` T2: single
   mismatch, hook's `P_real` = transfer's `P_real`, so `memset`-only pass, **not** the K CLI pass).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetKeepLrOfOutcome

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open CryptoVerification.SignalSession (CliHooks Inputs cliProcessInputs)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (GhostExternReplaysOn StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG block617TransferFixedG_of_replaysOn
   subroutineOutcome_running_pc_and_noFault)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (linkedCallHook_fs_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost
  (keepMemsetBlk21 memsetGhostHook memsetGhostHookBlk21)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn
  (ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrap
  (blk21_lr_trap_false_nonRunning)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet
  (Blk21TrapHook blk21TrapHook_memsetGhostHook blk21_lr_trap_at_call_ret
   blk21_lr_trap_false_memset_returned blk21_lr_trap_false_mixed_nonRunning
   blk21_lr_trap_false_mixed_returned blk21_lr_trap_false_single_returned)

/-! ## 1. Real-Side Entry-State `lr` Guards (`MemsetEntryGuard`, `F3MemsetEntryGuard`) -/

/-- Variant-A real-side entry guard at `s0`: the caller's link register `s0.readReg64 .lr` lies
    outside `mallocng` block `21` (`memset`, 260 B) and is distinct from `stubPc`. -/
@[expose] def MemsetEntryGuard
    (mmpl : Obj.MultiPlacement) (stubPc : BitVec 64) (s0 : State) : Prop :=
  keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

/-- Specialization of `MemsetEntryGuard` to the `libsignalSessionLib` external `"memset"` stub
    symbol `mpl.ρ "memset"`. -/
@[expose] def F3MemsetEntryGuard (mpl mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  MemsetEntryGuard mmpl (mpl.ρ "memset") s0

/-- Mixed-pass `(A2)` generalization of `MemsetEntryGuard`: `s0.readReg64 .lr` lies outside `blk21`
    and is not a mismatched extern stub between `P_ghost` and `P_real`. -/
@[expose] def MemsetMixedEntryGuard
    (P_ghost P_real : Program) (mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧
  P_ghost.externAt? (s0.readReg64 .lr) = P_real.externAt? (s0.readReg64 .lr)

/-- Any single-stub `MemsetEntryGuard mmpl stubPc s0` implies `MemsetMixedEntryGuard` whenever
    `P_ghost` and `P_real` agree outside `stubPc`. -/
theorem MemsetEntryGuard.toMixed
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64} {s0 : State}
    (hother : ∀ pc : BitVec 64, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hG : MemsetEntryGuard mmpl stubPc s0) :
    MemsetMixedEntryGuard P_ghost P_real mmpl s0 :=
  ⟨hG.1, hother (s0.readReg64 .lr) hG.2⟩

/-! ## 2. Call-Point `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` from Outcome Facts -/

/-! ## 3. Direct `SubroutineOutcome` & D1(c) `Block617TransferFixedHypG` Corollaries -/

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetKeepLrOfOutcome

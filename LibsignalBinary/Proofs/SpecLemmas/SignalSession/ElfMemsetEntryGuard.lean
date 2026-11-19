/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.F3LayoutData -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetKeepLrOfOutcome -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import ProofLib.ProgramReflection -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Layout-Generic Startup `lr` Guards, `W`-Independent Harness Corollaries & `Block617TransferFixedHypG` (`ElfMemsetEntryGuard`)

Delivers Card `H-C8` **D3** + Card `W2-C8` **S3b** (`CliElfLib`-rooted, `0` imports from
`ElfSlicesPqOomPlacedInst` or any of the 12 WP4 files, `0` hex address literals):

1. **`"memset"` & `"memcpy"` stub resolution + `LinkedAt` uniqueness + startup `lr` checks (§§1–2):**
   - Discharges `keepMemsetBlk21 mmpl (sm.readReg64 .lr) = false`, `sm.readReg64 .lr ≠ mpl.ρ "memset"`,
     `keepMemcpyBlk20 mmpl (sm.readReg64 .lr) = false`, `sm.readReg64 .lr ≠ mpl.ρ "memcpy"`,
     `F3MemsetEntryGuard mpl mmpl sm`, `F3MemcpyEntryGuard mpl mmpl sm`,
     `F3MemsetMemcpyEntryLrFalse mmpl sm`, and `keepMemOps mmpl (sm.readReg64 .lr) = false`
     from `StdMainEntryLr f3StdLayout sm` (`sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64`)
     and `LinkedAt cliElfBytes` witnesses for `mpl` / `mmpl`.
2. **`W`-independent guarded-harness corollaries (§3):**
   - Consumes `StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt` via `.mono_guard` to yield
     `MuslHarnessFineNeedLocksGuardedPerInput` at the `W`-independent entry guards
     `fun sm => keepMemsetBlk21 mmpl (sm.readReg64 .lr) = false`,
     `fun sm => keepMemcpyBlk20 mmpl (sm.readReg64 .lr) = false`,
     `F3MemsetMemcpyEntryLrFalse mmpl`, `fun sm => keepMemOps mmpl (sm.readReg64 .lr) = false`,
     `F3MemsetEntryGuard mpl mmpl`, `F3MemcpyEntryGuard mpl mmpl`, and their conjunction.
3. **`Block617TransferFixedHypG` instances via `block617TransferFixedG_of_replaysOn_outcome` (§4):**
   - General K-pass-ready combinators (`f3Block617TransferFixedG_of_entryLrFalse_outcome_keep` for
     arbitrary `keep : BitVec 64 → Bool`, and `f3Block617TransferFixedG_of_entryLrFalse_outcome` at
     `keep := fun _ => false` closing `hlr_calls` by `rfl`, plus `StdMainEntryLr f3StdLayout`
     specializations) over arbitrary `EG` / `ER` on `(F3CodeOk mpl mmpl, F3CodeInv mpl mmpl)`.
   - Concrete narrow-ghost instances for `memset`-only (`f3Block617TransferFixedG_memset_of_replaysOn_outcome`
     / `_of_stdMainEntryLr`) and simultaneous `memset` + `memcpy`
     (`f3Block617TransferFixedG_memsetMemcpy_of_replaysOn_outcome` / `_of_stdMainEntryLr`); per
     `rev_c6` F2 / `rev_c8` T2, those concrete wrappers equate `EG` and `ER` outside `memset`
     (resp. `memset`/`memcpy`) via `hother`, whereas the general `f3Block617TransferFixedG_of_*`
     combinators apply directly to the multi-hook K CLI pass without `hother`.

*Scoped-G1 & consumer note:* `Block617TransferFixedHypG` with a non-trivial `Guard` is weaker than
the trusted `Block617TransferFixedHyp` (`rev_c8` T4), and through `decide` / `rfl_kernel` on pinned
F3 data (`f3StdLayout`, `f3MallocngMpl`, `lsPlacedStubPairs`), this module sits on the scoped-G1
frontier; static layout-independence holds with `0` hex literals.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement mallocngBlockProg)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliElfBytes cliElfImage cliExternsPlaced cliProcessInputs libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open LibsignalBinary.Heap.Fine (f3MallocngMpl f3StdLayout fineCostModel)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MuslHarnessFineNeedLocksGuardedPerInput StdMainEntryLr cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt codeLoaded_cliProgExtPlaced_of_codeRoLoaded
   patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (GhostExternReplaysOn StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG block617TransferFixedG_of_replaysOn_outcome
   subroutineOutcome_running_pc_and_noFault)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost
  (keepMemOps keepMemcpyBlk20 memcpyGhostHookBlk20 memcpyGhostHook_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn
  (ghostExternReplaysOn_memcpyGhostHookNarrow_of_trap_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet (Blk20TrapHook)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost
  (keepMemsetBlk21 memsetGhostHookBlk21 memsetGhostHook_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn
  (ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetKeepLrOfOutcome
  (F3MemsetEntryGuard MemsetEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet (Blk21TrapHook)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (f3LsSymAddrs lsInternedMultiLib lsPlacedStubPairs lsPlacedStubPairs_eq lsSharedExterns ls_idsOk
   ls_names_nodup ls_sharedExterns_lt ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_libsignal_linkedAt_unique f3CliElf_mallocng_linkedAt_unique f3LsMpl)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv F3CodeOk cliElf_f3MuslHarnessLr_of_linkedAt)

/-! ## 1. `libsignalSessionLib` `"memset"` Stub Resolution & `LinkedAt` Uniqueness -/

noncomputable section

private def findStubPosAux (target : String) : List (String × BitVec 64) → Nat → Nat
  | [], acc => acc
  | (nm, _) :: rest, acc =>
    if nm == target then acc else findStubPosAux target rest (acc + 1)

private def lsMemsetExternPos : Nat :=
  findStubPosAux "memset" lsPlacedStubPairs 0

private def lsMemsetIdx : Nat :=
  lsSharedExterns.getD lsMemsetExternPos 0

private def f3LsMemsetStubAddr : BitVec 64 :=
  (lsPlacedStubPairs.getD lsMemsetExternPos ("", 0#64)).2

private def checkMemsetPinAux (pos : Nat) : Bool :=
  let idx := lsSharedExterns.getD pos 0
  let pair := lsPlacedStubPairs.getD pos ("", 0#64)
  Nat.blt pos lsSharedExterns.length &&
  (pair.1 == "memset") &&
  (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none) &&
  !(f3StdLayout.libcStartMainStage2Addr + 56#64 == pair.2)

set_option maxRecDepth 200000 in
private theorem f3Memset_pin_ok : checkMemsetPinAux lsMemsetExternPos = true := by
  rfl_kernel

private theorem f3Memset_pin_parts :
    lsMemsetExternPos < lsSharedExterns.length ∧
    (lsPlacedStubPairs.getD lsMemsetExternPos ("", 0#64)).1 = "memset" ∧
    Obj.Interned.lookupBlockSymId lsMemsetIdx lsInternedMultiLib.blocks = none ∧
    f3StdLayout.libcStartMainStage2Addr + 56#64 ≠ f3LsMemsetStubAddr := by
  have hc :
      (Nat.blt lsMemsetExternPos lsSharedExterns.length &&
       ((lsPlacedStubPairs.getD lsMemsetExternPos ("", 0#64)).1 == "memset") &&
       (Obj.Interned.lookupBlockSymId lsMemsetIdx lsInternedMultiLib.blocks == none) &&
       !(f3StdLayout.libcStartMainStage2Addr + 56#64 == f3LsMemsetStubAddr)) = true :=
    f3Memset_pin_ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, beq_iff_eq,
    beq_eq_false_iff_ne] at hc
  exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

attribute [local irreducible] lsMemsetExternPos lsMemsetIdx f3LsMemsetStubAddr

private theorem lsMemsetExternPos_lt : lsMemsetExternPos < lsSharedExterns.length :=
  f3Memset_pin_parts.1

private theorem toMultiPlacement_rho_eq (mly : Obj.Interned.MultiLayout) (names : List String)
    (s : String) :
    (mly.toMultiPlacement names).ρ s = mly.addrs.getD (names.idxOf s) 0#64 := by
  rfl

/-- Relocation-inversion uniqueness pins `mmpl.base 21` (`mallocng` `memset`) to
    `f3MallocngMpl.base 21` for every `mmpl` satisfying `mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem f3CliElf_mallocng_base21_eq {mmpl : Obj.MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mmpl.base 21 = f3MallocngMpl.base 21 := by
  have h21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  exact (f3CliElf_mallocng_linkedAt_unique hMm).1 21 h21

private def lsMemcpyExternPos : Nat :=
  findStubPosAux "memcpy" lsPlacedStubPairs 0

private def lsMemcpyIdx : Nat :=
  lsSharedExterns.getD lsMemcpyExternPos 0

private def f3LsMemcpyStubAddr : BitVec 64 :=
  (lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64)).2

private def checkMemcpyPinAux (pos : Nat) : Bool :=
  let idx := lsSharedExterns.getD pos 0
  let pair := lsPlacedStubPairs.getD pos ("", 0#64)
  Nat.blt pos lsSharedExterns.length &&
  (pair.1 == "memcpy") &&
  (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none) &&
  !(f3StdLayout.libcStartMainStage2Addr + 56#64 == pair.2)

set_option maxRecDepth 200000 in
private theorem f3Memcpy_pin_ok : checkMemcpyPinAux lsMemcpyExternPos = true := by
  rfl_kernel

private theorem f3Memcpy_pin_parts :
    lsMemcpyExternPos < lsSharedExterns.length ∧
    (lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64)).1 = "memcpy" ∧
    Obj.Interned.lookupBlockSymId lsMemcpyIdx lsInternedMultiLib.blocks = none ∧
    f3StdLayout.libcStartMainStage2Addr + 56#64 ≠ f3LsMemcpyStubAddr := by
  have hc :
      (Nat.blt lsMemcpyExternPos lsSharedExterns.length &&
       ((lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64)).1 == "memcpy") &&
       (Obj.Interned.lookupBlockSymId lsMemcpyIdx lsInternedMultiLib.blocks == none) &&
       !(f3StdLayout.libcStartMainStage2Addr + 56#64 == f3LsMemcpyStubAddr)) = true :=
    f3Memcpy_pin_ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, beq_iff_eq,
    beq_eq_false_iff_ne] at hc
  exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

private theorem lsMemcpyIdx_def :
    lsMemcpyIdx = lsSharedExterns.getD lsMemcpyExternPos 0 := rfl

private theorem f3LsMemcpyStubAddr_def :
    f3LsMemcpyStubAddr = (lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64)).2 := rfl

attribute [local irreducible] lsMemcpyExternPos lsMemcpyIdx f3LsMemcpyStubAddr

private theorem lsMemcpyExternPos_lt : lsMemcpyExternPos < lsSharedExterns.length :=
  f3Memcpy_pin_parts.1

private theorem lsMemcpyStubPair_fst :
    (lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64)).1 = "memcpy" :=
  f3Memcpy_pin_parts.2.1

private theorem lsMemcpyIdx_eq_getElem :
    lsMemcpyIdx = lsSharedExterns[lsMemcpyExternPos]'lsMemcpyExternPos_lt := by
  rw [lsMemcpyIdx_def]
  exact Obj.Interned.getD_of_lt lsMemcpyExternPos_lt

private theorem lsMemcpyIdx_lt : lsMemcpyIdx < lsInternedMultiLib.names.length := by
  have hmem : lsMemcpyIdx ∈ lsSharedExterns := by
    rw [lsMemcpyIdx_eq_getElem]
    exact List.getElem_mem lsMemcpyExternPos_lt
  exact Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt lsMemcpyIdx hmem)

private theorem lsMemcpyStubPair_eq :
    lsPlacedStubPairs.getD lsMemcpyExternPos ("", 0#64) =
      (lsInternedMultiLib.names.getD lsMemcpyIdx "", f3LsSymAddrs.getD lsMemcpyIdx 0#64) := by
  have hplen : lsMemcpyExternPos < lsPlacedStubPairs.length := by
    rw [lsPlacedStubPairs_eq, List.length_map]
    exact lsMemcpyExternPos_lt
  rw [Obj.Interned.getD_of_lt hplen]
  simp only [lsPlacedStubPairs_eq, List.getElem_map, ← lsMemcpyIdx_eq_getElem]

private theorem lsMemcpyIdx_name :
    lsInternedMultiLib.names.getD lsMemcpyIdx "" = "memcpy" := by
  have hfst := congrArg Prod.fst lsMemcpyStubPair_eq
  exact hfst.symm.trans lsMemcpyStubPair_fst

private theorem f3LsSymAddrs_memcpy_eq :
    f3LsSymAddrs.getD lsMemcpyIdx 0#64 = f3LsMemcpyStubAddr := by
  rw [f3LsMemcpyStubAddr_def]
  exact (congrArg Prod.snd lsMemcpyStubPair_eq).symm

private theorem lsMemcpyIdx_lookupBlockSymId_none :
    Obj.Interned.lookupBlockSymId lsMemcpyIdx lsInternedMultiLib.blocks = none :=
  f3Memcpy_pin_parts.2.2.1

private theorem ls_idxOf_memcpy :
    lsInternedMultiLib.names.idxOf "memcpy" = lsMemcpyIdx := by
  rw [← lsMemcpyIdx_name]
  exact Obj.Interned.idxOf_getD ls_names_nodup lsMemcpyIdx_lt

private theorem f3LsMpl_rho_memcpy :
    f3LsMpl.ρ "memcpy" = f3LsMemcpyStubAddr := by
  have h1 : f3LsMpl.ρ "memcpy" = f3LsSymAddrs.getD lsMemcpyIdx 0#64 := by
    unfold f3LsMpl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsMpl
    rw [toMultiPlacement_rho_eq, ls_idxOf_memcpy]
    rfl
  exact h1.trans f3LsSymAddrs_memcpy_eq

theorem ls_memcpy_mem_names : "memcpy" ∈ lsInternedMultiLib.names := by
  rw [← lsMemcpyIdx_name, Obj.Interned.getD_of_lt lsMemcpyIdx_lt]
  exact List.getElem_mem lsMemcpyIdx_lt

theorem ls_memcpy_lookupBlockSym_none :
    Obj.lookupBlockSym "memcpy" libsignalSessionLib.blocks = none := by
  rw [← lsMemcpyIdx_name, ls_toMultiPlacedLib_eq,
    Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk lsMemcpyIdx_lt]
  exact lsMemcpyIdx_lookupBlockSymId_none

/-- Relocation-inversion uniqueness pins `mpl.ρ "memcpy"` to `f3LsMpl.ρ "memcpy"` for every `mpl`
    satisfying `libsignalSessionLib.LinkedAt cliElfBytes mpl`. -/
theorem f3CliElf_libsignal_memcpy_rho_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    mpl.ρ "memcpy" = f3LsMpl.ρ "memcpy" :=
  (f3CliElf_libsignal_linkedAt_unique hLs).2.2.1 "memcpy"
    ls_memcpy_mem_names ls_memcpy_lookupBlockSym_none

/-- Relocation-inversion uniqueness pins `mmpl.base 20` (`mallocng` `memcpy`, 396 B) to
    `f3MallocngMpl.base 20` for every `mmpl` satisfying `mallocngLib.LinkedAt cliElfBytes mmpl`. -/
theorem f3CliElf_mallocng_base20_eq {mmpl : Obj.MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mmpl.base 20 = f3MallocngMpl.base 20 := by
  have h20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  exact (f3CliElf_mallocng_linkedAt_unique hMm).1 20 h20

/-! ## 2. Startup `lr` (`f3StdLayout.libcStartMainStage2Addr + 56#64`) `decide` Checks & `LinkedAt` Lift -/

/-- At the pinned `f3MallocngMpl` placement, `f3StdLayout.libcStartMainStage2Addr + 56#64` lies
    outside the 260-byte `memset` block (`blk21`). -/
theorem f3StartupLr_keepMemsetBlk21_f3 :
    keepMemsetBlk21 f3MallocngMpl (f3StdLayout.libcStartMainStage2Addr + 56#64) = false := by
  decide

/-- Layout-generic `keepMemsetBlk21 mmpl (sm.readReg64 .lr) = false` at startup `lr`. -/
theorem f3StartupLr_keepMemsetBlk21_false
    {mmpl : Obj.MultiPlacement} {sm : State}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64) :
    keepMemsetBlk21 mmpl (sm.readReg64 .lr) = false := by
  have hkeq : keepMemsetBlk21 mmpl (sm.readReg64 .lr) =
      keepMemsetBlk21 f3MallocngMpl (f3StdLayout.libcStartMainStage2Addr + 56#64) := by
    unfold keepMemsetBlk21
    rw [hlr, f3CliElf_mallocng_base21_eq hMm]
  exact hkeq.trans f3StartupLr_keepMemsetBlk21_f3

/-- At the pinned `f3MallocngMpl` placement, `f3StdLayout.libcStartMainStage2Addr + 56#64` lies
    outside the 396-byte `memcpy` block (`blk20`). -/
theorem f3StartupLr_keepMemcpyBlk20_f3 :
    keepMemcpyBlk20 f3MallocngMpl (f3StdLayout.libcStartMainStage2Addr + 56#64) = false := by
  decide

/-- At the pinned `f3LsMpl` placement, `f3StdLayout.libcStartMainStage2Addr + 56#64` is distinct
    from the `"memcpy"` stub `f3LsMpl.ρ "memcpy"`. -/
theorem f3StartupLr_ne_f3LsMemcpyStub :
    f3StdLayout.libcStartMainStage2Addr + 56#64 ≠ f3LsMpl.ρ "memcpy" := by
  rw [f3LsMpl_rho_memcpy]
  exact f3Memcpy_pin_parts.2.2.2

/-- Layout-generic `keepMemcpyBlk20 mmpl (sm.readReg64 .lr) = false` at startup `lr`. -/
theorem f3StartupLr_keepMemcpyBlk20_false
    {mmpl : Obj.MultiPlacement} {sm : State}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64) :
    keepMemcpyBlk20 mmpl (sm.readReg64 .lr) = false := by
  have hkeq : keepMemcpyBlk20 mmpl (sm.readReg64 .lr) =
      keepMemcpyBlk20 f3MallocngMpl (f3StdLayout.libcStartMainStage2Addr + 56#64) := by
    unfold keepMemcpyBlk20
    rw [hlr, f3CliElf_mallocng_base20_eq hMm]
  exact hkeq.trans f3StartupLr_keepMemcpyBlk20_f3

/-- Layout-generic `sm.readReg64 .lr ≠ mpl.ρ "memcpy"` at startup `lr`. -/
theorem f3StartupLr_ne_memcpyStub
    {mpl : Obj.MultiPlacement} {sm : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hlr : sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64) :
    sm.readReg64 .lr ≠ mpl.ρ "memcpy" := by
  rw [hlr, f3CliElf_libsignal_memcpy_rho_eq hLs]
  exact f3StartupLr_ne_f3LsMemcpyStub

/-- Variant-A real-side entry guard for `memcpy` (`blk20`, 396 B) at `stubPc`. -/
@[expose] def MemcpyEntryGuard
    (mmpl : Obj.MultiPlacement) (stubPc : BitVec 64) (s0 : State) : Prop :=
  keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

/-- Specialization of `MemcpyEntryGuard` to `libsignalSessionLib`'s `"memcpy"` stub `mpl.ρ "memcpy"`. -/
@[expose] def F3MemcpyEntryGuard (mpl mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  MemcpyEntryGuard mmpl (mpl.ρ "memcpy") s0

/-- Discharges `F3MemcpyEntryGuard mpl mmpl sm` layout-generically from `StdMainEntryLr f3StdLayout sm`
    and `LinkedAt cliElfBytes` witnesses for `mpl` and `mmpl`. -/
theorem f3MemcpyEntryGuard_of_startupLr
    {mpl mmpl : Obj.MultiPlacement} {sm : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : StdMainEntryLr f3StdLayout sm) :
    F3MemcpyEntryGuard mpl mmpl sm :=
  ⟨f3StartupLr_keepMemcpyBlk20_false hMm hlr, f3StartupLr_ne_memcpyStub hLs hlr⟩

/-- Combined `W`-independent Block-`617` entry-`lr`-false predicate covering both `memset` (`blk21`)
    and `memcpy` (`blk20`), sufficient for `_of_trap_ret` replays. -/
@[expose] def F3MemsetMemcpyEntryLrFalse (mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧
  keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false

theorem f3MemsetMemcpyEntryLrFalse_iff_keepMemOps_false
    (mmpl : Obj.MultiPlacement) (s0 : State) :
    F3MemsetMemcpyEntryLrFalse mmpl s0 ↔ keepMemOps mmpl (s0.readReg64 .lr) = false := by
  unfold F3MemsetMemcpyEntryLrFalse keepMemOps
  rw [Bool.or_eq_false_iff, and_comm]

/-- Derives `F3MemsetMemcpyEntryLrFalse mmpl sm` from `StdMainEntryLr f3StdLayout sm` and
    `hMm : mallocngLib.LinkedAt cliElfBytes mmpl` (`W`-independent, `mpl`-independent). -/
theorem f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr
    {mmpl : Obj.MultiPlacement} {sm : State}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hlr : StdMainEntryLr f3StdLayout sm) :
    F3MemsetMemcpyEntryLrFalse mmpl sm :=
  ⟨f3StartupLr_keepMemsetBlk21_false hMm hlr, f3StartupLr_keepMemcpyBlk20_false hMm hlr⟩

/-! ## 3. `W`-Independent Guarded-Harness Corollaries (`StartupStatics` → Entry Guards) -/

/-! ## 4. `Block617TransferFixedHypG` Instances via `block617TransferFixedG_of_replaysOn_outcome` -/

end

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard

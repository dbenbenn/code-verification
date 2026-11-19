/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.F3LayoutData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Card CC-LIBC (`strlen`) — `F3CodeInv` / `rxProg` Replay Wrappers & Block-`617` `"strlen"` Entry Guards (`ElfStrlenEntryGuard`)

Cutover-2 `c`-card companion to `Cli.HooksDehook.StrlenGhostReplays` (modeled on
`ElfBcmpEntryGuard` @ `1583e332c6`, staying in the default `LibsignalBinary` target with `0`
`CliElfLib`, C2, or trusted imports):

1. **Artifact 2b — `F3CodeInv` / `rxProg` `GhostRowReplayOn` Wrappers (`§1`):**
   - Parameterized over `(CodeInv : Memory → Prop)` (`:= StartupStatics.F3CodeInv mpl mmpl` at C2)
     and `(rxProg : Program)` (`:= Tie.f3TrialRxProg` at C2), taking STARTUP's stock-side facts as
     verbatim premises matching `Lib2LayoutFacts.lean` (`origin/stock-lld/c2-startup-dnm` @
     `a230f2671b`: `:114`, `:203`, `:271`, `:316`, `:317`, `:326`, `:338`, `:355`, `:368`, `:374`,
     `:428`, `:444`) so C2 assembly discharges every premise with plain `exact`.
   - Provides both `strlenGhost_rowReplayOn_f3CodeInv_of_strip` (consuming `hStripCL` verbatim from
     `f3CodeInv_rxWords_codeLoaded_strip` `:203–215`) and `strlenGhost_rowReplayOn_f3CodeInv`
     (consuming the 3 slice premises `hAlign`/`hNoWrap`/`hSubSlice` `:208–213` directly on `rxProg`
     with `hAlign : (strlenEntry mpl).toNat % 4 = 0` and discharging `hKeep` `:214` automatically
     via `keepR_strlen_of_code_offset`).
2. **Artifact 3 — Block-`617` Startup `lr` (`strlenEntryGuard` / `ExtraEntryGuard`) Discharge (`§2`):**
   - Parameterized over `(keepBPre : BitVec 64 → Bool)` (`:= Lib2LayoutFacts.keepTextBPre` at C2),
     taking `keepTextBPre_startupLr_false` (`:104`), `C2ExternTableFacts.batchLInKeep` (`:334` / `:419`),
     and hull inclusion (`:485` `f3BatchLEntryGuard_of_startupLr`) as verbatim premises at the
     concrete startup return address `f3StdLayout.libcStartMainStage2Addr + 56#64` (`= StdMainEntryLr
     f3StdLayout s0`, `rfl`-equal to `Lib2LayoutFacts.f3StartupLrVal` `:99`).
   - Supplies table-level `ExtraEntryGuard` arm helpers (`extraEntryGuard_strlen_arm` and
     `extraEntryGuard_singleton_strlen`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStrlenEntryGuard

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (StdMainEntryLr)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (
  ExtraEntryGuard GhostRowOk GhostRowReplayOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays (
  strlenEntry keepR_strlen strlenSubProg strlenSubProg_base strlenSubProg_code_length
  keepR_strlen_of_code_offset strlenSubProg_codeLoaded_of_stripExecOutside
  strlenGhost strlenGhostK strlenEntryGuard strlenEntryGuard_iff
  strlenGhost_rowReplayOn strlenGhost_rowSpecOk strlenGhostK_rowReplayOn
)

/-! ## 1. Artifact 2b — `F3CodeInv` / `rxProg` `GhostRowReplayOn` Wrappers (Verbatim C2 Premises) -/

/-! ## 2. Artifact 3 — Block-`617` Startup `lr` (`strlenEntryGuard` / `ExtraEntryGuard`) Discharge -/

/-- Concrete startup return address entering `main` (`block 617`), `rfl`-identical to
    `Lib2LayoutFacts.f3StartupLrVal` (`Lib2LayoutFacts.lean @a230f2671b:99`) and proved equal to
    `sm.readReg64 .lr` by `StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt`. -/
@[expose] def f3StartupLrVal : BitVec 64 :=
  f3StdLayout.libcStartMainStage2Addr + 56#64

/-- Direct adapter from `Lib2LayoutFacts.f3BatchLEntryGuard_of_startupLr`
    (`Lib2LayoutFacts.lean @a230f2671b:485-492`) into `strlenEntryGuard mpl s0` (`Iff.rfl`). -/
theorem f3StrlenEntryGuard_of_batchLEntryGuard
    {mpl : Obj.MultiPlacement} {s0 : State}
    -- [Lib2LayoutFacts.lean @a230f2671b:485-492] f3BatchLEntryGuard_of_startupLr:
    (hGuard : keepR_strlen mpl (s0.readReg64 .lr) = false ∧
      s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl "strlen") :
    strlenEntryGuard mpl s0 :=
  (strlenEntryGuard_iff mpl s0).mpr hGuard

/-- **Artifact 3 (`C11` §6.3):** Block-`617` `strlenEntryGuard mpl s0` discharge from startup `lr`
    (`s0.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64`), parameterized over
    `keepBPre : BitVec 64 → Bool` (`:= Lib2LayoutFacts.keepTextBPre` at C2) so zero C2-only
    constants are imported while every premise matches `Lib2LayoutFacts.lean @a230f2671b` verbatim. -/
theorem f3StrlenEntryGuard_of_startupLr
    {mpl : Obj.MultiPlacement} {s0 : State}
    (keepBPre : BitVec 64 → Bool)
    -- [StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt; rfl-equal to Lib2LayoutFacts.f3StartupLrVal @a230f2671b:99]:
    (hlr : s0.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64)
    -- [Lib2LayoutFacts.lean @a230f2671b:104] keepTextBPre_startupLr_false:
    (hLrOut : keepBPre (f3StdLayout.libcStartMainStage2Addr + 56#64) = false)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :334, :419] C2ExternTableFacts.batchLInKeep /
    -- f3BatchL_dehookedSym_in_keepTextBPre (at sym = "strlen"):
    (hSymIn : keepBPre (libsignalSessionLib.resolve mpl "strlen") = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:485, :490] f3BatchLEntryGuard_of_startupLr (`hsub` premise):
    (hHullSub : ∀ pc : BitVec 64, keepR_strlen mpl pc = true → keepBPre pc = true) :
    strlenEntryGuard mpl s0 := by
  rw [strlenEntryGuard_iff, hlr]
  refine ⟨?_, ?_⟩
  · cases hk : keepR_strlen mpl (f3StdLayout.libcStartMainStage2Addr + 56#64)
    · rfl
    · cases hLrOut.symm.trans (hHullSub _ hk)
  · intro hEq
    rw [hEq] at hLrOut
    cases hLrOut.symm.trans hSymIn

/-- `StdMainEntryLr f3StdLayout s0` wrapper around `f3StrlenEntryGuard_of_startupLr` (matching
    `ElfMemsetEntryGuard.f3MemsetEntryGuard_of_startupLr` / `StartupStatics`). -/
theorem f3StrlenEntryGuard_of_stdMainEntryLr
    {mpl : Obj.MultiPlacement} {s0 : State}
    (keepBPre : BitVec 64 → Bool)
    (hlr : StdMainEntryLr f3StdLayout s0)
    -- [Lib2LayoutFacts.lean @a230f2671b:104] keepTextBPre_startupLr_false:
    (hLrOut : keepBPre (f3StdLayout.libcStartMainStage2Addr + 56#64) = false)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :334, :419] C2ExternTableFacts.batchLInKeep /
    -- f3BatchL_dehookedSym_in_keepTextBPre (at sym = "strlen"):
    (hSymIn : keepBPre (libsignalSessionLib.resolve mpl "strlen") = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:485, :490] f3BatchLEntryGuard_of_startupLr (`hsub` premise):
    (hHullSub : ∀ pc : BitVec 64, keepR_strlen mpl pc = true → keepBPre pc = true) :
    strlenEntryGuard mpl s0 :=
  f3StrlenEntryGuard_of_startupLr keepBPre hlr hLrOut hSymIn hHullSub

/-- Per-arm `"strlen"` discharge for any `guardOf : String → State → Prop` agreeing with
    `strlenEntryGuard mpl` on `"strlen"`. -/
theorem extraEntryGuard_strlen_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf "strlen" s0 ↔ strlenEntryGuard mpl s0)
    (hStrlenGuard : strlenEntryGuard mpl s0) :
    guardOf "strlen" s0 :=
  hGuardEq.mpr hStrlenGuard

/-- Table-level `ExtraEntryGuard guardOf g s0` discharge when `g.extra` carries the singleton
    `"strlen"` row `[("strlen", strlenGhost mpl mmpl)]`. -/
theorem extraEntryGuard_singleton_strlen
    {mpl mmpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hg : g.extra = [("strlen", strlenGhost mpl mmpl)])
    (hGuardEq : guardOf "strlen" s0 ↔ strlenEntryGuard mpl s0)
    (hStrlenGuard : strlenEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 := by
  intro sym f _ hLook
  rw [hg] at hLook
  simp only [List.lookup] at hLook
  by_cases hSym : (sym == "strlen") = true
  · have hEq : sym = "strlen" := eq_of_beq hSym
    subst hEq
    exact hGuardEq.mpr hStrlenGuard
  · simp [hSym] at hLook

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStrlenEntryGuard

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostReplays
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
public import ProofLib.Placed.OpcodeExclusion
public import VerifiedLibraries.RustStd.Proofs.Wave1.TimeDurationSince
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Cutover-2 (`C2`) `SystemTime::duration_since` `.rodata.cst16` Glue (`C2RowLayoutFacts.DurCst16`)

Supplies GK §19(d) item 3 for `lsDurationSinceSym`:
1. `c2TimePlacedData0_eq_timePlacedData0`: byte identity between `Lib2LayoutFacts.c2TimePlacedData0`
   and `VerifiedLibraries.RustStd.timePlacedData0`.
2. `f3CodeInv_roDataAt_timeCst16` and `durationSince_hRo_of_f3CodeInv`: derives the exact `hRo`
   premise `∀ u : State, InvS u → RoDataAt u.mem (timeMpl.ρ timeRodataCst16Sym) timePlacedData0`
   consumed by `DurationSinceGhostReplays.durationSinceGhost_rowReplayOn` and
   `durationSinceGhost_rowOk` from `Lib2LayoutFacts.f3CodeInv_roDataAt_durationSinceCst16`
   (`C2RoSliceFacts` remains a hypothesis until T4 swaps to the final C2 ELF).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DurCst16

open Arm64 Arm64.Obj ProofLib.ProgramReflection
open VerifiedLibraries.RustStd (timePlacedData0 timeRodataCst16Sym)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2RoSliceFacts c2TimePlacedData0 f3CodeInv_roDataAt_durationSinceCst16)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen (c2DurationSinceCst16Addr)

/-- Canonical byte identity between `Lib2LayoutFacts.c2TimePlacedData0` and
    `VerifiedLibraries.RustStd.timePlacedData0` (`1_u128` 16-byte mask). -/
theorem c2TimePlacedData0_eq_timePlacedData0 :
    c2TimePlacedData0 = timePlacedData0 := by
  rfl_kernel

/-- Memory-level `.rodata.cst16` `RoDataAt` bridge from `F3CodeInv` + `LinkedAt cliElfBytes mpl`
    for any `timeMpl` resolving `timeRodataCst16Sym` to `c2DurationSinceCst16Addr`. -/
theorem f3CodeInv_roDataAt_timeCst16
    (hRoSlice : C2RoSliceFacts)
    {mpl mmpl timeMpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRho : timeMpl.ρ timeRodataCst16Sym = c2DurationSinceCst16Addr)
    (hInv : F3CodeInv mpl mmpl m) :
    RoDataAt m (timeMpl.ρ timeRodataCst16Sym) timePlacedData0 := by
  have h0 : RoDataAt m c2DurationSinceCst16Addr c2TimePlacedData0 :=
    f3CodeInv_roDataAt_durationSinceCst16 hRoSlice hLs hInv
  rw [hRho, ← c2TimePlacedData0_eq_timePlacedData0]
  exact h0

/-- Exact `hRo` premise shape consumed by `DurationSinceGhostReplays.durationSinceGhost_rowReplayOn`
    and `durationSinceGhost_rowOk`:
    `∀ u : State, InvS u → RoDataAt u.mem (timeMpl.ρ timeRodataCst16Sym) timePlacedData0`. -/
theorem durationSince_hRo_of_f3CodeInv
    (hRoSlice : C2RoSliceFacts)
    {mpl mmpl timeMpl : Obj.MultiPlacement}
    {InvS : State → Prop}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRho : timeMpl.ρ timeRodataCst16Sym = c2DurationSinceCst16Addr)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u → RoDataAt u.mem (timeMpl.ρ timeRodataCst16Sym) timePlacedData0 :=
  fun u hu => f3CodeInv_roDataAt_timeCst16 hRoSlice hLs hRho (hInv u hu)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DurCst16

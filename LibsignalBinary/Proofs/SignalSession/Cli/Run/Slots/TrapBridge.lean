/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
import ProofLib.SepLogic.WP.StateNorm

/-!
# Trap-at-RNG and Unlisted-Stub Program Bridges (`trTrapProgAt` and `trapUnlisted`)

Bridges subroutine proofs from `trTrapProgAt b W.C (cliExterns W)` (where `libsignal_session_rng_fill`
traps via `rngTrap`) to the CLI program `tripleRatchetProgAtExt b (cliExterns W)` via `TrapsOnly`
(`trapsOnly_trTrap_cli`, `subroutine_ok_cli_of_trTrap`). Neither `TrapsOnly kit cli` nor
`TrapsOnly cli kit` holds directly because the kit installs a returning `rngFillHook` at
`rngFillName` (`0x97388`) whereas `cliHookTable` leaves `rngFillName` unhooked.

Also defines `trapUnlisted ext`, replacing every non-panic symbol outside `cliHookNames` with
`rngTrap` while preserving `CliExternsOk P A`.
-/

public section

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib ProofLib.Variant CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet

/-- Away from `rngFillName`, `Rust.withPanics (tripleRatchetExterns W.C ctl (cliExterns W))` agrees
pointwise with `Rust.withPanics (cliExterns W)`. -/
theorem cliExterns_agree (W : CliHooks) (ctl : BitVec 64) {n : String} (hn : n ≠ rngFillName) :
    Rust.withPanics (tripleRatchetExterns W.C ctl (cliExterns W)) n =
      Rust.withPanics (cliExterns W) n := by
  rw [withPanics_cliExterns]
  by_cases hp : Rust.isPanicSymbol n = true
  · have hpC : isCliPanicSymbol n = true := isCliPanicSymbol_of_isPanicSymbol hp
    unfold cliExterns withCliPanics
    simp [Rust.withPanics, hp, hpC]
  · simp only [Rust.withPanics, hp, Bool.false_eq_true, ↓reduceIte]
    by_cases hk : n ∈ kitOwnNames
    · simp only [kitOwnNames, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
      simp [tripleRatchetExterns, CryptoVerification.LibsignalSession.sessionExterns,
        dhName, pubFromSecretName, staticDropName, sharedDropName, rngFillName, noHookNames] <;>
      first
        | (unfold cliExterns withCliPanics
           simp [isCliPanicSymbol, E2E.isImagePanicSymbol, E2E.extraImagePanicNames,
             deadCliHashbrownPanicNames]; done)
        | (refine (cliExterns_row W ?_).symm
           simp [cliHookTable])
        | (refine (cliExterns_none_of_not_imagePanic W ?_ ?_).symm
           · decide +kernel
           · simp [E2E.isImagePanicSymbol, Rust.isPanicSymbol, E2E.extraImagePanicNames])
    · exact tripleRatchetExterns_of_not_mem W.C ctl (cliExterns W) hk hn

set_option autoImplicit false

theorem cliHookNames_notPanic_std3 :
    cliHookNames.all (fun n => !E2E.isImagePanicSymbol n) = true := by
  rw [List.all_eq_true]
  intro n hn
  simp only [cliHookNames,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.compress512Name,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.toEdwardsName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.compressName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.edNegName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.torsionFreeName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.dsmbName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.scalarModName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.scalarWideName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.kemEncapsName,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.kemDecapsName,
    LibsignalSpqrV1.mlkemFromSeedName, LibsignalSpqrV1.mlkemPk1Name,
    LibsignalSpqrV1.mlkemPk2Name, LibsignalSpqrV1.mlkemEncaps1Name,
    LibsignalSpqrV1.mlkemEncaps2Name, LibsignalSpqrV1.mlkemDecapsName,
    LibsignalSpqrV1.mlkemValidatePkName, LibsignalSpqrV1.libcruxHmacName,
    SignalSession.readFileName, SignalSession.writeFileName,
    SignalSession.readStdinName, SignalSession.writeStdoutName,
    List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [E2E.isImagePanicSymbol, Rust.isPanicSymbol, E2E.extraImagePanicNames]

theorem isPanicSymbolE_false_of_mem_cliHookNames {n : String} (hn : n ∈ cliHookNames) :
    E2E.isImagePanicSymbol n = false := by
  have h := List.all_eq_true.mp cliHookNames_notPanic_std3 n hn
  simpa using h

theorem isCliPanicSymbol_false_of_mem_cliHookNames {n : String} (hn : n ∈ cliHookNames) :
    isCliPanicSymbol n = false :=
  isCliPanicSymbol_eq_false_of_isImagePanicSymbol_false (isPanicSymbolE_false_of_mem_cliHookNames hn)

end CryptoVerification.SignalSession.Cli.Slots

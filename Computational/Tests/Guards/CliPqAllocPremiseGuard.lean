/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers

/-!
# CLI PQXDH Allocation and Excused-Abort Premise Guards

**Checked by Lean.** Compile-time guards in `ComputationalTests` (`Computational/Tests.lean`, built
by default `lake build`) verifying:
* `svc` / `overrides` agreement on `Placed.cliProgPlacedSig mpl` (`Syscall.standard`,
  `overrides = fun _ => none`), giving `MallocngSvcValid (Placed.cliProgPlacedSig mpl).svc`.
* Empty `cliHookTablePlaced` (`0` rows; `cliHookTablePlaced_keys_guard` fails closed if any row is
  re-added) and absence of all `55` directly linked symbol names in `cliDehookedSymsPlaced` from
  both `isCliPanicSymbolPlaced` and `cliHookTablePlaced` (`cliExternsPlacedSig sym = none`).
* `cliRunPlacedSig_eq_none_of_reachesOOM_guard`: reaching `.OutOfMemory` (`CliReachesOOMPlaced`)
  forces `Placed.cliRunPlacedSig mpl elf i = none`.
* `outcomeOrExcusedAbort_ok_branch_nonvacuous_guard`,
  `outcomeOrExcusedAbort_oom_branch_nonvacuous_guard`,
  `outcomeOrExcusedAbort_placed_oom_disjunct_guard`, and
  `not_outcomeOrExcusedAbort_placed_of_unexcused_none_guard`: both disjuncts of
  `OutcomeOrExcusedAbort` are non-vacuous, and an unexcused `none` (`¬ CliReachesOOMPlaced`) fails
  closed.
* `cliSpecPqxdhOrExcusedAbort_false_iff_guard` and
  `cliSpecPqxdhNoMatchOrExcusedAbort_false_iff_guard`: at `exc := fun _ => False`, the excused
  predicates recover `CliSpecPqxdh` and `CliSpecPqxdhNoMatch`.
* `cliSpecPqxdh_and_noMatch_of_elfCorrectPlaced_and_noOOM_guard`: combining
  `CliPqxdhElfCorrectPlaced` with `hNoOOM` and `hNoStuck` recovers total `CliSpecPqxdh` and
  `CliSpecPqxdhNoMatch`; for `cliElfBytes`, `hNoOOM` is proved by
  `ElfNoOomPlacedInstK.cliElf_noOOM_of_parseK` (discharged via
  `ElfSlicesPqOomH2KM1.h2k_ghostArms_closed`).
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Tests.Guards.CliPqAllocPremiseGuard

open Arm64 Arm64.Process ProofLib
open CryptoVerification
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession

theorem cliProgPlacedSig_svc_eq_standard_guard
    (mpl : Obj.MultiPlacement) :
    (Placed.cliProgPlacedSig mpl).svc = Syscall.standard :=
  rfl

theorem cliProgPlacedSig_overrides_eq_none_guard
    (mpl : Obj.MultiPlacement) :
    (Placed.cliProgPlacedSig mpl).overrides = (fun _ => none) :=
  rfl

theorem cliProgPlacedSig_mallocngSvcValid_guard
    (mpl : Obj.MultiPlacement) :
    VerifiedLibraries.Mallocng.MallocngSvcValid (Placed.cliProgPlacedSig mpl).svc :=
  VerifiedLibraries.Mallocng.Proofs.mallocngSvcValid_standard

/-- Expected (empty) key list of `cliHookTablePlaced`. -/
def cliHookTableKeysExpected : List String := []

/-- Guard: `cliHookTablePlaced` has the exact expected (empty) symbol key list. -/
theorem cliHookTablePlaced_keys_guard :
    cliHookTablePlaced.map Prod.fst = cliHookTableKeysExpected :=
  rfl

/-- Guard: `cliHookTablePlaced` has `0` rows. -/
theorem cliHookTablePlaced_length_guard :
    cliHookTablePlaced.length = 0 :=
  rfl

/-- Guard: none of the `55` directly linked symbol names in `cliDehookedSymsPlaced` is a panic symbol (`isCliPanicSymbolPlaced`). -/
theorem cliDehookedSymsPlaced_not_panic_guard :
    (cliDehookedSymsPlaced.all fun s => !isCliPanicSymbolPlaced s) = true := by
  simp [cliDehookedSymsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
    Rust.isPanicSymbol, lsRustNoAllocShimSymCli, lsRustAllocSymCli, lsRustDeallocSymCli,
    lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsReadFileSym, lsReadStdinSym,
    lsWriteFileSym, lsWriteStdoutSym, lsFmtWriteSym, lsFormatInnerSym,
    lsMemrchrSym, lsFromUtf8Sym, lsDurationSinceSym, lsTimeAddSym,
    lsBlackBoxSym, lsStaticSecretDropSym, lsSharedSecretDropSym,
    lsCompress256Sym, lsLibcruxHmacSym, lsAesEncSym, lsAesDecSym, lsGetauxvalHwcapSym,
    lsPubFromSecretSym, lsDiffieHellmanSym]

private theorem not_panic_of_all {s : String} {l : List String}
    (hall : (l.all fun x => !isCliPanicSymbolPlaced x) = true) (hmem : s ∈ l) :
    isCliPanicSymbolPlaced s = false := by
  simpa using List.all_eq_true.mp hall s hmem

theorem cliExternsPlacedSig_dehooked_eq_none_guard
    {sym : String} (hsym : sym ∈ cliDehookedSymsPlaced) :
    cliExternsPlacedSig sym = none := by
  have hp : isCliPanicSymbolPlaced sym = false :=
    not_panic_of_all cliDehookedSymsPlaced_not_panic_guard hsym
  unfold cliExternsPlacedSig
  simp only [hp, Bool.false_eq_true, ↓reduceIte]

theorem cliRunPlacedSig_eq_none_of_reachesOOM_guard
    {mpl : Obj.MultiPlacement} {elf : ElfImage} {i : Inputs}
    (hOOM : CliReachesOOMPlaced mpl elf i) :
    Placed.cliRunPlacedSig mpl elf i = none :=
  cliRunPlacedSig_eq_none_of_reachesOOM hOOM

theorem outcomeOrExcusedAbort_ok_branch_nonvacuous_guard (i : Inputs) (o : Outcome) :
    let exc : Inputs → Prop := fun _ => False
    let run : CliRun := fun _ => some o
    OutcomeOrExcusedAbort exc run i (· = o) ∧ ¬ exc i :=
  ⟨.inl ⟨o, rfl, rfl⟩, not_false⟩

theorem outcomeOrExcusedAbort_oom_branch_nonvacuous_guard (i : Inputs) :
    let exc : Inputs → Prop := fun j => j = i
    let run : CliRun := fun _ => none
    OutcomeOrExcusedAbort exc run i (fun _ => False) ∧ exc i ∧ (∀ o, run i ≠ some o) :=
  ⟨.inr ⟨rfl, rfl⟩, rfl, fun _ h => nomatch h⟩

theorem outcomeOrExcusedAbort_placed_oom_disjunct_guard
    {mpl : Obj.MultiPlacement} {elf : ElfImage} {i : Inputs}
    {P : Outcome → Prop} (hOOM : CliReachesOOMPlaced mpl elf i) :
    OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl elf)
      (Placed.cliRunPlacedSig mpl elf) i P :=
  .inr ⟨cliRunPlacedSig_eq_none_of_reachesOOM hOOM, hOOM⟩

/-- An unexcused `none` result (`¬ CliReachesOOMPlaced`) refutes `OutcomeOrExcusedAbort`. -/
theorem not_outcomeOrExcusedAbort_placed_of_unexcused_none_guard
    {mpl : Obj.MultiPlacement} {elf : ElfImage} {i : Inputs}
    {P : Outcome → Prop}
    (hNone : Placed.cliRunPlacedSig mpl elf i = none)
    (hNoOOM : ¬ CliReachesOOMPlaced mpl elf i) :
    ¬ OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl elf)
        (Placed.cliRunPlacedSig mpl elf) i P := by
  rintro (⟨_, hr, _⟩ | ⟨_, hOOM⟩)
  · cases hNone.symm.trans hr
  · exact hNoOOM hOOM

theorem cliSpecPqxdhOrExcusedAbort_false_iff_guard
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    CliSpecPqxdhOrExcusedAbort (fun _ => False) run X W ↔ CliSpecPqxdh run X W :=
  cliSpecPqxdhOrExcusedAbort_false_iff run X W

theorem cliSpecPqxdhNoMatchOrExcusedAbort_false_iff_guard
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    CliSpecPqxdhNoMatchOrExcusedAbort (fun _ => False) run X W ↔ CliSpecPqxdhNoMatch run X W :=
  cliSpecPqxdhNoMatchOrExcusedAbort_false_iff run X W

theorem cliSpecPqxdh_and_noMatch_of_elfCorrectPlaced_and_noOOM_guard
    {mpl : Obj.MultiPlacement} {elf : ElfImage} {X : UnreachedPqxdhPrimitives}
    (hL4 : CliPqxdhElfCorrectPlaced mpl elf)
    (hNoOOM : ∀ i : Inputs, CliPqxdhInputs realPEParams i → ¬ CliReachesOOMPlaced mpl elf i)
    (hNoStuck : ∀ i : Inputs, CliPqxdhInputs realPEParams i →
      ¬ CliReachesSampleNttStuckPlaced mpl elf i) :
    CliSpecPqxdh (Placed.cliRunPlacedSig mpl elf) X realPEParams ∧
      CliSpecPqxdhNoMatch (Placed.cliRunPlacedSig mpl elf) X realPEParams :=
  ⟨cliSpecPqxdh_of_elfCorrectPlaced_and_noOOM hL4 hNoOOM hNoStuck,
    cliSpecPqxdhNoMatch_of_elfCorrectPlaced_and_noOOM hL4 hNoOOM hNoStuck⟩

end Computational.Tests.Guards.CliPqAllocPremiseGuard

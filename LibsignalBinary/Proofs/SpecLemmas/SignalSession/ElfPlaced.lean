/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMallocngPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataGen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
import LibsignalBinary.Proofs.Placed.PlacedCallSym

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Two-Placement Witnesses and Uniqueness for `cliElfBytes`

**Checked by Lean.** Assembles and re-exports the two-placement `libsignalSessionLib` and
`VerifiedLibraries.mallocngLib` witnesses on `cliElfBytes` (`LinkedAt`, `LinkedIn`,
relocation-inversion uniqueness, `CliElfCodeMatchesPlaced`, and distinctness of dispatched extern
targets `cliElf_externs_distinct_of_linkedAt`).
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced

open Arm64
open Arm64.Obj (MultiPlacedLib MultiPlacement)
open ProofLib.ProgramReflection
open CryptoVerification (ExternsDistinctOnHooked libsignalHookedExterns libsignalSessionExterns)
open CryptoVerification.SignalSession (
  cliElfBytes cliElfImage cliElf_parse CliHooks Inputs Outcome OutcomeMatchesProcess
  cliProcessInputs libsignalSessionLib cliCratePanicSyms cliDehookedSymsPlaced
  cliNonPanicDehookedSyms cliPanicSymbolsPlaced isCliPanicSymbolPlaced cliExternsPlaced
)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced (CliReachesOOMPlaced)
open CryptoVerification.SignalSession.Placed (cliTokenPatchPlaced)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed
  (CliElfCodeMatchesPlaced CliRunsToPlaced cliRunPlacedSig)
open LibsignalBinary.Heap.Fine (f3MallocngMpl)

/-! ## Re-exported Interned Layout and Reflection Witnesses -/

noncomputable abbrev lsInternedMultiLib : Obj.Interned.MultiLib :=
  ElfCodeMatchesData.lsInternedMultiLib

noncomputable abbrev lsNameChars : List (List Char) :=
  ElfCodeMatchesData.lsNameChars

noncomputable abbrev lsNames : List String :=
  ElfCodeMatchesData.lsNames

noncomputable abbrev lsSharedExterns : List Nat :=
  ElfCodeMatchesData.lsSharedExterns

noncomputable abbrev cliElfBlockBases : List (BitVec 64) :=
  ElfCodeMatchesData.f3LsBlockBases

noncomputable abbrev cliElfSymAddrs : List (BitVec 64) :=
  ElfCodeMatchesData.f3LsSymAddrs

noncomputable abbrev cliElfMultiLayout : Obj.Interned.MultiLayout :=
  ElfCodeMatchesData.f3LsLayout

noncomputable abbrev cliElfMultiPlacement : MultiPlacement :=
  ElfCodeMatchesData.f3LsMpl

noncomputable abbrev cliElfSymChars : List (List Char × BitVec 64) :=
  ElfSymChars.cliElfSymChars

theorem cliElf_symbols_eq :
    cliElfImage.symbols = ProofLib.ProgramReflection.toStringAssoc cliElfSymChars :=
  ElfSymChars.cliElf_symbols_eq

theorem ls_names_eq : lsInternedMultiLib.names = lsNameChars.map String.ofList :=
  ElfCodeMatchesData.ls_names_eq

theorem ls_names_nodup : lsInternedMultiLib.names.Nodup :=
  ElfCodeMatchesData.ls_names_nodup

theorem ls_toMultiPlacedLib_eq : libsignalSessionLib = lsInternedMultiLib.toMultiPlacedLib :=
  ElfCodeMatchesData.ls_toMultiPlacedLib_eq

/-! ## `libsignalSessionLib` Placement, `LinkedAt`, and Uniqueness -/

/-- `Placeable ∧ InElf cliElfImage ∧ DataDisjoint` for `libsignalSessionLib` at
`cliElfMultiPlacement`. -/
theorem cliElf_libsignal_placed :
    libsignalSessionLib.Placeable cliElfMultiPlacement ∧
    libsignalSessionLib.InElf cliElfImage cliElfMultiPlacement ∧
    libsignalSessionLib.DataDisjoint cliElfMultiPlacement :=
  ElfCodeMatchesPlaced.f3CliElf_libsignal_placed

theorem cliElf_linkedAt :
    libsignalSessionLib.LinkedAt cliElfBytes cliElfMultiPlacement :=
  ⟨cliElfImage, cliElf_parse, cliElf_libsignal_placed.1, cliElf_libsignal_placed.2.1⟩

theorem cliElf_linkedIn :
    libsignalSessionLib.LinkedIn cliElfBytes :=
  ⟨cliElfMultiPlacement, cliElf_linkedAt⟩

/-- Relocation-inversion uniqueness and `DataDisjoint` for any `LinkedAt cliElfBytes` placement of
`libsignalSessionLib`. -/
theorem cliElf_linkedAt_unique {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    (∀ i < libsignalSessionLib.blocks.length, mpl.base i = cliElfMultiPlacement.base i) ∧
    (∀ s ∈ lsInternedMultiLib.names,
      libsignalSessionLib.resolve mpl s = libsignalSessionLib.resolve cliElfMultiPlacement s) ∧
    (∀ s ∈ lsInternedMultiLib.names,
      Obj.lookupBlockSym s libsignalSessionLib.blocks = none →
        mpl.ρ s = cliElfMultiPlacement.ρ s) ∧
    libsignalSessionLib.DataDisjoint mpl :=
  ElfCodeMatchesPlaced.f3CliElf_libsignal_linkedAt_unique hlink

/-! ## `VerifiedLibraries.mallocngLib` Placement and Uniqueness -/

theorem cliElf_mallocng_linkedAt :
    VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes ElfMallocngPlaced.cliElfMallocngPlacement :=
  ElfMallocngPlaced.cliElf_mallocng_linkedAt

theorem cliElf_mallocng_linkedIn :
    VerifiedLibraries.mallocngLib.LinkedIn cliElfBytes :=
  ElfMallocngPlaced.cliElf_mallocng_linkedIn

/-- Relocation-inversion uniqueness and `DataDisjoint` for any `LinkedAt cliElfBytes` placement of
`VerifiedLibraries.mallocngLib`. -/
theorem cliElf_mallocng_linkedAt_unique {mmpl : MultiPlacement}
    (hlink : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl) :
    (∀ i < VerifiedLibraries.mallocngLib.blocks.length,
      mmpl.base i = ElfMallocngPlaced.cliElfMallocngPlacement.base i) ∧
    (∀ s ∈ VerifiedLibraries.Mallocng.Proofs.mallocngMultiL.names,
      VerifiedLibraries.mallocngLib.resolve mmpl s =
        VerifiedLibraries.mallocngLib.resolve ElfMallocngPlaced.cliElfMallocngPlacement s) ∧
    (∀ s ∈ VerifiedLibraries.Mallocng.Proofs.mallocngMultiL.names,
      Obj.lookupBlockSym s VerifiedLibraries.mallocngLib.blocks = none →
        mmpl.ρ s = ElfMallocngPlaced.cliElfMallocngPlacement.ρ s) ∧
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl :=
  ElfMallocngPlaced.cliElf_mallocng_linkedAt_unique hlink

/-! ## Two-Placement `CliElfCodeMatchesPlaced` Witnesses -/

/-- Concrete two-placement `CliElfCodeMatchesPlaced` witness on `cliElfMultiPlacement` and
`cliElfMallocngPlacement`. -/
theorem cliElf_codeMatchesPlaced :
    CliElfCodeMatchesPlaced cliElfMultiPlacement
      ElfMallocngPlaced.cliElfMallocngPlacement cliElfImage :=
  ElfCodeMatchesPlaced.f3TrialElf_codeMatchesPlaced_of_linkedAt
    cliElf_linkedAt ElfMallocngPlaced.cliElf_mallocng_linkedAt

theorem cliElf_codeMatchesPlaced_f3 :
    CliElfCodeMatchesPlaced cliElfMultiPlacement f3MallocngMpl cliElfImage :=
  ElfCodeMatchesPlaced.f3TrialElf_codeMatchesPlaced

/-- Universal `CliElfCodeMatchesPlaced mpl mmpl cliElfImage` witness for arbitrary `(mpl, mmpl)`
linked in `cliElfBytes`. -/
theorem cliElf_codeMatchesPlaced_of_linkedAt {mpl mmpl : MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl) :
    CliElfCodeMatchesPlaced mpl mmpl cliElfImage :=
  ElfCodeMatchesPlaced.f3TrialElf_codeMatchesPlaced_of_linkedAt hls hmng

/-- Universal trusted single-placement `CliElfCodeMatchesPlaced mpl cliElfImage` witness for
arbitrary `mpl` linked in `cliElfBytes`. -/
theorem cliElf_trustedCodeMatchesPlaced_of_linkedAt {mpl : MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    CryptoVerification.SignalSession.Placed.CliElfCodeMatchesPlaced mpl cliElfImage :=
  ElfCodeMatchesPlaced.f3TrialElf_trustedCodeMatchesPlaced_of_linkedAt hls

/-- `ElfImage.parse` form of `cliElf_trustedCodeMatchesPlaced_of_linkedAt`. -/
theorem cliElf_trustedCodeMatchesPlaced_of_parse {mpl : MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {elf : Arm64.Process.ElfImage} (hparse : Arm64.Process.ElfImage.parse cliElfBytes = .ok elf) :
    CryptoVerification.SignalSession.Placed.CliElfCodeMatchesPlaced mpl elf := by
  have h : cliElfImage = elf := Except.ok.inj (cliElf_parse.symm.trans hparse)
  subst h
  exact cliElf_trustedCodeMatchesPlaced_of_linkedAt hls

/-! ## Extern Address Injectivity -/

set_option maxRecDepth 4000000 in
private theorem sharedExterns_check_ok :
    libsignalSessionExterns =
        lsSharedExterns.map (fun idx => lsInternedMultiLib.names.getD idx "") ∧
      (lsSharedExterns.all fun idx =>
        Nat.blt idx lsInternedMultiLib.names.length &&
          (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none)) = true := by
  exact ⟨by rfl_kernel, by rfl_kernel⟩

private theorem toMultiPlacement_rho_eq (mly : Obj.Interned.MultiLayout) (names : List String)
    (s : String) :
    (mly.toMultiPlacement names).ρ s = mly.addrs.getD (names.idxOf s) 0#64 := by
  rfl

private theorem cliElf_rho_getD_eq {idx : Nat}
    (hlt : idx < lsInternedMultiLib.names.length) :
    cliElfMultiPlacement.ρ (lsInternedMultiLib.names.getD idx "") =
      cliElfSymAddrs.getD idx 0#64 := by
  unfold cliElfMultiPlacement ElfCodeMatchesData.f3LsMpl cliElfSymAddrs
  rw [toMultiPlacement_rho_eq, Obj.Interned.idxOf_getD ls_names_nodup hlt]
  rfl

private theorem mem_lsNames_of_lt {idx : Nat}
    (hlt : idx < lsInternedMultiLib.names.length) :
    lsInternedMultiLib.names.getD idx "" ∈ lsInternedMultiLib.names := by
  rw [Obj.Interned.getD_of_lt hlt]
  exact List.getElem_mem hlt

private theorem lookupBlockSym_none_of_lt {idx : Nat}
    (hlt : idx < lsInternedMultiLib.names.length)
    (hid : Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks = none) :
    Obj.lookupBlockSym (lsInternedMultiLib.names.getD idx "") libsignalSessionLib.blocks = none := by
  rw [ls_toMultiPlacedLib_eq,
    Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ElfCodeMatchesData.ls_idsOk hlt]
  exact hid

private def lsHookedExternPos : List Nat :=
  [1, 2, 30, 31, 37, 38, 39, 40, 41, 42, 43, 54, 56, 57, 58, 59, 60, 61,
   7, 3, 4, 5, 6, 12, 9, 90, 92, 91, 88, 93, 55, 53, 20, 65, 0, 73, 75,
   19, 27, 81, 29, 28, 13, 14, 15, 16, 34, 8, 33, 32, 35, 50, 49, 17, 45,
   46, 48, 47, 10, 11, 36, 62, 67, 21, 89]

private noncomputable def lsHookedExternIdxs : List Nat :=
  lsHookedExternPos.map (lsSharedExterns.getD · 0)

set_option maxRecDepth 4000000 in
private theorem hookedExterns_check_ok :
    libsignalHookedExterns =
        lsHookedExternIdxs.map (fun idx => lsInternedMultiLib.names.getD idx "") ∧
      (lsHookedExternIdxs.all fun idx =>
        Nat.blt idx lsInternedMultiLib.names.length &&
          (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none)) = true ∧
      (lsHookedExternIdxs.all fun sIdx =>
        lsSharedExterns.all fun eIdx =>
          Nat.beq eIdx sIdx ||
            (cliElfSymAddrs.getD eIdx 0#64 != cliElfSymAddrs.getD sIdx 0#64)) = true := by
  exact ⟨by rfl_kernel, by rfl_kernel, by rfl_kernel⟩

/-- Every `mpl` satisfying `libsignalSessionLib.LinkedAt cliElfBytes mpl` assigns each dispatched
extern target in `libsignalHookedExterns` an address distinct from every other extern in
`libsignalSessionExterns` (`ExternsDistinctOnHooked mpl.ρ`). -/
theorem cliElf_externs_distinct_of_linkedAt {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    ExternsDistinctOnHooked mpl.ρ := by
  have huniq := (cliElf_linkedAt_unique hlink).2.2.1
  intro sym hsym e he hρ
  rw [hookedExterns_check_ok.1, List.mem_map] at hsym
  rcases hsym with ⟨sIdx, hsIdx, rfl⟩
  rw [sharedExterns_check_ok.1, List.mem_map] at he
  rcases he with ⟨eIdx, heIdx, rfl⟩
  have hsOk := List.all_eq_true.mp hookedExterns_check_ok.2.1 sIdx hsIdx
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hsOk
  have heOk := List.all_eq_true.mp sharedExterns_check_ok.2 eIdx heIdx
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at heOk
  have hsρ :
      mpl.ρ (lsInternedMultiLib.names.getD sIdx "") = cliElfSymAddrs.getD sIdx 0#64 :=
    (huniq _ (mem_lsNames_of_lt hsOk.1) (lookupBlockSym_none_of_lt hsOk.1 hsOk.2)).trans
      (cliElf_rho_getD_eq hsOk.1)
  have heρ :
      mpl.ρ (lsInternedMultiLib.names.getD eIdx "") = cliElfSymAddrs.getD eIdx 0#64 :=
    (huniq _ (mem_lsNames_of_lt heOk.1) (lookupBlockSym_none_of_lt heOk.1 heOk.2)).trans
      (cliElf_rho_getD_eq heOk.1)
  have haddrEq : cliElfSymAddrs.getD eIdx 0#64 = cliElfSymAddrs.getD sIdx 0#64 :=
    heρ.symm.trans (hρ.trans hsρ)
  have hpair :=
    List.all_eq_true.mp (List.all_eq_true.mp hookedExterns_check_ok.2.2 sIdx hsIdx) eIdx heIdx
  simp only [Bool.or_eq_true, Nat.beq_eq, bne_iff_ne] at hpair
  rcases hpair with rfl | hne
  · rfl
  · exact absurd haddrEq hne

abbrev spqrOnceCallSymName : String :=
  "_RNvMs0_NtNtNtNtCsfr5T3GFabw_3std3sys4sync4once5futexNtB5_4Once4call"

set_option maxRecDepth 4000000 in
private theorem onceCallExtern_check_ok :
    libsignalSessionExterns.contains spqrOnceCallSymName = true ∧
    (lsSharedExterns.all fun sIdx =>
      if lsInternedMultiLib.names.getD sIdx "" == spqrOnceCallSymName then
        lsSharedExterns.all fun eIdx =>
          Nat.beq eIdx sIdx ||
            (cliElfSymAddrs.getD eIdx 0#64 != cliElfSymAddrs.getD sIdx 0#64)
      else true) = true :=
  ⟨by rfl_kernel, by rfl_kernel⟩

/-- Every `mpl` satisfying `libsignalSessionLib.LinkedAt cliElfBytes mpl` assigns `spqrOnceCallSym`
an address distinct from every other extern in `libsignalSessionExterns`. -/
theorem cliElf_onceCall_unique_of_linkedAt {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (e : String) (he : e ∈ libsignalSessionExterns)
    (hρ : mpl.ρ e = mpl.ρ spqrOnceCallSymName) :
    e = spqrOnceCallSymName := by
  have huniq := (cliElf_linkedAt_unique hlink).2.2.1
  have hmem_s : spqrOnceCallSymName ∈ libsignalSessionExterns :=
    List.contains_iff_mem.mp onceCallExtern_check_ok.1
  rw [sharedExterns_check_ok.1, List.mem_map] at hmem_s he
  rcases hmem_s with ⟨sIdx, hsIdx, hsEq⟩
  rcases he with ⟨eIdx, heIdx, rfl⟩
  have hsOk := List.all_eq_true.mp sharedExterns_check_ok.2 sIdx hsIdx
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hsOk
  have heOk := List.all_eq_true.mp sharedExterns_check_ok.2 eIdx heIdx
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at heOk
  have hsρ :
      mpl.ρ (lsInternedMultiLib.names.getD sIdx "") = cliElfSymAddrs.getD sIdx 0#64 :=
    (huniq _ (mem_lsNames_of_lt hsOk.1) (lookupBlockSym_none_of_lt hsOk.1 hsOk.2)).trans
      (cliElf_rho_getD_eq hsOk.1)
  have heρ :
      mpl.ρ (lsInternedMultiLib.names.getD eIdx "") = cliElfSymAddrs.getD eIdx 0#64 :=
    (huniq _ (mem_lsNames_of_lt heOk.1) (lookupBlockSym_none_of_lt heOk.1 heOk.2)).trans
      (cliElf_rho_getD_eq heOk.1)
  rw [← hsEq] at hρ
  have haddrEq : cliElfSymAddrs.getD eIdx 0#64 = cliElfSymAddrs.getD sIdx 0#64 :=
    heρ.symm.trans (hρ.trans hsρ)
  have hrow := List.all_eq_true.mp onceCallExtern_check_ok.2 sIdx hsIdx
  have hbeq : (lsInternedMultiLib.names.getD sIdx "" == spqrOnceCallSymName) = true :=
    beq_iff_eq.mpr hsEq
  simp only [hbeq, ↓reduceIte] at hrow
  have hpair := List.all_eq_true.mp hrow eIdx heIdx
  simp only [Bool.or_eq_true, Nat.beq_eq, bne_iff_ne] at hpair
  rcases hpair with rfl | hne
  · exact hsEq
  · exact absurd haddrEq hne

/-- Guard checking that `libsignalHookedExterns` equals the `18` crate-referenced Rust panic entry
points (`cliCratePanicSyms`), the `46` ghost-spec'd linked functions (`cliDehookedSymsPlaced.take 46`),
and `"libsignal_session_rng_fill"`, that `cliDehookedSymsPlaced` has length `55`, and that
`libsignalHookedExterns` omits the `7` unhooked `core::fmt` helpers and `2` SPQR CPU-probe symbols
(`cliDehookedSymsPlaced.drop 46`). -/
theorem libsignalHookedExterns_tables_guard :
    libsignalHookedExterns =
        cliCratePanicSyms ++ cliDehookedSymsPlaced.take 46 ++
          ["libsignal_session_rng_fill"] ∧
      cliDehookedSymsPlaced.length = 55 ∧
      ((cliDehookedSymsPlaced.drop 46).all (!libsignalHookedExterns.contains ·)) = true :=
  ⟨rfl, rfl, by decide⟩

/-! ## Two-Placement Execution Determinism Re-exports -/

theorem cliTokenPatchPlaced_eq_of_linkedAt {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    cliTokenPatchPlaced mpl = cliTokenPatchPlaced cliElfMultiPlacement :=
  ElfCodeMatchesPlaced.cliTokenPatchPlaced_eq_of_linkedAt hlink

theorem cliRunsToPlaced_eq_of_linkedAt {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) :
    CliRunsToPlaced mpl mmpl cliElfImage W =
      CliRunsToPlaced cliElfMultiPlacement mmpl cliElfImage W :=
  ElfCodeMatchesPlaced.cliRunsToPlaced_eq_of_linkedAt hlink mmpl W

theorem cliRunPlacedSig_eq_of_linkedAt {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) :
    cliRunPlacedSig mpl mmpl cliElfImage W =
      cliRunPlacedSig cliElfMultiPlacement mmpl cliElfImage W :=
  ElfCodeMatchesPlaced.cliRunPlacedSig_eq_of_linkedAt hlink mmpl W

theorem cliReachesOOMPlaced_iff_of_linkedAt {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) (i : Inputs) :
    CliReachesOOMPlaced mpl mmpl cliElfImage W i ↔
      CliReachesOOMPlaced cliElfMultiPlacement mmpl cliElfImage W i :=
  ElfCodeMatchesPlaced.cliReachesOOMPlaced_iff_of_linkedAt hlink mmpl W i

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced

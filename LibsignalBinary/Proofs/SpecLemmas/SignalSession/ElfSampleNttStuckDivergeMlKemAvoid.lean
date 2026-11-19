/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidNonSntt
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidTail
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidWrap

/-!
# Unified 7-Row ML-KEM `SampleNTT` `StepsStrictAvoid` Dispatchers (`ElfSampleNttStuckDivergeMlKemAvoid`)

Combines all 7 ML-KEM `ExtraGhostTable` rows into subtable-ready dispatchers matching
`c2LinkedExtraGhosts`:
1. **2 non-`SampleNTT` rows (`c2MlKemNonSnttTable`: block 20 `lsMlkemEncaps2Sym`, block 21
   `lsMlkemValidatePkSym`):** `mlkem_nonSnttAvoidS5` and `mlkem_nonSnttAvoidS5_of_subtable`
   discharging `H2KSnttExtraFacts.nonSnttAvoidS5` on `isMlKemNonSnttSym`.
2. **5 `SampleNTT` rows (`c2MlKemSnttTable`: block 24 `lsKemEncapsSym`, block 23
   `lsKemDecapsSym`, block 10 `lsMlkemFromSeedSym`, block 19 `lsMlkemEncaps1Sym`, block 22
   `lsMlkemDecapsSym`):** `mlkem_snttStrictAvoid` and `mlkem_snttStrictAvoid_of_subtable`
   discharging `H2KSnttExtraFacts.snttStrictAvoid` across `mlkemSampleNttSyms`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoid

open Arm64 (State)
open Arm64.Obj (MultiPlacement)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks MlKemSampleNttStuckAt cliElfBytes cliExternsPlaced libsignalSessionLib
   lsKemDecapsSym lsKemEncapsSym lsMlkemDecapsSym lsMlkemEncaps1Sym lsMlkemEncaps2Sym
   lsMlkemFromSeedSym lsMlkemValidatePkSym)
open CryptoVerification.SignalSession.Cli.RunGlue (ExtraGhostTable cliExtraGhostSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2MlkemMpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
  (c2ExternTableFacts_of_linkedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms mlkemSampleNttTermOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook
  (kemDecapsGhostAt kemEncapsGhostAt mlkemDecapsGhostAt mlkemEncaps1GhostAt mlkemEncaps2GhostAt
   mlkemFromSeedGhostAt mlkemValidatePkGhostAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (kemDecapsTightStack kemEncapsTightStack mlkemDecapsTightStack mlkemEncaps1TightStack
   mlkemEncaps2TightStack mlkemFromSeedTightStack mlkemValidatePkTightStack)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidNonSntt
  (c2_mlkemEncaps2_avoidS5 c2_mlkemValidatePk_avoidS5)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidTail
  (c2_kemDecaps_snttStrictAvoid c2_kemEncaps_snttStrictAvoid c2_mlkemDecaps_snttStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidWrap
  (c2_mlkemEncaps1_snttStrictAvoid c2_mlkemFromSeed_snttStrictAvoid)

/-! ## 1. Subtable & Lookup Helpers -/

private theorem lookup_cons_some {α : Type} {s k : String} {v f : α} {rest : List (String × α)}
    (h : List.lookup s ((k, v) :: rest) = some f) :
    (s = k ∧ f = v) ∨ List.lookup s rest = some f := by
  unfold List.lookup at h
  cases hsk : (s == k)
  · rw [hsk] at h
    exact Or.inr h
  · rw [hsk] at h
    exact Or.inl ⟨beq_iff_eq.mp hsk, (Option.some.inj h).symm⟩

/-! ## 2. 2-Row Non-`SampleNTT` ML-KEM Subtable (`B20` & `B21`) -/

/-- Ordered list of the 2 non-`SampleNTT` ML-KEM `ExtraGhostTable` symbols (`B20` and `B21`). -/
@[expose] def c2MlKemNonSnttSyms : List String :=
  [lsMlkemEncaps2Sym, lsMlkemValidatePkSym]

/-- Membership predicate for the 2 non-`SampleNTT` ML-KEM `ExtraGhostTable` symbols. -/
@[expose] def isMlKemNonSnttSym (sym : String) : Bool :=
  c2MlKemNonSnttSyms.contains sym

/-- Canonical 2-row non-`SampleNTT` ML-KEM `ExtraGhostTable` slice matching `c2LinkedExtraGhosts`. -/
@[expose] noncomputable def c2MlKemNonSnttTable [LibsignalPlacement] : ExtraGhostTable :=
  [ (lsMlkemEncaps2Sym, mlkemEncaps2GhostAt c2MlkemMpl mlkemEncaps2TightStack),
    (lsMlkemValidatePkSym, mlkemValidatePkGhostAt c2MlkemMpl mlkemValidatePkTightStack) ]

theorem c2MlKemNonSnttTable_keys [LibsignalPlacement] :
    c2MlKemNonSnttTable.map Prod.fst = c2MlKemNonSnttSyms :=
  rfl

theorem isMlKemNonSnttSym_imp_cliExtraGhostSyms {sym : String}
    (h : isMlKemNonSnttSym sym = true) :
    cliExtraGhostSyms.contains sym = true := by
  have hmem := List.contains_iff_mem.mp h
  simp only [c2MlKemNonSnttSyms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> decide

theorem isMlKemNonSnttSym_imp_not_sntt {sym : String}
    (h : isMlKemNonSnttSym sym = true) :
    mlkemSampleNttSyms.contains sym = false := by
  have hmem := List.contains_iff_mem.mp h
  simp only [c2MlKemNonSnttSyms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> decide

/-- Unified `StepsStrictAvoid` dispatcher across the 2 non-`SampleNTT` ML-KEM rows (`B20`, `B21`). -/
theorem mlkem_nonSnttAvoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) (sym : String) (f : State → State)
    (_hNonSntt : isMlKemNonSnttSym sym = true)
    (hLookTbl : c2MlKemNonSnttTable.lookup sym = some f)
    (u : State)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f u).status ≠ .Exception msg)
    (_hkf : u.mem.KeepsFrozen (f u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (f u) := by
  have hExt := c2ExternTableFacts_of_linkedAt hLs
  dsimp only [c2MlKemNonSnttTable] at hLookTbl
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_mlkemEncaps2_avoidS5 hLs hLs hExt (Nat.le_refl _) (by decide)
      W hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_mlkemValidatePk_avoidS5 hLs hLs hExt (Nat.le_refl _) (by decide)
      W hpc hrun hnoex hfr hinv
  cases hLookTbl

/-- Subtable wrapper around `mlkem_nonSnttAvoidS5` for any composite `extra : ExtraGhostTable`
    that agrees with `c2MlKemNonSnttTable` on `isMlKemNonSnttSym`. -/
theorem mlkem_nonSnttAvoidS5_of_subtable [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {extra : ExtraGhostTable}
    (hSub : ∀ s : String, isMlKemNonSnttSym s = true →
      extra.lookup s = c2MlKemNonSnttTable.lookup s)
    (W : CliHooks) (sym : String) (f : State → State)
    (hNonSntt : isMlKemNonSnttSym sym = true)
    (hLookExtra : extra.lookup sym = some f)
    (u : State)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (f u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (f u) :=
  mlkem_nonSnttAvoidS5 hLs W sym f hNonSntt ((hSub sym hNonSntt).symm.trans hLookExtra)
    u hpc hrun hnoex hkf hfr hinv

/-! ## 3. 5-Row `SampleNTT` ML-KEM Subtable (`B24`, `B23`, `B10`, `B19`, `B22`) -/

/-- Canonical 5-row `SampleNTT` ML-KEM `ExtraGhostTable` slice matching `c2LinkedExtraGhosts`. -/
@[expose] noncomputable def c2MlKemSnttTable [LibsignalPlacement] : ExtraGhostTable :=
  [ (lsKemEncapsSym, kemEncapsGhostAt c2MlkemMpl kemEncapsTightStack),
    (lsKemDecapsSym, kemDecapsGhostAt c2MlkemMpl kemDecapsTightStack),
    (lsMlkemFromSeedSym, mlkemFromSeedGhostAt c2MlkemMpl mlkemFromSeedTightStack),
    (lsMlkemEncaps1Sym, mlkemEncaps1GhostAt c2MlkemMpl mlkemEncaps1TightStack),
    (lsMlkemDecapsSym, mlkemDecapsGhostAt c2MlkemMpl mlkemDecapsTightStack) ]

theorem c2MlKemSnttTable_keys [LibsignalPlacement] :
    c2MlKemSnttTable.map Prod.fst = mlkemSampleNttSyms :=
  rfl

/-- Unified 5-row `SampleNTT` strict-avoidance + `ExecFrozen` dispatcher across `c2MlKemSnttTable`. -/
theorem mlkem_snttStrictAvoid [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) (sym : String) (f : State → State) (u : State)
    (_hsym : sym ∈ mlkemSampleNttSyms)
    (hLookTbl : c2MlKemSnttTable.lookup sym = some f)
    (hTerm : mlkemSampleNttTermOf sym u)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (f u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt lsmpl z)
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
      ExecFrozen (f u).mem := by
  have hExt := c2ExternTableFacts_of_linkedAt hLs
  dsimp only [c2MlKemSnttTable] at hLookTbl
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_kemEncaps_snttStrictAvoid hLs hLs hExt (Nat.le_refl _) (by decide)
      W hTerm hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_kemDecaps_snttStrictAvoid hLs hLs hExt (Nat.le_refl _) (by decide)
      W hTerm hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_mlkemFromSeed_snttStrictAvoid hLs hExt mlkemFromSeedTightStack
      (Nat.le_refl _) (by decide) W u hTerm hpc hrun hnoex hkf hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_mlkemEncaps1_snttStrictAvoid hLs hExt mlkemEncaps1TightStack
      (Nat.le_refl _) (by decide) W u hTerm hpc hrun hnoex hkf hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_mlkemDecaps_snttStrictAvoid hLs hLs hExt (Nat.le_refl _) (by decide)
      W hTerm hpc hrun hnoex hfr hinv
  cases hLookTbl

/-- Subtable wrapper around `mlkem_snttStrictAvoid` for any composite `extra : ExtraGhostTable`
    that agrees with `c2MlKemSnttTable` on `mlkemSampleNttSyms`. -/
theorem mlkem_snttStrictAvoid_of_subtable [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {extra : ExtraGhostTable}
    (hSub : ∀ s : String, s ∈ mlkemSampleNttSyms → extra.lookup s = c2MlKemSnttTable.lookup s)
    (W : CliHooks) (sym : String) (f : State → State) (u : State)
    (hsym : sym ∈ mlkemSampleNttSyms)
    (hLookExtra : extra.lookup sym = some f)
    (hTerm : mlkemSampleNttTermOf sym u)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (f u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt lsmpl z)
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
      ExecFrozen (f u).mem :=
  mlkem_snttStrictAvoid hLs W sym f u hsym ((hSub sym hsym).symm.trans hLookExtra)
    hTerm hpc hrun hnoex hkf hfr hinv

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoid

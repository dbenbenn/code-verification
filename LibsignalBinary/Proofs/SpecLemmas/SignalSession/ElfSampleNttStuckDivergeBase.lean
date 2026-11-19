/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliPlainPanPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTight -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeNamedAvoid -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDomainArms -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec
import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie

/-!
# `ElfSlicesPqOomH2KHooks`-Free Stuck-`SampleNTT` Assembly (`ElfSampleNttStuckDivergeBase`)

`ghFixed`-parametric assembly of `ElfSampleNttStuckDivergeCore`,
`ElfSampleNttStuckDomainArms`, `ElfSampleNttStuckDivergeNamedAvoid`,
`ElfSampleNttStuckDivergeExtraTight`, `T4Witness`, and `ElfSlicesPqOomPlacedG`, together with
the 38-symbol `cliExtraGhostSyms` partition (`23` tight + `2` ML-KEM non-`SampleNTT` + `8` wide +
`5` `mlkemSampleNttSyms`) and `h2kSnttExtraFacts_of_subtables`.

Kept free of importing `ElfSlicesPqOomH2KHooks` or `ElfSlicesPqOomH2KGhostArms` so it builds
independently of `H2KHooks` and avoids an import cycle with `ElfSlicesPqOomH2KGhostArms`.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeBase

open Arm64 (State Steps)
open ProofLib (hookNoop)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs MlKemSampleNttStuckAt cliElfBytes cliElfImage cliElf_parse
   cliExternsPlaced libsignalSessionLib lsAesDecSym lsAesEncSym lsFmtWriteSym lsFormatInnerSym
   lsKemDecapsSym lsKemEncapsSym lsLibcruxHmacSym lsMlkemDecapsSym lsMlkemEncaps1Sym
   lsMlkemEncaps2Sym lsMlkemFromSeedSym lsMlkemValidatePkSym lsSpqrOnceCallSym
   lsWriteFileSym lsWriteStdoutSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks ExtraGhostTable cliExtraGhostSyms cliGhostExterns cliGhostExternsWithExtra)
open LibsignalBinary.Heap (rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpec)
open LibsignalBinary.Proofs.Placed.CliPlainPanPlaced
  (CliReachesOOMPlainPanPlaced CliReachesSampleNttStuckPlainPanPlaced cliRunPlainPanPlacedSig)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G (V2F3StuckDomain)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (f3AllocFallback f3DeallocFallback f3LinkedCallHook f3ReallocFallback)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard (c2GuardOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2MlkemMpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
  (c2ExternTableFacts_of_linkedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (ExtraRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (AtCallRowReplayOn mlkemSampleNttSyms mlkemSampleNttTermOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook
  (kemDecapsGhostAt kemEncapsGhostAt mlkemDecapsGhostAt mlkemEncaps1GhostAt mlkemFromSeedGhostAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
  (f3EmptyMemcpyGhostHookNarrow f3EmptyMemsetGhostHookNarrow)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (kemDecapsTightStack kemEncapsTightStack mlkemDecapsTightStack mlkemEncaps1TightStack
   mlkemFromSeedTightStack)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv cliElf_f3B2NeedLocksAssumptions)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (GhostFixedFacts H2KSnttExtraFacts NamedGhostStepsBelow4b0000 NamedHarnessBelow4b0000
   StepsStrictAvoid cliRunPlacedSig_none_and_not_oom_of_ghostMainCase)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTight
  (c2ExtraTightTable extraTight_nonSnttAvoidS5_of_subtable isExtraTightSym)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeNamedAvoid
  (avoid_readFileFixedGhostHookFineK avoid_readStdinGhostHookFineK avoid_withKeepLrFalse
   cliElf_f3MuslHarness_c2EntryGuard_of_below4b0000 namedGhost_steps_of_below4b0000_of_ghFixed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDomainArms
  (GhostMainArmsFor v2F3StuckDomain_ghostMainCase_of_arms)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_emptyProg hole2_hblk hole2_hext_nodup hole2_hookStack hole2_keepSub hole2_targets)
open VerifiedLibraries (mallocngLib)

/-! ## 1. Named-Hook Seam Dischargers (`NamedHarnessBelow4b0000` & `NamedGhostStepsBelow4b0000`) -/

/-- Discharges `NamedHarnessBelow4b0000 mpl mmpl` from `ElfSampleNttStuckDivergeNamedAvoid`. -/
theorem namedHarness_h2k {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    NamedHarnessBelow4b0000 mpl mmpl :=
  fun P W hsvc hext => cliElf_f3MuslHarness_c2EntryGuard_of_below4b0000 hLs hMm W P hsvc hext

/-- Discharges `NamedGhostStepsBelow4b0000` for any `ghFixed : CliGhostHooks` whose 9 non-
    `stringClone` fields match `h2k_ghFixedK mpl mmpl` (all 9 equations hold by `rfl` on
    `h2k_ghFixedK mpl mmpl`). -/
theorem namedGhostSteps_of_ghFixed_eq [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (ghFixed : CliGhostHooks)
    (hAlloc : ghFixed.alloc =
      f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).alloc
        (fun γ tp => avoid_withKeepLrFalse hole2_keepSub
          (rustCliAllocBudgetSpec fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits false))
        (f3AllocFallback mmpl false))
    (hDealloc : ghFixed.dealloc =
      f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).dealloc
        (fun γ tp => avoid_withKeepLrFalse hole2_keepSub
          (rustCliDeallocBudgetSpec fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits))
        (f3DeallocFallback mmpl))
    (hRealloc : ghFixed.realloc =
      f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).realloc
        (fun γ tp => avoid_withKeepLrFalse hole2_keepSub
          (rustCliReallocBudgetSpec fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits))
        (f3ReallocFallback mmpl))
    (hAz : ghFixed.allocZeroed =
      f3LinkedCallHook hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).allocZeroed
        (fun γ tp => avoid_withKeepLrFalse hole2_keepSub
          (rustAllocZeroedBudgetSpec fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits))
        (f3AllocFallback mmpl true))
    (hShim : ghFixed.shim = hookNoop)
    (hReadFile : ∀ f h, ghFixed.readFile = some ⟨f, h⟩ →
      f = avoid_readFileFixedGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readFile mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
    (hReadStdin : ∀ f h, ghFixed.readStdin = some ⟨f, h⟩ →
      f = avoid_readStdinGhostHookFineK hole2_keepSub hole2_emptyProg f3TrialRxProg
        (hole2_targets mpl).readStdin mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
    (hMemset : ghFixed.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hMemcpy : ghFixed.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl)) :
    NamedGhostStepsBelow4b0000 mpl mmpl hole2_keepSub ghFixed :=
  fun P W hsvc hext =>
    namedGhost_steps_of_below4b0000_of_ghFixed hLs hMm W P hsvc hext ghFixed
      hAlloc hDealloc hRealloc hAz hShim hReadFile hReadStdin hMemset hMemcpy

/-! ## 2. 33-Row Non-`SampleNTT` Symbol Partition (`23` Tight + `2` ML-KEM + `8` Wide) -/

/-- The 2 non-`SampleNTT` ML-KEM `ExtraGhostTable` symbols (`B20` and `B21`). -/
@[expose] def c2MlKemNonSnttSymsBase : List String :=
  [lsMlkemEncaps2Sym, lsMlkemValidatePkSym]

/-- The 8 wide-keep `ExtraGhostTable` symbols. -/
@[expose] def c2ExtraWideSymsBase : List String :=
  [ lsLibcruxHmacSym,
    lsAesEncSym,
    lsAesDecSym,
    lsWriteFileSym,
    lsWriteStdoutSym,
    lsFmtWriteSym,
    lsFormatInnerSym,
    lsSpqrOnceCallSym ]

set_option maxRecDepth 400000 in
private theorem cliExtraGhostSyms_partition_check :
    (cliExtraGhostSyms.all fun s =>
      mlkemSampleNttSyms.contains s ||
      isExtraTightSym s ||
      c2MlKemNonSnttSymsBase.contains s ||
      c2ExtraWideSymsBase.contains s) = true := by
  decide

/-- Every non-`mlkemSampleNttSyms` symbol in `cliExtraGhostSyms` belongs to `isExtraTightSym` (23),
    `c2MlKemNonSnttSymsBase` (2), or `c2ExtraWideSymsBase` (8). -/
theorem cliExtraGhostSyms_nonSntt_cases {sym : String}
    (hDom : cliExtraGhostSyms.contains sym = true)
    (hNotSntt : mlkemSampleNttSyms.contains sym = false) :
    isExtraTightSym sym = true ∨
      c2MlKemNonSnttSymsBase.contains sym = true ∨
      c2ExtraWideSymsBase.contains sym = true := by
  have hall := List.all_eq_true.mp cliExtraGhostSyms_partition_check sym
    (List.contains_iff_mem.mp hDom)
  rw [hNotSntt] at hall
  simp only [Bool.false_or, Bool.or_eq_true] at hall
  rcases hall with (hT | hM) | hW
  · exact Or.inl hT
  · exact Or.inr (Or.inl hM)
  · exact Or.inr (Or.inr hW)

/-- Assembles `H2KSnttExtraFacts` at `lsmpl` from `extraTight_nonSnttAvoidS5_of_subtable` plus the
    2-row ML-KEM non-`SampleNTT`, 8-row `ExtraWide`, and 5-row `SampleNTT` subtable obligations. -/
theorem h2kSnttExtraFacts_of_subtables [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hGMemcpy : ghFixed.memcpy = none ∨ ghFixed.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : ghFixed.memset = none ∨ ghFixed.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hSubTight : ∀ s : String, isExtraTightSym s = true →
      extra.lookup s = (c2ExtraTightTable mmpl).lookup s)
    (hLookKemEncaps :
      ∃ stk, kemEncapsTightStack ≤ stk ∧ stk ≤ 2 ^ 64 ∧
        extra.lookup lsKemEncapsSym = some (kemEncapsGhostAt c2MlkemMpl stk))
    (hLookKemDecaps :
      ∃ stk, kemDecapsTightStack ≤ stk ∧ stk ≤ 2 ^ 64 ∧
        extra.lookup lsKemDecapsSym = some (kemDecapsGhostAt c2MlkemMpl stk))
    (hLookMlkemFromSeed :
      ∃ stk, mlkemFromSeedTightStack ≤ stk ∧ stk ≤ 2 ^ 64 ∧
        extra.lookup lsMlkemFromSeedSym = some (mlkemFromSeedGhostAt c2MlkemMpl stk))
    (hLookMlkemEncaps1 :
      ∃ stk, mlkemEncaps1TightStack ≤ stk ∧ stk ≤ 2 ^ 64 ∧
        extra.lookup lsMlkemEncaps1Sym = some (mlkemEncaps1GhostAt c2MlkemMpl stk))
    (hLookMlkemDecaps :
      ∃ stk, mlkemDecapsTightStack ≤ stk ∧ stk ≤ 2 ^ 64 ∧
        extra.lookup lsMlkemDecapsSym = some (mlkemDecapsGhostAt c2MlkemMpl stk))
    (hAtCallSntt :
      ∀ sym f, sym ∈ mlkemSampleNttSyms → extra.lookup sym = some f →
        AtCallRowReplayOn lsmpl (fun v : State => F3CodeInv lsmpl mmpl v.mem ∧ True)
          (cliExternsPlaced mmpl) sym (mlkemSampleNttTermOf sym) f)
    (hReplaysNonSntt :
      ∀ sym f, cliExtraGhostSyms.contains sym = true →
        mlkemSampleNttSyms.contains sym = false →
        extra.lookup sym = some f →
        ExtraRowReplayOn lsmpl mmpl (fun v : State => F3CodeInv lsmpl mmpl v.mem ∧ True)
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W'))
          sym (c2GuardOf lsmpl sym) f)
    (hMlKemNonSntt :
      ∀ (W : CliHooks) (sym : String) (f : State → State),
        c2MlKemNonSnttSymsBase.contains sym = true →
        extra.lookup sym = some f →
        ∀ u : State,
          u.pc = libsignalSessionLib.resolve lsmpl sym →
          u.status = .Running →
          (∀ msg, (f u).status ≠ .Exception msg) →
          u.mem.KeepsFrozen (f u).mem →
          ExecFrozen u.mem →
          F3CodeInv lsmpl mmpl u.mem →
          StepsStrictAvoid
            (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
            (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W) u (f u))
    (hExtraWide :
      ∀ (W : CliHooks) (s0 sf : State) (sym : String) (f : State → State),
        c2GuardOf lsmpl sym s0 →
        (sf.status = .Running → sf.pc = s0.readReg64 .lr) →
        (∀ msg, sf.status ≠ .Exception msg) →
        sf.status ≠ .Halted →
        c2ExtraWideSymsBase.contains sym = true →
        extra.lookup sym = some f →
        ∀ u : State,
          Steps
            (cliProgExtPlacedAt lsmpl
              (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
            s0 u →
          Steps
            (cliProgExtPlacedAt lsmpl
              (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
            (f u) sf →
          u.pc = libsignalSessionLib.resolve lsmpl sym →
          u.status = .Running →
          (∀ msg, (f u).status ≠ .Exception msg) →
          u.mem.KeepsFrozen (f u).mem →
          ExecFrozen u.mem →
          F3CodeInv lsmpl mmpl u.mem →
          StepsStrictAvoid
            (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
            (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W) u (f u))
    (hSnttStrictAvoid :
      ∀ (W : CliHooks) (sym : String) (f : State → State) (u : State),
        sym ∈ mlkemSampleNttSyms →
        extra.lookup sym = some f →
        mlkemSampleNttTermOf sym u →
        u.pc = libsignalSessionLib.resolve lsmpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        F3CodeInv lsmpl mmpl u.mem →
        StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt lsmpl z)
          (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
          ExecFrozen (f u).mem) :
    H2KSnttExtraFacts lsmpl mmpl ghFixed extra where
  lookup_kemEncaps := hLookKemEncaps
  lookup_kemDecaps := hLookKemDecaps
  lookup_mlkemFromSeed := hLookMlkemFromSeed
  lookup_mlkemEncaps1 := hLookMlkemEncaps1
  lookup_mlkemDecaps := hLookMlkemDecaps
  atCallSntt := hAtCallSntt
  replaysNonSntt := hReplaysNonSntt
  nonSnttAvoidS5 W s0 sf sym f hGuard hRetPc hNoExSf hNotHaltSf hDom hNotSntt hLook
      u hPre hPost hpc hrun hnoex hkf hfr hinv := by
    rcases cliExtraGhostSyms_nonSntt_cases hDom hNotSntt with hT | hM | hW
    · exact extraTight_nonSnttAvoidS5_of_subtable hLs hSubTight hGMemcpy hGMemset
        W s0 sf sym f hGuard hRetPc hNoExSf hNotHaltSf hT hLook
        u hPre hPost hpc hrun hnoex hkf hfr hinv
    · exact hMlKemNonSntt W sym f hM hLook u hpc hrun hnoex hkf hfr hinv
    · exact hExtraWide W s0 sf sym f hGuard hRetPc hNoExSf hNotHaltSf hW hLook
        u hPre hPost hpc hrun hnoex hkf hfr hinv
  snttStrictAvoid := hSnttStrictAvoid

/-! ## 3. `ghFixed`-Parametric `V2F3StuckDomain` Divergence & OOM-Freedom -/

/-- Full `V2F3StuckDomain` divergence and OOM-freedom theorem parameterized over `ghFixed`. -/
theorem cliRunPlacedSig_none_and_not_oom_of_v2F3StuckDomain_of_ghFixed
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (ghFixed :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      CliGhostHooks)
    (hArms :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      GhostMainArmsFor mpl mmpl (fun W => cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hGh :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      GhostFixedFacts mpl mmpl hole2_keepSub ghFixed)
    (hNamedSteps :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      NamedGhostStepsBelow4b0000 mpl mmpl hole2_keepSub ghFixed)
    (hExtra :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      H2KSnttExtraFacts mpl mmpl ghFixed ghFixed.extra)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (i : Inputs)
    (hDom : V2F3StuckDomain ⟨W.C, W.Q⟩ i)
    (hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl cliElfImage W i) :
    cliRunPlainPanPlacedSig mpl mmpl cliElfImage W i = none ∧
      ¬ CliReachesOOMPlainPanPlaced mpl mmpl cliElfImage W i := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have h547 : mpl.base 547 ≠ 0#64 :=
    (cliElf_f3B2NeedLocksAssumptions hLs hMm).base547NeZero
  obtain ⟨hi, hl, Run, r, hSubGhost, hc⟩ :=
    v2F3StuckDomain_ghostMainCase_of_arms h547 hArms W
      hF hE hD hX hPub hF512 hEnc hDec hK hDom
  exact cliRunPlacedSig_none_and_not_oom_of_ghostMainCase
    hLs hMm (c2ExternTableFacts_of_linkedAt hLs)
    hGh (namedHarness_h2k hLs hMm) hNamedSteps hExtra
    W hi hl hSubGhost hc hStuck

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeBase

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesDecErrRoGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWriteRow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LibcruxHmacGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrOnceCallGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideCrypto -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideFmt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideWrite -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `c2ExtraWideTable` & Unified 8-Row Wide-Keep `SampleNTT` Non-Visitation Dispatcher (`ElfSampleNttStuckDivergeExtraWideTable`)

Packages the 8 wide-keep `ExtraGhostTable` rows (`lsLibcruxHmacSym`, `lsAesEncSym`, `lsAesDecSym`,
`lsWriteFileSym`, `lsWriteStdoutSym`, `lsFmtWriteSym`, `lsFormatInnerSym`, `lsSpqrOnceCallSym`)
into `c2ExtraWideTable` (`c2ExtraWideSyms`, `isExtraWideSym`) and proves the unified
`extraWide_nonSnttAvoidS5` (plus `extraWide_nonSnttAvoidS5_of_subtable`) dispatcher discharging
`StepsStrictAvoid` against `mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl)` for
`H2KSnttExtraFacts.nonSnttAvoidS5`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideTable

open ProofLib.ProgramReflection

open Arm64
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib
   lsAesDecSym lsAesEncSym lsFmtWriteSym lsFormatInnerSym lsLibcruxHmacSym
   lsSpqrOnceCallSym lsWriteFileSym lsWriteStdoutSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks ExtraGhostTable cliExtraGhostSyms cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays (aesEncGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesDecErrRoGhost (aesDecErrRoGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard (c2GuardOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (aesCbcSubProg c2AesDecAddr c2AesEncAddr keepRxSeg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow
  (c2FmtWriteGhost c2FormatInnerGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWriteRow
  (c2WriteFileGhost c2WriteStdoutGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac
  (libcruxHmacSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
  (c2_resolve_spqrOnceCall_eq c2_spqrOnceCall_hRealHullNoExt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LibcruxHmacGhostReplays
  (libcruxHmacGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (emptyStdProg_externAt_none emptyStdProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrOnceCallGhostReplays
  (keepSpqrOnceCall spqrOnceCallGhost spqrOnceCallGhost_visitedIn spqrProbeGuard_of_codeLoaded)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore
  (c2S5Addrs setPC_eq_self_of_pc_eq stepsStrictAvoid_s5_of_visitedIn_all_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideCrypto
  (c2_aesDecErrRoGhost_avoidS5 c2_aesDecGhost_avoidS5 c2_aesEncGhost_avoidS5
   c2_libcruxHmacGhost_avoidS5)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideFmt
  (c2_fmtWriteGhost_avoidS5 c2_formatInnerGhost_avoidS5)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideWrite
  (c2_writeFileGhost_avoidS5 c2_writeStdoutGhost_avoidS5)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen (c2LibcruxHmacAddr)

export LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideCrypto
  (c2_aesDecGhost_avoidS5)

/-! ## 1. The 8 Wide-Keep Symbols & `c2ExtraWideTable` -/

/-- Ordered list of the 8 wide-keep `ExtraGhostTable` symbols. -/
@[expose] def c2ExtraWideSyms : List String :=
  [ lsLibcruxHmacSym,
    lsAesEncSym,
    lsAesDecSym,
    lsWriteFileSym,
    lsWriteStdoutSym,
    lsFmtWriteSym,
    lsFormatInnerSym,
    lsSpqrOnceCallSym ]

/-- Membership predicate for the 8 wide-keep `ExtraGhostTable` symbols. -/
@[expose] def isExtraWideSym (sym : String) : Bool :=
  c2ExtraWideSyms.contains sym

/-- Canonical 8-row wide-keep `ExtraGhostTable` slice specialized at `cliElfImage.brkStart`,
    `cliBudgetLimits`, and `hole2_hookStack` (`extHookStack`), matching `c2LinkedExtraGhosts mmpl`
    definitionally on every `isExtraWideSym` symbol. -/
@[expose] noncomputable def c2ExtraWideTable [LibsignalPlacement] (mmpl : MultiPlacement) :
    ExtraGhostTable :=
  [ (lsLibcruxHmacSym,
      libcruxHmacGhost
        LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac.keepRxSeg
        libcruxHmacSubProg c2LibcruxHmacAddr
        mmpl cliElfImage.brkStart cliBudgetLimits),
    (lsAesEncSym,
      aesEncGhost keepRxSeg aesCbcSubProg c2AesEncAddr
        mmpl cliElfImage.brkStart cliBudgetLimits),
    (lsAesDecSym,
      aesDecErrRoGhost keepRxSeg aesCbcSubProg c2AesDecAddr
        mmpl cliElfImage.brkStart cliBudgetLimits),
    (lsWriteFileSym,
      c2WriteFileGhost mmpl cliElfImage.brkStart cliBudgetLimits extHookStack),
    (lsWriteStdoutSym,
      c2WriteStdoutGhost mmpl cliElfImage.brkStart cliBudgetLimits extHookStack),
    (lsFmtWriteSym,
      c2FmtWriteGhost mmpl cliElfImage.brkStart cliBudgetLimits),
    (lsFormatInnerSym,
      c2FormatInnerGhost mmpl cliElfImage.brkStart cliBudgetLimits),
    (lsSpqrOnceCallSym,
      spqrOnceCallGhost) ]

/-! ## 2. Domain, Disjointness, & Table-Composition Helpers -/

theorem c2ExtraWideTable_keys [LibsignalPlacement] (mmpl : MultiPlacement) :
    (c2ExtraWideTable mmpl).map Prod.fst = c2ExtraWideSyms :=
  rfl

set_option maxRecDepth 400000 in
theorem c2ExtraWideSyms_nodup : c2ExtraWideSyms.Nodup := by
  decide

set_option maxRecDepth 400000 in
private theorem c2ExtraWideSyms_all_extra_and_nonSntt :
    (c2ExtraWideSyms.all fun s =>
      cliExtraGhostSyms.contains s && !(mlkemSampleNttSyms.contains s)) = true := by
  decide

theorem isExtraWideSym_imp_cliExtraGhostSyms {sym : String}
    (h : isExtraWideSym sym = true) :
    cliExtraGhostSyms.contains sym = true := by
  have hall := List.all_eq_true.mp c2ExtraWideSyms_all_extra_and_nonSntt sym
    (List.contains_iff_mem.mp h)
  simp only [Bool.and_eq_true] at hall
  exact hall.1

theorem isExtraWideSym_imp_not_sntt {sym : String}
    (h : isExtraWideSym sym = true) :
    mlkemSampleNttSyms.contains sym = false := by
  have hall := List.all_eq_true.mp c2ExtraWideSyms_all_extra_and_nonSntt sym
    (List.contains_iff_mem.mp h)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall
  exact hall.2

private theorem lookup_isSome_eq_map_fst_contains {α : Type} (sym : String) :
    ∀ t : List (String × α), (t.lookup sym).isSome = (t.map Prod.fst).contains sym
  | [] => rfl
  | (k, _) :: rest => by
    simp only [List.lookup, List.map_cons, List.contains_cons]
    cases sym == k
    · exact lookup_isSome_eq_map_fst_contains sym rest
    · rfl

theorem c2ExtraWideTable_lookup_isSome [LibsignalPlacement] (mmpl : MultiPlacement)
    (sym : String) :
    ((c2ExtraWideTable mmpl).lookup sym).isSome = isExtraWideSym sym :=
  lookup_isSome_eq_map_fst_contains sym (c2ExtraWideTable mmpl)

private theorem lookup_append_of_isSome {α : Type} {sym : String} {t₁ t₂ : List (String × α)}
    (h : (t₁.lookup sym).isSome = true) :
    (t₁ ++ t₂).lookup sym = t₁.lookup sym := by
  induction t₁ with
  | nil => cases h
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [List.cons_append, List.lookup] at h ⊢
    cases hsk : sym == k
    · rw [hsk] at h
      exact ih h
    · rfl

private theorem lookup_append_of_isNone {α : Type} {sym : String} {t₁ t₂ : List (String × α)}
    (h : (t₁.lookup sym).isSome = false) :
    (t₁ ++ t₂).lookup sym = t₂.lookup sym := by
  induction t₁ with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [List.cons_append, List.lookup] at h ⊢
    cases hsk : sym == k
    · rw [hsk] at h
      exact ih h
    · rw [hsk] at h
      cases h

theorem c2ExtraWideTable_lookup_append_of_true [LibsignalPlacement]
    (mmpl : MultiPlacement) (rest : ExtraGhostTable) {sym : String}
    (h : isExtraWideSym sym = true) :
    (c2ExtraWideTable mmpl ++ rest).lookup sym = (c2ExtraWideTable mmpl).lookup sym :=
  lookup_append_of_isSome ((c2ExtraWideTable_lookup_isSome mmpl sym).trans h)

theorem c2ExtraWideTable_lookup_append_of_false [LibsignalPlacement]
    (mmpl : MultiPlacement) (rest : ExtraGhostTable) {sym : String}
    (h : isExtraWideSym sym = false) :
    (c2ExtraWideTable mmpl ++ rest).lookup sym = rest.lookup sym :=
  lookup_append_of_isNone ((c2ExtraWideTable_lookup_isSome mmpl sym).trans h)

private theorem lookup_cons_some {α : Type} {s k : String} {v f : α} {rest : List (String × α)}
    (h : List.lookup s ((k, v) :: rest) = some f) :
    (s = k ∧ f = v) ∨ List.lookup s rest = some f := by
  unfold List.lookup at h
  cases hsk : (s == k)
  · rw [hsk] at h
    exact Or.inr h
  · rw [hsk] at h
    exact Or.inl ⟨beq_iff_eq.mp hsk, (Option.some.inj h).symm⟩

/-! ## 3. Unified 8-Row `StepsStrictAvoid` Dispatcher -/

set_option maxRecDepth 400000 in
private theorem c2S5Addrs_keepSpqrOnceCall_false (mpl : MultiPlacement) :
    (c2S5Addrs.all fun p => !(keepSpqrOnceCall mpl p)) = true := by
  rfl_kernel

theorem c2_spqrOnceCallGhost_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsSpqrOnceCallSym)
    (_hrun : u.status = .Running)
    (hnoex : ∀ msg, (spqrOnceCallGhost u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (spqrOnceCallGhost u) := by
  obtain ⟨hvis, _⟩ :=
    spqrOnceCallGhost_visitedIn (spqrProbeGuard_of_codeLoaded hLs hinv.lsRo.1 hinv.rxCode) hnoex hfr
  rw [setPC_eq_self_of_pc_eq (hpc.trans (c2_resolve_spqrOnceCall_eq hLs))] at hvis
  exact stepsStrictAvoid_s5_of_visitedIn_all_false hLs emptyStdProg_svc
    (fun pc _ => emptyStdProg_externAt_none pc)
    (fun _ hk => c2_spqrOnceCall_hRealHullNoExt hLs W hk)
    (c2S5Addrs_keepSpqrOnceCall_false lsmpl)
    hvis

/-- Unified `StepsStrictAvoid` dispatcher across all 8 rows of `c2ExtraWideTable`, matching
    `H2KSnttExtraFacts.nonSnttAvoidS5` at `mpl := lsmpl`. -/
theorem extraWide_nonSnttAvoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (W : CliHooks) (s0 sf : State) (sym : String) (f : State → State)
    (_hGuard : c2GuardOf lsmpl sym s0)
    (_hRetPc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (_hNoExSf : ∀ msg, sf.status ≠ .Exception msg)
    (_hNotHaltSf : sf.status ≠ .Halted)
    (_hWide : isExtraWideSym sym = true)
    (hLookTbl : (c2ExtraWideTable mmpl).lookup sym = some f)
    (_hLookExtra : extra.lookup sym = some f)
    (u : State)
    (_hStepsBefore :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        s0 u)
    (_hStepsAfter :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        (f u) sf)
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
  dsimp only [c2ExtraWideTable] at hLookTbl
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_libcruxHmacGhost_avoidS5 (W := W) hLs hLs hMm hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_aesEncGhost_avoidS5 (W := W) hLs hLs hMm hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_aesDecErrRoGhost_avoidS5 (W := W) hLs hLs hMm hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_writeFileGhost_avoidS5 (W := W) hLs hLs hMm (by decide) hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_writeStdoutGhost_avoidS5 (W := W) hLs hLs hMm (by decide) hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_fmtWriteGhost_avoidS5 (W := W) hLs hLs hMm hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_formatInnerGhost_avoidS5 (W := W) hLs hLs hMm hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact c2_spqrOnceCallGhost_avoidS5 hLs W hpc hrun hnoex hfr hinv
  cases hLookTbl

/-- Subtable wrapper around `extraWide_nonSnttAvoidS5` for any composite `extra : ExtraGhostTable`
    that agrees with `c2ExtraWideTable mmpl` on `isExtraWideSym`. -/
theorem extraWide_nonSnttAvoidS5_of_subtable [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hSub : ∀ s : String, isExtraWideSym s = true →
      extra.lookup s = (c2ExtraWideTable mmpl).lookup s)
    (W : CliHooks) (s0 sf : State) (sym : String) (f : State → State)
    (hGuard : c2GuardOf lsmpl sym s0)
    (hRetPc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hNoExSf : ∀ msg, sf.status ≠ .Exception msg)
    (hNotHaltSf : sf.status ≠ .Halted)
    (hWide : isExtraWideSym sym = true)
    (hLookExtra : extra.lookup sym = some f)
    (u : State)
    (hStepsBefore :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        s0 u)
    (hStepsAfter :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        (f u) sf)
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
  extraWide_nonSnttAvoidS5 hLs hMm W s0 sf sym f hGuard hRetPc hNoExSf hNotHaltSf
    hWide ((hSub sym hWide).symm.trans hLookExtra) hLookExtra u hStepsBefore hStepsAfter
    hpc hrun hnoex hkf hfr hinv

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideTable

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Dalek
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DalekRows
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DurCst16
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8Row
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcRows
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MemmoveRow
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MemrchrRow
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostLs
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostReplays
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrap
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostReplaysOn
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhostK

/-!
# Tight-Keep `SampleNTT` Non-Visitation for the 9 Libc / `memrchr` / `from_utf8` / Time / Dalek-Leaf Rows (`ElfSampleNttStuckDivergeExtraTightRows`)

Discharges `StepsStrictAvoid` against `mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl)`
for the remaining 9 tight-keep rows of `c2ExtraTightTable`:
`"memmove"`, `"bcmp"`, `"strlen"`, `lsMemrchrSym`, `lsFromUtf8Sym`, `lsDurationSinceSym`,
`lsTimeAddSym`, `lsBlackBoxSym`, and `lsStaticSecretDropSym`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightRows

open Arm64
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries.RustStd
  (timeAddSym timeMultiLib timePlacedData0 timeRodataCst16Sym)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
   lsBlackBoxSym lsDurationSinceSym lsFromUtf8Sym lsMemrchrSym
   lsStaticSecretDropSym lsTimeAddSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode (memcmpByteLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostK (f3EmptyBcmpGhostHook_visitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays
  (bcmpEntryGuard bcmpGhost bcmpHullBase bcmpSubProg
   bcmpSubProg_codeLoaded_stripExecOutside bcmpSubProg_externAt_none
   bcmpSubProg_hasWords bcmpSubProg_svc keepR_bcmp)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap
  (f3EmptyBcmpGhostHook_keepLr_false_after_hook_of_codeLoaded_u)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhost
  (f3EmptyBlackBoxGhostHook_visitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays
  (blackBoxEntryGuard blackBoxGhost blackBoxSubProg
   blackBoxSubProg_codeLoaded_stripExecOutside blackBoxSubProg_externAt_none
   blackBoxSubProg_hasWords blackBoxSubProg_svc keepR_blackBox)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxLrTrap
  (f3EmptyBlackBoxGhostHook_keepLr_false_after_hook_of_codeLoaded_u)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Dalek
  (keepR_blackBox_noPanic keepR_blackBox_sub_keepLib2Text keepR_staticSecretDrop_noPanic
   keepR_staticSecretDrop_sub_keepLib2Text)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DalekRows
  (c2_blackBox_hGhostNoExtNe c2_staticSecretDrop_hGhostNoExtNe)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DurCst16
  (durationSince_hRo_of_f3CodeInv)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8
  (c2_fromUtf8Block_placeable_unrelaxed c2_fromUtf8_hRo_of_f3CodeInv)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8Row
  (c2_fromUtf8_hCL c2_fromUtf8_hGhostAt c2_fromUtf8_hGhostNoExtNe_of_linkedAt
   c2_fromUtf8_hRealHullNoExt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcRows
  (bcmp_mem_c2RxDehookedSyms c2_bcmp_hGhostNoExtNe_of_linkedAt
   c2_strlen_hGhostNoExtNe_of_linkedAt keepR_bcmp_sub_keepTextBPre
   keepR_strlen_sub_keepTextBPre strlen_mem_c2RxDehookedSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MemmoveRow
  (c2_memmove_hGhostEntry c2_memmove_hGhostOffEntries_of_linkedAt
   c2_memmove_hMemcpyTrap c2_memmove_hMemmoveExt c2_memmove_hMemmoveOff
   c2_memmove_hMemsetTrap c2_memmove_hRealHullNoExt keepR_memmove_sub_keepTextBPre)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MemrchrRow
  (c2_memrchr_hKeep keepR_memrchr_noPanic keepR_memrchr_sub_keepLib2Text)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_ghostAt_of_extraLookup c2_realHullNoExt_of_keepLib2Text
   c2_realHullNoExt_of_keepTextBPre)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
  (c2ExternTableFacts_lsmpl c2Lib2RxSliceFacts_lsmpl c2ResolveFacts_lsmpl c2RoSliceFacts)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time
  (c2TimeMpl c2TimeMpl_hb1 c2TimeMpl_hRho c2TimeMpl_placeable c2_durationSince_hKeep
   c2_durationSince_hRealHullNoExt c2_timeAdd_hTargetEq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
  (c2TimeMpl_expectFailedStubPc_eq_cliElf_rho c2_timeAdd_hKeep c2_timeAdd_hPanReal
   c2_timeAdd_hRealHullNoExt c2_timeAdd_hlr_ne_stub)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode
  (durationSinceHullProg durationSinceHullProg_externAt_none
   durationSinceHullProg_hasWords_durationSince durationSinceHullProg_hasWords_subTimespec
   durationSinceHullProg_svc durationSincePatchedWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhost
  (durationSinceGhostFnLs subTimespecByteLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostLs
  (f3EmptyDurationSinceGhostHookLs f3EmptyDurationSinceGhostHookLs_visitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostReplays
  (durationSinceGhost durationSinceSubProg durationSinceSubProg_codeLoaded_stripExecOutside
   keepR_durationSince)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Ghost
  (emptyFromUtf8GhostHook fromUtf8GhostHook_visitedIn
   keepCoversFromUtf8_keepFromUtf8Block keepFromUtf8Block)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays
  (fromUtf8EntryGuard fromUtf8MplGhost fromUtf8MplPlacement fromUtf8MplPlacement_base
   fromUtf8SubProg fromUtf8SubProg_codeLoaded_stripExecOutside fromUtf8SubProg_externAt_none
   fromUtf8SubProg_hasWords fromUtf8SubProg_svc keepR_fromUtf8 keepR_fromUtf8Mpl
   keepR_fromUtf8_mplPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8LrTrap
  (emptyFromUtf8GhostHook_keepLr_false_after_hook_of_outcome_post)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode
  (bPreMemmoveByteOff bPrePadWord)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays
  (keepR_memmove memcpyEntry memmoveEntryGuard memmoveGhost memmoveSubProg
   memmoveSubProg_codeLoaded_stripExecOutside memmoveSubProg_externAt_none
   memmoveSubProg_hasWords memmoveSubProg_svc resolve_memcpy_eq_memcpyEntry)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostReplays
  (f3EmptyMemmoveGhostHook_visitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrap
  (bPreHull_keepLr_false_after_hook_of_codeLoaded_u bPreHull_reg_ext_forall_of_entries)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrapBase
  (trapHook_f3EmptyMemmoveGhostHook)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrExtraReplays
  (keepR_memrchr memrchrGhost memrchrSubProg memrchrSubProg_codeLoaded_stripExecOutside
   memrchrSubProg_externAt_none memrchrSubProg_hasWords memrchrSubProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostReplaysOn
  (f3EmptyMemrchrGhostHookLs_visitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (emptyStdProg emptyStdProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
  (f3EmptyMemcpyGhostHookNarrow f3EmptyMemsetGhostHookNarrow)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays
  (keepR_staticSecretDrop staticSecretDropEntryGuard staticSecretDropGhost
   staticSecretDropSubProg staticSecretDropSubProg_codeLoaded_stripExecOutside
   staticSecretDropSubProg_externAt_none staticSecretDropSubProg_hasWords
   staticSecretDropSubProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost
  (keepCoversStrlen_keepStrlenRange)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostK
  (f3EmptyStrlenGhostHook_visitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays
  (keepR_strlen strlenEntry strlenEntryGuard strlenGhost strlenSubProg
   strlenSubProg_codeLoaded_stripExecOutside strlenSubProg_externAt_none
   strlenSubProg_hasWords strlenSubProg_svc strlenEntry_no_wrap_of_codeLoaded)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenLrTrap
  (f3EmptyStrlenGhostHook_keepLr_false_after_hook_of_codeLoaded_u)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays
  (keepR_timeAdd keepR_timeAdd_entry timeAddGhost timeAddPanicExterns
   timeAddPanicExterns_expectFailed timeAddSubProg timeAddSubProg_codeLoaded_stripExecOutside)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhost
  (timeAddExpectFailedStubPc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhostK
  (timeAddGhostHookExternOnlyLsRet_replaysOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost
  (f3EmptyZeroizeGhostHook_visitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap
  (f3EmptyStaticSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore
  (c2S5Addrs externAt?_s5TrapExt_eq_of_keep_all_false externAt?_s5TrapExt_eq_of_not_mem
   not_mem_s5_of_keepTextBPre not_mem_s5_of_not_mem_c2S5Addrs realProg617_svc_eq s5TrapExt
   s5TrapProg_svc setPC_eq_self_of_pc_eq stepsStrictAvoid_of_s5Trap
   stepsStrictAvoid_of_visitedIn_noExtern stepsStrictAvoid_s5_of_visitedIn_all_false)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FromUtf8TableAddr c2RxDehookedSyms)

/-! ## 1. `.text.b_pre` Closed-`.lr` Rows: `"memmove"`, `"bcmp"`, `"strlen"` -/

theorem memmove_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hGMemcpy : ghFixed.memcpy = none ∨ ghFixed.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : ghFixed.memset = none ∨ ghFixed.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hLook : extra.lookup "memmove" = some (memmoveGhost lsmpl mmpl))
    (W : CliHooks) {s0 sf u : State}
    (hEntry : memmoveEntryGuard lsmpl s0)
    (hRetPc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hNoExSf : ∀ msg, sf.status ≠ .Exception msg)
    (hNotHaltSf : sf.status ≠ .Halted)
    (hStepsAfter :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        (memmoveGhost lsmpl mmpl u) sf)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl "memmove")
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (memmoveGhost lsmpl mmpl u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (memmoveGhost lsmpl mmpl u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (memmoveGhost lsmpl mmpl u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := c2ResolveFacts_lsmpl hLs
  have hRx := c2Lib2RxSliceFacts_lsmpl hLs
  let EG := fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')
  have hCodeU : (memmoveSubProg lsmpl).CodeLoaded u.mem :=
    codeLoaded_of_checkProgCodeSubslice hinv.rxCode hRx.memmove
  have hMemmoveOff := c2_memmove_hMemmoveOff hLs hRes.memmove_eq
  have hMemmoveExt := c2_memmove_hMemmoveExt ghFixed extra hLook
  have hRegExt :=
    bPreHull_reg_ext_forall_of_entries
      (m := memcpyEntry lsmpl)
      (P_ghost := cliProgExtPlacedAt lsmpl EG 617 W)
      (resolve := libsignalSessionLib.resolve lsmpl)
      (extOf := EG W)
      (fun hkp hnotin => c2_memmove_hGhostOffEntries_of_linkedAt EG hLs hExt W hkp hnotin)
      (fun hsym => c2_memmove_hGhostEntry hExt EG W hsym)
      (fun f hf _ hL => by
        dsimp only [EG] at hf
        rcases hMemmoveExt W with hn | hs
        · rw [hn] at hf; cases hf
        · rw [hs] at hf; cases hf
          exact trapHook_f3EmptyMemmoveGhostHook (memmoveSubProg lsmpl)
            (memcpyEntry lsmpl + bPreMemmoveByteOff) hL)
      (c2_memmove_hMemcpyTrap ghFixed extra hGMemcpy hLs hExt W)
      (c2_memmove_hMemsetTrap ghFixed extra hGMemset hLs hExt W)
  have hLrOut : keepR_memmove lsmpl (u.readReg64 .lr) = false :=
    bPreHull_keepLr_false_after_hook_of_codeLoaded_u
      (memmoveSubProg_hasWords lsmpl)
      (resolve_memcpy_eq_memcpyEntry lsmpl)
      hRegExt
      (fun _ hL => trapHook_f3EmptyMemmoveGhostHook (memmoveSubProg lsmpl)
        (memcpyEntry lsmpl + bPreMemmoveByteOff) hL)
      hEntry.1 hRetPc hNoExSf hNotHaltSf u hStepsAfter hrun hCodeU hkf
  obtain ⟨_, _, _, _, hvis⟩ :=
    f3EmptyMemmoveGhostHook_visitedIn
      (keepR := keepR_memmove lsmpl)
      (P_sub := memmoveSubProg lsmpl)
      (m := memcpyEntry lsmpl)
      (resolve := libsignalSessionLib.resolve lsmpl)
      (padWord := bPrePadWord)
      (memmoveSubProg_svc lsmpl)
      (memmoveSubProg_externAt_none lsmpl)
      (memmoveSubProg_hasWords lsmpl)
      (resolve_memcpy_eq_memcpyEntry lsmpl)
      hrun hnoex hfr hLrOut
      (memmoveSubProg_codeLoaded_stripExecOutside hCodeU)
  rw [setPC_eq_self_of_pc_eq (hpc.trans hMemmoveOff)] at hvis
  exact stepsStrictAvoid_of_visitedIn_noExtern
    (emptyStdProg_svc.trans (realProg617_svc_eq lsmpl mmpl W).symm)
    (fun _ _ => rfl)
    (fun _ hk => c2_memmove_hRealHullNoExt hLs hExt W hk)
    (fun _ hk => not_mem_s5_of_keepTextBPre hLs (keepR_memmove_sub_keepTextBPre hLs hk))
    hvis

theorem bcmp_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hLook : extra.lookup "bcmp" = some (bcmpGhost lsmpl mmpl))
    (W : CliHooks) {s0 sf u : State}
    (hEntry : bcmpEntryGuard lsmpl s0)
    (hRetPc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hNoExSf : ∀ msg, sf.status ≠ .Exception msg)
    (hNotHaltSf : sf.status ≠ .Halted)
    (hStepsAfter :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        (bcmpGhost lsmpl mmpl u) sf)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl "bcmp")
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (bcmpGhost lsmpl mmpl u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (bcmpGhost lsmpl mmpl u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (bcmpGhost lsmpl mmpl u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := c2ResolveFacts_lsmpl hLs
  have hRx := c2Lib2RxSliceFacts_lsmpl hLs
  let EG := fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')
  have hCodeU : (bcmpSubProg lsmpl).CodeLoaded u.mem :=
    codeLoaded_of_checkProgCodeSubslice hinv.rxCode hRx.bcmp
  have hGhostAt :=
    c2_ghostAt_of_extraLookup (mmpl := mmpl) hExt ghFixed extra bcmp_mem_c2RxDehookedSyms
      (by decide +kernel) hLook (by decide) W
  have hGhostNoExtNe := c2_bcmp_hGhostNoExtNe_of_linkedAt EG hLs hExt hRes.bcmp_eq
  have hLrOut : keepR_bcmp lsmpl (u.readReg64 .lr) = false :=
    f3EmptyBcmpGhostHook_keepLr_false_after_hook_of_codeLoaded_u
      (P_ghost := cliProgExtPlacedAt lsmpl EG 617 W)
      (P_sub := bcmpSubProg lsmpl)
      (keepR := keepR_bcmp lsmpl)
      (m := bcmpHullBase lsmpl)
      (stubPc := libsignalSessionLib.resolve lsmpl "bcmp")
      (entryTarget := bcmpHullBase lsmpl + memcmpByteLen)
      rfl
      (bcmpSubProg_hasWords lsmpl)
      (fun _ h => h)
      (fun _ hk hne => hGhostNoExtNe W hk hne)
      hGhostAt
      hEntry.1 hRetPc hNoExSf hNotHaltSf u hCodeU hStepsAfter hrun hkf
  obtain ⟨_, _, _, _, hvis⟩ :=
    f3EmptyBcmpGhostHook_visitedIn
      (keepR := keepR_bcmp lsmpl)
      (P_sub := bcmpSubProg lsmpl)
      (m := bcmpHullBase lsmpl)
      (bcmpSubProg_svc lsmpl)
      (bcmpSubProg_externAt_none lsmpl)
      (bcmpSubProg_hasWords lsmpl)
      rfl hrun hnoex hfr hLrOut
      (bcmpSubProg_codeLoaded_stripExecOutside hCodeU)
  have hOff : bcmpHullBase lsmpl + memcmpByteLen = libsignalSessionLib.resolve lsmpl "bcmp" := by
    unfold bcmpHullBase; bv_omega
  rw [setPC_eq_self_of_pc_eq (hpc.trans hOff.symm)] at hvis
  exact stepsStrictAvoid_of_visitedIn_noExtern
    (emptyStdProg_svc.trans (realProg617_svc_eq lsmpl mmpl W).symm)
    (fun _ _ => rfl)
    (fun _ hk => c2_realHullNoExt_of_keepTextBPre hExt (keepR_bcmp_sub_keepTextBPre hRes.bcmp_eq) W hk)
    (fun pc hk => not_mem_s5_of_keepTextBPre hLs (keepR_bcmp_sub_keepTextBPre hRes.bcmp_eq pc hk))
    hvis

theorem strlen_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hLook : extra.lookup "strlen" = some (strlenGhost lsmpl mmpl))
    (W : CliHooks) {s0 sf u : State}
    (hEntry : strlenEntryGuard lsmpl s0)
    (hRetPc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hNoExSf : ∀ msg, sf.status ≠ .Exception msg)
    (hNotHaltSf : sf.status ≠ .Halted)
    (hStepsAfter :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        (strlenGhost lsmpl mmpl u) sf)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl "strlen")
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (strlenGhost lsmpl mmpl u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (strlenGhost lsmpl mmpl u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (strlenGhost lsmpl mmpl u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := c2ResolveFacts_lsmpl hLs
  have hRx := c2Lib2RxSliceFacts_lsmpl hLs
  let EG := fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')
  have hCodeU : (strlenSubProg lsmpl).CodeLoaded u.mem :=
    codeLoaded_of_checkProgCodeSubslice hinv.rxCode hRx.strlen
  have hGhostAt :=
    c2_ghostAt_of_extraLookup (mmpl := mmpl) hExt ghFixed extra strlen_mem_c2RxDehookedSyms
      (by decide +kernel) hLook (by decide) W
  have hGhostNoExtNe := c2_strlen_hGhostNoExtNe_of_linkedAt EG hLs hExt hRes.strlen_eq
  have hLrOut : keepR_strlen lsmpl (u.readReg64 .lr) = false :=
    f3EmptyStrlenGhostHook_keepLr_false_after_hook_of_codeLoaded_u
      (P_ghost := cliProgExtPlacedAt lsmpl EG 617 W)
      (P_sub := strlenSubProg lsmpl)
      (keepR := keepR_strlen lsmpl)
      (entryTarget := strlenEntry lsmpl)
      (strlenSubProg_hasWords lsmpl)
      (keepCoversStrlen_keepStrlenRange (strlenEntry lsmpl))
      (fun _ hk hne => hGhostNoExtNe W hk hne)
      (Or.inr hGhostAt)
      hEntry.1 hRetPc hNoExSf hNotHaltSf u hCodeU hStepsAfter hrun hkf
  obtain ⟨hvis, _, _, _⟩ :=
    f3EmptyStrlenGhostHook_visitedIn
      (keep := keepR_strlen lsmpl)
      (P_sub := strlenSubProg lsmpl)
      (entryTarget := strlenEntry lsmpl)
      (strlenSubProg_svc lsmpl)
      (strlenSubProg_externAt_none lsmpl)
      (strlenSubProg_hasWords lsmpl)
      (strlenEntry_no_wrap_of_codeLoaded hCodeU)
      hrun hnoex hfr hLrOut
      (strlenSubProg_codeLoaded_stripExecOutside hCodeU)
  have hpc_s : u.pc = strlenEntry lsmpl := hpc
  rw [setPC_eq_self_of_pc_eq hpc_s] at hvis
  exact stepsStrictAvoid_of_visitedIn_noExtern
    (emptyStdProg_svc.trans (realProg617_svc_eq lsmpl mmpl W).symm)
    (fun _ _ => rfl)
    (fun _ hk => c2_realHullNoExt_of_keepTextBPre hExt (keepR_strlen_sub_keepTextBPre hRes.strlen_eq) W hk)
    (fun pc hk => not_mem_s5_of_keepTextBPre hLs (keepR_strlen_sub_keepTextBPre hRes.strlen_eq pc hk))
    hvis

/-! ## 2. `.text.lib2` Standard-Library Rows (`memrchr`, `from_utf8`, `duration_since`, `time_add`) -/

theorem memrchr_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsMemrchrSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (memrchrGhost lsmpl mmpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (memrchrGhost lsmpl mmpl u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := c2ResolveFacts_lsmpl hLs
  have hRx := c2Lib2RxSliceFacts_lsmpl hLs
  have hCodeU : (memrchrSubProg lsmpl).CodeLoaded u.mem :=
    codeLoaded_of_checkProgCodeSubslice hinv.rxCode hRx.memrchr
  obtain ⟨_, _, _, _, hvis⟩ :=
    f3EmptyMemrchrGhostHookLs_visitedIn
      (keepR := keepR_memrchr lsmpl)
      (P_sub := memrchrSubProg lsmpl)
      (entryTarget := libsignalSessionLib.resolve lsmpl lsMemrchrSym)
      (memrchrSubProg_svc lsmpl)
      (memrchrSubProg_externAt_none lsmpl)
      (memrchrSubProg_hasWords lsmpl)
      (c2_memrchr_hKeep hRes.memrchr_eq hLs)
      hrun hnoex hfr
      (memrchrSubProg_codeLoaded_stripExecOutside hCodeU)
  rw [setPC_eq_self_of_pc_eq hpc] at hvis
  have hall : (c2S5Addrs.all fun p => !(keepR_memrchr lsmpl p)) = true := by
    unfold keepR_memrchr
    rw [hRes.memrchr_eq]
    decide
  exact stepsStrictAvoid_s5_of_visitedIn_all_false
    hLs emptyStdProg_svc
    (fun _ _ => rfl)
    (fun _ hk => c2_realHullNoExt_of_keepLib2Text hExt (keepR_memrchr_sub_keepLib2Text hRes.memrchr_eq)
      (keepR_memrchr_noPanic hRes.memrchr_eq) W hk)
    hall hvis

theorem fromUtf8_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hLook : extra.lookup lsFromUtf8Sym =
      some (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr))
    (W : CliHooks) {s0 sf u : State}
    (hEntry : fromUtf8EntryGuard lsmpl s0)
    (hRetPc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hNoExSf : ∀ msg, sf.status ≠ .Exception msg)
    (hNotHaltSf : sf.status ≠ .Halted)
    (hStepsAfter :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        ((fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr : State → State) u) sf)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsFromUtf8Sym)
    (hrun : u.status = .Running)
    (hnoex :
      ∀ msg, ((fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr : State → State) u).status ≠
        .Exception msg)
    (hkf :
      u.mem.KeepsFrozen ((fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr : State → State) u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u ((fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr : State → State) u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := c2ResolveFacts_lsmpl hLs
  have hRx := c2Lib2RxSliceFacts_lsmpl hLs
  let EG := fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')
  let pl := fromUtf8MplPlacement lsmpl c2FromUtf8TableAddr
  have hpl := c2_fromUtf8Block_placeable_unrelaxed hLs hRes.fromUtf8_eq
  have hCodeU : (fromUtf8SubProg pl).CodeLoaded u.mem :=
    c2_fromUtf8_hCL hRx.fromUtf8 hRes.fromUtf8_eq (fun _ h => h) u hinv
  have hRo := c2_fromUtf8_hRo_of_f3CodeInv c2RoSliceFacts hLs (fun _ h => h) u hfr hinv
  have hGhostBase :
      (cliProgExtPlacedAt lsmpl EG 617 W).externAt? pl.base =
        some (emptyFromUtf8GhostHook (keepR_fromUtf8 pl) pl) := by
    rw [fromUtf8MplPlacement_base]
    exact c2_fromUtf8_hGhostAt (mmpl := mmpl) ghFixed extra hExt hLook W
  have hGhostNoExtNe := c2_fromUtf8_hGhostNoExtNe_of_linkedAt EG hLs hExt hRes.fromUtf8_eq
  have hKeepEq : keepR_fromUtf8 pl = keepR_fromUtf8Mpl lsmpl :=
    keepR_fromUtf8_mplPlacement lsmpl c2FromUtf8TableAddr
  have hBaseEq : pl.base = libsignalSessionLib.resolve lsmpl lsFromUtf8Sym :=
    fromUtf8MplPlacement_base lsmpl c2FromUtf8TableAddr
  have hLrOut : keepR_fromUtf8 pl (u.readReg64 .lr) = false :=
    emptyFromUtf8GhostHook_keepLr_false_after_hook_of_outcome_post
      (P_ghost := cliProgExtPlacedAt lsmpl EG 617 W)
      (keepR := keepR_fromUtf8 pl)
      (pl := pl)
      (keepCoversFromUtf8_keepFromUtf8Block pl.base)
      (fun _ hk hne => hGhostNoExtNe W (hKeepEq ▸ hk) (hBaseEq ▸ hne))
      (Or.inr hGhostBase)
      (by rw [hBaseEq]; exact hEntry.1) hRetPc hNoExSf hNotHaltSf u hStepsAfter hrun
      (hCodeU.of_keepsFrozen hkf)
  obtain ⟨hvis, _⟩ :=
    fromUtf8GhostHook_visitedIn
      (keep := keepR_fromUtf8 pl)
      (P_run := emptyStdProg)
      (P_sub := fromUtf8SubProg pl)
      (pl := pl)
      hpl
      emptyStdProg_svc
      (fromUtf8SubProg_svc pl)
      (fun _ _ => rfl)
      (fromUtf8SubProg_externAt_none pl)
      (fromUtf8SubProg_hasWords pl)
      hRo hnoex hfr hLrOut
      (fromUtf8SubProg_codeLoaded_stripExecOutside hCodeU)
  have hpc_pl : u.pc = pl.base := hpc.trans hBaseEq.symm
  rw [setPC_eq_self_of_pc_eq hpc_pl] at hvis
  have hall : (c2S5Addrs.all fun p => !(keepR_fromUtf8 pl p)) = true := by
    rw [hKeepEq]
    dsimp only [keepR_fromUtf8Mpl]
    rw [hRes.fromUtf8_eq]
    decide
  exact stepsStrictAvoid_s5_of_visitedIn_all_false
    hLs emptyStdProg_svc
    (fun _ _ => rfl)
    (fun _ hk => c2_fromUtf8_hRealHullNoExt hLs hExt hRes.fromUtf8_eq W (hKeepEq ▸ hk))
    hall hvis

theorem durationSince_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsDurationSinceSym)
    (hnoex : ∀ msg, (durationSinceGhost c2TimeMpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (durationSinceGhost c2TimeMpl u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := c2ResolveFacts_lsmpl hLs
  have hRx := c2Lib2RxSliceFacts_lsmpl hLs
  have hCodeU : (durationSinceSubProg c2TimeMpl).CodeLoaded u.mem :=
    codeLoaded_of_checkProgCodeSubslice hinv.rxCode hRx.durationSince
  have hRo : RoDataAt u.mem (c2TimeMpl.ρ timeRodataCst16Sym) timePlacedData0 :=
    durationSince_hRo_of_f3CodeInv c2RoSliceFacts hLs c2TimeMpl_hRho (fun _ h => h) u hinv
  have hEqGhost :
      f3EmptyDurationSinceGhostHookLs (c2TimeMpl.ρ timeRodataCst16Sym)
        (keepR_durationSince c2TimeMpl) (durationSinceHullProg c2TimeMpl)
        (c2TimeMpl.base 1) u =
      durationSinceGhost c2TimeMpl u := by
    change durationSinceGhostFnLs (c2TimeMpl.ρ timeRodataCst16Sym)
        (keepR_durationSince c2TimeMpl) emptyStdProg (durationSinceHullProg c2TimeMpl)
        (c2TimeMpl.base 1) u =
      durationSinceGhostFnLs (c2TimeMpl.ρ timeRodataCst16Sym)
        (keepR_durationSince c2TimeMpl) emptyStdProg (durationSinceHullProg c2TimeMpl)
        (c2TimeMpl.base 0 + subTimespecByteLen) u
    rw [c2TimeMpl_hb1]
  have hnoex1 :
      ∀ msg,
        (f3EmptyDurationSinceGhostHookLs (c2TimeMpl.ρ timeRodataCst16Sym)
          (keepR_durationSince c2TimeMpl) (durationSinceHullProg c2TimeMpl)
          (c2TimeMpl.base 1) u).status ≠ .Exception msg := by
    rw [hEqGhost]; exact hnoex
  have hw1 : (durationSinceHullProg c2TimeMpl).hasWords (c2TimeMpl.base 1)
      (durationSincePatchedWords c2TimeMpl) := by
    rw [c2TimeMpl_hb1]
    exact durationSinceHullProg_hasWords_durationSince c2TimeMpl
  obtain ⟨_, _, _, _, hvis⟩ :=
    f3EmptyDurationSinceGhostHookLs_visitedIn
      c2TimeMpl_placeable
      (durationSinceHullProg_svc c2TimeMpl)
      (durationSinceHullProg_externAt_none c2TimeMpl)
      (durationSinceHullProg_hasWords_subTimespec c2TimeMpl)
      hw1
      (c2_durationSince_hKeep hLs)
      hRo
      hnoex1
      hfr
      (durationSinceSubProg_codeLoaded_stripExecOutside hCodeU)
  rw [hEqGhost] at hvis
  have hpc1 : u.pc = c2TimeMpl.base 1 := hpc.trans hRes.durationSince_eq
  rw [setPC_eq_self_of_pc_eq hpc1] at hvis
  have hall : (c2S5Addrs.all fun p => !(keepR_durationSince c2TimeMpl p)) = true := by decide
  exact stepsStrictAvoid_s5_of_visitedIn_all_false
    hLs emptyStdProg_svc
    (fun _ _ => rfl)
    (fun _ hk => c2_durationSince_hRealHullNoExt hExt W hk)
    hall hvis

theorem timeAdd_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (W : CliHooks) {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsTimeAddSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (timeAddGhost c2TimeMpl u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (timeAddGhost c2TimeMpl u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := c2ResolveFacts_lsmpl hLs
  have hRx := c2Lib2RxSliceFacts_lsmpl hLs
  let P_trap := cliProgExtPlacedAt lsmpl (s5TrapExt mmpl) 617 W
  have hall : (c2S5Addrs.all fun p => !(keepR_timeAdd c2TimeMpl p)) = true := by decide
  have hTrapHullNoExt : ∀ pc, keepR_timeAdd c2TimeMpl pc = true → P_trap.externAt? pc = none := by
    intro pc hk
    rw [externAt?_s5TrapExt_eq_of_keep_all_false hLs W hall hk]
    exact c2_timeAdd_hRealHullNoExt hExt W hk
  have hn_pan : timeAddExpectFailedStubPc c2TimeMpl ∉ c2S5Addrs := by
    rw [c2TimeMpl_expectFailedStubPc_eq_cliElf_rho]
    decide +kernel
  have hTrapPan : P_trap.externAt? (timeAddExpectFailedStubPc c2TimeMpl) = some Rust.panicked := by
    rw [externAt?_s5TrapExt_eq_of_not_mem W (not_mem_s5_of_not_mem_c2S5Addrs hLs hn_pan)]
    exact c2_timeAdd_hPanReal mmpl hLs W
  have hTargetEq : libsignalSessionLib.resolve lsmpl lsTimeAddSym =
      timeMultiLib.fnAddr c2TimeMpl timeAddSym :=
    c2_timeAdd_hTargetEq hRes.timeAdd_eq
  have hTrapStubNone : P_trap.externAt? (libsignalSessionLib.resolve lsmpl lsTimeAddSym) = none := by
    rw [hTargetEq]
    exact hTrapHullNoExt _ (keepR_timeAdd_entry c2TimeMpl)
  have hRep :=
    timeAddGhostHookExternOnlyLsRet_replaysOn
      (InvMem := fun m => (timeAddSubProg c2TimeMpl).CodeLoaded m)
      (keep := keepR_timeAdd c2TimeMpl)
      (P_real := P_trap)
      (stubPc := libsignalSessionLib.resolve lsmpl lsTimeAddSym)
      (timeMpl := c2TimeMpl)
      (externs := timeAddPanicExterns)
      c2TimeMpl_placeable
      (s5TrapProg_svc lsmpl mmpl W)
      hTrapHullNoExt
      timeAddPanicExterns_expectFailed
      hTrapPan
      (c2_timeAdd_hKeep hLs)
      (c2_timeAdd_hlr_ne_stub hLs)
      hTrapStubNone
      (fun u' hpc' _ _ _ => by
        rw [setPC_eq_self_of_pc_eq (hpc'.trans hTargetEq)]
        exact Steps.refl _)
      (fun _ _ hInvM => timeAddSubProg_codeLoaded_stripExecOutside hInvM)
      (fun _ _ hInvM hkf => hInvM.of_keepsFrozen hkf)
  have hCodeU : (timeAddSubProg c2TimeMpl).CodeLoaded u.mem :=
    codeLoaded_of_checkProgCodeSubslice hinv.rxCode hRx.timeAdd
  obtain ⟨hSteps, _, _, _⟩ := hRep.2 u hpc hrun hnoex hfr hCodeU
  exact stepsStrictAvoid_of_s5Trap hExt W hSteps hnoex

/-! ## 3. `.text.lib2` Closed-`.lr` Dalek Leaf Rows (`black_box`, `StaticSecret::drop`) -/

set_option maxRecDepth 400000 in
private theorem lsBlackBoxSym_mem_c2RxDehookedSyms :
    lsBlackBoxSym ∈ c2RxDehookedSyms := by
  decide

theorem blackBox_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hLook : extra.lookup lsBlackBoxSym = some (blackBoxGhost lsmpl mmpl))
    (W : CliHooks) {s0 sf u : State}
    (hEntry : blackBoxEntryGuard lsmpl s0)
    (hRetPc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hNoExSf : ∀ msg, sf.status ≠ .Exception msg)
    (hNotHaltSf : sf.status ≠ .Halted)
    (hStepsAfter :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        (blackBoxGhost lsmpl mmpl u) sf)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsBlackBoxSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (blackBoxGhost lsmpl mmpl u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (blackBoxGhost lsmpl mmpl u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (blackBoxGhost lsmpl mmpl u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := c2ResolveFacts_lsmpl hLs
  have hRx := c2Lib2RxSliceFacts_lsmpl hLs
  let EG := fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')
  have hCodeU : (blackBoxSubProg lsmpl).CodeLoaded u.mem :=
    codeLoaded_of_checkProgCodeSubslice hinv.rxCode hRx.blackBox
  have hGhostAt :=
    c2_ghostAt_of_extraLookup (mmpl := mmpl) hExt ghFixed extra lsBlackBoxSym_mem_c2RxDehookedSyms
      (by decide) hLook (by decide) W
  have hGhostNoExtNe := c2_blackBox_hGhostNoExtNe hExt hRes.blackBox_eq hLs EG
  have hLrOut : keepR_blackBox lsmpl (u.readReg64 .lr) = false :=
    f3EmptyBlackBoxGhostHook_keepLr_false_after_hook_of_codeLoaded_u
      (P_ghost := cliProgExtPlacedAt lsmpl EG 617 W)
      (P_sub := blackBoxSubProg lsmpl)
      (keepR := keepR_blackBox lsmpl)
      (entry := libsignalSessionLib.resolve lsmpl lsBlackBoxSym)
      (stubPc := libsignalSessionLib.resolve lsmpl lsBlackBoxSym)
      (entryTarget := libsignalSessionLib.resolve lsmpl lsBlackBoxSym)
      (blackBoxSubProg_hasWords lsmpl)
      (fun _ h => h)
      (fun _ hk hne => hGhostNoExtNe W hk hne)
      hGhostAt
      hEntry.1 hRetPc hNoExSf hNotHaltSf u hCodeU hStepsAfter hrun hkf
  obtain ⟨hvis, _, _⟩ :=
    f3EmptyBlackBoxGhostHook_visitedIn
      (keep := keepR_blackBox lsmpl)
      (P_sub := blackBoxSubProg lsmpl)
      (entryTarget := libsignalSessionLib.resolve lsmpl lsBlackBoxSym)
      (blackBoxSubProg_svc lsmpl)
      (blackBoxSubProg_externAt_none lsmpl)
      (blackBoxSubProg_hasWords lsmpl)
      hrun hnoex hfr hLrOut
      (blackBoxSubProg_codeLoaded_stripExecOutside hCodeU)
  rw [setPC_eq_self_of_pc_eq hpc] at hvis
  have hall : (c2S5Addrs.all fun p => !(keepR_blackBox lsmpl p)) = true := by
    unfold keepR_blackBox
    rw [hRes.blackBox_eq]
    decide
  exact stepsStrictAvoid_s5_of_visitedIn_all_false
    hLs emptyStdProg_svc
    (fun _ _ => rfl)
    (fun _ hk => c2_realHullNoExt_of_keepLib2Text hExt (keepR_blackBox_sub_keepLib2Text hRes.blackBox_eq)
      (keepR_blackBox_noPanic hRes.blackBox_eq) W hk)
    hall hvis

set_option maxRecDepth 400000 in
private theorem lsStaticSecretDropSym_mem_c2RxDehookedSyms :
    lsStaticSecretDropSym ∈ c2RxDehookedSyms := by
  decide

theorem staticSecretDrop_avoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hLook : extra.lookup lsStaticSecretDropSym = some (staticSecretDropGhost lsmpl mmpl))
    (W : CliHooks) {s0 sf u : State}
    (hEntry : staticSecretDropEntryGuard lsmpl s0)
    (hRetPc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hNoExSf : ∀ msg, sf.status ≠ .Exception msg)
    (hNotHaltSf : sf.status ≠ .Halted)
    (hStepsAfter :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        (staticSecretDropGhost lsmpl mmpl u) sf)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl lsStaticSecretDropSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (staticSecretDropGhost lsmpl mmpl u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (staticSecretDropGhost lsmpl mmpl u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (staticSecretDropGhost lsmpl mmpl u) := by
  have hExt := c2ExternTableFacts_lsmpl hLs
  have hRes := c2ResolveFacts_lsmpl hLs
  have hRx := c2Lib2RxSliceFacts_lsmpl hLs
  let EG := fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')
  have hCodeU : (staticSecretDropSubProg lsmpl).CodeLoaded u.mem :=
    codeLoaded_of_checkProgCodeSubslice hinv.rxCode hRx.staticSecretDrop
  have hGhostAt :=
    c2_ghostAt_of_extraLookup (mmpl := mmpl) hExt ghFixed extra
      lsStaticSecretDropSym_mem_c2RxDehookedSyms (by decide) hLook (by decide) W
  have hGhostNoExtNe := c2_staticSecretDrop_hGhostNoExtNe hExt hRes.staticSecretDrop_eq hLs EG
  have hLrOut : keepR_staticSecretDrop lsmpl (u.readReg64 .lr) = false :=
    f3EmptyStaticSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u
      (P_ghost := cliProgExtPlacedAt lsmpl EG 617 W)
      (P_sub := staticSecretDropSubProg lsmpl)
      (keepR := keepR_staticSecretDrop lsmpl)
      (entry := libsignalSessionLib.resolve lsmpl lsStaticSecretDropSym)
      (stubPc := libsignalSessionLib.resolve lsmpl lsStaticSecretDropSym)
      (entryTarget := libsignalSessionLib.resolve lsmpl lsStaticSecretDropSym)
      (staticSecretDropSubProg_hasWords lsmpl)
      (fun _ h => h)
      (fun _ hk hne => hGhostNoExtNe W hk hne)
      hGhostAt
      hEntry.1 hRetPc hNoExSf hNotHaltSf u hCodeU hStepsAfter hrun hkf
  obtain ⟨hvis, _, _⟩ :=
    f3EmptyZeroizeGhostHook_visitedIn
      (keep := keepR_staticSecretDrop lsmpl)
      (P_sub := staticSecretDropSubProg lsmpl)
      (entryTarget := libsignalSessionLib.resolve lsmpl lsStaticSecretDropSym)
      (staticSecretDropSubProg_svc lsmpl)
      (staticSecretDropSubProg_externAt_none lsmpl)
      (staticSecretDropSubProg_hasWords lsmpl)
      hrun hnoex hfr hLrOut
      (staticSecretDropSubProg_codeLoaded_stripExecOutside hCodeU)
  rw [setPC_eq_self_of_pc_eq hpc] at hvis
  have hall : (c2S5Addrs.all fun p => !(keepR_staticSecretDrop lsmpl p)) = true := by
    unfold keepR_staticSecretDrop
    rw [hRes.staticSecretDrop_eq]
    decide
  exact stepsStrictAvoid_s5_of_visitedIn_all_false
    hLs emptyStdProg_svc
    (fun _ _ => rfl)
    (fun _ hk =>
      c2_realHullNoExt_of_keepLib2Text hExt
        (keepR_staticSecretDrop_sub_keepLib2Text hRes.staticSecretDrop_eq)
        (keepR_staticSecretDrop_noPanic hRes.staticSecretDrop_eq) W hk)
    hall hvis

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightRows

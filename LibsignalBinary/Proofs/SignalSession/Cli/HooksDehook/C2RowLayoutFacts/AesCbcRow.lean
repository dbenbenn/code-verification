/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl4
import ProofLib.Process.FastParse
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `GhostRowOk` and `HookOk` Discharge for AES-256-CBC

Assembles `c2_aesEncGhost_hookOk`, `c2_aesDecGhost_hookOk`, `c2_aesDecGhost_weakHookOk`,
`c2_aesEncGhost_rowOk[_of_inv, _lsmpl_and_fs, _guardOf]`, and
`c2_aesDecGhost_rowOk[_of_inv, _lsmpl_and_fs, _guardOf]` for `lsAesEncSym` and `lsAesDecSym`
over `.text.lib2`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbcRow

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.SepLogic
  ProofLib.StdStartup
open VerifiedLibraries (mallocngLib)
open CryptoVerification (LibsignalPlacement libsignalHookedExterns libsignalSessionExterns lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced cliPanicSymbolsLinked isCliPanicSymbolPlaced
   libsignalSessionLib lsAesDecSym lsAesEncSym patchElfByte patchRegionByte)
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Heap.Fine (f3RxWordCount f3StdLayout)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays
  (aesDecGhost aesDecGhost_ok aesDecGhost_rowOk aesDecGhost_weak_ok aesDecSpecOf aesDecWeakSpecOf
   aesEncGhost aesEncGhost_ok aesEncGhost_rowOk aesEncSpecOf c2AesRconAddr stubFrozenGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (aesCbcSubProg aesCbcSubProg_codeLoaded_iff aesCbcSubProg_externAt_aesDec
   aesCbcSubProg_externAt_aesEnc aesCbcSubProg_externAt_cases aesCbcSubProg_externAt_eq
   aesCbcSubProg_svc c2AesDecAddr c2AesEncAddr
   c2_aesCbc_hKeep c2_aesCbc_hlr_ne_stub c2_aesDec_subroutineOk
   c2_aesEnc_subroutineOk c2_keepRxSeg_mallocng c2_mng_placeable keepRxSeg keepRxSeg_aesDec
   keepRxSeg_aesEnc keepRxSeg_eq_progKeep rustHandleErrorSym)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (checkRoSegSlice f3CodeInv_roDataAt_of_roSegSlice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time
  (c2_f3CodeInv_and_fs_hInvKeep)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
  (externAt?_cliProgExtPlacedAt_617 libsignalSessionExterns_resolve_eq_rho
   ls_block617_externs_eq_libsignalSessionExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
  (stripCommExtern_rustPanicked)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (lsPlacedStubPairs lsPlacedStubPairs_eq ls_block617_externs_eq ls_sharedExterns_lt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElfSymAddrs cliElf_externs_distinct_of_linkedAt cliElf_linkedAt_unique
   lsInternedMultiLib ls_names_nodup)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts cliLinkedPanicAddrs f3RxSeg_realProg617_externAt_none isLinkedPanicAddr)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree_eq f3TrialRxWordTree_size)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen (wp4HandleErrorAddr)

/-! ## 1. `stubFrozenGuard` & Block-`617` `hPanReal` Discharges (`18` Linked Panic Entries) -/

theorem c2_aesCbc_hStubFrozen
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (_hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u → stubFrozenGuard aesCbcSubProg u := by
  intro u hu pc hne
  cases he : aesCbcSubProg.externAt? pc with
  | none => exact False.elim (hne he)
  | some f =>
    obtain ⟨_, hp⟩ := aesCbcSubProg_externAt_cases he
    have hc := (hInv u hu).rxCode
    have hlen : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
      rw [f3TrialRxWordTree_eq]
      exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size
    have hrx_in : (pc - f3TrialRxProg.base).toNat < f3TrialRxProg.code.length ∧
        f3TrialRxProg.base + BitVec.ofNat 64 (pc - f3TrialRxProg.base).toNat = pc := by
      rw [f3TrialRxProg_base, hlen]
      unfold isLinkedPanicAddr cliLinkedPanicAddrs at hp
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
        beq_iff_eq] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hperm := hc.perm_eq (pc - f3TrialRxProg.base).toNat hrx_in.1
    rw [hrx_in.2] at hperm
    rw [hperm]
    exact ⟨rfl, rfl⟩

private def panicPrefixCharsLocal : List Char :=
  ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':']

private theorem core_panicking_toList_eq_local :
    "core::panicking::".toList = panicPrefixCharsLocal := by
  decide

private def isCliPanicSymbolPlacedFastLocal (s : String) : Bool :=
  CryptoVerification.SignalSession.cliCratePanicSyms.contains s ||
  (List.isPrefixOf panicPrefixCharsLocal s.toList ||
   [ "core::result::unwrap_failed",
     "core::option::unwrap_failed",
     "core::option::expect_failed",
     "core::slice::index::slice_start_index_len_fail",
     "core::slice::index::slice_end_index_len_fail",
     "core::slice::index::slice_index_order_fail",
     "core::slice::index::slice_index_fail",
     "alloc::raw_vec::handle_error",
     "alloc::raw_vec::capacity_overflow",
     "alloc::alloc::handle_alloc_error" ].contains s)

private theorem isCliPanicSymbolPlaced_eq_fastLocal (s : String) :
    isCliPanicSymbolPlaced s = isCliPanicSymbolPlacedFastLocal s := by
  have hsw : s.startsWith "core::panicking::" =
      List.isPrefixOf "core::panicking::".toList s.toList := by
    rw [Bool.eq_iff_iff, String.startsWith_string_iff, List.isPrefixOf_iff_prefix]
  unfold isCliPanicSymbolPlaced isCliPanicSymbolPlacedFastLocal Rust.isPanicSymbol
  rw [hsw, core_panicking_toList_eq_local]

private theorem ls_externs_eq_stubPairs_fst_local :
    libsignalSessionExterns = lsPlacedStubPairs.map Prod.fst := by
  rw [← ls_block617_externs_eq_libsignalSessionExterns, ls_block617_externs_eq,
    lsPlacedStubPairs_eq, List.map_map]
  rfl

private theorem lsPlacedStubPairs_mem_and_rho_local :
    ∀ p ∈ lsPlacedStubPairs,
      p.1 ∈ lsInternedMultiLib.names ∧ cliElfMultiPlacement.ρ p.1 = p.2 := by
  rw [lsPlacedStubPairs_eq]
  intro p hp
  obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hp
  have hlt : idx < lsInternedMultiLib.names.length :=
    Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx)
  have hget : lsInternedMultiLib.names.getD idx "" = lsInternedMultiLib.names[idx] := by
    simp [List.getD, hlt]
  have hmem : lsInternedMultiLib.names.getD idx "" ∈ lsInternedMultiLib.names := by
    rw [hget]; exact List.getElem_mem hlt
  have hrho : cliElfMultiPlacement.ρ (lsInternedMultiLib.names.getD idx "") =
      cliElfSymAddrs.getD idx 0#64 := by
    change cliElfSymAddrs.getD
      (lsInternedMultiLib.names.idxOf (lsInternedMultiLib.names.getD idx "")) 0#64 =
      cliElfSymAddrs.getD idx 0#64
    rw [Obj.Interned.idxOf_getD ls_names_nodup hlt]
  exact ⟨hmem, hrho⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000000 in
private theorem c2_linkedPanicAddrs_in_real_pairs_chk :
    (cliLinkedPanicAddrs.all fun pc =>
      (lsPlacedStubPairs.findSome? fun (e, a) =>
        if a == pc then
          if isCliPanicSymbolPlacedFastLocal e then some true else none
        else none) == some true) = true := by
  rfl_kernel

theorem c2_linkedPanicAddr_externAt_real {mpl : Obj.MultiPlacement} (mmpl : Obj.MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) {pc : BitVec 64} (hp : isLinkedPanicAddr pc = true) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked := by
  have hmem_pc : pc ∈ cliLinkedPanicAddrs := List.contains_iff_mem.mp hp
  have hchk := beq_iff_eq.mp (List.all_eq_true.mp c2_linkedPanicAddrs_in_real_pairs_chk pc hmem_pc)
  rw [externAt?_cliProgExtPlacedAt_617, ls_block617_externs_eq_libsignalSessionExterns,
    ls_externs_eq_stubPairs_fst_local, List.findSome?_map]
  have hcongr : ∀ p ∈ lsPlacedStubPairs,
      (if (libsignalSessionLib.resolve mpl p.1 == pc) = true
       then cliExternsPlaced mmpl W p.1 else none) =
      ((if (p.2 == pc) = true then
        if isCliPanicSymbolPlacedFastLocal p.1 then some true else none
      else none)).map (fun _ => Rust.panicked) := by
    intro p hpPair
    have hMemExt : p.1 ∈ libsignalSessionExterns :=
      ls_externs_eq_stubPairs_fst_local ▸ List.mem_map_of_mem hpPair
    obtain ⟨hName, hRho⟩ := lsPlacedStubPairs_mem_and_rho_local p hpPair
    have hRes : libsignalSessionLib.resolve mpl p.1 = p.2 :=
      ((cliElf_linkedAt_unique hLs).2.1 p.1 hName).trans
        ((libsignalSessionExterns_resolve_eq_rho cliElfMultiPlacement p.1 hMemExt).trans hRho)
    rw [hRes]
    unfold cliExternsPlaced
    change (if (p.2 == pc) = true then
        if isCliPanicSymbolPlaced p.1 then some Rust.panicked else none
      else none) = _
    rw [isCliPanicSymbolPlaced_eq_fastLocal]
    cases (p.2 == pc) with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; rfl
    | true =>
      simp only [↓reduceIte]
      cases isCliPanicSymbolPlacedFastLocal p.1 <;> rfl
  trans ((lsPlacedStubPairs.findSome? fun (e, a) =>
      if a == pc then
        if isCliPanicSymbolPlacedFastLocal e then some true else none
      else none).map (fun _ => Rust.panicked))
  · revert hcongr
    generalize lsPlacedStubPairs = ps
    intro hcongr
    induction ps with
    | nil => rfl
    | cons p rest ih =>
      simp only [List.findSome?_cons, Function.comp_apply]
      rw [hcongr p (.head _)]
      cases (if (p.2 == pc) = true then
        if isCliPanicSymbolPlacedFastLocal p.1 then some true else none
      else none) with
      | none => exact ih fun q hq => hcongr q (.tail _ hq)
      | some _ => rfl
  · rw [hchk]; rfl

theorem c2_aesCbc_hPanReal {mpl : Obj.MultiPlacement} (mmpl : Obj.MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      aesCbcSubProg.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked := by
  intro W pc f he
  obtain ⟨hf, hp⟩ := aesCbcSubProg_externAt_cases he
  exact ⟨hf, c2_linkedPanicAddr_externAt_real mmpl hLs W hp⟩

/-! ## 2. `hCL_strip`, `hRealHullNoExt`, `HookOk`, & Full `GhostRowOk` Assembly -/

theorem c2_aesCbc_hCL_strip
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, ExecFrozen u.mem → InvS u →
      aesCbcSubProg.CodeLoaded (stripExecOutside keepRxSeg u.mem) := by
  intro u _ hu
  rw [aesCbcSubProg_codeLoaded_iff]
  have hc := (hInv u hu).rxCode
  refine Program.CodeLoaded.intro hc.aligned hc.no_wrap ?_
  intro i hi
  have hi64 : i < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi (Nat.le_add_left _ _)) hc.no_wrap
  have hk_i : keepRxSeg (f3TrialRxProg.base + BitVec.ofNat 64 i) = true := by
    unfold keepRxSeg
    have hsub : f3TrialRxProg.base + BitVec.ofNat 64 i - f3TrialRxProg.base =
        BitVec.ofNat 64 i := by bv_omega
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
    exact decide_eq_true hi
  refine ⟨?_, ?_, ?_⟩
  · rw [strip_read8]
    exact hc.byte_eq i hi
  · rw [strip_perm, hk_i, hc.perm_eq i hi]
    rfl
  · rw [strip_isLazyFree]
    exact hc.isLazyFree_eq i hi

theorem c2_aesCbc_hRealHullNoExt {mpl mmpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepRxSeg pc = true → aesCbcSubProg.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
  intro W pc hkeep hnone
  rw [aesCbcSubProg_externAt_eq] at hnone
  cases hp : isLinkedPanicAddr pc with
  | true => rw [hp] at hnone; cases hnone
  | false => exact f3RxSeg_realProg617_externAt_none hExt W (keepRxSeg_eq_progKeep ▸ hkeep) hp

set_option maxRecDepth 4000000 in
private theorem c2_aesRcon_roSegSlice_ok :
    checkRoSegSlice f3PatchedElf c2AesRconAddr aesRconBytes = true := by
  rfl_kernel

theorem c2_aesCbc_hRconRo
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u → RoDataAt u.mem c2AesRconAddr aesRconBytes :=
  fun u hu => f3CodeInv_roDataAt_of_roSegSlice hLs (hInv u hu) c2_aesRcon_roSegSlice_ok

theorem c2_aesEncGhost_hookOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (aesEncGhost keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim)
      (aesEncSpecOf mmpl brkStart lim γ tp) :=
  aesEncGhost_ok
    aesCbcSubProg_svc
    (fun _ _ he =>
      (aesCbcSubProg_externAt_cases he).1 ▸ stripCommExtern_rustPanicked keepRxSeg)
    (c2_aesCbc_hlr_ne_stub hLsLsmpl)
    (c2_mng_placeable mmpl hMm)
    (c2_keepRxSeg_mallocng mmpl hMm)
    γ tp
    (fun hbrk => c2_aesEnc_subroutineOk mmpl hMm brkStart hbrk lim γ tp)

theorem c2_aesDecGhost_hookOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (aesDecGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim)
      (aesDecSpecOf mmpl brkStart lim γ tp) :=
  aesDecGhost_ok
    aesCbcSubProg_svc
    (fun _ _ he =>
      (aesCbcSubProg_externAt_cases he).1 ▸ stripCommExtern_rustPanicked keepRxSeg)
    (c2_aesCbc_hlr_ne_stub hLsLsmpl)
    (c2_mng_placeable mmpl hMm)
    (c2_keepRxSeg_mallocng mmpl hMm)
    γ tp
    (fun hbrk => c2_aesDec_subroutineOk mmpl hMm brkStart hbrk lim γ tp)

theorem c2_aesDecGhost_weakHookOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (aesDecGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim)
      (aesDecWeakSpecOf mmpl brkStart lim γ tp) :=
  aesDecGhost_weak_ok
    aesCbcSubProg_svc
    (fun _ _ he =>
      (aesCbcSubProg_externAt_cases he).1 ▸ stripCommExtern_rustPanicked keepRxSeg)
    (c2_aesCbc_hlr_ne_stub hLsLsmpl)
    (c2_mng_placeable mmpl hMm)
    (c2_keepRxSeg_mallocng mmpl hMm)
    γ tp
    (fun hbrk => c2_aesDec_subroutineOk mmpl hMm brkStart hbrk lim γ tp)

theorem c2_aesEncGhost_rowOk_of_inv [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts mpl)
    (hResEnc : libsignalSessionLib.resolve mpl lsAesEncSym = c2AesEncAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk mpl mmpl InvS EG lsAesEncSym (fun _ => True)
      (aesEncGhost keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim) :=
  aesEncGhost_rowOk mpl mmpl keepRxSeg aesCbcSubProg c2AesEncAddr brkStart lim
    InvS EG
    aesCbcSubProg_svc
    aesCbcSubProg_externAt_aesEnc
    keepRxSeg_aesEnc
    (c2_keepRxSeg_mallocng mmpl hMm)
    (fun γ tp => c2_aesEnc_subroutineOk mmpl hMm brkStart hbrk lim γ tp)
    (c2_aesCbc_hStubFrozen hLs hInv)
    (c2_aesCbc_hRconRo hLs hInv)
    hbrk
    hResEnc
    (c2_aesCbc_hCL_strip hInv)
    hInvKeep
    (fun _ hlr => c2_aesCbc_hKeep hLsLsmpl hlr)
    (c2_aesCbc_hlr_ne_stub hLsLsmpl)
    (c2_aesCbc_hRealHullNoExt hExt)
    (c2_aesCbc_hPanReal mmpl hLs)

theorem c2_aesEncGhost_rowOk_lsmpl_and_fs [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hResEnc : libsignalSessionLib.resolve lsmpl lsAesEncSym = c2AesEncAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsAesEncSym
      (fun _ => True)
      (aesEncGhost keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim) :=
  c2_aesEncGhost_rowOk_of_inv lsmpl mmpl brkStart lim
    (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
    hExt hResEnc hLs hLs hMm
    (fun _ h => h.1)
    (c2_f3CodeInv_and_fs_hInvKeep lsmpl mmpl PredFs)
    hbrk

theorem c2_aesEncGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hExt : C2ExternTableFacts lsmpl)
    (hResEnc : libsignalSessionLib.resolve lsmpl lsAesEncSym = c2AesEncAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsAesEncSym
      (guardOf lsAesEncSym)
      (aesEncGhost keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim) := by
  obtain ⟨hSpec, hRep⟩ :=
    c2_aesEncGhost_rowOk_lsmpl_and_fs mmpl brkStart lim PredFs EG hExt hResEnc hLs hMm hbrk
  exact ⟨hSpec, ⟨hRep.preserves_execFrozen, fun W s0 sf _ => hRep.replay_at_stub W s0 sf trivial⟩⟩

theorem c2_aesDecGhost_rowOk_of_inv [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts mpl)
    (hResDec : libsignalSessionLib.resolve mpl lsAesDecSym = c2AesDecAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk mpl mmpl InvS EG lsAesDecSym (fun _ => True)
      (aesDecGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) :=
  aesDecGhost_rowOk mpl mmpl keepRxSeg aesCbcSubProg c2AesDecAddr brkStart lim
    InvS EG
    aesCbcSubProg_svc
    aesCbcSubProg_externAt_aesDec
    keepRxSeg_aesDec
    (c2_keepRxSeg_mallocng mmpl hMm)
    (fun γ tp => c2_aesDec_subroutineOk mmpl hMm brkStart hbrk lim γ tp)
    (c2_aesCbc_hStubFrozen hLs hInv)
    (c2_aesCbc_hRconRo hLs hInv)
    hbrk
    hResDec
    (c2_aesCbc_hCL_strip hInv)
    hInvKeep
    (fun _ hlr => c2_aesCbc_hKeep hLsLsmpl hlr)
    (c2_aesCbc_hlr_ne_stub hLsLsmpl)
    (c2_aesCbc_hRealHullNoExt hExt)
    (c2_aesCbc_hPanReal mmpl hLs)

theorem c2_aesDecGhost_rowOk_lsmpl_and_fs [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hResDec : libsignalSessionLib.resolve lsmpl lsAesDecSym = c2AesDecAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsAesDecSym
      (fun _ => True)
      (aesDecGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) :=
  c2_aesDecGhost_rowOk_of_inv lsmpl mmpl brkStart lim
    (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
    hExt hResDec hLs hLs hMm
    (fun _ h => h.1)
    (c2_f3CodeInv_and_fs_hInvKeep lsmpl mmpl PredFs)
    hbrk

theorem c2_aesDecGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hExt : C2ExternTableFacts lsmpl)
    (hResDec : libsignalSessionLib.resolve lsmpl lsAesDecSym = c2AesDecAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsAesDecSym
      (guardOf lsAesDecSym)
      (aesDecGhost keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) := by
  obtain ⟨hSpec, hRep⟩ :=
    c2_aesDecGhost_rowOk_lsmpl_and_fs mmpl brkStart lim PredFs EG hExt hResDec hLs hMm hbrk
  exact ⟨hSpec, ⟨hRep.preserves_execFrozen, fun W s0 sf _ => hRep.replay_at_stub W s0 sf trivial⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbcRow

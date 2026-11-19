/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbcRow
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
import ProofLib.Process.FastParse
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import

/-!
# `GhostRowOk` and `HookOk` Discharge for `libcrux_hmac::hmac`

Assembles `c2_libcruxHmacGhost_hookOk`, `c2_libcruxHmacGhost_rowOk_of_inv`,
`c2_libcruxHmacGhost_rowOk_lsmpl_and_fs`, and `c2_libcruxHmacGhost_rowOk_guardOf` for
`lsLibcruxHmacSym` (`libcrux_hmac::hmac`, SHA-256 `w0 = 0`) over `.text.lib2`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmacRow

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.SepLogic
  ProofLib.StdStartup
open VerifiedLibraries (mallocngLib)
open CryptoVerification (LibsignalPlacement libsignalHookedExterns libsignalSessionExterns lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced isCliPanicSymbolPlaced libsignalSessionLib
   lsLibcruxHmacSym patchElfByte patchRegionByte)
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
  (rustHandleErrorSym rustUnwrapFailedSym)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbcRow
  (c2_aesCbc_hPanReal c2_aesCbc_hRealHullNoExt c2_aesCbc_hStubFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac
  (c2_keepRxSeg_mallocng c2_libcruxHmac_hKeep c2_libcruxHmac_hlr_ne_stub
   c2_libcruxHmac_subroutineOk c2_mng_placeable keepRxSeg keepRxSeg_entry keepRxSeg_eq_progKeep
   libcruxHmacSubProg libcruxHmacSubProg_codeLoaded_iff libcruxHmacSubProg_externAt_cases
   libcruxHmacSubProg_externAt_hmac libcruxHmacSubProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time
  (c2_f3CodeInv_and_fs_hInvKeep)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
  (externAt?_cliProgExtPlacedAt_617_of_unique_resolve libsignalSessionExterns_resolve_eq_rho
   ls_block617_externs_eq_libsignalSessionExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LibcruxHmacGhostReplays
  (libcruxHmacGhost libcruxHmacGhost_ok libcruxHmacGhost_rowOk libcruxHmacSpecOf stubFrozenGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
  (stripCommExtern_rustPanicked)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElf_externs_distinct_of_linkedAt cliElf_linkedAt_unique lsInternedMultiLib)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3RxSeg_realProg617_externAt_none)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2HaclMpl c2LibcruxHmacAddr)

/-! ## 1. Vacuous `stubFrozenGuard` & Block-`617` `hPanReal` Discharges (zero externs) -/

theorem c2_libcruxHmac_hStubFrozen
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u → stubFrozenGuard libcruxHmacSubProg u :=
  c2_aesCbc_hStubFrozen hLs hInv

theorem c2_libcruxHmac_hPanReal {mpl : Obj.MultiPlacement} (mmpl : Obj.MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      libcruxHmacSubProg.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked :=
  c2_aesCbc_hPanReal mmpl hLs

/-! ## 2. `hCL_strip`, `hRealHullNoExt`, `HookOk`, & Full `GhostRowOk` Assembly -/

theorem c2_libcruxHmac_hCL_strip
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, ExecFrozen u.mem → InvS u →
      libcruxHmacSubProg.CodeLoaded (stripExecOutside keepRxSeg u.mem) := by
  intro u _ hu
  rw [libcruxHmacSubProg_codeLoaded_iff]
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

theorem c2_libcruxHmac_hRealHullNoExt {mpl mmpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepRxSeg pc = true → libcruxHmacSubProg.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  c2_aesCbc_hRealHullNoExt hExt

theorem c2_libcruxHmacGhost_hookOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (libcruxHmacGhost keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim)
      (libcruxHmacSpecOf mmpl brkStart lim γ tp) :=
  libcruxHmacGhost_ok
    libcruxHmacSubProg_svc
    (fun _ _ he =>
      (libcruxHmacSubProg_externAt_cases he).1 ▸ stripCommExtern_rustPanicked keepRxSeg)
    (c2_libcruxHmac_hlr_ne_stub hLsLsmpl)
    (c2_mng_placeable mmpl hMm)
    (c2_keepRxSeg_mallocng mmpl hMm)
    γ tp
    (c2_libcruxHmac_subroutineOk mmpl hMm brkStart lim γ tp)

theorem c2_libcruxHmacGhost_rowOk_of_inv [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts mpl)
    (hResHmac : libsignalSessionLib.resolve mpl lsLibcruxHmacSym = c2LibcruxHmacAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v) :
    GhostRowOk mpl mmpl InvS EG lsLibcruxHmacSym (fun _ => True)
      (libcruxHmacGhost keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim) :=
  libcruxHmacGhost_rowOk mpl mmpl keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr brkStart lim
    InvS EG
    libcruxHmacSubProg_svc
    libcruxHmacSubProg_externAt_hmac
    keepRxSeg_entry
    (c2_keepRxSeg_mallocng mmpl hMm)
    (fun γ tp => c2_libcruxHmac_subroutineOk mmpl hMm brkStart lim γ tp)
    (c2_libcruxHmac_hStubFrozen hLs hInv)
    hResHmac
    (c2_libcruxHmac_hCL_strip hInv)
    hInvKeep
    (fun _ hlr => c2_libcruxHmac_hKeep hLsLsmpl hlr)
    (c2_libcruxHmac_hlr_ne_stub hLsLsmpl)
    (c2_libcruxHmac_hRealHullNoExt hExt)
    (c2_libcruxHmac_hPanReal mmpl hLs)

theorem c2_libcruxHmacGhost_rowOk_lsmpl_and_fs [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hResHmac : libsignalSessionLib.resolve lsmpl lsLibcruxHmacSym = c2LibcruxHmacAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsLibcruxHmacSym
      (fun _ => True)
      (libcruxHmacGhost keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim) :=
  c2_libcruxHmacGhost_rowOk_of_inv lsmpl mmpl brkStart lim
    (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
    hExt hResHmac hLs hLs hMm
    (fun _ h => h.1)
    (c2_f3CodeInv_and_fs_hInvKeep lsmpl mmpl PredFs)

theorem c2_libcruxHmacGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hExt : C2ExternTableFacts lsmpl)
    (hResHmac : libsignalSessionLib.resolve lsmpl lsLibcruxHmacSym = c2LibcruxHmacAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsLibcruxHmacSym
      (guardOf lsLibcruxHmacSym)
      (libcruxHmacGhost keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim) := by
  obtain ⟨hSpec, hRep⟩ :=
    c2_libcruxHmacGhost_rowOk_lsmpl_and_fs mmpl brkStart lim PredFs EG hExt hResHmac hLs hMm
  exact ⟨hSpec, ⟨hRep.preserves_execFrozen, fun W s0 sf _ => hRep.replay_at_stub W s0 sf trivial⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmacRow

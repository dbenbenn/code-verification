/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer

/-!
# `W`-Independent Route-β′ `duration_since` Ghost Hook & Stock-Safe `StepsVisitedIn` Replay (`HooksDehook.DurationSinceGhostLs`)

Specializes Route-β′ `durationSinceGhostFnLs` (`withLsRet masterDurationSinceSpec`) to
`P_real := emptyStdProg` (`f3EmptyDurationSinceGhostHookLs`) and proves the stock-safe
`h2fsgen_StepsVisitedIn` first-stop witness (`f3EmptyDurationSinceGhostHookLs_visitedIn`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostLs

open Arm64 Arm64.Obj ProofLib
open VerifiedLibraries.RustStd (timeMultiLib timePlacedData0 timeRodataCst16Sym)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (durationSinceExactHook)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ActiveRealPre ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  linkedCallHookG_activeRealPre_of_noException
  linkedCallHookG_stepsUntil linkedCallHookG_visitedIn roTableGuard_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg emptyStdProg_svc)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (h2fsgen_StepsVisitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode (
  masterDurationSinceSpec subTimespecPatchedWords durationSincePatchedWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhost (
  durationSinceGhostFnLs durationSinceGhostFnLs_fs
  durationSinceGhostFnLs_keepLr_false_of_noException
  specStripSInvariant_masterDurationSinceLs specPreservesFsTrace_masterDurationSinceLs
  masterDurationSinceLs_pre_setPC masterDurationSinceLs_outcome_setPC
  subroutine_ok_masterDurationSinceLs_of_hasWords
)

/-- Route-β′ (`withLsRet masterDurationSinceSpec`) `W`-independent `duration_since` ghost hook. -/
@[expose] noncomputable def f3EmptyDurationSinceGhostHookLs [LibsignalPlacement]
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_sub : Program)
    (entry : BitVec 64) : State → State :=
  durationSinceGhostFnLs cst16Addr keepR emptyStdProg P_sub entry

theorem durationSinceGhostFnLs_visitedIn [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    {u : State} (hRo : RoDataAt u.mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hnoex : ∀ msg,
      (durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub
        (mpl.base 1) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    let sf := durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub (mpl.base 1) u
    StepsUntil P_run (SubroutineStop u) (u.setPC (mpl.base 1)) sf ∧
      SubroutineStop u sf ∧ ExecFrozen sf.mem ∧ sf.fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC (mpl.base 1)) sf := by
  have hlr_out := durationSinceGhostFnLs_keepLr_false_of_noException hKeep hnoex
  have hActPre : ActiveRealPre (withLsRet masterDurationSinceSpec) u :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  have hOk := subroutine_ok_masterDurationSinceLs_of_hasWords hpl hsvc_sub hsub_no hw0 hw1
  have hGS := roTableGuard_stripS keepR (mpl.base 1) (mpl.ρ timeRodataCst16Sym) timePlacedData0
  obtain ⟨huntil, hstop, hfr_sf⟩ :=
    linkedCallHookG_stepsUntil (fallback := durationSinceExactHook)
      hsvc_run hsvc_sub hrun_no hsub_no hGS hOk
      (specStripSInvariant_masterDurationSinceLs keepR) specPreservesFsTrace_masterDurationSinceLs
      masterDurationSinceLs_pre_setPC masterDurationSinceLs_outcome_setPC
      hRo hActPre hFr hlr_out hCodeSub
  obtain ⟨hvis, _⟩ :=
    linkedCallHookG_visitedIn (fallback := durationSinceExactHook)
      hsvc_run hsvc_sub hrun_no hsub_no hGS hOk
      (specStripSInvariant_masterDurationSinceLs keepR) specPreservesFsTrace_masterDurationSinceLs
      masterDurationSinceLs_pre_setPC masterDurationSinceLs_outcome_setPC
      hRo hActPre hFr hlr_out hCodeSub
  exact ⟨huntil, hstop, hfr_sf,
    durationSinceGhostFnLs_fs (mpl.ρ timeRodataCst16Sym) keepR P_run P_sub (mpl.base 1) u, hvis⟩

theorem f3EmptyDurationSinceGhostHookLs_visitedIn [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    {u : State} (hRo : RoDataAt u.mem (mpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hnoex : ∀ msg,
      (f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub
        (mpl.base 1) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    let sf := f3EmptyDurationSinceGhostHookLs (mpl.ρ timeRodataCst16Sym) keepR P_sub (mpl.base 1) u
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC (mpl.base 1)) sf ∧
      SubroutineStop u sf ∧ ExecFrozen sf.mem ∧ sf.fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (mpl.base 1)) sf :=
  durationSinceGhostFnLs_visitedIn hpl emptyStdProg_svc hsvc_sub (fun _ _ => rfl) hsub_no hw0 hw1
    hKeep hRo hnoex hFr hCodeSub

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostLs

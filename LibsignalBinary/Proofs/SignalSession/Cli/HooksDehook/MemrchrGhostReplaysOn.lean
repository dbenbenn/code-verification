/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `GhostExternReplaysOn` / `GhostExternReplaysS` & `StepsVisitedIn` Bridges for `memrchr` (`HooksDehook.MemrchrGhostReplaysOn`)

Card **R2-b** replay module for `memrchr` (mirroring `HooksDehook.BcmpGhostK` §4–§5 and
`HooksDehook.MemcpyGhostReplaysOn`):

1. **Direct `P_real` Guarded Replay (`memrchrGhostFn{Ls,,K}_replayOn`):**
   - Route `β′` (`memrchrGhostFnLs`) discharges `keepR (u.readReg64 .lr) = false` automatically from
     `hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false` (`K3`) + `hnoex`.
   - `K`-narrowed (`memrchrGhostFnK`) discharges `keepR (u.readReg64 .lr) = false` unconditionally
     from `hnoex`.
   - Raw plain (`memrchrGhostFn`) takes `keepR (u.readReg64 .lr) = false` at call sites.
2. **Stock-Safe `h2fsgen_StepsVisitedIn` First-Stop Witnesses & `GhostExternReplays{On,S}`:**
   Provides `*_visitedIn`, `*_replayOn_of_visitedIn`, `*_replaysS_of_visitedIn`, and
   `*_replaysOn_of_visitedIn` for `f3EmptyMemrchrGhostHook{Ls,,K}` as well as concrete
   `P_sub := pureWordsProg entryTarget coreMemrchrWords` (`f3PureMemrchrGhostHook{Ls,,K}`)
   specializations (`REV-MRO` card-c note).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostReplaysOn

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (memrchrHook)
open LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO (coreMemrchrWords)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_linkedCallHook
  ghostExternReplaysOn_of_single_stub
  ghostExternReplaysS_of_single_stub
  linkedCallHook_activeRealPre_of_noException
  linkedCallHook_fs_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  withLsRet subroutine_ok_withLsRet withLsRet_pre_setPC withLsRet_outcome_setPC
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det h2fsgen_real_subroutine_run_visitedIn_of_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrCode (
  masterMemrchrSpec memrchrSpecK
  specStripSInvariant_masterMemrchr specStripSInvariant_masterMemrchrK
  pureWordsProg_memrchr_hasWords
  subroutine_ok_masterMemrchr_of_hasWords
  subroutine_ok_masterMemrchrK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhost (
  memrchrGhostFnLs memrchrGhostFn memrchrGhostFnK
  specStripSInvariant_masterMemrchrLs
  specPreservesFsTrace_masterMemrchr specPreservesFsTrace_masterMemrchrLs specPreservesFsTrace_masterMemrchrK
  masterMemrchr_pre_setPC masterMemrchrK_pre_setPC
  masterMemrchr_outcome_setPC masterMemrchrK_outcome_setPC
  memrchrGhostFnLs_keepLr_false_of_noException
  memrchrGhostFnK_keepLr_false_of_noException
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostK (
  f3EmptyMemrchrGhostHookLs f3EmptyMemrchrGhostHook f3EmptyMemrchrGhostHookK
  f3PureMemrchrGhostHookLs f3PureMemrchrGhostHook f3PureMemrchrGhostHookK
  f3EmptyMemrchrGhostHookLs_eq f3EmptyMemrchrGhostHook_eq f3EmptyMemrchrGhostHookK_eq
)

/-! ## 4. Direct `P_real` Guarded Replay (`GhostExternReplaysOn` / `GhostExternReplaysS`) -/

/-! ## 5. Stock-Safe `h2fsgen_StepsVisitedIn` First-Stop Witness & `GhostExternReplaysOn` / `S` -/

/-- Stock-safe `h2fsgen_StepsVisitedIn keepR P_run` first-stop witness for Route `β′`
    `memrchrGhostFnLs` (`keepR (u.readReg64 .lr) = false` discharged from `hKeep` + `hnoex`). -/
theorem memrchrGhostFnLs_visitedIn [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (memrchrGhostFnLs keepR P_run P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil P_run (SubroutineStop u) (u.setPC entryTarget)
        (memrchrGhostFnLs keepR P_run P_sub entryTarget u) ∧
      SubroutineStop u (memrchrGhostFnLs keepR P_run P_sub entryTarget u) ∧
      ExecFrozen (memrchrGhostFnLs keepR P_run P_sub entryTarget u).mem ∧
      (memrchrGhostFnLs keepR P_run P_sub entryTarget u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC entryTarget)
        (memrchrGhostFnLs keepR P_run P_sub entryTarget u) := by
  classical
  have hlr_out : keepR (u.readReg64 .lr) = false :=
    memrchrGhostFnLs_keepLr_false_of_noException hKeep hnoex
  have hActPre : ActiveRealPre (withLsRet masterMemrchrSpec) u :=
    linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS
      hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_withLsRet (subroutine_ok_masterMemrchr_of_hasWords hsub_no hwords))
      (specStripSInvariant_masterMemrchrLs keepR)
      specPreservesFsTrace_masterMemrchrLs
      (withLsRet_pre_setPC masterMemrchr_pre_setPC)
      (withLsRet_outcome_setPC masterMemrchr_outcome_setPC)
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keepR P_run P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have hfn_eq : memrchrGhostFnLs keepR P_run P_sub entryTarget u =
      Classical.choose hReal.2.2.2 := by
    unfold memrchrGhostFnLs linkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hsf_eq : sf = Classical.choose hReal.2.2.2 :=
    h2fsgen_stepsUntil_det huntil hstop hchoose.1 hchoose.2.1
  rw [hfn_eq, ← hsf_eq]
  exact ⟨huntil, hstop, hfr_sf, hfs, hvis⟩

/-- Stock-safe `h2fsgen_StepsVisitedIn keepR P_run` first-stop witness for `memrchrGhostFnK`
    (zero caller `lr` premise). -/
theorem memrchrGhostFnK_visitedIn
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (memrchrGhostFnK keepR P_run P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil P_run (SubroutineStop u) (u.setPC entryTarget)
        (memrchrGhostFnK keepR P_run P_sub entryTarget u) ∧
      SubroutineStop u (memrchrGhostFnK keepR P_run P_sub entryTarget u) ∧
      ExecFrozen (memrchrGhostFnK keepR P_run P_sub entryTarget u).mem ∧
      (memrchrGhostFnK keepR P_run P_sub entryTarget u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC entryTarget)
        (memrchrGhostFnK keepR P_run P_sub entryTarget u) := by
  classical
  have hlr_out : keepR (u.readReg64 .lr) = false :=
    memrchrGhostFnK_keepLr_false_of_noException hnoex
  have hActPre : ActiveRealPre (memrchrSpecK keepR masterMemrchrSpec) u :=
    linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS
      hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_masterMemrchrK_of_hasWords keepR hsub_no hwords)
      (specStripSInvariant_masterMemrchrK keepR)
      (specPreservesFsTrace_masterMemrchrK keepR)
      (masterMemrchrK_pre_setPC keepR)
      (masterMemrchrK_outcome_setPC keepR)
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keepR P_run P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have hfn_eq : memrchrGhostFnK keepR P_run P_sub entryTarget u =
      Classical.choose hReal.2.2.2 := by
    unfold memrchrGhostFnK linkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hsf_eq : sf = Classical.choose hReal.2.2.2 :=
    h2fsgen_stepsUntil_det huntil hstop hchoose.1 hchoose.2.1
  rw [hfn_eq, ← hsf_eq]
  exact ⟨huntil, hstop, hfr_sf, hfs, hvis⟩

/-- `W`-independent `h2fsgen_StepsVisitedIn keepR emptyStdProg` witness for
    `f3EmptyMemrchrGhostHookLs` (Route `β′`). -/
theorem f3EmptyMemrchrGhostHookLs_visitedIn [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget)
        (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).mem ∧
      (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget)
        (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u) := by
  rw [f3EmptyMemrchrGhostHookLs_eq] at hnoex ⊢
  exact memrchrGhostFnLs_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords hKeep
    hrun hnoex hFr hCodeSub

/-- `W`-independent `h2fsgen_StepsVisitedIn keepR emptyStdProg` witness for
    `f3EmptyMemrchrGhostHookK` (zero caller `lr` premise). -/
theorem f3EmptyMemrchrGhostHookK_visitedIn
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget)
        (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u).mem ∧
      (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget)
        (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u) := by
  rw [f3EmptyMemrchrGhostHookK_eq] at hnoex ⊢
  exact memrchrGhostFnK_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords hrun hnoex hFr
    hCodeSub

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostReplaysOn

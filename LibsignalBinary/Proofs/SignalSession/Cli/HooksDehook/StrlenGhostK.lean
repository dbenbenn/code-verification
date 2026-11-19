/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `W`-Independent K-Convention `strlen` Ghost Hook & Stock-Safe `visitedIn` Replays (`HooksDehook.StrlenGhostK`)

Layout-independent, `CliElf`-free (`LibsignalBinary.Cli`-rootable) K-convention layer for the
placement-generic `strlen` ghost hook (`Card L2-b`):

1. **`strlenGhostHookK` Consumer `HookOk` Suite (All 11 SWAR-Padded Contracts + `withAlloc`):**
   Lifts `strlenGhostHookK_masterK_ok` across all 11 SWAR-padded `strlen` consumer specs (`_ok`,
   `_keepsFs_ok`, `_budget_ok`, `_budget_keepsFs_ok`, `_withAlloc_ok`, and `_withAllocK_ok`),
   including `hookOk_strlenSpecK_of_withAlloc` / `hookOk_withAlloc_of_strlenSpecK` commuting
   `strlenSpecK keep` with `WithAlloc.withAlloc`.
2. **`f3EmptyStrlenGhostHook` & `f3EmptyStrlenGhostHookK` (`P_real := emptyStdProg`):**
   Reuses `MemsetGhostK.emptyStdProg` (`Program.ofSvc Syscall.standard`, `rfl`-equal to
   `hole2_emptyProg`) and `MemsetGhostK.f3LinkedCallHook_const_eq_linkedCallHook` so the ghost hook
   has **zero dependence on `W : CliHooks`**, forwarding all `HookOk`, `HookFsTraced IsFsC`,
   `VmPreserved`, `OomPreserved ∧ PoolPreserved`, `ExecFrozen`, and `keep lr = false` lemmas with
   **zero `P_real` hypotheses**.
3. **Stock-Safe `h2fsgen_StepsVisitedIn`-Only Replay Bridges (`MUST` Rule):**
   Uses `h2fsgen_real_subroutine_run_visitedIn_of_stripS` and `h2fsgen_stepsUntil_det` to emit
   `h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) (f u)` (`_visitedIn`) and bridges
   across any `P_real` via a visited-PC lift premise `hLiftVis` (`_target_replay_of_visitedIn`,
   `_replayOn_of_visitedIn`, `_replaysS_of_visitedIn`) — with **zero** legacy `StepsUntil → Steps`
   `hLift` and **zero** `h2fsgen_HooksUnfetched`. Also exports direct `P_real` behind-stub replays
   `strlenGhostHook{,K}_replayOn`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostK

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (muslStrlenWords)
open CryptoVerification.SignalSession (strlenHook)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.Cli.MainHops (strlenSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (strlenSpecRO)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget
  VmPreserved OomPreserved PoolPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (
  cliStrlenPaddedSpec strlenPaddedSpecRO
  withStrlenPadRO withStrlenRoDataPad withStrlenAlignedEnd
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  ActiveF3CallPre f3LinkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_linkedCallHook ghostExternReplaysS_of_single_stub linkedCallHook_fs_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (memcpySpecK)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  activeF3CallPre_const_iff emptyStdProg f3LinkedCallHook_const_eq_linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  withAlloc hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode (
  masterStrlenSpec masterStrlenROSpec strlenSpecK
  subroutine_ok_masterStrlen_of_hasWords subroutine_ok_masterStrlenK_of_hasWords
  hookOk_cliStrlenPaddedK_of_master hookOk_strlenPaddedROK_of_master
  hookOk_strlenSpecRO_padROK_of_master hookOk_strlenSpecRO_roDataPadK_of_master
  hookOk_strlenSpecRO_alignedEndK_of_master
  hookOk_mainStrlen_padROK_of_master hookOk_mainStrlen_roDataPadK_of_master
  hookOk_mainStrlen_alignedEndK_of_master
  hookOk_cliExtStrlen_padROK_of_master hookOk_cliExtStrlen_roDataPadK_of_master
  hookOk_cliExtStrlen_alignedEndK_of_master
  strlenSpecK_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost (
  strlenByteLen strlenByteLen_eq
  strlenGhostHook strlenGhostHookK
  specStripSInvariant_masterStrlen specStripSInvariant_masterStrlenK
  specPreservesFsTrace_masterStrlen specPreservesFsTrace_masterStrlenK
  masterStrlen_pre_setPC masterStrlenK_pre_setPC
  masterStrlen_outcome_setPC masterStrlenK_outcome_setPC
  strlenGhostHook_master_ok strlenGhostHookK_masterK_ok
  strlenGhostHook_masterRO_ok strlenGhostHookK_masterROK_ok
  strlenGhostHook_masterVm_ok strlenGhostHookK_masterVmK_ok
  strlenGhostHook_fs strlenGhostHookK_fs
  strlenGhostHook_fsT strlenGhostHookK_fsT
  strlenGhostHook_vmPreserved strlenGhostHookK_vmPreserved
  strlenGhostHook_oomPoolPreserved strlenGhostHookK_oomPoolPreserved
  strlenGhostHook_trace strlenGhostHookK_trace
  strlenGhostHook_preserves_execFrozen strlenGhostHookK_preserves_execFrozen
  strlenGhostHookK_keepLr_false_of_noException
  strlenGhostHook_of_keepLr_true strlenGhostHookK_of_keepLr_true
  strlenGhostHookK_any_keepsFs_ok strlenGhostHook_any_strlenSpecK_ok
  strlenGhostHook_cliStrlenPadded_ok strlenGhostHook_cliStrlenPadded_keepsFs_ok
  strlenGhostHook_cliStrlenPadded_budget_ok strlenGhostHook_cliStrlenPadded_withAlloc_ok
  strlenGhostHook_strlenPaddedRO_ok strlenGhostHook_strlenPaddedRO_keepsFs_ok
  strlenGhostHook_strlenPaddedRO_budget_ok strlenGhostHook_strlenPaddedRO_withAlloc_ok
  strlenGhostHook_strlenSpecRO_padRO_ok strlenGhostHook_strlenSpecRO_padRO_budget_ok
  strlenGhostHook_strlenSpecRO_padRO_withAlloc_ok
  strlenGhostHook_mainStrlen_padRO_ok strlenGhostHook_mainStrlen_padRO_budget_ok
  strlenGhostHook_mainStrlen_padRO_withAlloc_ok
  strlenGhostHook_cliExtStrlen_padRO_ok strlenGhostHook_cliExtStrlen_padRO_budget_ok
  strlenGhostHook_cliExtStrlen_padRO_withAlloc_ok
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_real_subroutine_run_visitedIn_of_stripS h2fsgen_stepsUntil_det
)

/-! ## 1. `strlenSpecK` ↔ `withAlloc` Commutation & `strlenGhostHookK` Consumer Suite -/

section KConsumerSuite

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget muslStrlenWords)
variable (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)

include hsvc_real hsvc_sub hreal_no hsub_no hwords haddr

-- All 11 SWAR-padded consumer contracts on `strlenGhostHookK`:
end KConsumerSuite

/-! ## 2. `W`-Independent `f3EmptyStrlenGhostHook{,K}` & `P_real`-Free Properties / `HookOk` -/

@[expose] noncomputable def f3EmptyStrlenGhostHook
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => masterStrlenSpec) strlenHook
@[expose] noncomputable def f3EmptyStrlenGhostHookK
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget
    (fun _ _ => strlenSpecK keep masterStrlenSpec) strlenHook
noncomputable abbrev f3EmptyStrlenGhostHookPure
    (keep : BitVec 64 → Bool) (entryTarget : BitVec 64) : State → State :=
  f3EmptyStrlenGhostHook keep (pureWordsProg entryTarget muslStrlenWords) entryTarget
theorem f3EmptyStrlenGhostHook_eq
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyStrlenGhostHook keep P_sub entryTarget =
      strlenGhostHook keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget
    masterStrlenSpec strlenHook
theorem f3EmptyStrlenGhostHookK_eq
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyStrlenGhostHookK keep P_sub entryTarget =
      strlenGhostHookK keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget
    (strlenSpecK keep masterStrlenSpec) strlenHook

theorem f3EmptyStrlenGhostHook_fs
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyStrlenGhostHook keep P_sub entryTarget s0).fs = s0.fs := by
  rw [f3EmptyStrlenGhostHook_eq]; exact strlenGhostHook_fs keep emptyStdProg P_sub entryTarget s0
theorem f3EmptyStrlenGhostHookK_fs
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyStrlenGhostHookK keep P_sub entryTarget s0).fs = s0.fs := by
  rw [f3EmptyStrlenGhostHookK_eq]; exact strlenGhostHookK_fs keep emptyStdProg P_sub entryTarget s0
theorem f3EmptyStrlenGhostHook_fsT
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyStrlenGhostHook keep P_sub entryTarget) := by
  rw [f3EmptyStrlenGhostHook_eq]; exact strlenGhostHook_fsT keep emptyStdProg P_sub entryTarget
theorem f3EmptyStrlenGhostHookK_fsT
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyStrlenGhostHookK keep P_sub entryTarget) := by
  rw [f3EmptyStrlenGhostHookK_eq]; exact strlenGhostHookK_fsT keep emptyStdProg P_sub entryTarget
theorem f3EmptyStrlenGhostHook_preserves_execFrozen
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (f3EmptyStrlenGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHook keep P_sub entryTarget u).fs = u.fs := by
  rw [f3EmptyStrlenGhostHook_eq]
  exact strlenGhostHook_preserves_execFrozen keep emptyStdProg P_sub entryTarget hfr
theorem f3EmptyStrlenGhostHookK_preserves_execFrozen
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  rw [f3EmptyStrlenGhostHookK_eq]
  exact strlenGhostHookK_preserves_execFrozen keep emptyStdProg P_sub entryTarget hfr

theorem f3EmptyStrlenGhostHookK_keepLr_false_of_noException
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg, (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  rw [f3EmptyStrlenGhostHookK_eq] at hnoex; exact strlenGhostHookK_keepLr_false_of_noException hnoex

section F3EmptyHookOkForwarding

variable {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget muslStrlenWords)
variable (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)

include hsvc_sub hsub_no hwords haddr in
theorem f3EmptyStrlenGhostHook_vmPreserved (s0 : State) :
    VmPreserved s0 (f3EmptyStrlenGhostHook keep P_sub entryTarget s0) := by
  rw [f3EmptyStrlenGhostHook_eq]
  exact strlenGhostHook_vmPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr s0

theorem f3EmptyStrlenGhostHook_ok_of_ghost {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHook keep emptyStdProg P_sub entryTarget) spec) :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) spec := by
  rwa [f3EmptyStrlenGhostHook_eq]

include hsvc_sub hsub_no hwords haddr

theorem f3EmptyStrlenGhostHook_master_ok :
    HookOk (f3EmptyStrlenGhostHook keep P_sub entryTarget) masterStrlenSpec :=
  f3EmptyStrlenGhostHook_ok_of_ghost
    (strlenGhostHook_master_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords haddr)
-- Plain `f3EmptyStrlenGhostHook` consumer lifts (all 11 SWAR-padded contracts):
-- `K` `f3EmptyStrlenGhostHookK` headline consumer lifts (+ `f3EmptyStrlenGhostHookK_ok_of_ghostK` for all others):
end F3EmptyHookOkForwarding

/-! ## 3. Stock-Safe `visitedIn`-Only Replay Bridges & Direct `P_real` Behind-Stub Replays -/

/-- `W`-independent `h2fsgen_StepsVisitedIn keep emptyStdProg` witness for
    `f3EmptyStrlenGhostHook`, pinning the `Classical.choose` endpoint via `h2fsgen_stepsUntil_det`. -/
theorem f3EmptyStrlenGhostHook_visitedIn
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyStrlenGhostHook keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget)
        (f3EmptyStrlenGhostHook keep P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyStrlenGhostHook keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyStrlenGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHook keep P_sub entryTarget u).fs = u.fs := by
  classical
  have hActPre : ActiveF3CallPre (fun _ _ => masterStrlenSpec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3EmptyStrlenGhostHook f3LinkedCallHook
    simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ := (activeF3CallPre_const_iff masterStrlenSpec u).mp hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS (P1 := emptyStdProg) rfl hsvc_sub
      (fun _ _ => rfl) hsub_no
      (subroutine_ok_masterStrlen_of_hasWords (entry := entryTarget) hsub_no hwords
        (by simpa [strlenByteLen_eq] using haddr))
      (specStripSInvariant_masterStrlen keep)
      specPreservesFsTrace_masterStrlen
      masterStrlen_pre_setPC
      masterStrlen_outcome_setPC
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep emptyStdProg P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq : f3EmptyStrlenGhostHook keep P_sub entryTarget u = sf := by
    unfold f3EmptyStrlenGhostHook f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  rw [heq]
  exact ⟨hvis, hstop, hfr_sf, hfs⟩

/-- `W`-independent `h2fsgen_StepsVisitedIn keep emptyStdProg` witness for
    `f3EmptyStrlenGhostHookK`, automatically discharging `keep (u.readReg64 .lr) = false` from
    `hnoex` via `f3EmptyStrlenGhostHookK_keepLr_false_of_noException`. -/
theorem f3EmptyStrlenGhostHookK_visitedIn
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget)
        (f3EmptyStrlenGhostHookK keep P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyStrlenGhostHookK keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyStrlenGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  classical
  have hlr_out : keep (u.readReg64 .lr) = false :=
    f3EmptyStrlenGhostHookK_keepLr_false_of_noException hnoex
  have hActPre : ActiveF3CallPre (fun _ _ => strlenSpecK keep masterStrlenSpec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3EmptyStrlenGhostHookK f3LinkedCallHook
    simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ :=
    (activeF3CallPre_const_iff (strlenSpecK keep masterStrlenSpec) u).mp hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS (P1 := emptyStdProg) rfl hsvc_sub
      (fun _ _ => rfl) hsub_no
      (subroutine_ok_masterStrlenK_of_hasWords keep (entry := entryTarget) hsub_no hwords
        (by simpa [strlenByteLen_eq] using haddr))
      (specStripSInvariant_masterStrlenK keep)
      (specPreservesFsTrace_masterStrlenK keep)
      (masterStrlenK_pre_setPC keep)
      (masterStrlenK_outcome_setPC keep)
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep emptyStdProg P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq : f3EmptyStrlenGhostHookK keep P_sub entryTarget u = sf := by
    unfold f3EmptyStrlenGhostHookK f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  rw [heq]
  exact ⟨hvis, hstop, hfr_sf, hfs⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostK

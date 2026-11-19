/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhost -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `W`-Independent K-Convention `bcmp` Ghost Hook & Stock-Safe `StepsVisitedIn` Bridge (`HooksDehook.BcmpGhostK`)

Card **L1-b** companion module to `HooksDehook.BcmpGhost` (mirroring `HooksDehook.MemsetGhostK`
while replacing the legacy `StepsUntil` `hLift` bridge with the stock-safe `h2fsgen_StepsVisitedIn`
bridge):

1. **`f3EmptyBcmpGhostHook` & `f3EmptyBcmpGhostHookK`**:
   Defined with `F3AllocStdinGhostHooks.f3LinkedCallHook` at `P_real := emptyStdProg` (`= Program.ofSvc
   Syscall.standard`, `rfl`-equal to `hole2_emptyProg`) and the `W`-independent fallback
   `hookBcmpFallback` from `BcmpCode`, so both hooks have **zero dependence on `W : CliHooks`**.
2. **Extensional Bridge to `bcmpGhostFn` / `bcmpGhostFnK`**:
   `f3EmptyBcmpGhostHook_eq` and `f3EmptyBcmpGhostHookK_eq` invoke
   `MemsetGhostK.f3LinkedCallHook_const_eq_linkedCallHook`, forwarding all C11 §8.1 state/trace/VM
   obligations and consumer `HookOk` theorems (plain, `withVmPreserved`, `withAlloc A lim`, `.keepsFs`,
   and `K`) with **zero `P_real` hypotheses**.
3. **Stock-Safe `h2fsgen_StepsVisitedIn` First-Stop Witness & `P_run → P_real` Guarded Replays**:
   - `bcmpGhostFn_visitedIn` / `bcmpGhostFnK_visitedIn` and `f3EmptyBcmpGhostHook_visitedIn` /
     `f3EmptyBcmpGhostHookK_visitedIn` produce
     `h2fsgen_StepsVisitedIn keepR P_run (u.setPC (m + memcmpByteLen)) (f u)` via
     `h2fsgen_real_subroutine_run_visitedIn_of_stripS` + `h2fsgen_stepsUntil_det` (no
     `h2sl_stepsUntil_emptyProg_to_realW`, no `h2fsgen_HooksUnfetched`).
   - `bcmpGhostFn{,K}_replayOn_of_visitedIn`, `f3EmptyBcmpGhostHook{,K}_replayOn_of_visitedIn`, and
     `f3EmptyBcmpGhostHook{,K}_replaysS_of_visitedIn` replay onto any `P_real` via a premise
     `hLiftVis` (discharged in card `c` via C2's `f3RxSeg_steps_realW_of_visitedIn`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostK

open Arm64 ProofLib
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.Cli (cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (bcmpSpec)
open CryptoVerification.E2E.HooksE (bcmpVregsSpec e2eBcmpSpec)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits OomPreserved PoolPreserved RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Bcmp (cliBcmpStackSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysS_of_single_stub linkedCallHook_activeRealPre_of_noException
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (withExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg f3LinkedCallHook_const_eq_linkedCallHook
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det h2fsgen_real_subroutine_run_visitedIn_of_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode (
  masterBcmpSpec bcmpSpecK
  memcmpByteLen bcmpHullWords
  subroutine_ok_hull_masterBcmp_of_hasWords subroutine_ok_hull_masterBcmpK_of_hasWords
  hookBcmpFallback
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhost (
  bcmpGhostFn bcmpGhostFnK
  specStripSInvariant_masterBcmp specStripSInvariant_masterBcmpK
  specPreservesFsTrace_masterBcmp specPreservesFsTrace_masterBcmpK
  masterBcmp_pre_setPC masterBcmpK_pre_setPC
  masterBcmp_outcome_setPC masterBcmpK_outcome_setPC
  bcmpGhostFn_master_ok bcmpGhostFnK_masterK_ok
  bcmpGhostFn_vmPreserved bcmpGhostFnK_vmPreserved
  bcmpGhostFn_oomPoolPreserved bcmpGhostFnK_oomPoolPreserved
  bcmpGhostFn_oracle bcmpGhostFnK_oracle
  bcmpGhostFn_trace bcmpGhostFnK_trace
  bcmpGhostFnK_keepLr_false_of_noException
  bcmpGhostFn_of_keepLr_true bcmpGhostFnK_of_keepLr_true
  bcmpGhostFn_dirCliBcmp_ok bcmpGhostFn_cliBcmpStack_ok bcmpGhostFn_cliExtBcmp_ok
  bcmpGhostFn_bcmpVregs_ok bcmpGhostFn_e2eBcmp_ok
  bcmpGhostFn_dirCliBcmp_budget_ok bcmpGhostFn_cliBcmpStack_budget_ok
  bcmpGhostFn_cliExtBcmp_budget_ok bcmpGhostFn_bcmpVregs_budget_ok bcmpGhostFn_e2eBcmp_budget_ok
  bcmpGhostFn_dirCliBcmp_withAlloc_ok bcmpGhostFn_dirCliBcmp_budget_withAlloc_ok
  bcmpGhostFn_cliBcmpStack_withAlloc_ok bcmpGhostFn_cliBcmpStack_budget_withAlloc_ok
  bcmpGhostFn_cliExtBcmp_withAlloc_ok bcmpGhostFn_cliExtBcmp_budget_withAlloc_ok
  bcmpGhostFn_bcmpVregs_withAlloc_ok bcmpGhostFn_bcmpVregs_budget_withAlloc_ok
  bcmpGhostFn_e2eBcmp_withAlloc_ok bcmpGhostFn_e2eBcmp_budget_withAlloc_ok
  bcmpGhostFn_any_keepsFs_ok bcmpGhostFn_any_withOomPoolPreserved_ok
  bcmpGhostFn_any_execFrozen_ok bcmpGhostFn_any_bcmpSpecK_ok
  bcmpGhostFnK_dirCliBcmpK_ok bcmpGhostFnK_cliBcmpStackK_ok bcmpGhostFnK_cliExtBcmpK_ok
  bcmpGhostFnK_bcmpVregsK_ok bcmpGhostFnK_e2eBcmpK_ok
  bcmpGhostFnK_dirCliBcmpK_budget_ok bcmpGhostFnK_cliBcmpStackK_budget_ok
  bcmpGhostFnK_cliExtBcmpK_budget_ok bcmpGhostFnK_bcmpVregsBudgetK_ok
  bcmpGhostFnK_e2eBcmpBudgetK_ok
  bcmpGhostFnK_dirCliBcmpK_withAlloc_ok bcmpGhostFnK_dirCliBcmpK_budget_withAlloc_ok
  bcmpGhostFnK_cliBcmpStackK_withAlloc_ok bcmpGhostFnK_cliBcmpStackK_budget_withAlloc_ok
  bcmpGhostFnK_cliExtBcmpK_withAlloc_ok bcmpGhostFnK_cliExtBcmpK_budget_withAlloc_ok
  bcmpGhostFnK_bcmpVregsK_withAlloc_ok bcmpGhostFnK_bcmpVregsBudgetK_withAlloc_ok
  bcmpGhostFnK_e2eBcmpK_withAlloc_ok bcmpGhostFnK_e2eBcmpBudgetK_withAlloc_ok
  bcmpGhostFnK_any_keepsFs_ok bcmpGhostFnK_any_withOomPoolPreserved_ok
  bcmpGhostFnK_any_execFrozen_ok
)

/-! ## 1. `W`-Independent K-Convention `bcmp` Ghost Hook Definitions & Equalities -/

/-- Plain `W`-independent K-convention `bcmp` ghost hook (`P_real := emptyStdProg =
    Program.ofSvc Syscall.standard`), parametric in `keepR`, `P_sub`, and `entryTarget`. -/
@[expose] noncomputable def f3EmptyBcmpGhostHook
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keepR emptyStdProg P_sub entryTarget
    (fun _ _ => masterBcmpSpec) hookBcmpFallback

/-- `K`-narrowed (`bcmpSpecK keepR masterBcmpSpec`) `W`-independent K-convention `bcmp` ghost hook. -/
@[expose] noncomputable def f3EmptyBcmpGhostHookK
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keepR emptyStdProg P_sub entryTarget
    (fun _ _ => bcmpSpecK keepR masterBcmpSpec) hookBcmpFallback

/-- `f3EmptyBcmpGhostHook` equals `bcmpGhostFn` specialized to `P_real := emptyStdProg`. -/
theorem f3EmptyBcmpGhostHook_eq
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyBcmpGhostHook keepR P_sub entryTarget =
      bcmpGhostFn keepR emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keepR emptyStdProg P_sub entryTarget
    masterBcmpSpec hookBcmpFallback

/-- `f3EmptyBcmpGhostHookK` equals `bcmpGhostFnK` specialized to `P_real := emptyStdProg`. -/
theorem f3EmptyBcmpGhostHookK_eq
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyBcmpGhostHookK keepR P_sub entryTarget =
      bcmpGhostFnK keepR emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keepR emptyStdProg P_sub entryTarget
    (bcmpSpecK keepR masterBcmpSpec) hookBcmpFallback

/-! ## 2. State / Frame / `lr` Properties (`P_real` Hypotheses Discharged Unconditionally) -/

theorem f3EmptyBcmpGhostHook_fs
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyBcmpGhostHook keepR P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keepR emptyStdProg P_sub entryTarget _ hookBcmpFallback s0

theorem f3EmptyBcmpGhostHookK_fs
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyBcmpGhostHookK keepR P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keepR emptyStdProg P_sub entryTarget _ hookBcmpFallback s0

theorem f3EmptyBcmpGhostHook_fsT
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyBcmpGhostHook keepR P_sub entryTarget) :=
  f3LinkedCallHook_fsT keepR emptyStdProg P_sub entryTarget _ hookBcmpFallback

theorem f3EmptyBcmpGhostHookK_fsT
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyBcmpGhostHookK keepR P_sub entryTarget) :=
  f3LinkedCallHook_fsT keepR emptyStdProg P_sub entryTarget _ hookBcmpFallback

theorem f3EmptyBcmpGhostHook_vmPreserved
    {keepR : BitVec 64 → Bool} {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    (s0 : State) :
    VmPreserved s0 (f3EmptyBcmpGhostHook keepR P_sub (m + memcmpByteLen) s0) := by
  rw [f3EmptyBcmpGhostHook_eq]
  exact bcmpGhostFn_vmPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres s0

/-! ## 3. Consumer `HookOk` Forwarding (`P_real` Hypotheses Discharged Unconditionally) -/

section HookOkForwarding

variable {keepR : BitVec 64 → Bool} {P_sub : Program}
variable {m : BitVec 64} {resolve : String → BitVec 64}
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
variable (hres : resolve "memcmp" = m)

include hsvc_sub hsub_no hhull hres

-- 3.1 Plain contracts on `f3EmptyBcmpGhostHook`:

theorem f3EmptyBcmpGhostHook_dirCliBcmp_ok :
    HookOk (f3EmptyBcmpGhostHook keepR P_sub (m + memcmpByteLen)) cliBcmpSpec := by
  rw [f3EmptyBcmpGhostHook_eq]
  exact bcmpGhostFn_dirCliBcmp_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres

theorem f3EmptyBcmpGhostHook_bcmpVregs_ok :
    HookOk (f3EmptyBcmpGhostHook keepR P_sub (m + memcmpByteLen)) bcmpVregsSpec := by
  rw [f3EmptyBcmpGhostHook_eq]
  exact bcmpGhostFn_bcmpVregs_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres

-- 3.2 Budget / `withVmPreserved` variants on `f3EmptyBcmpGhostHook`:

-- 3.3 Pool-framed `withAlloc (M := M) A lim` variants on `f3EmptyBcmpGhostHook`:

-- 3.4 Generic `.keepsFs`, `withOomPoolPreserved`, `withExecFrozen`, & `bcmpSpecK` corollaries:

-- 3.5 `K`-narrowed (`bcmpSpecK keepR …`) contracts on `f3EmptyBcmpGhostHookK`:

end HookOkForwarding

/-! ## 4. Stock-Safe `h2fsgen_StepsVisitedIn` First-Stop Witness & `P_run → P_real` Guarded Replays -/

/-- Stock-safe `h2fsgen_StepsVisitedIn keepR P_run` first-stop execution witness for `bcmpGhostFn`
    (no `h2sl_stepsUntil_emptyProg_to_realW`, no `h2fsgen_HooksUnfetched`), pinning the chosen
    first-stop endpoint via `h2fsgen_stepsUntil_det`. -/
theorem bcmpGhostFn_visitedIn
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (bcmpGhostFn keepR P_run P_sub (m + memcmpByteLen) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keepR (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil P_run (SubroutineStop u) (u.setPC (m + memcmpByteLen))
        (bcmpGhostFn keepR P_run P_sub (m + memcmpByteLen) u) ∧
      SubroutineStop u (bcmpGhostFn keepR P_run P_sub (m + memcmpByteLen) u) ∧
      ExecFrozen (bcmpGhostFn keepR P_run P_sub (m + memcmpByteLen) u).mem ∧
      (bcmpGhostFn keepR P_run P_sub (m + memcmpByteLen) u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC (m + memcmpByteLen))
        (bcmpGhostFn keepR P_run P_sub (m + memcmpByteLen) u) := by
  classical
  have hActPre : ActiveRealPre masterBcmpSpec u :=
    linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS
      hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_hull_masterBcmp_of_hasWords hsub_no hhull hres)
      (specStripSInvariant_masterBcmp keepR)
      specPreservesFsTrace_masterBcmp
      masterBcmp_pre_setPC
      masterBcmp_outcome_setPC
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keepR P_run P_sub (m + memcmpByteLen) u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have hfn_eq : bcmpGhostFn keepR P_run P_sub (m + memcmpByteLen) u =
      Classical.choose hReal.2.2.2 := by
    unfold bcmpGhostFn linkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hsf_eq : sf = Classical.choose hReal.2.2.2 :=
    h2fsgen_stepsUntil_det huntil hstop hchoose.1 hchoose.2.1
  rw [hfn_eq, ← hsf_eq]
  exact ⟨huntil, hstop, hfr_sf, hfs, hvis⟩

/-- Stock-safe `h2fsgen_StepsVisitedIn keepR P_run` first-stop execution witness for `bcmpGhostFnK`,
    discharging `keepR (u.readReg64 .lr) = false` automatically from `hnoex`. -/
theorem bcmpGhostFnK_visitedIn
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (bcmpGhostFnK keepR P_run P_sub (m + memcmpByteLen) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil P_run (SubroutineStop u) (u.setPC (m + memcmpByteLen))
        (bcmpGhostFnK keepR P_run P_sub (m + memcmpByteLen) u) ∧
      SubroutineStop u (bcmpGhostFnK keepR P_run P_sub (m + memcmpByteLen) u) ∧
      ExecFrozen (bcmpGhostFnK keepR P_run P_sub (m + memcmpByteLen) u).mem ∧
      (bcmpGhostFnK keepR P_run P_sub (m + memcmpByteLen) u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC (m + memcmpByteLen))
        (bcmpGhostFnK keepR P_run P_sub (m + memcmpByteLen) u) := by
  classical
  have hlr_out : keepR (u.readReg64 .lr) = false :=
    bcmpGhostFnK_keepLr_false_of_noException hnoex
  have hActPre : ActiveRealPre (bcmpSpecK keepR masterBcmpSpec) u :=
    linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS
      hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_hull_masterBcmpK_of_hasWords keepR hsub_no hhull hres)
      (specStripSInvariant_masterBcmpK keepR)
      (specPreservesFsTrace_masterBcmpK keepR)
      (masterBcmpK_pre_setPC keepR)
      (masterBcmpK_outcome_setPC keepR)
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keepR P_run P_sub (m + memcmpByteLen) u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have hfn_eq : bcmpGhostFnK keepR P_run P_sub (m + memcmpByteLen) u =
      Classical.choose hReal.2.2.2 := by
    unfold bcmpGhostFnK linkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hsf_eq : sf = Classical.choose hReal.2.2.2 :=
    h2fsgen_stepsUntil_det huntil hstop hchoose.1 hchoose.2.1
  rw [hfn_eq, ← hsf_eq]
  exact ⟨huntil, hstop, hfr_sf, hfs, hvis⟩

/-- `W`-independent `h2fsgen_StepsVisitedIn keepR emptyStdProg` first-stop witness for
    `f3EmptyBcmpGhostHook` (feeds C2's `f3RxSeg_steps_realW_of_visitedIn` in card `c`). -/
theorem f3EmptyBcmpGhostHook_visitedIn
    {keepR : BitVec 64 → Bool} {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyBcmpGhostHook keepR P_sub (m + memcmpByteLen) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keepR (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC (m + memcmpByteLen))
        (f3EmptyBcmpGhostHook keepR P_sub (m + memcmpByteLen) u) ∧
      SubroutineStop u (f3EmptyBcmpGhostHook keepR P_sub (m + memcmpByteLen) u) ∧
      ExecFrozen (f3EmptyBcmpGhostHook keepR P_sub (m + memcmpByteLen) u).mem ∧
      (f3EmptyBcmpGhostHook keepR P_sub (m + memcmpByteLen) u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + memcmpByteLen))
        (f3EmptyBcmpGhostHook keepR P_sub (m + memcmpByteLen) u) := by
  rw [f3EmptyBcmpGhostHook_eq] at hnoex ⊢
  exact bcmpGhostFn_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres
    hrun hnoex hFr hlr_out hCodeSub

/-- `W`-independent `h2fsgen_StepsVisitedIn keepR emptyStdProg` first-stop witness for
    `f3EmptyBcmpGhostHookK` (zero caller `lr` premise). -/
theorem f3EmptyBcmpGhostHookK_visitedIn
    {keepR : BitVec 64 → Bool} {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyBcmpGhostHookK keepR P_sub (m + memcmpByteLen) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC (m + memcmpByteLen))
        (f3EmptyBcmpGhostHookK keepR P_sub (m + memcmpByteLen) u) ∧
      SubroutineStop u (f3EmptyBcmpGhostHookK keepR P_sub (m + memcmpByteLen) u) ∧
      ExecFrozen (f3EmptyBcmpGhostHookK keepR P_sub (m + memcmpByteLen) u).mem ∧
      (f3EmptyBcmpGhostHookK keepR P_sub (m + memcmpByteLen) u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + memcmpByteLen))
        (f3EmptyBcmpGhostHookK keepR P_sub (m + memcmpByteLen) u) := by
  rw [f3EmptyBcmpGhostHookK_eq] at hnoex ⊢
  exact bcmpGhostFnK_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres
    hrun hnoex hFr hCodeSub

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostK

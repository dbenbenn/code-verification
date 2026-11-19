/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `W`-Independent `memmove` Ghost Hook (`f3Empty` / `f3Pure`) & `K`-Narrowed Consumer Suite (`HooksDehook.MemmoveGhostK`)

Card **L3-b** (`W`-independent `emptyStdProg` ghost `memmove` hooks + complete `K`-narrowed bounded
consumer `HookOk` suite; stock-safe `visitedIn` and `GhostExternReplaysOn` / `S` bridges live in the
companion split module `HooksDehook.MemmoveGhostReplays`):

1. **`K`-narrowed consumer `HookOk` suite on `memmoveGhostFnK` (§1):**
   All bounded `*MemmoveBounded*` consumer contracts (`libcMemmoveBoundedSpec`,
   `sessionMemmoveBoundedSpec` + `keepsFs`, `sessionMemmoveBoundedBudgetSpec` + `keepsFs`,
   `sessionMemmoveBoundedAcpSpec`, `withAllocVmPreserved (sessionMemmoveBoundedSpec stk)`) lifted
   under `memmoveSpecK keepR`, across non-budget, budget (`withVmPreserved`), and `withAlloc A lim`
   arms.
2. **`W`-independent `f3EmptyMemmoveGhostHook{,K}` & `f3PureMemmoveGhostHook{,K}` (§2):**
   Defined with `F3AllocStdinGhostHooks.f3LinkedCallHook` at `P_real := MemsetGhostK.emptyStdProg`
   (`= Program.ofSvc Syscall.standard`), with **zero dependence on `W : CliHooks`** so the row hook
   can be fixed before `∀ W` in `CliGhostHooks.extra` / `GhostRowReplayOn`.
   By `MemsetGhostK.f3LinkedCallHook_const_eq_linkedCallHook`, `f3EmptyMemmoveGhostHook{,K}` is
   extensionally equal to `memmoveGhostFn{,K} keepR emptyStdProg`, discharging `P_real.svc =
   Syscall.standard` and `∀ pc, keepR pc = true → P_real.externAt? pc = none` unconditionally by
   `rfl` (**C4 / F1**: `P_ghost`'s active `g.memcpy` / `g.memset` entries never affect internal
   `memmove → b memcpy` execution).
3. **`P_real`-free state / frame / `TrapRetHook` & consumer `HookOk` forwarding (§§3–4):**
   Every state/frame/trap lemma and every plain, `K`, budget, and `withAlloc` consumer `HookOk`
   contract forwarded to `f3EmptyMemmoveGhostHook{,K}` (zero `P_real` hypotheses) and specialized to
   `f3PureMemmoveGhostHook{,K}` (`P_sub := pureWordsProg m (bPreHullWords m resolve padWord)`, zero
   `P_sub` hypotheses).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostK

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (StdStatePreserved)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits OomPreserved PoolPreserved
  RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.Fine (hookOk_withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved hookOk_withOomPoolPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (
  libcMemmoveBoundedSpec sessionMemmoveBoundedSpec sessionMemmoveBoundedBudgetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ActiveRealPre linkedCallHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  withAlloc hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  pureWordsProg_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  withExecFrozen hookOk_withExecFrozen_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg f3LinkedCallHook_const_eq_linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode (
  masterMemmoveSpec stdMemmoveSpec memmoveSpecK
  bPrePadWord bPreMemmoveByteOff bPreHullWords
  pureWordsProg_bPreHull_hasWords
  sessionMemmoveBoundedAcpSpec
  hookOk_libcMemmoveBoundedK_of_master
  hookOk_sessionMemmoveBoundedK_of_master
  hookOk_sessionMemmoveBounded_keepsFsK_of_master
  hookOk_sessionMemmoveBoundedBudgetK_of_master
  hookOk_sessionMemmoveBoundedAcpK_of_master
  hookOk_allocVmPreserved_sessionMemmoveBoundedK_of_master
  memmoveSpecK_keepsFs memmoveSpecK_withVmPreserved
  TrapRetHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost (
  spec_keepsFs_eq_common memmoveSpecK_withAlloc memmoveSpecK_withOomPoolPreserved
  memmoveGhostFn memmoveGhostFnK memmoveGhostPure memmoveGhostPureK
  memmoveGhostFn_symtab memmoveGhostFnK_fs memmoveGhostFnK_symtab
  memmoveGhostFn_master_ok memmoveGhostFnK_masterK_ok
  memmoveGhostFn_stdStatePreserved memmoveGhostFnK_stdStatePreserved
  memmoveGhostFn_vmPreserved memmoveGhostFnK_vmPreserved
  memmoveGhostFn_oomPoolPreserved memmoveGhostFnK_oomPoolPreserved
  memmoveGhostFn_oracle memmoveGhostFnK_oracle
  memmoveGhostFn_allocCallPreserved memmoveGhostFnK_allocCallPreserved
  memmoveGhostFn_trace memmoveGhostFnK_trace
  memmoveGhostFnK_keepLr_false_of_noException
  memmoveGhostFn_of_keepLr_true memmoveGhostFnK_of_keepLr_true
  trapRetHook_memmoveGhostFn trapRetHook_memmoveGhostFnK
  memmoveGhostFn_stdMemmove_ok memmoveGhostFnK_stdMemmoveK_ok
  memmoveGhostFn_masterVm_ok memmoveGhostFnK_masterVmK_ok
  memmoveGhostFn_libcBounded_ok memmoveGhostFn_libcBounded_budget_ok
  memmoveGhostFn_sessionBounded_ok memmoveGhostFn_sessionBounded_keepsFs_ok
  memmoveGhostFn_sessionBoundedBudget_ok memmoveGhostFn_sessionBoundedBudget_keepsFs_ok
  memmoveGhostFn_sessionBoundedAcp_ok memmoveGhostFn_allocVmPreserved_sessionBounded_ok
  memmoveGhostFn_master_withAlloc_ok memmoveGhostFn_masterVm_withAlloc_ok
  memmoveGhostFn_libcBounded_withAlloc_ok memmoveGhostFn_libcBounded_budget_withAlloc_ok
  memmoveGhostFn_sessionBounded_withAlloc_ok memmoveGhostFn_sessionBoundedBudget_withAlloc_ok
  memmoveGhostFn_sessionBoundedAcp_withAlloc_ok
  memmoveGhostFn_allocVmPreserved_sessionBounded_withAlloc_ok
  memmoveGhostFn_any_keepsFs_ok memmoveGhostFn_any_withOomPoolPreserved_ok
  memmoveGhostFn_any_execFrozen_ok memmoveGhostFn_any_memmoveSpecK_ok
)

/-! ## 1. `K`-Narrowed Consumer `HookOk` Suite on `memmoveGhostFnK` -/

section GenericKHookOkSuite

variable
  {keepR : BitVec 64 → Bool}
  {P_real P_sub : Program}
  {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
  (hsvc_real : P_real.svc = Syscall.standard)
  (hsvc_sub : P_sub.svc = Syscall.standard)
  (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
  (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
  (hres : resolve "memcpy" = m)

include hsvc_real hsvc_sub hreal_no hsub_no hhull hres

end GenericKHookOkSuite

/-! ## 2. `W`-Independent `f3EmptyMemmoveGhostHook{,K}` & `f3PureMemmoveGhostHook{,K}` (`P_real := emptyStdProg`) -/

/-- `W`-independent `memmove` ghost hook (`P_real := emptyStdProg`, fallback `hookMemmove`),
    matching the 7 F3 ghosts in `ElfSlicesPqOomH2KHooks` and `CliGhostHooks.extra`. -/
@[expose] noncomputable def f3EmptyMemmoveGhostHook
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    State → State :=
  f3LinkedCallHook keepR emptyStdProg P_sub entryTarget (fun _ _ => masterMemmoveSpec) hookMemmove

/-- `W`-independent `K`-narrowed `memmove` ghost hook (`P_real := emptyStdProg`, fallback
    `hookMemmove`). -/
@[expose] noncomputable def f3EmptyMemmoveGhostHookK
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    State → State :=
  f3LinkedCallHook keepR emptyStdProg P_sub entryTarget
    (fun _ _ => memmoveSpecK keepR masterMemmoveSpec) hookMemmove

/-- Single-`P_sub` `.text.b_pre` hull instantiation of `f3EmptyMemmoveGhostHook` (`239` words
    `bPreHullWords m resolve padWord`, entered at `m + bPreMemmoveByteOff` = `m + 660#64`). -/
noncomputable abbrev f3PureMemmoveGhostHook
    (keepR : BitVec 64 → Bool) (m : BitVec 64)
    (resolve : String → BitVec 64) (padWord : BitVec 32 := bPrePadWord) :
    State → State :=
  f3EmptyMemmoveGhostHook keepR
    (pureWordsProg m (bPreHullWords m resolve padWord)) (m + bPreMemmoveByteOff)

/-- Single-`P_sub` `.text.b_pre` hull instantiation of `f3EmptyMemmoveGhostHookK`. -/
noncomputable abbrev f3PureMemmoveGhostHookK
    (keepR : BitVec 64 → Bool) (m : BitVec 64)
    (resolve : String → BitVec 64) (padWord : BitVec 32 := bPrePadWord) :
    State → State :=
  f3EmptyMemmoveGhostHookK keepR
    (pureWordsProg m (bPreHullWords m resolve padWord)) (m + bPreMemmoveByteOff)

/-- `f3EmptyMemmoveGhostHook` is extensionally equal to `memmoveGhostFn keepR emptyStdProg`. -/
theorem f3EmptyMemmoveGhostHook_eq
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyMemmoveGhostHook keepR P_sub entryTarget =
      memmoveGhostFn keepR emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keepR emptyStdProg P_sub entryTarget
    masterMemmoveSpec hookMemmove

/-- `f3EmptyMemmoveGhostHookK` is extensionally equal to `memmoveGhostFnK keepR emptyStdProg`. -/
theorem f3EmptyMemmoveGhostHookK_eq
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyMemmoveGhostHookK keepR P_sub entryTarget =
      memmoveGhostFnK keepR emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keepR emptyStdProg P_sub entryTarget
    (memmoveSpecK keepR masterMemmoveSpec) hookMemmove

/-! ## 3. `P_real`-Free State / Frame / `TrapRetHook` Properties (`0` `P_ghost` Extern Premises) -/

theorem f3EmptyMemmoveGhostHook_fs
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    ∀ s0, (f3EmptyMemmoveGhostHook keepR P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keepR emptyStdProg P_sub entryTarget (fun _ _ => masterMemmoveSpec) hookMemmove

theorem f3EmptyMemmoveGhostHookK_fs
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    ∀ s0, (f3EmptyMemmoveGhostHookK keepR P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keepR emptyStdProg P_sub entryTarget
    (fun _ _ => memmoveSpecK keepR masterMemmoveSpec) hookMemmove

theorem f3EmptyMemmoveGhostHook_fsT
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyMemmoveGhostHook keepR P_sub entryTarget) :=
  f3LinkedCallHook_fsT keepR emptyStdProg P_sub entryTarget (fun _ _ => masterMemmoveSpec) hookMemmove

theorem f3EmptyMemmoveGhostHookK_fsT
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyMemmoveGhostHookK keepR P_sub entryTarget) :=
  f3LinkedCallHook_fsT keepR emptyStdProg P_sub entryTarget
    (fun _ _ => memmoveSpecK keepR masterMemmoveSpec) hookMemmove

theorem f3EmptyMemmoveGhostHook_vmPreserved
    {keepR : BitVec 64 → Bool} {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl) :
    ∀ s0, VmPreserved s0 (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) s0) := by
  rw [f3EmptyMemmoveGhostHook_eq]
  exact memmoveGhostFn_vmPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres

theorem f3EmptyMemmoveGhostHookK_vmPreserved
    {keepR : BitVec 64 → Bool} {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl) :
    ∀ s0, VmPreserved s0 (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) s0) := by
  rw [f3EmptyMemmoveGhostHookK_eq]
  exact memmoveGhostFnK_vmPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres

theorem f3EmptyMemmoveGhostHook_allocCallPreserved
    {keepR : BitVec 64 → Bool} {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl) :
    ∀ s0, AllocCallPreserved s0 (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) s0) := by
  rw [f3EmptyMemmoveGhostHook_eq]
  exact memmoveGhostFn_allocCallPreserved rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres

theorem trapRetHook_f3EmptyMemmoveGhostHook
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget L : BitVec 64}
    (hlr : keepR L = true) :
    TrapRetHook L (f3EmptyMemmoveGhostHook keepR P_sub entryTarget) := by
  rw [f3EmptyMemmoveGhostHook_eq]
  exact trapRetHook_memmoveGhostFn hlr

theorem trapRetHook_f3EmptyMemmoveGhostHookK
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget L : BitVec 64}
    (hlr : keepR L = true) :
    TrapRetHook L (f3EmptyMemmoveGhostHookK keepR P_sub entryTarget) := by
  rw [f3EmptyMemmoveGhostHookK_eq]
  exact trapRetHook_memmoveGhostFnK hlr

/-! ## 4. `P_real`-Free Consumer `HookOk` Forwarding (`f3Empty` & `f3Pure` Forms) -/

section HookOkForwarding

theorem f3EmptyMemmoveGhostHook_ok_of_ghost {α : Type}
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (memmoveGhostFn keepR emptyStdProg P_sub entry) spec) :
    HookOk (f3EmptyMemmoveGhostHook keepR P_sub entry) spec := by
  rwa [f3EmptyMemmoveGhostHook_eq]

theorem f3EmptyMemmoveGhostHookK_ok_of_ghostK {α : Type}
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (memmoveGhostFnK keepR emptyStdProg P_sub entry) spec) :
    HookOk (f3EmptyMemmoveGhostHookK keepR P_sub entry) spec := by
  rwa [f3EmptyMemmoveGhostHookK_eq]

variable
  {keepR : BitVec 64 → Bool}
  {P_sub : Program}
  {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
  (hsvc_sub : P_sub.svc = Syscall.standard)
  (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
  (hres : resolve "memcpy" = m)

include hsvc_sub hsub_no hhull hres

-- 4.1 Master & `stdMemmoveSpec` `HookOk`:

theorem f3EmptyMemmoveGhostHook_master_ok :
    HookOk (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff)) masterMemmoveSpec :=
  f3EmptyMemmoveGhostHook_ok_of_ghost
    (memmoveGhostFn_master_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres)

theorem f3EmptyMemmoveGhostHookK_masterK_ok :
    HookOk (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff))
      (memmoveSpecK keepR masterMemmoveSpec) :=
  f3EmptyMemmoveGhostHookK_ok_of_ghostK
    (memmoveGhostFnK_masterK_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres)

-- 4.2 Plain bounded consumer `HookOk` (non-budget, budget, & `withAlloc`):

theorem f3EmptyMemmoveGhostHook_libcBounded_ok (stk : Nat := extHookStack) :
    HookOk (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff))
      (libcMemmoveBoundedSpec stk) :=
  f3EmptyMemmoveGhostHook_ok_of_ghost
    (memmoveGhostFn_libcBounded_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres stk)

theorem f3EmptyMemmoveGhostHook_libcBounded_budget_ok (stk : Nat := extHookStack) :
    HookOk (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff))
      (withVmPreserved (libcMemmoveBoundedSpec stk)) :=
  f3EmptyMemmoveGhostHook_ok_of_ghost
    (memmoveGhostFn_libcBounded_budget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres stk)

theorem f3EmptyMemmoveGhostHook_sessionBounded_ok (stk : Nat := extHookStack) :
    HookOk (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff))
      (sessionMemmoveBoundedSpec stk) :=
  f3EmptyMemmoveGhostHook_ok_of_ghost
    (memmoveGhostFn_sessionBounded_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres stk)

theorem f3EmptyMemmoveGhostHook_sessionBoundedBudget_ok (stk : Nat := extHookStack) :
    HookOk (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff))
      (sessionMemmoveBoundedBudgetSpec stk) :=
  f3EmptyMemmoveGhostHook_ok_of_ghost
    (memmoveGhostFn_sessionBoundedBudget_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres stk)

theorem f3EmptyMemmoveGhostHook_libcBounded_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := extHookStack) :
    HookOk (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff))
      (withAlloc (M := M) A lim (libcMemmoveBoundedSpec stk)) :=
  f3EmptyMemmoveGhostHook_ok_of_ghost
    (memmoveGhostFn_libcBounded_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres A lim stk)

theorem f3EmptyMemmoveGhostHook_sessionBounded_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := extHookStack) :
    HookOk (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff))
      (withAlloc (M := M) A lim (sessionMemmoveBoundedSpec stk)) :=
  f3EmptyMemmoveGhostHook_ok_of_ghost
    (memmoveGhostFn_sessionBounded_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres A lim stk)

theorem f3EmptyMemmoveGhostHook_sessionBoundedBudget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := extHookStack) :
    HookOk (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff))
      (withAlloc (M := M) A lim (sessionMemmoveBoundedBudgetSpec stk)) :=
  f3EmptyMemmoveGhostHook_ok_of_ghost
    (memmoveGhostFn_sessionBoundedBudget_withAlloc_ok rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres A lim stk)

-- 4.3 `K`-narrowed bounded consumer `HookOk` on `f3EmptyMemmoveGhostHookK` (non-budget, budget, `withAlloc`):

end HookOkForwarding

-- 4.4 Zero-premise concrete `f3PureMemmoveGhostHook{,K}` (`pureWordsProg` + `emptyStdProg`) witnesses:

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostK

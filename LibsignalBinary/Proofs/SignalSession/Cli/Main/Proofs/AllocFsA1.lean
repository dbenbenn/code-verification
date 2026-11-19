/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.HooksE.TripleRatchetHooksCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# Allocator and Memory Hook Helpers for `cliExterns`

File-system preservation for allocator/memory hooks, hook-table row witnesses, `CliAllocHooks`, and
read-only-source `memcpy` (`session_memcpy_region_ro`) on `cliExterns W`.
-/

public section

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-! ## File-System Preservation for Allocator and Memory Hooks -/

/-- `bumpThen` preserves `fs` whenever both continuations do. -/
theorem bumpThen_fs {size align : Nat} {ok : State → BitVec 64 → State} {fail : State → State}
    (hok : ∀ s p, (ok s p).fs = s.fs) (hfail : ∀ s, (fail s).fs = s.fs) :
    ∀ s, (E2E.bumpThen size align ok fail s).fs = s.fs := by
  intro s
  unfold E2E.bumpThen
  split
  · rw [hok, State.fs_setMem]
  · exact hfail s

theorem allocFail_fs : ∀ s, (E2E.allocFail s).fs = s.fs := by
  intro s
  simp [E2E.allocFail, retHook]

theorem hookNoop_fs : ∀ s, (hookNoop s).fs = s.fs := by
  intro s
  simp [hookNoop, retHook]

theorem allocHook0_fs : ∀ s, (E2E.allocHook0 s).fs = s.fs := by
  intro s
  unfold E2E.allocHook0
  exact bumpThen_fs (fun _ _ => by simp [retHook]) allocFail_fs s

theorem deallocHook_fs : ∀ s, (E2E.deallocHook s).fs = s.fs := hookNoop_fs

theorem reallocHook0_fs : ∀ s, (E2E.reallocHook0 s).fs = s.fs := by
  intro s
  unfold E2E.reallocHook0
  exact bumpThen_fs (fun _ _ => by simp [retHook]) allocFail_fs s

theorem hookMemset_fs : ∀ s, (hookMemset s).fs = s.fs := by
  intro s
  simp [hookMemset, retHook]

theorem hookMemcpy_fs : ∀ s, (hookMemcpy s).fs = s.fs := by
  intro s
  simp [hookMemcpy, retHook]

theorem hookMemmove_fs : ∀ s, (hookMemmove s).fs = s.fs := hookMemcpy_fs

/-! ## Stub Plumbing on `mProg img (cliExterns W)` -/

theorem shim_row (W : CliHooks) : (shimName, hookNoop) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 0) rfl)

theorem alloc_row (W : CliHooks) : (allocName, E2E.allocHook0) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 1) rfl)

theorem dealloc_row (W : CliHooks) : (deallocName, E2E.deallocHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 2) rfl)

theorem realloc_row (W : CliHooks) : (reallocName, E2E.reallocHook0) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 3) rfl)

theorem memset_row (W : CliHooks) : (memsetName, hookMemset) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 5) rfl)

theorem memmove_row (W : CliHooks) : (memmoveName, hookMemmove) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 6) rfl)

theorem memcpy_row (W : CliHooks) : (memcpyName, hookMemcpy) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 7) rfl)

/-- Bundle of `HookOk` witnesses for `allocHook0`, `deallocHook`, and `reallocHook0` at `A`. -/
structure CliAllocHooks (A : RustAlloc) : Prop where
  alloc : HookOk E2E.allocHook0 (rustAllocSpec A)
  dealloc : HookOk E2E.deallocHook (rustDeallocSpec A)
  realloc : HookOk E2E.reallocHook0 (rustReallocSpec A)

theorem cliAllocHooks_A0 : CliAllocHooks E2E.HooksE.A0 where
  alloc := E2E.HooksE.allocHook0_ok
  dealloc := E2E.HooksE.deallocHook_ok
  realloc := E2E.HooksE.reallocHook0_ok

theorem allocHookStack_le_extHookStack : allocHookStack ≤ extHookStack := by decide

theorem extHookStack_le : extHookStack ≤ 2 ^ 64 := by decide

theorem pos_of_extHookStack_le {stk : Nat} (h : extHookStack ≤ stk) : 0 < stk :=
  Nat.lt_of_lt_of_le (by decide) h

theorem cli_hookSat_memcpy_region_ro (W : CliHooks) :
    HookSat (cliExterns W) memcpyName CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec :=
  ⟨hookMemcpy, cliExterns_row W (memcpy_row W),
    CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok⟩

end CryptoVerification.SignalSession.Cli.MainHops

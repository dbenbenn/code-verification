/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Heap.IfaceBudget
import ProofLib.Process.OracleEq
import ProofLib.BV.Bits
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Ghost `memmove` Hook and Bounded Consumer `HookOk` Suite (`HooksDehook.MemmoveGhost`)

Defines the `memmove` ghost hooks and consumer `HookOk` lifts for the `("memmove", f)` entry in
`CliGhostHooks.extra`:

1. Ghost `memmove` hooks (`memmoveGhostFn`, `memmoveGhostFnK`, `memmoveGhostPure`, `memmoveGhostPureK`):
   - `memmoveGhostFn keepR P_real P_sub entry`: wraps `MemmoveCode.masterMemmoveSpec` via
     `linkedCallHook` with the `W`-independent fallback `hookMemmove`.
   - `memmoveGhostFnK keepR P_real P_sub entry`: wraps the `K`-narrowed contract
     `memmoveSpecK keepR masterMemmoveSpec` via `linkedCallHook` with fallback `hookMemmove`.
   - `keepR : BitVec 64 → Bool` stays generic, with canonical `.text.b_pre` hull predicate
     `keepBPreHull m` (`[m, m + 956)`, `rfl`-identical to `TrapSafeWords.keepBlock m 956`) over the
     `239`-word (`956` B) `.text.b_pre` hull `bPreHullWords m resolve padWord` entered at
     `m + bPreMemmoveByteOff` (`= m + 660#64`).
2. State, frame, `oracle`, `AllocCallPreserved`, and `TrapRetHook` properties:
   - Unconditional (`0` `hasWords` / `svc` premises): `*_fs`, `*_fsT` (`HookFsTraced IsFsC`),
     `*_symtab`, `*_keepLr_false_of_noException` (`K`), `*_of_keepLr_true`, and
     `trapRetHook_memmoveGhostFn{,K}` (`TrapRetHook L f` when `keepR L = true`).
   - Over the `239`-word `bPreHullWords m resolve padWord` hull: `VmPreserved` (recovered across
     `stripS keepR` via `MemmoveCode.stdMemmoveSpec`), `OomPreserved ∧ PoolPreserved`,
     `.oracle = s0.oracle`, `AllocCallPreserved`, and `.trace = s0.trace`.
3. Bounded consumer `HookOk` suite (plain, `K`, budget, `withAlloc`):
   Real `libc.a` `memmove` (`masterMemmoveSpec`) requires `MemmoveArithBound` (`base.toNat + len ≤
   2^64 ∧ len < 2^63`) because forward/backward end-pointer calculation `d + n` / `s + n` wraps
   modulo `2^64` otherwise. Consumer `*Sat` chains use bounded `*MemmoveBounded*` contracts, so
   this module proves plain, `K`-narrowed, `withVmPreserved`, and `withAlloc A lim` `HookOk`
   lemmas across `libcMemmoveBoundedSpec`, `sessionMemmoveBoundedSpec`,
   `sessionMemmoveBoundedBudgetSpec`, `sessionMemmoveBoundedAcpSpec`, and
   `withAllocVmPreserved (sessionMemmoveBoundedSpec stk)` for arbitrary `stk : Nat` (`memmove` is
   a `0`-stack frameless leaf).

## Architecture of the 3-Entry `.text.b_pre` Hull

The single-`P_sub` `.text.b_pre` hull `[m, m + 956)` (`239` words) spans `memcpy` (`99` words at
`m`), `padWord` (`1` word at `m + 396`), `memset` (`65` words at `m + 400`), and `memmove` (`74`
words at `m + 660`). On `P_ghost := cliProgExtPlacedAt mpl extFn 617 W`, `resolve mpl "memcpy"` and
`resolve mpl "memset"` carry active hooks `g.memcpy` and `g.memset`, so a naive interior-unhooked
hypothesis fails; moreover `g.memcpy` / `g.memset` may use narrow `keepMemcpyBlk20` (`396` B) /
`keepMemsetBlk21` (`260` B) predicates where `keep L = false` on `[m + 660, m + 956)`.

This is handled across `MemmoveGhost{,K,Replays}`, `MemmoveLrTrap`, and `MemmoveExtraReplays`:
1. Internal ghost execution (`MemmoveGhostK.f3EmptyMemmoveGhostHook{,K}`): instantiates
   `P_real := MemsetGhostK.emptyStdProg` (`= Program.ofSvc Syscall.standard`), where
   `externAt? pc = none` unconditionally. Thus active `g.memcpy` / `g.memset` hooks never intercept
   the internal `memmove → b memcpy` jump, and the `HookOk` and `visitedIn` theorems need no
   `P_ghost` extern premises.
2. Call-site `CodeLoaded`: in `MemmoveGhostReplays`, `hInvLoaded` evaluates
   `P_sub.CodeLoaded (stripExecOutside keepR u.mem)` at the call-site state `u.mem` (not `s0.mem`),
   discharged via `f3CodeInv_rxWords_codeLoaded_strip` and transported across `hSteps.keepsFrozen`.
3. Outer `Steps P_ghost` `lr`-trap: `MemmoveGhostReplays` exports
   `f3EmptyMemmoveGhostHook_replaysOn_of_lrOut` and `bPreHull3_reg_ext_of_entries` with premises
   matching `Lib2LayoutFacts` over `["memmove", "memcpy", "memset"]`:
   - Off-entry pcs in `keepBPreHull m` have `P_ghost.externAt? pc = none`.
   - The 3 entry pcs carry `TrapRetHook L`:
     - `"memmove"` for `keepBPreHull m L = true` via `trapRetHook_f3EmptyMemmoveGhostHook{,K}`;
     - `"memcpy"` and `"memset"` for all `L` via `trapRetHook_linkedCallHook_of_hookOk_and_lr` and
       `MemcpyLrTrap` / `MemsetLrTrap` leaf `lr`-preservation.
   - At the `0#32` alignment pad (`m + 396`), `decode 0#32 = none`, so `fetchMem` returns `none`
     and `Step.halt_unmapped` transitions to `.Halted`, ruled out by `sf.status ≠ .Halted` in
     `MemmoveLrTrap.trap_impossible`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (StdStatePreserved)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FdsHiFrame OomPreserved PoolPreserved
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
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen
  satisfies_stripExecOutside stepsUntil_of_stripS_standard
  SpecStripSInvariant SpecPreservesFsTrace keepFsTrace
  ActiveRealPre ActiveRealRun
  linkedCallHook linkedCallHook_fs linkedCallHook_fsT linkedCallHook_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  withAlloc hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  pureWordsProg_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  hookOk_map_frame_pureAbort
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  withExecFrozen hookOk_withExecFrozen_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode (
  MemmoveStatePreserved
  masterMemmoveSpec stdMemmoveSpec stdMemmove_pre_eq memmoveSpecK
  masterMemmoveSpec_stripSInvariant masterMemmoveSpecK_stripSInvariant
  masterMemmoveSpec_preservesFsTrace masterMemmoveSpecK_preservesFsTrace
  masterMemmoveSpec_pre_setPC masterMemmoveSpecK_pre_setPC
  masterMemmoveSpec_outcome_setPC masterMemmoveSpecK_outcome_setPC
  bPrePadWord bPreMemsetByteOff bPreMemmoveByteOff
  bPreMemsetByteOff_eq bPreMemmoveByteOff_eq bPreHullWords
  pureWordsProg_bPreHull_hasWords
  subroutine_ok_bPreHull_stdMemmove_of_hasWords
  subroutine_ok_bPreHull_masterMemmove_of_hasWords
  subroutine_ok_bPreHull_masterMemmoveK_of_hasWords
  hookMemmove_processFieldsPreserved hookMemmove_oracle_eq hookMemmove_symtab_eq
  keepFsTrace_hookMemmove_eq
  hookMemmove_masterMemmove_ok hookMemmove_masterMemmoveK_ok
  hookOk_memmoveSpecK_of_plain hookOk_memmoveSpecK_map_frame_pureAbort
  sessionMemmoveBoundedAcpSpec
  hookOk_libcMemmoveBounded_of_master
  hookOk_withVmPreserved_libcMemmoveBounded_of_master
  hookOk_sessionMemmoveBounded_of_master
  hookOk_sessionMemmoveBounded_keepsFs_of_master
  hookOk_sessionMemmoveBoundedBudget_of_master
  hookOk_sessionMemmoveBoundedAcp_of_master
  hookOk_allocVmPreserved_sessionMemmoveBounded_of_master
  hookOk_withAlloc_masterMemmove_of_master hookOk_withAlloc_masterMemmoveVm_of_master
  hookOk_withAlloc_libcMemmoveBounded_of_master
  hookOk_withAlloc_sessionMemmoveBounded_of_master
  hookOk_withAlloc_sessionMemmoveBoundedBudget_of_master
  hookOk_withAlloc_sessionMemmoveBoundedAcp_of_master
  hookOk_withAlloc_allocVmPreserved_sessionMemmoveBounded_of_master
  memmoveSpecK_withVmPreserved
  TrapRetHook trapRetHook_hookMemmove
  trapRetHook_linkedCallHook_of_keepLr trapRetHook_linkedCallHook_memmoveSpecK
)

/-! ## 0. `.text.b_pre` Hull Predicate (`keepBPreHull`) & Spec-Wrapper Commutations -/

/-- Canonical `956`-byte (`239`-word) `.text.b_pre` hull predicate `[m, m + 956)` (`rfl`-identical
    to `TrapSafeWords.keepBlock m 956`). -/
@[expose] def keepBPreHull (m : BitVec 64) (pc : BitVec 64) : Bool :=
  decide ((pc - m).toNat < 956)

theorem keepBPreHull_of_offset (m : BitVec 64) {off : Nat} (hoff : off < 956) :
    keepBPreHull m (m + BitVec.ofNat 64 off) = true := by
  unfold keepBPreHull
  rw [decide_eq_true_eq]
  have hsub : m + BitVec.ofNat 64 off - m = BitVec.ofNat 64 off := by bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hoff

theorem keepBPreHull_memcpyEntry (m : BitVec 64) : keepBPreHull m m = true := by
  simpa using keepBPreHull_of_offset m (off := 0) (by decide)

theorem keepBPreHull_memsetEntry (m : BitVec 64) :
    keepBPreHull m (m + bPreMemsetByteOff) = true := by
  rw [bPreMemsetByteOff_eq]
  exact keepBPreHull_of_offset m (off := 400) (by decide)

theorem keepBPreHull_memmoveEntry (m : BitVec 64) :
    keepBPreHull m (m + bPreMemmoveByteOff) = true := by
  rw [bPreMemmoveByteOff_eq]
  exact keepBPreHull_of_offset m (off := 660) (by decide)

/-- `Arm64.Spec.keepsFs` (`Callees.lean`) and `HookDischarge.Libc.Common.keepsFs` are `rfl`-equal. -/
theorem spec_keepsFs_eq_common {α : Type} (spec : Spec α) :
    spec.keepsFs = keepsFs spec := rfl

/-- `memmoveSpecK keepR` commutes with `WithAlloc.withAlloc A lim` by `sepConj_assoc`. -/
theorem memmoveSpecK_withAlloc (keepR : BitVec 64 → Bool) {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    memmoveSpecK keepR (withAlloc (M := M) A lim spec) =
      withAlloc (M := M) A lim (memmoveSpecK keepR spec) := by
  unfold memmoveSpecK withAlloc
  congr 1
  funext ⟨x, st⟩ s
  exact (sepConj_assoc _ _ _).symm

/-- `memmoveSpecK keepR` commutes with `withOomPoolPreserved` by `rfl`. -/
theorem memmoveSpecK_withOomPoolPreserved (keepR : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    memmoveSpecK keepR (withOomPoolPreserved spec) =
      withOomPoolPreserved (memmoveSpecK keepR spec) := rfl

/-! ## 1. Ghost `memmove` Hook Definitions (`memmoveGhostFn`, `memmoveGhostFnK`, Pure Hull Forms) -/

/-- Plain ghost `memmove` hook wrapping `masterMemmoveSpec` via `linkedCallHook` with `W`-free
    fallback `hookMemmove`. Parametric in `keepR`, `P_real`, `P_sub`, and `entry`. -/
@[expose] noncomputable def memmoveGhostFn
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    State → State :=
  linkedCallHook keepR P_real P_sub entry masterMemmoveSpec hookMemmove

/-- `K`-narrowed ghost `memmove` hook wrapping `memmoveSpecK keepR masterMemmoveSpec` via
    `linkedCallHook` with fallback `hookMemmove`. Outside `keepR (s.readReg64 .lr) = false` (or when
    `masterMemmoveSpec.pre` fails), transitions to `.Exception` so any non-`.Exception` ghost run
    automatically witnesses `keepR (u.readReg64 .lr) = false` at every call site. -/
@[expose] noncomputable def memmoveGhostFnK
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    State → State :=
  linkedCallHook keepR P_real P_sub entry (memmoveSpecK keepR masterMemmoveSpec) hookMemmove

/-- Concrete single-`P_sub` `.text.b_pre` pure-words specialization of `memmoveGhostFn` over
    `pureWordsProg m (bPreHullWords m resolve padWord)` entered at `m + bPreMemmoveByteOff`. -/
noncomputable abbrev memmoveGhostPure
    (keepR : BitVec 64 → Bool) (P_real : Program) (m : BitVec 64)
    (resolve : String → BitVec 64) (padWord : BitVec 32 := bPrePadWord) :
    State → State :=
  memmoveGhostFn keepR P_real (pureWordsProg m (bPreHullWords m resolve padWord))
    (m + bPreMemmoveByteOff)

/-- Concrete single-`P_sub` `.text.b_pre` pure-words specialization of `memmoveGhostFnK`. -/
noncomputable abbrev memmoveGhostPureK
    (keepR : BitVec 64 → Bool) (P_real : Program) (m : BitVec 64)
    (resolve : String → BitVec 64) (padWord : BitVec 32 := bPrePadWord) :
    State → State :=
  memmoveGhostFnK keepR P_real (pureWordsProg m (bPreHullWords m resolve padWord))
    (m + bPreMemmoveByteOff)

theorem keepFsTrace_hookMemmove_master_ok :
    HookOk (keepFsTrace hookMemmove) masterMemmoveSpec := by
  have hfn : keepFsTrace hookMemmove = hookMemmove := funext keepFsTrace_hookMemmove_eq
  rw [hfn]
  exact hookMemmove_masterMemmove_ok

theorem keepFsTrace_hookMemmove_masterK_ok (keepR : BitVec 64 → Bool) :
    HookOk (keepFsTrace hookMemmove) (memmoveSpecK keepR masterMemmoveSpec) := by
  have hfn : keepFsTrace hookMemmove = hookMemmove := funext keepFsTrace_hookMemmove_eq
  rw [hfn]
  exact hookMemmove_masterMemmoveK_ok keepR

/-! ## 2. Master `HookOk` & Pointwise State / Frame / Trap Properties -/

/-- `memmoveGhostFn` preserves `State.fs` unconditionally. -/
theorem memmoveGhostFn_fs
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) (s0 : State) :
    (memmoveGhostFn keepR P_real P_sub entry s0).fs = s0.fs :=
  linkedCallHook_fs keepR P_real P_sub entry masterMemmoveSpec hookMemmove s0

/-- `memmoveGhostFnK` preserves `State.fs` unconditionally. -/
theorem memmoveGhostFnK_fs
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) (s0 : State) :
    (memmoveGhostFnK keepR P_real P_sub entry s0).fs = s0.fs :=
  linkedCallHook_fs keepR P_real P_sub entry (memmoveSpecK keepR masterMemmoveSpec) hookMemmove s0

/-- Unconditional `.symtab` preservation for `linkedCallHook` whenever `(fallback s0).symtab = s0.symtab`. -/
theorem linkedCallHook_symtab_eq {α : Type}
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64)
    (spec : Spec α) (fallback : State → State)
    (hfb_sym : ∀ s : State, (fallback s).symtab = s.symtab) (s0 : State) :
    (linkedCallHook keepR P_real P_sub entry spec fallback s0).symtab = s0.symtab := by
  classical
  unfold linkedCallHook
  split
  · split
    · rename_i hReal
      have hsteps := (Classical.choose_spec hReal.2.2.2).1.toSteps
      have hsym : (Classical.choose hReal.2.2.2).symtab = (s0.setPC entry).symtab := hsteps.symtab_eq
      have hpc_sym : (s0.setPC entry).symtab = s0.symtab := by cases s0; rfl
      exact hsym.trans hpc_sym
    · change (keepFsTrace fallback s0).symtab = s0.symtab
      unfold keepFsTrace
      exact hfb_sym s0
  · rfl

/-- `memmoveGhostFn` preserves `State.symtab` unconditionally. -/
theorem memmoveGhostFn_symtab
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) (s0 : State) :
    (memmoveGhostFn keepR P_real P_sub entry s0).symtab = s0.symtab :=
  linkedCallHook_symtab_eq keepR P_real P_sub entry masterMemmoveSpec hookMemmove
    hookMemmove_symtab_eq s0

/-- `memmoveGhostFnK` preserves `State.symtab` unconditionally. -/
theorem memmoveGhostFnK_symtab
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) (s0 : State) :
    (memmoveGhostFnK keepR P_real P_sub entry s0).symtab = s0.symtab :=
  linkedCallHook_symtab_eq keepR P_real P_sub entry (memmoveSpecK keepR masterMemmoveSpec)
    hookMemmove hookMemmove_symtab_eq s0

/-- Master `HookOk` of `memmoveGhostFn` for `masterMemmoveSpec`, over any hook-free `P_sub` holding
    the `239`-word `.text.b_pre` hull `bPreHullWords m resolve padWord` at `m`, entered at
    `m + bPreMemmoveByteOff` (`= m + 660#64`). -/
theorem memmoveGhostFn_master_ok
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff)) masterMemmoveSpec :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_bPreHull_masterMemmove_of_hasWords hsub_no hhull hres)
    (masterMemmoveSpec_stripSInvariant keepR)
    masterMemmoveSpec_preservesFsTrace
    masterMemmoveSpec_pre_setPC
    masterMemmoveSpec_outcome_setPC
    keepFsTrace_hookMemmove_master_ok

/-- Master `HookOk` of `memmoveGhostFnK` for `memmoveSpecK keepR masterMemmoveSpec`, over any
    hook-free `P_sub` holding `bPreHullWords m resolve padWord` at `m`. -/
theorem memmoveGhostFnK_masterK_ok
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl) :
    HookOk (memmoveGhostFnK keepR P_real P_sub (m + bPreMemmoveByteOff))
      (memmoveSpecK keepR masterMemmoveSpec) :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_bPreHull_masterMemmoveK_of_hasWords keepR hsub_no hhull hres)
    (masterMemmoveSpecK_stripSInvariant keepR keepR)
    (masterMemmoveSpecK_preservesFsTrace keepR)
    (masterMemmoveSpecK_pre_setPC keepR)
    (masterMemmoveSpecK_outcome_setPC keepR)
    (keepFsTrace_hookMemmove_masterK_ok keepR)

private theorem perm_eq_of_stripExecOutside_keepsFrozen
    {keepR : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64,
      (stripExecOutside keepR mf).perm a = (stripExecOutside keepR m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := by
  intro a
  have hst := hstrip a
  rw [strip_perm, strip_perm] at hst
  have hfr0_a := hfr0 a
  have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a with
    | none =>
      cases hpf : mf.perm a with
      | none => rfl
      | some pf =>
        rw [hp0, hpf] at hst
        simp [Option.map] at hst
    | some p0 =>
      cases hpf : mf.perm a with
      | none =>
        rw [hp0, hpf] at hst
        simp [Option.map] at hst
      | some pf =>
        rw [hp0] at hfr0_a hfrozen0 hst
        rw [hpf] at hfrf_a hst
        rcases p0 with ⟨r0, w0, x0, lf0, an0⟩
        rcases pf with ⟨rf, wf, xf, lff, anf⟩
        unfold stripPerm at hst
        cases hk : keepR a <;> cases r0 <;> cases w0 <;> cases x0 <;>
          cases rf <;> cases wf <;> cases xf <;>
          simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem subroutineStop_of_stdMemmoveOutcome
    {x : BitVec 64 × List (BitVec 8) × Nat × Nat × Nat} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome stdMemmoveSpec x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine ⟨Or.inl hret, ?_⟩
    rw [hret.2.2]; decide
  · dsimp only [stdMemmoveSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [stdMemmoveSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [stdMemmoveSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

private theorem activeRealRun_stdStatePreserved_and_oracle
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : subroutine_ok P_sub entry stdMemmoveSpec)
    {x : BitVec 64 × List (BitVec 8) × Nat × Nat × Nat} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpreM : s0.mem ⊨ masterMemmoveSpec.pre x s0 ∗ R)
    (hReal : ActiveRealRun keepR P_real P_sub entry s0) :
    StdStatePreserved s0 (Classical.choose hReal.2.2.2) ∧
      (Classical.choose hReal.2.2.2).oracle = s0.oracle := by
  let s1 := s0.setPC entry
  let s1' := stripS keepR s1
  have hs1_pre : s1.mem ⊨ stdMemmoveSpec.pre x s1 ∗ R := by
    cases x; cases s0; exact hpreM
  have hs1'_pre : s1'.mem ⊨ stdMemmoveSpec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keepR hs1_pre
    have heq : stdMemmoveSpec.pre x s1' = stdMemmoveSpec.pre x s1 := by
      dsimp only [s1']
      cases x; cases s1; rfl
    rwa [heq]
  have hs1'_sp : s1'.spAligned = true := hsp
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hrun hs1'_pre hs1'_sp hReal.2.2.1
  obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_stdMemmoveOutcome hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0)
      hsvc_real hsvc_sub hreal_no
      (fun pc f he => nomatch hsub_no pc ▸ he)
      hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hdet : Classical.choose hReal.2.2.2 = sf :=
    StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
  rw [hdet]
  have horc' : sf'.oracle = s1'.oracle := Steps.oracle_eq_of_standard hsvc_sub hsub_no hsteps'
  rw [hsf_eq] at horc'
  have horc : sf.oracle = s0.oracle := by
    dsimp only [s1', s1] at horc'
    cases s0; cases sf; exact horc'
  rcases hout' with ⟨_, _, hpost'⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · rcases x with ⟨base, buf, dst, src, len⟩
    change sf'.mem ⊨
      (⌜sf'.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧ StdStatePreserved s1' sf'⌝ ∗
        (base ↦ₛ ProofLib.listMove buf dst src len)) ∗ R at hpost'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    have hstd' : StdStatePreserved s1' sf' := hpost'.1.2
    rw [hsf_eq] at hstd'
    have hperm : ∀ a, sf.mem.perm a = s0.mem.perm a :=
      perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf huntil.toSteps.keepsFrozen
        hstd'.2.2.2.2.2.2.2
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hperm⟩, horc⟩
    · cases s0; cases sf; exact hstd'.1
    · cases s0; cases sf; exact hstd'.2.1
    · cases s0; cases sf; exact hstd'.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.2.2.2.1
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem vmPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

private theorem oomPoolPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : OomPreserved s0 sf ∧ PoolPreserved s0 sf :=
  ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

/-- Pointwise `StdStatePreserved` (= `ProcessFieldsPreserved`) for `memmoveGhostFn` across all
    three branches (`ActiveRealRun`, fallback `hookMemmove`, and `.Exception`). -/
theorem memmoveGhostFn_stdStatePreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    StdStatePreserved s0 (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff) s0) := by
  classical
  unfold memmoveGhostFn linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
        (subroutine_ok_bPreHull_stdMemmove_of_hasWords hsub_no hhull hres) hrun hsp hpre hReal).1
    · rw [keepFsTrace_hookMemmove_eq]
      exact hookMemmove_processFieldsPreserved s0
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- Pointwise `StdStatePreserved` for `memmoveGhostFnK` across all three branches. -/
theorem memmoveGhostFnK_stdStatePreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    StdStatePreserved s0 (memmoveGhostFnK keepR P_real P_sub (m + bPreMemmoveByteOff) s0) := by
  classical
  unfold memmoveGhostFnK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memmoveSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
        (subroutine_ok_bPreHull_stdMemmove_of_hasWords hsub_no hhull hres) hrun hsp hpre.2 hReal).1
    · rw [keepFsTrace_hookMemmove_eq]
      exact hookMemmove_processFieldsPreserved s0
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- Pointwise `VmPreserved` for `memmoveGhostFn`. -/
theorem memmoveGhostFn_vmPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    VmPreserved s0 (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff) s0) :=
  vmPreserved_of_stdStatePreserved
    (memmoveGhostFn_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0)

/-- Pointwise `VmPreserved` for `memmoveGhostFnK`. -/
theorem memmoveGhostFnK_vmPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    VmPreserved s0 (memmoveGhostFnK keepR P_real P_sub (m + bPreMemmoveByteOff) s0) :=
  vmPreserved_of_stdStatePreserved
    (memmoveGhostFnK_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0)

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `memmoveGhostFn`. -/
theorem memmoveGhostFn_oomPoolPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    OomPreserved s0 (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff) s0) ∧
      PoolPreserved s0 (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff) s0) :=
  oomPoolPreserved_of_stdStatePreserved
    (memmoveGhostFn_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0)

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `memmoveGhostFnK`. -/
theorem memmoveGhostFnK_oomPoolPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    OomPreserved s0 (memmoveGhostFnK keepR P_real P_sub (m + bPreMemmoveByteOff) s0) ∧
      PoolPreserved s0 (memmoveGhostFnK keepR P_real P_sub (m + bPreMemmoveByteOff) s0) :=
  oomPoolPreserved_of_stdStatePreserved
    (memmoveGhostFnK_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0)

/-- Pointwise `.oracle = s0.oracle` for `memmoveGhostFn` (requiring `externAt? = none` only on
    `keepR`, not globally on `P_real`). -/
theorem memmoveGhostFn_oracle
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff) s0).oracle = s0.oracle := by
  classical
  unfold memmoveGhostFn linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
        (subroutine_ok_bPreHull_stdMemmove_of_hasWords hsub_no hhull hres) hrun hsp hpre hReal).2
    · rw [keepFsTrace_hookMemmove_eq]
      exact hookMemmove_oracle_eq s0
  · rfl

/-- Pointwise `.oracle = s0.oracle` for `memmoveGhostFnK`. -/
theorem memmoveGhostFnK_oracle
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    (memmoveGhostFnK keepR P_real P_sub (m + bPreMemmoveByteOff) s0).oracle = s0.oracle := by
  classical
  unfold memmoveGhostFnK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memmoveSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
        (subroutine_ok_bPreHull_stdMemmove_of_hasWords hsub_no hhull hres) hrun hsp hpre.2 hReal).2
    · rw [keepFsTrace_hookMemmove_eq]
      exact hookMemmove_oracle_eq s0
  · rfl

/-- Pointwise `AllocCallPreserved` for `memmoveGhostFn`. -/
theorem memmoveGhostFn_allocCallPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    AllocCallPreserved s0 (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff) s0) :=
  (MemmoveStatePreserved.of_stdStatePreserved
    (memmoveGhostFn_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0)).toAllocCallPreserved
    (memmoveGhostFn_oracle hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0)
    (memmoveGhostFn_symtab keepR P_real P_sub (m + bPreMemmoveByteOff) s0)

/-- Pointwise `AllocCallPreserved` for `memmoveGhostFnK`. -/
theorem memmoveGhostFnK_allocCallPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    AllocCallPreserved s0 (memmoveGhostFnK keepR P_real P_sub (m + bPreMemmoveByteOff) s0) :=
  (MemmoveStatePreserved.of_stdStatePreserved
    (memmoveGhostFnK_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0)).toAllocCallPreserved
    (memmoveGhostFnK_oracle hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0)
    (memmoveGhostFnK_symtab keepR P_real P_sub (m + bPreMemmoveByteOff) s0)

/-- Pointwise `.trace = s0.trace` for `memmoveGhostFn`. -/
theorem memmoveGhostFn_trace
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff) s0).trace = s0.trace :=
  (memmoveGhostFn_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0).1.2.1

/-- Pointwise `.trace = s0.trace` for `memmoveGhostFnK`. -/
theorem memmoveGhostFnK_trace
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (s0 : State) :
    (memmoveGhostFnK keepR P_real P_sub (m + bPreMemmoveByteOff) s0).trace = s0.trace :=
  (memmoveGhostFnK_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0).1.2.1

/-- Along any non-`.Exception` call step of `memmoveGhostFnK`, `keepR (u.readReg64 .lr) = false`
    holds automatically (`K`-route `lr ∉ keepR` extractor). -/
theorem memmoveGhostFnK_keepLr_false_of_noException
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {u : State}
    (hnoex : ∀ msg, (memmoveGhostFnK keepR P_real P_sub entry u).status ≠ .Exception msg) :
    keepR (u.readReg64 .lr) = false := by
  classical
  have hActPre : ActiveRealPre (memmoveSpecK keepR masterMemmoveSpec) u := by
    by_contra hnAct
    have hex : (memmoveGhostFnK keepR P_real P_sub entry u).status =
        .Exception "ghost-hook precondition violated" := by
      unfold memmoveGhostFnK linkedCallHook
      simp [hnAct]
    exact hnoex _ hex
  rcases hActPre with ⟨_, _, x, R, hpre⟩
  dsimp only [memmoveSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Behavior of plain `memmoveGhostFn` when `keepR (s0.readReg64 .lr) = true` and
    `ActiveRealPre masterMemmoveSpec s0` holds: `ActiveRealRun` is false, so `linkedCallHook`
    delegates to `keepFsTrace hookMemmove s0 = hookMemmove s0`. -/
theorem memmoveGhostFn_of_keepLr_true
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {s0 : State}
    (hActPre : ActiveRealPre masterMemmoveSpec s0)
    (hlr_in : keepR (s0.readReg64 .lr) = true) :
    memmoveGhostFn keepR P_real P_sub entry s0 = hookMemmove s0 := by
  classical
  have hnReal : ¬ ActiveRealRun keepR P_real P_sub entry s0 := by
    intro hReal
    have hfalse : keepR (s0.readReg64 .lr) = false := hReal.2.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold memmoveGhostFn linkedCallHook
  simp only [hActPre, hnReal, ↓reduceDIte]
  exact keepFsTrace_hookMemmove_eq s0

/-- Behavior of `K`-narrowed `memmoveGhostFnK` when `keepR (s0.readReg64 .lr) = true`:
    `ActiveRealPre (memmoveSpecK keepR masterMemmoveSpec) s0` is false regardless of memory
    contents, so `linkedCallHook` transitions to `.Exception "ghost-hook precondition violated"`. -/
theorem memmoveGhostFnK_of_keepLr_true
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {s0 : State}
    (hlr_in : keepR (s0.readReg64 .lr) = true) :
    memmoveGhostFnK keepR P_real P_sub entry s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  classical
  have hnAct : ¬ ActiveRealPre (memmoveSpecK keepR masterMemmoveSpec) s0 := by
    rintro ⟨_, _, x, R, hpre⟩
    dsimp only [memmoveSpecK] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    have hfalse : keepR (s0.readReg64 .lr) = false := hpre.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold memmoveGhostFnK linkedCallHook
  simp only [hnAct, ↓reduceDIte]

/-- `TrapRetHook L` (`rfl`-identical to `TrapSafeWords.TrapHook L`) for plain `memmoveGhostFn`
    whenever `keepR L = true` (`MemmoveCode.lean:1110`). -/
theorem trapRetHook_memmoveGhostFn
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapRetHook L (memmoveGhostFn keepR P_real P_sub entry) :=
  trapRetHook_linkedCallHook_of_keepLr hkeepL (trapRetHook_hookMemmove L)

/-- `TrapRetHook L` (`rfl`-identical to `TrapSafeWords.TrapHook L`) for `K`-narrowed
    `memmoveGhostFnK` whenever `keepR L = true` (`MemmoveCode.lean:1140`). -/
theorem trapRetHook_memmoveGhostFnK
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapRetHook L (memmoveGhostFnK keepR P_real P_sub entry) :=
  trapRetHook_linkedCallHook_memmoveSpecK hkeepL

/-! ## 3. Complete Bounded Consumer `HookOk` Suite (Plain, `keepsFs`, Budget, `withAlloc`, & `K`) -/

section GenericHookOkSuite

variable {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
variable {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
variable (hres : resolve "memcpy" = m)

include hsvc_real hsvc_sub hreal_no hsub_no hhull hres

-- 3.1 Master / `stdMemmoveSpec` / `withVmPreserved masterMemmoveSpec` arms:

theorem memmoveGhostFn_stdMemmove_ok :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff)) stdMemmoveSpec := by
  refine hookOk_map_frame_pureAbort id (fun _ _ => emp)
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (fun _ _ => by rw [sepConj_emp]; exact Entails.refl _)
    (fun ⟨base, buf, dst, src, len⟩ s0 sf hsf _ => ?_)
  subst hsf
  dsimp only [masterMemmoveSpec, stdMemmoveSpec, id]
  rw [sepConj_emp]
  exact Entails.pure_left fun ⟨hx0, _⟩ =>
    Entails.pure_right
      ⟨hx0, memmoveGhostFn_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0⟩
      (Entails.refl _)

theorem memmoveGhostFnK_stdMemmoveK_ok :
    HookOk (memmoveGhostFnK keepR P_real P_sub (m + bPreMemmoveByteOff))
      (memmoveSpecK keepR stdMemmoveSpec) := by
  refine hookOk_memmoveSpecK_map_frame_pureAbort keepR id (fun _ _ => emp)
    (memmoveGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (fun _ _ => by rw [sepConj_emp]; exact Entails.refl _)
    (fun ⟨base, buf, dst, src, len⟩ s0 sf hsf _ => ?_)
  subst hsf
  dsimp only [masterMemmoveSpec, stdMemmoveSpec, id]
  rw [sepConj_emp]
  exact Entails.pure_left fun ⟨hx0, _⟩ =>
    Entails.pure_right
      ⟨hx0, memmoveGhostFnK_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0⟩
      (Entails.refl _)

theorem memmoveGhostFn_masterVm_ok :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withVmPreserved masterMemmoveSpec) :=
  hookOk_withVmPreserved
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem memmoveGhostFnK_masterVmK_ok :
    HookOk (memmoveGhostFnK keepR P_real P_sub (m + bPreMemmoveByteOff))
      (memmoveSpecK keepR (withVmPreserved masterMemmoveSpec)) := by
  rw [← memmoveSpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memmoveGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFnK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

-- 3.2 Plain non-budget & budget (`withVmPreserved` / `Acp` / `AllocVmPreserved`) consumer contracts:

theorem memmoveGhostFn_libcBounded_ok (stk : Nat := extHookStack) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (libcMemmoveBoundedSpec stk) :=
  hookOk_libcMemmoveBounded_of_master
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem memmoveGhostFn_libcBounded_budget_ok (stk : Nat := extHookStack) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withVmPreserved (libcMemmoveBoundedSpec stk)) :=
  hookOk_withVmPreserved_libcMemmoveBounded_of_master
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem memmoveGhostFn_sessionBounded_ok (stk : Nat := extHookStack) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (sessionMemmoveBoundedSpec stk) :=
  hookOk_sessionMemmoveBounded_of_master
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem memmoveGhostFn_sessionBounded_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (keepsFs (sessionMemmoveBoundedSpec stk)) :=
  hookOk_sessionMemmoveBounded_keepsFs_of_master
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem memmoveGhostFn_sessionBoundedBudget_ok (stk : Nat := extHookStack) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (sessionMemmoveBoundedBudgetSpec stk) :=
  hookOk_sessionMemmoveBoundedBudget_of_master
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem memmoveGhostFn_sessionBoundedBudget_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (keepsFs (sessionMemmoveBoundedBudgetSpec stk)) :=
  spec_keepsFs_eq_common (sessionMemmoveBoundedBudgetSpec stk) ▸
    (memmoveGhostFn_sessionBoundedBudget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres stk).keepsFs
      (memmoveGhostFn_fs keepR P_real P_sub (m + bPreMemmoveByteOff))

theorem memmoveGhostFn_sessionBoundedAcp_ok (stk : Nat := 4096) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (sessionMemmoveBoundedAcpSpec stk) :=
  hookOk_sessionMemmoveBoundedAcp_of_master
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_oracle hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem memmoveGhostFn_allocVmPreserved_sessionBounded_ok (stk : Nat := 0) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withAllocVmPreserved (sessionMemmoveBoundedSpec stk)) :=
  hookOk_allocVmPreserved_sessionMemmoveBounded_of_master
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_oracle hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

-- 3.3 Plain `withAlloc A lim` contracts on `memmoveGhostFn` (`GhostRowSpecOk` arms):

theorem memmoveGhostFn_master_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withAlloc (M := M) A lim masterMemmoveSpec) :=
  hookOk_withAlloc_masterMemmove_of_master A lim
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem memmoveGhostFn_masterVm_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withAlloc (M := M) A lim (withVmPreserved masterMemmoveSpec)) :=
  hookOk_withAlloc_masterMemmoveVm_of_master A lim
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem memmoveGhostFn_libcBounded_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := extHookStack) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withAlloc (M := M) A lim (libcMemmoveBoundedSpec stk)) :=
  hookOk_withAlloc_libcMemmoveBounded_of_master A lim
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem memmoveGhostFn_libcBounded_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := extHookStack) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withAlloc (M := M) A lim (withVmPreserved (libcMemmoveBoundedSpec stk))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (memmoveGhostFn_libcBounded_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres stk)

theorem memmoveGhostFn_sessionBounded_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := extHookStack) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withAlloc (M := M) A lim (sessionMemmoveBoundedSpec stk)) :=
  hookOk_withAlloc_sessionMemmoveBounded_of_master A lim
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem memmoveGhostFn_sessionBoundedBudget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := extHookStack) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withAlloc (M := M) A lim (sessionMemmoveBoundedBudgetSpec stk)) :=
  hookOk_withAlloc_sessionMemmoveBoundedBudget_of_master A lim
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem memmoveGhostFn_sessionBoundedAcp_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withAlloc (M := M) A lim (sessionMemmoveBoundedAcpSpec stk)) :=
  hookOk_withAlloc_sessionMemmoveBoundedAcp_of_master A lim
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_oracle hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem memmoveGhostFn_allocVmPreserved_sessionBounded_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 0) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withAlloc (M := M) A lim (withAllocVmPreserved (sessionMemmoveBoundedSpec stk))) :=
  hookOk_withAlloc_allocVmPreserved_sessionMemmoveBounded_of_master A lim
    (memmoveGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (memmoveGhostFn_oracle hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

-- 3.4 Generic combinators on `memmoveGhostFn` (`keepsFs`, `withOomPoolPreserved`, `withExecFrozen`, `memmoveSpecK`):

omit hsvc_real hsvc_sub hreal_no hsub_no hhull hres in
theorem memmoveGhostFn_any_keepsFs_ok {α : Type} {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (memmoveGhostFn keepR P_real P_sub entry) spec) :
    HookOk (memmoveGhostFn keepR P_real P_sub entry) (keepsFs spec) :=
  spec_keepsFs_eq_common spec ▸ hh.keepsFs (memmoveGhostFn_fs keepR P_real P_sub entry)

theorem memmoveGhostFn_any_withOomPoolPreserved_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff)) spec) :
    HookOk (memmoveGhostFn keepR P_real P_sub (m + bPreMemmoveByteOff))
      (withOomPoolPreserved spec) :=
  hookOk_withOomPoolPreserved hh
    (memmoveGhostFn_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

omit hsvc_real hsvc_sub hreal_no hsub_no hhull hres in
theorem memmoveGhostFn_any_execFrozen_ok {α : Type} {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (memmoveGhostFn keepR P_real P_sub entry) spec) :
    HookOk (memmoveGhostFn keepR P_real P_sub entry) (withExecFrozen spec) :=
  hookOk_withExecFrozen_of_plain hh

omit hsvc_real hsvc_sub hreal_no hsub_no hhull hres in
theorem memmoveGhostFn_any_memmoveSpecK_ok (keep' : BitVec 64 → Bool)
    {α : Type} {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (memmoveGhostFn keepR P_real P_sub entry) spec) :
    HookOk (memmoveGhostFn keepR P_real P_sub entry) (memmoveSpecK keep' spec) :=
  hookOk_memmoveSpecK_of_plain keep' hh

-- (`K`-narrowed consumer contracts on `memmoveGhostFnK` live in `HooksDehook.MemmoveGhostK` §1.)

end GenericHookOkSuite

/-! ## 4. Concrete `pureWordsProg m (bPreHullWords m resolve padWord)` Satisfiability Witnesses -/

/-! ## 5. Bundling into `GhostRowSpecOk`

`GhostRowSpecOk` lives in `Cli.Run.Slots.ExtraGhostSpecs` with the `"memmove"` row arm in
`ExtraRowSpecs.MemmoveRowSpec`. The bounded `HookOk` obligations proved in this module are
assembled into `memmoveGhost_rowSpecOk` in `HooksDehook.MemmoveExtraReplays`.
-/

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostK -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Closed-`lr` Trap & Subroutine-Outcome `keepStrlenRange lr = false` Suite (`HooksDehook.StrlenLrTrap`)

Card **I1-d** of the `strlen` de-hook row (`dehook_plan.md` §1, §5; C11 §8.2): proves that inside
the 88-byte (`22`-word) `libc.a` `muslStrlenWords` block at `entryTarget`, no execution path writes
`x30` (`lr`) or leaves `[entryTarget, entryTarget + 88)` except via `ret x30` to `lr`. Consequently,
whenever a ghost run starting with `keepStrlenRange entryTarget (s0.readReg64 .lr) = false`
terminates without `.Exception`/`.Halted` and (if `.Running`) returns to `s0.readReg64 .lr`, every
intermediate call site `u` satisfies `keepStrlenRange entryTarget (u.readReg64 .lr) = false`.

## Summary of Exported Results
1. **88 B `muslStrlenWords` Hull (`keepStrlenRange`, `strlenRegion`, `strlenRegion_wordsSafe`):**
   - Reuses `StrlenGhost.{strlenByteLen, keepStrlenRange, KeepCoversStrlen}` (`keepStrlenRange` is
     `rfl`-identical to `TrapSafeWords.keepBlock entryTarget strlenByteLen`) and lifts
     `TrapSafeWords.strlen_all_safe` (`22` words, zero new `decide` calls) to
     `RegionWordsSafe (strlenRegion entryTarget)` for any `entryTarget`.
2. **`TrapHook` Instances (Idealized Fallback, Plain Ghost, and `K` Ghost):**
   - `trapHook_strlenHook`, `trapHook_keepFsTrace_strlenHook` (`∀ L : BitVec 64`).
   - `trapHook_strlenGhostHook`, `trapHook_f3EmptyStrlenGhostHook` (plain `linkedCallHook` /
     `f3LinkedCallHook`) and `trapHook_strlenGhostHookK`, `trapHook_f3EmptyStrlenGhostHookK`
     (`K`-narrowed), plus `KeepCoversStrlen` corollaries (spec-independent; applies to every
     `StrlenGhost` consumer).
3. **Entry-Excluded Region Extern Adapters (`SPEC-PLANNER T2` + `REV-S2 F1`):**
   - `strlen_reg_ext_of_entry_excluded`, `strlen_reg_ext_forall_of_entry_excluded`, and single-entry
     `[entryTarget]` specializations allowing `P_ghost.externAt? entryTarget` to hold the ghost
     `strlen` hook itself while `externAt? pc = none` for `pc ≠ entryTarget`.
4. **Post-Hook Continuation & At-Stub `SubroutineOutcome` Trap Theorems for Card `c`:**
   - **Post-hook `u`-local (`InvS u`) & continuation forms** (`Steps P_ghost (f_stub u) sf` +
     `P_sub.CodeLoaded u.mem` + `u.mem.KeepsFrozen (f_stub u).mem`, matching
     `GhostRowReplayOn.replay_at_stub` Arm 2 directly without needing `P_sub.CodeLoaded s0.mem` or
     `s0.readReg64 .lr ≠ stubPc`):
     `strlen_lr_trap_after_hook_ret`, `strlen_lr_trap_after_hook_returned`,
     `strlen_keepLr_false_after_hook_of_codeLoaded_u`,
     `f3EmptyStrlenGhostHook{,K}_keepLr_false_after_hook_of_codeLoaded_u`, and
     `strlenGhostHook{,K}_keepLr_false_after_hook_of_codeLoaded_u`; plus `s0.mem`-`CodeLoaded`
     trajectory companions `strlen_keepLr_false_after_hook_of_{outcome,subroutineOutcome}` and
     `f3EmptyStrlenGhostHook{,K}` / `strlenGhostHook{,K}` specializations.
   - **At-stub trajectory form** (`Steps P_ghost s0 u` + `Steps P_ghost u sf` +
     `StrlenEntryGuard entryTarget stubPc s0`):
     `strlen_lr_trap_at_call_ret`, `strlen_lr_trap_at_call`,
     `strlen_keepLr_false_at_stub_of_outcome`, `strlen_keepLr_false_at_stub_of_subroutineOutcome`,
     and `f3EmptyStrlenGhostHook{,K}` specializations.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenLrTrap

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (muslStrlenWords)
open CryptoVerification.SignalSession (strlenHook)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (keepFsTrace)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (
  subroutineOutcome_running_pc_and_noFault
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (
  TrapRegion keepBlock keepOf keepOf_singleton
  RegionWordsSafe RegionHasWords RegionCodeLoaded
  codeLoaded_stripExecOutside_of_keep
  TrapHook trapHook_of_exception_on_keepLr trapHook_linkedCallHook
  trap_impossible lr_trap_at_call_ret lr_trap_at_call
  TrapEntryGuard keepLr_false_at_stub_of_outcome
  reg_ext_of_entry_excluded reg_ext_forall_of_entry_excluded
  regionWordsSafe_single strlen_all_safe
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode (
  muslStrlenWords_length pureWordsProg_strlen_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost (
  strlenByteLen strlenByteLen_eq keepStrlenRange KeepCoversStrlen
  keepFsTrace_strlenHook_eq
  strlenGhostHook strlenGhostHookK strlenGhostHookK_of_keepLr_true
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostK (
  f3EmptyStrlenGhostHook f3EmptyStrlenGhostHookK
  f3EmptyStrlenGhostHook_eq f3EmptyStrlenGhostHookK_eq
)

/-! ## 1. 88 B `muslStrlenWords` Hull (`keepStrlenRange`, `strlenRegion`, `RegionWordsSafe`) -/

theorem keepStrlenRange_iff (entryTarget pc : BitVec 64) :
    keepStrlenRange entryTarget pc = true ↔ (pc - entryTarget).toNat < strlenByteLen := by
  simp [keepStrlenRange, decide_eq_true_eq]

theorem keepStrlenRange_iff_lt88 (entryTarget pc : BitVec 64) :
    keepStrlenRange entryTarget pc = true ↔ (pc - entryTarget).toNat < 88 := by
  rw [keepStrlenRange_iff, strlenByteLen_eq]

/-- The `strlen` entry `entryTarget` lies inside `keepStrlenRange entryTarget` (`0 < 88`). -/
theorem keepStrlenRange_entry (entryTarget : BitVec 64) :
    keepStrlenRange entryTarget entryTarget = true := by
  rw [keepStrlenRange_iff_lt88, BitVec.sub_self]
  decide

/-- Any `keepR` satisfying `KeepCoversStrlen keepR entryTarget` is `true` at every `pc` inside
    `keepStrlenRange entryTarget`. -/
theorem keep_of_keepCoversStrlen {keepR : BitVec 64 → Bool} {entryTarget pc : BitVec 64}
    (hcov : KeepCoversStrlen keepR entryTarget)
    (hin : keepStrlenRange entryTarget pc = true) :
    keepR pc = true := by
  have hlt : (pc - entryTarget).toNat < strlenByteLen :=
    (keepStrlenRange_iff entryTarget pc).mp hin
  have hpc : entryTarget + BitVec.ofNat 64 (pc - entryTarget).toNat = pc := by
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rw [← hpc]
  exact hcov (pc - entryTarget).toNat hlt

/-- Single-block `TrapRegion` for the contiguous 88 B (`22`-word) `muslStrlenWords` hull at
    `entryTarget`. -/
@[expose] def strlenRegion (entryTarget : BitVec 64) : TrapRegion :=
  [(entryTarget, muslStrlenWords)]

/-- `keepOf (strlenRegion entryTarget)` equals `keepStrlenRange entryTarget`. -/
theorem keepOf_strlenRegion (entryTarget : BitVec 64) :
    keepOf (strlenRegion entryTarget) = keepStrlenRange entryTarget := by
  funext pc
  dsimp only [strlenRegion]
  rw [keepOf_singleton]
  rfl

theorem keepOf_strlenRegion_apply (entryTarget pc : BitVec 64) :
    keepOf (strlenRegion entryTarget) pc = keepStrlenRange entryTarget pc :=
  congrFun (keepOf_strlenRegion entryTarget) pc

/-- `RegionWordsSafe` for the 88 B `muslStrlenWords` hull at any `entryTarget` (lifted directly from
    `TrapSafeWords.strlen_all_safe`, zero additional `decide` calls). -/
theorem strlenRegion_wordsSafe (entryTarget : BitVec 64) :
    RegionWordsSafe (strlenRegion entryTarget) :=
  regionWordsSafe_single entryTarget strlen_all_safe

/-- `RegionHasWords [P_sub] (strlenRegion entryTarget)` from `P_sub.hasWords entryTarget muslStrlenWords`. -/
theorem strlenRegion_hasWords_of_hasWords {P_sub : Program} {entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entryTarget muslStrlenWords) :
    RegionHasWords [P_sub] (strlenRegion entryTarget) := by
  intro blk hmem
  rw [strlenRegion, List.mem_singleton] at hmem
  subst hmem
  exact ⟨P_sub, List.mem_singleton.mpr rfl, hHas⟩

theorem strlenRegion_codeLoaded_iff {P_sub : Program} {mem : Memory} :
    RegionCodeLoaded [P_sub] mem ↔ P_sub.CodeLoaded mem := by
  constructor
  · intro h
    exact h P_sub (List.mem_singleton.mpr rfl)
  · intro h P hP
    rw [List.mem_singleton] at hP
    subst hP
    exact h

/-- Lift `P_sub.CodeLoaded mem` across `ProofLib.stripExecOutside keepR mem` whenever `keepR`
    retains all bytes of `P_sub`. -/
theorem strlen_codeLoaded_stripExecOutside_of_prog {keepR : BitVec 64 → Bool} {P_sub : Program}
    {mem : Memory}
    (hkeep : ∀ off : Nat, off < P_sub.code.length →
      keepR (P_sub.base + BitVec.ofNat 64 off) = true)
    (hL : P_sub.CodeLoaded mem) :
    P_sub.CodeLoaded (ProofLib.stripExecOutside keepR mem) :=
  codeLoaded_stripExecOutside_of_keep hkeep hL

/-- Entry-state `lr` guard at `s0` for `strlen` stub replay
    (`keepStrlenRange entryTarget lr = false ∧ lr ≠ stubPc`). -/
@[expose] def StrlenEntryGuard (entryTarget stubPc : BitVec 64) (s0 : State) : Prop :=
  keepStrlenRange entryTarget (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

theorem strlenEntryGuard_iff_trapEntryGuard (entryTarget stubPc : BitVec 64) (s0 : State) :
    StrlenEntryGuard entryTarget stubPc s0 ↔
      TrapEntryGuard (strlenRegion entryTarget) stubPc s0 := by
  simp only [StrlenEntryGuard, TrapEntryGuard, keepOf_strlenRegion_apply]

/-! ## 2. `TrapHook` Instances (Idealized Fallback, Plain Ghost, and `K` Ghost) -/

/-- `strlenHook` either returns to `lr` via `retHook` (with `status = .Running` and `lr` unchanged)
    or faults with `.Exception "strlen: no readable NUL"` via `unmodelled`, so it satisfies
    `TrapHook L` for every `L : BitVec 64`. -/
theorem trapHook_strlenHook (L : BitVec 64) :
    TrapHook L strlenHook := by
  intro w hrun hlr
  unfold strlenHook
  dsimp only
  split
  · exact Or.inr ⟨hrun, hlr, hlr⟩
  · exact Or.inl ⟨"strlen: no readable NUL", rfl⟩

theorem trapHook_keepFsTrace_strlenHook (L : BitVec 64) :
    TrapHook L (keepFsTrace strlenHook) := by
  rw [show keepFsTrace strlenHook = strlenHook from funext keepFsTrace_strlenHook_eq]
  exact trapHook_strlenHook L

/-- Plain `strlenGhostHook` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_strlenGhostHook {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (strlenGhostHook keepR P_real P_sub entryTarget) :=
  trapHook_linkedCallHook hkeepL (trapHook_keepFsTrace_strlenHook L)

/-- Plain `W`-independent `f3EmptyStrlenGhostHook` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_f3EmptyStrlenGhostHook {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (f3EmptyStrlenGhostHook keepR P_sub entryTarget) := by
  rw [f3EmptyStrlenGhostHook_eq]
  exact trapHook_strlenGhostHook _ P_sub entryTarget hkeepL

theorem trapHook_f3EmptyStrlenGhostHook_of_cover {keepR : BitVec 64 → Bool}
    {entryTarget m L : BitVec 64}
    (P_sub : Program)
    (hcov : KeepCoversStrlen keepR m)
    (hL : keepStrlenRange m L = true) :
    TrapHook L (f3EmptyStrlenGhostHook keepR P_sub entryTarget) :=
  trapHook_f3EmptyStrlenGhostHook P_sub entryTarget (keep_of_keepCoversStrlen hcov hL)

/-! ## 3. Entry-Excluded Region Extern Adapters (`SPEC-PLANNER T2` + `REV-S2 F1`) -/

/-- `∀ L` entry-excluded adapter on `keepStrlenRange entryTarget` (`entries : List (BitVec 64)`),
    wrapping `TrapSafeWords.reg_ext_forall_of_entry_excluded` and feeding
    `strlen_keepLr_false_after_hook_of_outcome` / `strlen_keepLr_false_at_stub_of_outcome`. -/
theorem strlen_reg_ext_forall_of_entry_excluded {P_ghost : Program} {entryTarget : BitVec 64}
    {entries : List (BitVec 64)}
    (hno_ext_outside : ∀ pc, keepStrlenRange entryTarget pc = true → pc ∉ entries →
      P_ghost.externAt? pc = none)
    (hentries : ∀ e ∈ entries, P_ghost.externAt? e = none ∨
      ∃ f, P_ghost.externAt? e = some f ∧
        ∀ L, keepStrlenRange entryTarget L = true → TrapHook L f) :
    ∀ pc, keepStrlenRange entryTarget pc = true → P_ghost.externAt? pc = none ∨
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L, keepStrlenRange entryTarget L = true → TrapHook L f := by
  intro pc hkp
  have hraw := reg_ext_forall_of_entry_excluded (region := strlenRegion entryTarget)
    (fun q hq => hno_ext_outside q (keepOf_strlenRegion_apply entryTarget q ▸ hq))
    (fun e he => (hentries e he).imp id fun ⟨f, hf, htf⟩ =>
      ⟨f, hf, fun L hL => htf L (keepOf_strlenRegion_apply entryTarget L ▸ hL)⟩)
    pc ((keepOf_strlenRegion_apply entryTarget pc).trans hkp)
  exact hraw.imp id fun ⟨f, hf, htf⟩ =>
    ⟨f, hf, fun L hL => htf L ((keepOf_strlenRegion_apply entryTarget L).trans hL)⟩

/-- Single-entry (`entries := [entryTarget]`) `∀ L` adapter for the direct-entry ghost route where
    `P_ghost.externAt? pc = none` for `pc ≠ entryTarget` and `P_ghost.externAt? entryTarget` is
    either `none` or a `TrapHook`-satisfying `f_entry`. -/
theorem strlen_reg_ext_forall_of_single_entry {P_ghost : Program} {entryTarget : BitVec 64}
    {f_entry : State → State}
    (hno_ext_outside : ∀ pc, keepStrlenRange entryTarget pc = true → pc ≠ entryTarget →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? entryTarget = none ∨
      P_ghost.externAt? entryTarget = some f_entry)
    (htrap_entry : ∀ L, keepStrlenRange entryTarget L = true → TrapHook L f_entry) :
    ∀ pc, keepStrlenRange entryTarget pc = true → P_ghost.externAt? pc = none ∨
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L, keepStrlenRange entryTarget L = true → TrapHook L f :=
  strlen_reg_ext_forall_of_entry_excluded (entries := [entryTarget])
    (fun pc hkp hne => hno_ext_outside pc hkp (fun h => hne (List.mem_singleton.mpr h)))
    (fun e he => by
      rw [List.mem_singleton] at he
      subst he
      exact hext_entry.imp id fun h => ⟨f_entry, h, htrap_entry⟩)

/-! ## 4. Post-Hook Continuation & At-Stub `SubroutineOutcome` Trap Theorems for Card `c` -/

/-- **Post-hook continuation `keepStrlenRange entryTarget (u.readReg64 .lr) = false`
    (`strlen_lr_trap_after_hook_ret`):**
    Consumes `hrest : Steps P_ghost (f_u u) sf` directly (requiring zero `sf.pc ≠ stubPc`
    inequality). -/
theorem strlen_lr_trap_after_hook_ret
    {P_ghost P_sub : Program} {entryTarget : BitVec 64}
    {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords entryTarget muslStrlenWords)
    (htrap_u : keepStrlenRange entryTarget (u.readReg64 .lr) = true →
      TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepStrlenRange entryTarget (u.readReg64 .lr) = true →
      ∀ pc, keepStrlenRange entryTarget pc = true →
        P_ghost.externAt? pc = none ∨
          ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hout_sf : sf.status = .Running → keepStrlenRange entryTarget sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepStrlenRange entryTarget (u.readReg64 .lr) = false := by
  cases hkeepL : keepStrlenRange entryTarget (u.readReg64 .lr) with
  | false => rfl
  | true =>
    exfalso
    have hL_reg : keepOf (strlenRegion entryTarget) (u.readReg64 .lr) = true :=
      (keepOf_strlenRegion_apply entryTarget _).trans hkeepL
    rcases htrap_u hkeepL u hrun_u rfl with ⟨msg, hex⟩ | ⟨hrun_v, hpc_v, hlr_v⟩
    · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest (by rw [hex]; nofun)
      exact hnoex_sf msg (by rw [heq, hex])
    · exact trap_impossible
        (strlenRegion_wordsSafe entryTarget)
        (strlenRegion_hasWords_of_hasWords hHas)
        hL_reg
        (fun pc hkp => hreg_ext hkeepL pc
          ((keepOf_strlenRegion_apply entryTarget pc).symm.trans hkp))
        hrest
        (fun hr => (keepOf_strlenRegion_apply entryTarget sf.pc).trans (hout_sf hr))
        hnoex_sf hnhalt_sf
        ⟨hrun_v, hpc_v ▸ hL_reg, hlr_v, strlenRegion_codeLoaded_iff.mpr hCode_fu⟩

/-- **Card-`c` `InvS u` post-hook theorem (`strlen_keepLr_false_after_hook_of_codeLoaded_u`):**
    Variant of `strlen_keepLr_false_after_hook_of_outcome` taking `P_sub.CodeLoaded u.mem` at the
    call state `u` (supplied by `InvS u` in `GhostRowReplayOn.replay_at_stub` Arm 2) instead of
    `P_sub.CodeLoaded s0.mem`. -/
theorem strlen_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {entryTarget : BitVec 64}
    {f_stub : State → State}
    (hHas : P_sub.hasWords entryTarget muslStrlenWords)
    (hreg_ext : ∀ pc : BitVec 64, keepStrlenRange entryTarget pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepStrlenRange entryTarget L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepStrlenRange entryTarget L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hlr_s0 : keepStrlenRange entryTarget (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepStrlenRange entryTarget (u.readReg64 .lr) = false := by
  intro u hc_u hsteps_fu_sf hrun_u hkf
  exact strlen_lr_trap_after_hook_ret hHas
    (fun hL => htrap_stub _ hL)
    (fun hL pc hkp => (hreg_ext pc hkp).imp id fun ⟨f, hf, htf⟩ => ⟨f, hf, htf _ hL⟩)
    (hc_u.of_keepsFrozen hkf)
    hsteps_fu_sf hrun_u
    (fun hrun_sf => hret_pc hrun_sf ▸ hlr_s0)
    hnoex_sf hnhalt_sf

/-- Entry-excluded card-`c` `InvS u` post-hook theorem for `W`-independent `f3EmptyStrlenGhostHook`
    (consumes `P_sub.CodeLoaded u.mem` at `u` for `GhostRowReplayOn.replay_at_stub` Arm 2; allows
    `P_ghost.externAt? entryTarget` to be either `none` or the ghost `strlen` hook itself). -/
theorem f3EmptyStrlenGhostHook_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entryTarget muslStrlenWords)
    (hcov : KeepCoversStrlen keepR entryTarget)
    (hno_ext_outside : ∀ pc : BitVec 64, keepStrlenRange entryTarget pc = true →
      pc ≠ entryTarget → P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? entryTarget = none ∨
      P_ghost.externAt? entryTarget = some (f3EmptyStrlenGhostHook keepR P_sub entryTarget))
    {s0 sf : State}
    (hlr_s0 : keepStrlenRange entryTarget (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptyStrlenGhostHook keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyStrlenGhostHook keepR P_sub entryTarget u).mem →
      keepStrlenRange entryTarget (u.readReg64 .lr) = false :=
  strlen_keepLr_false_after_hook_of_codeLoaded_u hHas
    (strlen_reg_ext_forall_of_single_entry hno_ext_outside hext_entry
      (fun _ hL => trapHook_f3EmptyStrlenGhostHook_of_cover P_sub hcov hL))
    (fun _ hL => trapHook_f3EmptyStrlenGhostHook_of_cover P_sub hcov hL)
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenLrTrap

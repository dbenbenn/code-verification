/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds

/-!
# `libcrux_hmac::hmac` Ghost Hook and `GhostRowOk`

Ghost-hook and replay proofs for `lsLibcruxHmacSym` (`_RNvCs65XVORQObL2_12libcrux_hmac4hmac`):
- `libcruxHmacEntryGuard` (`True`), `libcruxHmacSpecOf`, and `libcruxHmacGhost` (built on
  `f3LinkedCallHook`, `externOnlyStdProg P_sub`, and fallback `libcruxHmacHookMallocng mmpl sha256Compress`).
- Generic panic-extern extensions of `f3LinkedCallHook_ok` and `externOnlyStdProg` replay.
- Per-row `HookOk`, `GhostRowSpecOk`, `GhostRowReplayOn`, and `GhostRowOk` bundles.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LibcruxHmacGhostReplays

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (restoreCallerRegs stepRustAlloc1)
open CryptoVerification.LibsignalSpqrV1 (LibcruxHmacCall sha256Compress)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced libsignalSessionLib lsBlackBoxSym lsCompress256Sym
   lsDurationSinceSym lsFromUtf8Sym lsLibcruxHmacSym lsMemrchrSym lsSharedSecretDropSym
   lsStaticSecretDropSym lsTimeAddSym)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (AllocEvent BudgetLimits FitsEnv)
open LibsignalBinary.Heap.Fine (fineCostModel fineCostModelSound fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (LibcruxHmacEnv libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineLibcruxHmac_budget_hookOk mallocngHookBudgetPool)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (libcruxHmacFrameBytes libcruxHmacHookMallocng)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant keepFsTrace keepFsTrace_ok
   satisfies_of_stripExecOutside satisfies_stripExecOutside)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
  (libcruxHmacHookMallocng_fs_eq_of_pre)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (fineHookRustCliAllocBudget_pool_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (StubReachesTargetOn execFrozen_libcruxHmacHookMallocng)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
  (StripCommExtern externOnlyStdProg externOnlyStdProg_externAt keepOrSubExtern
   stepsVisitedIn_of_stripS_with_externs_inKeep
   steps_externOnly_to_real_of_visitedIn_inKeep stripCommExtern_rustPanicked)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (hookOk_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowSpec GhostRowSpecOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.LibcruxHmacRowSpec
  (LibcruxHmacRowSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det)

/-! ## 1. Row Anchor Definitions (`libcruxHmacEntryGuard`, `libcruxHmacSpecOf`, `libcruxHmacGhost`) -/

/-- Trivial entry guard for `lsLibcruxHmacSym` (`.text.lib2`). -/
@[expose] def libcruxHmacEntryGuard (_mpl : Obj.MultiPlacement) (_s0 : State) : Prop :=
  True

theorem libcruxHmacEntryGuard_intro (mpl : Obj.MultiPlacement) (s0 : State) :
    libcruxHmacEntryGuard mpl s0 :=
  trivial

/-- Guard asserting every extern stub PC of `P_sub` is mapped readable and non-writable (`r = true`,
    `w = false`) in `s.mem`, so `stripExecOutside keep s.mem` leaves it `Frozen` and non-executable. -/
@[expose] def stubFrozenGuard (P_sub : Program) (s : State) : Prop :=
  ∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
    (s.mem.perm pc).r = true ∧ (s.mem.perm pc).w = false

/-- Prepend pure read-only extern-stub guard (`r = true ∧ w = false`) and `ExecFrozen s0.mem`
    on `s0.mem` to `spec.pre`. -/
@[expose] def withHooksUnfetched (P_sub : Program) {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 =>
      ⌜(∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
        (s0.mem.perm pc).r = true ∧ (s0.mem.perm pc).w = false) ∧ ExecFrozen s0.mem⌝ ∗
      spec.pre x s0 }

/-- `(γ, tp)`-indexed `withLsRet`-narrowed `libcruxHmacBudgetSpec` for `f3LinkedCallHook`. -/
@[expose] def libcruxHmacSpecOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) : Spec (LibcruxHmacCall × fineCostModel.σ) :=
  withLsRet (libcruxHmacBudgetSpec sha256Compress fineCostModel
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)

/-- `(γ, tp)`- and `W`-independent linked ghost-call hook for `lsLibcruxHmacSym`. -/
@[expose] noncomputable def libcruxHmacGhost [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) : State :=
  letI := Classical.propDecidable
  if stubFrozenGuard P_sub s0 then
    f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
      (libcruxHmacSpecOf mmpl brkStart lim)
      (libcruxHmacHookMallocng mmpl sha256Compress) s0
  else if ActiveF3CallPre (libcruxHmacSpecOf mmpl brkStart lim) s0 then
    keepFsTrace (libcruxHmacHookMallocng mmpl sha256Compress) s0
  else
    { s0 with status := .Exception "ghost-hook precondition violated" }

theorem libcruxHmacGhost_eq_f3LinkedCallHook_of_stubFrozen [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    {s0 : State} (hSF : stubFrozenGuard P_sub s0) :
    libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim s0 =
      f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
        (libcruxHmacSpecOf mmpl brkStart lim)
        (libcruxHmacHookMallocng mmpl sha256Compress) s0 := by
  classical
  unfold libcruxHmacGhost
  simp only [hSF, ↓reduceIte]

/-! ## 2. Unconditional State Preservation & `GhostRowSpecOk` -/

theorem libcruxHmacGhost_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) :
    (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim s0).fs = s0.fs := by
  classical
  unfold libcruxHmacGhost
  split
  · exact f3LinkedCallHook_fs keep (externOnlyStdProg P_sub) P_sub entryTarget
      (libcruxHmacSpecOf mmpl brkStart lim)
      (libcruxHmacHookMallocng mmpl sha256Compress) s0
  · split <;> rfl

theorem libcruxHmacGhost_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    HookFsTraced IsFsC (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim) := by
  classical
  intro s0
  unfold libcruxHmacGhost
  split
  · exact f3LinkedCallHook_fsT keep (externOnlyStdProg P_sub) P_sub entryTarget
      (libcruxHmacSpecOf mmpl brkStart lim)
      (libcruxHmacHookMallocng mmpl sha256Compress) s0
  · split <;> exact FsTraced.of_eq rfl rfl

theorem libcruxHmacGhost_preserves_execFrozen [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim u).mem := by
  classical
  unfold libcruxHmacGhost
  split
  · unfold f3LinkedCallHook
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
      · exact execFrozen_libcruxHmacHookMallocng mmpl sha256Compress u hfr
    · exact hfr
  · split
    · exact execFrozen_libcruxHmacHookMallocng mmpl sha256Compress u hfr
    · exact hfr

theorem libcruxHmacGhost_rowSpecOk [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    GhostRowSpecOk lsLibcruxHmacSym
      (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim) where
  fs_eq := libcruxHmacGhost_fs keep P_sub entryTarget mmpl brkStart lim
  fsT := libcruxHmacGhost_fsT keep P_sub entryTarget mmpl brkStart lim
  rowSpec := by
    unfold ExtraRowSpec
    simp (config := { decide := true })
    exact LibcruxHmacRowSpec.intro _

/-! ## 3. `withFsTraceExact` Post-Strengthening & Panic-Extern `f3LinkedCallHook` Combinators -/

/-- Strengthen `spec.post` and `spec.onPanic` with `⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝`
    (with `onExit = False` and `onOom = False`), keeping `spec.pre` definitionally (`rfl`) unchanged. -/
@[expose] def withFsTraceExact {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    post := fun x s0 sf => ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ spec.post x s0 sf
    onPanic := fun x s0 sf => ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ spec.onPanic x s0 sf
    onExit := fun _ _ _ _ => ⌜False⌝
    onOom := fun _ _ _ => ⌜False⌝ }

theorem specPreservesFsTrace_withFsTraceExact {α : Type} (spec : Spec α) :
    SpecPreservesFsTrace (withFsTraceExact spec) := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [withFsTraceExact] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1.1, FsTraced.of_eq hpost.1.2 (congrArg FsState.files hpost.1.1)⟩
  · dsimp only [withFsTraceExact] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact ⟨hpan.1.1, FsTraced.of_eq hpan.1.2 (congrArg FsState.files hpan.1.1)⟩
  · dsimp only [withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem hookOk_of_withFsTraceExact {α : Type} {f : State → State} {spec : Spec α}
    (hok : HookOk f (withFsTraceExact spec)) : HookOk f spec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFsTraceExact] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    dsimp only [withFsTraceExact] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact hpan.2
  · dsimp only [withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem hooksUnfetched_stripExecOutside_of_stubFrozen
    {keep : BitVec 64 → Bool} {P_sub : Program} {u : State}
    (hSF : stubFrozenGuard P_sub u) :
    ∀ pc : BitVec 64,
      P_sub.externAt? pc ≠ none →
      ((stripExecOutside keep u.mem).perm pc).r = true ∧
        ((stripExecOutside keep u.mem).perm pc).w = false := by
  intro pc hext
  have hfr_u : (u.mem.perm pc).r = true ∧ (u.mem.perm pc).w = false := hSF pc hext
  unfold Memory.perm at hfr_u
  unfold Memory.perm stripExecOutside stripPerm
  dsimp only
  cases hc : u.mem.cells pc with
  | none => simp [hc, Option.r] at hfr_u
  | some v =>
    rcases v with ⟨op, b⟩
    cases op with
    | none => simp [hc, Option.r] at hfr_u
    | some p =>
      simp only [hc, Option.r, Option.w, Perm.rwx] at hfr_u
      rcases p with ⟨r, w, x, lf, an⟩
      cases hkp : keep pc <;> cases r <;> cases w <;> cases x <;>
        simp_all [Option.r, Option.w, Perm.rwx]

private theorem subroutineOutcome_to_stop {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : SubroutineStop s0 sf := by
  rcases h with ⟨h1, _, _⟩ | ⟨h2, _⟩ | ⟨c, h3, _⟩ | ⟨h4, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl ⟨c, h3⟩))
  · exact Or.inr (Or.inr (Or.inr h4))

private theorem subroutineOutcome_not_halted {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hst⟩, _, _⟩ | ⟨hst, _⟩ | ⟨_, hst, _⟩ | ⟨hst, _⟩ <;>
    (rw [hst]; nofun)

private theorem real_subroutine_run_visitedIn_of_stripS_with_unfetched {α : Type}
    {keep : BitVec 64 → Bool} {P1 P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    {s0 : State} (hsvc1 : P1.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P_sub.externAt? pc = none → P1.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → P1.externAt? pc = some f ∧ StripCommExtern keep f)
    (hOk : subroutine_ok P_sub entryTarget (withHooksUnfetched P_sub spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} (hRun : s0.status = .Running) (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R) (hFr : ExecFrozen s0.mem)
    (hSF : stubFrozenGuard P_sub s0)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P1 (SubroutineStop s0) (s0.setPC entryTarget) sf ∧ SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf ∧ sf.fs = s0.fs ∧ FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem ∧
      h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) P1 (s0.setPC entryTarget) sf := by
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ spec.pre x s1 ∗ R := by
    change s0.mem ⊨ spec.pre x (s0.setPC entryTarget) ∗ R
    rwa [hPrePC x s0 entryTarget]
  have hs1'_pre : s1'.mem ⊨ spec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← hInv.pre_eq x s1] at hsat
  have hunf : ∀ pc : BitVec 64,
      P_sub.externAt? pc ≠ none →
        (s1'.mem.perm pc).r = true ∧ (s1'.mem.perm pc).w = false :=
    hooksUnfetched_stripExecOutside_of_stubFrozen hSF
  have hfr_s1' : ExecFrozen s1'.mem := fun a hx => by
    dsimp only [s1', stripS, State.setMem] at hx ⊢
    obtain ⟨hx_m, hk⟩ := strip_perm_x_imp hx
    rw [strip_perm_of_keep hk]
    exact hFr a hx_m
  have hs1'_pre_unf : s1'.mem ⊨ (withHooksUnfetched P_sub spec).pre x s1' ∗ R := by
    dsimp only [withHooksUnfetched]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hunf, hfr_s1'⟩, hs1'_pre⟩
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_pre_unf hSp hCodeSub
  have hout_base : SubroutineOutcome spec x R s1' sf' := hout'
  have hstop1' : SubroutineStop s1' sf' := subroutineOutcome_to_stop hout_base
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout_base
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, hvis⟩ :=
    stepsVisitedIn_of_stripS_with_externs_inKeep hsvc1 hsvc_sub hext1_no hext_sub
      hlr_out hlr_ne hsteps' hstop0' hnhalt' hFr
  have hout1 : SubroutineOutcome spec x R s1 sf := by
    rw [hsf_eq] at hout_base
    rcases hout_base with ⟨hret', hcc', hpost'⟩ | ⟨hp', hpan'⟩ | ⟨c, he', hex'⟩ | ⟨ho', hoom'⟩
    · refine Or.inl ⟨⟨hret'.1, hret'.2.1, hret'.2.2⟩, ?_, ?_⟩
      · cases s0; cases sf; exact hcc'
      · rw [hInv.post_eq x s1 sf] at hpost'
        exact satisfies_of_stripExecOutside hfr_sf hpost'
    · refine Or.inr (Or.inl ⟨hp', ?_⟩)
      rw [hInv.onPanic_eq x s1 sf] at hpan'
      exact satisfies_of_stripExecOutside hfr_sf hpan'
    · refine Or.inr (Or.inr (Or.inl ⟨c, he', ?_⟩))
      rw [hInv.onExit_eq x c s1 sf] at hex'
      exact satisfies_of_stripExecOutside hfr_sf hex'
    · refine Or.inr (Or.inr (Or.inr ⟨ho', ?_⟩))
      rw [hInv.onOom_eq x s1 sf] at hoom'
      exact satisfies_of_stripExecOutside hfr_sf hoom'
  have hout0 : SubroutineOutcome spec x R s0 sf := hOutPC x R s0 sf entryTarget hout1
  obtain ⟨hfs, hfst⟩ := hFsT x R s0 sf hout0
  exact ⟨sf, huntil, hstop_sf, hout0, hfs, hfst, hfr_sf, hvis⟩

theorem f3LinkedCallHook_ok_at_stubFrozen {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_sub.externAt? pc = none → P_real.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (γ : GhostName) (tp : BitVec 64)
    (hlr_ne_pre : ∀ x (R : SepProp) (s0 : State),
      (s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hOk : subroutine_ok P_sub entryTarget (withHooksUnfetched P_sub (specOf γ tp)))
    (hInv : SpecStripSInvariant keep (specOf γ tp))
    (hFsT : SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) (specOf γ tp))
    {x : α} {R : SepProp} {s0 : State}
    (hSF : stubFrozenGuard P_sub s0)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    s0.mem.KeepsFrozen
        (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0).mem ∧
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0).symtab = s0.symtab ∧
      SubroutineOutcome (specOf γ tp) x R s0
        (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0) := by
  classical
  have hActPre : ActiveF3CallPre specOf s0 := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  unfold f3LinkedCallHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _, _⟩ :=
      real_subroutine_run_visitedIn_of_stripS_with_unfetched hsvc_real hsvc_sub hreal_no
        hext_sub hOk hInv hFsT hPrePC hOutPC hrun hsp hpre hReal.1 hSF
        hReal.2.1 (hlr_ne_pre x R s0 hpre) hReal.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
  · simp only [hReal, ↓reduceDIte]
    exact hFallbackOk x R s0 hrun hpre hsp

private theorem f3LinkedCallHook_activeF3CallPre_of_noException {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State} {u : State}
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).status ≠ .Exception msg) :
    ActiveF3CallPre specOf u := by
  classical
  by_contra hnot
  have hex :
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).status =
        .Exception "ghost-hook precondition violated" := by
    unfold f3LinkedCallHook
    simp only [hnot, ↓reduceDIte]
  exact hnoex _ hex

theorem f3LinkedCallHook_externOnly_visitedIn_with_externs {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget (withHooksUnfetched P_sub (specOf γ tp)))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    {u : State}
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hSF : stubFrozenGuard P_sub u)
    (hlr_out : keep (u.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) (externOnlyStdProg P_sub)
        (u.setPC entryTarget)
        (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u) ∧
      ExecFrozen
        (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).mem ∧
      (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).fs =
        u.fs := by
  classical
  obtain ⟨hrun, hsp, γ, tp, x, R, hpre⟩ := f3LinkedCallHook_activeF3CallPre_of_noException hnoex
  have hActPre : ActiveF3CallPre specOf u := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  obtain ⟨sf, huntil_sf, hstop_sf, _, hfs_sf, hfst_sf, hfr_sf, hvis_sf⟩ :=
    real_subroutine_run_visitedIn_of_stripS_with_unfetched
      (P1 := externOnlyStdProg P_sub) rfl hsvc_sub
      (fun pc _ h => (externOnlyStdProg_externAt P_sub pc).trans h)
      (fun pc f he => ⟨(externOnlyStdProg_externAt P_sub pc).trans he, hcomm pc f he⟩)
      (hOk γ tp) (hInv γ tp) (hFsT γ tp) (hPrePC γ tp) (hOutPC γ tp)
      hrun hsp hpre hFr hSF hlr_out hlr_ne hCodeSub
  have hReal : ActiveRealRun keep (externOnlyStdProg P_sub) P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil_sf, hstop_sf, hfs_sf, hfst_sf, hfr_sf⟩
  have hhook_eq :
      f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u = sf := by
    unfold f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil_sf hstop_sf
  rw [hhook_eq]
  exact ⟨hvis_sf, hfr_sf, hfs_sf⟩

/-! ## 4. `libcruxHmacSpecOf` Invariants, Fallback `HookOk`, & `libcruxHmacGhost_ok` -/

theorem specStripSInvariant_libcruxHmacSpecOf [LibsignalPlacement]
    {keep : BitVec 64 → Bool} (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) :
    SpecStripSInvariant keep (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp)) where
  pre_eq := by
    intro ⟨x, st⟩ s
    dsimp only [withFsTraceExact, libcruxHmacSpecOf, withLsRet, libcruxHmacBudgetSpec]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s]
    rfl
  post_eq := by
    intro ⟨x, st⟩ s0 sf
    dsimp only [withFsTraceExact, libcruxHmacSpecOf, withLsRet, libcruxHmacBudgetSpec]
    congr 1
    exact congrArg sepExists (funext fun evs => by
      rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim _ sf]
      rfl)
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

private theorem prePC_libcruxHmacSpecOf [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) :
    ∀ x (s : State) (pc : BitVec 64),
      (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp)).pre x (s.setPC pc) =
        (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp)).pre x s := by
  intro ⟨x, st⟩ s pc
  cases s
  rfl

private theorem outPC_libcruxHmacSpecOf [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) :
    ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp))
        x R (s0.setPC pc) sf →
      SubroutineOutcome (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp))
        x R s0 sf := by
  intro x R s0 sf pc
  cases s0
  exact id

private theorem libcruxHmacFallback_withFsTraceExact_ok [LibsignalPlacement]
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookOk (keepFsTrace (libcruxHmacHookMallocng mmpl sha256Compress))
      (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp)) := by
  have hBase : HookOk (libcruxHmacHookMallocng mmpl sha256Compress)
      (libcruxHmacSpecOf mmpl brkStart lim γ tp) :=
    hookOk_withLsRet (fineLibcruxHmac_budget_hookOk γ tp brkStart lim hPl sha256Compress)
  have hExact : HookOk (libcruxHmacHookMallocng mmpl sha256Compress)
      (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp)) := by
    intro ⟨x, st⟩ R s0 hrun hpre hsp
    have hpre_ls : s0.mem ⊨ (libcruxHmacSpecOf mmpl brkStart lim γ tp).pre (x, st) s0 ∗ R :=
      hpre
    dsimp only [libcruxHmacSpecOf, withLsRet] at hpre_ls
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_ls
    have hpre_bud : s0.mem ⊨
        (libcruxHmacBudgetSpec sha256Compress fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim).pre (x, st) s0 ∗ R := hpre_ls.2
    have hfs : (libcruxHmacHookMallocng mmpl sha256Compress s0).fs = s0.fs :=
      libcruxHmacHookMallocng_fs_eq_of_pre fineCostModelSound γ tp brkStart lim hPl sha256Compress
        hpre_bud hsp
    obtain ⟨hkf, hsym, hout⟩ := hBase (x, st) R s0 hrun hpre hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      have htr : (libcruxHmacHookMallocng mmpl sha256Compress s0).trace = s0.trace := by
        dsimp only [libcruxHmacSpecOf, withLsRet, libcruxHmacBudgetSpec] at hpost
        rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
        rcases hpost with ⟨evs, hevs⟩
        simp only [sepConj_assoc] at hevs
        rw [satisfies_pure_sepConj] at hevs
        exact hevs.1.2.2.1
      dsimp only [withFsTraceExact]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hfs, htr⟩, hpost⟩
    · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
      have htr : (libcruxHmacHookMallocng mmpl sha256Compress s0).trace = s0.trace := by
        dsimp only [libcruxHmacSpecOf, withLsRet, libcruxHmacBudgetSpec] at hpan hpre_bud
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpan hpre_bud
        rcases hpre_bud with ⟨⟨_, hx0, _, hx2, _, hx4, _, _, _⟩, _⟩
        have hbig : (decide (2 ^ 32 ≤ x.key.length) || decide (2 ^ 32 ≤ x.data.length)) = true := by
          rcases hpan.1.1 with hk | hd
          · exact Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true hk))
          · exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true hd))
        unfold libcruxHmacHookMallocng
        simp only [show ((s0.readReg64 .x0).setWidth 32 != 0#32) = false by rw [hx0]; rfl,
          Bool.false_eq_true, ↓reduceIte, hx2, hx4, hbig]
        rfl
      dsimp only [withFsTraceExact]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hfs, htr⟩, hpan⟩
    · dsimp only [libcruxHmacSpecOf, withLsRet, libcruxHmacBudgetSpec] at hex
      rw [satisfies_pure_sepConj] at hex
      exact False.elim hex.1
    · dsimp only [libcruxHmacSpecOf, withLsRet, libcruxHmacBudgetSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      exact False.elim hoom.1
  refine keepFsTrace_ok hExact (fun _ _ s0 hout => ?_)
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [withFsTraceExact] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · dsimp only [withFsTraceExact] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact hpan.1
  · dsimp only [withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- Pointwise `HookOk` for `libcruxHmacGhost` at every `(γ, tp)`. -/
theorem libcruxHmacGhost_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : subroutine_ok P_sub entryTarget
      (withHooksUnfetched P_sub (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp)))) :
    HookOk (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim)
      (libcruxHmacSpecOf mmpl brkStart lim γ tp) := by
  classical
  apply hookOk_of_withFsTraceExact
  intro x R s0 hrun hpre hsp
  by_cases hSF : stubFrozenGuard P_sub s0
  · rw [libcruxHmacGhost_eq_f3LinkedCallHook_of_stubFrozen keep P_sub entryTarget mmpl brkStart
      lim hSF]
    exact f3LinkedCallHook_ok_at_stubFrozen
      (P_real := externOnlyStdProg P_sub)
      (specOf := fun γ' tp' => withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ' tp'))
      (fallback := libcruxHmacHookMallocng mmpl sha256Compress)
      rfl hsvc_sub (fun pc _ h => (externOnlyStdProg_externAt P_sub pc).trans h)
      (fun pc f he => ⟨(externOnlyStdProg_externAt P_sub pc).trans he, hcomm pc f he⟩) γ tp
      (fun _ _ s0' hpre' => by
        dsimp only [withFsTraceExact, libcruxHmacSpecOf, withLsRet] at hpre'
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
        exact hlr_ne_stub (s0'.readReg64 .lr) hpre'.1)
      hOk
      (specStripSInvariant_libcruxHmacSpecOf γ mmpl tp brkStart hKeepMallocng lim)
      (specPreservesFsTrace_withFsTraceExact _)
      (prePC_libcruxHmacSpecOf γ mmpl tp brkStart lim)
      (outPC_libcruxHmacSpecOf γ mmpl tp brkStart lim)
      (libcruxHmacFallback_withFsTraceExact_ok γ tp brkStart lim hPl)
      hSF hrun hpre hsp
  · have hActPre : ActiveF3CallPre (libcruxHmacSpecOf mmpl brkStart lim) s0 :=
      ⟨hrun, hsp, γ, tp, x, R, hpre⟩
    have heq : libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim s0 =
        keepFsTrace (libcruxHmacHookMallocng mmpl sha256Compress) s0 := by
      unfold libcruxHmacGhost
      simp only [hSF, hActPre, ↓reduceIte]
    rw [heq]
    exact libcruxHmacFallback_withFsTraceExact_ok γ tp brkStart lim hPl x R s0 hrun hpre hsp

/-! ## 5. `GhostRowReplayOn` & `GhostRowOk` -/

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u
  dsimp only [State.setPC] at hpc ⊢
  subst hpc
  rfl

private theorem lsRetAddr624_of_noException [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits} {u : State}
    (hnoex : ∀ msg,
      (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) := by
  classical
  have hAct : ActiveF3CallPre (libcruxHmacSpecOf mmpl brkStart lim) u := by
    by_cases hSF : stubFrozenGuard P_sub u
    · rw [libcruxHmacGhost_eq_f3LinkedCallHook_of_stubFrozen keep P_sub entryTarget mmpl brkStart
        lim hSF] at hnoex
      exact f3LinkedCallHook_activeF3CallPre_of_noException hnoex
    · by_contra hnot
      have hex : (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim u).status =
          .Exception "ghost-hook precondition violated" := by
        unfold libcruxHmacGhost
        simp only [hSF, hnot, ↓reduceIte]
      exact hnoex _ hex
  rcases hAct with ⟨_, _, γ, tp, x, R, hpre⟩
  dsimp only [libcruxHmacSpecOf, withLsRet] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

theorem libcruxHmacGhost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withHooksUnfetched P_sub (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsLibcruxHmacSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn
        (fun m => P_sub.CodeLoaded (stripExecOutside keep m))
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsLibcruxHmacSym)
        entryTarget) :
    GhostRowReplayOn mpl mmpl InvS EG lsLibcruxHmacSym (fun _ => True)
      (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨libcruxHmacGhost_preserves_execFrozen keep P_sub entryTarget mmpl brkStart lim hfr,
     libcruxHmacGhost_fs keep P_sub entryTarget mmpl brkStart lim u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealStubNone W, ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hSF : stubFrozenGuard P_sub u := hStubFrozen u hInvU
    have hlr624 : LsRetAddr624 (u.readReg64 .lr) := lsRetAddr624_of_noException hnoex
    have hlr_out : keep (u.readReg64 .lr) = false := hKeep _ hlr624
    have hlr_ne := hlr_ne_stub _ hlr624
    have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hCL_strip u hfr hInvU
    have heq_f3 := libcruxHmacGhost_eq_f3LinkedCallHook_of_stubFrozen
      keep P_sub entryTarget mmpl brkStart lim hSF
    have hnoex_f3 : ∀ msg,
        (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
          (libcruxHmacSpecOf mmpl brkStart lim)
          (libcruxHmacHookMallocng mmpl sha256Compress) u).status ≠ .Exception msg := by
      rwa [← heq_f3]
    obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
      f3LinkedCallHook_externOnly_visitedIn_with_externs
        (specOf := fun γ tp => withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp))
        (fallback := libcruxHmacHookMallocng mmpl sha256Compress)
        hsvc_sub
        (fun pc f he => by
          obtain ⟨rfl, _⟩ := hPanReal W pc f he
          exact stripCommExtern_rustPanicked keep)
        hOk
        (fun γ tp => specStripSInvariant_libcruxHmacSpecOf γ mmpl tp brkStart hKeepMallocng lim)
        (fun _ _ => specPreservesFsTrace_withFsTraceExact _)
        (fun γ tp => prePC_libcruxHmacSpecOf γ mmpl tp brkStart lim)
        (fun γ tp => outPC_libcruxHmacSpecOf γ mmpl tp brkStart lim)
        hnoex_f3 hfr hSF hlr_out hlr_ne hCodeSub
    have hhook_exact_eq :
        f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
            (fun γ tp => withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp))
            (libcruxHmacHookMallocng mmpl sha256Compress) u =
          f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
            (libcruxHmacSpecOf mmpl brkStart lim)
            (libcruxHmacHookMallocng mmpl sha256Compress) u := rfl
    rw [hhook_exact_eq] at hvis hfr_sf hfs_sf
    have hStubSteps : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        u (u.setPC entryTarget) :=
      hStub W u hpc hrun hfr hCodeSub
    have hBodySteps : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC entryTarget)
        (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim u) := by
      rw [heq_f3]
      exact steps_externOnly_to_real_of_visitedIn_inKeep rfl
        (fun _ hk hsub => hRealHullNoExt W hk hsub)
        (fun pc f he => by
          obtain ⟨rfl, hreal⟩ := hPanReal W pc f he
          exact hreal)
        hvis
    rw [← heq_f3] at hfr_sf hfs_sf
    exact ⟨hStubSteps.trans hBodySteps, hfr_sf,
      hInvKeep u (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim u) hInvU hkf hfs_sf⟩

theorem libcruxHmacGhost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_entry_none : P_sub.externAt? entryTarget = none)
    (hkeep_entry : keep entryTarget = true)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withHooksUnfetched P_sub (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hTargetEq : libsignalSessionLib.resolve mpl lsLibcruxHmacSym = entryTarget)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked) :
    GhostRowReplayOn mpl mmpl InvS EG lsLibcruxHmacSym (fun _ => True)
      (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim) :=
  libcruxHmacGhost_rowReplayOn_of_stub mpl mmpl keep P_sub entryTarget brkStart lim InvS EG
    hsvc_sub hKeepMallocng hOk hStubFrozen hCL_strip hInvKeep hKeep hlr_ne_stub
    hRealHullNoExt hPanReal
    (fun W => by rw [hTargetEq]; exact hRealHullNoExt W hkeep_entry hsub_entry_none)
    (fun _ u hpc _ _ _ => by
      rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)]
      exact Steps.refl _)

theorem libcruxHmacGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_entry_none : P_sub.externAt? entryTarget = none)
    (hkeep_entry : keep entryTarget = true)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withHooksUnfetched P_sub (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hTargetEq : libsignalSessionLib.resolve mpl lsLibcruxHmacSym = entryTarget)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked) :
    GhostRowOk mpl mmpl InvS EG lsLibcruxHmacSym (fun _ => True)
      (libcruxHmacGhost keep P_sub entryTarget mmpl brkStart lim) :=
  ⟨libcruxHmacGhost_rowSpecOk keep P_sub entryTarget mmpl brkStart lim,
   libcruxHmacGhost_rowReplayOn mpl mmpl keep P_sub entryTarget brkStart lim InvS EG
     hsvc_sub hsub_entry_none hkeep_entry hKeepMallocng hOk hStubFrozen hTargetEq hCL_strip hInvKeep
     hKeep hlr_ne_stub hRealHullNoExt hPanReal⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LibcruxHmacGhostReplays

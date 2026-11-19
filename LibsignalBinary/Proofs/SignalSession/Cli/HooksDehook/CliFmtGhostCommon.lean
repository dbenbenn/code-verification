/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns -- proof-setup: allow-public-import

/-!
# Shared Panic-Extern, `stubFrozenGuard`, and `.rodata`-Guarded Ghost-Hook Combinators

Combinators (`stubFrozenGuard`, `withStubPermRO`, `withRoMemGuard`, `withFsTraceExact`,
`f3LinkedCallHook_ok_at_stubFrozen` (`_ro`), and `f3LinkedCallHook_externOnly_visitedIn_with_externs`
(`_ro`)) for directly linked allocating Rust `core::fmt` / `alloc::fmt` rows
(`lsFmtWriteSym`, `lsFormatInnerSym`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon

open Arm64 ProofLib ProofLib.SepLogic
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant keepFsTrace
   satisfies_of_stripExecOutside satisfies_stripExecOutside)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
  (StripCommExtern externOnlyStdProg keepOrSubExtern stepsVisitedIn_of_stripS_with_externs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det)

/-- `(γ, tp)`-existentialized active precondition for `f3LinkedCallHook`: holds at `s0` whenever
there exist `γ : GhostName`, `tp : BitVec 64`, `x`, and `R` satisfying `(specOf γ tp).pre x s0 ∗ R`. -/
@[expose] def ActiveF3CallPre {α : Type} (specOf : GhostName → BitVec 64 → Spec α) (s0 : State) : Prop :=
  s0.status = .Running ∧ s0.spAligned = true ∧
    ∃ (γ : GhostName) (tp : BitVec 64) (x : α) (R : SepProp),
      s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R

/-- `(γ, tp)`-independent linked ghost-call hook: returns the deterministic first-stop state of
`P_real` from `s0.setPC entryTarget` under `ActiveF3CallPre` and `ActiveRealRun`, delegates to
`keepFsTrace fallback s0` outside `ActiveRealRun`, and sets `.Exception` outside `ActiveF3CallPre`. -/
@[expose] noncomputable def f3LinkedCallHook {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State) (s0 : State) : State := by
  classical
  exact
    if _ : ActiveF3CallPre specOf s0 then
      if hReal : ActiveRealRun keep P_real P_sub entryTarget s0 then
        Classical.choose hReal.2.2.2
      else
        keepFsTrace fallback s0
    else
      { s0 with status := .Exception "ghost-hook precondition violated" }

theorem f3LinkedCallHook_fs {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State) (s0 : State) :
    (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0).fs = s0.fs := by
  classical
  unfold f3LinkedCallHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.1
    · rfl
  · rfl

theorem f3LinkedCallHook_fsT {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State) :
    HookFsTraced IsFsC (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback) := by
  classical
  intro s0
  unfold f3LinkedCallHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.2.1
    · exact FsTraced.of_eq rfl rfl
  · exact FsTraced.of_eq rfl rfl

/-- Guard asserting every extern stub PC of `P_sub` is mapped readable and non-writable (`r = true`,
    `w = false`) in `s.mem`, so `stripExecOutside keep s.mem` leaves it `Frozen` and non-executable. -/
@[expose] def stubFrozenGuard (P_sub : Program) (s : State) : Prop :=
  ∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
    (s.mem.perm pc).r = true ∧ (s.mem.perm pc).w = false

/-- Prepend pure read-only non-executable extern-stub guard on `s0.mem` to `spec.pre`. -/
@[expose] def withStubPermRO (P_sub : Program) {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 =>
      ⌜∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
        (s0.mem.perm pc).r = true ∧ (s0.mem.perm pc).w = false ∧ (s0.mem.perm pc).x = false⌝ ∗
      spec.pre x s0 }

/-- Prepend pure read-only memory invariant `⌜roGuard s0.mem⌝` (e.g. `.rodata` slices/vtables) to
    `spec.pre`, leaving `.post`, `.onPanic`, `.onExit`, and `.onOom` definitionally (`rfl`) unchanged. -/
@[expose] def withRoMemGuard (roGuard : Memory → Prop) {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => ⌜roGuard s0.mem⌝ ∗ spec.pre x s0 }

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

theorem stubPermRO_stripExecOutside_of_stubFrozen
    {keep : BitVec 64 → Bool} {P_sub : Program} {u : State}
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hSF : stubFrozenGuard P_sub u) :
    ∀ pc : BitVec 64,
      P_sub.externAt? pc ≠ none →
      ((stripExecOutside keep u.mem).perm pc).r = true ∧
        ((stripExecOutside keep u.mem).perm pc).w = false ∧
        ((stripExecOutside keep u.mem).perm pc).x = false := by
  intro pc hext
  have hk : keep pc = false := by
    cases h : keep pc
    · rfl
    · exact absurd (hsub_out_keep pc h) hext
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
      simp only [hk, Bool.false_or]
      rcases p with ⟨r, w, x, lf, an⟩
      cases r <;> cases w <;> cases x <;>
        simp_all [Option.r, Option.w, Option.x, Perm.rwx]

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

theorem real_subroutine_run_visitedIn_of_stripS_with_stubPermRO_ro {α : Type}
    {keep : BitVec 64 → Bool} {roGuard : Memory → Prop}
    {P1 P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    {s0 : State} (hsvc1 : P1.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P1.externAt? pc = none)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → P1.externAt? pc = some f ∧ StripCommExtern keep f)
    (hRoStrip : ∀ m : Memory, roGuard m → roGuard (stripExecOutside keep m))
    (hOk : subroutine_ok P_sub entryTarget (withStubPermRO P_sub (withRoMemGuard roGuard spec)))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} (hRun : s0.status = .Running) (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R) (hFr : ExecFrozen s0.mem)
    (hSF : stubFrozenGuard P_sub s0) (hRo : roGuard s0.mem)
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
  have hro_stub : ∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
      (s1'.mem.perm pc).r = true ∧ (s1'.mem.perm pc).w = false ∧ (s1'.mem.perm pc).x = false :=
    stubPermRO_stripExecOutside_of_stubFrozen hsub_out_keep hSF
  have hro_mem : roGuard s1'.mem := hRoStrip s0.mem hRo
  have hs1'_pre_ro :
      s1'.mem ⊨ (withStubPermRO P_sub (withRoMemGuard roGuard spec)).pre x s1' ∗ R := by
    dsimp only [withStubPermRO, withRoMemGuard]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hro_stub, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hro_mem, hs1'_pre⟩
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_pre_ro hSp hCodeSub
  have hout_base : SubroutineOutcome spec x R s1' sf' := hout'
  have hstop1' : SubroutineStop s1' sf' := subroutineOutcome_to_stop hout_base
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout_base
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, hvis⟩ :=
    stepsVisitedIn_of_stripS_with_externs hsvc1 hsvc_sub hext1_no hext_sub
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

theorem real_subroutine_run_visitedIn_of_stripS_with_stubPermRO {α : Type}
    {keep : BitVec 64 → Bool} {P1 P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    {s0 : State} (hsvc1 : P1.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P1.externAt? pc = none)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → P1.externAt? pc = some f ∧ StripCommExtern keep f)
    (hOk : subroutine_ok P_sub entryTarget (withStubPermRO P_sub spec))
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
  refine real_subroutine_run_visitedIn_of_stripS_with_stubPermRO_ro
    (roGuard := fun _ => True) hsvc1 hsvc_sub hext1_no hsub_out_keep hext_sub
    (fun _ _ => trivial) ?_ hInv hFsT hPrePC hOutPC hRun hSp hPre hFr hSF trivial
    hlr_out hlr_ne hCodeSub
  apply subroutine_ok.of_codeLoaded
  intro x' R' s' hpc' hrun' hpre' hsp' _hL
  dsimp only [withStubPermRO, withRoMemGuard] at hpre'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨h1, h2⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at h2
  have hp : s'.mem ⊨ (withStubPermRO P_sub spec).pre x' s' ∗ R' := by
    dsimp only [withStubPermRO]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨h1, h2.2⟩
  exact hOk.mono_outcome x' R' s' hpc' hrun' hp hsp' (fun _ h => h)

theorem f3LinkedCallHook_ok_at_stubFrozen_ro {α : Type}
    {keep : BitVec 64 → Bool} {roGuard : Memory → Prop}
    {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (hRoStrip : ∀ m : Memory, roGuard m → roGuard (stripExecOutside keep m))
    (γ : GhostName) (tp : BitVec 64)
    (hlr_ne_pre : ∀ x (R : SepProp) (s0 : State),
      (s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hOk : subroutine_ok P_sub entryTarget (withStubPermRO P_sub (withRoMemGuard roGuard (specOf γ tp))))
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
    (hRo : roGuard s0.mem)
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
      real_subroutine_run_visitedIn_of_stripS_with_stubPermRO_ro hsvc_real hsvc_sub hreal_no
        hsub_out_keep hext_sub hRoStrip hOk hInv hFsT hPrePC hOutPC hrun hsp hpre hReal.1 hSF hRo
        hReal.2.1 (hlr_ne_pre x R s0 hpre) hReal.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
  · simp only [hReal, ↓reduceDIte]
    exact hFallbackOk x R s0 hrun hpre hsp

theorem f3LinkedCallHook_ok_at_stubFrozen {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (γ : GhostName) (tp : BitVec 64)
    (hlr_ne_pre : ∀ x (R : SepProp) (s0 : State),
      (s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hOk : subroutine_ok P_sub entryTarget (withStubPermRO P_sub (specOf γ tp)))
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
      real_subroutine_run_visitedIn_of_stripS_with_stubPermRO hsvc_real hsvc_sub hreal_no
        hsub_out_keep hext_sub hOk hInv hFsT hPrePC hOutPC hrun hsp hpre hReal.1 hSF
        hReal.2.1 (hlr_ne_pre x R s0 hpre) hReal.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
  · simp only [hReal, ↓reduceDIte]
    exact hFallbackOk x R s0 hrun hpre hsp

theorem f3LinkedCallHook_activeF3CallPre_of_noException {α : Type}
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

theorem f3LinkedCallHook_externOnly_visitedIn_with_externs_ro {α : Type}
    {keep : BitVec 64 → Bool} {roGuard : Memory → Prop} {P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hRoStrip : ∀ m : Memory, roGuard m → roGuard (stripExecOutside keep m))
    (hOk : ∀ γ tp,
      subroutine_ok P_sub entryTarget (withStubPermRO P_sub (withRoMemGuard roGuard (specOf γ tp))))
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
    (hFr : ExecFrozen u.mem) (hSF : stubFrozenGuard P_sub u) (hRo : roGuard u.mem)
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
  obtain ⟨sf, huntil_sf, hstop_sf, _, hfs_sf, _, hfr_sf, hvis_sf⟩ :=
    real_subroutine_run_visitedIn_of_stripS_with_stubPermRO_ro
      (P1 := externOnlyStdProg P_sub) rfl hsvc_sub hsub_out_keep hsub_out_keep
      (fun pc f he => ⟨he, hcomm pc f he⟩) hRoStrip
      (hOk γ tp) (hInv γ tp) (hFsT γ tp) (hPrePC γ tp) (hOutPC γ tp)
      hrun hsp hpre hFr hSF hRo hlr_out hlr_ne hCodeSub
  have hReal : ActiveRealRun keep (externOnlyStdProg P_sub) P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil_sf, hstop_sf, hfs_sf,
      (by
        obtain ⟨sf2, huntil2, hstop2, _, _, hfst0, _, _⟩ :=
          real_subroutine_run_visitedIn_of_stripS_with_stubPermRO_ro
            (P1 := externOnlyStdProg P_sub) rfl hsvc_sub hsub_out_keep hsub_out_keep
            (fun pc f he => ⟨he, hcomm pc f he⟩) hRoStrip
            (hOk γ tp) (hInv γ tp) (hFsT γ tp) (hPrePC γ tp) (hOutPC γ tp)
            hrun hsp hpre hFr hSF hRo hlr_out hlr_ne hCodeSub
        have heq := h2fsgen_stepsUntil_det huntil2 hstop2 huntil_sf hstop_sf
        exact heq ▸ hfst0),
      hfr_sf⟩
  have hhook_eq :
      f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u = sf := by
    unfold f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    exact h2fsgen_stepsUntil_det (Classical.choose_spec hReal.2.2.2).1
      (Classical.choose_spec hReal.2.2.2).2.1 huntil_sf hstop_sf
  rw [hhook_eq]
  exact ⟨hvis_sf, hfr_sf, hfs_sf⟩

theorem f3LinkedCallHook_externOnly_visitedIn_with_externs {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget (withStubPermRO P_sub (specOf γ tp)))
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
    real_subroutine_run_visitedIn_of_stripS_with_stubPermRO
      (P1 := externOnlyStdProg P_sub) rfl hsvc_sub hsub_out_keep hsub_out_keep
      (fun pc f he => ⟨he, hcomm pc f he⟩)
      (hOk γ tp) (hInv γ tp) (hFsT γ tp) (hPrePC γ tp) (hOutPC γ tp)
      hrun hsp hpre hFr hSF hlr_out hlr_ne hCodeSub
  have hReal : ActiveRealRun keep (externOnlyStdProg P_sub) P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil_sf, hstop_sf, hfs_sf, hfst_sf, hfr_sf⟩
  have hhook_eq :
      f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u = sf := by
    unfold f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    exact h2fsgen_stepsUntil_det (Classical.choose_spec hReal.2.2.2).1
      (Classical.choose_spec hReal.2.2.2).2.1 huntil_sf hstop_sf
  rw [hhook_eq]
  exact ⟨hvis_sf, hfr_sf, hfs_sf⟩

/-- Exact `fs` and `trace` preservation across all subroutine outcomes
    (`sf.fs = s0.fs ∧ sf.trace = s0.trace`). -/
@[expose] def SpecPreservesFsTraceExact {α : Type} (spec : Spec α) : Prop :=
  ∀ x (R : SepProp) (s0 sf : State),
    SubroutineOutcome spec x R s0 sf → sf.fs = s0.fs ∧ sf.trace = s0.trace

theorem specPreservesFsTraceExact_withFsTraceExact {α : Type} (spec : Spec α) :
    SpecPreservesFsTraceExact (withFsTraceExact spec) := by
  intro x R s0 sf hout
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

/-- Exact-trace counterpart of `ActiveRealRun` (`sf.trace = s0.trace`). -/
@[expose] def ActiveRealRunExact
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (s0 : State) : Prop :=
  ExecFrozen s0.mem ∧
    keep (s0.readReg64 .lr) = false ∧
    P_sub.CodeLoaded (stripExecOutside keep s0.mem) ∧
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      ExecFrozen sf.mem

/-- `(γ, tp)`-independent linked ghost-call hook with unconditional exact `trace` preservation
    (`(f3LinkedCallHookExact ... s0).trace = s0.trace`). -/
@[expose] noncomputable def f3LinkedCallHookExact {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State) (s0 : State) : State := by
  classical
  exact
    if _ : ActiveF3CallPre specOf s0 then
      if hReal : ActiveRealRunExact keep P_real P_sub entryTarget s0 then
        Classical.choose hReal.2.2.2
      else
        keepFsTrace fallback s0
    else
      { s0 with status := .Exception "ghost-hook precondition violated" }

theorem f3LinkedCallHookExact_fs {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State) (s0 : State) :
    (f3LinkedCallHookExact keep P_real P_sub entryTarget specOf fallback s0).fs = s0.fs := by
  classical
  unfold f3LinkedCallHookExact
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.1
    · rfl
  · rfl

theorem f3LinkedCallHookExact_trace {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State) (s0 : State) :
    (f3LinkedCallHookExact keep P_real P_sub entryTarget specOf fallback s0).trace = s0.trace := by
  classical
  unfold f3LinkedCallHookExact
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.2.1
    · rfl
  · rfl

theorem f3LinkedCallHookExact_fsT {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State) :
    HookFsTraced IsFsC (f3LinkedCallHookExact keep P_real P_sub entryTarget specOf fallback) := by
  intro s0
  exact FsTraced.of_eq
    (f3LinkedCallHookExact_trace keep P_real P_sub entryTarget specOf fallback s0)
    (congrArg FsState.files
      (f3LinkedCallHookExact_fs keep P_real P_sub entryTarget specOf fallback s0))

theorem real_subroutine_run_visitedIn_of_stripS_with_stubPermRO_ro_exact {α : Type}
    {keep : BitVec 64 → Bool} {roGuard : Memory → Prop}
    {P1 P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    {s0 : State} (hsvc1 : P1.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P1.externAt? pc = none)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → P1.externAt? pc = some f ∧ StripCommExtern keep f)
    (hRoStrip : ∀ m : Memory, roGuard m → roGuard (stripExecOutside keep m))
    (hOk : subroutine_ok P_sub entryTarget (withStubPermRO P_sub (withRoMemGuard roGuard spec)))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTraceExact spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} (hRun : s0.status = .Running) (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R) (hFr : ExecFrozen s0.mem)
    (hSF : stubFrozenGuard P_sub s0) (hRo : roGuard s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P1 (SubroutineStop s0) (s0.setPC entryTarget) sf ∧ SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
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
  have hro_stub : ∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
      (s1'.mem.perm pc).r = true ∧ (s1'.mem.perm pc).w = false ∧ (s1'.mem.perm pc).x = false :=
    stubPermRO_stripExecOutside_of_stubFrozen hsub_out_keep hSF
  have hro_mem : roGuard s1'.mem := hRoStrip s0.mem hRo
  have hs1'_pre_ro :
      s1'.mem ⊨ (withStubPermRO P_sub (withRoMemGuard roGuard spec)).pre x s1' ∗ R := by
    dsimp only [withStubPermRO, withRoMemGuard]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hro_stub, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hro_mem, hs1'_pre⟩
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_pre_ro hSp hCodeSub
  have hout_base : SubroutineOutcome spec x R s1' sf' := hout'
  have hstop1' : SubroutineStop s1' sf' := subroutineOutcome_to_stop hout_base
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout_base
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, hvis⟩ :=
    stepsVisitedIn_of_stripS_with_externs hsvc1 hsvc_sub hext1_no hext_sub
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
  obtain ⟨hfs, htr⟩ := hFsT x R s0 sf hout0
  exact ⟨sf, huntil, hstop_sf, hout0, hfs, htr, hfr_sf, hvis⟩

theorem f3LinkedCallHookExact_ok_at_stubFrozen_ro {α : Type}
    {keep : BitVec 64 → Bool} {roGuard : Memory → Prop}
    {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (hRoStrip : ∀ m : Memory, roGuard m → roGuard (stripExecOutside keep m))
    (γ : GhostName) (tp : BitVec 64)
    (hlr_ne_pre : ∀ x (R : SepProp) (s0 : State),
      (s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hOk : subroutine_ok P_sub entryTarget (withStubPermRO P_sub (withRoMemGuard roGuard (specOf γ tp))))
    (hInv : SpecStripSInvariant keep (specOf γ tp))
    (hFsT : SpecPreservesFsTraceExact (specOf γ tp))
    (hPrePC : ∀ x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) (specOf γ tp))
    {x : α} {R : SepProp} {s0 : State}
    (hSF : stubFrozenGuard P_sub s0)
    (hRo : roGuard s0.mem)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    s0.mem.KeepsFrozen
        (f3LinkedCallHookExact keep P_real P_sub entryTarget specOf fallback s0).mem ∧
      (f3LinkedCallHookExact keep P_real P_sub entryTarget specOf fallback s0).symtab = s0.symtab ∧
      SubroutineOutcome (specOf γ tp) x R s0
        (f3LinkedCallHookExact keep P_real P_sub entryTarget specOf fallback s0) := by
  classical
  have hActPre : ActiveF3CallPre specOf s0 := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  unfold f3LinkedCallHookExact
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveRealRunExact keep P_real P_sub entryTarget s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _, _⟩ :=
      real_subroutine_run_visitedIn_of_stripS_with_stubPermRO_ro_exact hsvc_real hsvc_sub hreal_no
        hsub_out_keep hext_sub hRoStrip hOk hInv hFsT hPrePC hOutPC hrun hsp hpre hReal.1 hSF hRo
        hReal.2.1 (hlr_ne_pre x R s0 hpre) hReal.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
  · simp only [hReal, ↓reduceDIte]
    exact hFallbackOk x R s0 hrun hpre hsp

theorem f3LinkedCallHookExact_activeF3CallPre_of_noException {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State} {u : State}
    (hnoex : ∀ msg,
      (f3LinkedCallHookExact keep P_real P_sub entryTarget specOf fallback u).status ≠
        .Exception msg) :
    ActiveF3CallPre specOf u := by
  classical
  by_contra hnot
  have hex :
      (f3LinkedCallHookExact keep P_real P_sub entryTarget specOf fallback u).status =
        .Exception "ghost-hook precondition violated" := by
    unfold f3LinkedCallHookExact
    simp only [hnot, ↓reduceDIte]
  exact hnoex _ hex

theorem f3LinkedCallHookExact_externOnly_visitedIn_with_externs_ro {α : Type}
    {keep : BitVec 64 → Bool} {roGuard : Memory → Prop} {P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hRoStrip : ∀ m : Memory, roGuard m → roGuard (stripExecOutside keep m))
    (hOk : ∀ γ tp,
      subroutine_ok P_sub entryTarget (withStubPermRO P_sub (withRoMemGuard roGuard (specOf γ tp))))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTraceExact (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    {u : State}
    (hnoex : ∀ msg,
      (f3LinkedCallHookExact keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hSF : stubFrozenGuard P_sub u) (hRo : roGuard u.mem)
    (hlr_out : keep (u.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) (externOnlyStdProg P_sub)
        (u.setPC entryTarget)
        (f3LinkedCallHookExact keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u) ∧
      ExecFrozen
        (f3LinkedCallHookExact keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).mem ∧
      (f3LinkedCallHookExact keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).fs =
        u.fs := by
  classical
  obtain ⟨hrun, hsp, γ, tp, x, R, hpre⟩ :=
    f3LinkedCallHookExact_activeF3CallPre_of_noException hnoex
  have hActPre : ActiveF3CallPre specOf u := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  obtain ⟨sf, huntil_sf, hstop_sf, _, hfs_sf, htr_sf, hfr_sf, hvis_sf⟩ :=
    real_subroutine_run_visitedIn_of_stripS_with_stubPermRO_ro_exact
      (P1 := externOnlyStdProg P_sub) rfl hsvc_sub hsub_out_keep hsub_out_keep
      (fun pc f he => ⟨he, hcomm pc f he⟩) hRoStrip
      (hOk γ tp) (hInv γ tp) (hFsT γ tp) (hPrePC γ tp) (hOutPC γ tp)
      hrun hsp hpre hFr hSF hRo hlr_out hlr_ne hCodeSub
  have hReal : ActiveRealRunExact keep (externOnlyStdProg P_sub) P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil_sf, hstop_sf, hfs_sf, htr_sf, hfr_sf⟩
  have hhook_eq :
      f3LinkedCallHookExact keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u = sf := by
    unfold f3LinkedCallHookExact
    simp only [hActPre, hReal, ↓reduceDIte]
    exact h2fsgen_stepsUntil_det (Classical.choose_spec hReal.2.2.2).1
      (Classical.choose_spec hReal.2.2.2).2.1 huntil_sf hstop_sf
  rw [hhook_eq]
  exact ⟨hvis_sf, hfr_sf, hfs_sf⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon

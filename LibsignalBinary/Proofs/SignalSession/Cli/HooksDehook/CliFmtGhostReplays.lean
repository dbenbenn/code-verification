/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtSubroutineProofs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FmtWriteRowSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FormatInnerRowSpec
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Ghost Hooks and `GhostRowReplayOn` for `lsFmtWriteSym` and `lsFormatInnerSym`

`CliGhostHooks.extra` ghost hooks and block-617 replay proofs for the two allocating formatting
rows (`lsFmtWriteSym` and `lsFormatInnerSym`):

- `stubGuardedF3GhostRo` (§1): wraps `f3LinkedCallHookExact` on `externOnlyStdProg P_sub` inside a
  `stubFrozenGuard P_sub s0 ∧ roGuard s0.mem` check with fallback `keepFsTrace fallback s0`. The
  resulting hook is independent of `W : CliHooks`, `γ : GhostName`, `tp : BitVec 64`, and caller
  `Env`, gives unconditional `_fs`, `_trace`, `_fsT`, `_preserves_execFrozen`, and `HookOk` without
  `stubFrozenGuard` or `.rodata` hypotheses at caller sites, and yields `GhostRowReplayOn`
  (`entryGuard := fun _ => True`) when `InvS u` implies `stubFrozenGuard P_sub u`, `roGuard u.mem`,
  and `P_sub.CodeLoaded (stripExecOutside keep u.mem)`.
- `fmtWriteProtoAddrGhost` (`lsFmtWriteSym`, §2) and `formatInnerLsCallGhost`
  (`lsFormatInnerSym`, §3): `[LibsignalPlacement]`-native instantiations over
  `fineHookRustCliAllocBudget γ mmpl tp brkStart` with return-address guards (`withLsRetFmtWrite` /
  `withLsRetFormatInner`) and `ExactOrNilEnv c.exactEvs`, lifting to any caller `Env` containing
  `[]` (including `CliFmtWriteEnv`, `CliFormatInnerEnv`, `MsgDeserErrEnv`, `FmtWriteEnv`,
  `FormatInnerEnv`, and `SeqEnv` stages) and satisfying `FmtWriteRowSpec`, `FormatInnerRowSpec`,
  and `GhostRowReplayOn`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostReplays

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (fmtWriteHook0 formatInnerHook0)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj (lsFmtWriteSym lsFormatInnerSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (perm_writeVecHeader)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen SpecStripSInvariant keepFsTrace)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (fineHookRustCliAllocBudget_pool_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (ActiveF3CallPre)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon
  (ActiveRealRunExact SpecPreservesFsTraceExact f3LinkedCallHookExact
   f3LinkedCallHookExact_activeF3CallPre_of_noException
   f3LinkedCallHookExact_externOnly_visitedIn_with_externs_ro
   f3LinkedCallHookExact_fs f3LinkedCallHookExact_ok_at_stubFrozen_ro
   f3LinkedCallHookExact_trace specPreservesFsTraceExact_withFsTraceExact
   stubFrozenGuard withFsTraceExact withRoMemGuard withStubPermRO)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
  (CliFmtWriteProtoAddrCall CliFmtWriteVtableKind CliFormatInnerLsCall
   LsRetAddrFmtWrite LsRetAddrFormatInner
   cliFmtWriteProtoAddrSpec cliFormatInnerLsCallSpec
   extract_withLsRetFmtWrite extract_withLsRetFormatInner
   fmtWriteHook0_cliProtoAddr_ok fmtWriteProtoAddrCliLsSpec fmtWriteProtoAddrLsEnvSpec
   formatInnerCallCliLsSpec formatInnerCallLsEnvSpec formatInnerHook0_cliLsCallSpec_ok
   intro_withLsRetFmtWrite intro_withLsRetFormatInner
   withLsRetFmtWrite withLsRetFormatInner)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
  (ExactOrNilEnv cliFmtWriteEnv_nil cliFormatInnerEnv_nil
   exactOrNilEnv_exact exactOrNilEnv_imp exactOrNilEnv_nil fitsEnv_exactOrNil)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtSubroutineProofs
  (CliFmtWriteSubLink CliFormatInnerSubLink
   cliAllocFormatInner_lsCall_ro_ok cliCoreFmtWrite_protoAddr_ro_ok
   cliFmtWriteRoGuard cliFmtWriteRoGuard_stripExecOutside
   cliFormatInnerRoGuard cliFormatInnerRoGuard_stripExecOutside)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
  (StripCommExtern externOnlyStdProg steps_externOnly_to_real_of_visitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FmtWriteRowSpec
  (FmtWriteRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FormatInnerRowSpec
  (FormatInnerRowSpec)
open VerifiedLibraries.RustStd
  (allocFormatInnerSym allocMultiLib coreFmtWriteSym coreMultiLib)

/-! ## 1. Generic `stubFrozenGuard ∧ roGuard`-Guarded `f3LinkedCallHookExact` Combinator -/

/-- `W`-independent `(γ, tp)`-generic ghost hook guarded by `stubFrozenGuard P_sub s0 ∧ roGuard s0.mem`:
    executes `f3LinkedCallHookExact` on `externOnlyStdProg P_sub` when extern stubs are frozen/RO
    and the `.rodata` image invariant `roGuard s0.mem` holds, and falls back to
    `keepFsTrace fallback` otherwise so `HookOk`, `.fs = s0.fs`, and `.trace = s0.trace` hold
    unconditionally. -/
@[expose] noncomputable def stubGuardedF3GhostRo {α : Type}
    (keep : BitVec 64 → Bool) (roGuard : Memory → Prop)
    (P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State)
    (s0 : State) : State := by
  classical
  exact if stubFrozenGuard P_sub s0 ∧ roGuard s0.mem then
    f3LinkedCallHookExact keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback s0
  else
    keepFsTrace fallback s0

theorem subroutine_ok_withStubPermRO_ro {α : Type} {roGuard : Memory → Prop}
    {P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    (hOk : subroutine_ok P_sub entryTarget (withRoMemGuard roGuard spec)) :
    subroutine_ok P_sub entryTarget (withStubPermRO P_sub (withRoMemGuard roGuard spec)) := by
  apply subroutine_ok.of_codeLoaded
  intro x R₀ s0 hpc hrun hpre hsp0 _hLP
  dsimp only [withStubPermRO] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hOk.mono_outcome x R₀ s0 hpc hrun hpre.2 hsp0 (fun _ hout => hout)

theorem stubGuardedF3GhostRo_fs {α : Type}
    (keep : BitVec 64 → Bool) (roGuard : Memory → Prop)
    (P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) (s0 : State) :
    (stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback s0).fs = s0.fs := by
  classical
  unfold stubGuardedF3GhostRo
  split
  · exact f3LinkedCallHookExact_fs keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback s0
  · rfl

theorem stubGuardedF3GhostRo_trace {α : Type}
    (keep : BitVec 64 → Bool) (roGuard : Memory → Prop)
    (P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) (s0 : State) :
    (stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback s0).trace = s0.trace := by
  classical
  unfold stubGuardedF3GhostRo
  split
  · exact f3LinkedCallHookExact_trace keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback s0
  · rfl

theorem stubGuardedF3GhostRo_fsT {α : Type}
    (keep : BitVec 64 → Bool) (roGuard : Memory → Prop)
    (P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) (s0 : State) :
    FsTraced IsFsC s0 (stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback s0) :=
  FsTraced.of_eq
    (stubGuardedF3GhostRo_trace keep roGuard P_sub entryTarget specOf fallback s0)
    (congrArg FsState.files
      (stubGuardedF3GhostRo_fs keep roGuard P_sub entryTarget specOf fallback s0))

theorem stubGuardedF3GhostRo_preserves_execFrozen {α : Type}
    (keep : BitVec 64 → Bool) (roGuard : Memory → Prop)
    (P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) {fallback : State → State}
    (hFallbackPerm : ∀ s : State, (fallback s).mem.perm = s.mem.perm)
    {u : State} (_hrun : u.status = .Running)
    (_hnoex : ∀ msg,
      (stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) :
    ExecFrozen (stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback u).mem ∧
      (stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback u).fs = u.fs := by
  classical
  refine ⟨?_, stubGuardedF3GhostRo_fs keep roGuard P_sub entryTarget specOf fallback u⟩
  unfold stubGuardedF3GhostRo
  split
  · unfold f3LinkedCallHookExact
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
      · exact ExecFrozen.of_perm_eq hFr (congrFun (hFallbackPerm u))
    · exact hFr
  · exact ExecFrozen.of_perm_eq hFr (congrFun (hFallbackPerm u))

/-- Unconditional `HookOk` for `stubGuardedF3GhostRo` (zero `stubFrozenGuard` or `roGuard`
    hypotheses at caller sites). -/
theorem stubGuardedF3GhostRo_ok {α : Type}
    {keep : BitVec 64 → Bool} {roGuard : Memory → Prop}
    {P_sub : Program} {entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α} {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hRoStrip : ∀ m : Memory, roGuard m → roGuard (stripExecOutside keep m))
    (γ : GhostName) (tp : BitVec 64)
    (hlr_ne_pre : ∀ x (R : SepProp) (s0 : State),
      (s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hOk : subroutine_ok P_sub entryTarget (withRoMemGuard roGuard (specOf γ tp)))
    (hInv : SpecStripSInvariant keep (specOf γ tp))
    (hFsT : SpecPreservesFsTraceExact (specOf γ tp))
    (hPrePC : ∀ x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) (specOf γ tp)) :
    HookOk (stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback) (specOf γ tp) := by
  classical
  intro x R s0 hrun hpre hsp
  unfold stubGuardedF3GhostRo
  by_cases hG : stubFrozenGuard P_sub s0 ∧ roGuard s0.mem
  · simp only [hG, and_self, ↓reduceIte]
    exact f3LinkedCallHookExact_ok_at_stubFrozen_ro
      (P_real := externOnlyStdProg P_sub) rfl hsvc_sub hsub_out_keep hsub_out_keep
      (fun pc f he => ⟨he, hcomm pc f he⟩) hRoStrip γ tp hlr_ne_pre
      (subroutine_ok_withStubPermRO_ro hOk) hInv hFsT hPrePC hOutPC hFallbackOk
      hG.1 hG.2 hrun hpre hsp
  · simp only [hG, ↓reduceIte]
    exact hFallbackOk x R s0 hrun hpre hsp

/-- Trajectory-aware `GhostRowReplayOn` (`entryGuard := fun _ => True`) for
    `stubGuardedF3GhostRo` at any linked row `sym`. -/
theorem stubGuardedF3GhostRo_rowReplayOn_of_stub {α : Type}
    {mpl mmpl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {sym : String} {keep : BitVec 64 → Bool} {roGuard : Memory → Prop}
    {P_sub : Program} {entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α} {fallback : State → State}
    (hFallbackPerm : ∀ s : State, (fallback s).mem.perm = s.mem.perm)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hRoStrip : ∀ m : Memory, roGuard m → roGuard (stripExecOutside keep m))
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget (withRoMemGuard roGuard (specOf γ tp)))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTraceExact (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hlr_out_pre : ∀ γ tp x (R : SepProp) (u : State),
      (u.mem ⊨ (specOf γ tp).pre x u ∗ R) → keep (u.readReg64 .lr) = false)
    (hlr_ne_pre : ∀ γ tp x (R : SepProp) (u : State),
      (u.mem ⊨ (specOf γ tp).pre x u ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hSubExtInReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl sym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (u.setPC entryTarget))
    (hInvSF : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hInvRo : ∀ u : State, ExecFrozen u.mem → InvS u → roGuard u.mem)
    (hInvCode : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem → v.fs = u.fs → InvS u → InvS v) :
    GhostRowReplayOn mpl mmpl InvS EG sym (fun _ => True)
      (stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback) where
  preserves_execFrozen u hrun hnoex hFr :=
    stubGuardedF3GhostRo_preserves_execFrozen keep roGuard P_sub entryTarget specOf hFallbackPerm
      hrun hnoex hFr
  replay_at_stub W _s0 _sf _ _ _ _ := by
    classical
    refine Or.inr ⟨hRealStubNone W, fun u _ _ hpc hrun hnoex hkf hfr hinv => ?_⟩
    have hSF : stubFrozenGuard P_sub u := hInvSF u hinv
    have hRo : roGuard u.mem := hInvRo u hfr hinv
    have hG : stubFrozenGuard P_sub u ∧ roGuard u.mem := ⟨hSF, hRo⟩
    have hEq :
        stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback u =
          f3LinkedCallHookExact keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u := by
      unfold stubGuardedF3GhostRo; simp only [hG, and_self, ↓reduceIte]
    rw [hEq] at hnoex hkf ⊢
    obtain ⟨_, _, γ, tp, x, R, hpre⟩ :=
      f3LinkedCallHookExact_activeF3CallPre_of_noException hnoex
    have hlr_out : keep (u.readReg64 .lr) = false := hlr_out_pre γ tp x R u hpre
    have hlr_ne := hlr_ne_pre γ tp x R u hpre
    obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
      f3LinkedCallHookExact_externOnly_visitedIn_with_externs_ro
        hsvc_sub hsub_out_keep hcomm hRoStrip
        (fun γ' tp' => subroutine_ok_withStubPermRO_ro (hOk γ' tp'))
        hInv hFsT hPrePC hOutPC hnoex hfr hSF hRo hlr_out hlr_ne (hInvCode u hfr hinv)
    have h1 : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC entryTarget) :=
      hStubSteps W u hpc hrun hfr hinv
    have h2 : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC entryTarget)
        (f3LinkedCallHookExact keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u) :=
      steps_externOnly_to_real_of_visitedIn
        (hRealSvc W) hsub_out_keep (hRealNoExt W) (hSubExtInReal W) hvis
    have hSteps := h1.trans h2
    exact ⟨hSteps, hfr_sf, hInvStep W u _ hSteps hkf hfr_sf hfs_sf hinv⟩

/-! ## 2. `lsFmtWriteSym` (`core::fmt::write`) Ghost Hook & Replay Suite -/

theorem subroutine_ok_withRoMemGuard_withLsRetFmtWrite [LibsignalPlacement] {α : Type}
    {roGuard : Memory → Prop} {P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    (hOk : subroutine_ok P_sub entryTarget (withRoMemGuard roGuard spec)) :
    subroutine_ok P_sub entryTarget (withRoMemGuard roGuard (withLsRetFmtWrite spec)) := by
  apply subroutine_ok.of_codeLoaded
  intro x R₀ s0 hpc hrun hpre hsp0 _hLP
  dsimp only [withRoMemGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, hpreL⟩
  have hpre0 : s0.mem ⊨ (withRoMemGuard roGuard spec).pre x s0 ∗ R₀ := by
    dsimp only [withRoMemGuard]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hro, (extract_withLsRetFmtWrite hpreL).2⟩
  exact hOk.mono_outcome x R₀ s0 hpc hrun hpre0 hsp0 (fun _ hout => hout)

/-- `(γ, tp)`-indexed `withLsRetFmtWrite` specification family for `fmtWriteProtoAddrGhost`. -/
@[expose] def fmtWriteGhostSpecOf [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    Spec (CliFmtWriteProtoAddrCall × fineCostModel.σ) :=
  withLsRetFmtWrite (withFsTraceExact
    (cliFmtWriteProtoAddrSpec fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (fun c => ExactOrNilEnv c.exactEvs)))

/-- `W`-independent ghost hook for `lsFmtWriteSym` (`core::fmt::write`). -/
@[expose] noncomputable def fmtWriteProtoAddrGhost [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (mplCore : MultiPlacement) (mplAllocOf : CliFmtWriteVtableKind → MultiPlacement)
    (mplFmt : MultiPlacement) :
    State → State :=
  stubGuardedF3GhostRo keep (cliFmtWriteRoGuard mplAllocOf mplFmt)
    P_sub (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    (fmtWriteGhostSpecOf mmpl brkStart lim)
    fmtWriteHook0

theorem fmtWriteProtoAddrGhost_rowSpec [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (mplCore : MultiPlacement) (mplAllocOf : CliFmtWriteVtableKind → MultiPlacement)
    (mplFmt : MultiPlacement) :
    FmtWriteRowSpec
      (fmtWriteProtoAddrGhost keep P_sub mmpl brkStart lim mplCore mplAllocOf mplFmt) :=
  trivial

theorem fmtWriteProtoAddrGhost_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (mplCore : MultiPlacement) (mplAllocOf : CliFmtWriteVtableKind → MultiPlacement)
    (mplFmt : MultiPlacement) (s0 : State) :
    (fmtWriteProtoAddrGhost keep P_sub mmpl brkStart lim mplCore mplAllocOf mplFmt s0).fs =
      s0.fs :=
  stubGuardedF3GhostRo_fs _ _ _ _ _ _ s0

theorem fmtWriteProtoAddrGhost_trace [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (mplCore : MultiPlacement) (mplAllocOf : CliFmtWriteVtableKind → MultiPlacement)
    (mplFmt : MultiPlacement) (s0 : State) :
    (fmtWriteProtoAddrGhost keep P_sub mmpl brkStart lim mplCore mplAllocOf mplFmt s0).trace =
      s0.trace :=
  stubGuardedF3GhostRo_trace _ _ _ _ _ _ s0

theorem fmtWriteProtoAddrGhost_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (mplCore : MultiPlacement) (mplAllocOf : CliFmtWriteVtableKind → MultiPlacement)
    (mplFmt : MultiPlacement) (s0 : State) :
    FsTraced IsFsC s0
      (fmtWriteProtoAddrGhost keep P_sub mmpl brkStart lim mplCore mplAllocOf mplFmt s0) :=
  stubGuardedF3GhostRo_fsT _ _ _ _ _ _ s0

theorem fmtWriteGhostSpecOf_stripSInvariant [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64) :
    SpecStripSInvariant keep (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) where
  pre_eq := by
    rintro ⟨c, st0⟩ s
    dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact, cliFmtWriteProtoAddrSpec]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st0 s]
    rfl
  post_eq := by
    rintro ⟨c, st0⟩ s0 sf
    dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact, cliFmtWriteProtoAddrSpec]
    have hp := fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim
    have hacp : ∀ a b : State,
        LibsignalBinary.Heap.AllocCallPreserved (stripS keep a) b =
          LibsignalBinary.Heap.AllocCallPreserved a b := by
      intro a b; cases a; rfl
    simp only [hp, hacp]
    rfl
  onPanic_eq := by
    rintro ⟨c, st0⟩ s0 sf; rfl
  onExit_eq := by
    rintro ⟨c, st0⟩ _ s0 sf; rfl
  onOom_eq := by
    rintro ⟨c, st0⟩ s0 sf; rfl

theorem fmtWriteGhostSpecOf_pre_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64)
    (x : CliFmtWriteProtoAddrCall × fineCostModel.σ) (s : State) (pc : BitVec 64) :
    (fmtWriteGhostSpecOf mmpl brkStart lim γ tp).pre x (s.setPC pc) =
      (fmtWriteGhostSpecOf mmpl brkStart lim γ tp).pre x s := by
  rcases x with ⟨c, st0⟩
  dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact, cliFmtWriteProtoAddrSpec]
  have hp :
      (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim st0 (s.setPC pc) =
        (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim st0 s :=
    LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj.pool_of_setPC
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim st0 s pc
  rw [hp]
  rfl

theorem fmtWriteGhostSpecOf_outcome_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64)
    (x : CliFmtWriteProtoAddrCall × fineCostModel.σ) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) x R (s0.setPC pc) sf) :
    SubroutineOutcome (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) x R s0 sf := by
  rcases x with ⟨c, st0⟩
  rcases h with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨ec, he, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, ?_, hpost⟩
    cases s0; cases sf; exact hcc
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ec, he, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- Unconditional `HookOk` for `fmtWriteProtoAddrGhost` under any caller `Env` containing `[]`
    (with `withFsTraceExact`). -/
theorem fmtWriteProtoAddrGhost_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {mmpl : MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    {mplCore : MultiPlacement} {mplAllocOf : CliFmtWriteVtableKind → MultiPlacement}
    {mplFmt : MultiPlacement}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_ne : ∀ lr : BitVec 64, LsRetAddrFmtWrite lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (γ : GhostName) (tp : BitVec 64)
    (L : CliFmtWriteSubLink fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim P_sub mplCore mplAllocOf mplFmt)
    {Env : List AllocEvent → Prop} (hNil : Env []) :
    HookOk
      (fmtWriteProtoAddrGhost keep P_sub mmpl brkStart lim mplCore mplAllocOf mplFmt)
      (withLsRetFmtWrite (withFsTraceExact
        (cliFmtWriteProtoAddrSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (fun _ => Env)))) := by
  have hOkBase :=
    subroutine_ok_withRoMemGuard_withLsRetFmtWrite
      (cliCoreFmtWrite_protoAddr_ro_ok (EnvOf := fun c => ExactOrNilEnv c.exactEvs) L)
  have hFallback : HookOk (keepFsTrace fmtWriteHook0)
      (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) :=
    CliFmtGhostSpecs.hookOk_withLsRetFmtWrite
      (fmtWriteHook0_cliProtoAddr_ok fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
        (fun c => exactOrNilEnv_nil c.exactEvs))
  have hFsT : SpecPreservesFsTraceExact (fmtWriteGhostSpecOf mmpl brkStart lim γ tp) :=
    fun x R s0 sf hout => specPreservesFsTraceExact_withFsTraceExact _ x R s0 sf hout
  have hGhostOk := stubGuardedF3GhostRo_ok hsvc_sub hsub_out_keep hcomm
    (fun _ h => cliFmtWriteRoGuard_stripExecOutside keep h) γ tp
    (fun _ _ _ hpre => hlr_ne _ (extract_withLsRetFmtWrite hpre).1)
    hOkBase
    (fmtWriteGhostSpecOf_stripSInvariant mmpl brkStart lim hKeepMallocng γ tp)
    hFsT
    (fmtWriteGhostSpecOf_pre_setPC mmpl brkStart lim γ tp)
    (fmtWriteGhostSpecOf_outcome_setPC mmpl brkStart lim γ tp)
    hFallback
  rintro x R s0 hrun hpre hsp
  obtain ⟨hlr, hpreInner⟩ := extract_withLsRetFmtWrite hpre
  rcases x with ⟨c, st0⟩
  dsimp only [withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpreInner
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreInner
  rcases hpreInner with ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen, hFit, hEx⟩, hm0⟩
  have hpre0 : s0.mem ⊨ (fmtWriteGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) s0 ∗ R := by
    refine intro_withLsRetFmtWrite hlr ?_
    dsimp only [withFsTraceExact, cliFmtWriteProtoAddrSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hsh, heven, hlen,
      fitsEnv_exactOrNil hFit hEx, exactOrNilEnv_exact c.exactEvs⟩, hm0⟩
  obtain ⟨hkf, hsym, hout⟩ := hGhostOk (c, st0) R s0 hrun hpre0 hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact, cliFmtWriteProtoAddrSpec]
      at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩
    have hp := hpost.2
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨evs, hp⟩
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨bs', hp⟩
    refine ⟨bs', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1,
      exactOrNilEnv_imp hNil hEx evs hp.1.2.2.2.2⟩, hp.2⟩
  · dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact,
      cliFmtWriteProtoAddrSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [fmtWriteGhostSpecOf, withLsRetFmtWrite, withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Unconditional `HookOk` for `fmtWriteProtoAddrGhost` on `fmtWriteProtoAddrLsEnvSpec` under any
    caller `Env` containing `[]`. -/
theorem fmtWriteProtoAddrGhost_lsEnv_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {mmpl : MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    {mplCore : MultiPlacement} {mplAllocOf : CliFmtWriteVtableKind → MultiPlacement}
    {mplFmt : MultiPlacement}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_ne : ∀ lr : BitVec 64, LsRetAddrFmtWrite lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (γ : GhostName) (tp : BitVec 64)
    (L : CliFmtWriteSubLink fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim P_sub mplCore mplAllocOf mplFmt)
    {Env : List AllocEvent → Prop} (hNil : Env []) :
    HookOk
      (fmtWriteProtoAddrGhost keep P_sub mmpl brkStart lim mplCore mplAllocOf mplFmt)
      (fmtWriteProtoAddrLsEnvSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim Env) := by
  have hok := fmtWriteProtoAddrGhost_ok hsvc_sub hsub_out_keep hcomm hKeepMallocng hlr_ne γ tp L hNil
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [fmtWriteProtoAddrLsEnvSpec, withLsRetFmtWrite, withFsTraceExact] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · dsimp only [withLsRetFmtWrite, withFsTraceExact, cliFmtWriteProtoAddrSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [withLsRetFmtWrite, withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [withLsRetFmtWrite, withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Canonical CLI `HookOk` (`Env := CliFmtWriteEnv`) for `fmtWriteProtoAddrGhost`. -/
theorem fmtWriteProtoAddrGhost_cliLs_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {mmpl : MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    {mplCore : MultiPlacement} {mplAllocOf : CliFmtWriteVtableKind → MultiPlacement}
    {mplFmt : MultiPlacement}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_ne : ∀ lr : BitVec 64, LsRetAddrFmtWrite lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (γ : GhostName) (tp : BitVec 64)
    (L : CliFmtWriteSubLink fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim P_sub mplCore mplAllocOf mplFmt) :
    HookOk
      (fmtWriteProtoAddrGhost keep P_sub mmpl brkStart lim mplCore mplAllocOf mplFmt)
      (fmtWriteProtoAddrCliLsSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) :=
  fmtWriteProtoAddrGhost_lsEnv_ok hsvc_sub hsub_out_keep hcomm hKeepMallocng hlr_ne γ tp L
    cliFmtWriteEnv_nil

/-- `GhostRowReplayOn` (`entryGuard := fun _ => True`) for `fmtWriteProtoAddrGhost` at
    `lsFmtWriteSym`. -/
theorem fmtWriteProtoAddrGhost_rowReplayOn_of_stub [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits}
    {mplCore : MultiPlacement} {mplAllocOf : CliFmtWriteVtableKind → MultiPlacement}
    {mplFmt : MultiPlacement}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddrFmtWrite lr → keep lr = false)
    (hlr_ne : ∀ lr : BitVec 64, LsRetAddrFmtWrite lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (L : ∀ γ tp, CliFmtWriteSubLink fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim P_sub mplCore mplAllocOf mplFmt)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsFmtWriteSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hSubExtInReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsFmtWriteSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (coreMultiLib.fnAddr mplCore coreFmtWriteSym)))
    (hInvSF : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hInvRo : ∀ u : State, ExecFrozen u.mem → InvS u →
      cliFmtWriteRoGuard mplAllocOf mplFmt u.mem)
    (hInvCode : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem → v.fs = u.fs → InvS u → InvS v) :
    GhostRowReplayOn mpl mmpl InvS EG lsFmtWriteSym (fun _ => True)
      (fmtWriteProtoAddrGhost keep P_sub mmpl brkStart lim mplCore mplAllocOf mplFmt) :=
  stubGuardedF3GhostRo_rowReplayOn_of_stub
    (fun _ => rfl) hsvc_sub hsub_out_keep hcomm
    (fun _ h => cliFmtWriteRoGuard_stripExecOutside keep h)
    (fun γ tp =>
      subroutine_ok_withRoMemGuard_withLsRetFmtWrite
        (cliCoreFmtWrite_protoAddr_ro_ok (EnvOf := fun c => ExactOrNilEnv c.exactEvs) (L γ tp)))
    (fmtWriteGhostSpecOf_stripSInvariant mmpl brkStart lim hKeepMallocng)
    (fun _ _ x R s0 sf hout => specPreservesFsTraceExact_withFsTraceExact _ x R s0 sf hout)
    (fmtWriteGhostSpecOf_pre_setPC mmpl brkStart lim)
    (fmtWriteGhostSpecOf_outcome_setPC mmpl brkStart lim)
    (fun _ _ _ _ _ hpre => hlr_out _ (extract_withLsRetFmtWrite hpre).1)
    (fun _ _ _ _ _ hpre => hlr_ne _ (extract_withLsRetFmtWrite hpre).1)
    hRealStubNone hRealSvc hRealNoExt hSubExtInReal hStubSteps hInvSF hInvRo hInvCode hInvStep

/-! ## 3. `lsFormatInnerSym` (`alloc::fmt::format::format_inner`) Ghost Hook & Replay Suite -/

theorem subroutine_ok_withRoMemGuard_withLsRetFormatInner [LibsignalPlacement] {α : Type}
    {roGuard : Memory → Prop} {P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    (hOk : subroutine_ok P_sub entryTarget (withRoMemGuard roGuard spec)) :
    subroutine_ok P_sub entryTarget (withRoMemGuard roGuard (withLsRetFormatInner spec)) := by
  apply subroutine_ok.of_codeLoaded
  intro x R₀ s0 hpc hrun hpre hsp0 _hLP
  dsimp only [withRoMemGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, hpreL⟩
  have hpre0 : s0.mem ⊨ (withRoMemGuard roGuard spec).pre x s0 ∗ R₀ := by
    dsimp only [withRoMemGuard]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hro, (extract_withLsRetFormatInner hpreL).2⟩
  exact hOk.mono_outcome x R₀ s0 hpc hrun hpre0 hsp0 (fun _ hout => hout)

/-- `(γ, tp)`-indexed `withLsRetFormatInner` specification family for `formatInnerLsCallGhost`. -/
@[expose] def formatInnerGhostSpecOf [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    Spec (CliFormatInnerLsCall × fineCostModel.σ) :=
  withLsRetFormatInner (withFsTraceExact
    (cliFormatInnerLsCallSpec fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (fun c => ExactOrNilEnv c.exactEvs)))

/-- `W`-independent ghost hook for `lsFormatInnerSym` (`alloc::fmt::format::format_inner`),
    covering all 13 CLI formatting shapes in `CliFormatInnerLsShape`. -/
@[expose] noncomputable def formatInnerLsCallGhost [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (mplAlloc mplFmt : MultiPlacement) :
    State → State :=
  stubGuardedF3GhostRo keep (cliFormatInnerRoGuard mplAlloc mplFmt)
    P_sub (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
    (formatInnerGhostSpecOf mmpl brkStart lim)
    formatInnerHook0

theorem formatInnerLsCallGhost_rowSpec [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (mplAlloc mplFmt : MultiPlacement) :
    FormatInnerRowSpec
      (formatInnerLsCallGhost keep P_sub mmpl brkStart lim mplAlloc mplFmt) :=
  trivial

theorem formatInnerLsCallGhost_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (mplAlloc mplFmt : MultiPlacement) (s0 : State) :
    (formatInnerLsCallGhost keep P_sub mmpl brkStart lim mplAlloc mplFmt s0).fs = s0.fs :=
  stubGuardedF3GhostRo_fs _ _ _ _ _ _ s0

theorem formatInnerLsCallGhost_trace [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (mplAlloc mplFmt : MultiPlacement) (s0 : State) :
    (formatInnerLsCallGhost keep P_sub mmpl brkStart lim mplAlloc mplFmt s0).trace = s0.trace :=
  stubGuardedF3GhostRo_trace _ _ _ _ _ _ s0

theorem formatInnerLsCallGhost_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (mplAlloc mplFmt : MultiPlacement) (s0 : State) :
    FsTraced IsFsC s0
      (formatInnerLsCallGhost keep P_sub mmpl brkStart lim mplAlloc mplFmt s0) :=
  stubGuardedF3GhostRo_fsT _ _ _ _ _ _ s0

theorem formatInnerGhostSpecOf_stripSInvariant [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64) :
    SpecStripSInvariant keep (formatInnerGhostSpecOf mmpl brkStart lim γ tp) where
  pre_eq := by
    rintro ⟨c, st0⟩ s
    dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact,
      cliFormatInnerLsCallSpec]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st0 s]
    rfl
  post_eq := by
    rintro ⟨c, st0⟩ s0 sf
    dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact,
      cliFormatInnerLsCallSpec]
    have hp := fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim
    have hacp : ∀ a b : State,
        LibsignalBinary.Heap.AllocCallPreserved (stripS keep a) b =
          LibsignalBinary.Heap.AllocCallPreserved a b := by
      intro a b; cases a; rfl
    simp only [hp, hacp]
    rfl
  onPanic_eq := by
    rintro ⟨c, st0⟩ s0 sf; rfl
  onExit_eq := by
    rintro ⟨c, st0⟩ _ s0 sf; rfl
  onOom_eq := by
    rintro ⟨c, st0⟩ s0 sf; rfl

theorem formatInnerGhostSpecOf_pre_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64)
    (x : CliFormatInnerLsCall × fineCostModel.σ) (s : State) (pc : BitVec 64) :
    (formatInnerGhostSpecOf mmpl brkStart lim γ tp).pre x (s.setPC pc) =
      (formatInnerGhostSpecOf mmpl brkStart lim γ tp).pre x s := by
  rcases x with ⟨c, st0⟩
  dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact,
    cliFormatInnerLsCallSpec]
  have hp :
      (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim st0 (s.setPC pc) =
        (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim st0 s :=
    LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj.pool_of_setPC
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim st0 s pc
  rw [hp]
  rfl

theorem formatInnerGhostSpecOf_outcome_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64)
    (x : CliFormatInnerLsCall × fineCostModel.σ) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (formatInnerGhostSpecOf mmpl brkStart lim γ tp) x R (s0.setPC pc) sf) :
    SubroutineOutcome (formatInnerGhostSpecOf mmpl brkStart lim γ tp) x R s0 sf := by
  rcases x with ⟨c, st0⟩
  rcases h with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨ec, he, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, ?_, hpost⟩
    cases s0; cases sf; exact hcc
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ec, he, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- Unconditional `HookOk` for `formatInnerLsCallGhost` across all 13 shapes and any caller
    `Env` containing `[]` (with `withFsTraceExact`). -/
theorem formatInnerLsCallGhost_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {mmpl : MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_ne : ∀ lr : BitVec 64, LsRetAddrFormatInner lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (γ : GhostName) (tp : BitVec 64)
    (L : CliFormatInnerSubLink fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim P_sub mplCore mplAlloc mplFmt)
    {Env : List AllocEvent → Prop} (hNil : Env []) :
    HookOk
      (formatInnerLsCallGhost keep P_sub mmpl brkStart lim mplAlloc mplFmt)
      (withLsRetFormatInner (withFsTraceExact
        (cliFormatInnerLsCallSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (fun _ => Env)))) := by
  have hOkBase :=
    subroutine_ok_withRoMemGuard_withLsRetFormatInner
      (cliAllocFormatInner_lsCall_ro_ok (EnvOf := fun c => ExactOrNilEnv c.exactEvs) L)
  have hFallback : HookOk (keepFsTrace formatInnerHook0)
      (formatInnerGhostSpecOf mmpl brkStart lim γ tp) :=
    CliFmtGhostSpecs.hookOk_withLsRetFormatInner
      (formatInnerHook0_cliLsCallSpec_ok fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
        (fun c => exactOrNilEnv_nil c.exactEvs))
  have hFsT : SpecPreservesFsTraceExact (formatInnerGhostSpecOf mmpl brkStart lim γ tp) :=
    fun x R s0 sf hout => specPreservesFsTraceExact_withFsTraceExact _ x R s0 sf hout
  have hGhostOk := stubGuardedF3GhostRo_ok hsvc_sub hsub_out_keep hcomm
    (fun _ h => cliFormatInnerRoGuard_stripExecOutside keep h) γ tp
    (fun _ _ _ hpre => hlr_ne _ (extract_withLsRetFormatInner hpre).1)
    hOkBase
    (formatInnerGhostSpecOf_stripSInvariant mmpl brkStart lim hKeepMallocng γ tp)
    hFsT
    (formatInnerGhostSpecOf_pre_setPC mmpl brkStart lim γ tp)
    (formatInnerGhostSpecOf_outcome_setPC mmpl brkStart lim γ tp)
    hFallback
  rintro x R s0 hrun hpre hsp
  obtain ⟨hlr, hpreInner⟩ := extract_withLsRetFormatInner hpre
  rcases x with ⟨c, st0⟩
  dsimp only [withFsTraceExact, cliFormatInnerLsCallSpec] at hpreInner
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreInner
  rcases hpreInner with ⟨⟨hx8, hx0, hx1, hshOk, hFit, hEx⟩, hm0⟩
  have hpre0 : s0.mem ⊨ (formatInnerGhostSpecOf mmpl brkStart lim γ tp).pre (c, st0) s0 ∗ R := by
    refine intro_withLsRetFormatInner hlr ?_
    dsimp only [withFsTraceExact, cliFormatInnerLsCallSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hshOk,
      fitsEnv_exactOrNil hFit hEx, exactOrNilEnv_exact c.exactEvs⟩, hm0⟩
  obtain ⟨hkf, hsym, hout⟩ := hGhostOk (c, st0) R s0 hrun hpre0 hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact,
      cliFormatInnerLsCallSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩
    have hp := hpost.2
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨evs, hp⟩
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨bs', hp⟩
    refine ⟨bs', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1,
      exactOrNilEnv_imp hNil hEx evs hp.1.2.2.2⟩, hp.2⟩
  · dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact,
      cliFormatInnerLsCallSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [formatInnerGhostSpecOf, withLsRetFormatInner, withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Unconditional `HookOk` for `formatInnerLsCallGhost` on `formatInnerCallLsEnvSpec` under any
    caller `Env` containing `[]`. -/
theorem formatInnerLsCallGhost_lsEnv_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {mmpl : MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_ne : ∀ lr : BitVec 64, LsRetAddrFormatInner lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (γ : GhostName) (tp : BitVec 64)
    (L : CliFormatInnerSubLink fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim P_sub mplCore mplAlloc mplFmt)
    {Env : List AllocEvent → Prop} (hNil : Env []) :
    HookOk
      (formatInnerLsCallGhost keep P_sub mmpl brkStart lim mplAlloc mplFmt)
      (formatInnerCallLsEnvSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim Env) := by
  have hok := formatInnerLsCallGhost_ok hsvc_sub hsub_out_keep hcomm hKeepMallocng hlr_ne γ tp L hNil
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [formatInnerCallLsEnvSpec, withLsRetFormatInner, withFsTraceExact] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · dsimp only [withLsRetFormatInner, withFsTraceExact, cliFormatInnerLsCallSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    have hf := hpan.2; rw [satisfies_pure_sepConj] at hf; exact False.elim hf.1
  · dsimp only [withLsRetFormatInner, withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [withLsRetFormatInner, withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Canonical CLI `HookOk` (`Env := CliFormatInnerEnv`) for `formatInnerLsCallGhost`. -/
theorem formatInnerLsCallGhost_cliLs_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {mmpl : MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_ne : ∀ lr : BitVec 64, LsRetAddrFormatInner lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (γ : GhostName) (tp : BitVec 64)
    (L : CliFormatInnerSubLink fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim P_sub mplCore mplAlloc mplFmt) :
    HookOk
      (formatInnerLsCallGhost keep P_sub mmpl brkStart lim mplAlloc mplFmt)
      (formatInnerCallCliLsSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) :=
  formatInnerLsCallGhost_lsEnv_ok hsvc_sub hsub_out_keep hcomm hKeepMallocng hlr_ne γ tp L
    cliFormatInnerEnv_nil

/-- `GhostRowReplayOn` (`entryGuard := fun _ => True`) for `formatInnerLsCallGhost` at
    `lsFormatInnerSym`. -/
theorem formatInnerLsCallGhost_rowReplayOn_of_stub [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddrFormatInner lr → keep lr = false)
    (hlr_ne : ∀ lr : BitVec 64, LsRetAddrFormatInner lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (L : ∀ γ tp, CliFormatInnerSubLink fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim P_sub mplCore mplAlloc mplFmt)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsFormatInnerSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hSubExtInReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsFormatInnerSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)))
    (hInvSF : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hInvRo : ∀ u : State, ExecFrozen u.mem → InvS u →
      cliFormatInnerRoGuard mplAlloc mplFmt u.mem)
    (hInvCode : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem → v.fs = u.fs → InvS u → InvS v) :
    GhostRowReplayOn mpl mmpl InvS EG lsFormatInnerSym (fun _ => True)
      (formatInnerLsCallGhost keep P_sub mmpl brkStart lim mplAlloc mplFmt) :=
  stubGuardedF3GhostRo_rowReplayOn_of_stub
    (fun s => perm_writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)
    hsvc_sub hsub_out_keep hcomm
    (fun _ h => cliFormatInnerRoGuard_stripExecOutside keep h)
    (fun γ tp =>
      subroutine_ok_withRoMemGuard_withLsRetFormatInner
        (cliAllocFormatInner_lsCall_ro_ok (EnvOf := fun c => ExactOrNilEnv c.exactEvs) (L γ tp)))
    (formatInnerGhostSpecOf_stripSInvariant mmpl brkStart lim hKeepMallocng)
    (fun _ _ x R s0 sf hout => specPreservesFsTraceExact_withFsTraceExact _ x R s0 sf hout)
    (formatInnerGhostSpecOf_pre_setPC mmpl brkStart lim)
    (formatInnerGhostSpecOf_outcome_setPC mmpl brkStart lim)
    (fun _ _ _ _ _ hpre => hlr_out _ (extract_withLsRetFormatInner hpre).1)
    (fun _ _ _ _ _ hpre => hlr_ne _ (extract_withLsRetFormatInner hpre).1)
    hRealStubNone hRealSvc hRealNoExt hSubExtInReal hStubSteps hInvSF hInvRo hInvCode hInvStep

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostReplays

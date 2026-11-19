/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.SignalSessionIoPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
public import LibsignalBinary.Proofs.SignalSession.CliIo.Sym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
public import VerifiedLibraries.Musl.Proofs.SyscallProof
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutProof
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoMusl9
import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecsHook
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget

/-!
# Ghost Hooks and Trajectory Replays for `write_stdout` and `write_file`

Zero-hook leaf proofs for `libsignal_cli_io::write_stdout` (`lsWriteStdoutSym`) and
`libsignal_cli_io::write_file` (`lsWriteFileSym`):

- `writeIoLinkedGhost` (§1): total `W`- and `(γ, tp)`-independent first-stop combinator executing
  `StepsUntil P_sub` on `P_sub` (`P_sub.svc = Syscall.standard`, `P_sub.externAt? = none`) when
  `ExecFrozen s0.mem`, `keep (s0.readReg64 .lr) = false`, and both `P_sub` and
  `signalSessionIoMultiLib` are loaded in `stripExecOutside keep s0.mem`. Outside that guard it
  falls back directly to the raw idealized hook (`writeStdoutHook` / `writeFileHook`, without
  `keepFsTrace`, so `.trace` and `.fs.files` effects stay exact on unconstrained `HookOk` states).
- `writeStdoutGhost` (`lsWriteStdoutSym`, §2): preserves `.fs`, `HookFsTraced IsFsC`,
  `VmPreserved`, and `ExecFrozen`; satisfies unconditional `HookOk` against
  `withLsRet (writeStdoutSpecPlacedSat ...)` and trajectory-aware `GhostRowReplayOn`.
- `writeFileGhost` (`lsWriteFileSym`, §3): preserves `.fs.fds`, `HookFsTraced IsFsC`,
  `VmPreserved`, `WriteFileRowSpec`, and `ExecFrozen`; satisfies unconditional `HookOk` against
  `withLsRet (writeFileSpecPlacedSat ...)` and trajectory-aware `WriteFileRowReplayOn`.

This module avoids `CliElf` imports; concrete ELF placement facts enter only at witness
instantiation sites.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoWriteGhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic
open CryptoVerification (LibsignalPlacement signalSessionIoMultiLib)
open CryptoVerification.RustHeap (allocFailedEvent)
open CryptoVerification.SignalSession
  (CliHooks blockingAncestor? cliExternsPlaced libsignalSessionLib
   lsWriteFileSym lsWriteStdoutSym readPath writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli.MainHops (IoModel WriteFileGhost WriteStdoutGhost cliIo)
open CryptoVerification.SignalSession.Cli.RunGlue
  (IsFsC writeFileHook_fsT writeStdoutHook_fsT)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.Fine
  (VmPreserved.of_eq fineCostModel fineHookRustCliAllocBudget hookOk_withVmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (WriteFileEnv vmPreserved_writeFileHook vmPreserved_writeStdoutHook withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileProof
  (cliIoWriteFile_budget_withCodeLoaded_ok writeFileHonestCoreClamped writeFileSpecPlacedSatClamped)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutProof
  (cliIoWriteStdout_honest_withCodeLoaded_ok)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen SpecStripSInvariant satisfies_of_stripExecOutside
   satisfies_stripExecOutside standard_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (fineHookRustCliAllocBudget_pool_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst
  (fineHookPoolErrnoSplit)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
  (writeFileHook_ok_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (ActiveF3CallPre)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs (withCallGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoMusl9
  (muslClose48Local_of_where9_ok muslErrnoLocation_of_where9_ok
   muslOpenCreateTrunc_of_where9_ok muslWriteFile32Clamped_of_where9_ok
   muslWriteStdout32_of_where9_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (ExtraRowFullOk ExtraRowReplayOn GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (extract_withLsRet hookOk_withLsRet withLsRet withLsRet_outcome_setPC withLsRet_pre_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileHonestCore writeFileSpecPlacedSat writeFileStackFloor
   writeStdoutHonestCore writeStdoutSpecPlacedSat)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecsHook
  (writeFileHook_ok_honestCore writeStdoutHook_ok_honestCore)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowSpec GhostRowSpecOk WriteFileRowOk WriteFileRowSpec WriteStdoutRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (writeFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym
  (CliIoBlockNoExtern cliIoCloseSym cliIoErrnoLocationSym cliIoOpenSym
   cliIoWriteFileSym cliIoWriteStdoutSym cliIoWriteSym)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det h2fsgen_steps_lift_of_visitedIn_noExtern)
open VerifiedLibraries.Musl (muslSysPlacedLib)

/-! ## 1. Hook-Free First-Stop Ghost Combinator (`writeIoLinkedGhost`) -/

private theorem stripS_mem_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).mem = stripExecOutside keep s.mem := by cases s; rfl
private theorem stripS_pc_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).pc = s.pc := by cases s; rfl
private theorem stripS_sp_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).sp = s.sp := by cases s; rfl
private theorem stripS_status_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).status = s.status := by cases s; rfl
private theorem stripS_r64_eq (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (stripS keep s).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem stripS_fs_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).fs = s.fs := by cases s; rfl
private theorem stripS_trace_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).trace = s.trace := by cases s; rfl
private theorem strip_read32_eq (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).read32 a = m.read32 a := by
  simp [Memory.read32, strip_read8]

private theorem fsTraced_stripS_eq (keep : BitVec 64 → Bool)
    (isFs : TraceEvent → Prop) (s0 sf : State) :
    FsTraced isFs (stripS keep s0) (stripS keep sf) = FsTraced isFs s0 sf := by
  cases s0; cases sf; rfl

private theorem subroutineStop_stripS_iff {keep : BitVec 64 → Bool} {s0 s : State} :
    SubroutineStop s0 (stripS keep s) ↔ SubroutineStop s0 s := by
  simp [SubroutineStop, Returned, stripS_pc_eq, stripS_sp_eq, stripS_status_eq]

private theorem step_status_running {P : Program} {s1 s2 : State}
    (h : Step P s1 s2) : s1.status = .Running := by
  cases h <;> assumption

private theorem steps_preserves_halted {P : Program} {u v : State}
    (hs : Steps P u v) (hu : u.status = .Halted) : v.status = .Halted := by
  induction hs with
  | refl => exact hu
  | step hs1 _ ihs => cases hs1 <;> simp_all

private theorem subroutineOutcome_to_stop {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : SubroutineStop s0 sf := by
  rcases h with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, he, _⟩ | ⟨ho, _⟩
  · exact Or.inl hret
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he⟩))
  · exact Or.inr (Or.inr (Or.inr ho))

private theorem subroutineOutcome_not_halted {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
  · rw [hr]; decide
  · rw [hp]; decide
  · rw [he]; nofun
  · rw [ho]; decide

theorem subroutine_ok_withCodeLoaded_withLsRet [LibsignalPlacement] {α : Type}
    {L : MultiPlacedLib} {mpl : MultiPlacement} {P : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P addr (L.withCodeLoaded mpl spec)) :
    subroutine_ok P addr (L.withCodeLoaded mpl (withLsRet spec)) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _hLP
  dsimp only [MultiPlacedLib.withCodeLoaded, withLsRet] at hpre
  rw [sepConj_comm _ ⌜L.CodeLoaded mpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre0 : s0.mem ⊨ (L.withCodeLoaded mpl spec).pre x s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜L.CodeLoaded mpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl, hpre.2⟩
  exact h.mono_outcome x R s0 hpc hrun hpre0 hsp (fun _ hout => hout)

/-- Recover `mf.perm = m0.perm` from `(stripExecOutside keep mf).perm = (stripExecOutside keep m0).perm`
    under `ExecFrozen m0`, `ExecFrozen mf`, and `m0.KeepsFrozen mf`. -/
theorem perm_eq_of_stripExecOutside_keepsFrozen
    {keep : BitVec 64 → Bool} {m0 mf : Memory}
    (hFr0 : ExecFrozen m0) (hFrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64,
      (stripExecOutside keep mf).perm a = (stripExecOutside keep m0).perm a) :
    mf.perm = m0.perm := by
  funext a
  have hs := hstrip a
  rw [strip_perm, strip_perm] at hs
  have h0 := hFr0 a
  have hf := hFrf a
  cases hp0 : m0.perm a with
  | none =>
    cases hpf : mf.perm a with
    | none => rfl
    | some pf => simp [hp0, hpf] at hs
  | some p0 =>
    cases hpf : mf.perm a with
    | none => simp [hp0, hpf] at hs
    | some pf =>
      by_cases hfr_a : m0.Frozen a
      · have hpeq := (hkf a hfr_a).2.1
        rwa [hp0, hpf] at hpeq
      · unfold Memory.Frozen Option.frozen Perm.frozen at hfr_a
        rw [hp0] at hs h0 hfr_a
        rw [hpf] at hs hf
        rcases p0 with ⟨r0, w0, x0, lf0, an0⟩
        rcases pf with ⟨rf, wf, xf, lff, anf⟩
        unfold stripPerm at hs
        cases hk : keep a <;> cases r0 <;> cases w0 <;> cases x0 <;>
          cases rf <;> cases wf <;> cases xf <;>
          simp_all [Option.map, Option.x, Option.r, Option.w]

/-- Recover `VmPreserved s0 sf` from `VmPreserved (stripS keep (s0.setPC entryTarget)) (stripS keep sf)`
    under `ExecFrozen s0.mem`, `ExecFrozen sf.mem`, `s0.mem.KeepsFrozen sf.mem`, and
    `sf.fs.fds = s0.fs.fds`. -/
theorem vmPreserved_of_stripS_keepsFrozen
    {keep : BitVec 64 → Bool} {entryTarget : BitVec 64} {s0 sf : State}
    (hFr0 : ExecFrozen s0.mem) (hFrf : ExecFrozen sf.mem)
    (hkf : s0.mem.KeepsFrozen sf.mem) (hfds : sf.fs.fds = s0.fs.fds)
    (hvm' : VmPreserved (stripS keep (s0.setPC entryTarget)) (stripS keep sf)) :
    VmPreserved s0 sf := by
  rcases hvm' with ⟨⟨hbrkS, hbrk, htp⟩, hphys, hperm', _⟩
  have hperm : sf.mem.perm = s0.mem.perm := by
    refine perm_eq_of_stripExecOutside_keepsFrozen (keep := keep) hFr0 hFrf hkf fun a => ?_
    have hp := hperm' a
    cases s0; cases sf
    exact hp
  refine VmPreserved.of_eq ?_ ?_ ?_ ?_ hperm (fun fd _ _ => congrFun hfds (BitVec.ofNat 64 fd))
  · cases s0; cases sf; exact hbrkS
  · cases s0; cases sf; exact hbrk
  · cases s0; cases sf; exact htp
  · cases s0; cases sf; exact hphys

/-- Lift `Steps P_sub s1' sf'` from `s1' = stripS keep s1` on hook-free `Syscall.standard` `P_sub`
    to simultaneous `StepsUntil P_sub (SubroutineStop s0) s1 sf` and
    `h2fsgen_StepsVisitedIn keep P_sub s1 sf` (so `Steps` transfers to any `P_real` with
    `P_real.svc = Syscall.standard` and `∀ pc, keep pc = true → P_real.externAt? pc = none`). -/
theorem stepsUntil_visitedIn_of_stripS_standard
    {keep : BitVec 64 → Bool} {P_sub : Program} {s0 : State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    {s1' sf' : State}
    (hsteps : Steps P_sub s1' sf')
    (hstop' : SubroutineStop s0 sf')
    (hnhalt' : sf'.status ≠ .Halted) :
    ∀ s1 : State,
      s1' = stripS keep s1 →
      ExecFrozen s1.mem →
      ∃ sf : State,
        StepsUntil P_sub (SubroutineStop s0) s1 sf ∧
        h2fsgen_StepsVisitedIn keep P_sub s1 sf ∧
        SubroutineStop s0 sf ∧
        sf' = stripS keep sf ∧
        ExecFrozen sf.mem := by
  induction hsteps with
  | refl _ =>
    intro s1 hs1 hfr1
    have hstop1 : SubroutineStop s0 s1 := subroutineStop_stripS_iff.mp (hs1 ▸ hstop')
    exact ⟨s1, StepsUntil.refl s1, .refl s1, hstop1, hs1, hfr1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro sa hsa hfra
    by_cases hstop_sa : SubroutineStop s0 sa
    · rcases hstop_sa with ⟨hpc_lr, _⟩ | hpan | ⟨_, hex⟩ | hoom
      · cases h1 with
        | @exec inst _ hfm' =>
          rw [hsa, stripS_pc_eq, stripS_mem_eq] at hfm'
          unfold Program.fetchMem at hfm'
          rw [hsub_no sa.pc] at hfm'
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
          by_cases hal : sa.pc.toNat % 4 = 0
          · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
            by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
            · have hx0 : ((stripExecOutside keep sa.mem).perm sa.pc).x = true := by
                have h4 :
                    ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                    ((stripExecOutside keep sa.mem).allPerm (·.x) (sa.pc + 1#64) 3) = true := by
                  simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true] using hce'
                exact h4.1
              have hkp := (strip_perm_x_imp hx0).2
              rw [hpc_lr, hlr_out] at hkp
              cases hkp
            · simp [hce'] at hfm'
          · simp [hal] at hfm'
        | halt_unmapped _ _ _ =>
          exact False.elim (hnhalt' (steps_preserves_halted hrest rfl))
        | extern _ he _ _ =>
          rw [hsa, stripS_pc_eq, hsub_no sa.pc] at he; cases he
        | extern_fault _ he _ =>
          rw [hsa, stripS_pc_eq, hsub_no sa.pc] at he; cases he
      · have hr_sa : sa.status = .Running := by
          have h := step_status_running h1; rwa [hsa, stripS_status_eq] at h
        rw [hpan] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := step_status_running h1; rwa [hsa, stripS_status_eq] at h
        rw [hex] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := step_status_running h1; rwa [hsa, stripS_status_eq] at h
        rw [hoom] at hr_sa; cases hr_sa
    · cases h1 with
      | halt_unmapped _ _ _ =>
        exact False.elim (hnhalt' (steps_preserves_halted hrest rfl))
      | extern _ he _ _ =>
        rw [hsa, stripS_pc_eq, hsub_no sa.pc] at he; cases he
      | extern_fault _ he _ =>
        rw [hsa, stripS_pc_eq, hsub_no sa.pc] at he; cases he
      | @exec inst hr' hfm' =>
        have hra : sa.status = .Running := by
          rw [hsa, stripS_status_eq] at hr'; exact hr'
        rw [hsa, stripS_pc_eq, stripS_mem_eq] at hfm'
        unfold Program.fetchMem at hfm'
        have he_sub := hsub_no sa.pc
        simp only [he_sub, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
        by_cases hal_pc : sa.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
          by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
          · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm'
            have hx4 :
                ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                ((stripExecOutside keep sa.mem).perm (sa.pc + 1#64)).x = true ∧
                ((stripExecOutside keep sa.mem).perm (sa.pc + 2#64)).x = true ∧
                ((stripExecOutside keep sa.mem).perm (sa.pc + 3#64)).x = true := by
              simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
            obtain ⟨hx0, hkp0⟩ := strip_perm_x_imp hx4.1
            obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
            obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
            obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
            have hce : sa.mem.canExec sa.pc 4 = true := by
              simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
            rw [strip_read32_eq] at hfm'
            have hfm_sub : P_sub.fetchMem sa.mem sa.pc = some inst := by
              unfold Program.fetchMem
              simp [he_sub, hal_pc, hce, hfm']
            by_cases hsvc0 : inst.isSvc0 = true
            · have hinst : inst = .system false 0#16 := by
                cases inst <;> simp [Instr.isSvc0] at hsvc0
                rcases hsvc0 with ⟨rfl, rfl⟩; rfl
              subst hinst
              obtain ⟨hcomm, hfr_sb⟩ := standard_stripS (keep := keep) hfra
              have hev_strip :
                  P_sub.evalInst (.system false 0#16) (stripS keep sa) =
                    stripS keep (Syscall.standard sa) := by
                simp [Program.evalInst, execInstWithSvc, hsvc_sub, hcomm]
              have hev_sub :
                  P_sub.evalInst (.system false 0#16) sa = Syscall.standard sa := by
                simp [Program.evalInst, execInstWithSvc, hsvc_sub]
              have hstep_sub : Step P_sub sa (Syscall.standard sa) :=
                hev_sub ▸ Step.exec hra hfm_sub
              rw [hsa, hev_strip] at hrest ih
              obtain ⟨sf, huntil_rest, hvis_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
                ih hstop' hnhalt' (Syscall.standard sa) rfl hfr_sb
              exact ⟨sf, StepsUntil.step hstop_sa hstep_sub huntil_rest,
                .step hkp0 hstep_sub hvis_rest, hstop_sf, hsf_eq, hfr_sf⟩
            · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
              have hev_strip :
                  P_sub.evalInst inst (stripS keep sa) =
                    stripS keep (execInst inst sa) := by
                rw [evalInst_eq_execInst_of_not_isSvc0 hnsvc0, execInst_stripS hnsvc0]
              have hev_sub : P_sub.evalInst inst sa = execInst inst sa :=
                evalInst_eq_execInst_of_not_isSvc0 hnsvc0 sa
              have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 sa
              have hfr_sb : ExecFrozen (execInst inst sa).mem :=
                ExecFrozen.of_perm_eq hfra (congrFun hpf.2.1)
              have hstep_sub : Step P_sub sa (execInst inst sa) :=
                hev_sub ▸ Step.exec hra hfm_sub
              rw [hsa, hev_strip] at hrest ih
              obtain ⟨sf, huntil_rest, hvis_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
                ih hstop' hnhalt' (execInst inst sa) rfl hfr_sb
              exact ⟨sf, StepsUntil.step hstop_sa hstep_sub huntil_rest,
                .step hkp0 hstep_sub hvis_rest, hstop_sf, hsf_eq, hfr_sf⟩
          · simp [hce'] at hfm'
        · simp [hal_pc] at hfm'

/-- `(γ, tp)`-independent active real-execution witness on `P_sub` + `signalSessionIoMultiLib`. -/
@[expose] def ActiveWriteIoRun
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo : MultiPlacement)
    (entryTarget : BitVec 64) (FsPres : State → State → Prop) (s0 : State) : Prop :=
  ExecFrozen s0.mem ∧
  keep (s0.readReg64 .lr) = false ∧
  P_sub.CodeLoaded (stripExecOutside keep s0.mem) ∧
  signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep s0.mem) ∧
  ∃ sf : State,
    StepsUntil P_sub (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
    SubroutineStop s0 sf ∧
    FsPres s0 sf ∧
    FsTraced IsFsC s0 sf ∧
    VmPreserved s0 sf ∧
    ExecFrozen sf.mem

/-- Total `W`-independent `(γ, tp)`-independent ghost-hook combinator for `write_stdout` / `write_file`:
    runs `StepsUntil P_sub` when `ActiveWriteIoRun` holds, falls back to raw `fallback` (preserving
    exact `.trace` and `.fs.files` effects on unconstrained `HookOk` states), and raises `.Exception`
    outside `ActiveF3CallPre`. -/
@[expose] noncomputable def writeIoLinkedGhost {α : Type}
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo : MultiPlacement)
    (entryTarget : BitVec 64) (specCore : GhostName → BitVec 64 → Spec α)
    (FsPres : State → State → Prop) (fallback : State → State)
    (s0 : State) : State := by
  classical
  exact
    if _ : ActiveF3CallPre specCore s0 then
      if hReal : ActiveWriteIoRun keep P_sub mplIo entryTarget FsPres s0 then
        Classical.choose hReal.2.2.2.2
      else
        fallback s0
    else
      { s0 with status := .Exception "write_io ghost-hook precondition violated" }

theorem writeIoLinkedGhost_activePre_of_noException {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program} {mplIo : MultiPlacement}
    {entryTarget : BitVec 64} {specCore : GhostName → BitVec 64 → Spec α}
    {FsPres : State → State → Prop} {fallback : State → State} {u : State}
    (hnoex : ∀ msg,
      (writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback u).status ≠
        .Exception msg) :
    ActiveF3CallPre specCore u := by
  classical
  by_contra hNot
  apply hnoex "write_io ghost-hook precondition violated"
  unfold writeIoLinkedGhost
  simp only [hNot, ↓reduceDIte]

theorem writeIoLinkedGhost_fsPres {α : Type}
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo : MultiPlacement)
    (entryTarget : BitVec 64) (specCore : GhostName → BitVec 64 → Spec α)
    {FsPres : State → State → Prop} {fallback : State → State}
    (hFsRefl : ∀ s s' : State, s'.fs = s.fs → FsPres s s')
    (hFallbackFs : ∀ s : State, FsPres s (fallback s))
    (s0 : State) :
    FsPres s0 (writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback s0) := by
  classical
  unfold writeIoLinkedGhost
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.1
    · exact hFallbackFs s0
  · exact hFsRefl s0 _ rfl

theorem writeIoLinkedGhost_fsT {α : Type}
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo : MultiPlacement)
    (entryTarget : BitVec 64) (specCore : GhostName → BitVec 64 → Spec α)
    (FsPres : State → State → Prop) {fallback : State → State}
    (hFallbackFsT : HookFsTraced IsFsC fallback)
    (s0 : State) :
    FsTraced IsFsC s0
      (writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback s0) := by
  classical
  unfold writeIoLinkedGhost
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.1
    · exact hFallbackFsT s0
  · exact FsTraced.of_eq rfl rfl

theorem writeIoLinkedGhost_vmPreserved {α : Type}
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo : MultiPlacement)
    (entryTarget : BitVec 64) (specCore : GhostName → BitVec 64 → Spec α)
    (FsPres : State → State → Prop) {fallback : State → State}
    (hFallbackVm : ∀ s : State, VmPreserved s (fallback s))
    (s0 : State) :
    VmPreserved s0
      (writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback s0) := by
  classical
  unfold writeIoLinkedGhost
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.2.1
    · exact hFallbackVm s0
  · exact VmPreserved.of_eq rfl rfl rfl rfl rfl

theorem writeIoLinkedGhost_preserves_execFrozen {α : Type}
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo : MultiPlacement)
    (entryTarget : BitVec 64) (specCore : GhostName → BitVec 64 → Spec α)
    (FsPres : State → State → Prop) {fallback : State → State}
    (hFallbackPerm : ∀ s : State, (fallback s).mem.perm = s.mem.perm)
    {u : State} (_hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) :
    ExecFrozen
      (writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback u).mem := by
  classical
  have hAct := writeIoLinkedGhost_activePre_of_noException hnoex
  unfold writeIoLinkedGhost
  simp only [hAct, ↓reduceDIte]
  split
  · rename_i hReal
    exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.2.2
  · exact ExecFrozen.of_perm_eq hFr (fun a => congrFun (hFallbackPerm u) a)

/-- Core eliminator across `stripS keep` for `write_stdout` / `write_file`. -/
theorem writeIo_elim_stripS {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program} {mplIo : MultiPlacement}
    {entryTarget : BitVec 64} {specCore : GhostName → BitVec 64 → Spec α}
    {FsPres : State → State → Prop}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    {γ : GhostName} {tp : BitVec 64}
    (hOk : subroutine_ok P_sub entryTarget
      (signalSessionIoMultiLib.withCodeLoaded mplIo (withVmPreserved (specCore γ tp))))
    (hInv : SpecStripSInvariant keep (specCore γ tp))
    (hPrePC : ∀ x (s : State) (pc : BitVec 64),
      (specCore γ tp).pre x (s.setPC pc) = (specCore γ tp).pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specCore γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specCore γ tp) x R s0 sf)
    (hOutEffects : ∀ x (R : SepProp) (s0 sf : State),
      SubroutineOutcome (specCore γ tp) x R s0 sf →
      Returned s0 sf ∧ FsPres s0 sf ∧ sf.fs.fds = s0.fs.fds ∧ FsTraced IsFsC s0 sf)
    {x : α} {R : SepProp} {s0 : State}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ (specCore γ tp).pre x s0 ∗ R)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem))
    (hCodeIo : signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P_sub (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
      h2fsgen_StepsVisitedIn keep P_sub (s0.setPC entryTarget) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome (specCore γ tp) x R s0 sf ∧
      FsPres s0 sf ∧
      FsTraced IsFsC s0 sf ∧
      VmPreserved s0 sf ∧
      ExecFrozen sf.mem := by
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ (specCore γ tp).pre x s1 ∗ R := by
    change s0.mem ⊨ (specCore γ tp).pre x (s0.setPC entryTarget) ∗ R
    rwa [hPrePC x s0 entryTarget]
  have hs1'_core : s1'.mem ⊨ (specCore γ tp).pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← hInv.pre_eq x s1] at hsat
  have hs1'_wcl :
      s1'.mem ⊨
        (signalSessionIoMultiLib.withCodeLoaded mplIo
          (withVmPreserved (specCore γ tp))).pre x s1' ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded, withVmPreserved]
    rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mplIo s1'.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨by rwa [stripS_mem_eq], hs1'_core⟩
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_wcl hSp hCodeSub
  have hstop0' : SubroutineStop s0 sf' := by
    have h := subroutineOutcome_to_stop hout'
    cases s0; exact h
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout'
  obtain ⟨sf, huntil, hvis, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_visitedIn_of_stripS_standard hsvc_sub hsub_no hlr_out
      hsteps' hstop0' hnhalt' s1 rfl hFr
  have hout_core_vm :
      SubroutineOutcome (specCore γ tp) x R s0 sf ∧
      (Returned s1' sf' → VmPreserved s1' sf') := by
    rw [hsf_eq] at hout'
    rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨hp', hpan'⟩ | ⟨c, he', hex'⟩ | ⟨ho', hoom'⟩
    · dsimp only [MultiPlacedLib.withCodeLoaded, withVmPreserved] at hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
      rcases hpost' with ⟨hvm', hpost_core'⟩
      rw [hInv.post_eq x s1 sf] at hpost_core'
      have hpost_core := satisfies_of_stripExecOutside hfr_sf hpost_core'
      have hout1 : SubroutineOutcome (specCore γ tp) x R s1 sf :=
        Or.inl ⟨⟨hret'.1, hret'.2.1, hret'.2.2⟩, by cases s0; cases sf; exact hcc', hpost_core⟩
      exact ⟨hOutPC x R s0 sf entryTarget hout1, fun _ => hsf_eq ▸ hvm'⟩
    · dsimp only [MultiPlacedLib.withCodeLoaded, withVmPreserved] at hpan'
      rw [hInv.onPanic_eq x s1 sf] at hpan'
      have hout1 : SubroutineOutcome (specCore γ tp) x R s1 sf :=
        Or.inr (Or.inl ⟨hp', satisfies_of_stripExecOutside hfr_sf hpan'⟩)
      exact ⟨hOutPC x R s0 sf entryTarget hout1,
        fun hr => False.elim (by rw [hsf_eq] at hr; cases hr.2.2.symm.trans hp')⟩
    · dsimp only [MultiPlacedLib.withCodeLoaded, withVmPreserved] at hex'
      rw [hInv.onExit_eq x c s1 sf] at hex'
      have hout1 : SubroutineOutcome (specCore γ tp) x R s1 sf :=
        Or.inr (Or.inr (Or.inl ⟨c, he', satisfies_of_stripExecOutside hfr_sf hex'⟩))
      exact ⟨hOutPC x R s0 sf entryTarget hout1,
        fun hr => False.elim (by rw [hsf_eq] at hr; cases hr.2.2.symm.trans he')⟩
    · dsimp only [MultiPlacedLib.withCodeLoaded, withVmPreserved] at hoom'
      rw [hInv.onOom_eq x s1 sf] at hoom'
      have hout1 : SubroutineOutcome (specCore γ tp) x R s1 sf :=
        Or.inr (Or.inr (Or.inr ⟨ho', satisfies_of_stripExecOutside hfr_sf hoom'⟩))
      exact ⟨hOutPC x R s0 sf entryTarget hout1,
        fun hr => False.elim (by rw [hsf_eq] at hr; cases hr.2.2.symm.trans ho')⟩
  obtain ⟨hout0, hvm_of_ret⟩ := hout_core_vm
  obtain ⟨hret0, hFsPres, hfds_eq, hFsT⟩ := hOutEffects x R s0 sf hout0
  have hret' : Returned s1' sf' := by
    rw [hsf_eq]
    exact ⟨hret0.1, hret0.2.1, hret0.2.2⟩
  have hvm' : VmPreserved (stripS keep (s0.setPC entryTarget)) (stripS keep sf) :=
    hsf_eq ▸ hvm_of_ret hret'
  have hVm : VmPreserved s0 sf :=
    vmPreserved_of_stripS_keepsFrozen hFr hfr_sf huntil.toSteps.keepsFrozen hfds_eq hvm'
  exact ⟨sf, huntil, hvis, hstop_sf, hout0, hFsPres, hFsT, hVm, hfr_sf⟩

/-- Unconditional `HookOk` for `writeIoLinkedGhost` against `specCore γ tp`. -/
theorem writeIoLinkedGhost_ok {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program} {mplIo : MultiPlacement}
    {entryTarget : BitVec 64} {specCore : GhostName → BitVec 64 → Spec α}
    {FsPres : State → State → Prop} {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : subroutine_ok P_sub entryTarget
      (signalSessionIoMultiLib.withCodeLoaded mplIo (withVmPreserved (specCore γ tp))))
    (hInv : SpecStripSInvariant keep (specCore γ tp))
    (hPrePC : ∀ x (s : State) (pc : BitVec 64),
      (specCore γ tp).pre x (s.setPC pc) = (specCore γ tp).pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specCore γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specCore γ tp) x R s0 sf)
    (hOutEffects : ∀ x (R : SepProp) (s0 sf : State),
      SubroutineOutcome (specCore γ tp) x R s0 sf →
      Returned s0 sf ∧ FsPres s0 sf ∧ sf.fs.fds = s0.fs.fds ∧ FsTraced IsFsC s0 sf)
    (hFallbackOk : HookOk fallback (specCore γ tp)) :
    HookOk (writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback)
      (specCore γ tp) := by
  classical
  intro x R s0 hrun hpre hsp
  have hAct : ActiveF3CallPre specCore s0 := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  unfold writeIoLinkedGhost
  simp only [hAct, ↓reduceDIte]
  by_cases hReal : ActiveWriteIoRun keep P_sub mplIo entryTarget FsPres s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, _, hstop_sf, hout0, _, _, _, _⟩ :=
      writeIo_elim_stripS hsvc_sub hsub_no hOk hInv hPrePC hOutPC hOutEffects
        hrun hsp hpre hReal.1 hReal.2.1 hReal.2.2.1 hReal.2.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2.2
    have hdet : Classical.choose hReal.2.2.2.2 = sf :=
      h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop_sf
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout0⟩
  · simp only [hReal, ↓reduceDIte]
    exact hFallbackOk x R s0 hrun hpre hsp

/-- Unconditional `HookOk` for `writeIoLinkedGhost` against `withVmPreserved (specCore γ tp)`. -/
theorem writeIoLinkedGhost_withVmPreserved_ok {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program} {mplIo : MultiPlacement}
    {entryTarget : BitVec 64} {specCore : GhostName → BitVec 64 → Spec α}
    {FsPres : State → State → Prop} {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : subroutine_ok P_sub entryTarget
      (signalSessionIoMultiLib.withCodeLoaded mplIo (withVmPreserved (specCore γ tp))))
    (hInv : SpecStripSInvariant keep (specCore γ tp))
    (hPrePC : ∀ x (s : State) (pc : BitVec 64),
      (specCore γ tp).pre x (s.setPC pc) = (specCore γ tp).pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specCore γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specCore γ tp) x R s0 sf)
    (hOutEffects : ∀ x (R : SepProp) (s0 sf : State),
      SubroutineOutcome (specCore γ tp) x R s0 sf →
      Returned s0 sf ∧ FsPres s0 sf ∧ sf.fs.fds = s0.fs.fds ∧ FsTraced IsFsC s0 sf)
    (hFallbackOk : HookOk fallback (specCore γ tp))
    (hFallbackVm : ∀ s : State, VmPreserved s (fallback s)) :
    HookOk (writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback)
      (withVmPreserved (specCore γ tp)) :=
  hookOk_withVmPreserved
    (writeIoLinkedGhost_ok hsvc_sub hsub_no γ tp hOk hInv hPrePC hOutPC hOutEffects hFallbackOk)
    (writeIoLinkedGhost_vmPreserved keep P_sub mplIo entryTarget specCore FsPres hFallbackVm)

/-- Trajectory-step replay for `writeIoLinkedGhost`: on any state `u` with `ExecFrozen u.mem`,
    `P_sub.CodeLoaded`, `signalSessionIoMultiLib.CodeLoaded`, and no `.Exception`, the ghost step
    replays as real `Steps P_real (u.setPC entryTarget) (f u)` (killing the fallback branch). -/
theorem writeIoLinkedGhost_real_steps {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {mplIo : MultiPlacement}
    {entryTarget : BitVec 64} {specCore : GhostName → BitVec 64 → Spec α}
    {FsPres : State → State → Prop} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (signalSessionIoMultiLib.withCodeLoaded mplIo (withVmPreserved (specCore γ tp))))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specCore γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specCore γ tp).pre x (s.setPC pc) = (specCore γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specCore γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specCore γ tp) x R s0 sf)
    (hOutEffects : ∀ γ tp x (R : SepProp) (s0 sf : State),
      SubroutineOutcome (specCore γ tp) x R s0 sf →
      Returned s0 sf ∧ FsPres s0 sf ∧ sf.fs.fds = s0.fs.fds ∧ FsTraced IsFsC s0 sf)
    (hlr_out_pre : ∀ γ tp x (R : SepProp) (u : State),
      (u.mem ⊨ (specCore γ tp).pre x u ∗ R) → keep (u.readReg64 .lr) = false)
    {u : State}
    (hnoex : ∀ msg,
      (writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hCodeIo : signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem)) :
    let f := writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback
    Steps P_real (u.setPC entryTarget) (f u) ∧
    ExecFrozen (f u).mem ∧
    FsPres u (f u) ∧
    (f u).fs.fds = u.fs.fds ∧
    FsTraced IsFsC u (f u) := by
  classical
  dsimp only []
  have hAct0 := writeIoLinkedGhost_activePre_of_noException hnoex
  rcases hAct0 with ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  have hAct : ActiveF3CallPre specCore u := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  have hlr_out : keep (u.readReg64 .lr) = false := hlr_out_pre γ tp x R u hpre
  obtain ⟨sf, huntil, hvis, hstop_sf, hout0, hFsPres, hFsT, hVm, hfr_sf⟩ :=
    writeIo_elim_stripS hsvc_sub hsub_no (hOk γ tp) (hInv γ tp)
      (hPrePC γ tp) (hOutPC γ tp) (hOutEffects γ tp)
      hrun hsp hpre hFr hlr_out hCodeSub hCodeIo
  obtain ⟨_, _, hfds_eq, _⟩ := hOutEffects γ tp x R u sf hout0
  have hReal : ActiveWriteIoRun keep P_sub mplIo entryTarget FsPres u :=
    ⟨hFr, hlr_out, hCodeSub, hCodeIo, sf, huntil, hstop_sf, hFsPres, hFsT, hVm, hfr_sf⟩
  have hEq :
      writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback u = sf := by
    unfold writeIoLinkedGhost
    simp only [hAct, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop_sf
  rw [hEq]
  have hStepsReal : Steps P_real (u.setPC entryTarget) sf :=
    h2fsgen_steps_lift_of_visitedIn_noExtern
      (hsvc_sub.trans hsvc_real.symm) (fun pc _ => hsub_no pc) hreal_no hvis
  exact ⟨hStepsReal, hfr_sf, hFsPres, hfds_eq, hFsT⟩

/-- Structural branch decomposition of `writeIoLinkedGhost` for `HookNoAllocFailed` callers:
    either `writeIoLinkedGhost` steps via `Steps P_sub (s0.setPC entryTarget)`, equals `fallback s0`,
    or leaves `.trace` unchanged. -/
theorem writeIoLinkedGhost_steps_or_fallback {α : Type}
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo : MultiPlacement)
    (entryTarget : BitVec 64) (specCore : GhostName → BitVec 64 → Spec α)
    (FsPres : State → State → Prop) (fallback : State → State) (s0 : State) :
    (∃ sf : State,
      Steps P_sub (s0.setPC entryTarget) sf ∧
      writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback s0 = sf) ∨
    writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback s0 = fallback s0 ∨
    (writeIoLinkedGhost keep P_sub mplIo entryTarget specCore FsPres fallback s0).trace = s0.trace := by
  classical
  unfold writeIoLinkedGhost
  split
  · split
    · rename_i hReal
      exact Or.inl ⟨Classical.choose hReal.2.2.2.2,
        (Classical.choose_spec hReal.2.2.2.2).1.toSteps, rfl⟩
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-! ## 2. `writeStdoutGhost` (`lsWriteStdoutSym`) & `GhostRowReplayOn` -/

theorem writeStdoutHook_fs_eq (s : State) : (writeStdoutHook s).fs = s.fs := by
  unfold writeStdoutHook
  dsimp only []
  split_ifs <;> rfl

theorem writeStdoutHook_traceDelta_noAllocFailed (s : State) :
    ∃ d : List TraceEvent, (writeStdoutHook s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d := by
  unfold writeStdoutHook
  dsimp only []
  split_ifs
  · exact ⟨[], (List.append_nil s.trace).symm, by simp⟩
  · exact ⟨TraceEvent.ofBytes .stdout _, rfl, by simp [TraceEvent.ofBytes, allocFailedEvent]⟩

/-- `(γ, tp)`-indexed `withLsRet` core contract family for `writeStdoutGhost`. -/
@[expose] def writeStdoutCoreSpecOf [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64) :
    Spec (WriteStdoutGhost × fineCostModel.σ) :=
  withLsRet (writeStdoutHonestCore (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)

/-- `W`-independent `(γ, tp)`-independent ghost hook for `lsWriteStdoutSym` (`write_stdout`). -/
@[expose] noncomputable def writeStdoutGhost [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    State → State :=
  writeIoLinkedGhost keep P_sub mplIo
    (signalSessionIoMultiLib.resolve mplIo cliIoWriteStdoutSym)
    (writeStdoutCoreSpecOf mmpl brkStart lim stk)
    (fun s0 sf => sf.fs = s0.fs)
    writeStdoutHook

theorem writeStdoutGhost_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) (s0 : State) :
    (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk s0).fs = s0.fs :=
  writeIoLinkedGhost_fsPres keep P_sub mplIo _ _ (fun _ _ h => h) writeStdoutHook_fs_eq s0

theorem writeStdoutGhost_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    HookFsTraced IsFsC (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  writeIoLinkedGhost_fsT keep P_sub mplIo _ _ _ writeStdoutHook_fsT

theorem writeStdoutGhost_vmPreserved [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) (s0 : State) :
    VmPreserved s0 (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk s0) :=
  writeIoLinkedGhost_vmPreserved keep P_sub mplIo _ _ _ vmPreserved_writeStdoutHook s0

theorem writeStdoutGhost_rowSpec [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    WriteStdoutRowSpec (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  WriteStdoutRowSpec.intro _

theorem writeStdoutGhost_rowSpecOk [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    GhostRowSpecOk lsWriteStdoutSym (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk) where
  fs_eq := writeStdoutGhost_fs keep P_sub mplIo mmpl brkStart lim stk
  fsT := writeStdoutGhost_fsT keep P_sub mplIo mmpl brkStart lim stk
  rowSpec := by
    unfold ExtraRowSpec
    iterate 20 rw [ite_eq_right (by decide)]
    repeat rw [ite_eq_right (by decide)]
    rw [ite_eq_left (by decide)]
    exact WriteStdoutRowSpec.intro _

theorem writeStdoutGhost_preserves_execFrozen [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) :
    ExecFrozen (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk u).mem ∧
      (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk u).fs = u.fs :=
  ⟨writeIoLinkedGhost_preserves_execFrozen keep P_sub mplIo _ _ _
      (fun s => funext (vmPreserved_writeStdoutHook s).2.2.1) hrun hnoex hFr,
    writeStdoutGhost_fs keep P_sub mplIo mmpl brkStart lim stk u⟩

private theorem specStripSInvariant_writeStdoutCore [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {mmpl : MultiPlacement}
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64) :
    SpecStripSInvariant keep (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp) where
  pre_eq := fun ⟨x, st⟩ s => by
    dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore]
    rw [stripS_r64_eq, stripS_r64_eq, stripS_r64_eq, stripS_sp_eq,
      fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s]
  post_eq := fun ⟨x, st⟩ s0 sf => by
    dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore]
    congr 1; funext evs
    rw [stripS_r64_eq, stripS_fs_eq, stripS_fs_eq, stripS_trace_eq, stripS_trace_eq, stripS_sp_eq,
      fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim _ sf]
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

private theorem writeStdoutCore_pre_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteStdoutGhost × fineCostModel.σ) (s : State) (pc : BitVec 64) :
    (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp).pre y (s.setPC pc) =
      (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp).pre y s := by
  rcases y with ⟨x, st⟩
  cases s; rfl

private theorem writeStdoutCore_outcome_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteStdoutGhost × fineCostModel.σ) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp) y R
      (s0.setPC pc) sf) :
    SubroutineOutcome (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp) y R s0 sf := by
  rcases y with ⟨x, st⟩
  cases s0; cases sf; exact h

private theorem writeStdoutCore_outEffects [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteStdoutGhost × fineCostModel.σ) (R : SepProp) (s0 sf : State)
    (hout : SubroutineOutcome (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp) y R s0 sf) :
    Returned s0 sf ∧ sf.fs = s0.fs ∧ sf.fs.fds = s0.fs.fds ∧ FsTraced IsFsC s0 sf := by
  rcases y with ⟨x, st⟩
  rcases hout with ⟨hret, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have htr : sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout x.bs := hpost.1.2.2.2.2.2.1
    have hfs : sf.fs = s0.fs := hpost.1.2.2.2.2.2.2
    exact ⟨hret, hfs, congrArg FsState.fds hfs,
      ⟨TraceEvent.ofBytes .stdout x.bs, htr, fun _ => congrArg FsState.files hfs⟩⟩
  · dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem writeStdout_subroutine_ok_of_musl9 [LibsignalPlacement]
    {P_sub : Program} {mplIo mplMusl mmpl : MultiPlacement}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext2 : CliIoBlockNoExtern mplIo P_sub 2)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hEnf : lim.enforced = true)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok P_sub (signalSessionIoMultiLib.resolve mplIo cliIoWriteStdoutSym)
      (signalSessionIoMultiLib.withCodeLoaded mplIo
        (withVmPreserved (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp))) := by
  have hwrite_musl :=
    muslWriteStdout32_of_where9_ok hplMusl hsub_no hsvc_sub hMuslCode
  rw [← hresWrite] at hwrite_musl
  have hwcl :=
    cliIoWriteStdout_honest_withCodeLoaded_ok
      (fineHookPoolErrnoSplit γ mmpl tp brkStart) lim hplIo (stk := stk) hext2 hwrite_musl hEnf
  exact subroutine_ok_withCodeLoaded_withLsRet hwcl

/-- Unconditional `HookOk` for `writeStdoutGhost` against
    `withLsRet (writeStdoutSpecPlacedSat (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)`. -/
theorem writeStdoutGhost_ok_sat [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {mplIo mplMusl mmpl : MultiPlacement}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext2 : CliIoBlockNoExtern mplIo P_sub 2)
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hEnf : lim.enforced = true := by decide) :
    HookOk (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk)
      (withLsRet (writeStdoutSpecPlacedSat
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)) :=
  writeIoLinkedGhost_withVmPreserved_ok hsvc_sub hsub_no γ tp
    (writeStdout_subroutine_ok_of_musl9 hplIo hplMusl hMuslCode hext2 hsub_no hsvc_sub
      hresWrite hEnf γ tp)
    (specStripSInvariant_writeStdoutCore hKeepMallocng brkStart lim stk γ tp)
    (writeStdoutCore_pre_setPC mmpl brkStart lim stk γ tp)
    (writeStdoutCore_outcome_setPC mmpl brkStart lim stk γ tp)
    (writeStdoutCore_outEffects mmpl brkStart lim stk γ tp)
    (hookOk_withLsRet (writeStdoutHook_ok_honestCore
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk))
    vmPreserved_writeStdoutHook

/-- Trajectory-aware `GhostRowReplayOn` (`entryGuard := fun _ => True`) for `writeStdoutGhost`
    at `lsWriteStdoutSym`. -/
theorem writeStdoutGhost_rowReplayOn [LibsignalPlacement]
    {mpl mmpl mplIo mplMusl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext2 : CliIoBlockNoExtern mplIo P_sub 2)
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsWriteStdoutSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsWriteStdoutSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteStdoutSym)))
    (hInvCodeSub : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvCodeIo : ∀ u : State, ExecFrozen u.mem → InvS u →
      signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem → v.fs = u.fs → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    GhostRowReplayOn mpl mmpl InvS EG lsWriteStdoutSym (fun _ => True)
      (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk) where
  preserves_execFrozen u hrun hnoex hFr :=
    writeStdoutGhost_preserves_execFrozen keep P_sub mplIo mmpl brkStart lim stk hrun hnoex hFr
  replay_at_stub W _s0 _sf _ _ _ _ := by
    refine Or.inr ⟨hRealStubNone W, fun u _ _ hpc hrun hnoex hkf hfr hinv => ?_⟩
    obtain ⟨hStepsBody, hfr_sf, hfs_sf, _, _⟩ :=
      writeIoLinkedGhost_real_steps (hRealSvc W) hsvc_sub (hRealNoExt W) hsub_no
        (writeStdout_subroutine_ok_of_musl9 hplIo hplMusl hMuslCode hext2 hsub_no hsvc_sub
          hresWrite hEnf)
        (specStripSInvariant_writeStdoutCore hKeepMallocng brkStart lim stk)
        (writeStdoutCore_pre_setPC mmpl brkStart lim stk)
        (writeStdoutCore_outcome_setPC mmpl brkStart lim stk)
        (writeStdoutCore_outEffects mmpl brkStart lim stk)
        (fun _ _ _ _ u0 hp => hlr_out _ (extract_withLsRet hp).1)
        hnoex hfr (hInvCodeSub u hfr hinv) (hInvCodeIo u hfr hinv)
    have hSteps := (hStubSteps W u hpc hrun hfr hinv).trans hStepsBody
    exact ⟨hSteps, hfr_sf, hInvStep W u _ hSteps hkf hfr_sf hfs_sf hinv⟩

/-- `ExtraRowReplayOn` lift of `writeStdoutGhost_rowReplayOn` at `lsWriteStdoutSym`. -/
theorem writeStdoutGhost_extraRowReplayOn [LibsignalPlacement]
    {mpl mmpl mplIo mplMusl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext2 : CliIoBlockNoExtern mplIo P_sub 2)
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsWriteStdoutSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsWriteStdoutSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteStdoutSym)))
    (hInvCodeSub : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvCodeIo : ∀ u : State, ExecFrozen u.mem → InvS u →
      signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem → v.fs = u.fs → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowReplayOn mpl mmpl InvS EG lsWriteStdoutSym (fun _ => True)
      (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  (writeStdoutGhost_rowReplayOn hsvc_sub hsub_no hplIo hplMusl hMuslCode hext2 hresWrite
    hKeepMallocng hlr_out hRealStubNone hRealSvc hRealNoExt hStubSteps hInvCodeSub hInvCodeIo
    hInvStep hEnf).toExtraRowReplayOn

/-- Combined `GhostRowOk` (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) for `writeStdoutGhost`. -/
theorem writeStdoutGhost_rowOk [LibsignalPlacement]
    {mpl mmpl mplIo mplMusl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext2 : CliIoBlockNoExtern mplIo P_sub 2)
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsWriteStdoutSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsWriteStdoutSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteStdoutSym)))
    (hInvCodeSub : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvCodeIo : ∀ u : State, ExecFrozen u.mem → InvS u →
      signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem → v.fs = u.fs → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    GhostRowOk mpl mmpl InvS EG lsWriteStdoutSym (fun _ => True)
      (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  ⟨writeStdoutGhost_rowSpecOk keep P_sub mplIo mmpl brkStart lim stk,
   writeStdoutGhost_rowReplayOn hsvc_sub hsub_no hplIo hplMusl hMuslCode hext2 hresWrite
     hKeepMallocng hlr_out hRealStubNone hRealSvc hRealNoExt hStubSteps hInvCodeSub hInvCodeIo
     hInvStep hEnf⟩

/-- Combined `ExtraRowFullOk` (`ExtraRowOk` ∧ `ExtraRowReplayOn`) for `writeStdoutGhost`. -/
theorem writeStdoutGhost_extraRowFullOk [LibsignalPlacement]
    {mpl mmpl mplIo mplMusl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext2 : CliIoBlockNoExtern mplIo P_sub 2)
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsWriteStdoutSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsWriteStdoutSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteStdoutSym)))
    (hInvCodeSub : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvCodeIo : ∀ u : State, ExecFrozen u.mem → InvS u →
      signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem → v.fs = u.fs → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowFullOk mpl mmpl InvS EG lsWriteStdoutSym (fun _ => True)
      (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  (writeStdoutGhost_rowOk hsvc_sub hsub_no hplIo hplMusl hMuslCode hext2 hresWrite
    hKeepMallocng hlr_out hRealStubNone hRealSvc hRealNoExt hStubSteps hInvCodeSub hInvCodeIo
    hInvStep hEnf).toExtraRowFullOk

/-- Direct single-call body replay for `writeStdoutGhost` on any `P_real`. -/
theorem writeStdoutGhost_steps_of_call [LibsignalPlacement]
    {P_real P_sub : Program} {mplIo mplMusl mmpl : MultiPlacement}
    {keep : BitVec 64 → Bool}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext2 : CliIoBlockNoExtern mplIo P_sub 2)
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    {u : State}
    (hnoex : ∀ msg,
      (writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hCodeIo : signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hEnf : lim.enforced = true := by decide) :
    let f := writeStdoutGhost keep P_sub mplIo mmpl brkStart lim stk
    Steps P_real (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteStdoutSym)) (f u) ∧
    ExecFrozen (f u).mem ∧
    (f u).fs = u.fs ∧
    FsTraced IsFsC u (f u) := by
  dsimp only []
  obtain ⟨hSteps, hFr', hFs, _, hFsT⟩ :=
    writeIoLinkedGhost_real_steps hsvc_real hsvc_sub hreal_no hsub_no
      (writeStdout_subroutine_ok_of_musl9 hplIo hplMusl hMuslCode hext2 hsub_no hsvc_sub
        hresWrite hEnf)
      (specStripSInvariant_writeStdoutCore hKeepMallocng brkStart lim stk)
      (writeStdoutCore_pre_setPC mmpl brkStart lim stk)
      (writeStdoutCore_outcome_setPC mmpl brkStart lim stk)
      (writeStdoutCore_outEffects mmpl brkStart lim stk)
      (fun _ _ _ _ u0 hp => hlr_out _ (extract_withLsRet hp).1)
      hnoex hFr hCodeSub hCodeIo
  exact ⟨hSteps, hFr', hFs, hFsT⟩

/-! ## 3. `writeFileGhost` (`lsWriteFileSym`) & `WriteFileRowReplayOn` -/

/-- Behind-stub `On` replay bundle for `lsWriteFileSym` (`write_file`), which mutates `fs.files`
    via `cliIo.wr` while preserving `fs.fds` (`FdsGe3Closed`) and `FsTraced IsFsC`. -/
structure WriteFileRowReplayOn
    (mpl mmpl : MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (sym : String) (entryGuard : State → Prop) (f : State → State) : Prop where
  preserves_execFrozen :
    ∀ u : State, u.status = .Running → (∀ msg, (f u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      ExecFrozen (f u).mem ∧ (f u).fs.fds = u.fs.fds ∧ FsTraced IsFsC u (f u)
  replay_at_stub :
    ∀ (W : CliHooks) (s0 sf : State),
      let stubPc  := libsignalSessionLib.resolve mpl sym
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real  := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
      entryGuard s0 →
      (sf.status = .Running → sf.pc = s0.readReg64 .lr) →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      (P_real.externAt? stubPc = some f ∧
        ∀ u : State,
          Steps P_ghost s0 u → Steps P_ghost (f u) sf →
          u.pc = stubPc → u.status = .Running →
          (∀ msg, (f u).status ≠ .Exception msg) →
          u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem → InvS u →
          ExecFrozen (f u).mem ∧ InvS (f u)) ∨
      (P_real.externAt? stubPc = none ∧
        ∀ u : State,
          Steps P_ghost s0 u → Steps P_ghost (f u) sf →
          u.pc = stubPc → u.status = .Running →
          (∀ msg, (f u).status ≠ .Exception msg) →
          u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem → InvS u →
          Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvS (f u))

theorem WriteFileRowReplayOn.toExtraRowReplayOn
    {mpl mmpl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {entryGuard : State → Prop} {f : State → State}
    (h : WriteFileRowReplayOn mpl mmpl InvS EG lsWriteFileSym entryGuard f) :
    ExtraRowReplayOn mpl mmpl InvS EG lsWriteFileSym entryGuard f :=
  ExtraRowReplayOn.of_writeFile
    (fun u hrun hnoex hfr => (h.preserves_execFrozen u hrun hnoex hfr).1)
    h.replay_at_stub

theorem writeFileHook_fds_eq (s : State) : (writeFileHook s).fs.fds = s.fs.fds := by
  unfold writeFileHook
  dsimp only []
  split_ifs
  · rfl
  · rfl
  · rfl
  · have hs1 :
        (s.appendTrace [.fileChanged (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1))]).fs.fds =
          s.fs.fds := rfl
    generalize s.appendTrace [.fileChanged (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1))] =
      s1 at hs1 ⊢
    cases blockingAncestor? s1.fs (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1)) with
    | some _ => exact hs1
    | none =>
      cases s1.fs.files (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1)) with
      | none => exact hs1
      | some entry => cases entry <;> exact hs1

theorem writeFileHook_traceDelta_noAllocFailed (s : State) :
    ∃ d : List TraceEvent, (writeFileHook s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d := by
  unfold writeFileHook
  dsimp only []
  split_ifs
  · exact ⟨[], (List.append_nil s.trace).symm, by simp⟩
  · exact ⟨[], (List.append_nil s.trace).symm, by simp⟩
  · exact ⟨[], (List.append_nil s.trace).symm, by simp⟩
  · let p := readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1)
    have hs1 : (s.appendTrace [.fileChanged p]).trace = s.trace ++ [.fileChanged p] := rfl
    have hn1 : allocFailedEvent ∉ [TraceEvent.fileChanged p] := by simp [allocFailedEvent]
    generalize s.appendTrace [.fileChanged p] = s1 at hs1 ⊢
    cases blockingAncestor? s1.fs p with
    | some _ => exact ⟨[.fileChanged p], hs1, hn1⟩
    | none =>
      cases s1.fs.files p with
      | none => exact ⟨[.fileChanged p], hs1, hn1⟩
      | some entry => cases entry <;> exact ⟨[.fileChanged p], hs1, hn1⟩

/-- `(γ, tp)`-indexed `withLsRet` core contract family for `writeFileGhost`. -/
@[expose] def writeFileCoreSpecOf [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64) :
    Spec (WriteFileGhost × fineCostModel.σ) :=
  withLsRet (writeFileHonestCore cliIo (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)

/-- `W`-independent `(γ, tp)`-independent ghost hook for `lsWriteFileSym` (`write_file`). -/
@[expose] noncomputable def writeFileGhost [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    State → State :=
  writeIoLinkedGhost keep P_sub mplIo
    (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)
    (writeFileCoreSpecOf mmpl brkStart lim stk)
    (fun s0 sf => sf.fs.fds = s0.fs.fds)
    writeFileHook

theorem writeFileGhost_fds [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) (s0 : State) :
    (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk s0).fs.fds = s0.fs.fds :=
  writeIoLinkedGhost_fsPres keep P_sub mplIo _ _
    (fun _ _ h => congrArg FsState.fds h) writeFileHook_fds_eq s0

theorem writeFileGhost_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    HookFsTraced IsFsC (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  writeIoLinkedGhost_fsT keep P_sub mplIo _ _ _ writeFileHook_fsT

theorem writeFileGhost_vmPreserved [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) (s0 : State) :
    VmPreserved s0 (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk s0) :=
  writeIoLinkedGhost_vmPreserved keep P_sub mplIo _ _ _ vmPreserved_writeFileHook s0

theorem writeFileGhost_rowSpec [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    WriteFileRowSpec (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  WriteFileRowSpec.intro _

theorem writeFileGhost_rowOk [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    WriteFileRowOk (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk) where
  fsT := writeFileGhost_fsT keep P_sub mplIo mmpl brkStart lim stk
  rowSpec := WriteFileRowSpec.intro _

theorem writeFileGhost_preserves_execFrozen [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) :
    ExecFrozen (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk u).mem ∧
      (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk u).fs.fds = u.fs.fds ∧
      FsTraced IsFsC u (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk u) :=
  ⟨writeIoLinkedGhost_preserves_execFrozen keep P_sub mplIo _ _ _
      (fun s => funext (vmPreserved_writeFileHook s).2.2.1) hrun hnoex hFr,
    writeFileGhost_fds keep P_sub mplIo mmpl brkStart lim stk u,
    writeFileGhost_fsT keep P_sub mplIo mmpl brkStart lim stk u⟩

private theorem specStripSInvariant_writeFileCore [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {mmpl : MultiPlacement}
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64) :
    SpecStripSInvariant keep (writeFileCoreSpecOf mmpl brkStart lim stk γ tp) where
  pre_eq := fun ⟨x, st⟩ s => by
    dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore]
    rw [stripS_r64_eq, stripS_r64_eq, stripS_r64_eq, stripS_r64_eq, stripS_r64_eq,
      stripS_fs_eq, stripS_sp_eq,
      fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s]
  post_eq := fun ⟨x, st⟩ s0 sf => by
    dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore]
    congr 1; funext evs
    rw [stripS_r64_eq, stripS_fs_eq, stripS_fs_eq, stripS_trace_eq, stripS_trace_eq,
      fsTraced_stripS_eq, stripS_sp_eq,
      fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim _ sf]
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

private theorem writeFileCore_pre_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteFileGhost × fineCostModel.σ) (s : State) (pc : BitVec 64) :
    (writeFileCoreSpecOf mmpl brkStart lim stk γ tp).pre y (s.setPC pc) =
      (writeFileCoreSpecOf mmpl brkStart lim stk γ tp).pre y s := by
  rcases y with ⟨x, st⟩
  cases s; rfl

private theorem writeFileCore_outcome_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteFileGhost × fineCostModel.σ) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (writeFileCoreSpecOf mmpl brkStart lim stk γ tp) y R
      (s0.setPC pc) sf) :
    SubroutineOutcome (writeFileCoreSpecOf mmpl brkStart lim stk γ tp) y R s0 sf := by
  rcases y with ⟨x, st⟩
  cases s0; cases sf; exact h

private theorem writeFileCore_outEffects [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteFileGhost × fineCostModel.σ) (R : SepProp) (s0 sf : State)
    (hout : SubroutineOutcome (writeFileCoreSpecOf mmpl brkStart lim stk γ tp) y R s0 sf) :
    Returned s0 sf ∧ sf.fs.fds = s0.fs.fds ∧ sf.fs.fds = s0.fs.fds ∧ FsTraced IsFsC s0 sf := by
  rcases y with ⟨x, st⟩
  rcases hout with ⟨hret, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfds : sf.fs.fds = s0.fs.fds := hpost.1.2.2.2.2.1
    have hfst : FsTraced IsFsC s0 sf := hpost.1.2.2.2.2.2.1
    exact ⟨hret, hfds, hfds, hfst⟩
  · dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem writeFile_subroutine_ok_of_musl9 [LibsignalPlacement]
    {P_sub : Program} {mplIo mplMusl mmpl : MultiPlacement}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hEnf : lim.enforced = true)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok P_sub (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mplIo
        (withVmPreserved (writeFileCoreSpecOf mmpl brkStart lim stk γ tp))) := by
  have hopen := muslOpenCreateTrunc_of_where9_ok hplMusl 3#64 hsub_no hsvc_sub hMuslCode
  have herrno := muslErrnoLocation_of_where9_ok hplMusl hsub_no hsvc_sub hMuslCode
  have hwrite := muslWriteFile32Clamped_of_where9_ok hplMusl hsub_no hsvc_sub hMuslCode
  have hclose := muslClose48Local_of_where9_ok hplMusl hsub_no hsvc_sub hMuslCode
  rw [← hresOpen] at hopen
  rw [← hresErrno] at herrno
  rw [← hresWrite] at hwrite
  rw [← hresClose] at hclose
  have hwcl_clamped :=
    cliIoWriteFile_budget_withCodeLoaded_ok
      (fineHookPoolErrnoSplit γ mmpl tp brkStart) lim hplIo stk hext1
      hopen herrno hwrite hclose hEnf
  have hwcl_sat :
      subroutine_ok P_sub (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)
        (signalSessionIoMultiLib.withCodeLoaded mplIo
          (writeFileSpecPlacedSat cliIo
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)) := by
    apply subroutine_ok.of_codeLoaded
    rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _hLP
    dsimp only [MultiPlacedLib.withCodeLoaded, writeFileSpecPlacedSat, withVmPreserved,
      writeFileHonestCore] at hpre
    have hpre_c :
        s0.mem ⊨
          (signalSessionIoMultiLib.withCodeLoaded mplIo
            (writeFileSpecPlacedSatClamped cliIo
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)).pre (x, st) s0 ∗ R := by
      dsimp only [MultiPlacedLib.withCodeLoaded, writeFileSpecPlacedSatClamped, withVmPreserved,
        writeFileHonestCoreClamped]
      exact hpre
    exact hwcl_clamped.mono_outcome (x, st) R s0 hpc hrun hpre_c hsp (fun _ hout => hout)
  exact subroutine_ok_withCodeLoaded_withLsRet hwcl_sat

/-- Unconditional `HookOk` for `writeFileGhost` against
    `withLsRet (writeFileSpecPlacedSat cliIo (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)`. -/
theorem writeFileGhost_ok_sat [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {mplIo mplMusl mmpl : MultiPlacement}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hEnf : lim.enforced = true := by decide) :
    HookOk (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk)
      (withLsRet (writeFileSpecPlacedSat cliIo
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)) :=
  writeIoLinkedGhost_withVmPreserved_ok hsvc_sub hsub_no γ tp
    (writeFile_subroutine_ok_of_musl9 hplIo hplMusl hMuslCode hext1 hsub_no hsvc_sub
      hresOpen hresErrno hresWrite hresClose hEnf γ tp)
    (specStripSInvariant_writeFileCore hKeepMallocng brkStart lim stk γ tp)
    (writeFileCore_pre_setPC mmpl brkStart lim stk γ tp)
    (writeFileCore_outcome_setPC mmpl brkStart lim stk γ tp)
    (writeFileCore_outEffects mmpl brkStart lim stk γ tp)
    (hookOk_withLsRet (writeFileHook_ok_honestCore
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk))
    vmPreserved_writeFileHook

/-- Companion `withCallGuard` variant of `writeFileGhost_ok_sat`. -/
theorem writeFileGhost_ok_sat_clampedGuard [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {mplIo mplMusl mmpl : MultiPlacement}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hEnf : lim.enforced = true := by decide) :
    HookOk (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk)
      (withLsRet (withCallGuard (fun (x, _) _ => x.bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE)
        (writeFileSpecPlacedSat cliIo
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk))) := by
  have hok :=
    writeFileGhost_ok_sat (brkStart := brkStart) (stk := stk)
      hsvc_sub hsub_no hplIo hplMusl hMuslCode hext1
      hresOpen hresErrno hresWrite hresClose hKeepMallocng γ tp hEnf
  intro y R s0 hrun hpre hsp
  dsimp only [withLsRet, withCallGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hlr, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre0 :
      s0.mem ⊨
        (withLsRet (writeFileSpecPlacedSat cliIo
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)).pre y s0 ∗ R := by
    dsimp only [withLsRet]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hlr, hpre.2⟩
  exact hok y R s0 hrun hpre0 hsp

/-- Trajectory-aware `WriteFileRowReplayOn` (`entryGuard := fun _ => True`) for `writeFileGhost`
    at `lsWriteFileSym`. -/
theorem writeFileGhost_rowReplayOn [LibsignalPlacement]
    {mpl mmpl mplIo mplMusl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsWriteFileSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsWriteFileSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)))
    (hInvCodeSub : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvCodeIo : ∀ u : State, ExecFrozen u.mem → InvS u →
      signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem →
      v.fs.fds = u.fs.fds → FsTraced IsFsC u v → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    WriteFileRowReplayOn mpl mmpl InvS EG lsWriteFileSym (fun _ => True)
      (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk) where
  preserves_execFrozen u hrun hnoex hFr :=
    writeFileGhost_preserves_execFrozen keep P_sub mplIo mmpl brkStart lim stk hrun hnoex hFr
  replay_at_stub W _s0 _sf _ _ _ _ := by
    refine Or.inr ⟨hRealStubNone W, fun u _ _ hpc hrun hnoex hkf hfr hinv => ?_⟩
    obtain ⟨hStepsBody, hfr_sf, _, hfds_sf, hfst_sf⟩ :=
      writeIoLinkedGhost_real_steps (hRealSvc W) hsvc_sub (hRealNoExt W) hsub_no
        (writeFile_subroutine_ok_of_musl9 hplIo hplMusl hMuslCode hext1 hsub_no hsvc_sub
          hresOpen hresErrno hresWrite hresClose hEnf)
        (specStripSInvariant_writeFileCore hKeepMallocng brkStart lim stk)
        (writeFileCore_pre_setPC mmpl brkStart lim stk)
        (writeFileCore_outcome_setPC mmpl brkStart lim stk)
        (writeFileCore_outEffects mmpl brkStart lim stk)
        (fun _ _ _ _ u0 hp => hlr_out _ (extract_withLsRet hp).1)
        hnoex hfr (hInvCodeSub u hfr hinv) (hInvCodeIo u hfr hinv)
    have hSteps := (hStubSteps W u hpc hrun hfr hinv).trans hStepsBody
    exact ⟨hSteps, hfr_sf, hInvStep W u _ hSteps hkf hfr_sf hfds_sf hfst_sf hinv⟩

/-- `ExtraRowReplayOn` lift of `writeFileGhost_rowReplayOn` at `lsWriteFileSym`. -/
theorem writeFileGhost_extraRowReplayOn [LibsignalPlacement]
    {mpl mmpl mplIo mplMusl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsWriteFileSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsWriteFileSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)))
    (hInvCodeSub : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvCodeIo : ∀ u : State, ExecFrozen u.mem → InvS u →
      signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem →
      v.fs.fds = u.fs.fds → FsTraced IsFsC u v → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowReplayOn mpl mmpl InvS EG lsWriteFileSym (fun _ => True)
      (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  (writeFileGhost_rowReplayOn hsvc_sub hsub_no hplIo hplMusl hMuslCode hext1
    hresOpen hresErrno hresWrite hresClose hKeepMallocng hlr_out hRealStubNone hRealSvc
    hRealNoExt hStubSteps hInvCodeSub hInvCodeIo hInvStep hEnf).toExtraRowReplayOn

/-- Combined `ExtraRowFullOk` (`ExtraRowOk` ∧ `ExtraRowReplayOn`) for `writeFileGhost`. -/
theorem writeFileGhost_extraRowFullOk [LibsignalPlacement]
    {mpl mmpl mplIo mplMusl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsWriteFileSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsWriteFileSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)))
    (hInvCodeSub : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvCodeIo : ∀ u : State, ExecFrozen u.mem → InvS u →
      signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem →
      v.fs.fds = u.fs.fds → FsTraced IsFsC u v → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowFullOk mpl mmpl InvS EG lsWriteFileSym (fun _ => True)
      (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  ExtraRowFullOk.of_writeFile
    (writeFileGhost_rowOk keep P_sub mplIo mmpl brkStart lim stk)
    (writeFileGhost_extraRowReplayOn hsvc_sub hsub_no hplIo hplMusl hMuslCode hext1
      hresOpen hresErrno hresWrite hresClose hKeepMallocng hlr_out hRealStubNone hRealSvc
      hRealNoExt hStubSteps hInvCodeSub hInvCodeIo hInvStep hEnf)

/-- Direct single-call body replay for `writeFileGhost` on any `P_real`. -/
theorem writeFileGhost_steps_of_call [LibsignalPlacement]
    {P_real P_sub : Program} {mplIo mplMusl mmpl : MultiPlacement}
    {keep : BitVec 64 → Bool}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    {u : State}
    (hnoex : ∀ msg,
      (writeFileGhost keep P_sub mplIo mmpl brkStart lim stk u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hCodeIo : signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hEnf : lim.enforced = true := by decide) :
    let f := writeFileGhost keep P_sub mplIo mmpl brkStart lim stk
    Steps P_real (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)) (f u) ∧
    ExecFrozen (f u).mem ∧
    (f u).fs.fds = u.fs.fds ∧
    FsTraced IsFsC u (f u) := by
  dsimp only []
  obtain ⟨hSteps, hFr', _, hFds, hFsT⟩ :=
    writeIoLinkedGhost_real_steps hsvc_real hsvc_sub hreal_no hsub_no
      (writeFile_subroutine_ok_of_musl9 hplIo hplMusl hMuslCode hext1 hsub_no hsvc_sub
        hresOpen hresErrno hresWrite hresClose hEnf)
      (specStripSInvariant_writeFileCore hKeepMallocng brkStart lim stk)
      (writeFileCore_pre_setPC mmpl brkStart lim stk)
      (writeFileCore_outcome_setPC mmpl brkStart lim stk)
      (writeFileCore_outEffects mmpl brkStart lim stk)
      (fun _ _ _ _ u0 hp => hlr_out _ (extract_withLsRet hp).1)
      hnoex hFr hCodeSub hCodeIo
  exact ⟨hSteps, hFr', hFds, hFsT⟩

/-! ## 4. `FdsGe3Closed`-Fallback Twin (`writeFileFdsGhost`) -/

/-- `writeFileHonestCore` omitting `FdsGe3Closed s.fs` from `.pre` while retaining the full honest
    `.post`, for callers where `FdsGe3Closed` is maintained by trajectory invariants rather than
    threaded through `RunSem`. -/
@[expose] def writeFileNoFdsHonestCore {M : AllocCostModel} (io : IoModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (WriteFileGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x2 = x.buf ∧ (s.readReg64 .x3).toNat = x.bs.length ∧
      x.path.length < 2 ^ 32 ∧ io.pathOk x.path ∧
      FitsEnv M lim st (WriteFileEnv x.path.length) ∧
      writeFileStackFloor ≤ stk ∧
      x.bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := (writeFileHonestCore io A lim stk).post

/-- `withVmPreserved` wrapper around `writeFileNoFdsHonestCore`. -/
@[expose] def writeFileNoFdsSpecPlacedSat {M : AllocCostModel} (io : IoModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (WriteFileGhost × M.σ) :=
  withVmPreserved (writeFileNoFdsHonestCore io A lim stk)

/-- The idealized `writeFileHook` meets `writeFileNoFdsHonestCore` without `FdsGe3Closed`. -/
theorem writeFileHook_ok_noFdsCore {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    HookOk writeFileHook (writeFileNoFdsHonestCore cliIo A lim stk) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ (writeFileSpecPlaced cliIo A lim stk).pre (x, st) s0 ∗ R := by
    simp only [writeFileNoFdsHonestCore, writeFileSpecPlaced, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, hfits, _, _⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, hfits⟩, hmem⟩
  rcases writeFileHook_ok_placed A lim stk (x, st) R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcs, ?_⟩
    simp only [writeFileSpecPlaced, sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    dsimp only [writeFileNoFdsHonestCore, writeFileHonestCore]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨henv, hwr, htr, hstd⟩, hmem⟩
    refine ⟨⟨henv, hwr, htr, hstd, writeFileHook_fds_eq s0, writeFileHook_fsT s0, ?_⟩, hmem⟩
    intro hnoaf
    obtain ⟨d, hd, hnd⟩ := writeFileHook_traceDelta_noAllocFailed s0
    rw [hd, List.mem_append, not_or]
    exact ⟨hnoaf, hnd⟩
  · exact Or.inr hrest

/-- `(γ, tp)`-indexed `withLsRet` core contract family for `writeFileFdsGhost`. -/
@[expose] def writeFileNoFdsCoreSpecOf [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64) :
    Spec (WriteFileGhost × fineCostModel.σ) :=
  withLsRet (writeFileNoFdsHonestCore cliIo (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)

/-- `FdsGe3Closed`-guarded ghost hook for `lsWriteFileSym`: coincides definitionally with
    `writeFileGhost` whenever `FdsGe3Closed s0.fs` holds (so trajectory replay holds on any `InvS`
    implying `FdsGe3Closed`), and falls back to `writeFileHook` inside
    `ActiveF3CallPre (writeFileNoFdsCoreSpecOf ...)` when `¬ FdsGe3Closed s0.fs` (giving `HookOk`
    against `withLsRet (writeFileNoFdsSpecPlacedSat ...)` with no `FdsGe3Closed` premise in `.pre`). -/
@[expose] noncomputable def writeFileFdsGhost [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) (s0 : State) : State := by
  classical
  exact if FdsGe3Closed s0.fs then
    writeFileGhost keep P_sub mplIo mmpl brkStart lim stk s0
  else if _ : ActiveF3CallPre (writeFileNoFdsCoreSpecOf mmpl brkStart lim stk) s0 then
    writeFileHook s0
  else
    { s0 with status := .Exception "write_file ghost-hook precondition violated" }

theorem writeFileFdsGhost_eq_of_fds [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    {s0 : State} (hFds : FdsGe3Closed s0.fs) :
    writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk s0 =
      writeFileGhost keep P_sub mplIo mmpl brkStart lim stk s0 := by
  unfold writeFileFdsGhost
  simp only [hFds, ↓reduceIte]

theorem writeFileFdsGhost_fds [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) (s0 : State) :
    (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk s0).fs.fds = s0.fs.fds := by
  classical
  unfold writeFileFdsGhost
  split
  · exact writeFileGhost_fds keep P_sub mplIo mmpl brkStart lim stk s0
  · split
    · exact writeFileHook_fds_eq s0
    · rfl

theorem writeFileFdsGhost_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    HookFsTraced IsFsC (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk) := by
  classical
  intro s0
  unfold writeFileFdsGhost
  split
  · exact writeFileGhost_fsT keep P_sub mplIo mmpl brkStart lim stk s0
  · split
    · exact writeFileHook_fsT s0
    · exact FsTraced.of_eq rfl rfl

theorem writeFileFdsGhost_vmPreserved [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) (s0 : State) :
    VmPreserved s0 (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk s0) := by
  classical
  unfold writeFileFdsGhost
  split
  · exact writeFileGhost_vmPreserved keep P_sub mplIo mmpl brkStart lim stk s0
  · split
    · exact vmPreserved_writeFileHook s0
    · exact VmPreserved.of_eq rfl rfl rfl rfl rfl

theorem writeFileFdsGhost_rowSpec [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    WriteFileRowSpec (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  WriteFileRowSpec.intro _

theorem writeFileFdsGhost_rowOk [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    WriteFileRowOk (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk) where
  fsT := writeFileFdsGhost_fsT keep P_sub mplIo mmpl brkStart lim stk
  rowSpec := WriteFileRowSpec.intro _

theorem writeFileFdsGhost_preserves_execFrozen [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) :
    ExecFrozen (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk u).mem ∧
      (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk u).fs.fds = u.fs.fds ∧
      FsTraced IsFsC u (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk u) := by
  classical
  by_cases hFds : FdsGe3Closed u.fs
  · rw [writeFileFdsGhost_eq_of_fds keep P_sub mplIo mmpl brkStart lim stk hFds] at hnoex ⊢
    exact writeFileGhost_preserves_execFrozen keep P_sub mplIo mmpl brkStart lim stk hrun hnoex hFr
  · have hAct : ActiveF3CallPre (writeFileNoFdsCoreSpecOf mmpl brkStart lim stk) u := by
      by_contra hNot
      apply hnoex "write_file ghost-hook precondition violated"
      unfold writeFileFdsGhost
      simp only [hFds, ↓reduceIte, hNot, ↓reduceDIte]
    have hEq :
        writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk u = writeFileHook u := by
      unfold writeFileFdsGhost
      simp only [hFds, ↓reduceIte, hAct, ↓reduceDIte]
    rw [hEq]
    exact ⟨ExecFrozen.of_perm_eq hFr (fun a => (vmPreserved_writeFileHook u).2.2.1 a),
      writeFileHook_fds_eq u, writeFileHook_fsT u⟩

theorem writeFileFdsGhost_steps_or_fallback [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (mplIo mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) (s0 : State) :
    (∃ sf : State,
      Steps P_sub (s0.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)) sf ∧
      writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk s0 = sf) ∨
    writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk s0 = writeFileHook s0 ∨
    (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk s0).trace = s0.trace := by
  classical
  by_cases hFds : FdsGe3Closed s0.fs
  · rw [writeFileFdsGhost_eq_of_fds keep P_sub mplIo mmpl brkStart lim stk hFds]
    exact writeIoLinkedGhost_steps_or_fallback keep P_sub mplIo
      (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)
      (writeFileCoreSpecOf mmpl brkStart lim stk)
      (fun a b => b.fs.fds = a.fs.fds) writeFileHook s0
  · unfold writeFileFdsGhost
    simp only [hFds, ↓reduceIte]
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- `HookOk` for `writeFileFdsGhost` against `withLsRet (writeFileNoFdsSpecPlacedSat ...)`
    (no `FdsGe3Closed` premise in `.pre`). -/
theorem writeFileFdsGhost_ok_noFds_sat [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {mplIo mplMusl mmpl : MultiPlacement}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hEnf : lim.enforced = true := by decide) :
    HookOk (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk)
      (withLsRet (writeFileNoFdsSpecPlacedSat cliIo
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)) := by
  classical
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  by_cases hFds : FdsGe3Closed s0.fs
  · have hEq := writeFileFdsGhost_eq_of_fds keep P_sub mplIo mmpl brkStart lim stk hFds
    have hpre_fds :
        s0.mem ⊨
          (withLsRet (writeFileSpecPlacedSat cliIo
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)).pre (x, st) s0 ∗ R := by
      dsimp only [withLsRet, writeFileNoFdsSpecPlacedSat, writeFileSpecPlacedSat,
        withVmPreserved, writeFileNoFdsHonestCore, writeFileHonestCore] at hpre ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨hlr, hpre⟩
      refine ⟨hlr, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, hfits, hstk_fl, hbs⟩, hmem⟩
      exact ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, hfits, hstk_fl, hFds, hbs⟩, hmem⟩
    have hok :=
      writeFileGhost_ok_sat hsvc_sub hsub_no hplIo hplMusl hMuslCode hext1
        hresOpen hresErrno hresWrite hresClose hKeepMallocng γ tp hEnf (x, st) R s0 hrun hpre_fds hsp
    rwa [hEq]
  · have hAct : ActiveF3CallPre (writeFileNoFdsCoreSpecOf mmpl brkStart lim stk) s0 :=
      ⟨hrun, hsp, γ, tp, (x, st), R, hpre⟩
    have hEq :
        writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk s0 = writeFileHook s0 := by
      unfold writeFileFdsGhost
      simp only [hFds, ↓reduceIte, hAct, ↓reduceDIte]
    have hfb :=
      hookOk_withVmPreserved
        (hookOk_withLsRet
          (writeFileHook_ok_noFdsCore (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk))
        vmPreserved_writeFileHook (x, st) R s0 hrun hpre hsp
    rwa [hEq]

/-- `HookOk` for `writeFileFdsGhost` against `withLsRet (writeFileSpecPlacedSat ...)`
    (weakening `writeFileFdsGhost_ok_noFds_sat` across `FdsGe3Closed s0.fs`). -/
theorem writeFileFdsGhost_ok_sat [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {mplIo mplMusl mmpl : MultiPlacement}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hEnf : lim.enforced = true := by decide) :
    HookOk (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk)
      (withLsRet (writeFileSpecPlacedSat cliIo
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  have hpre0 :
      s0.mem ⊨
        (withLsRet (writeFileNoFdsSpecPlacedSat cliIo
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)).pre (x, st) s0 ∗ R := by
    dsimp only [withLsRet, writeFileNoFdsSpecPlacedSat, writeFileSpecPlacedSat,
      withVmPreserved, writeFileNoFdsHonestCore, writeFileHonestCore] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hlr, hpre⟩
    refine ⟨hlr, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, hfits, hstk_fl, _hFds, hbs⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, hfits, hstk_fl, hbs⟩, hmem⟩
  exact writeFileFdsGhost_ok_noFds_sat hsvc_sub hsub_no hplIo hplMusl hMuslCode hext1
    hresOpen hresErrno hresWrite hresClose hKeepMallocng γ tp hEnf (x, st) R s0 hrun hpre0 hsp

/-- Trajectory-aware `WriteFileRowReplayOn` for `writeFileFdsGhost` under any invariant `InvS`
    implying `FdsGe3Closed u.fs`. -/
theorem writeFileFdsGhost_rowReplayOn [LibsignalPlacement]
    {mpl mmpl mplIo mplMusl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsWriteFileSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsWriteFileSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)))
    (hInvCodeSub : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvCodeIo : ∀ u : State, ExecFrozen u.mem → InvS u →
      signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hInvFds : ∀ u : State, InvS u → FdsGe3Closed u.fs)
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem →
      v.fs.fds = u.fs.fds → FsTraced IsFsC u v → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    WriteFileRowReplayOn mpl mmpl InvS EG lsWriteFileSym (fun _ => True)
      (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk) where
  preserves_execFrozen u hrun hnoex hFr :=
    writeFileFdsGhost_preserves_execFrozen keep P_sub mplIo mmpl brkStart lim stk hrun hnoex hFr
  replay_at_stub W _s0 _sf _ _ _ _ := by
    refine Or.inr ⟨hRealStubNone W, fun u _ _ hpc hrun hnoex hkf hfr hinv => ?_⟩
    have hEq := writeFileFdsGhost_eq_of_fds keep P_sub mplIo mmpl brkStart lim stk (hInvFds u hinv)
    rw [hEq] at hnoex hkf ⊢
    obtain ⟨hStepsBody, hfr_sf, hfds_sf, hfst_sf⟩ :=
      writeFileGhost_steps_of_call (hRealSvc W) hsvc_sub (hRealNoExt W) hsub_no
        hplIo hplMusl hMuslCode hext1 hresOpen hresErrno hresWrite hresClose
        hKeepMallocng hlr_out hnoex hfr (hInvCodeSub u hfr hinv) (hInvCodeIo u hfr hinv) hEnf
    have hSteps := (hStubSteps W u hpc hrun hfr hinv).trans hStepsBody
    exact ⟨hSteps, hfr_sf, hInvStep W u _ hSteps hkf hfr_sf hfds_sf hfst_sf hinv⟩

/-- `ExtraRowReplayOn` lift of `writeFileFdsGhost_rowReplayOn` at `lsWriteFileSym`. -/
theorem writeFileFdsGhost_extraRowReplayOn [LibsignalPlacement]
    {mpl mmpl mplIo mplMusl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsWriteFileSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsWriteFileSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)))
    (hInvCodeSub : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvCodeIo : ∀ u : State, ExecFrozen u.mem → InvS u →
      signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hInvFds : ∀ u : State, InvS u → FdsGe3Closed u.fs)
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem →
      v.fs.fds = u.fs.fds → FsTraced IsFsC u v → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowReplayOn mpl mmpl InvS EG lsWriteFileSym (fun _ => True)
      (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  (writeFileFdsGhost_rowReplayOn hsvc_sub hsub_no hplIo hplMusl hMuslCode hext1
    hresOpen hresErrno hresWrite hresClose hKeepMallocng hlr_out hRealStubNone hRealSvc
    hRealNoExt hStubSteps hInvCodeSub hInvCodeIo hInvFds hInvStep hEnf).toExtraRowReplayOn

/-- Combined `ExtraRowFullOk` for `writeFileFdsGhost` under `hInvFds`. -/
theorem writeFileFdsGhost_extraRowFullOk [LibsignalPlacement]
    {mpl mmpl mplIo mplMusl : MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsWriteFileSym) = none)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hStubSteps : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl lsWriteFileSym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
        (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)))
    (hInvCodeSub : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvCodeIo : ∀ u : State, ExecFrozen u.mem → InvS u →
      signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hInvFds : ∀ u : State, InvS u → FdsGe3Closed u.fs)
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem →
      v.fs.fds = u.fs.fds → FsTraced IsFsC u v → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowFullOk mpl mmpl InvS EG lsWriteFileSym (fun _ => True)
      (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk) :=
  ExtraRowFullOk.of_writeFile
    (writeFileFdsGhost_rowOk keep P_sub mplIo mmpl brkStart lim stk)
    (writeFileFdsGhost_extraRowReplayOn hsvc_sub hsub_no hplIo hplMusl hMuslCode hext1
      hresOpen hresErrno hresWrite hresClose hKeepMallocng hlr_out hRealStubNone hRealSvc
      hRealNoExt hStubSteps hInvCodeSub hInvCodeIo hInvFds hInvStep hEnf)

/-- Direct single-call body replay for `writeFileFdsGhost` at any call state `u` with
    `FdsGe3Closed u.fs`. -/
theorem writeFileFdsGhost_steps_of_call [LibsignalPlacement]
    {P_real P_sub : Program} {mplIo mplMusl mmpl : MultiPlacement}
    {keep : BitVec 64 → Bool}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hplIo : signalSessionIoMultiLib.Placeable mplIo)
    (hplMusl : muslSysPlacedLib.Placeable mplMusl)
    (hMuslCode : ∀ m : Memory, P_sub.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mplMusl m)
    (hext1 : CliIoBlockNoExtern mplIo P_sub 1)
    (hresOpen :
      signalSessionIoMultiLib.resolve mplIo cliIoOpenSym =
        muslSysPlacedLib.fnAddr mplMusl "open")
    (hresErrno :
      signalSessionIoMultiLib.resolve mplIo cliIoErrnoLocationSym =
        muslSysPlacedLib.fnAddr mplMusl "__errno_location")
    (hresWrite :
      signalSessionIoMultiLib.resolve mplIo cliIoWriteSym =
        muslSysPlacedLib.fnAddr mplMusl "write")
    (hresClose :
      signalSessionIoMultiLib.resolve mplIo cliIoCloseSym =
        muslSysPlacedLib.fnAddr mplMusl "close")
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hlr_out : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    {u : State}
    (hFds : FdsGe3Closed u.fs)
    (hnoex : ∀ msg,
      (writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hCodeIo : signalSessionIoMultiLib.CodeLoaded mplIo (stripExecOutside keep u.mem))
    (hEnf : lim.enforced = true := by decide) :
    let f := writeFileFdsGhost keep P_sub mplIo mmpl brkStart lim stk
    Steps P_real (u.setPC (signalSessionIoMultiLib.resolve mplIo cliIoWriteFileSym)) (f u) ∧
    ExecFrozen (f u).mem ∧
    (f u).fs.fds = u.fs.fds ∧
    FsTraced IsFsC u (f u) := by
  dsimp only []
  have hEq := writeFileFdsGhost_eq_of_fds keep P_sub mplIo mmpl brkStart lim stk hFds
  rw [hEq] at hnoex ⊢
  exact writeFileGhost_steps_of_call hsvc_real hsvc_sub hreal_no hsub_no
    hplIo hplMusl hMuslCode hext1 hresOpen hresErrno hresWrite hresClose
    hKeepMallocng hlr_out hnoex hFr hCodeSub hCodeIo hEnf

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoWriteGhostReplays

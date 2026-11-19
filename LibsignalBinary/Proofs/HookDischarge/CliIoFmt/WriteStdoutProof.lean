/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Proofs.SyscallProof
public import VerifiedLibraries.RustStd.Proofs.StdoutRaw
public import LibsignalBinary.Proofs.SignalSession.CliIo.Sym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.MuslWrite
import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutSteps
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Placement-Generic Proof of `libsignal_cli_io::write_stdout` and Honest Consumer Discharge

Assembles the prologue, `0x7fff_f000`-chunk `write(1, ...)` loop, and epilogue from
`WriteStdoutSteps` with the `musl` `write(1, ...)` contract and `PoolErrnoSplit` `USER_VA_LIMIT`
helpers from `MuslWrite`:
1. `cliIoWriteStdoutSpec`: tight `96`-byte stack (`64`-B `write_stdout` frame + `32`-B `musl`
   `write` frame), `ro : Bool`, `bs.length < 2 ^ 63`, and
   `bs.length = 0 ∨ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT`.
2. `cliIoWriteStdout_okWhere`, `cliIoWriteStdout_ok`, and `cliIoWriteStdout_musl_ok`:
   placement-generic proofs on `signalSessionIoMultiLib` block `2` (`cliIoWriteStdoutSym`).
3. `cliIoWriteStdout_honest_withCodeLoadedWhere_ok`, `cliIoWriteStdout_honest_withCodeLoaded_ok`,
   and `cliIoWriteStdout_honest_ok` (`cliIoWriteStdout_budget_ok`): budget-threaded discharge of
   `IoHonestSpecs.writeStdoutSpecPlacedSat A lim stk` via `PoolErrnoSplit` (`evs = []`, `0` heap
   allocations), plus concrete instantiations for `mallocngRustCliAllocBudget`,
   `mallocngHookRustCliAllocBudget`, and `fineHookRustCliAllocBudget`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutProof

open Arm64 ProofLib
open Arm64.Obj (MultiPlacedLib MultiPlacement)
open Arm64.Process (ProcessOutcome)
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.Musl (MuslSysPlacement muslSysPlacedLib muslSysMpl)
open VerifiedLibraries.RustStd (stdoutBytesAt)
open VerifiedLibraries.RustStd.Io (muslWriteStdout32Spec)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FdsHiFrame RustCliAllocBudget VmMemPreserved VmPreserved
  MallocngCostModelIface MallocngCostModelSound
  mallocngRustCliAllocBudget
)
open LibsignalBinary.Heap.SpecBudget (WriteStdoutEnv writeStdoutEnv_nil withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  mallocngHookRustCliAllocBudget fineHookRustCliAllocBudget
)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  cliIoBlocks_len cliIoResolve_eq_base
  cliIoWriteStdoutSym cliIoWriteSym cliIoWriteStdout_lookup
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs (
  writeStdoutStackFloor writeStdoutHonestCore writeStdoutSpecPlacedSat
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst (
  PoolErrnoSplit mallocngPoolErrnoSplit mallocngHookPoolErrnoSplit fineHookPoolErrnoSplit
)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.MuslWrite (
  muslWriteStdout32_ok poolErrnoSplit_pointsToBytes_le_userVa poolErrnoSplit_stackAt_le_two_pow_64
)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutSteps (
  cliIoWriteStdout_prologue cliIoWriteStdout_loop
)

/-! ## 1. Tight `96`-B Specification & Block-`2` Placement-Generic Proofs -/

/-- Tight `96`-byte stack Hoare contract for `libsignal_cli_io::write_stdout(buf, len) -> Result<(), IoError>`
    (`x0 = buf`, `x1 = len`, returning `x0 = 0#64` = `Ok(())`).
    Ghost argument: `(ro, buf, bs)`. -/
@[expose] def cliIoWriteStdoutSpec : Spec (Bool × BitVec 64 × List (BitVec 8)) where
  pre := fun (ro, buf, bs) s0 =>
    ⌜s0.readReg64 .x0 = buf ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      bs.length < 2 ^ 63 ∧
      (bs.length = 0 ∨ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT)⌝ ∗
      stdoutBytesAt ro buf bs ∗ stackAt s0.sp 96
  post := fun (ro, buf, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ sf.fs = s0.fs ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout bs ∧ SyscallPreserved s0 sf⌝ ∗
      stdoutBytesAt ro buf bs ∗ stackAt s0.sp 96
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem vmPreserved_of_syscallPreserved_fs {s0 sf : State}
    (hsys : SyscallPreserved s0 sf) (hfs : sf.fs = s0.fs) :
    VmPreserved s0 sf := by
  have hm := VmMemPreserved.of_vm_tpidr hsys.2.2 hsys.1
  exact ⟨hm.1, hm.2.1, hm.2.2, FdsHiFrame.of_fds_eq (by rw [hfs])⟩

/-- Placement-generic proof of `libsignal_cli_io::write_stdout` (`block[2]`) under `CodeLoadedWhere keep`. -/
theorem cliIoWriteStdout_okWhere {keep : Nat → Bool} (hk2 : keep 2 = true)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext2 : CliIoBlockNoExtern mpl P 2)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere keep mpl muslWriteStdout32Spec)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteStdoutSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere keep mpl cliIoWriteStdoutSpec) := by
  let _ : CliIoPlacement := ⟨mpl, hpl⟩
  have h2_lt : 2 < signalSessionIoMultiLib.blocks.length := by rw [cliIoBlocks_len]; decide
  rw [cliIoResolve_eq_base hpl 2 cliIoWriteStdoutSym h2_lt cliIoWriteStdout_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ro, buf, bs⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoWriteStdoutSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoadedWhere keep mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlt63, hva_or⟩, hmem⟩
  refine ⟨stackAt s0.sp 96 ∗ stdoutBytesAt ro buf bs,
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  apply cliIoWriteStdout_prologue hk2 hext2 hcl0 hpc hrun hsp0 hx0 hx1
  intro sm hcl_m hpc_m hrun_m hsp_m hx19_m hx20_m hx23_m hx24_m hup_m hsys_0m hfs_0m htr_0m
  have hbuf0 : buf + BitVec.ofNat 64 0 = buf := by bv_omega
  have hpre_loop :
      stackAt (s0.sp - 64#64) 32 ∗
        LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutSteps.cliIoWriteStdoutSaved s0 ∗
        stdoutBytesAt ro buf bs =
      stackAt (s0.sp - 64#64) 32 ∗
        LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutSteps.cliIoWriteStdoutSaved s0 ∗
        stdoutBytesAt ro (buf + BitVec.ofNat 64 0) bs ∗ emp := by
    rw [hbuf0]; sep_ac_rfl
  rw [hpre_loop]
  refine cliIoWriteStdout_loop hk2 hext2 hwrite bs.length
    (written := 0) (rem := bs) (F := emp)
    (Nat.le_refl _) (by omega) ?_ hsp0 hcl_m hpc_m hrun_m hsp_m
    (by simpa only [Nat.zero_add] using hx19_m) hx20_m hx23_m hx24_m hup_m ?_
  · intro hpos
    rw [hbuf0]
    rcases hva_or with h0 | hva
    · omega
    · exact hva
  · intro sf Pre_f hent hpc_f hrun_f hsp_f hcs_f hsys_mf hfs_mf htr_mf hx0_f
    refine ⟨?_, hsp_f, hcs_f⟩
    intro hmf
    have hmf' : sf.mem ⊨
        (stackAt s0.sp 96 ∗ stdoutBytesAt ro (buf + BitVec.ofNat 64 0) bs ∗ emp) ∗ R :=
      Satisfies.mono (sepConj_mono_left hent) hmf
    rw [hbuf0] at hmf'
    have hsys_0f : SyscallPreserved s0 sf := hsys_0m.trans hsys_mf
    have hfs_0f : sf.fs = s0.fs := hfs_mf.trans hfs_0m
    have htr_0f : sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout bs := by
      rw [htr_mf, htr_0m]
    have hpost_mem : sf.mem ⊨ (stdoutBytesAt ro buf bs ∗ stackAt s0.sp 96) ∗ R :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf'
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_f, hfs_0f, htr_0f, hsys_0f⟩, hpost_mem⟩

private theorem subroutine_ok_withCodeLoadedWhere_of_plain {α : Type}
    {lib : MultiPlacedLib} (keep : Nat → Bool) (mpl : MultiPlacement)
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry spec) :
    subroutine_ok P entry (lib.withCodeLoadedWhere keep mpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  dsimp only [MultiPlacedLib.withCodeLoadedWhere] at hpre
  rw [sepConj_comm _ ⌜lib.CodeLoadedWhere keep mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp (fun _ hout => hout)

/-- Plain-callee variant of `cliIoWriteStdout_okWhere` (lifts `muslWriteStdout32Spec` to
    `withCodeLoadedWhere`). -/
theorem cliIoWriteStdout_okWhere_of_plain {keep : Nat → Bool} (hk2 : keep 2 = true)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext2 : CliIoBlockNoExtern mpl P 2)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteStdout32Spec) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteStdoutSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere keep mpl cliIoWriteStdoutSpec) :=
  cliIoWriteStdout_okWhere hk2 hpl hext2 (subroutine_ok_withCodeLoadedWhere_of_plain keep mpl hwrite)

private theorem subroutine_ok_withCodeLoaded_of_where {α : Type}
    {lib : MultiPlacedLib} {mpl : MultiPlacement} {P : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok P entry (lib.withCodeLoadedWhere (fun _ => true) mpl spec)) :
    subroutine_ok P entry (lib.withCodeLoaded mpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (lib.withCodeLoadedWhere (fun _ => true) mpl spec).pre x s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded, MultiPlacedLib.withCodeLoadedWhere] at hpre ⊢
    rw [sepConj_comm _ ⌜lib.CodeLoaded mpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm _ ⌜lib.CodeLoadedWhere (fun _ => true) mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨hpre.1.toWhere _, hpre.2⟩
  exact h.mono_outcome x R s0 hpc hrun hpre' hsp (fun _ hout => hout)

private theorem subroutine_ok_strip_withCodeLoadedWhere {α : Type}
    {lib : MultiPlacedLib} {keep : Nat → Bool} {mpl : MultiPlacement}
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hCode : ∀ m : Memory, P.CodeLoaded m → lib.CodeLoadedWhere keep mpl m)
    (h : subroutine_ok P entry (lib.withCodeLoadedWhere keep mpl spec)) :
    subroutine_ok P entry spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hpre' : s0.mem ⊨ (lib.withCodeLoadedWhere keep mpl spec).pre x s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoadedWhere]
    rw [sepConj_comm _ ⌜lib.CodeLoadedWhere keep mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨hCode s0.mem hLP, hpre⟩
  exact subroutine_ok.mono_outcome h x R s0 hpc hrun hpre' hsp (fun _ hout => hout)

private theorem subroutine_ok_strip_withCodeLoaded {α : Type}
    {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hCode : ∀ m : Memory, P.CodeLoaded m → lib.CodeLoaded mpl m)
    (h : subroutine_ok P entry (lib.withCodeLoaded mpl spec)) :
    subroutine_ok P entry spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hpre' : s0.mem ⊨ (lib.withCodeLoaded mpl spec).pre x s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜lib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨hCode s0.mem hLP, hpre⟩
  exact subroutine_ok.mono_outcome h x R s0 hpc hrun hpre' hsp (fun _ hout => hout)

/-- Placement-generic proof of `libsignal_cli_io::write_stdout` (`block[2]`) under `withCodeLoaded`. -/
theorem cliIoWriteStdout_ok
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext2 : CliIoBlockNoExtern mpl P 2)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteStdout32Spec) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteStdoutSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl cliIoWriteStdoutSpec) :=
  subroutine_ok_withCodeLoaded_of_where
    (cliIoWriteStdout_okWhere_of_plain rfl hpl hext2 hwrite)

/-- End-to-end tied proof of `libsignal_cli_io::write_stdout` linked against `muslSysPlacedLib`
    block `7` (`"write"`). -/
theorem cliIoWriteStdout_musl_ok [MuslSysPlacement]
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program}
    (hext : ∀ pc, P.externAt? pc = none)
    (hsvc : P.svc = Syscall.standard)
    (hlink_write :
      signalSessionIoMultiLib.resolve mpl cliIoWriteSym =
        muslSysPlacedLib.fnAddr muslSysMpl "write")
    (hmusl_code : ∀ m : Memory, P.CodeLoaded m → muslSysPlacedLib.CodeLoaded muslSysMpl m) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteStdoutSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl cliIoWriteStdoutSpec) := by
  have hext2 : CliIoBlockNoExtern mpl P 2 := fun _ _ => hext _
  have hwrite_musl : subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "write")
      muslWriteStdout32Spec :=
    subroutine_ok_strip_withCodeLoaded hmusl_code (muslWriteStdout32_ok hext hsvc)
  rw [← hlink_write] at hwrite_musl
  exact cliIoWriteStdout_ok hpl hext2 hwrite_musl

/-! ## 2. Budget-Threaded `IoHonestSpecs.writeStdoutSpecPlacedSat` Discharge -/

/-- Budget-threaded discharge of `IoHonestSpecs.writeStdoutSpecPlacedSat A lim stk` under
    `CodeLoadedWhere keep` for any allocator model satisfying `PoolErrnoSplit` (`evs = []`,
    `0` heap allocations, peak stack `96 ≤ writeStdoutStackFloor = 1024`). -/
theorem cliIoWriteStdout_honest_withCodeLoadedWhere_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {keep : Nat → Bool} (hk2 : keep 2 = true)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hext2 : CliIoBlockNoExtern mpl P 2)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteStdout32Spec)
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteStdoutSym)
      (signalSessionIoMultiLib.withCodeLoadedWhere keep mpl
        (writeStdoutSpecPlacedSat A lim stk)) := by
  have hcore := cliIoWriteStdout_okWhere_of_plain hk2 hpl hext2 hwrite
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, writeStdoutSpecPlacedSat,
    withVmPreserved, writeStdoutHonestCore] at hpre
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoadedWhere keep mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1_nat, _hfits, hstk_lo, hlt63⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bs.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat]; simp
  have hstk_pos : 0 < stk := by unfold writeStdoutStackFloor at hstk_lo; omega
  have hstk_96 : 96 ≤ stk := by unfold writeStdoutStackFloor at hstk_lo; omega
  have hsat_stk_pool : s0.mem ⊨ stackAt s0.sp stk ∗ A.pool lim st s0 ∗ ((x.buf ↦ₛ x.bs) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hstk_hi : stk ≤ 2 ^ 64 :=
    poolErrnoSplit_stackAt_le_two_pow_64 S hstk_pos hsat_stk_pool
  have hva_or : x.bs.length = 0 ∨ x.buf.toNat + x.bs.length ≤ Arm64.USER_VA_LIMIT := by
    rcases Nat.eq_zero_or_pos x.bs.length with h0 | hpos
    · exact Or.inl h0
    · have hsat_va : s0.mem ⊨ A.pool lim st s0 ∗ (x.buf ↦ₛ x.bs) ∗ (stackAt s0.sp stk ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      exact Or.inr (poolErrnoSplit_pointsToBytes_le_userVa S hEnf hpos hsat_va)
  have hstk_split :
      stackAt s0.sp stk =
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 96) ∗ stackAt s0.sp 96 := by
    conv => lhs; rw [show stk = 96 + (stk - 96) by omega]
    rw [stackAt_split_bottom s0.sp 96 (stk - 96) (by omega),
      show 96 + (stk - 96) = stk by omega]
  have hro_f : stdoutBytesAt false x.buf x.bs = (x.buf ↦ₛ x.bs) := rfl
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 96) ∗ A.pool lim st s0 ∗ R
  have hpre_core : s0.mem ⊨
      (signalSessionIoMultiLib.withCodeLoadedWhere keep mpl cliIoWriteStdoutSpec).pre
        (false, x.buf, x.bs) s0 ∗ R' := by
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoWriteStdoutSpec, R']
    rw [hro_f, sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoadedWhere keep mpl s0.mem⌝,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlt63, hva_or⟩, ?_⟩
    rw [hstk_split] at hmem
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine hcore.mono_outcome (false, x.buf, x.bs) R' s0 hpc hrun hpre_core hsp0 ?_
  intro sf hout
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoWriteStdoutSpec, R'] at hpost
    rw [hro_f, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_f, hfs_f, htr_f, hsys_f⟩, hmem_f⟩
    have hvm : VmPreserved s0 sf := vmPreserved_of_syscallPreserved_fs hsys_f hfs_f
    have hpool_eq : A.pool lim (M.stepEvents [] st) sf = A.pool lim st s0 :=
      A.pool_transport lim st s0 sf hvm
    have hfiles : sf.fs.files = s0.fs.files := by rw [hfs_f]
    have hpref : s0.trace <+: sf.trace := ⟨TraceEvent.ofBytes .stdout x.bs, htr_f.symm⟩
    have hstream :
        ProcessOutcome.traceStreamBytes .stdout sf.trace =
          ProcessOutcome.traceStreamBytes .stdout s0.trace ++ x.bs := by
      rw [htr_f, traceStreamBytes_append, (traceStreamBytes_ofBytes_stdout x.bs).1]
    have hmem_stk : sf.mem ⊨ ((x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents [] st) sf) ∗ R := by
      have h1 : sf.mem ⊨
          ((x.buf ↦ₛ x.bs) ∗
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 96) ∗ stackAt s0.sp 96) ∗
            A.pool lim st s0) ∗ R :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem_f
      rw [← hstk_split, ← hpool_eq] at h1
      exact h1
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, writeStdoutSpecPlacedSat,
      withVmPreserved, writeStdoutHonestCore]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    refine Satisfies.mono
      (sepConj_mono_left (Entails.sepExists_right ([] : List AllocEvent) ?_)) hmem_stk
    exact Entails.pure_right
      ⟨writeStdoutEnv_nil, hx0_f, hfiles, hpref, hstream, htr_f, hfs_f⟩
      (Entails.refl _)
  · dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoWriteStdoutSpec] at hp
    exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoWriteStdoutSpec] at he
    exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [MultiPlacedLib.withCodeLoadedWhere, cliIoWriteStdoutSpec] at hoom
    exact False.elim (not_satisfies_false_sepConj hoom)

/-- `withCodeLoaded` variant of `cliIoWriteStdout_honest_withCodeLoadedWhere_ok`. -/
theorem cliIoWriteStdout_honest_withCodeLoaded_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hext2 : CliIoBlockNoExtern mpl P 2)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteStdout32Spec)
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteStdoutSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (writeStdoutSpecPlacedSat A lim stk)) :=
  subroutine_ok_withCodeLoaded_of_where
    (cliIoWriteStdout_honest_withCodeLoadedWhere_ok S lim rfl hpl hext2 hwrite hEnf)

/-- Direct `subroutine_ok` discharge of `IoHonestSpecs.writeStdoutSpecPlacedSat A lim stk` for any
    program `P` whose `P.CodeLoaded` implies block `2` of `signalSessionIoMultiLib` is loaded. -/
theorem cliIoWriteStdout_honest_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {keep : Nat → Bool} (hk2 : keep 2 = true)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoadedWhere keep mpl m)
    (hext2 : CliIoBlockNoExtern mpl P 2)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteStdout32Spec)
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteStdoutSym)
      (writeStdoutSpecPlacedSat A lim stk) :=
  subroutine_ok_strip_withCodeLoadedWhere hCode
    (cliIoWriteStdout_honest_withCodeLoadedWhere_ok S lim hk2 hpl hext2 hwrite hEnf)

/-- Alias for `cliIoWriteStdout_honest_ok`. -/
abbrev cliIoWriteStdout_budget_ok := @cliIoWriteStdout_honest_ok

/-! ## 3. Concrete Allocator-Budget Instantiations (`mallocng`, `mallocngHook`, `fineHook`) -/

/-- Concrete `mallocngRustCliAllocBudget` instantiation of `writeStdoutSpecPlacedSat`. -/
theorem cliIoWriteStdout_mallocng_honest_ok
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mplAlloc : MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits)
    {keep : Nat → Bool} (hk2 : keep 2 = true)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoadedWhere keep mpl m)
    (hext2 : CliIoBlockNoExtern mpl P 2)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteStdout32Spec)
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteStdoutSym)
      (writeStdoutSpecPlacedSat (mallocngRustCliAllocBudget M I hS γ mplAlloc tp brkStart) lim stk) :=
  cliIoWriteStdout_honest_ok (mallocngPoolErrnoSplit hS γ mplAlloc tp brkStart)
    lim hk2 hpl hCode hext2 hwrite hEnf

/-- Concrete `mallocngHookRustCliAllocBudget` instantiation of `writeStdoutSpecPlacedSat`. -/
theorem cliIoWriteStdout_mallocngHook_honest_ok
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mplAlloc : MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits)
    {keep : Nat → Bool} (hk2 : keep 2 = true)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoadedWhere keep mpl m)
    (hext2 : CliIoBlockNoExtern mpl P 2)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteStdout32Spec)
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteStdoutSym)
      (writeStdoutSpecPlacedSat
        (mallocngHookRustCliAllocBudget M I hS γ mplAlloc tp brkStart) lim stk) :=
  cliIoWriteStdout_honest_ok (mallocngHookPoolErrnoSplit hS γ mplAlloc tp brkStart)
    lim hk2 hpl hCode hext2 hwrite hEnf

/-- Concrete `fineHookRustCliAllocBudget` instantiation of `writeStdoutSpecPlacedSat`. -/
theorem cliIoWriteStdout_fineHook_honest_ok
    (γ : GhostName) (mplAlloc : MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits)
    {keep : Nat → Bool} (hk2 : keep 2 = true)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stk : Nat}
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoadedWhere keep mpl m)
    (hext2 : CliIoBlockNoExtern mpl P 2)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteStdout32Spec)
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteStdoutSym)
      (writeStdoutSpecPlacedSat (fineHookRustCliAllocBudget γ mplAlloc tp brkStart) lim stk) :=
  cliIoWriteStdout_honest_ok (fineHookPoolErrnoSplit γ mplAlloc tp brkStart)
    lim hk2 hpl hCode hext2 hwrite hEnf

end LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutProof

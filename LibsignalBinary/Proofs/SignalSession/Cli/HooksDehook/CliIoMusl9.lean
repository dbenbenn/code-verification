/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose -- proof-setup: allow-public-import
public import VerifiedLibraries.Musl.Proofs.SyscallProof
public import VerifiedLibraries.RustStd.Proofs.StdoutRaw
import Arm64.Trusted.Spec.SepLogic
import ProofLib
meta import ProofLib -- shake: keep
meta import VerifiedLibraries.Musl.Proofs.SyscallProof -- shake: keep

/-!
# Placement-Generic 9-Block `musl` Syscall Sub-Library Discharges

**Checked by Lean.**

Lifts the `musl` syscall wrapper contracts needed by `libsignal_cli_io` (`__errno_location`,
`close`, `write` to `stdout`, clamped `write` to `.localFile`, and `open` with
`O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC`) from the 9 linked blocks (`0..8`) of
`muslSysPlacedLib`, requiring only `muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9))`
instead of all 11 blocks (blocks `9..10` `fstat` / `fstatat` are unlinked on the CLI ELF).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoMusl9

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open VerifiedLibraries.Musl (
  MuslSysPlacement muslSysPlacedLib muslSysMpl
  muslBlk00_errno_location muslBlk01_syscall_ret muslBlk02_sccp
  muslBlk03_syscall_cp muslBlk04_aio_close muslBlk05_close
  muslBlk06_read muslBlk07_write muslBlk08_open
  muslSysLib00 muslSysPl00 muslSysPC00
  muslSysLib01 muslSysPl01 muslSysPC01
  muslSysLib02 muslSysPl02 muslSysPC02
  muslSysLib03 muslSysPl03 muslSysPC03
  muslSysLib04 muslSysPl04 muslSysPC04
  muslSysLib05 muslSysPl05 muslSysPC05
  muslSysLib07 muslSysPl07 muslSysPC07
  muslSysLib08 muslSysPl08 muslSysPC08
  muslSysPC02_svc muslSysPC08_svc
  ValidCPath ValidRelCPath
  placed_program_rebase_self FsState.setFd_self
  sxtw64_truncate32 ofNat64_toNat_of_lt63 ofNat64_le_maxSyscallOk
  CodeLoadedAt seq_codeLoaded_lr
  step_str64_perm_c step_stp64_perm step_str32_perm step_stp32_64_perm
  OpenatOutcome OpenatExecSpec
  muslErrnoLocationSpec muslWriteFile32ClampedSpec
  muslOpenNoCreatCloexecExecSpec muslOpenCreatCloexecExecSpec muslOpenCreateTruncSpec
)
open VerifiedLibraries.RustStd (stdoutBytesAt)
open VerifiedLibraries.RustStd.Io (muslWriteStdout32Spec)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  muslClose48LocalSpec resolve_syscall_cp step_svc_close_fd_local
)

section Musl9Priv

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

private theorem stdoutBytesAt_append_eq (ro : Bool) (a : BitVec 64) (xs ys : List (BitVec 8)) :
    stdoutBytesAt ro a (xs ++ ys) =
      (stdoutBytesAt ro a xs ∗ stdoutBytesAt ro (a + BitVec.ofNat 64 xs.length) ys) := by
  cases ro
  · exact pointsToBytes_append a xs ys
  · exact pointsToBytesRO_append a xs ys

private theorem stdoutBytesAt_take_drop_eq (ro : Bool) (a : BitVec 64) (n : Nat)
    (bs : List (BitVec 8)) (hn : n ≤ bs.length) :
    stdoutBytesAt ro a bs =
      (stdoutBytesAt ro a (bs.take n) ∗ stdoutBytesAt ro (a + BitVec.ofNat 64 n) (bs.drop n)) := by
  conv => lhs; rw [← List.take_append_drop n bs]
  rw [stdoutBytesAt_append_eq, List.length_take_of_le hn]

private def cliIoMusl9Idx : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8]

private def cliIoMusl9Lib : MultiPlacedLib where
  name := "musl_sys_9"
  blocks := [
    muslBlk00_errno_location, muslBlk01_syscall_ret, muslBlk02_sccp,
    muslBlk03_syscall_cp, muslBlk04_aio_close, muslBlk05_close,
    muslBlk06_read, muslBlk07_write, muslBlk08_open]
  data := []
  exports := [
    "___errno_location", "__errno_location", "__syscall_ret",
    "__syscall_cp", "__aio_close", "close", "read", "write", "open"]

private theorem cliIoMusl9_embedsAt :
    cliIoMusl9Lib.embedsAt muslSysPlacedLib cliIoMusl9Idx = true := by decide

private abbrev subMpl [MuslSysPlacement] : MultiPlacement :=
  MuslSysPlacement.mpl.subPlacement muslSysPlacedLib cliIoMusl9Idx

private theorem cliIoMusl9Idx_getD (k : Nat) (hk : k < 9) :
    cliIoMusl9Idx.getD k 0 = k := by
  revert k hk; decide

private theorem sub_blockProgram_eq [MuslSysPlacement] (k : Nat) (hk : k < 9 := by decide) :
    cliIoMusl9Lib.blockProgram subMpl k =
      muslSysPlacedLib.blockProgram MuslSysPlacement.mpl k := by
  have hk' : k < cliIoMusl9Lib.blocks.length := by simpa [cliIoMusl9Lib] using hk
  rw [cliIoMusl9Lib.blockProgram_subPlacement cliIoMusl9_embedsAt MuslSysPlacement.placeable hk',
    cliIoMusl9Idx_getD k hk]

private theorem sub_codeLoaded_of_where9 [MuslSysPlacement] {m : Memory}
    (hw : muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) MuslSysPlacement.mpl m) :
    cliIoMusl9Lib.CodeLoaded subMpl m := by
  intro k hk
  have hk9 : k < 9 := by simpa [cliIoMusl9Lib] using hk
  rw [sub_blockProgram_eq k hk9]
  exact hw k (by simpa [muslSysPlacedLib] using Nat.lt_trans hk9 (by decide)) (decide_eq_true hk9)

private theorem condHI_adds_4096_false {a : BitVec 64} (ha : a.toNat ≤ 2 ^ 64 - 4096) :
    ConditionHolds .HI (addsPState64 a 4096#64) = false := by
  rw [conditionHolds_hi_addsPState64]
  by_cases heq : a = -4096#64
  · subst heq; decide
  · have hlt_strict : a.toNat < 2 ^ 64 - 4096 := by
      refine Nat.lt_of_le_of_ne ha fun h => heq (BitVec.eq_of_toNat_eq ?_)
      have : (-4096#64 : BitVec 64).toNat = 2 ^ 64 - 4096 := by decide
      omega
    have hadd : (a + 4096#64).toNat = a.toNat + 4096 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : 4096 % 2 ^ 64 = 4096 := by decide
      rw [this, Nat.mod_eq_of_lt (by omega)]
    have hult : BitVec.ult (a + 4096#64) a = false := by
      simp only [BitVec.ult, hadd, decide_eq_false_iff_not]; omega
    rw [hult, Bool.false_and]

private theorem condHI_adds_4096_true {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ConditionHolds .HI (addsPState64 (-BitVec.ofNat 64 err) 4096#64) = true := by
  rw [conditionHolds_hi_addsPState64]
  have herr_mod : err % 2 ^ 64 = err := Nat.mod_eq_of_lt (by omega)
  have h4096_mod : 4096 % 2 ^ 64 = 4096 := by decide
  have hneg : (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
    rw [BitVec.toNat_neg, BitVec.toNat_ofNat, herr_mod, Nat.mod_eq_of_lt (by omega)]
  have hsum : (-BitVec.ofNat 64 err + 4096#64).toNat = 4096 - err := by
    rw [BitVec.toNat_add, hneg, BitVec.toNat_ofNat, h4096_mod]
    have : 2 ^ 64 - err + 4096 = 2 ^ 64 + (4096 - err) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hult : BitVec.ult (-BitVec.ofNat 64 err + 4096#64) (-BitVec.ofNat 64 err) = true := by
    simp only [BitVec.ult, hneg, hsum, decide_eq_true_eq]; omega
  have hne : (-BitVec.ofNat 64 err + 4096#64 != 0#64) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro heq
    have := congrArg BitVec.toNat heq
    simp only [hsum, BitVec.toNat_ofNat] at this
    omega
  rw [hult, hne]; rfl

private theorem neg_truncate32_neg_ofNat (err : Nat) :
    0#32 - (-BitVec.ofNat 64 err).truncate 32 = BitVec.ofNat 32 err := by bv_omega

private def subSyscallRetOkSpec : Spec (BitVec 64) where
  pre := fun retVal s0 =>
    ⌜s0.readReg64 .x0 = retVal ∧ retVal.toNat ≤ 2 ^ 64 - 4096⌝ ∗ stackAt s0.sp 32
  post := fun retVal s0 sf =>
    ⌜sf.readReg64 .x0 = retVal ∧ StdStatePreserved s0 sf⌝ ∗ stackAt s0.sp 32
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private def subSyscallRetErrSpec : Spec (Nat × BitVec 32) where
  pre := fun (err, e0) s0 =>
    ⌜s0.readReg64 .x0 = -BitVec.ofNat 64 err ∧ 1 ≤ err ∧ err ≤ 4095⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (err, _) s0 sf =>
    ⌜sf.readReg64 .x0 = -1#64 ∧ StdStatePreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ BitVec.ofNat 32 err))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private def subAioCloseSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = s0.readReg64 .x0 ∧ sf.mem = s0.mem ∧ StdStatePreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem sub_errnoLocation3_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 0)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "___errno_location")
      (cliIoMusl9Lib.withCodeLoaded subMpl muslErrnoLocationSpec) := by
  rw [sub_blockProgram_eq 0, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 0 =
    muslSysPC00.rebase muslSysPl00.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib00 muslSysPl00).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "___errno_location" = muslSysPl00.base := by
    have hl : Obj.lookupBlockSym "___errno_location" muslSysPlacedLib.blocks = some (0, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl00, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry; wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm],
    by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp [wp_norm, arm64_norm, muslErrnoAddr], rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩

private theorem sub_errnoLocation2_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 0)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "__errno_location")
      (cliIoMusl9Lib.withCodeLoaded subMpl muslErrnoLocationSpec) := by
  have heq : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "__errno_location" =
      muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "___errno_location" := by
    have hl2 : Obj.lookupBlockSym "__errno_location" muslSysPlacedLib.blocks = some (0, 0) := by decide
    have hl3 : Obj.lookupBlockSym "___errno_location" muslSysPlacedLib.blocks = some (0, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl2, hl3]
  rw [heq]
  exact sub_errnoLocation3_blk_ok

private theorem sub_aioClose_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 4)
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__aio_close")
      (cliIoMusl9Lib.withCodeLoaded subMpl subAioCloseSpec) := by
  rw [sub_blockProgram_eq 4, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 4 =
    muslSysPC04.rebase muslSysPl04.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib04 muslSysPl04).symm]
  have hentry : muslSysPlacedLib.resolve MuslSysPlacement.mpl "__aio_close" = muslSysPl04.base := by
    have hl : Obj.lookupBlockSym "__aio_close" muslSysPlacedLib.blocks = some (4, 0) := by decide
    simp [Obj.MultiPlacedLib.resolve, hl, muslSysPl04, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry; wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm],
    by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    by simpa using hmem⟩

private theorem sub_syscallRetOk_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 1)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "__syscall_ret")
      (cliIoMusl9Lib.withCodeLoaded subMpl subSyscallRetOkSpec) := by
  rw [sub_blockProgram_eq 1, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 1 =
    muslSysPC01.rebase muslSysPl01.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib01 muslSysPl01).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "__syscall_ret" = muslSysPl01.base := by
    have hl : Obj.lookupBlockSym "__syscall_ret" muslSysPlacedLib.blocks = some (1, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl01, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepConj_assoc]; repeat (apply SepWP.exists_left; intro)
  wp_stp64_perm hm1; wp_sym_steps 2; wp_str64_perm hm2; wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = false := condHI_adds_4096_false ‹_›
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]; wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp_all [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp only [wp_norm, arm64_norm, hm2, hm1]⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [wp_norm, arm64_norm]

private theorem sub_syscallRetErr_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 1)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "__syscall_ret")
      (cliIoMusl9Lib.withCodeLoaded subMpl subSyscallRetErrSpec) := by
  rw [sub_blockProgram_eq 1, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 1 =
    muslSysPC01.rebase muslSysPl01.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib01 muslSysPl01).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "__syscall_ret" = muslSysPl01.base := by
    have hl : Obj.lookupBlockSym "__syscall_ret" muslSysPlacedLib.blocks = some (1, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl01, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  wp_stp64_perm hm1; wp_sym_steps 2; wp_str64_perm hm2; wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = true := condHI_adds_4096_true ‹_› ‹_›
  simp only [hcond, ↓reduceIte]; wp_sym_steps
  wp_call_block sub_errnoLocation3_blk_ok ()
  rcases ‹StdStatePreserved _ sf› with ⟨hbrk_sf, hfs_sf, htpidr_sf, htr_sf, hoidx_sf, horacle_sf, hphys_sf, _⟩
  simp only [wp_norm, arm64_norm] at hbrk_sf hfs_sf htpidr_sf htr_sf hoidx_sf horacle_sf hphys_sf
  simp only [muslErrnoAddr] at *; wp_sym_steps 3
  wp_str32_perm hm3; wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, ‹sf.status = .Running›])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hbrk_sf.symm],
      by simp [wp_norm, arm64_norm, hfs_sf.symm], by simp [wp_norm, arm64_norm, htpidr_sf.symm],
      by simp [wp_norm, arm64_norm, htr_sf.symm], by simp [wp_norm, arm64_norm, hoidx_sf.symm],
      by simp [wp_norm, arm64_norm, horacle_sf.symm], by simp [wp_norm, arm64_norm, hphys_sf.symm],
      fun _ => by simp only [wp_norm, arm64_norm, hm3, ‹sf.mem = _›, hm2, hm1]⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm, htpidr_sf.symm, neg_truncate32_neg_ofNat]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem sub_syscallCp_step [MuslSysPlacement] {s0 : State} {target_pc : BitVec 64}
    {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s0.pc = muslSysPl03.base) (hrun : s0.status = .Running)
    (hcl : cliIoMusl9Lib.CodeLoaded subMpl s0.mem)
    (hnext : SepWP (muslSysPC02.rebase muslSysPl02.base (fun _ => none)) target_pc
      ((((((((s0.writeReg64 .x8 (s0.readReg64 .x0)).writeReg64 .x0 (s0.readReg64 .x1)).writeReg64
        .x1 (s0.readReg64 .x2)).writeReg64 .x2 (s0.readReg64 .x3)).writeReg64
        .x3 (s0.readReg64 .x4)).writeReg64 .x4 (s0.readReg64 .x5)).writeReg64
        .x5 (s0.readReg64 .x6)).setPC (muslSysPl02.base + 28#64)) P post) :
    SepWP (muslSysPC03.rebase muslSysPl03.base (fun _ => none)) target_pc s0 P post := by
  wp_sym_steps
  have hsccp : muslSysPl03.base + (muslSysPl03.ρ "sccp" - muslSysPl03.base) = muslSysPl02.base := by
    have hadd : muslSysPl03.base + (muslSysPl03.ρ "sccp" - muslSysPl03.base) = muslSysPl03.ρ "sccp" := by bv_omega
    have hl : Obj.lookupBlockSym "sccp" muslSysPlacedLib.blocks = some (2, 0) := by decide
    rw [hadd]
    simp [muslSysPl03, muslSysPl02, Obj.MultiPlacedLib.blockPlacement, Obj.MultiPlacedLib.resolve, hl]
  rw [hsccp]
  have hcl2 : (muslSysPC02.rebase muslSysPl02.base (fun _ => none)).CodeLoaded s0.mem := by
    have h2 := hcl 2 (by decide)
    rw [sub_blockProgram_eq 2, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 2 =
      muslSysPC02.rebase muslSysPl02.base (fun _ => none) from
      (placed_program_rebase_self muslSysLib02 muslSysPl02).symm] at h2
    exact h2
  refine SepWP.of_sameHooks (P := muslSysPC03.rebase muslSysPl03.base (fun _ => none))
    (Q := muslSysPC02.rebase muslSysPl02.base (fun _ => none))
    (by intro pc
        change ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 2).rebase muslSysPl02.base (fun _ => none)).externAt? pc =
          ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 3).rebase muslSysPl03.base (fun _ => none)).externAt? pc
        simp)
    rfl hcl2 ?_
  wp_sym_steps
  simpa [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8] using hnext

/-! ## `close` (`muslClose48LocalSpec`) -/

private def subSccpCloseLocalSpec : Spec (BitVec 64 × FdEntry) where
  pre := fun (fd, desc) s0 =>
    ⌜s0.readReg64 .x0 = 57#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind = .localFile ∨ desc.kind = .localDir)⌝
  post := fun (fd, _) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.fs = s0.fs.setFd fd none ∧
      sf.mem = s0.mem ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem sub_sccpCloseLocal_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 3)
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (cliIoMusl9Lib.withCodeLoaded subMpl subSccpCloseLocalSpec) := by
  rw [sub_blockProgram_eq 3, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib03 muslSysPl03).symm, resolve_syscall_cp]
  wp_entry
  refine sub_syscallCp_step hpc hrun h ?_
  refine step_svc_close_fd_local (fd := a_1) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4 h_5 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      rfl, by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem sub_close48Local_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 5)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "close")
      (cliIoMusl9Lib.withCodeLoaded subMpl muslClose48LocalSpec) := by
  rw [sub_blockProgram_eq 5, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 5 =
    muslSysPC05.rebase muslSysPl05.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib05 muslSysPl05).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "close" = muslSysPl05.base := by
    have hl : Obj.lookupBlockSym "close" muslSysPlacedLib.blocks = some (5, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl05, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 32 2 (by decide)]
  cells_unfold; simp only [sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep sub_aioClose_blk_ok ()
  rcases ‹StdStatePreserved _ _› with ⟨hfs1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at hfs1 htr1 htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block_keep sub_sccpCloseLocal_blk_ok (a_1, a_rest)
  rcases ‹SyscallPreserved _ _› with ⟨htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at htp2 hsig2 hb2 hbs2 hp2 hmp2
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block sub_syscallRetOk_blk_ok 0#64
  rcases ‹StdStatePreserved _ _› with ⟨hfs3, htr3, htp3, hsig3, hb3, hbs3, hp3, hmp3⟩
  simp only [wp_norm, arm64_norm, htp2, hsig2, hb2, hbs2, hp2, hmp2] at hfs3 htr3 htp3 hsig3 hb3 hbs3 hp3 hmp3
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
      by simp [wp_norm, arm64_norm, *], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
        stackAt_split_cells s0.sp 32 2 (by decide)]
      cells_unfold; simp only [wp_norm, arm64_norm, *]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

/-! ## `write` to `stdout` (`muslWriteStdout32Spec`) & `.localFile` (`muslWriteFile32ClampedSpec`) -/

private theorem stdoutBytesAt_canRead_read {ro : Bool} {m : Memory} {buf : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} (hlen : bs.length ≤ 2 ^ 64)
    (hm : m ⊨ stdoutBytesAt ro buf bs ∗ R) :
    m.canRead buf bs.length = true ∧ m.readBytes buf bs.length = bs := by
  cases ro
  · dsimp only [stdoutBytesAt, Bool.false_eq_true, ↓reduceIte] at hm
    have hblk := IsBlock.pointsToBytes buf bs
    exact ⟨hblk.canRead hlen hm, (hblk.read hm).2⟩
  · dsimp only [stdoutBytesAt, ↓reduceIte] at hm
    have hblk := IsBlockRO.pointsToBytesRO buf bs hlen
    exact ⟨hblk.canRead hlen hm, hblk.read hm⟩

private theorem step_svc_write_stdout_clamped {prog : Program} {target_pc : BitVec 64}
    {s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    {ro : Bool} {pc buf count : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hfd : s.readReg32 .x0 = 1#32)
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hnz : count ≠ 0#64)
    (hlen : bs.length = min count.toNat Arm64.MAX_RW_COUNT)
    (hsvc : prog.evalInst (.system false 0#16) s = execWrite s)
    (hva : buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT)
    (hnext : SepWP prog target_pc
      (((s.appendTrace (TraceEvent.ofBytes .stdout bs)).writeReg64
        .x0 (BitVec.ofNat 64 (min count.toNat Arm64.MAX_RW_COUNT))).setPC (pc + 4#64))
      (stdoutBytesAt ro buf bs ∗ F) post oom) :
    SepWP prog target_pc s (stdoutBytesAt ro buf bs ∗ F) post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm' : s.mem ⊨ stdoutBytesAt ro buf bs ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hlen64 : bs.length ≤ 2 ^ 64 := by
    rw [hlen]; exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_of_lt count.isLt)
  obtain ⟨hcr, hrd⟩ := stdoutBytesAt_canRead_read hlen64 hm'
  rw [hlen] at hcr hrd
  have hslt : (s.readReg32 .x0).slt 0#32 = false := by rw [hfd]; rfl
  have hfd64 : (s.readReg32 .x0).zeroExtend 64 = 1#64 := by rw [hfd]; rfl
  have hva_f : decide (buf.toNat + count.toNat > Arm64.USER_VA_LIMIT) = false :=
    decide_eq_false (Nat.not_lt.mpr hva)
  have h0_f : (count == 0#64) = false := beq_false_of_ne hnz
  have hexec : execWrite s =
      (((s.appendTrace (TraceEvent.ofBytes .stdout bs)).writeReg64
        .x0 (BitVec.ofNat 64 (min count.toNat Arm64.MAX_RW_COUNT))).setPC (pc + 4#64)) := by
    have hadv : (((s.appendTrace (TraceEvent.ofBytes .stdout bs)).writeReg64
        .x0 (BitVec.ofNat 64 (min count.toNat Arm64.MAX_RW_COUNT)))).advancePC =
      (((s.appendTrace (TraceEvent.ofBytes .stdout bs)).writeReg64
        .x0 (BitVec.ofNat 64 (min count.toNat Arm64.MAX_RW_COUNT)))).setPC (pc + 4#64) := by
      have hpc' : (((s.appendTrace (TraceEvent.ofBytes .stdout bs)).writeReg64
          .x0 (BitVec.ofNat 64 (min count.toNat Arm64.MAX_RW_COUNT)))).pc = pc := by
        simpa [State.appendTrace, arm64_norm] using hpc
      cases hst : ((s.appendTrace (TraceEvent.ofBytes .stdout bs)).writeReg64
        .x0 (BitVec.ofNat 64 (min count.toNat Arm64.MAX_RW_COUNT)))
      rw [hst] at hpc'; subst hpc'; rfl
    refine Eq.trans ?_ hadv
    dsimp only [execWrite]
    rw [hslt, hfd64, hbuf, hcnt]
    simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte,
      hva_f, h0_f, hcr, hrd, Bool.false_eq_true, OutputStream.ofFd]
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec]
  exact SepWP.to_reaches_pc hnext (by simpa using hm)

@[reducible] private def subSccpWriteStdoutSpec : Spec (Bool × BitVec 64 × List (BitVec 8)) where
  pre := fun (ro, buf, bs) s0 =>
    ⌜s0.readReg64 .x0 = 64#64 ∧ s0.readReg32 .x1 = 1#32 ∧ s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = BitVec.ofNat 64 bs.length ∧ 0 < bs.length ∧
      bs.length < 2 ^ 63 ∧ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT⌝ ∗
    stdoutBytesAt ro buf bs
  post := fun (ro, buf, bs) s0 sf =>
    let chunk := bs.take (min bs.length Arm64.MAX_RW_COUNT)
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧ sf.fs = s0.fs ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout chunk ∧ SyscallPreserved s0 sf⌝ ∗
    stdoutBytesAt ro buf bs
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem sub_sccpWriteStdout_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 3)
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (cliIoMusl9Lib.withCodeLoaded subMpl subSccpWriteStdoutSpec) := by
  rw [sub_blockProgram_eq 3, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib03 muslSysPl03).symm, resolve_syscall_cp]
  wp_entry
  have hlen_nat : (BitVec.ofNat 64 a_rest_1.length).toNat = a_rest_1.length :=
    ofNat64_toNat_of_lt63 h_7
  have hcnt_ne0 : BitVec.ofNat 64 a_rest_1.length ≠ 0#64 := by
    intro h0
    have h0n := congrArg BitVec.toNat h0
    rw [hlen_nat] at h0n
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h0n
    omega
  let k := min a_rest_1.length Arm64.MAX_RW_COUNT
  have hk_le : k ≤ a_rest_1.length := Nat.min_le_left _ _
  have hchunk_len : (a_rest_1.take k).length = min (BitVec.ofNat 64 a_rest_1.length).toNat Arm64.MAX_RW_COUNT := by
    rw [List.length_take_of_le hk_le, hlen_nat]
  refine sub_syscallCp_step hpc hrun h ?_
  rw [stdoutBytesAt_take_drop_eq a_1 a k a_rest_1 hk_le]
  refine step_svc_write_stdout_clamped (ro := a_1) (buf := a)
    (count := BitVec.ofNat 64 a_rest_1.length) (bs := a_rest_1.take k)
    (F := stdoutBytesAt a_1 (a + BitVec.ofNat 64 k) (a_rest_1.drop k))
    rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simpa [wp_norm, arm64_norm] using h_3)
    (by simp [wp_norm, arm64_norm, h_4])
    (by simp [wp_norm, arm64_norm, h_5])
    hcnt_ne0 hchunk_len
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
    (by rw [hlen_nat]; exact h_1) ?_
  rw [← stdoutBytesAt_take_drop_eq a_1 a k a_rest_1 hk_le]
  (conv => arg 3; simp only [wp_norm, arm64_norm, hlen_nat])
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm, State.appendTrace, k], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
      by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [wp_norm, arm64_norm, State.appendTrace, calleeSavedVRegs]

private theorem sub_writeStdout32_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 7)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "write")
      (cliIoMusl9Lib.withCodeLoaded subMpl muslWriteStdout32Spec) := by
  rw [sub_blockProgram_eq 7, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 7 =
    muslSysPC07.rebase muslSysPl07.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib07 muslSysPl07).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "write" = muslSysPl07.base := by
    have hl : Obj.lookupBlockSym "write" muslSysPlacedLib.blocks = some (7, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl07, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep sub_sccpWriteStdout_blk_ok (a_1, a, a_rest_1)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗ stdoutBytesAt a_1 a a_rest_1)
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hchunk_lt63 : (a_rest_1.take (min a_rest_1.length 2147479552)).length < 2 ^ 63 := by
    have hle : (a_rest_1.take (min a_rest_1.length 2147479552)).length ≤ 2147479552 := by
      rw [List.length_take_of_le (Nat.min_le_left _ _)]
      exact Nat.min_le_right _ _
    exact Nat.lt_of_le_of_lt hle (by decide)
  have hlen_ok := ofNat64_le_maxSyscallOk hchunk_lt63
  wp_call_block sub_syscallRetOk_blk_ok (BitVec.ofNat 64 (a_rest_1.take (min a_rest_1.length 2147479552)).length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1]
    at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, Arm64.MAX_RW_COUNT, *], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm, Arm64.MAX_RW_COUNT], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private def subSccpWriteFileClampedSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, bs) s0 =>
    ⌜s0.readReg64 .x0 = 64#64 ∧ (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      3 ≤ fd.toNat ∧ fd.toNat < 2 ^ 31 ∧ s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧ count ≠ 0#64 ∧
      bs.length = min count.toNat Arm64.MAX_RW_COUNT ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE ∧
      s0.fs.fds fd = some desc ∧ desc.kind = .localFile ∧
      desc.accMode.canWrite = true ∧ desc.append = false ∧
      desc.offset + bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE⌝ ∗
    (buf ↦ₛ bs)
  post := fun (fd, buf, _, desc, bs) s0 sf =>
    let oldBytes := match s0.fs.files desc.path with | some (.file b) => b | _ => []
    let newBytes := writeFileBytes oldBytes desc.offset bs
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 bs.length ∧
      sf.fs = (s0.fs.setFile desc.path (some (.file newBytes))).setFd fd
        (some { desc with offset := desc.offset + bs.length }) ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes (OutputStream.ofFd fd) bs ∧
      SyscallPreserved s0 sf⌝ ∗
    (buf ↦ₛ bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem sub_sccpWriteFileClamped_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 3)
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (cliIoMusl9Lib.withCodeLoaded subMpl subSccpWriteFileClampedSpec) := by
  rw [sub_blockProgram_eq 3, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib03 muslSysPl03).symm, resolve_syscall_cp]
  wp_entry
  refine sub_syscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine step_svc_write_file_clamped (fd := a_1) (buf := a)
    (count := a_2) (desc := a_3) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4 h_5
    (by simp [wp_norm, arm64_norm, h_6]) (by simp [wp_norm, arm64_norm, h_7])
    h_8 h_9 h_12 h_13 h_14 h_15 h_11 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
    h_10 (by simpa [Arm64.MAX_RW_COUNT, ← h_9] using h_1)
  dsimp only; rw [sepConj_emp]; (conv => arg 3; simp only [wp_norm, arm64_norm, Arm64.MAX_RW_COUNT, ← h_9]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm, ← h_9],
      by cases a_3; cases hfl : s0.fs.files _ <;> (try cases ‹FsEntry›) <;>
           simp_all [wp_norm, arm64_norm, State.appendTrace],
      by simp [wp_norm, arm64_norm, State.appendTrace], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
      by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [wp_norm, arm64_norm, State.appendTrace, calleeSavedVRegs]

private theorem sub_writeFile32Clamped_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 7)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "write")
      (cliIoMusl9Lib.withCodeLoaded subMpl muslWriteFile32ClampedSpec) := by
  rw [sub_blockProgram_eq 7, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 7 =
    muslSysPC07.rebase muslSysPl07.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib07 muslSysPl07).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "write" = muslSysPl07.base := by
    have hl : Obj.lookupBlockSym "write" muslSysPlacedLib.blocks = some (7, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl07, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep sub_sccpWriteFileClamped_blk_ok (a_1, a, a_2, a_3, a_rest_1)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗ (a ↦ₛ a_rest_1))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hlt63 : a_rest_1.length < 2 ^ 63 := by
    have hle : a_rest_1.length ≤ Arm64.MAX_RW_COUNT := by
      rw [‹a_rest_1.length = min a_2.toNat Arm64.MAX_RW_COUNT›]
      exact Nat.min_le_right _ _
    exact Nat.lt_of_le_of_lt hle (by decide)
  have hlen_ok := ofNat64_le_maxSyscallOk hlt63
  wp_call_block sub_syscallRetOk_blk_ok (BitVec.ofNat 64 a_rest_1.length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1]
    at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], ?_,
      by simp_all [wp_norm, arm64_norm, TraceEvent.ofBytes, OutputStream.ofFd], ?_⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    · cases a_3; cases hfl : s0.fs.files _ <;> (try cases ‹FsEntry›) <;> simp_all [wp_norm, arm64_norm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

/-! ## `open` (`muslOpenCreateTruncSpec`) -/

private def subSccpOpenatExecSpec :
    Spec (BitVec 64 × String × BitVec 32 × BitVec 32 × FsState × List TraceEvent × OpenatOutcome) where
  pre := fun (cstr, path, flags, mode, fs0, tr0, out) s0 =>
    ⌜s0.readReg64 .x0 = 56#64 ∧
      s0.readReg32 .x1 = AT_FDCWD_W32 ∧
      s0.readReg64 .x2 = cstr ∧
      s0.readReg32 .x3 = flags ||| O_LARGEFILE_W32 ∧
      s0.readReg32 .x4 = mode ∧
      s0.fs = fs0 ∧
      s0.trace = tr0 ∧
      ValidCPath path ∧
      OpenatExecSpec fs0 tr0 path flags mode out⌝ ∗
    (cstr ↦ₛ cstrBytes path)
  post := fun (cstr, path, _, _, fs0, tr0, out) s0 sf =>
    match out with
    | .ok fd desc fs' traceExtra =>
      ⌜sf.readReg64 .x0 = fd ∧
        fd.toNat < 2 ^ 31 ∧
        fs'.fds fd = some desc ∧
        desc.kind = .localFile ∧
        desc.cloexec = true ∧
        sf.fs = fs' ∧
        sf.mem = s0.mem ∧
        sf.trace = tr0 ++ traceExtra ∧
        SyscallPreserved s0 sf⌝ ∗
      (cstr ↦ₛ cstrBytes path)
    | .err errPred =>
      ∃∗ errno : Nat,
        ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 errno ∧
          1 ≤ errno ∧ errno ≤ 4095 ∧ errPred errno ∧
          sf.fs = fs0 ∧
          sf.mem = s0.mem ∧
          sf.trace = tr0 ∧
          SyscallPreserved s0 sf⌝ ∗
        (cstr ↦ₛ cstrBytes path)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem sub_sccpOpenatExec_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 3)
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (cliIoMusl9Lib.withCodeLoaded subMpl subSccpOpenatExecSpec) := by
  rw [sub_blockProgram_eq 3, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib03 muslSysPl03).symm, resolve_syscall_cp]
  wp_entry
  obtain ⟨hlen_p, hval_p⟩ := h_9
  refine sub_syscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine step_svc_openat_rw (path := a) (fname := a_1) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simp [wp_norm, arm64_norm, h_4])
    hlen_p hval_p (fun hcs => ?_)
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  rw [sepConj_emp]
  have hexec := h_1 hcs (by simp [wp_norm, arm64_norm, h_7]) (by simp [wp_norm, arm64_norm, h_8])
    (by simpa [wp_norm, arm64_norm] using h_3) (by simpa [wp_norm, arm64_norm] using h_5)
    (by simpa [wp_norm, arm64_norm] using h_6)
  cases a_rest_1 with
  | ok fd desc fs' traceExtra =>
    dsimp only [OpenatExecSpec] at hexec
    rcases hexec with ⟨hfd_lt, hfds, hkind, hclo, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [subSccpOpenatExecSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], hfd_lt, hfds, hkind, hclo,
        by simp [wp_norm, arm64_norm, State.appendTrace], rfl,
        by simp [wp_norm, arm64_norm, State.appendTrace, h_8], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [wp_norm, arm64_norm, State.appendTrace, calleeSavedVRegs]
  | err errPred =>
    dsimp only [OpenatExecSpec] at hexec
    rcases hexec with ⟨errno, h1, h2, hpred, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [subSccpOpenatExecSpec]
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], h1, h2, hpred,
        by simp [wp_norm, arm64_norm, h_7], rfl,
        by simp [wp_norm, arm64_norm, h_8], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

@[local simp, local arm64_norm] private theorem muslErrnoAddr_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    muslErrnoAddr (s.writeReg64 r v) = muslErrnoAddr s := rfl
@[local simp, local arm64_norm] private theorem muslErrnoAddr_setPC (s : State) (pc : BitVec 64) :
    muslErrnoAddr (s.setPC pc) = muslErrnoAddr s := rfl
@[local simp, local arm64_norm] private theorem muslErrnoAddr_setMem (s : State) (m : Memory) :
    muslErrnoAddr (s.setMem m) = muslErrnoAddr s := rfl

private theorem getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    fd.getLsbD 31 = false := by
  rw [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow hfd

private theorem truncate32_getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd.truncate 32).getLsbD 31 = false := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, getLsbD_31_false_of_lt hfd]; decide

private theorem mask32_or_zero_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 ||| 0#64) = fd := by
  simp only [BitVec.ushiftRight_zero, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem setWidth64_setWidth32_and_mask_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.setWidth 32 fd) &&& 4294967295#64 = fd := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
  rw [h1]
  simpa [BitVec.ushiftRight_zero, BitVec.or_zero] using mask32_or_zero_of_lt31 hfd

private theorem sxtw64_eq_self_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 |||
      (if fd.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = fd := by
  rw [getLsbD_31_false_of_lt hfd]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.or_zero, BitVec.ushiftRight_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem neg_ofNat_toNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
  rw [BitVec.toNat_neg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).getLsbD 31 = true := by
  rw [BitVec.getLsbD, neg_ofNat_toNat h1 h2, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hdiv : (2 ^ 64 - err) / 2 ^ 31 = 2 ^ 33 - 1 := by omega
  rw [hdiv]; decide

private theorem truncate32_getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err).truncate 32).getLsbD 31 = true := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, getLsbD_31_neg_ofNat h1 h2]; decide

private theorem sxtw_neg_of_hi_ones {v : BitVec 64} (h : v >>> 32 = 0xffffffff#64) :
    (v >>> 0 &&& 4294967295#64 ||| 0xffffffffffffffff#64 &&& 0xffffffff00000000#64) = v := by
  bv_robdd

private theorem sxtw64_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err) >>> 0 &&& 4294967295#64 |||
      (if (-BitVec.ofNat 64 err).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = -BitVec.ofNat 64 err := by
  rw [getLsbD_31_neg_ofNat h1 h2]
  simp only [↓reduceIte]
  refine sxtw_neg_of_hi_ones (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_ushiftRight, neg_ofNat_toNat h1 h2, Nat.shiftRight_eq_div_pow]
  have hmax : (4294967295#64 : BitVec 64).toNat = 2 ^ 32 - 1 := by decide
  rw [hmax]; omega

private theorem zeroExtend64_getLsbD_6 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 6 = flags.getLsbD 6 := by simp

private theorem zeroExtend64_getLsbD_19 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 19 = flags.getLsbD 19 := by simp

private theorem or_largefile_sxtw_truncate32 (flags : BitVec 32) :
    (((flags.zeroExtend 64 ||| 131072#64) >>> 0 &&& 4294967295#64 |||
      (if (flags.zeroExtend 64 ||| 131072#64).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64).truncate 32) = flags ||| O_LARGEFILE_W32 := by
  rw [sxtw64_truncate32]
  change (flags.zeroExtend 64 ||| 0x20000#64).truncate 32 = flags ||| 0x20000#32
  bv_bits

private theorem sub_openCreatCloexecExec_blk_ok [MuslSysPlacement] :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 8)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "open")
      (cliIoMusl9Lib.withCodeLoaded subMpl muslOpenCreatCloexecExecSpec) := by
  rw [sub_blockProgram_eq 8, show muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 8 =
    muslSysPC08.rebase muslSysPl08.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib08 muslSysPl08).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "open" = muslSysPl08.base := by
    have hl : Obj.lookupBlockSym "open" muslSysPlacedLib.blocks = some (8, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl08, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 112 = stackAt (s0.sp - 80#64) 32 ∗ cells (s0.sp - 80#64) 10 from
      stackAt_split_cells s0.sp 32 10 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  wp_stp64_perm hm1; wp_sym_steps 1; wp_str64_perm hm2; wp_sym_steps 1; wp_str64_perm hm3
  (conv => arg 3; simp only [wp_norm, arm64_norm, h_3, zeroExtend64_getLsbD_6, h_4])
  wp_sym_steps 2
  wp_conv_pre => rw [pointsTo64_split32_sub s0.sp 8#64 4#64]
  wp_sym_steps 4
  wp_conv_pre => rw [← pointsTo64_split32_sub s0.sp 8#64 4#64]
  wp_stp64_perm hm4; wp_str64_perm hm5; wp_stp32_64_perm hm6
  wp_sym_steps
  have hcwd : (-100#32 : BitVec 32) = AT_FDCWD_W32 := by decide
  have hflg := or_largefile_sxtw_truncate32 a_2
  have ⟨_, _⟩ := ‹ValidCPath a›
  wp_call_block_keep sub_sccpOpenatExec_blk_ok (a_1, a, a_2, s0.readReg32 .x2, s0.fs, s0.trace, a_rest_1)
  cases a_rest_1 with
  | ok fd desc fs' traceExtra =>
    wp_conv_pre => try dsimp only [subSccpOpenatExecSpec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hx0, hfd_lt, hfds, hkind, hclo, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsvc08 : muslSysPC08.svc = Syscall.standard := rfl
    have hsxtw : (fd >>> 0 &&& 4294967295#64 |||
        (if fd.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
          0xffffffff00000000#64) = fd := sxtw64_eq_self_of_lt31 hfd_lt
    have hmask0 : (fd >>> 0 &&& 4294967295#64 ||| 0#64) = fd := mask32_or_zero_of_lt31 hfd_lt
    have hfd_ze_mask : BitVec.setWidth 64 (BitVec.setWidth 32 fd) &&& 4294967295#64 = fd :=
      setWidth64_setWidth32_and_mask_of_lt31 hfd_lt
    have hfd_ze : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
    have htbnz : fd.getLsbD 31 = false := getLsbD_31_false_of_lt hfd_lt
    have htbnz32 : (fd.truncate 32).getLsbD 31 = false := truncate32_getLsbD_31_false_of_lt hfd_lt
    wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, hmask0, htbnz, htbnz32])
    wp_sym_steps 1
    simp only [wp_norm, arm64_norm, hx0, hsxtw, hmask0, htbnz, htbnz32, Bool.false_eq_true, ↓reduceIte]
    wp_sym_steps 1
    simp only [wp_norm, arm64_norm, ‹State.readReg64 sf (Reg.gpr 19#5) = _›,
      zeroExtend64_getLsbD_19, h_5, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hdesc_eq : ({ desc with cloexec := true } : FdEntry) = desc := by
      cases desc; simp at hclo; subst hclo; rfl
    have hsetfd_eq : fs'.setFd fd (some { desc with cloexec := true }) = fs' := by
      rw [hdesc_eq]; exact FsState.setFd_self hfds
    have h1_clo : (1#64 &&& 1#64 != 0#64) = true := by decide
    wp_sym_steps
    refine step_svc_fcntl_setfd (fd := fd) (arg := 1#64) rfl
      (by simp [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hsxtw, hmask0, hfd_ze_mask, hfd_ze]) hfd_lt
      (by simp [wp_norm, arm64_norm, F_SETFD_W32]) (by simp [wp_norm, arm64_norm])
      (by simpa [wp_norm, arm64_norm, hfs1] using hfds) hkind ?_
      (by simp [wp_norm, arm64_norm, hsvc08, Reg.x8, *])
    dsimp only
    (conv => arg 3; simp only [wp_norm, arm64_norm, hfs1, h1_clo, hsetfd_eq])
    wp_sym_steps
    have hfd_ok : fd.toNat ≤ 2 ^ 64 - 4096 := by omega
    wp_cut_codeLoaded
    wp_call_block sub_syscallRetOk_blk_ok fd
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecExecSpec, muslOpenCreatCloexecExecSpec]
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp_all [wp_norm, arm64_norm],
        by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt s0.sp 112 =
            stackAt (s0.sp - 80#64) 32 ∗ cells (s0.sp - 80#64) 10 from
          stackAt_split_cells s0.sp 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]
  | err errPred =>
    wp_conv_pre => try dsimp only [subSccpOpenatExecSpec]; simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_left; intro errno
    apply SepWP.pure_elim
    rintro ⟨hx0, h1, h2, hpred, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsxtw : ((-BitVec.ofNat 64 errno) >>> 0 &&& 4294967295#64 |||
        (if (-BitVec.ofNat 64 errno).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
          0xffffffff00000000#64) = -BitVec.ofNat 64 errno := sxtw64_neg_ofNat h1 h2
    have htbnz : (-BitVec.ofNat 64 errno).getLsbD 31 = true := getLsbD_31_neg_ofNat h1 h2
    have htbnz32 : ((-BitVec.ofNat 64 errno).truncate 32).getLsbD 31 = true :=
      truncate32_getLsbD_31_neg_ofNat h1 h2
    have htp_e : muslErrnoAddr s0 = muslErrnoAddr sf := by unfold muslErrnoAddr; rw [htp1]
    wp_conv_pre => rw [htp_e]
    wp_cut_codeLoaded; wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, htbnz, htbnz32])
    wp_sym_steps 1
    simp only [wp_norm, arm64_norm, hx0, htbnz, htbnz32, ↓reduceIte]
    wp_sym_steps
    wp_call_block sub_syscallRetErr_blk_ok (errno, a_3)
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecExecSpec, muslOpenCreatCloexecExecSpec]
      try rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨h1, h2, hpred, by simp [wp_norm, arm64_norm, *],
        by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *], ?_⟩,
        ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt s0.sp 112 =
            stackAt (s0.sp - 80#64) 32 ∗ cells (s0.sp - 80#64) 10 from
          stackAt_split_cells s0.sp 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem sub_openCreateTrunc_blk_ok [MuslSysPlacement] (fd : BitVec 64 := 3#64) :
    subroutine_ok (cliIoMusl9Lib.blockProgram subMpl 8)
      (muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "open")
      (cliIoMusl9Lib.withCodeLoaded subMpl (muslOpenCreateTruncSpec fd)) := by
  refine subroutine_ok_refine_entails sub_openCreatCloexecExec_blk_ok ?_
  rintro ⟨cstr, path, e0⟩ R s0 hpre
  simp only [MultiPlacedLib.withCodeLoaded, muslOpenCreateTruncSpec, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hmode, ⟨hcp, hlead, hdot⟩, halloc, hfd_lt⟩, hm⟩
  let flags32 : BitVec 32 := 1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_CLOEXEC_W32
  have hb6 : flags32.getLsbD 6 = true := by decide
  have hb19 : flags32.getLsbD 19 = true := by decide
  have hfl_eq : flags32 ||| O_LARGEFILE_W32 =
      1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_LARGEFILE_W32 ||| O_CLOEXEC_W32 := by decide
  by_cases hcan : fsCanWriteFile s0.fs path = true
  · let desc : FdEntry :=
      { path := path, accMode := .wronly, append := false, cloexec := true, offset := 0 }
    let fs' : FsState := (s0.fs.setFile path (some (.file []))).setFd fd (some desc)
    let trExtra : List TraceEvent := [.fileChanged (normalizePath path).toPathString]
    refine ⟨(cstr, path, flags32, e0, .ok fd desc fs' trExtra), ?_, fun sf => ?_⟩
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenCreatCloexecExecSpec, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2 hs_x3
      have hexec := execOpenat_wronly_creat_trunc_cloexec hs_x0 (hfl_eq ▸ hs_x2)
        (hs_x3.symm ▸ hmode) hcs hlead hdot (hs_fs.symm ▸ halloc)
      rw [hs_fs, hcan] at hexec; simp only [↓reduceIte] at hexec
      refine ⟨hfd_lt, by simp [fs', FsState.setFd], rfl, rfl, ?_⟩
      simpa [fs', desc, trExtra] using hexec
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenCreatCloexecExecSpec,
        muslOpenNoCreatCloexecExecSpec, muslOpenCreateTruncSpec, hcan, ↓reduceIte]
      exact Entails.refl _
  · simp only [Bool.not_eq_true] at hcan
    refine ⟨(cstr, path, flags32, e0, .err (fun n => n = 2 ∨ n = 20 ∨ n = 21 ∨ n = 36)), ?_, fun sf => ?_⟩
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenCreatCloexecExecSpec, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2 hs_x3
      have hexec := execOpenat_wronly_creat_trunc_cloexec hs_x0 (hfl_eq ▸ hs_x2)
        (hs_x3.symm ▸ hmode) hcs hlead hdot (hs_fs.symm ▸ halloc)
      rw [hs_fs, hcan] at hexec; simp only [Bool.false_eq_true, ↓reduceIte] at hexec
      rcases hexec with ⟨err, herr, hexec_eq⟩
      rcases herr with rfl | rfl | rfl | rfl
      · exact ⟨2, by decide, by decide, Or.inl rfl, hexec_eq⟩
      · exact ⟨20, by decide, by decide, Or.inr (Or.inl rfl), hexec_eq⟩
      · exact ⟨21, by decide, by decide, Or.inr (Or.inr (Or.inl rfl)), hexec_eq⟩
      · exact ⟨36, by decide, by decide, Or.inr (Or.inr (Or.inr rfl)), hexec_eq⟩
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenCreatCloexecExecSpec,
        muslOpenNoCreatCloexecExecSpec, muslOpenCreateTruncSpec, hcan, Bool.false_eq_true, ↓reduceIte]
      refine Entails.sepExists_elim fun errno => Entails.sepExists_right (BitVec.ofNat 32 errno) ?_
      exact sepConj_mono_left (Entails.pure_mono fun ⟨_, _, hpred, hr0, hfs, htr, hsp⟩ =>
        ⟨hr0, by
          rcases hpred with rfl | rfl | rfl | rfl <;> decide, hfs, htr, hsp⟩)

private theorem hooksUnfetched_of_no_ext {P : Program} (hext : ∀ pc, P.externAt? pc = none) :
    ∀ m, P.CodeLoaded m → P.HooksUnfetched m :=
  fun _ _ _ pc _ he => False.elim (he (hext pc))

end Musl9Priv

/-! ## Exported `subroutine_ok` Discharges from 9-Block `CodeLoadedWhere` -/

/-- `int *___errno_location(void)` (`blk00`) on any hook-free `Syscall.standard` program loading
    blocks `0..8` of `muslSysPlacedLib`. -/
theorem muslErrnoLocation3_of_where9_ok {mpl : MultiPlacement} (hpl : muslSysPlacedLib.Placeable mpl)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hcl9 : ∀ m, P.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mpl m) :
    subroutine_ok P (muslSysPlacedLib.fnAddr mpl "___errno_location") muslErrnoLocationSpec := by
  letI : MuslSysPlacement := ⟨mpl, hpl⟩
  exact cliIoMusl9Lib.subroutine_ok_of_pureMem (j := 0) (by decide)
    sub_errnoLocation3_blk_ok (fun m hm => sub_codeLoaded_of_where9 (hcl9 m hm))
    (hooksUnfetched_of_no_ext hext) hsvc

/-- `int *__errno_location(void)` (`blk00`) on any hook-free `Syscall.standard` program loading
    blocks `0..8` of `muslSysPlacedLib`. -/
theorem muslErrnoLocation_of_where9_ok {mpl : MultiPlacement} (hpl : muslSysPlacedLib.Placeable mpl)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hcl9 : ∀ m, P.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mpl m) :
    subroutine_ok P (muslSysPlacedLib.fnAddr mpl "__errno_location") muslErrnoLocationSpec := by
  letI : MuslSysPlacement := ⟨mpl, hpl⟩
  exact cliIoMusl9Lib.subroutine_ok_of_pureMem (j := 0) (by decide)
    sub_errnoLocation2_blk_ok (fun m hm => sub_codeLoaded_of_where9 (hcl9 m hm))
    (hooksUnfetched_of_no_ext hext) hsvc

/-- `int close(int fd)` (`blk05`, `muslClose48LocalSpec`) on any hook-free `Syscall.standard`
    program loading blocks `0..8` of `muslSysPlacedLib`. -/
theorem muslClose48Local_of_where9_ok {mpl : MultiPlacement} (hpl : muslSysPlacedLib.Placeable mpl)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hcl9 : ∀ m, P.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mpl m) :
    subroutine_ok P (muslSysPlacedLib.fnAddr mpl "close") muslClose48LocalSpec := by
  letI : MuslSysPlacement := ⟨mpl, hpl⟩
  exact cliIoMusl9Lib.subroutine_ok_of_pureMem (j := 5) (by decide)
    sub_close48Local_blk_ok (fun m hm => sub_codeLoaded_of_where9 (hcl9 m hm))
    (hooksUnfetched_of_no_ext hext) hsvc

/-- `ssize_t write(1, buf, count)` (`blk07`, `muslWriteStdout32Spec`) on any hook-free
    `Syscall.standard` program loading blocks `0..8` of `muslSysPlacedLib`. -/
theorem muslWriteStdout32_of_where9_ok {mpl : MultiPlacement} (hpl : muslSysPlacedLib.Placeable mpl)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hcl9 : ∀ m, P.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mpl m) :
    subroutine_ok P (muslSysPlacedLib.fnAddr mpl "write") muslWriteStdout32Spec := by
  letI : MuslSysPlacement := ⟨mpl, hpl⟩
  exact cliIoMusl9Lib.subroutine_ok_of_pureMem (j := 7) (by decide)
    sub_writeStdout32_blk_ok (fun m hm => sub_codeLoaded_of_where9 (hcl9 m hm))
    (hooksUnfetched_of_no_ext hext) hsvc

/-- `ssize_t write(fd, buf, count)` (`blk07`, `muslWriteFile32ClampedSpec`) on any hook-free
    `Syscall.standard` program loading blocks `0..8` of `muslSysPlacedLib`. -/
theorem muslWriteFile32Clamped_of_where9_ok {mpl : MultiPlacement}
    (hpl : muslSysPlacedLib.Placeable mpl)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hcl9 : ∀ m, P.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mpl m) :
    subroutine_ok P (muslSysPlacedLib.fnAddr mpl "write") muslWriteFile32ClampedSpec := by
  letI : MuslSysPlacement := ⟨mpl, hpl⟩
  exact cliIoMusl9Lib.subroutine_ok_of_pureMem (j := 7) (by decide)
    sub_writeFile32Clamped_blk_ok (fun m hm => sub_codeLoaded_of_where9 (hcl9 m hm))
    (hooksUnfetched_of_no_ext hext) hsvc

/-- `int open(path, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, mode)` (`blk08`,
    `muslOpenCreateTruncSpec fd`) on any hook-free `Syscall.standard` program loading blocks `0..8`
    of `muslSysPlacedLib`. -/
theorem muslOpenCreateTrunc_of_where9_ok {mpl : MultiPlacement}
    (hpl : muslSysPlacedLib.Placeable mpl) (fd : BitVec 64 := 3#64)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hcl9 : ∀ m, P.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) mpl m) :
    subroutine_ok P (muslSysPlacedLib.fnAddr mpl "open") (muslOpenCreateTruncSpec fd) := by
  letI : MuslSysPlacement := ⟨mpl, hpl⟩
  exact cliIoMusl9Lib.subroutine_ok_of_pureMem (j := 8) (by decide)
    (sub_openCreateTrunc_blk_ok fd) (fun m hm => sub_codeLoaded_of_where9 (hcl9 m hm))
    (hooksUnfetched_of_no_ext hext) hsvc

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoMusl9

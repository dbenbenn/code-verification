/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Proofs.SyscallProof
meta import VerifiedLibraries.Musl.Proofs.SyscallProof -- shake: keep
public import VerifiedLibraries.RustStd.Proofs.StdoutRaw
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Placement-Generic `musl` `write(1, ...)` Contract and `USER_VA_LIMIT` Pool Helpers

1. Proves `muslWriteStdout32_block_ok` and `muslWriteStdout32_ok` on `muslSysPlacedLib` block `7`
   (`"write"`, `32`-B stack frame) against `VerifiedLibraries.RustStd.Io.muslWriteStdout32Spec`
   (`fd = 1`, `ro : Bool`, `stdoutBytesAt ro buf bs`, clamping to `MAX_RW_COUNT = 0x7fff_f000`).
2. Proves `USER_VA_LIMIT` and `stackAt` bound helpers from `PoolErrnoSplit` so `lim.enforced = true`
   together with `A.pool lim st s ∗ stdoutBytesAt ro buf bs` (`0 < bs.length`) automatically yields
   `buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CliIoFmt.MuslWrite

open Arm64 ProofLib
open Arm64.Obj (MultiPlacedLib)
open ProofLib.StdStartup (StdStatePreserved)
open VerifiedLibraries.Musl (
  MuslSysPlacement muslSysPlacedLib muslSysMpl
  muslSysPl02 muslSysPC02
  muslSysPl03 muslSysPC03
  muslSysLib07 muslSysPl07 muslSysPC07
  placed_program_rebase_self
  ofNat64_toNat_of_lt63 ofNat64_le_maxSyscallOk
  CodeLoadedAt seq_codeLoaded_lr
  step_stp64_perm
  muslSyscallRetOk_block_ok
  muslSysPC02_svc
)
open VerifiedLibraries.RustStd (
  stdoutBytesAt StdErrnoCell stdErrnoAddr
)
open CryptoVerification.SignalSession.CliExt (bytesAt)
open VerifiedLibraries.RustStd.Io (muslWriteStdout32Spec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst (PoolErrnoSplit)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  muslSyscallCp_step resolve_syscall_cp
)

/-! ## 1. `stdoutBytesAt` Splitting & Clamped `svc #0` Step for `fd = 1` -/

theorem stdoutBytesAt_append_eq (ro : Bool) (a : BitVec 64) (xs ys : List (BitVec 8)) :
    stdoutBytesAt ro a (xs ++ ys) =
      (stdoutBytesAt ro a xs ∗ stdoutBytesAt ro (a + BitVec.ofNat 64 xs.length) ys) := by
  cases ro
  · exact pointsToBytes_append a xs ys
  · exact pointsToBytesRO_append a xs ys

theorem stdoutBytesAt_take_drop_eq (ro : Bool) (a : BitVec 64) (n : Nat) (bs : List (BitVec 8))
    (hn : n ≤ bs.length) :
    stdoutBytesAt ro a bs =
      (stdoutBytesAt ro a (bs.take n) ∗ stdoutBytesAt ro (a + BitVec.ofNat 64 n) (bs.drop n)) := by
  conv => lhs; rw [← List.take_append_drop n bs]
  rw [stdoutBytesAt_append_eq, List.length_take_of_le hn]

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

private theorem state_advancePC_eq_setPC {s : State} {pc : BitVec 64} (hpc : s.pc = pc) :
    s.advancePC = s.setPC (pc + 4#64) := by
  subst hpc; rfl

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
    refine Eq.trans ?_ (state_advancePC_eq_setPC (by simpa [State.appendTrace, arm64_norm] using hpc))
    dsimp only [execWrite]
    rw [hslt, hfd64, hbuf, hcnt]
    simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte,
      hva_f, h0_f, hcr, hrd, Bool.false_eq_true, OutputStream.ofFd]
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec]
  exact SepWP.to_reaches_pc hnext (by simpa using hm)

/-! ## 2. `muslWriteStdout32_block_ok` & `muslWriteStdout32_ok` (`muslSysPlacedLib` Block `7`) -/

@[reducible] private def muslSccpWriteStdoutSpec : Spec (Bool × BitVec 64 × List (BitVec 8)) where
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

private theorem muslSccpWriteStdout_blk_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPC03.rebase muslSysPl03.base (fun _ => none))
      (muslSysPlacedLib.resolve MuslSysPlacement.mpl "__syscall_cp")
      (muslSysPlacedLib.withCodeLoaded MuslSysPlacement.mpl muslSccpWriteStdoutSpec) := by
  rw [resolve_syscall_cp]; wp_entry
  set ro := a_1
  set buf := a
  set bs := a_rest_1
  have hlen_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length :=
    ofNat64_toNat_of_lt63 h_7
  have hcnt_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 := by
    intro h0
    have h0n := congrArg BitVec.toNat h0
    rw [hlen_nat] at h0n
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h0n
    omega
  let k := min bs.length Arm64.MAX_RW_COUNT
  have hk_le : k ≤ bs.length := Nat.min_le_left _ _
  have hchunk_len : (bs.take k).length = min (BitVec.ofNat 64 bs.length).toNat Arm64.MAX_RW_COUNT := by
    rw [List.length_take_of_le hk_le, hlen_nat]
  refine muslSyscallCp_step hpc hrun h ?_
  rw [stdoutBytesAt_take_drop_eq ro buf k bs hk_le]
  refine step_svc_write_stdout_clamped (ro := ro) (buf := buf)
    (count := BitVec.ofNat 64 bs.length) (bs := bs.take k)
    (F := stdoutBytesAt ro (buf + BitVec.ofNat 64 k) (bs.drop k))
    rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simpa [wp_norm, arm64_norm] using h_3)
    (by simp [wp_norm, arm64_norm, h_4])
    (by simp [wp_norm, arm64_norm, h_5])
    hcnt_ne0 hchunk_len
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
    (by rw [hlen_nat]; exact h_1) ?_
  rw [← stdoutBytesAt_take_drop_eq ro buf k bs hk_le]
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

/-- Block-`7` proof of `musl` `write(1, buf, count)` against `muslWriteStdout32Spec`. -/
theorem muslWriteStdout32_block_ok [MuslSysPlacement] :
    subroutine_ok (muslSysPlacedLib.blockProgram muslSysMpl 7)
      (muslSysPlacedLib.fnAddr muslSysMpl "write")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslWriteStdout32Spec) := by
  rw [show muslSysPlacedLib.blockProgram muslSysMpl 7 =
    muslSysPC07.rebase muslSysPl07.base (fun _ => none) from
    (placed_program_rebase_self muslSysLib07 muslSysPl07).symm]
  have hentry : muslSysPlacedLib.fnAddr MuslSysPlacement.mpl "write" = muslSysPl07.base := by
    have hl : Obj.lookupBlockSym "write" muslSysPlacedLib.blocks = some (7, 0) := by decide
    simp [Obj.MultiPlacedLib.fnAddr, hl, muslSysPl07, Obj.MultiPlacedLib.blockPlacement]
  rw [hentry]; wp_entry
  set ro := a_1
  set buf := a
  set bs := a_rest_1
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep muslSccpWriteStdout_blk_ok (ro, buf, bs)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗ stdoutBytesAt ro buf bs)
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hchunk_lt63 : (bs.take (min bs.length 2147479552)).length < 2 ^ 63 := by
    have hle : (bs.take (min bs.length 2147479552)).length ≤ 2147479552 := by
      rw [List.length_take_of_le (Nat.min_le_left _ _)]
      exact Nat.min_le_right _ _
    exact Nat.lt_of_le_of_lt hle (by decide)
  have hlen_ok := ofNat64_le_maxSyscallOk hchunk_lt63
  wp_call_block muslSyscallRetOk_block_ok (BitVec.ofNat 64 (bs.take (min bs.length 2147479552)).length)
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

/-- Program-level proof of `musl` `write(1, buf, count)` against `muslWriteStdout32Spec`. -/
theorem muslWriteStdout32_ok [MuslSysPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "write")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslWriteStdout32Spec) :=
  muslSysPlacedLib.subroutine_ok_of_block (j := 7) (by decide) muslWriteStdout32_block_ok hext hsvc

/-! ## 3. `USER_VA_LIMIT` & Stack-Bound Helpers from `PoolErrnoSplit` -/

private theorem stdoutBytesAt_mapped_at {ro : Bool} {m : Memory} {buf : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} {k : Nat} (hk : k < bs.length)
    (hsat : m ⊨ stdoutBytesAt ro buf bs ∗ R) :
    (m.perm (buf + BitVec.ofNat 64 k)).mapped = true := by
  have hk_le : k ≤ bs.length := Nat.le_of_lt hk
  rw [stdoutBytesAt_take_drop_eq ro buf k bs hk_le] at hsat
  have h1_le : 1 ≤ (bs.drop k).length := by rw [List.length_drop]; omega
  rw [stdoutBytesAt_take_drop_eq ro (buf + BitVec.ofNat 64 k) 1 (bs.drop k) h1_le] at hsat
  have hsat1 : m ⊨ stdoutBytesAt ro (buf + BitVec.ofNat 64 k) ((bs.drop k).take 1) ∗
      (stdoutBytesAt ro (buf + BitVec.ofNat 64 k + BitVec.ofNat 64 1) ((bs.drop k).drop 1) ∗
        stdoutBytesAt ro buf (bs.take k) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsat
  have hlen1 : ((bs.drop k).take 1).length = 1 := List.length_take_of_le h1_le
  have hcr : m.canRead (buf + BitVec.ofNat 64 k) 1 = true := by
    have ⟨hcr', _⟩ := stdoutBytesAt_canRead_read (by omega) hsat1
    rwa [hlen1] at hcr'
  unfold Memory.canRead Memory.allPerm at hcr
  cases hp : m.perm (buf + BitVec.ofNat 64 k) with
  | none => simp [hp] at hcr
  | some _ => rfl

/-- Any non-empty `stdoutBytesAt ro buf bs` (`bs.length ≤ 2 ^ 64`) in a memory whose mapped bytes
    all lie below `USER_VA_LIMIT` satisfies `buf.toNat + bs.length ≤ USER_VA_LIMIT`. -/
theorem stdoutBytesAt_userVa_of_mapped {ro : Bool} {m : Memory} {buf : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp}
    (hpos : 0 < bs.length) (hle : bs.length ≤ 2 ^ 64)
    (hmapVa : ∀ a : BitVec 64, (m.perm a).mapped = true → a.toNat < Arm64.USER_VA_LIMIT)
    (hsat : m ⊨ stdoutBytesAt ro buf bs ∗ R) :
    buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT := by
  have hbuf_lt : buf.toNat < Arm64.USER_VA_LIMIT := by
    have hm0 := stdoutBytesAt_mapped_at hpos hsat
    have hadd0 : buf + BitVec.ofNat 64 0 = buf := by bv_omega
    rw [hadd0] at hm0
    exact hmapVa buf hm0
  have hLim : Arm64.USER_VA_LIMIT = 2 ^ 48 := rfl
  have hno_wrap : buf.toNat + bs.length ≤ 2 ^ 64 := by
    exact Classical.byContradiction fun hgt => by
      let k := 2 ^ 64 - 1 - buf.toNat
      have hk : k < bs.length := by omega
      have hmk := stdoutBytesAt_mapped_at hk hsat
      have hlt_k := hmapVa (buf + BitVec.ofNat 64 k) hmk
      have htoNat_k : (buf + BitVec.ofNat 64 k).toNat = 2 ^ 64 - 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show buf.toNat + k < 2 ^ 64 by omega)]
        omega
      omega
  have hlast_lt : (buf + BitVec.ofNat 64 (bs.length - 1)).toNat < Arm64.USER_VA_LIMIT :=
    hmapVa _ (stdoutBytesAt_mapped_at (by omega : bs.length - 1 < bs.length) hsat)
  have hlast_toNat : (buf + BitVec.ofNat 64 (bs.length - 1)).toNat = buf.toNat + (bs.length - 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show bs.length - 1 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show buf.toNat + (bs.length - 1) < 2 ^ 64 by omega)]
  omega

/-- `PoolErrnoSplit` discharge of `buf.toNat + bs.length ≤ USER_VA_LIMIT` for `stdoutBytesAt`. -/
theorem poolErrnoSplit_stdoutBytesAt_le_userVa
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart)
    {lim : BudgetLimits} {st : M.σ} {s : State}
    {ro : Bool} {buf : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (henf : lim.enforced = true) (hpos : 0 < bs.length) (hle : bs.length ≤ 2 ^ 64)
    (hsat : s.mem ⊨ A.pool lim st s ∗ stdoutBytesAt ro buf bs ∗ R) :
    buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT :=
  stdoutBytesAt_userVa_of_mapped hpos hle
    (fun _ hmap => S.pool_mapped_lt_userVa lim st henf hsat hmap)
    (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsat)

/-- `PoolErrnoSplit` discharge of `buf.toNat + bs.length ≤ USER_VA_LIMIT` for `bytesAt`. -/
theorem poolErrnoSplit_bytesAt_le_userVa
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart)
    {lim : BudgetLimits} {st : M.σ} {s : State}
    {ro : Bool} {buf : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (henf : lim.enforced = true) (hpos : 0 < bs.length) (hle : bs.length ≤ 2 ^ 64)
    (hsat : s.mem ⊨ A.pool lim st s ∗ bytesAt ro buf bs ∗ R) :
    buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT := by
  have heq : bytesAt ro buf bs = stdoutBytesAt ro buf bs := by cases ro <;> rfl
  rw [heq] at hsat
  exact poolErrnoSplit_stdoutBytesAt_le_userVa S henf hpos hle hsat

/-- `PoolErrnoSplit` discharge of `buf.toNat + bs.length ≤ USER_VA_LIMIT` for owned `(buf ↦ₛ bs)`
    (extracting `bs.length ≤ 2 ^ 64` directly from `IsBlock.pointsToBytes`). -/
theorem poolErrnoSplit_pointsToBytes_le_userVa
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart)
    {lim : BudgetLimits} {st : M.σ} {s : State}
    {buf : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (henf : lim.enforced = true) (hpos : 0 < bs.length)
    (hsat : s.mem ⊨ A.pool lim st s ∗ (buf ↦ₛ bs) ∗ R) :
    buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT := by
  have hsat_bs : s.mem ⊨ (buf ↦ₛ bs) ∗ (A.pool lim st s ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsat
  have hle : bs.length ≤ 2 ^ 64 := ((IsBlock.pointsToBytes buf bs).read hsat_bs).1
  exact poolErrnoSplit_stdoutBytesAt_le_userVa (ro := false) S henf hpos hle hsat

/-- `PoolErrnoSplit` discharge of `stk ≤ 2 ^ 64` from `stackAt s.sp stk ∗ A.pool lim st s`
    via disjointness against the `4`-byte `StdErrnoCell` owned by `A.pool`. -/
theorem poolErrnoSplit_stackAt_le_two_pow_64
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart)
    {lim : BudgetLimits} {st : M.σ} {s : State} {stk : Nat} {R : SepProp}
    (hstk : 0 < stk)
    (hsat : s.mem ⊨ stackAt s.sp stk ∗ A.pool lim st s ∗ R) :
    stk ≤ 2 ^ 64 := by
  have herr_mem : StdErrnoCell s.tpidrEl0 ⊢ memRegion (stdErrnoAddr s.tpidrEl0) 4 := by
    unfold StdErrnoCell
    refine Entails.sepExists_elim fun v => ?_
    exact (IsBlock.pointsTo32 (stdErrnoAddr s.tpidrEl0) v).entails_memRegion
  have hsat_split : s.mem ⊨ A.pool lim st s ∗ (stackAt s.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsat
  have hsat_err : s.mem ⊨
      (⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
        S.core lim st s ∗ memRegion (stdErrnoAddr s.tpidrEl0) 4) ∗
        (stackAt s.sp stk ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left
        (Entails.trans (S.pool_split lim st s)
          (sepConj_mono_right (sepConj_mono_right herr_mem))))
      hsat_split
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsat_err
  have hsat_disj : s.mem ⊨ memRegion (stdErrnoAddr s.tpidrEl0) 4 ∗
      (stackAt s.sp stk ∗ (S.core lim st s ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsat_err.2
  have hdisj := (IsBlock.memRegion (stdErrnoAddr s.tpidrEl0) 4).disjoint
    (IsBlock.memRegion (s.sp - BitVec.ofNat 64 stk) stk) (by decide) hstk hsat_disj
  have hlt := (stdErrnoAddr s.tpidrEl0 - (s.sp - BitVec.ofNat 64 stk)).isLt
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

end LibsignalBinary.Proofs.HookDischarge.CliIoFmt.MuslWrite

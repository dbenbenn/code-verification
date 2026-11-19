/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.Process.FsLemmas
public import VerifiedLibraries.Musl.Proofs.SyscallProof
public import VerifiedLibraries.RustStd.Spec.IoCommon
public import VerifiedLibraries.RustStd.Proofs.CoreIo
public import LibsignalBinary.Proofs.SignalSession.CliIo.Sym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileOpenSteps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
meta import ProofLib.ProgramReflection

/-!
# `write_file` Chunked `write` Loop and `close` + Return Path

Proves the `0x7ffff000`-clamped `write` loop (`+0x0ac .. +0x104`) and `close` + epilogue
(`+0x104 .. +0x12c`) for `signalSessionIoMultiLib` block `1` (`libsignal_cli_io::write_file`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileLoop

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.Musl (muslWriteFile32ClampedSpec)
open VerifiedLibraries.RustStd (
  StdErrnoCell cPathOf
)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  sepWP_seg_cliIo_block_pure
  cliIoWriteSym cliIoCloseSym
  cliIoBlockNoSvc0_01
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  bit63_eq_zero_of_lt bv64_beq_ofNat_false bv64_sub_ofNat
  bv64_ult_ofNat_true bv64_ult_ofNat_false
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (muslClose48LocalSpec)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileOpenSteps (
  cliIoPl01 cliIoPC01
  cliIo1_lt cliIoWriteFile_write_pc cliIoWriteFile_close_pc
  syscallPreserved_trans syscallPreserved_of_seg
  cliIoSavedRegs10 cliIoWriteFile_ret_epilogue
  getLsbD_31_of_fd_lt readReg32_zeroExtend_of_truncate
)

/-! ## 1. Chunked `writeFileBytes`, `TraceEvent.ofBytes`, `FsState`, and Slice-Split Lemmas -/

/-- Bytes requested per `write` iteration in `write_file`: `min (total - written) MAX_RW_COUNT`. -/
@[expose] def writeChunkBytes (total written : Nat) : Nat :=
  min (total - written) Arm64.MAX_RW_COUNT

theorem writeChunkBytes_pos {total written : Nat} (hlt : written < total) :
    0 < writeChunkBytes total written := by
  have hmax : 0 < Arm64.MAX_RW_COUNT := by decide
  unfold writeChunkBytes
  omega

theorem writeChunkBytes_le_max (total written : Nat) :
    writeChunkBytes total written ≤ Arm64.MAX_RW_COUNT :=
  Nat.min_le_right _ _

theorem writeChunkBytes_le_sub (total written : Nat) :
    writeChunkBytes total written ≤ total - written :=
  Nat.min_le_left _ _

theorem writeChunkBytes_lt_pow63 (total written : Nat) :
    writeChunkBytes total written < 2 ^ 63 :=
  Nat.lt_of_le_of_lt (writeChunkBytes_le_max total written) (by decide)

theorem writeChunkBytes_lt_pow64 (total written : Nat) :
    writeChunkBytes total written < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (writeChunkBytes_le_max total written) (by decide)

theorem writeChunkBytes_csel_bv {total written : Nat} (_hle : written ≤ total)
    (htot : total < 2 ^ 64) :
    (if (BitVec.ofNat 64 (total - written)).ult 0x7ffff000#64 = true
     then BitVec.ofNat 64 (total - written)
     else 0x7ffff000#64) = BitVec.ofNat 64 (writeChunkBytes total written) := by
  have hsub_lt : total - written < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) htot
  have hmax_eq : (0x7ffff000#64 : BitVec 64) = BitVec.ofNat 64 Arm64.MAX_RW_COUNT := rfl
  have hmax_lt : Arm64.MAX_RW_COUNT < 2 ^ 64 := by decide
  rw [hmax_eq]
  unfold writeChunkBytes
  by_cases hlt : total - written < Arm64.MAX_RW_COUNT
  · rw [bv64_ult_ofNat_true hlt hmax_lt]
    simp [Nat.min_eq_left (Nat.le_of_lt hlt)]
  · rw [bv64_ult_ofNat_false (by omega : Arm64.MAX_RW_COUNT ≤ total - written) hsub_lt]
    simp [Nat.min_eq_right (by omega : Arm64.MAX_RW_COUNT ≤ total - written)]

theorem take_append_drop_take {α : Type} :
    ∀ (bs : List α) (i j : Nat), bs.take i ++ (bs.drop i).take j = bs.take (i + j)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: bs, i + 1, j => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
      Nat.succ_add, List.cons.injEq, true_and]
    exact take_append_drop_take bs i j

theorem writeFileBytes_take_step (bs : List (BitVec 8)) {written want : Nat}
    (hle : written ≤ bs.length) (_hwant : want ≤ bs.length - written) :
    writeFileBytes (bs.take written) written ((bs.drop written).take want) =
      bs.take (written + want) := by
  have hlen_pre : (bs.take written).length = written := List.length_take_of_le hle
  have htake_self : (bs.take written).take written = bs.take written := by
    rw [List.take_take, Nat.min_self]
  have hdrop_nil :
      (bs.take written).drop (written + ((bs.drop written).take want).length) = [] := by
    apply List.drop_eq_nil_of_le
    rw [hlen_pre]
    omega
  unfold writeFileBytes
  simp only [hlen_pre, Nat.le_refl, ↓reduceIte, htake_self, hdrop_nil, List.append_nil]
  exact take_append_drop_take bs written want

theorem ofBytes_take_step (out : OutputStream) (bs : List (BitVec 8)) (written want : Nat) :
    TraceEvent.ofBytes out (bs.take written) ++
      TraceEvent.ofBytes out ((bs.drop written).take want) =
    TraceEvent.ofBytes out (bs.take (written + want)) := by
  simp only [TraceEvent.ofBytes, ← List.map_append, take_append_drop_take]

theorem normalizePath_isEmpty_false_of_fsCanWriteFile {fs : FsState} {path : String}
    (h : fsCanWriteFile fs path = true) :
    (normalizePath path).isEmpty = false := by
  unfold fsCanWriteFile at h
  simp only [Bool.and_eq_true] at h
  have h2 := h.2
  cases hemp : (normalizePath path).isEmpty with
  | false => rfl
  | true =>
    simp [FsState.files, FsState.getEntry, hemp] at h2
    exact absurd h2 (by decide)

theorem files_setFile_same_of_isEmpty_false (fs : FsState) {path : String}
    (hemp : (normalizePath path).isEmpty = false) (e : Option FsEntry) :
    (fs.setFile path e).files path = e := by
  simp [FsState.files, FsState.setFile, FsState.getEntry, FsState.setEntry, hemp]

@[simp]
theorem setFd_setFd_same (fs : FsState) (fd : BitVec 64) (d1 d2 : Option FdEntry) :
    (fs.setFd fd d1).setFd fd d2 = fs.setFd fd d2 := by
  cases fs
  simp only [FsState.setFd, FsState.mk.injEq, true_and]
  funext k
  by_cases hk : (k == fd) = true <;> simp [hk]

@[simp]
theorem fds_setFd_same (fs : FsState) (fd : BitVec 64) (d : Option FdEntry) :
    (fs.setFd fd d).fds fd = d := by
  cases fs
  simp [FsState.setFd]

@[simp]
theorem fds_setFile (fs : FsState) (path : String) (e : Option FsEntry) :
    (fs.setFile path e).fds = fs.fds := by
  cases fs; rfl

section
arm64_proof_prelude

/-- Split `buf ↦ₛ bs` into `[0, written)`, `[written, written + want)`, and
    `[written + want, bs.length)`. -/
theorem pointsToBytes_split3 (buf : BitVec 64) (bs : List (BitVec 8))
    {written want : Nat} (hle : written ≤ bs.length) (hwant : want ≤ bs.length - written) :
    (buf ↦ₛ bs) =
      (buf ↦ₛ bs.take written) ∗
        ((buf + BitVec.ofNat 64 written) ↦ₛ (bs.drop written).take want) ∗
        ((buf + BitVec.ofNat 64 (written + want)) ↦ₛ bs.drop (written + want)) := by
  have hbs : bs = bs.take written ++ ((bs.drop written).take want ++ bs.drop (written + want)) := by
    have h1 : bs = bs.take written ++ bs.drop written := (List.take_append_drop written bs).symm
    have h2 : bs.drop written = (bs.drop written).take want ++ (bs.drop written).drop want :=
      (List.take_append_drop want (bs.drop written)).symm
    rw [List.drop_drop] at h2
    exact h1.trans (congrArg (bs.take written ++ ·) h2)
  have hlen1 : (bs.take written).length = written := List.length_take_of_le hle
  have hlen2 : ((bs.drop written).take want).length = want := by
    rw [List.length_take_of_le (by simp; omega)]
  have haddr : buf + BitVec.ofNat 64 written + BitVec.ofNat 64 want =
      buf + BitVec.ofNat 64 (written + want) := by
    rw [BitVec.ofNat_add]; bv_lin
  conv => lhs; rw [hbs]
  rw [pointsToBytes_append, hlen1, pointsToBytes_append, hlen2, haddr]

/-! ## 2. Inductive Chunked `write` Loop (`+0x0ac .. +0x104`) -/

private theorem bv64_ule_ofNat_false {a b : Nat} (hgt : b < a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = false := by
  have hb : b < 2 ^ 64 := Nat.lt_trans hgt ha
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_false_iff_not]
  omega

private theorem bv64_ule_self (x : BitVec 64) : x.ule x = true := by
  simp [BitVec.ule]

/-- Inductive `write` loop (`+0x0ac = 172#64 .. +0x104 = 260#64`) writing `bs.drop written` in
    `MAX_RW_COUNT` (`0x7ffff000`) chunks to `fd`. -/
theorem cliIoWriteFile_write_loop [CliIoPlacement]
    {P : Program} {fd : BitVec 64}
    (hext1 : CliIoBlockNoExtern cliIoMpl P 1)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoWriteSym)
      muslWriteFile32ClampedSpec)
    {s0 : State} {buf : BitVec 64} {cpath : String} {bs : List (BitVec 8)}
    {stackBytes : Nat} {R_tail : SepProp}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4304 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_ge : 3 ≤ fd.toNat) (hfd_lt : fd.toNat < 2 ^ 31)
    (hemp_cpath : (normalizePath cpath).isEmpty = false)
    (hbs_max : bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE)
    (hbs_va : bs.length = 0 ∨ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT)
    (hsp0 : s0.spAligned = true)
    (h_at_close :
      ∀ sc : State,
        signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem →
        sc.pc = cliIoPl01.base + 260#64 →
        sc.status = .Running →
        sc.sp = s0.sp - 4192#64 →
        sc.spAligned = true →
        sc.readReg64 (.gpr 21#5) = fd →
        sc.readReg64 (.gpr 23#5) = 0#64 →
        sc.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) →
        sc.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) →
        calleeSavedVRegs sc = calleeSavedVRegs s0 →
        sc.fs = (s0.fs.setFile cpath (some (.file bs))).setFd fd
          (some { path := cpath, accMode := .wronly, append := false,
                  cloexec := true, offset := bs.length }) →
        sc.trace = s0.trace ++ [.fileChanged (normalizePath cpath).toPathString] ++
          TraceEvent.ofBytes (OutputStream.ofFd fd) bs →
        SyscallPreserved s0 sc →
        SepWP P (s0.readReg64 .lr) sc
          (stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗ (buf ↦ₛ bs) ∗ R_tail)
          post oomProp) :
    ∀ (rem : Nat) (written : Nat) (s : State),
      bs.length - written = rem →
      written ≤ bs.length →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl s.mem →
      s.pc = cliIoPl01.base + 172#64 →
      s.status = .Running →
      s.sp = s0.sp - 4192#64 →
      s.spAligned = true →
      s.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length →
      s.readReg64 (.gpr 20#5) = buf →
      s.readReg64 (.gpr 21#5) = fd →
      s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 written →
      s.readReg64 (.gpr 25#5) = 0x7ffff000#64 →
      s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) →
      s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.fs = (s0.fs.setFile cpath (some (.file (bs.take written)))).setFd fd
        (some { path := cpath, accMode := .wronly, append := false,
                cloexec := true, offset := written }) →
      s.trace = s0.trace ++ [.fileChanged (normalizePath cpath).toPathString] ++
        TraceEvent.ofBytes (OutputStream.ofFd fd) (bs.take written) →
      SyscallPreserved s0 s →
      SepWP P (s0.readReg64 .lr) s
        (stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗ (buf ↦ₛ bs) ∗ R_tail)
        post oomProp := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro written s hrem hwle hcl_s hpc_s hrun_s hsp_s_eq hsp_s
      hx19_s hx20_s hx21_s hx24_s hx25_s hx26_s hx27_s hvregs_s hfs_s htr_s hsys_0s
    have hbs_lt64 : bs.length < 2 ^ 64 :=
      Nat.lt_of_le_of_lt hbs_max (by decide)
    by_cases hlt : written < bs.length
    · -- Non-empty remaining slice (`written < bs.length`): issue one `write` chunk.
      let want := writeChunkBytes bs.length written
      have hwant_pos : 0 < want := writeChunkBytes_pos hlt
      have hwant_le_max : want ≤ Arm64.MAX_RW_COUNT := writeChunkBytes_le_max bs.length written
      have hwant_le_sub : want ≤ bs.length - written := writeChunkBytes_le_sub bs.length written
      have hwant_lt63 : want < 2 ^ 63 := writeChunkBytes_lt_pow63 bs.length written
      have hwant_lt64 : want < 2 ^ 64 := writeChunkBytes_lt_pow64 bs.length written
      have hule_hdr : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 written) = false :=
        bv64_ule_ofNat_false hlt hbs_lt64
      have hult_hdr : (BitVec.ofNat 64 written).ult (BitVec.ofNat 64 bs.length) = true :=
        bv64_ult_ofNat_true hlt hbs_lt64
      have hsub_bv : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 written =
          BitVec.ofNat 64 (bs.length - written) := bv64_sub_ofNat hwle
      have hcsel_bv :
          (if (BitVec.ofNat 64 rem).ult 0x7ffff000#64 = true
           then BitVec.ofNat 64 rem
           else 0x7ffff000#64) = BitVec.ofNat 64 want := by
        rw [← hrem]
        exact writeChunkBytes_csel_bv hwle hbs_lt64
      -- Step `+0x0ac .. +0x0d0` (`172#64 -> resolve cliIoMpl cliIoWriteSym`).
      apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl_s
        (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoWriteSym)
      intro s' hcpu_s0; have hcpu_s := hcpu_s0.1
      change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
      have hpc_s' : s'.pc = cliIoPl01.base + 172#64 := hcpu_s.pc_eq.trans hpc_s
      have hrun_s' : s'.status = .Running := hcpu_s.status_eq.trans hrun_s
      have hsp_s' : s'.spAligned = true := by rw [hcpu_s.spAligned]; exact hsp_s
      have hx19_s' : s'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length :=
        (hcpu_s.readReg64 _).trans hx19_s
      have hx20_s' : s'.readReg64 (.gpr 20#5) = buf := (hcpu_s.readReg64 _).trans hx20_s
      have hx21_s' : s'.readReg64 (.gpr 21#5) = fd := (hcpu_s.readReg64 _).trans hx21_s
      have hx24_s' : s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 written :=
        (hcpu_s.readReg64 _).trans hx24_s
      have hx25_s' : s'.readReg64 (.gpr 25#5) = 0x7ffff000#64 :=
        (hcpu_s.readReg64 _).trans hx25_s
      wp_sym_steps
      refine SepWP.done cliIoWriteFile_write_pc (by simpa [arm64_norm] using hrun_s')
        fun sm hcpu_m0 hcl_m hnsp_m _ => ?_
      have hcpu_m := hcpu_m0.1
      have ⟨⟨hfs_sm, htr_sm⟩, hsys_sm⟩ :=
        syscallPreserved_of_seg hcpu_s0 hcpu_m0 hnsp_m
          (by simp [arm64_norm]) (by simp [arm64_norm])
      have hsys_0m : SyscallPreserved s0 sm := syscallPreserved_trans hsys_0s hsys_sm
      have hfs_m : sm.fs = s.fs := hfs_sm
      have htr_m : sm.trace = s.trace := htr_sm
      have hpc_m : sm.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoWriteSym :=
        hcpu_m.pc_eq.trans cliIoWriteFile_write_pc
      have hrun_m : sm.status = .Running := hcpu_m.status_eq.trans hrun_s'
      have hsp_m_eq : sm.sp = s0.sp - 4192#64 :=
        hcpu_m.sp_eq.trans ((by simp [arm64_norm] : _ = s'.sp).trans (hcpu_s.sp_eq.trans hsp_s_eq))
      have hsp_m : sm.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_m_eq]; exact s0.spAligned_sub 4192#64 hsp0
      have hlr_m : sm.readReg64 .lr = cliIoPl01.base + 212#64 := by
        rw [hcpu_m.readReg64 .lr]; simp [arm64_norm]
      have hw0_m : (sm.readReg32 .x0).zeroExtend 64 = fd := by
        have h32 : sm.readReg32 .x0 = fd.truncate 32 := by
          rw [State.readReg32, hcpu_m.readReg64 .x0]
          simp [arm64_norm]
        exact readReg32_zeroExtend_of_truncate h32 (Nat.lt_trans hfd_lt (by decide))
      have hx1_m : sm.readReg64 .x1 = buf + BitVec.ofNat 64 written := by
        rw [hcpu_m.readReg64 .x1]; simp [arm64_norm]
      have hx2_m : sm.readReg64 .x2 = BitVec.ofNat 64 want := by
        rw [hcpu_m.readReg64 .x2]
        simp only [arm64_norm]
      have hx19_m : sm.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length :=
        (hcpu_m.readReg64 _).trans ((by simp [arm64_norm] : _ = s'.readReg64 _).trans hx19_s')
      have hx20_m : sm.readReg64 (.gpr 20#5) = buf :=
        (hcpu_m.readReg64 _).trans ((by simp [arm64_norm] : _ = s'.readReg64 _).trans hx20_s')
      have hx21_m : sm.readReg64 (.gpr 21#5) = fd :=
        (hcpu_m.readReg64 _).trans ((by simp [arm64_norm] : _ = s'.readReg64 _).trans hx21_s')
      have hx22_m : sm.readReg64 (.gpr 22#5) = BitVec.ofNat 64 want := by
        rw [hcpu_m.readReg64]
        simp only [arm64_norm]
      have hx24_m : sm.readReg64 (.gpr 24#5) = BitVec.ofNat 64 written :=
        (hcpu_m.readReg64 _).trans ((by simp [arm64_norm] : _ = s'.readReg64 _).trans hx24_s')
      have hx25_m : sm.readReg64 (.gpr 25#5) = 0x7ffff000#64 :=
        (hcpu_m.readReg64 _).trans ((by simp [arm64_norm] : _ = s'.readReg64 _).trans hx25_s')
      have hx26_m : sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
        (hcpu_m.readReg64 _).trans ((by simp [arm64_norm] : _ = s'.readReg64 _).trans
          ((hcpu_s.readReg64 _).trans hx26_s))
      have hx27_m : sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
        (hcpu_m.readReg64 _).trans ((by simp [arm64_norm] : _ = s'.readReg64 _).trans
          ((hcpu_s.readReg64 _).trans hx27_s))
      have hvregs_m : calleeSavedVRegs sm = calleeSavedVRegs s0 :=
        hcpu_m.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s').trans
          (hcpu_s.calleeSavedVRegs.trans hvregs_s))
      -- Prepare arguments and frame for `muslWriteFile32ClampedSpec`.
      have h32_le : 32 ≤ stackBytes - 4192 := by omega
      have hsb_hi : stackBytes - 4192 ≤ 2 ^ 64 := by omega
      let desc : FdEntry :=
        { path := cpath, accMode := .wronly, append := false, cloexec := true, offset := written }
      let chunk : List (BitVec 8) := (bs.drop written).take want
      have hchunk_len : chunk.length = want := by
        dsimp only [chunk]
        rw [List.length_take_of_le (by simp; omega)]
      have hwant_toNat : (BitVec.ofNat 64 want).toNat = want := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwant_lt64]
      have hcount_nz : BitVec.ofNat 64 want ≠ 0#64 := by
        intro hz
        have := congrArg BitVec.toNat hz
        rw [hwant_toNat] at this
        simp at this
        omega
      have hchunk_clamp : chunk.length = min (BitVec.ofNat 64 want).toNat Arm64.MAX_RW_COUNT := by
        rw [hchunk_len, hwant_toNat, Nat.min_eq_left hwant_le_max]
      have hva_chunk :
          (buf + BitVec.ofNat 64 written).toNat + (BitVec.ofNat 64 want).toNat ≤
            Arm64.USER_VA_LIMIT := by
        have hbs_va' : buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT := by
          rcases hbs_va with h0 | hva
          · omega
          · exact hva
        have hva_lt64 : Arm64.USER_VA_LIMIT < 2 ^ 64 := by decide
        have hw_lt64 : written < 2 ^ 64 := by omega
        have hadd_lt64 : buf.toNat + written < 2 ^ 64 := by omega
        have hbuf_add : (buf + BitVec.ofNat 64 written).toNat = buf.toNat + written := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt64,
            Nat.mod_eq_of_lt hadd_lt64]
        rw [hbuf_add, hwant_toNat]
        omega
      have hlfs_chunk : desc.offset + (BitVec.ofNat 64 want).toNat ≤ Arm64.MAX_LFS_FILESIZE := by
        dsimp only [desc]
        rw [hwant_toNat]
        have hsafe_le_lfs : Arm64.FS_SAFE_MAX_FILESIZE ≤ Arm64.MAX_LFS_FILESIZE := by decide
        omega
      have hsafe_chunk : desc.offset + chunk.length ≤ Arm64.FS_SAFE_MAX_FILESIZE := by
        dsimp only [desc]
        rw [hchunk_len]
        omega
      have hfds_m : sm.fs.fds fd = some desc := by
        rw [hfs_m, hfs_s, fds_setFd_same]
      let T_wr : SepProp :=
        memRegion (s0.sp - 4192#64 - BitVec.ofNat 64 (stackBytes - 4192)) (stackBytes - 4192 - 32) ∗
          (buf ↦ₛ bs.take written) ∗
          ((buf + BitVec.ofNat 64 (written + want)) ↦ₛ bs.drop (written + want)) ∗
          R_tail
      wp_conv_pre =>
        rw [stackAt_shrink (s0.sp - 4192#64) (stackBytes - 4192) 32 h32_le hsb_hi,
          pointsToBytes_split3 buf bs hwle hwant_le_sub]
        simp only [sepConj_assoc]
      apply WriteFileOpenSteps.seqCodeLoaded hcl_m (mid := cliIoPl01.base + 212#64)
      apply (SepWP.call_subroutine_frame hwrite (F := T_wr)
        (x := (fd, buf + BitVec.ofNat 64 written, BitVec.ofNat 64 want, desc, chunk))
        hpc_m hrun_m hsp_m hlr_m
        (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
        (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
      · intro R' hm'
        dsimp only [muslWriteFile32ClampedSpec, T_wr]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hw0_m, hfd_ge, hfd_lt, hx1_m, hx2_m, hcount_nz, hchunk_clamp,
          hva_chunk, hlfs_chunk, hfds_m, rfl, rfl, rfl, hsafe_chunk⟩, ?_⟩
        refine Satisfies.mono ?_ hm'
        rw [hsp_m_eq]
        sep_frame
      · intro sw hpc_sw hrun_sw hsp_sw hcs_sw
        refine SepWP.done hpc_sw hrun_sw fun hcl_sw => ?_
        wp_conv_pre => dsimp only [muslWriteFile32ClampedSpec, T_wr]; simp only [sepConj_assoc]
        apply SepWP.pure_elim
        rintro ⟨hx0_sw, hfs_sw_raw, htr_sw_raw, hsys_mw⟩
        have hsys_0w : SyscallPreserved s0 sw := syscallPreserved_trans hsys_0m hsys_mw
        have hsp_sw_eq : sw.sp = s0.sp - 4192#64 := hsp_sw.trans hsp_m_eq
        have hsp_sw_al : sw.spAligned = true := by
          simp only [State.spAligned]; rw [hsp_sw_eq]; exact s0.spAligned_sub 4192#64 hsp0
        have hx0_sw_want : sw.readReg64 .x0 = BitVec.ofNat 64 want := by
          rw [hx0_sw, hchunk_len]
        have hx19_sw : sw.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length :=
          hcs_sw.readReg64_x19.trans hx19_m
        have hx20_sw : sw.readReg64 (.gpr 20#5) = buf :=
          hcs_sw.readReg64_x20.trans hx20_m
        have hx21_sw : sw.readReg64 (.gpr 21#5) = fd :=
          hcs_sw.readReg64_x21.trans hx21_m
        have hx22_sw : sw.readReg64 (.gpr 22#5) = BitVec.ofNat 64 want :=
          hcs_sw.readReg64_x22.trans hx22_m
        have hx24_sw : sw.readReg64 (.gpr 24#5) = BitVec.ofNat 64 written :=
          hcs_sw.readReg64_x24.trans hx24_m
        have hx25_sw : sw.readReg64 (.gpr 25#5) = 0x7ffff000#64 :=
          hcs_sw.readReg64_x25.trans hx25_m
        have hx26_sw : sw.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
          hcs_sw.readReg64_x26.trans hx26_m
        have hx27_sw : sw.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
          hcs_sw.readReg64_x27.trans hx27_m
        have hvregs_sw : calleeSavedVRegs sw = calleeSavedVRegs s0 :=
          hcs_sw.vregs.trans hvregs_m
        -- Simplify `sw.fs` and `sw.trace` to the `written + want` invariant.
        have hold_files : sm.fs.files cpath = some (.file (bs.take written)) := by
          rw [hfs_m, hfs_s, FsState.files_setFd,
            files_setFile_same_of_isEmpty_false s0.fs hemp_cpath]
        have hfs_sw :
            sw.fs = (s0.fs.setFile cpath (some (.file (bs.take (written + want))))).setFd fd
              (some { path := cpath, accMode := .wronly, append := false,
                      cloexec := true, offset := written + want }) := by
          dsimp only [desc, chunk] at hfs_sw_raw
          rw [hold_files] at hfs_sw_raw
          dsimp only at hfs_sw_raw
          rw [writeFileBytes_take_step bs hwle hwant_le_sub,
            hchunk_len, hfs_m, hfs_s,
            FsState.setFd_setFile_comm, FsState.setFile_setFile_same, setFd_setFd_same] at hfs_sw_raw
          exact hfs_sw_raw
        have htr_sw :
            sw.trace = s0.trace ++ [.fileChanged (normalizePath cpath).toPathString] ++
              TraceEvent.ofBytes (OutputStream.ofFd fd) (bs.take (written + want)) := by
          dsimp only [chunk] at htr_sw_raw
          rw [htr_sw_raw, htr_m, htr_s]
          simp only [List.append_assoc, ofBytes_take_step]
        -- Refold `stackAt` and `buf ↦ₛ bs`, then step `+0x0d4 .. +0x0f8` (`212#64 -> 172#64`).
        refine SepWP.weaken_pre
          (P' := stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗ (buf ↦ₛ bs) ∗ R_tail)
          (by
            rw [hsp_m_eq,
              stackAt_shrink (s0.sp - 4192#64) (stackBytes - 4192) 32 h32_le hsb_hi,
              pointsToBytes_split3 buf bs hwle hwant_le_sub]
            dsimp only [chunk]
            sep_entail) ?_
        have hwant_nez : (BitVec.ofNat 64 want == 0#64) = false :=
          bv64_beq_ofNat_false (b := 0) (by omega) hwant_lt64 (by decide)
        have hwant_b63 : (BitVec.ofNat 64 want).getLsbD 63 = false :=
          bit63_eq_zero_of_lt hwant_lt63
        have hwant_ule : (BitVec.ofNat 64 want).ule (BitVec.ofNat 64 want) = true :=
          bv64_ule_self _
        apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl_sw
          (mid := cliIoPl01.base + 172#64)
        intro sw' hcpu_w0; have hcpu_w := hcpu_w0.1
        change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
        have hpc_w' : sw'.pc = cliIoPl01.base + 212#64 := hcpu_w.pc_eq.trans hpc_sw
        have hrun_w' : sw'.status = .Running := hcpu_w.status_eq.trans hrun_sw
        have hsp_w' : sw'.spAligned = true := by rw [hcpu_w.spAligned]; exact hsp_sw_al
        have hx0_w' : sw'.readReg64 .x0 = BitVec.ofNat 64 want :=
          (hcpu_w.readReg64 .x0).trans hx0_sw_want
        have hx22_w' : sw'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 want :=
          (hcpu_w.readReg64 _).trans hx22_sw
        have hx24_w' : sw'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 written :=
          (hcpu_w.readReg64 _).trans hx24_sw
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_w')
          fun sn hcpu_n0 hcl_n hnsp_n _ => ?_
        have hcpu_n := hcpu_n0.1
        have ⟨⟨hfs_wn, htr_wn⟩, hsys_wn⟩ :=
          syscallPreserved_of_seg hcpu_w0 hcpu_n0 hnsp_n
            (by simp [arm64_norm]) (by simp [arm64_norm])
        have hsys_0n : SyscallPreserved s0 sn := syscallPreserved_trans hsys_0w hsys_wn
        have hpc_n : sn.pc = cliIoPl01.base + 172#64 :=
          hcpu_n.pc_eq.trans (by simp [arm64_norm])
        have hrun_n : sn.status = .Running := hcpu_n.status_eq.trans hrun_w'
        have hsp_n_eq : sn.sp = s0.sp - 4192#64 :=
          hcpu_n.sp_eq.trans ((by simp [arm64_norm] : _ = sw'.sp).trans (hcpu_w.sp_eq.trans hsp_sw_eq))
        have hsp_n_al : sn.spAligned = true := by
          simp only [State.spAligned]; rw [hsp_n_eq]; exact s0.spAligned_sub 4192#64 hsp0
        have hx19_n : sn.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length :=
          (hcpu_n.readReg64 _).trans ((by simp [arm64_norm] : _ = sw'.readReg64 _).trans
            ((hcpu_w.readReg64 _).trans hx19_sw))
        have hx20_n : sn.readReg64 (.gpr 20#5) = buf :=
          (hcpu_n.readReg64 _).trans ((by simp [arm64_norm] : _ = sw'.readReg64 _).trans
            ((hcpu_w.readReg64 _).trans hx20_sw))
        have hx21_n : sn.readReg64 (.gpr 21#5) = fd :=
          (hcpu_n.readReg64 _).trans ((by simp [arm64_norm] : _ = sw'.readReg64 _).trans
            ((hcpu_w.readReg64 _).trans hx21_sw))
        have hx24_n : sn.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (written + want) := by
          rw [hcpu_n.readReg64]
          simp only [arm64_norm]
          rw [← BitVec.ofNat_add, Nat.add_comm]
        have hx25_n : sn.readReg64 (.gpr 25#5) = 0x7ffff000#64 :=
          (hcpu_n.readReg64 _).trans ((by simp [arm64_norm] : _ = sw'.readReg64 _).trans
            ((hcpu_w.readReg64 _).trans hx25_sw))
        have hx26_n : sn.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
          (hcpu_n.readReg64 _).trans ((by simp [arm64_norm] : _ = sw'.readReg64 _).trans
            ((hcpu_w.readReg64 _).trans hx26_sw))
        have hx27_n : sn.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
          (hcpu_n.readReg64 _).trans ((by simp [arm64_norm] : _ = sw'.readReg64 _).trans
            ((hcpu_w.readReg64 _).trans hx27_sw))
        have hvregs_n : calleeSavedVRegs sn = calleeSavedVRegs s0 :=
          hcpu_n.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sw').trans
            (hcpu_w.calleeSavedVRegs.trans hvregs_sw))
        exact ih (bs.length - (written + want)) (by omega) (written + want) sn rfl (by omega)
          hcl_n hpc_n hrun_n hsp_n_eq hsp_n_al
          hx19_n hx20_n hx21_n hx24_n hx25_n hx26_n hx27_n hvregs_n
          (hfs_wn.trans hfs_sw) (htr_wn.trans htr_sw) hsys_0n
    · -- Loop exit (`written = bs.length`): `+0x0ac .. +0x0c0` branches to `+0x104 = 260#64`.
      have hw_eq : written = bs.length := by omega
      subst hw_eq
      have hule_done : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 bs.length) = true :=
        bv64_ule_self _
      have hult_done : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 bs.length) = false :=
        bv64_ult_ofNat_false (Nat.le_refl _) hbs_lt64
      apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl_s
        (mid := cliIoPl01.base + 260#64)
      intro s' hcpu_s0; have hcpu_s := hcpu_s0.1
      change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
      have hpc_s' : s'.pc = cliIoPl01.base + 172#64 := hcpu_s.pc_eq.trans hpc_s
      have hrun_s' : s'.status = .Running := hcpu_s.status_eq.trans hrun_s
      have hsp_s' : s'.spAligned = true := by rw [hcpu_s.spAligned]; exact hsp_s
      have hx19_s' : s'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length :=
        (hcpu_s.readReg64 _).trans hx19_s
      have hx24_s' : s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 bs.length :=
        (hcpu_s.readReg64 _).trans hx24_s
      have hx25_s' : s'.readReg64 (.gpr 25#5) = 0x7ffff000#64 :=
        (hcpu_s.readReg64 _).trans hx25_s
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_s')
        fun sc hcpu_c0 hcl_c hnsp_c _ => ?_
      have hcpu_c := hcpu_c0.1
      have ⟨⟨hfs_sc, htr_sc⟩, hsys_sc⟩ :=
        syscallPreserved_of_seg hcpu_s0 hcpu_c0 hnsp_c
          (by simp [arm64_norm]) (by simp [arm64_norm])
      have hsys_0c : SyscallPreserved s0 sc := syscallPreserved_trans hsys_0s hsys_sc
      have hpc_c : sc.pc = cliIoPl01.base + 260#64 :=
        hcpu_c.pc_eq.trans (by simp [arm64_norm])
      have hrun_c : sc.status = .Running := hcpu_c.status_eq.trans hrun_s'
      have hsp_c_eq : sc.sp = s0.sp - 4192#64 :=
        hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = s'.sp).trans (hcpu_s.sp_eq.trans hsp_s_eq))
      have hsp_c_al : sc.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_c_eq]; exact s0.spAligned_sub 4192#64 hsp0
      have hx21_c : sc.readReg64 (.gpr 21#5) = fd :=
        (hcpu_c.readReg64 _).trans ((by simp [arm64_norm] : _ = s'.readReg64 _).trans
          ((hcpu_s.readReg64 _).trans hx21_s))
      have hx23_c : sc.readReg64 (.gpr 23#5) = 0#64 := by
        rw [hcpu_c.readReg64]; simp [arm64_norm]
      have hx26_c : sc.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
        (hcpu_c.readReg64 _).trans ((by simp [arm64_norm] : _ = s'.readReg64 _).trans
          ((hcpu_s.readReg64 _).trans hx26_s))
      have hx27_c : sc.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
        (hcpu_c.readReg64 _).trans ((by simp [arm64_norm] : _ = s'.readReg64 _).trans
          ((hcpu_s.readReg64 _).trans hx27_s))
      have hvregs_c : calleeSavedVRegs sc = calleeSavedVRegs s0 :=
        hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s').trans
          (hcpu_s.calleeSavedVRegs.trans hvregs_s))
      have hfs_c :
          sc.fs = (s0.fs.setFile cpath (some (.file bs))).setFd fd
            (some { path := cpath, accMode := .wronly, append := false,
                    cloexec := true, offset := bs.length }) := by
        rw [hfs_sc, hfs_s, List.take_length]
      have htr_c :
          sc.trace = s0.trace ++ [.fileChanged (normalizePath cpath).toPathString] ++
            TraceEvent.ofBytes (OutputStream.ofFd fd) bs := by
        rw [htr_sc, htr_s, List.take_length]
      exact h_at_close sc hcl_c hpc_c hrun_c hsp_c_eq hsp_c_al
        hx21_c hx23_c hx26_c hx27_c hvregs_c hfs_c htr_c hsys_0c

/-! ## 3. Post-`open` Success Path (`+0x084 .. +0x12c`) -/

/-- Execute `write_file` from `+0x084 = 132#64` after `open` succeeds (`w0 = fd.truncate 32`):
    branches to `+0x0a0`, runs `cliIoWriteFile_write_loop`, calls `close(fd)` via
    `muslClose48LocalSpec`, sets `w0 = 0`, and runs `cliIoWriteFile_ret_epilogue` returning
    `x0 = 0#64` with `sf.fs = s0.fs.setFile (cPathOf pathBytes) (some (.file bs))`. -/
theorem cliIoWriteFile_post_open [CliIoPlacement]
    {P : Program} {fd : BitVec 64}
    (hext1 : CliIoBlockNoExtern cliIoMpl P 1)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoWriteSym)
      muslWriteFile32ClampedSpec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
      muslClose48LocalSpec)
    {s0 so : State} {buf : BitVec 64} {pathBytes bs : List (BitVec 8)}
    {stackBytes : Nat} {R_rest : SepProp}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4304 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hfd_ge : 3 ≤ fd.toNat) (hfd_lt : fd.toNat < 2 ^ 31)
    (hfds_none : s0.fs.fds fd = none)
    (hcan : fsCanWriteFile s0.fs (cPathOf pathBytes) = true)
    (hbs_max : bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE)
    (hbs_va : bs.length = 0 ∨ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT)
    (hcl_so : signalSessionIoMultiLib.CodeLoaded cliIoMpl so.mem)
    (hpc_so : so.pc = cliIoPl01.base + 132#64)
    (hrun_so : so.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_so_eq : so.sp = s0.sp - 4192#64) (hsp_so : so.spAligned = true)
    (hw0_so : so.readReg32 .x0 = fd.truncate 32)
    (hx19_so : so.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length)
    (hx20_so : so.readReg64 (.gpr 20#5) = buf)
    (hx26_so : so.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5))
    (hx27_so : so.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5))
    (hvregs_so : calleeSavedVRegs so = calleeSavedVRegs s0)
    (hfs_so : so.fs = (s0.fs.setFile (cPathOf pathBytes) (some (.file []))).setFd fd
      (some { path := cPathOf pathBytes, accMode := .wronly, append := false,
              cloexec := true, offset := 0 }))
    (htr_so : so.trace = s0.trace ++ [.fileChanged (normalizePath (cPathOf pathBytes)).toPathString])
    (hsys_0so : SyscallPreserved s0 so)
    (hok_ret :
      ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
        signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
        sf.readReg64 .x0 = 0#64 →
        sf.fs = s0.fs.setFile (cPathOf pathBytes) (some (.file bs)) →
        sf.trace = s0.trace ++ [.fileChanged (normalizePath (cPathOf pathBytes)).toPathString] ++
          TraceEvent.ofBytes (OutputStream.ofFd fd) bs →
        SyscallPreserved s0 sf →
        ∀ {Pre_f : SepProp},
          (Pre_f ⊢ stackAt s0.sp stackBytes ∗ (buf ↦ₛ bs) ∗ StdErrnoCell s0.tpidrEl0 ∗ R_rest) →
          post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) so
      (stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
        memRegion (s0.sp - 4192#64) 12 ∗
        memRegion (s0.sp - 4180#64) 4096 ∗
        memRegion (s0.sp - 84#64) 4 ∗
        cliIoSavedRegs10 s0 ∗
        StdErrnoCell s0.tpidrEl0 ∗
        (buf ↦ₛ bs) ∗
        R_rest)
      post oomProp := by
  have hlo4192 : 4192 ≤ stackBytes := by omega
  have hemp_cpath : (normalizePath (cPathOf pathBytes)).isEmpty = false :=
    normalizePath_isEmpty_false_of_fsCanWriteFile hcan
  -- Step `+0x084` (`tbz w0, #0x1f, +0x0a0`) + `+0x0a0 .. +0x0a8` (`132#64 -> 172#64`).
  apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl_so
    (mid := cliIoPl01.base + 172#64)
  intro so' hcpu_o0; have hcpu_o := hcpu_o0.1
  change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
  have hpc_o' : so'.pc = cliIoPl01.base + 132#64 := hcpu_o.pc_eq.trans hpc_so
  have hrun_o' : so'.status = .Running := hcpu_o.status_eq.trans hrun_so
  have hsp_o' : so'.spAligned = true := by rw [hcpu_o.spAligned]; exact hsp_so
  have hbit31_o' : (so'.readReg64 .x0).getLsbD 31 = false := by
    have hw32 : (so'.readReg64 .x0).truncate 32 = fd.truncate 32 :=
      (hcpu_o.readReg32 .x0).trans hw0_so
    have htr : (so'.readReg64 .x0).getLsbD 31 = ((so'.readReg64 .x0).truncate 32).getLsbD 31 := by
      simp
    rw [htr, hw32]
    exact getLsbD_31_of_fd_lt hfd_lt
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_o')
    fun sl0 hcpu_l0 hcl_l0 hnsp_l0 _ => ?_
  have hcpu_l := hcpu_l0.1
  have ⟨⟨hfs_ol, htr_ol⟩, hsys_ol⟩ :=
    syscallPreserved_of_seg hcpu_o0 hcpu_l0 hnsp_l0
      (by simp [arm64_norm]) (by simp [arm64_norm])
  have hsys_0l : SyscallPreserved s0 sl0 := syscallPreserved_trans hsys_0so hsys_ol
  have hpc_l : sl0.pc = cliIoPl01.base + 172#64 :=
    hcpu_l.pc_eq.trans (by simp [arm64_norm])
  have hrun_l : sl0.status = .Running := hcpu_l.status_eq.trans hrun_o'
  have hsp_l_eq : sl0.sp = s0.sp - 4192#64 :=
    hcpu_l.sp_eq.trans ((by simp [arm64_norm] : _ = so'.sp).trans (hcpu_o.sp_eq.trans hsp_so_eq))
  have hsp_l_al : sl0.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_l_eq]; exact s0.spAligned_sub 4192#64 hsp0
  have hx19_l : sl0.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length :=
    (hcpu_l.readReg64 _).trans ((by simp [arm64_norm] : _ = so'.readReg64 _).trans
      ((hcpu_o.readReg64 _).trans hx19_so))
  have hx20_l : sl0.readReg64 (.gpr 20#5) = buf :=
    (hcpu_l.readReg64 _).trans ((by simp [arm64_norm] : _ = so'.readReg64 _).trans
      ((hcpu_o.readReg64 _).trans hx20_so))
  have hx21_l : sl0.readReg64 (.gpr 21#5) = fd := by
    have hw32 : so'.readReg32 .x0 = fd.truncate 32 := (hcpu_o.readReg32 .x0).trans hw0_so
    rw [hcpu_l.readReg64]
    simp only [arm64_norm]
    exact readReg32_zeroExtend_of_truncate hw32 (Nat.lt_trans hfd_lt (by decide))
  have hx24_l : sl0.readReg64 (.gpr 24#5) = BitVec.ofNat 64 0 := by
    rw [hcpu_l.readReg64]; simp [arm64_norm]
  have hx25_l : sl0.readReg64 (.gpr 25#5) = 0x7ffff000#64 := by
    rw [hcpu_l.readReg64]; simp [arm64_norm]
  have hx26_l : sl0.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
    (hcpu_l.readReg64 _).trans ((by simp [arm64_norm] : _ = so'.readReg64 _).trans
      ((hcpu_o.readReg64 _).trans hx26_so))
  have hx27_l : sl0.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
    (hcpu_l.readReg64 _).trans ((by simp [arm64_norm] : _ = so'.readReg64 _).trans
      ((hcpu_o.readReg64 _).trans hx27_so))
  have hvregs_l : calleeSavedVRegs sl0 = calleeSavedVRegs s0 :=
    hcpu_l.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs so').trans
      (hcpu_o.calleeSavedVRegs.trans hvregs_so))
  have hfs_l :
      sl0.fs = (s0.fs.setFile (cPathOf pathBytes) (some (.file (bs.take 0)))).setFd fd
        (some { path := cPathOf pathBytes, accMode := .wronly, append := false,
                cloexec := true, offset := 0 }) := by
    simpa using hfs_ol.trans hfs_so
  have htr_l :
      sl0.trace = s0.trace ++ [.fileChanged (normalizePath (cPathOf pathBytes)).toPathString] ++
        TraceEvent.ofBytes (OutputStream.ofFd fd) (bs.take 0) := by
    simpa [TraceEvent.ofBytes] using htr_ol.trans htr_so
  let R_frame : SepProp :=
    memRegion (s0.sp - 4192#64) 12 ∗
      memRegion (s0.sp - 4180#64) 4096 ∗
      memRegion (s0.sp - 84#64) 4 ∗
      cliIoSavedRegs10 s0 ∗
      StdErrnoCell s0.tpidrEl0 ∗
      R_rest
  refine SepWP.weaken_pre
    (P' := stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗ (buf ↦ₛ bs) ∗ R_frame)
    (by dsimp only [R_frame]; sep_entail) ?_
  refine cliIoWriteFile_write_loop hext1 hwrite hlo hhi hfd_ge hfd_lt hemp_cpath hbs_max hbs_va hsp0
    (R_tail := R_frame) (fun sc hcl_c hpc_c hrun_c hsp_c_eq hsp_c_al
      hx21_c hx23_c hx26_c hx27_c hvregs_c hfs_c htr_c hsys_0c => ?_)
    bs.length 0 sl0 (Nat.sub_zero _) (Nat.zero_le _)
    hcl_l0 hpc_l hrun_l hsp_l_eq hsp_l_al
    hx19_l hx20_l hx21_l hx24_l hx25_l hx26_l hx27_l hvregs_l hfs_l htr_l hsys_0l
  -- At `+0x104 = 260#64`: `mov w0, w21; bl close` (`260#64 -> resolve cliIoMpl cliIoCloseSym`).
  apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl_c
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym)
  intro sc' hcpu_c0; have hcpu_c := hcpu_c0.1
  change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
  have hpc_c' : sc'.pc = cliIoPl01.base + 260#64 := hcpu_c.pc_eq.trans hpc_c
  have hrun_c' : sc'.status = .Running := hcpu_c.status_eq.trans hrun_c
  have hsp_c' : sc'.spAligned = true := by rw [hcpu_c.spAligned]; exact hsp_c_al
  have hx21_c' : sc'.readReg64 (.gpr 21#5) = fd := (hcpu_c.readReg64 _).trans hx21_c
  wp_sym_steps
  refine SepWP.done cliIoWriteFile_close_pc (by simpa [arm64_norm] using hrun_c')
    fun smc hcpu_mc0 hcl_mc hnsp_mc _ => ?_
  have hcpu_mc := hcpu_mc0.1
  have ⟨⟨hfs_cmc, htr_cmc⟩, hsys_cmc⟩ :=
    syscallPreserved_of_seg hcpu_c0 hcpu_mc0 hnsp_mc
      (by simp [arm64_norm]) (by simp [arm64_norm])
  have hsys_0mc : SyscallPreserved s0 smc := syscallPreserved_trans hsys_0c hsys_cmc
  have hpc_mc : smc.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoCloseSym :=
    hcpu_mc.pc_eq.trans cliIoWriteFile_close_pc
  have hrun_mc : smc.status = .Running := hcpu_mc.status_eq.trans hrun_c'
  have hsp_mc_eq : smc.sp = s0.sp - 4192#64 :=
    hcpu_mc.sp_eq.trans ((by simp [arm64_norm] : _ = sc'.sp).trans (hcpu_c.sp_eq.trans hsp_c_eq))
  have hsp_mc : smc.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_mc_eq]; exact s0.spAligned_sub 4192#64 hsp0
  have hlr_mc : smc.readReg64 .lr = cliIoPl01.base + 268#64 := by
    rw [hcpu_mc.readReg64 .lr]; simp [arm64_norm]
  have hw0_mc : (smc.readReg32 .x0).zeroExtend 64 = fd := by
    have h32 : smc.readReg32 .x0 = fd.truncate 32 := by
      rw [State.readReg32, hcpu_mc.readReg64 .x0]
      simp [arm64_norm]
    exact readReg32_zeroExtend_of_truncate h32 (Nat.lt_trans hfd_lt (by decide))
  have hx23_mc : smc.readReg64 (.gpr 23#5) = 0#64 :=
    (hcpu_mc.readReg64 _).trans ((by simp [arm64_norm] : _ = sc'.readReg64 _).trans
      ((hcpu_c.readReg64 _).trans hx23_c))
  have hx26_mc : smc.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
    (hcpu_mc.readReg64 _).trans ((by simp [arm64_norm] : _ = sc'.readReg64 _).trans
      ((hcpu_c.readReg64 _).trans hx26_c))
  have hx27_mc : smc.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
    (hcpu_mc.readReg64 _).trans ((by simp [arm64_norm] : _ = sc'.readReg64 _).trans
      ((hcpu_c.readReg64 _).trans hx27_c))
  have hvregs_mc : calleeSavedVRegs smc = calleeSavedVRegs s0 :=
    hcpu_mc.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sc').trans
      (hcpu_c.calleeSavedVRegs.trans hvregs_c))
  -- Call `muslClose48LocalSpec` (`48`-B stack).
  have h48_le : 48 ≤ stackBytes - 4192 := by omega
  have hsb_hi : stackBytes - 4192 ≤ 2 ^ 64 := by omega
  let desc_end : FdEntry :=
    { path := cPathOf pathBytes, accMode := .wronly, append := false,
      cloexec := true, offset := bs.length }
  have hfds_mc : smc.fs.fds fd = some desc_end := by
    rw [hfs_cmc, hfs_c, fds_setFd_same]
  let T_cl : SepProp :=
    memRegion (s0.sp - 4192#64 - BitVec.ofNat 64 (stackBytes - 4192)) (stackBytes - 4192 - 48) ∗
      (buf ↦ₛ bs) ∗ R_frame
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 4192#64) (stackBytes - 4192) 48 h48_le hsb_hi]
    simp only [sepConj_assoc]
  apply WriteFileOpenSteps.seqCodeLoaded hcl_mc (mid := cliIoPl01.base + 268#64)
  apply (SepWP.call_subroutine_frame hclose (F := T_cl) (x := (fd, desc_end))
    hpc_mc hrun_mc hsp_mc hlr_mc
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslClose48LocalSpec, T_cl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hw0_mc, hfd_lt, hfds_mc, Or.inl rfl⟩, ?_⟩
    refine Satisfies.mono ?_ hm'
    rw [hsp_mc_eq]
    sep_frame
  · intro scl hpc_scl hrun_scl hsp_scl hcs_scl
    refine SepWP.done hpc_scl hrun_scl fun hcl_scl => ?_
    wp_conv_pre => dsimp only [muslClose48LocalSpec, T_cl]; simp only [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨_hw0_scl, hfs_scl_raw, htr_scl_raw, hsys_mc_scl⟩
    have hsys_0scl : SyscallPreserved s0 scl := syscallPreserved_trans hsys_0mc hsys_mc_scl
    have hsp_scl_eq : scl.sp = s0.sp - 4192#64 := hsp_scl.trans hsp_mc_eq
    have hsp_scl_al : scl.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_scl_eq]; exact s0.spAligned_sub 4192#64 hsp0
    have hx23_scl : scl.readReg64 (.gpr 23#5) = 0#64 := hcs_scl.readReg64_x23.trans hx23_mc
    have hx26_scl : scl.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
      hcs_scl.readReg64_x26.trans hx26_mc
    have hx27_scl : scl.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
      hcs_scl.readReg64_x27.trans hx27_mc
    have hvregs_scl : calleeSavedVRegs scl = calleeSavedVRegs s0 := hcs_scl.vregs.trans hvregs_mc
    have hfs_scl : scl.fs = s0.fs.setFile (cPathOf pathBytes) (some (.file bs)) := by
      have hfds_set : (s0.fs.setFile (cPathOf pathBytes) (some (.file bs))).fds fd = none := by
        rw [fds_setFile, hfds_none]
      rw [hfs_scl_raw, hfs_cmc, hfs_c, setFd_setFd_same,
        FsState.setFd_none_of_eq_none hfds_set]
    have htr_scl :
        scl.trace = s0.trace ++ [.fileChanged (normalizePath (cPathOf pathBytes)).toPathString] ++
          TraceEvent.ofBytes (OutputStream.ofFd fd) bs :=
      htr_scl_raw.trans (htr_cmc.trans htr_c)
    -- Step `+0x10c` (`mov w0, w23`, `268#64 -> 272#64`), then `cliIoWriteFile_ret_epilogue`.
    apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl_scl
      (mid := cliIoPl01.base + 272#64)
    intro scl' hcpu_cl0; have hcpu_cl := hcpu_cl0.1
    change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
    have hpc_cl' : scl'.pc = cliIoPl01.base + 268#64 := hcpu_cl.pc_eq.trans hpc_scl
    have hrun_cl' : scl'.status = .Running := hcpu_cl.status_eq.trans hrun_scl
    have hsp_cl' : scl'.spAligned = true := by rw [hcpu_cl.spAligned]; exact hsp_scl_al
    have hx23_cl' : scl'.readReg64 (.gpr 23#5) = 0#64 := (hcpu_cl.readReg64 _).trans hx23_scl
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_cl')
      fun se hcpu_e0 hcl_e hnsp_e _ => ?_
    have hcpu_e := hcpu_e0.1
    have ⟨⟨hfs_cle, htr_cle⟩, hsys_cle⟩ :=
      syscallPreserved_of_seg hcpu_cl0 hcpu_e0 hnsp_e
        (by simp [arm64_norm]) (by simp [arm64_norm])
    have hsys_0e : SyscallPreserved s0 se := syscallPreserved_trans hsys_0scl hsys_cle
    have hpc_e : se.pc = cliIoPl01.base + 272#64 :=
      hcpu_e.pc_eq.trans (by simp [arm64_norm])
    have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_cl'
    have hsp_e_eq : se.sp = s0.sp - 4192#64 :=
      hcpu_e.sp_eq.trans
        ((by simp [arm64_norm] : _ = scl'.sp).trans (hcpu_cl.sp_eq.trans hsp_scl_eq))
    have hx0_e : se.readReg64 .x0 = 0#64 := by
      rw [hcpu_e.readReg64 .x0]; simp [arm64_norm]
    have hx26_e : se.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
      (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = scl'.readReg64 _).trans
        ((hcpu_cl.readReg64 _).trans hx26_scl))
    have hx27_e : se.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
      (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = scl'.readReg64 _).trans
        ((hcpu_cl.readReg64 _).trans hx27_scl))
    have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
      hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs scl').trans
        (hcpu_cl.calleeSavedVRegs.trans hvregs_scl))
    refine SepWP.weaken_pre ?_
      (cliIoWriteFile_ret_epilogue hext1
        (R_out := (buf ↦ₛ bs) ∗ StdErrnoCell s0.tpidrEl0 ∗ R_rest)
        hlo4192 hhi hcl_e hpc_e hrun_e hsp0 hsp_e_eq hx26_e hx27_e hvregs_e
        fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hx0_f hfs_ef htr_ef hsys_ef _ hent =>
          hok_ret sf hpc_f hrun_f hsp_f hcs_f hcl_f
            (hx0_f.trans hx0_e)
            (hfs_ef.trans (hfs_cle.trans hfs_scl))
            (htr_ef.trans (htr_cle.trans htr_scl))
            (syscallPreserved_trans hsys_0e hsys_ef) hent)
    rw [hsp_mc_eq, stackAt_shrink (s0.sp - 4192#64) (stackBytes - 4192) 48 h48_le hsb_hi]
    dsimp only [R_frame]
    sep_entail

end

end LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileLoop

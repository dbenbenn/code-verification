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
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.SignalSession.CliIo.Sym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst -- proof-setup: allow-public-import
import LibsignalBinary.Heap.MallocngBridgeBudget
import LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FinishGrowBudget
import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileOpenSteps
import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileLoop

/-!
# End-to-End `MultiPlacedLib` and Budget-Threaded Proofs of `libsignal_cli_io::write_file`

Composes `WriteFileOpenSteps` and `WriteFileLoop` on `signalSessionIoMultiLib` block `1`
(`304` B / `76` insns) to establish:

1. **Layer 1 (`cliIoWriteFile_ok` & `cliIoWriteFile_musl_ok`)**: Raw `MultiPlacedLib` contract
   `cliIoWriteFileSpec` using `4304` B peak stack (`4192` B `write_file` frame + `112` B `open`
   frame) and `0` heap allocations over `muslOpenCreateTruncSpec`, `muslErrnoLocationSpec`,
   `muslWriteFile32ClampedSpec`, and `muslClose48LocalSpec` (instantiated to `muslSysPlacedLib`).
2. **Layer 2 (`cliIoWriteFile_budget_ok` & `mallocng` / `fineCostModel` corollaries)**:
   Budget-threaded honest contract `writeFileSpecPlacedSatClamped` (`evs = []`,
   `WriteFileEnv x.path.length []`, `VmPreserved s0 sf`) matching
   `IoHonestSpecs.writeFileSpecPlacedSat cliIo A lim stk` under `lim.enforced = true` and
   `x.bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE` (`0xffff_ffff`) for any `PoolErrnoSplit A tp brkStart`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileProof

open Arm64 Arm64.Obj Arm64.Process
open ProofLib hiding MallocngAddrs MallocngIface
open ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open CryptoVerification.RustHeap (allocFailedEvent)
open CryptoVerification.SignalSession (
  PathOk blockingAncestor? contains_zero_eq_false_of_pathOk pathComps
)
open CryptoVerification.SignalSession.Cli.MainHops (
  IoModel WriteFileGhost blockingAncestorF cliIo cliWr pathStr
)
open VerifiedLibraries.Mallocng (MallocngAddrs)
open VerifiedLibraries.Musl (
  MuslSysPlacement ValidRelCPath muslErrnoLocation2_block_ok muslErrnoLocationSpec
  muslOpenCreateTruncSpec muslOpenCreateTrunc_ok muslSysMpl muslSysPlacedLib
  muslWriteFile32ClampedSpec muslWriteFile32Clamped_ok
)
open VerifiedLibraries.RustStd (StdErrnoCell cPathOf stdErrnoAddr)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FdsHiFrame FitsEnv MallocngCostModelIface
  MallocngCostModelSound RustCliAllocBudget VmPreserved mallocngRustCliAllocBudget
  mallocngRustCliAllocBudgetAt
)
open LibsignalBinary.Heap.Fine (fineRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (WriteFileEnv withVmPreserved writeFileEnv_nil)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  fineHookRustCliAllocBudget mallocngHookRustCliAllocBudget
)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoBlockNoExtern CliIoPlacement cliIoCloseSym cliIoErrnoLocationSym cliIoMpl
  cliIoOpenSym cliIoResolve_eq_base cliIoWriteFileSym cliIoWriteFile_lookup cliIoWriteSym
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  muslClose48LocalSpec muslClose48Local_ok
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic (
  ancestorWalkErrno?_eq_of_pathOk blockingAncestor?_ne_some_dir
  isEmpty_false_of_pathOk trailingDir_false_of_pathOk validRelCPath_of_pathOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FinishGrowBudget (
  vmMemPreserved_of_syscallPreserved vmPreserved_of_syscallPreserved_fds
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed allocFd_eq_three_of_fdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst (
  PoolErrnoSplit fineHookPoolErrnoSplit finePoolErrnoSplit
  mallocngHookPoolErrnoSplit mallocngPoolErrnoSplit mallocngPoolErrnoSplitAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs (
  writeFileHonestCore writeFileStackFloor
)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileOpenSteps (
  cliIo1_lt cliIoWriteFile_open_step cliIoWriteFile_pre_open
  mem_toList_cPathOf_lt_256 syscallPreserved_trans toList_cPathOf_length
)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileLoop (
  cliIoWriteFile_post_open fds_setFile
)

/-! ## 1. Path, Filesystem (`fsCanWriteFile` ↔ `cliIo.wr`), Trace, and `USER_VA_LIMIT` Lemmas -/

/-- Exact peak stack usage of `libsignal_cli_io::write_file` (`4192` B frame + `112` B `open`). -/
@[expose] def cliIoWriteFileStackBytes : Nat := 4304

theorem cliIoWriteFileStackBytes_le_floor : cliIoWriteFileStackBytes ≤ writeFileStackFloor := by
  decide

private theorem cPathOf_eq_pathStr (path : List (BitVec 8)) : cPathOf path = pathStr path := rfl

theorem zero_not_mem_of_cliPathOk {path : List (BitVec 8)} (h : cliIo.pathOk path) :
    (0#8 : BitVec 8) ∉ path := by
  intro hm
  have hc : path.contains 0#8 = true := List.contains_iff_mem.mpr hm
  rw [contains_zero_eq_false_of_pathOk h.1] at hc
  exact Bool.noConfusion hc

theorem path_lt_4096_of_cliPathOk {path : List (BitVec 8)} (h : cliIo.pathOk path) :
    path.length < 4096 :=
  h.2.2

theorem validRelCPath_of_cliPathOk {path : List (BitVec 8)} (h : cliIo.pathOk path) :
    ValidRelCPath (cPathOf path) :=
  validRelCPath_of_pathOk
    (by rw [cPathOf_eq_pathStr]; exact h.1)
    (by rw [toList_cPathOf_length]; exact h.2.2)
    (fun _ hc => mem_toList_cPathOf_lt_256 hc)

theorem setFile_files_eq_fn (fs : FsState) (p : String) (bs : List (BitVec 8)) :
    (fs.setFile p (some (.file bs))).files = fun q =>
      if (normalizePath q).isEmpty then some .dir
      else if normalizePath q = normalizePath p then some (.file bs) else fs.files q := by
  funext q
  unfold FsState.files FsState.setFile FsState.getEntry FsState.setEntry
  cases hemp : (normalizePath q).isEmpty with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases heq : normalizePath q = normalizePath p
    · simp [heq]
    · have hbeq : (normalizePath q == normalizePath p) = false := beq_eq_false_iff_ne.mpr heq
      simp [heq, hbeq]

/-- Exact alignment between `fsCanWriteFile fs (cPathOf path)` and `cliIo.wr fs.files path bs`
    under `cliIo.pathOk path`. -/
theorem cliWr_eq_of_cliPathOk (fs : FsState) {path : List (BitVec 8)}
    (hpok : cliIo.pathOk path) (bs : List (BitVec 8)) :
    cliIo.wr fs.files path bs =
      if fsCanWriteFile fs (cPathOf path) then
        some (fs.setFile (cPathOf path) (some (.file bs))).files
      else none := by
  have hp : PathOk (cPathOf path) = true := by rw [cPathOf_eq_pathStr]; exact hpok.1
  have hmax : ((pathComps (cPathOf path)).all fun c => decide (c.length ≤ NAME_MAX)) = true := by
    rw [cPathOf_eq_pathStr]; exact hpok.2.1.2
  have hemp : (cPathOf path).isEmpty = false := isEmpty_false_of_pathOk hp
  have htrail : trailingDir (cPathOf path) = false := trailingDir_false_of_pathOk hp
  have hanc := ancestorWalkErrno?_eq_of_pathOk fs hp hmax
  have hb_ndir := blockingAncestor?_ne_some_dir fs (cPathOf path)
  have hset := setFile_files_eq_fn fs (pathStr path) bs
  change cliWr fs.files path bs = _
  unfold cliWr fsCanWriteFile
  rw [hemp, htrail, hanc]
  have hba_eq : blockingAncestor? fs (cPathOf path) = blockingAncestorF fs.files (pathStr path) := rfl
  have hfl_eq : fs.files (cPathOf path) = fs.files (pathStr path) := rfl
  rw [hba_eq, hfl_eq, cPathOf_eq_pathStr, hset]
  cases hb : blockingAncestorF fs.files (pathStr path) with
  | none =>
    cases hf : fs.files (pathStr path) with
    | none => rfl
    | some e =>
      cases e with
      | file _ => rfl
      | dir => rfl
  | some a =>
    cases a with
    | none => rfl
    | some e =>
      cases e with
      | file _ => rfl
      | dir => exact absurd (hba_eq.trans hb) hb_ndir

theorem traceStreamBytes_stdout_ofBytes_ne {out : OutputStream} (hne : out ≠ .stdout) :
    ∀ (bs : List (BitVec 8)),
      ProcessOutcome.traceStreamBytes .stdout (TraceEvent.ofBytes out bs) = []
  | [] => rfl
  | b :: bs => by
    have hhd : ProcessOutcome.traceStreamBytes .stdout [TraceEvent.writeByte out b] = [] := by
      cases out with
      | stdout => exact absurd rfl hne
      | stderr => rfl
      | fd _ => rfl
    change ProcessOutcome.traceStreamBytes .stdout
        ([TraceEvent.writeByte out b] ++ TraceEvent.ofBytes out bs) = []
    rw [traceStreamBytes_append, hhd, List.nil_append]
    exact traceStreamBytes_stdout_ofBytes_ne hne bs

theorem ofFd_ne_stdout_of_ge3 {fd : BitVec 64} (hfd : 3 ≤ fd.toNat) :
    OutputStream.ofFd fd ≠ .stdout := by
  unfold OutputStream.ofFd
  have hne1 : fd ≠ 1#64 := fun h => by subst h; simp at hfd
  have hne2 : fd ≠ 2#64 := fun h => by subst h; simp at hfd
  simp [hne1, hne2]

theorem allocFailedEvent_not_mem_ofBytes (out : OutputStream) :
    ∀ (bs : List (BitVec 8)), allocFailedEvent ∉ TraceEvent.ofBytes out bs
  | [] => List.not_mem_nil
  | b :: bs => by
    intro hm
    rcases List.mem_cons.mp hm with hhd | htl
    · exact TraceEvent.noConfusion hhd
    · exact allocFailedEvent_not_mem_ofBytes out bs htl

theorem allocFailedEvent_not_mem_writeFileTrace {tr : List TraceEvent} (p : String)
    (out : OutputStream) (bs : List (BitVec 8)) (h0 : allocFailedEvent ∉ tr) :
    allocFailedEvent ∉ tr ++ [.fileChanged p] ++ TraceEvent.ofBytes out bs := by
  intro hm
  rcases List.mem_append.mp hm with hm1 | hm2
  · rcases List.mem_append.mp hm1 with ht | hfc
    · exact h0 ht
    · rw [List.mem_singleton] at hfc
      exact TraceEvent.noConfusion hfc
  · exact allocFailedEvent_not_mem_ofBytes out bs hm2

/-- Derive `bs.length = 0 ∨ buf.toNat + bs.length ≤ USER_VA_LIMIT` from `(buf ↦ₛ bs)` and any
    mapped-address `< USER_VA_LIMIT` invariant (such as `PoolErrnoSplit.pool_mapped_lt_userVa`). -/
theorem pointsToBytes_userVa_of_mapped {m : Memory} {buf : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} (hbs_le : bs.length ≤ 2 ^ 48)
    (hmapVa : ∀ a : BitVec 64, (m.perm a).mapped = true → a.toNat < Arm64.USER_VA_LIMIT)
    (hsat : m ⊨ (buf ↦ₛ bs) ∗ R) :
    bs.length = 0 ∨ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT := by
  rcases Nat.eq_zero_or_pos bs.length with hz | hpos
  · exact Or.inl hz
  · right
    have hsat_mr : m ⊨ memRegion buf bs.length ∗ R :=
      Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion buf bs)) hsat
    have hle64 : bs.length ≤ 2 ^ 64 := by omega
    have hbyte : ∀ k : Nat, k < bs.length →
        (buf + BitVec.ofNat 64 k).toNat < Arm64.USER_VA_LIMIT := by
      intro k hk
      have hcw : m.canWrite (buf + BitVec.ofNat 64 k) 1 = true :=
        memRegion_canWrite1 hsat_mr hk hle64
      have hmap : (m.perm (buf + BitVec.ofNat 64 k)).mapped = true := by
        unfold Memory.canWrite Memory.allPerm at hcw
        cases hp : m.perm (buf + BitVec.ofNat 64 k) with
        | none => rw [hp] at hcw; cases hcw
        | some _ => rfl
      exact hmapVa _ hmap
    have hLim : Arm64.USER_VA_LIMIT = 2 ^ 48 := rfl
    have h0 : buf.toNat < Arm64.USER_VA_LIMIT := by
      have h := hbyte 0 hpos
      simpa using h
    let last := bs.length - 1
    have hlast_lt : last < bs.length := by omega
    have hlast_va : (buf + BitVec.ofNat 64 last).toNat < Arm64.USER_VA_LIMIT :=
      hbyte last hlast_lt
    have hlast_64 : last < 2 ^ 64 := by omega
    have hadd_64 : buf.toNat + last < 2 ^ 64 := by omega
    have htoNat : (buf + BitVec.ofNat 64 last).toNat = buf.toNat + last := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlast_64,
        Nat.mod_eq_of_lt hadd_64]
    omega

private theorem stackAt_le_two_pow_64_of_errnoCell {m : Memory} {tp sp : BitVec 64} {stk : Nat}
    {R : SepProp} (hstk : 0 < stk)
    (h : m ⊨ StdErrnoCell tp ∗ (stackAt sp stk ∗ R)) : stk ≤ 2 ^ 64 := by
  have hmr : StdErrnoCell tp ⊢ memRegion (stdErrnoAddr tp) 4 := by
    unfold StdErrnoCell
    refine Entails.sepExists_elim fun v => ?_
    exact IsBlock.entails (IsBlock.pointsTo32 (stdErrnoAddr tp) v)
      (IsBlock.memRegion (stdErrnoAddr tp) 4) (fun _ _ => trivial)
  have hm' : m ⊨ memRegion (stdErrnoAddr tp) 4 ∗ (stackAt sp stk ∗ R) :=
    Satisfies.mono (sepConj_mono_left hmr) h
  have hdisj := (IsBlock.memRegion (stdErrnoAddr tp) 4).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) (by decide) hstk hm'
  have hlt := (stdErrnoAddr tp - (sp - BitVec.ofNat 64 stk)).isLt
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

/-! ## 2. Layer 1: Raw `MultiPlacedLib` Contract (`cliIoWriteFileSpec` & `cliIoWriteFile_ok`) -/

/-- Pure postcondition relation of `libsignal_cli_io::write_file` on state fields. -/
@[expose] def cliIoWriteFileOutcome (fd : BitVec 64) (pathBytes bs : List (BitVec 8))
    (s0 sf : State) : Prop :=
  if pathBytes.length < 4096 ∧ (0#8 : BitVec 8) ∉ pathBytes ∧
      fsCanWriteFile s0.fs (cPathOf pathBytes) = true then
    sf.readReg64 .x0 = 0#64 ∧
      sf.fs = s0.fs.setFile (cPathOf pathBytes) (some (.file bs)) ∧
      sf.trace = s0.trace ++ [.fileChanged (normalizePath (cPathOf pathBytes)).toPathString] ++
        TraceEvent.ofBytes (OutputStream.ofFd fd) bs ∧
      SyscallPreserved s0 sf
  else
    sf.readReg64 .x0 = 1#64 ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf

/-- Placement-generic Hoare contract for `signalSessionIoMultiLib` block `1`
    (`libsignal_cli_io::write_file(path, bytes)`): `4304`-B stack, `0` heap allocations.
    Ghost argument: `(pathPtr, pathBytes, buf, bs)`. -/
@[expose] def cliIoWriteFileSpec (fd : BitVec 64 := 3#64)
    (stackBytes : Nat := cliIoWriteFileStackBytes) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (pathPtr, pathBytes, buf, bs) s0 =>
    ⌜s0.readReg64 .x0 = pathPtr ∧
      (s0.readReg64 .x1).toNat = pathBytes.length ∧
      s0.readReg64 .x2 = buf ∧
      (s0.readReg64 .x3).toNat = bs.length ∧
      cliIoWriteFileStackBytes ≤ stackBytes ∧
      (pathBytes.length < 4096 ∧ (0#8 : BitVec 8) ∉ pathBytes →
        ValidRelCPath (cPathOf pathBytes) ∧
          s0.fs.allocFd = some fd ∧
          3 ≤ fd.toNat ∧ fd.toNat < 2 ^ 31 ∧
          s0.fs.fds fd = none ∧
          bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE ∧
          (bs.length = 0 ∨ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT))⌝ ∗
      ((pathPtr ↦ₛ pathBytes) ∗ (buf ↦ₛ bs) ∗ stackAt s0.sp stackBytes ∗ StdErrnoCell s0.tpidrEl0)
  post := fun (pathPtr, pathBytes, buf, bs) s0 sf =>
    ⌜cliIoWriteFileOutcome fd pathBytes bs s0 sf⌝ ∗
      ((pathPtr ↦ₛ pathBytes) ∗ (buf ↦ₛ bs) ∗ stackAt s0.sp stackBytes ∗ StdErrnoCell s0.tpidrEl0)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Placement-generic verification of `libsignal_cli_io::write_file` (`signalSessionIoMultiLib`
    block `1`) over `open`, `__errno_location`, `write`, and `close` subroutine contracts. -/
theorem cliIoWriteFile_ok {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} (fd : BitVec 64 := 3#64) (stackBytes : Nat := cliIoWriteFileStackBytes)
    (hext1 : CliIoBlockNoExtern mpl P 1)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      (muslOpenCreateTruncSpec fd))
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      (muslWriteFile32ClampedSpec))
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      (muslClose48LocalSpec)) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (cliIoWriteFileSpec fd stackBytes)) := by
  let _ : CliIoPlacement := ⟨mpl, hpl⟩
  rw [cliIoResolve_eq_base hpl 1 cliIoWriteFileSym cliIo1_lt cliIoWriteFile_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨pathPtr, pathBytes, buf, bs⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, cliIoWriteFileSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlo, hvalid_imp⟩, hmem⟩
  have hlo4192 : 4192 ≤ stackBytes := by unfold cliIoWriteFileStackBytes at hlo; omega
  have hlo4304 : 4304 ≤ stackBytes := hlo
  have hhi : stackBytes ≤ 2 ^ 64 :=
    stackAt_le_two_pow_64_of_errnoCell (tp := s0.tpidrEl0) (sp := s0.sp) (stk := stackBytes)
      (R := (pathPtr ↦ₛ pathBytes) ∗ (buf ↦ₛ bs) ∗ R)
      (by omega) (Satisfies.mono (by sep_entail) hmem)
  have hmem_pre :
      s0.mem ⊨ (stackAt s0.sp stackBytes ∗ (pathPtr ↦ₛ pathBytes) ∗
        ((buf ↦ₛ bs) ∗ StdErrnoCell s0.tpidrEl0)) ∗ R :=
    Satisfies.mono (by sep_entail) hmem
  refine ⟨_, hmem_pre, ?_⟩
  refine cliIoWriteFile_pre_open hext1 (ro := false)
    (R_rest := (buf ↦ₛ bs) ∗ StdErrnoCell s0.tpidrEl0)
    hlo4192 hhi hcl0 hpc hrun hsp0 hx0 hx1 hx2 hx3
    (fun hbad sf _hpc_f _hrun_f hsp_f hcs_f _hcl_f hx0_f hfs_f htr_f hsys_f {_Pre_f} hent => ?_)
    (fun hlt4096 hnul sm hcl_m hpc_m hrun_m hsp_m_eq hsp_m hlr_m
        hx0_m hw1_m hw2_m hx19_m hx20_m hx26_m hx27_m hvregs_m hfs_m htr_m hsys_0m => ?_)
  · -- Early error return (`4096 ≤ pathBytes.length ∨ 0#8 ∈ pathBytes`).
    have hcond_f :
        ¬ (pathBytes.length < 4096 ∧ (0#8 : BitVec 8) ∉ pathBytes ∧
            fsCanWriteFile s0.fs (cPathOf pathBytes) = true) := by
      rintro ⟨h1, h2, _⟩
      rcases hbad with hge | hm
      · omega
      · exact h2 hm
    refine ⟨fun hm_f => ?_, hsp_f, hcs_f⟩
    have hpost_pure : cliIoWriteFileOutcome fd pathBytes bs s0 sf := by
      unfold cliIoWriteFileOutcome
      simp only [hcond_f, ↓reduceIte]
      exact ⟨hx0_f, hfs_f, htr_f, hsys_f⟩
    rw [pure_sepConj_of_true hpost_pure]
    exact Satisfies.mono
      (Entails.trans (sepConj_mono_left hent)
        (by rw [show VerifiedLibraries.Musl.memcpySrc false pathPtr pathBytes =
              (pathPtr ↦ₛ pathBytes) from rfl]
            sep_entail))
      hm_f
  · -- Valid-path branch (`pathBytes.length < 4096 ∧ 0#8 ∉ pathBytes`): step `open` then loop/err.
    obtain ⟨hvrel, halloc, hfd_ge, hfd_lt, hfds_none, hbs_max, hbs_va⟩ :=
      hvalid_imp ⟨hlt4096, hnul⟩
    refine SepWP.weaken_pre
      (by rw [show VerifiedLibraries.Musl.memcpySrc false pathPtr pathBytes =
            (pathPtr ↦ₛ pathBytes) from rfl]
          sep_entail)
      (cliIoWriteFile_open_step hext1 hopen herrno
        (R_keep := (pathPtr ↦ₛ pathBytes) ∗ (buf ↦ₛ bs))
        hlo4304 hhi hlt4096 hvrel halloc hfd_lt
        hcl_m hpc_m hrun_m hsp0 hsp_m_eq hsp_m hlr_m
        hx0_m hw1_m hw2_m hx19_m hx20_m hx26_m hx27_m hvregs_m
        hfs_m htr_m hsys_0m
        (fun hcan0 sf _hpc_f _hrun_f hsp_f hcs_f _hcl_f hx0_f hfs_f htr_f hsys_f
            {_Pre_f} hent => ?_)
        (fun hcan0 so hcl_so hpc_so hrun_so hsp_so_eq hsp_so hw0_so
            hx19_so hx20_so hx26_so hx27_so hvregs_so hfs_so0 htr_so0 hsys_0so => ?_))
    · -- `open` failed (`fsCanWriteFile = false`): returns `1#64` with `fs` & `trace` unchanged.
      have hcond_f :
          ¬ (pathBytes.length < 4096 ∧ (0#8 : BitVec 8) ∉ pathBytes ∧
              fsCanWriteFile s0.fs (cPathOf pathBytes) = true) := by
        rintro ⟨_, _, hc⟩
        rw [hcan0] at hc
        exact Bool.noConfusion hc
      refine ⟨fun hm_f => ?_, hsp_f, hcs_f⟩
      have hpost_pure : cliIoWriteFileOutcome fd pathBytes bs s0 sf := by
        unfold cliIoWriteFileOutcome
        simp only [hcond_f, ↓reduceIte]
        exact ⟨hx0_f, hfs_f, htr_f, hsys_f⟩
      rw [pure_sepConj_of_true hpost_pure]
      exact Satisfies.mono
        (Entails.trans (sepConj_mono_left hent) (by sep_entail)) hm_f
    · -- `open` succeeded (`fsCanWriteFile = true`): run `cliIoWriteFile_post_open`.
      refine SepWP.weaken_pre
        (by sep_entail)
        (cliIoWriteFile_post_open hext1 hwrite hclose (R_rest := pathPtr ↦ₛ pathBytes)
          hlo4304 hhi hfd_ge hfd_lt hfds_none hcan0 hbs_max hbs_va
          hcl_so hpc_so hrun_so hsp0 hsp_so_eq hsp_so hw0_so
          hx19_so hx20_so hx26_so hx27_so hvregs_so hfs_so0 htr_so0 hsys_0so
          fun sf _hpc_f _hrun_f hsp_f hcs_f _hcl_f hx0_f hfs_f htr_f hsys_f {_Pre_f} hent => ?_)
      have hcond_t :
          pathBytes.length < 4096 ∧ (0#8 : BitVec 8) ∉ pathBytes ∧
            fsCanWriteFile s0.fs (cPathOf pathBytes) = true :=
        ⟨hlt4096, hnul, hcan0⟩
      refine ⟨fun hm_f => ?_, hsp_f, hcs_f⟩
      have hpost_pure : cliIoWriteFileOutcome fd pathBytes bs s0 sf := by
        unfold cliIoWriteFileOutcome
        simp only [hcond_t]
        exact ⟨hx0_f, hfs_f, htr_f, hsys_f⟩
      rw [pure_sepConj_of_true hpost_pure]
      exact Satisfies.mono
        (Entails.trans (sepConj_mono_left hent) (by sep_entail)) hm_f

private theorem subroutine_ok_strip_muslCodeLoaded {α : Type}
    {P : Program} {entry : BitVec 64} {spec : Spec α} [MuslSysPlacement]
    (hMuslCode : ∀ m : Memory, P.CodeLoaded m → muslSysPlacedLib.CodeLoaded muslSysMpl m)
    (h : subroutine_ok P entry (muslSysPlacedLib.withCodeLoaded muslSysMpl spec)) :
    subroutine_ok P entry spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hpre' : s0.mem ⊨ (muslSysPlacedLib.withCodeLoaded muslSysMpl spec).pre x s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜muslSysPlacedLib.CodeLoaded muslSysMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨hMuslCode s0.mem hLP, hpre⟩
  exact subroutine_ok.mono_outcome h x R s0 hpc hrun hpre' hsp (fun _ hout => hout)

/-- Concrete `muslSysPlacedLib` instantiation of `cliIoWriteFile_ok` under `Syscall.standard`
    with zero libc hooks (`∀ pc, P.externAt? pc = none`). -/
theorem cliIoWriteFile_musl_ok [MuslSysPlacement]
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} (fd : BitVec 64 := 3#64) (stackBytes : Nat := cliIoWriteFileStackBytes)
    (hext : ∀ pc, P.externAt? pc = none)
    (hsvc : P.svc = Syscall.standard)
    (hMuslCode : ∀ m : Memory, P.CodeLoaded m → muslSysPlacedLib.CodeLoaded muslSysMpl m)
    (hOpenAddr : signalSessionIoMultiLib.resolve mpl cliIoOpenSym =
      muslSysPlacedLib.fnAddr muslSysMpl "open")
    (hErrnoAddr : signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym =
      muslSysPlacedLib.fnAddr muslSysMpl "__errno_location")
    (hWriteAddr : signalSessionIoMultiLib.resolve mpl cliIoWriteSym =
      muslSysPlacedLib.fnAddr muslSysMpl "write")
    (hCloseAddr : signalSessionIoMultiLib.resolve mpl cliIoCloseSym =
      muslSysPlacedLib.fnAddr muslSysMpl "close") :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl (cliIoWriteFileSpec fd stackBytes)) := by
  have herrno_musl : subroutine_ok P (muslSysPlacedLib.fnAddr muslSysMpl "__errno_location")
      (muslSysPlacedLib.withCodeLoaded muslSysMpl muslErrnoLocationSpec) :=
    muslSysPlacedLib.subroutine_ok_of_block (j := 0) (by decide) muslErrnoLocation2_block_ok
      hext hsvc
  exact cliIoWriteFile_ok hpl fd stackBytes
    (CliIoBlockNoExtern.of_no_extern hext 1)
    (hOpenAddr ▸ subroutine_ok_strip_muslCodeLoaded hMuslCode
      (muslOpenCreateTrunc_ok fd hext hsvc))
    (hErrnoAddr ▸ subroutine_ok_strip_muslCodeLoaded hMuslCode herrno_musl)
    (hWriteAddr ▸ subroutine_ok_strip_muslCodeLoaded hMuslCode
      (muslWriteFile32Clamped_ok hext hsvc))
    (hCloseAddr ▸ subroutine_ok_strip_muslCodeLoaded hMuslCode
      (muslClose48Local_ok hext hsvc))

/-! ## 3. Layer 2: Budget-Threaded Honest Contract (`writeFileSpecPlacedSatClamped`) -/

/-- Clamped counterpart of `IoHonestSpecs.writeFileHonestCore`: identical `post`, `onPanic`,
    `onExit`, and `onOom`, with `x.bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE` (`0xffff_ffff`,
    strictly stronger than `< 2 ^ 63`, required because `Syscall.standard` `execWrite` traps above
    `FS_SAFE_MAX_FILESIZE`). -/
@[expose] def writeFileHonestCoreClamped {M : AllocCostModel} (io : IoModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (WriteFileGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x2 = x.buf ∧ (s.readReg64 .x3).toNat = x.bs.length ∧
      x.path.length < 2 ^ 32 ∧ io.pathOk x.path ∧
      FitsEnv M lim st (WriteFileEnv x.path.length) ∧
      writeFileStackFloor ≤ stk ∧ FdsGe3Closed s.fs ∧
      x.bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := (writeFileHonestCore io A lim stk).post
  onPanic := (writeFileHonestCore io A lim stk).onPanic
  onExit := (writeFileHonestCore io A lim stk).onExit
  onOom := (writeFileHonestCore io A lim stk).onOom

/-- Clamped counterpart of `IoHonestSpecs.writeFileSpecPlacedSat` (`withVmPreserved`). -/
@[expose] def writeFileSpecPlacedSatClamped {M : AllocCostModel} (io : IoModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (WriteFileGhost × M.σ) :=
  withVmPreserved (writeFileHonestCoreClamped io A lim stk)

/-- Budget-threaded `withCodeLoaded` verification of `libsignal_cli_io::write_file` against
    `writeFileSpecPlacedSatClamped cliIo A lim stk` for any `PoolErrnoSplit A tp brkStart`. -/
theorem cliIoWriteFile_budget_withCodeLoaded_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} (stk : Nat)
    (hext1 : CliIoBlockNoExtern mpl P 1)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      (muslOpenCreateTruncSpec 3#64))
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteFile32ClampedSpec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (writeFileSpecPlacedSatClamped cliIo A lim stk)) := by
  have hraw := cliIoWriteFile_ok hpl 3#64 stk hext1 hopen herrno hwrite hclose
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp0 _hLP
  dsimp only [MultiPlacedLib.withCodeLoaded, writeFileSpecPlacedSatClamped, withVmPreserved,
    writeFileHonestCoreClamped] at hpre
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1_nat, hx2, hx3_nat, _hplen32, hpok, _hfits, hstk_floor, hfds_closed,
    hbs_max⟩, hmem⟩
  have hlo : cliIoWriteFileStackBytes ≤ stk :=
    Nat.le_trans cliIoWriteFileStackBytes_le_floor hstk_floor
  have hbs_le48 : x.bs.length ≤ 2 ^ 48 := Nat.le_trans hbs_max (by decide)
  have hbs_va : x.bs.length = 0 ∨ x.buf.toNat + x.bs.length ≤ Arm64.USER_VA_LIMIT :=
    pointsToBytes_userVa_of_mapped hbs_le48
      (fun _ hmap => S.pool_mapped_lt_userVa lim st hEnf
        (R := (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ R)
        (Satisfies.mono (by sep_entail) hmem) hmap)
      (R := (x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ A.pool lim st s0 ∗ R)
      (Satisfies.mono (by sep_entail) hmem)
  have halloc3 : s0.fs.allocFd = some 3#64 := allocFd_eq_three_of_fdsGe3Closed hfds_closed
  have hfds3 : s0.fs.fds 3#64 = none := hfds_closed 3 (Nat.le_refl 3) (by decide)
  have hvrel : ValidRelCPath (cPathOf x.path) := validRelCPath_of_cliPathOk hpok
  -- Split `A.pool lim st s0` into `S.core lim st s0 ∗ StdErrnoCell s0.tpidrEl0`.
  have hmem_split :
      s0.mem ⊨ ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
        (((x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗
          StdErrnoCell s0.tpidrEl0) ∗ (S.core lim st s0 ∗ R)) := by
    refine Satisfies.mono ?_ hmem
    let Keep0 : SepProp := ((x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk) ∗ R
    refine Entails.trans (by dsimp only [Keep0]; sep_entail)
      (Entails.trans (sepConj_mono_left (Q := Keep0) (S.pool_split lim st s0))
        (by dsimp only [Keep0]; sep_entail))
  rw [satisfies_pure_sepConj] at hmem_split
  rcases hmem_split with ⟨⟨htp0, hbs0⟩, hmem_core⟩
  have hpre_raw :
      s0.mem ⊨ (signalSessionIoMultiLib.withCodeLoaded mpl (cliIoWriteFileSpec 3#64 stk)).pre
        (x.pathA, x.path, x.buf, x.bs) s0 ∗ (S.core lim st s0 ∗ R) := by
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoWriteFileSpec]
    rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_nat, hx2, hx3_nat, hlo, fun _ =>
      ⟨hvrel, halloc3, by decide, by decide, hfds3, hbs_max, hbs_va⟩⟩, hmem_core⟩
  refine subroutine_ok.mono_outcome hraw (x.pathA, x.path, x.buf, x.bs)
    (S.core lim st s0 ∗ R) s0 hpc hrun hpre_raw hsp0 ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoWriteFileSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hout, hmem_out⟩
    have hlt4096 : x.path.length < 4096 := path_lt_4096_of_cliPathOk hpok
    have hnul : (0#8 : BitVec 8) ∉ x.path := zero_not_mem_of_cliPathOk hpok
    have hwr_eq := cliWr_eq_of_cliPathOk s0.fs hpok x.bs
    dsimp only [MultiPlacedLib.withCodeLoaded, writeFileSpecPlacedSatClamped, withVmPreserved,
      writeFileHonestCoreClamped, writeFileHonestCore]
    by_cases hcan : fsCanWriteFile s0.fs (cPathOf x.path) = true
    · -- Success path (`fsCanWriteFile = true`, `cliIo.wr = some ...`, `x0 = 0#64`).
      have hcond_t :
          x.path.length < 4096 ∧ (0#8 : BitVec 8) ∉ x.path ∧
            fsCanWriteFile s0.fs (cPathOf x.path) = true := ⟨hlt4096, hnul, hcan⟩
      unfold cliIoWriteFileOutcome at hout
      simp only [hcond_t] at hout
      rcases hout with ⟨hx0_f, hfs_f, htr_f, hsys_f⟩
      have hfds_f : sf.fs.fds = s0.fs.fds := by rw [hfs_f, fds_setFile]
      have hhi_fds : FdsHiFrame s0 sf := fun fd _ _ => congrFun hfds_f (BitVec.ofNat 64 fd)
      have hvm_f : VmPreserved s0 sf := vmPreserved_of_syscallPreserved_fds hsys_f hhi_fds
      have hcore_eq : S.core lim st s0 = S.core lim st sf :=
        (S.core_transport lim st (vmMemPreserved_of_syscallPreserved hsys_f)).symm
      have hjoin_sf : S.core lim st sf ∗ StdErrnoCell s0.tpidrEl0 ⊢ A.pool lim st sf := by
        rw [htp0]
        exact S.pool_join lim st (hsys_f.1.trans htp0) (hsys_f.2.2.brkStart_eq.trans hbs0)
      have hwr_some :
          cliIo.wr s0.fs.files x.path x.bs =
            some (s0.fs.setFile (cPathOf x.path) (some (.file x.bs))).files := by
        rw [hwr_eq, hcan]; rfl
      let pnorm := (normalizePath (cPathOf x.path)).toPathString
      let d : List TraceEvent :=
        [.fileChanged pnorm] ++ TraceEvent.ofBytes (OutputStream.ofFd 3#64) x.bs
      have htr_d : sf.trace = s0.trace ++ d := by
        dsimp only [d, pnorm]; rw [htr_f, List.append_assoc]
      have hpref : s0.trace <+: sf.trace := ⟨d, htr_d.symm⟩
      have hstdout :
          ProcessOutcome.traceStreamBytes .stdout sf.trace =
            ProcessOutcome.traceStreamBytes .stdout s0.trace := by
        rw [htr_d, traceStreamBytes_append, traceStreamBytes_append,
          traceStreamBytes_fileChanged,
          traceStreamBytes_stdout_ofBytes_ne (ofFd_ne_stdout_of_ge3 (by decide)),
          List.append_nil, List.append_nil]
      have hfstr : FsTraced (fun e => e.isFsChange = true) s0 sf :=
        FsTraced.of_fsEvent d htr_d (.fileChanged pnorm) (List.mem_cons_self ..) rfl
      have halloc_ev : allocFailedEvent ∉ s0.trace → allocFailedEvent ∉ sf.trace := by
        intro h0
        rw [htr_f]
        exact allocFailedEvent_not_mem_writeFileTrace pnorm (OutputStream.ofFd 3#64) x.bs h0
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hvm_f, ?_⟩
      apply Satisfies.sepExists_intro ([] : List AllocEvent)
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨?_, ?_⟩
      · rw [hwr_some]
        exact ⟨writeFileEnv_nil x.path.length, ⟨hx0_f, congrArg FsState.files hfs_f⟩,
          hpref, hstdout, hfds_f, hfstr, halloc_ev⟩
      · have hstep_nil : M.stepEvents ([] : List AllocEvent) st = st := rfl
        rw [hstep_nil]
        refine Satisfies.mono ?_ hmem_out
        rw [hcore_eq]
        let KeepF : SepProp :=
          (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk
        refine Entails.trans (by dsimp only [KeepF]; sep_entail)
          (Entails.trans (sepConj_mono_left (Q := R) (sepConj_mono_right (P := KeepF) hjoin_sf))
            (by dsimp only [KeepF]; sep_entail))
    · -- Error path (`fsCanWriteFile = false`, `cliIo.wr = none`, `x0 = 1#64`).
      have hcan_f : fsCanWriteFile s0.fs (cPathOf x.path) = false :=
        Bool.eq_false_iff.mpr hcan
      have hcond_f :
          ¬ (x.path.length < 4096 ∧ (0#8 : BitVec 8) ∉ x.path ∧
              fsCanWriteFile s0.fs (cPathOf x.path) = true) := by
        rintro ⟨_, _, hc⟩; exact hcan hc
      unfold cliIoWriteFileOutcome at hout
      simp only [hcond_f, ↓reduceIte] at hout
      rcases hout with ⟨hx0_f, hfs_f, htr_f, hsys_f⟩
      have hfds_f : sf.fs.fds = s0.fs.fds := congrArg FsState.fds hfs_f
      have hhi_fds : FdsHiFrame s0 sf := fun fd _ _ => congrFun hfds_f (BitVec.ofNat 64 fd)
      have hvm_f : VmPreserved s0 sf := vmPreserved_of_syscallPreserved_fds hsys_f hhi_fds
      have hcore_eq : S.core lim st s0 = S.core lim st sf :=
        (S.core_transport lim st (vmMemPreserved_of_syscallPreserved hsys_f)).symm
      have hjoin_sf : S.core lim st sf ∗ StdErrnoCell s0.tpidrEl0 ⊢ A.pool lim st sf := by
        rw [htp0]
        exact S.pool_join lim st (hsys_f.1.trans htp0) (hsys_f.2.2.brkStart_eq.trans hbs0)
      have hwr_none : cliIo.wr s0.fs.files x.path x.bs = none := by
        rw [hwr_eq, hcan_f]; rfl
      have hpref : s0.trace <+: sf.trace := htr_f ▸ List.prefix_refl _
      have hstdout :
          ProcessOutcome.traceStreamBytes .stdout sf.trace =
            ProcessOutcome.traceStreamBytes .stdout s0.trace := by rw [htr_f]
      have hfstr : FsTraced (fun e => e.isFsChange = true) s0 sf :=
        FsTraced.of_eq htr_f (congrArg FsState.files hfs_f)
      have halloc_ev : allocFailedEvent ∉ s0.trace → allocFailedEvent ∉ sf.trace := by
        rw [htr_f]; exact id
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hvm_f, ?_⟩
      apply Satisfies.sepExists_intro ([] : List AllocEvent)
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨?_, ?_⟩
      · rw [hwr_none]
        exact ⟨writeFileEnv_nil x.path.length, ⟨hx0_f, congrArg FsState.files hfs_f⟩,
          hpref, hstdout, hfds_f, hfstr, halloc_ev⟩
      · have hstep_nil : M.stepEvents ([] : List AllocEvent) st = st := rfl
        rw [hstep_nil]
        refine Satisfies.mono ?_ hmem_out
        rw [hcore_eq]
        let KeepF : SepProp :=
          (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk
        refine Entails.trans (by dsimp only [KeepF]; sep_entail)
          (Entails.trans (sepConj_mono_left (Q := R) (sepConj_mono_right (P := KeepF) hjoin_sf))
            (by dsimp only [KeepF]; sep_entail))
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Budget-threaded verification of `libsignal_cli_io::write_file` stripping `withCodeLoaded`
    for any `PoolErrnoSplit A tp brkStart`. -/
theorem cliIoWriteFile_budget_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {tp brkStart : BitVec 64}
    (S : PoolErrnoSplit A tp brkStart) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} (stk : Nat)
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m)
    (hext1 : CliIoBlockNoExtern mpl P 1)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      (muslOpenCreateTruncSpec 3#64))
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteFile32ClampedSpec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteFileSym)
      (writeFileSpecPlacedSatClamped cliIo A lim stk) := by
  have hwcl :=
    cliIoWriteFile_budget_withCodeLoaded_ok S lim hpl stk hext1 hopen herrno hwrite hclose hEnf
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hpre' :
      s0.mem ⊨ (signalSessionIoMultiLib.withCodeLoaded mpl
        (writeFileSpecPlacedSatClamped cliIo A lim stk)).pre x s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨hCode s0.mem hLP, hpre⟩
  exact subroutine_ok.mono_outcome hwcl x R s0 hpc hrun hpre' hsp (fun _ hout => hout)

/-! ## 4. Concrete `mallocng` and `fineCostModel` Instantiations -/

/-- `mallocngRustCliAllocBudget` instantiation of `cliIoWriteFile_budget_ok`. -/
theorem cliIoWriteFile_mallocng_ok
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) (mmpl : MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} (stk : Nat)
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m)
    (hext1 : CliIoBlockNoExtern mpl P 1)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      (muslOpenCreateTruncSpec 3#64))
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteFile32ClampedSpec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteFileSym)
      (writeFileSpecPlacedSatClamped cliIo
        (mallocngRustCliAllocBudget M I hS γ mmpl tp brkStart) lim stk) :=
  cliIoWriteFile_budget_ok (mallocngPoolErrnoSplit hS γ mmpl tp brkStart) lim hpl stk hCode
    hext1 hopen herrno hwrite hclose hEnf

/-- `mallocngHookRustCliAllocBudget` instantiation of `cliIoWriteFile_budget_ok`. -/
theorem cliIoWriteFile_mallocngHook_ok
    {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) (mmpl : MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} (stk : Nat)
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m)
    (hext1 : CliIoBlockNoExtern mpl P 1)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      (muslOpenCreateTruncSpec 3#64))
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteFile32ClampedSpec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteFileSym)
      (writeFileSpecPlacedSatClamped cliIo
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim stk) :=
  cliIoWriteFile_budget_ok (mallocngHookPoolErrnoSplit hS γ mmpl tp brkStart) lim hpl stk hCode
    hext1 hopen herrno hwrite hclose hEnf

/-- `fineHookRustCliAllocBudget` instantiation of `cliIoWriteFile_budget_ok`. -/
theorem cliIoWriteFile_fineHook_ok
    (γ : GhostName) (mmpl : MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} (stk : Nat)
    (hCode : ∀ m : Memory, P.CodeLoaded m → signalSessionIoMultiLib.CodeLoaded mpl m)
    (hext1 : CliIoBlockNoExtern mpl P 1)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      (muslOpenCreateTruncSpec 3#64))
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hwrite : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteSym)
      muslWriteFile32ClampedSpec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hEnf : lim.enforced = true := by decide) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoWriteFileSym)
      (writeFileSpecPlacedSatClamped cliIo
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk) :=
  cliIoWriteFile_budget_ok (fineHookPoolErrnoSplit γ mmpl tp brkStart) lim hpl stk hCode
    hext1 hopen herrno hwrite hclose hEnf

end LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileProof

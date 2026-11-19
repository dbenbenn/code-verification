/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Honest `write_file` and `write_stdout` Contracts (`Cli.Main.IoHonestSpecs`)

The earlier consumer specs `SpecsPlacedBudget.writeFileSpecPlaced` and
`SpecsPlacedBudget.writeStdoutSpecPlaced` omit stack-floor, file-descriptor, and file-size
preconditions required by the compiled `signal_session_io::write_file` and `write_stdout`
(`third_party/libsignal/libsignal-session/cli/io/src/lib.rs:222`, `:285`), which allocate a
`4096`-byte stack path buffer, open a file descriptor, and are bounded by
`Arm64.FS_SAFE_MAX_FILESIZE`.

This module defines the real-code-compatible contracts so consumers depend only on
`HookSat H sym <spec>`:
1. `writeFileHonestCore` / `writeFileSpecPlacedSat`;
2. `writeStdoutHonestCore` / `writeStdoutSpecPlacedSat`.

Each contract adds preconditions to `pre` (stack floor, closed descriptors, length bound) and
only adds conjuncts to `post` (keeping every earlier `post` conjunct verbatim).
Idealized-hook bridges live in `Cli.Main.IoHonestSpecsHook`; machine-code proofs against
`signalSessionIoMultiLib` and `muslSysPlacedLib` live in
`HookDischarge.CliIoFmt.WriteFileProof` and `HookDischarge.CliIoFmt.WriteStdoutProof`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession.Cli.MainHops (IoModel WriteFileGhost WriteStdoutGhost)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (allocFailedEvent)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (WriteFileEnv WriteStdoutEnv withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)

/-! ## 1. Stack floors -/

/-- Conservative stack floor (bytes below `sp`) for the compiled `write_file`.
    The compiled function keeps a `4096`-byte NUL-terminated path copy on the stack (`cpath`,
    `lib.rs:222`) plus its own frame and the musl `open` / `write` / `close` / `__errno_location`
    frames (`4304` bytes peak stack in `WriteFileProof`). `8192` is a conservative named constant
    below `extHookStack` (`16384`). -/
@[expose] def writeFileStackFloor : Nat := 8192

/-- Conservative stack floor (bytes below `sp`) for the compiled `write_stdout`
    (`write_all_fd::<true>(1, bytes)` plus musl `write` and `__errno_location`; `96` bytes peak
    stack in `WriteStdoutProof`). `1024` is a conservative named constant `≤ extHookStack`. -/
@[expose] def writeStdoutStackFloor : Nat := 1024

theorem writeFileStackFloor_le_extHookStack : writeFileStackFloor ≤ extHookStack := by decide

theorem writeStdoutStackFloor_le_extHookStack : writeStdoutStackFloor ≤ extHookStack := by decide

/-! ## 2. `write_file` -/

/-- Core contract of the compiled `signal_session_io::write_file(path, bytes)`
(`x0..x3`; `Result<(), IoError>` in `x0`: `0` Ok, `1` Err), extending
`SpecsPlacedBudget.writeFileSpecPlaced` with the preconditions needed by the compiled code.

The compiled function (`lib.rs:222-282`) copies `path` byte by byte (via `black_box`) into a
`4096`-byte stack buffer, returns `Err` if the path is `≥ 4096` bytes or contains an interior NUL,
calls musl `open(cpath, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0o666)` with an `EINTR` retry
loop, writes all bytes via `write_all_fd::<false>` (chunks of `0x7fff_f000`, `n == 0` is `Err`),
and closes the descriptor on exit. It performs no heap allocation; errors read thread-local `errno`.

`pre` additions:
* `writeFileStackFloor ≤ stk`: reserves stack space for the `4096`-byte buffer and musl frames.
* `FdsGe3Closed s.fs`: ensures `open` allocates descriptor `3` (`allocFd_eq_three_of_fds3_none`)
  and cannot fail with `EMFILE` (stronger than `s.fs.allocFd.isSome`, matching the descriptor
  invariant threaded by callers).
* `x.bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE` (`0xffff_ffff`): required by `Syscall.standard`
  regular-file `execWrite` (`offset + count ≤ FS_SAFE_MAX_FILESIZE`).

`post` additions (all earlier conjuncts are preserved verbatim and first):
* `sf.fs.fds = s0.fs.fds`: `open` allocates fd `3` and `close` clears it on return.
* `FsTraced (·.isFsChange) s0 sf`: trace only grows, and `fs.files` changes are accompanied by
  file events. Kept prefix-only because `writeFileHook` emits `fileChanged p` on error paths and
  omits per-byte `writeByte (.fd fd)` events.
* `allocFailedEvent ∉ s0.trace → allocFailedEvent ∉ sf.trace`: no allocation occurs.
* `VmPreserved s0 sf` is added by `writeFileSpecPlacedSat` (`withVmPreserved`).

Unchanged choices:
* `WriteFileEnv` (`SpecBudget.lean:840`) still over-approximates allocation events (`evs = []`),
  keeping consumers' `FitsEnv` shapes unchanged.
* `x0 = 0#64` / `1#64` is kept as a full 64-bit value.
* `errno`: on error paths the compiled code writes thread-local `errno`, which for a concrete
  allocator `A` is owned by `A.pool` (`PoolErrnoSplit` / `pool_split_errno`), so machine-code
  proofs (`WriteFileProof`) discharge `writeFileSpecPlacedSat` per concrete `A` rather than an
  arbitrary abstract `A`. -/
@[expose] def writeFileHonestCore {M : AllocCostModel} (io : IoModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (WriteFileGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x2 = x.buf ∧ (s.readReg64 .x3).toNat = x.bs.length ∧
      x.path.length < 2 ^ 32 ∧ io.pathOk x.path ∧
      FitsEnv M lim st (WriteFileEnv x.path.length) ∧
      writeFileStackFloor ≤ stk ∧ FdsGe3Closed s.fs ∧
      x.bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜WriteFileEnv x.path.length evs ∧
        (match io.wr s0.fs.files x.path x.bs with
         | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
         | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) ∧
        s0.trace <+: sf.trace ∧
        ProcessOutcome.traceStreamBytes .stdout sf.trace =
          ProcessOutcome.traceStreamBytes .stdout s0.trace ∧
        sf.fs.fds = s0.fs.fds ∧
        FsTraced (fun e => e.isFsChange = true) s0 sf ∧
        (allocFailedEvent ∉ s0.trace → allocFailedEvent ∉ sf.trace)⌝ ∗
        (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗
        A.pool lim (M.stepEvents evs st) sf

/-- `write_file` consumer contract: `writeFileHonestCore` with `VmPreserved s0 sf` on normal
return (`withVmPreserved`). No allocation or `mmap` occurs, `brk`/`tpidr_el0`/`physMemAvail` and
page permissions are unchanged, and the descriptor table is unchanged on return. Discharged on
machine code in `HookDischarge.CliIoFmt.WriteFileProof` for allocators with `PoolErrnoSplit`. -/
@[expose] def writeFileSpecPlacedSat {M : AllocCostModel} (io : IoModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (WriteFileGhost × M.σ) :=
  withVmPreserved (writeFileHonestCore io A lim stk)

/-! ## 3. `write_stdout` -/

/-- Core contract of the compiled `signal_session_io::write_stdout(bytes)`
(`x0, x1`; `Result<(), IoError>` in `x0`), extending `SpecsPlacedBudget.writeStdoutSpecPlaced`.

The compiled function (`lib.rs:285` = `write_all_fd::<true>(1, bytes)`) calls musl `write(1, …)`
in chunks of at most `0x7fff_f000` bytes without heap allocation. Under `Syscall.standard`,
`execWrite` on fd `1` appends `TraceEvent.ofBytes .stdout chunk` and returns the count while
leaving `fs` unchanged, so the loop appends `TraceEvent.ofBytes .stdout x.bs` and returns `Ok`.

`pre` additions:
* `writeStdoutStackFloor ≤ stk`: covers the `96`-byte peak stack of the compiled loop and musl
  `write` frame.
* `x.bs.length < 2 ^ 63`: Rust slice bound (`≤ isize::MAX`), satisfied at `M6` via
  `ownedBytes_unpack` (`outCap.toNat < 2 ^ 63`).

`post` additions (all earlier conjuncts are preserved verbatim and first):
* `sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout x.bs` and `sf.fs = s0.fs` (implying the
  earlier prefix/stdout-stream conjuncts and that no `rust_alloc_failed` event is logged).
* `VmPreserved s0 sf` is added by `writeStdoutSpecPlacedSat` (`withVmPreserved`).

`WriteStdoutEnv` (`SpecBudget.lean:889`) still over-approximates allocation events (`evs = []`),
and `x0 = 0#64` is kept as a full 64-bit value. See the `errno` note on `writeFileHonestCore`. -/
@[expose] def writeStdoutHonestCore {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (WriteStdoutGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.buf ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      FitsEnv M lim st WriteStdoutEnv ∧
      writeStdoutStackFloor ≤ stk ∧ x.bs.length < 2 ^ 63⌝ ∗
      (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜WriteStdoutEnv evs ∧
        sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = s0.fs.files ∧ s0.trace <+: sf.trace ∧
        ProcessOutcome.traceStreamBytes .stdout sf.trace =
          ProcessOutcome.traceStreamBytes .stdout s0.trace ++ x.bs ∧
        sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout x.bs ∧
        sf.fs = s0.fs⌝ ∗
        (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

/-- `write_stdout` consumer contract: `writeStdoutHonestCore` with `VmPreserved s0 sf` on normal
return (`withVmPreserved`). Discharged on machine code in
`HookDischarge.CliIoFmt.WriteStdoutProof` via `PoolErrnoSplit`. -/
@[expose] def writeStdoutSpecPlacedSat {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (WriteStdoutGhost × M.σ) :=
  withVmPreserved (writeStdoutHonestCore A lim stk)

/-! ## 4. Related modules

* Idealized-hook bridges: `Cli.Main.IoHonestSpecsHook`.
* Machine-code proofs: `HookDischarge.CliIoFmt.WriteFileProof` and
  `HookDischarge.CliIoFmt.WriteStdoutProof`.
* Consumer carriers using these contracts: `Cli.SpecsPlacedBudgetSat`,
  `Cli.M24.MainIoBoundedPlacedSat`, and `Cli.Main.Proofs.M3PlacedBudgetFdSat`.
  There is no projection `MainIoPlacedSat → MainIoPlaced` because the honest `pre` is stronger;
  `post` retains every earlier conjunct verbatim.
-/

end LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs

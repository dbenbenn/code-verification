/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.LibcHooks
public import LibsignalBinary.Specifications.SignalSession.Process
public import LibsignalBinary.Specifications.SignalSession.Run
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs

@[expose] public section

set_option autoImplicit false

/-!
# One engine process of the `libsignal-cli` CLI: primitive parameter bundle (`CliHooks`)

**Trusted: definitions used by the statement.** In this file, `CliHooks` is the symbolic primitive
parameter bundle `(C, Q)` used by `signal_session_secure` (`Symbolic/Theorems/Security.lean`)
and `comp_refines_cli` (`Symbolic/Theorems/Refinement.lean`) via `RealHooksAgreeOnInput` in
`ElfBinding.lean` (the computational binary headlines in `Computational/Theorems/Main.lean`
instantiate the closed `realPEParams` bundle directly in `CliBinaryPq.lean` and
`StatementPqElf.lean`; see `Computational/docs/TRUSTED_BASE.md`).

All four `libsignal_cli_io` I/O entry points (`read_file`, `read_stdin`, `write_file`,
`write_stdout`) execute linked ELF code directly against `Syscall.standard`; the legacy proof-side
path predicates (`PathOk`, `readPath`, `pathComps`, `isUnmodelledPathComponent`, `ancestors`,
`blockingAncestor?`), result helpers (`unitResult`, `unmodelled`), and legacy I/O hook contracts
(`writeFileHook`, `writeStdoutHook`, `readFileHook`, `readStdinHook`) live in untrusted `Proofs/`:
* `LibsignalBinary/Proofs/SpecLemmas/SignalSession/IoHooksLegacy.lean`
* `LibsignalBinary/Proofs/SpecLemmas/SignalSession/CliRunFixed.lean`

## How panic externs are intercepted

`Step prog` fetches every instruction from memory, so `prog.code` plays no part in a run. Under
`cliProgElf addrs` (`overrideProgram execSyscall cliPanicOverrides addrs.panicAddrs` in
`CliBinaryPq.lean`), `addrs.panicAddrs` holds the `.symtab`-resolved entry addresses of the `18`
Rust panic symbols (`cliPanicSymbolsPlaced`), which `Program.overrides` intercepts and maps to
`SIGABRT` (`abortOnPanic Rust.panicked`); every other instruction — including `aes` and `spqr`
CPU-feature probes against the pinned auxv (`AT_HWCAP = 0x1b`) — executes directly from plain
loaded ELF memory (`ElfImage.loadState`, zero initial memory patches), and unlinked zero-word
stubs decode to `udf #0` and halt (fail closed). Proof-side placed execution
(`Placed.cliProgPlacedSig` / `cliExternsPlacedSig`) lives in untrusted
`LibsignalBinary/Proofs/Placed/CliBinaryPqPlaced.lean`.

## The I/O functions: compiled read and write paths

The CLI does all of its I/O in four `#[inline(never)]` functions of its own I/O crate,
`libsignal-cli-io` (`third_party/libsignal/libsignal-session/cli/io/`, Rust path
`libsignal_cli_io`). `libsignal-session/translation.toml` keeps `libsignal-cli-io` out of
`libsignalSessionMultiLib` and `cli/io/translation.toml` translates it separately into
`GeneratedLean.SignalSessionIoPlacedObj` (`signalSessionIoMultiLib`). All four functions execute
their linked `libsignal-cli-io` ELF bytes directly (`read_file` and `read_stdin` proved in
`LibsignalBinary/Proofs/SignalSession/CliIo/`, `write_file` and `write_stdout` proved in
`LibsignalBinary/Proofs/HookDischarge/CliIoFmt/`, DEV-CLI4, DEV-CLI8, DEV-CLI21, DEV-CLI19), with
the legacy fixed-image hook helpers kept proof-side in
`LibsignalBinary/Proofs/SpecLemmas/SignalSession/CliRunFixed.lean` and `IoHooksLegacy.lean`.
Paths are relative to the party's directory and looked up by their canonical form
(`FsState.files`), as `Process.lean` describes.

**Only `write_file` changes the files, and `openat` records it in the trace.** Across the linked
CLI code (and in the legacy `writeFileHook` helper), only `write_file` mutates `fs.files` via
`openat`/`write` (compiled `read_stdin` changes only file descriptor 0's offset, and `write_stdout`
writes only to file descriptor 1). On every `PathOk` `< 4096`-byte path call that reaches `openat`
(written or not; paths with an interior NUL or `len ≥ 4096` return `Err` before `openat`), the
engine's `openat` syscall (and legacy `writeFileHook`) appends `TraceEvent.fileChanged path` when it
creates or truncates a file, so a run segment whose trace has no such event did not call
`write_file` on a valid path and left `fs.files` as it was. The event is not output: stdout keeps
only `writeByte` events (`traceStreamBytes`), so it changes neither `outcomeOf` nor the run's
`Outcome`.

**DEV-CLI4 (machine model): I/O does not fail except as specified.** The I/O specifications
fail only where Linux / the bounded I/O crate fails on the engine's file system for these calls: a
path of `4096` bytes or more (`ENAMETOOLONG`) or containing an interior NUL byte, a path through a
regular file (`ENOTDIR`), a missing parent directory on write (`ENOENT`), a directory where a file is
expected (`EISDIR`), a regular file above `fileCapBytes` (`2^21`) on `read_file`, standard input
above `stdinCapBytes` (`2^20`) on `read_stdin`, and an out-of-memory allocation failure on a read
buffer (DEV-CLI15, DEV-CLI21; `vecOk` in `CliRunFixed.lean` in the legacy hook model). On the linked
compiled I/O paths (`cli/io/src/lib.rs`, all four executing linked ELF bytes: `read_stdin`
and `read_file` proved in `LibsignalBinary/Proofs/SignalSession/CliIo/`; `write_file` and
`write_stdout` proved in `LibsignalBinary/Proofs/HookDischarge/CliIoFmt/`, DEV-CLI19), `read_stdin`
and `read_file` enforce those same `stdinCapBytes = 2^20`, `fileCapBytes = 2^21`, and `< 4096`-byte
NUL-free stack-path bounds (mapping `ENOENT` to `Ok([])` and `EBADF` on `fd 0` to `Ok(out)`), while
`write_file` and `write_stdout` execute 0-allocation C-ABI musl `open`/`write`/`close`/`__errno_location` loops
(`< 4096`-byte NUL-free stack path check, `O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC` mode `0o666`,
`EINTR` retry, `n == 0` treated as `Err`, `close` on every exit after `open`, and `EBADF` on closed
`fd 1` treated as `Ok(())` matching `std`'s `handle_ebadf` and `read_stdin`; in `processInputs`
`fd 1` is open `.stdio` stdout). A real
kernel can also fail for other reasons (`EMFILE`, `ENOSPC`, `EIO`, a denied permission (`EACCES`; no
mode bits), a short write, a full disk
mid-commit); such a failure gives exit 2 in the real CLI, possibly after a partial commit. Effect:
the theorems say nothing about runs on which the kernel fails an I/O call in another way; the run
otherwise ends as the real one does (same exit code, stdout and files).

**DEV-CLI8 (machine model): the legacy hooked I/O model omits real read `Vec`-growth allocations.**
Compiled `libsignal-cli-io` (`read_stdin`, `read_file`, `write_file`, `write_stdout`, all four
executed directly as linked ELF code in the placed binary theorems) reads through `4096`-B stack
buffers and grows output `Vec<u8>`s on a doubling schedule up to `stdinCapBytes` / `fileCapBytes`
(DEV-CLI21) while `write_file` and `write_stdout` perform zero heap allocations, whereas the legacy
read hooks (`readFileHook`, `readStdinHook` in `CliRunFixed.lean`, outside the headline closure)
allocate a single exact-size block via `vecOk`. Legacy hook-form theorems make no claim when a
doubling allocation fails where `vecOk`'s exact-size block fits.

**DEV-CLI19 (machine model): `libsignal_cli_io` I/O executes linked ELF code.**
`read_file` and `read_stdin` execute compiled `SignalSessionIoPlacedObj` blocks proved against musl
`open`/`read`/`close`/`__errno_location` in `LibsignalBinary/Proofs/SignalSession/CliIo/`.
`write_file` and `write_stdout` (`0`-allocation C-ABI musl `open`/`write`/`close`/`__errno_location`
loops) execute linked ELF code proved against `Syscall.standard` in
`LibsignalBinary/Proofs/HookDischarge/CliIoFmt/`. The legacy `writeFileHook` and `writeStdoutHook`
definitions live in `LibsignalBinary/Proofs/SpecLemmas/SignalSession/IoHooksLegacy.lean` for
unplaced/legacy proofs outside the placed headline closure, where paths outside `PathOk` and
unreadable/unwritable caller buffers fail closed (`.Exception`).

## Free choices

`W : CliHooks` holds the symbolic primitive bundle `(C, Q)` guarded per input via
`RealHooksAgreeOnInput` in `ElfBinding.lean` (while the computational ELF-direct headlines in
`CliBinaryPq.lean` and `StatementPqElf.lean` instantiate the closed `realPEParams` bundle directly).

## Unintercepted externs

No non-panic extern is intercepted in `cliProgElf` (`CliBinaryPq.lean`; or proof-side
`cliExternsPlacedSig` in `LibsignalBinary/Proofs/Placed/CliBinaryPqPlaced.lean`):
* never intercepted: `std::sys::random::linux::hashmap_random_keys` (the CLI builds no `HashMap`)
  and `libsignal_session_rng_fill` (the CLI's coins are plain Rust, `cli/src/coins.rs`); reaching
  either halts on `udf #0` (fail closed by design);
* all `55` allocator, libc, I/O, formatting, Rust stdlib, CPU feature probe, and cryptographic
  entry points (recorded for link auditing in untrusted
  `LibsignalBinary/Proofs/Placed/CliBinaryPqPlaced.lean`) execute their linked ELF code directly.
-/


namespace CryptoVerification.SignalSession

/-! ## The free choices -/

/-- **Abstract primitive bundle** (the `W` parameter of the symbolic CLI statements in
`ElfBinding.lean` / `Binary.lean`, guarded per input against `realCliHooks`). -/
structure CliHooks where
  /-- SHA-256 compression, AES-256-CBC, X25519 (`CryptoGames.LibsignalSession.Crypto`). -/
  C : CryptoGames.LibsignalSession.Crypto
  /-- SHA-512, Kyber1024, SPQR's ML-KEM-768 (`E2E.PqxdhPrims`). -/
  Q : E2E.PqxdhPrims

end CryptoVerification.SignalSession

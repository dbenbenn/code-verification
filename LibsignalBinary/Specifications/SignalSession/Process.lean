/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Loader

@[expose] public section

set_option autoImplicit false

/-!
# The outcome of one run of a static ELF process

**Trusted in part.** See `Computational/docs/TRUSTED_BASE.md`. The binary-level theorems use
`processInputs` (via `CliProcess.lean`), while `ProcessResult` (`exited`, `aborted`) is used by
proof-side process definitions (`ProcessProofDefs.lean`).

`processInputs` constructs `Arm64.Process.ProcessInputs` with ASCII `argv` (`"libsignal-cli" :: cmd.argv`),
`stdin` on file descriptor 0, canonical working-directory-relative `files` and `dirs` (the CLI never
creates directories), an 8 MiB stack topped at `0x7fff_ffff_0000` (DEV-CLI7), `AT_HWCAP = 0x1b`
(`HWCAP_FP | HWCAP_ASIMD | HWCAP_AES | HWCAP_PMULL`, enabling ARMv8 hardware AES and SPQR `PMULL`
GF(2¹⁶) while keeping LSE atomics bit 8 `= 0`), and the engine's default `envp`, remaining auxiliary
vector fields, and `mmap` oracle (`0x6000_0000_0000` upward). Runs reaching `.Halted`,
`.OutOfMemory`, `.Exception`, or non-termination produce no `ProcessResult`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process

/-- What one terminated run produces: it exited with exit code `code` (the full `x0` of
    `exit_group`), having written `stdout` to file descriptor 1 and left the file system `fs`;
    or it aborted (`.Panicked`). -/
inductive ProcessResult where
  | exited (code : BitVec 64) (stdout : List (BitVec 8)) (fs : FsState)
  | aborted
  deriving Inhabited

namespace ProcessResult

end ProcessResult

/-- The inputs of one run: the argument vector `argv` (`argv[0]` included, ASCII), the bytes
    `stdin` on file descriptor 0, the regular files `files` and the directories `dirs` that exist
    at the start, with paths relative to the process's working directory (the party's). The
    stack is 8 MiB, Linux's default `RLIMIT_STACK`, instead of the engine's default 128 KiB
    (DEV-CLI7). Every other field is the engine's default (`ProcessInputs`); `execfn` is `[]`, so
    `AT_EXECFN` points to `""` (Linux passes the execve path); the only reader is musl's
    `__init_libc`, which uses it for `__progname` only when `argv[0]` is null, and `argv[0]` is
    always `"libsignal-cli"` here (and `__progname` is never read); `auxv.hwcap` is `0x1b` (FP
    bit 0, ASIMD bit 1, AES bit 3, and PMULL bit 4, so both `aes` 0.9.1's and SPQR's `AT_HWCAP`
    feature probes select ARMv8 hardware AES and `PMULL` GF(2¹⁶) while LSE bit 8 remains `0`); in
    particular `auxv` keeps `AuxvConfig`'s non-setuid ids and the loader sets `AT_SECURE = 0`
    (DEV-CLI6). -/
def processInputs (argv : List String) (stdin : List (BitVec 8))
    (files : List (String × List (BitVec 8))) (dirs : List String) : ProcessInputs :=
  { argv := argv.map bytesOfString
    stdin := stdin
    files := files
    dirs := dirs
    init := { stackSize := 8388608, auxv := { hwcap := 0x1b#64 } } }

end CryptoVerification.SignalSession

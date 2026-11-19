/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliRun

/-!
# Legacy I/O Path Helpers and Retired Write Hooks (`IoHooksLegacy`)

**Checked by Lean.** Proof-side path predicates (`readPath`, `pathComps`,
`isUnmodelledPathComponent`, `PathOk`, `ancestors`, `blockingAncestor?`), result combinators
(`unitResult`, `unmodelled`), and legacy write-hook contracts (`writeFileHook`, `writeStdoutHook`),
moved out of `LibsignalBinary/Specifications/SignalSession/CliRun.lean` once all four
`libsignal_cli_io` functions (`read_file`, `read_stdin`, `write_file`, `write_stdout`) were linked
directly and removed from `cliHookTablePlaced`; none of the placed binary headline statements
reference these helpers.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib

/-! ## Paths -/

/-- The path argument `(ptr, len)` of an I/O function as an `FsState.files` key: one character per
byte (`Char.ofNat`), as the engine reads a path of `openat` (`readCString`, `ISA/Eval.lean`). -/
@[expose] def readPath (m : Memory) (ptr len : BitVec 64) : String :=
  String.ofList ((m.readBytes ptr len.toNat).map fun b => Char.ofNat b.toNat)

/-- The components of path `p`: its characters split at `/` (`List.splitOn`). On a `PathOk` path
they are the segments of the engine's canonical form (`Arm64.normalizePath`). -/
@[expose] def pathComps (p : String) : List (List Char) := p.toList.splitOn '/'

/-- A component the specifications do not model: empty (a leading, trailing or doubled `/`, or the
empty path), `.` or `..`. -/
@[expose] def isUnmodelledPathComponent (c : List Char) : Bool :=
  c.isEmpty || c == ['.'] || c == ['.', '.']

/-- **The paths the I/O specifications model**: relative and canonical (every component non-empty
and neither `.` nor `..`), no NUL byte (Rust's `CString` would reject it), and no component that
`fsView` hides (`stdioPaths`, `Run.lean`), so every file a hook reads or writes is observable. The
standard streams themselves are not in the file system (`FsState.files`): the loader opens file
descriptors 0, 1, 2 as `.stdio` descriptors, and stdin's bytes are `FsState.stdin`.
On such paths the engine's canonical lookup (`FsState.files`) agrees with the way Linux resolves
them. -/
@[expose] def PathOk (p : String) : Bool :=
  (pathComps p).all fun c =>
    !isUnmodelledPathComponent c && !c.contains '\x00' && !(stdioPaths.contains (String.ofList c))

/-- The proper ancestors of `p`, shallowest first: `"a/b/c"` gives `["a", "a/b"]`; a single
component has none (its parent is the party's directory, which exists). -/
@[expose] def ancestors (p : String) : List String :=
  let cs := pathComps p
  (List.range (cs.length - 1)).map fun i => String.ofList (['/'].intercalate (cs.take (i + 1)))

/-- **The first proper ancestor of `p` that is not a directory**, with what is there: `some
(some (.file _))` (Linux: `ENOTDIR`) or `some none` (missing: `ENOENT`); `none` if every proper
ancestor is a directory. This is Linux's walk of the path's directories (`link_path_walk`). -/
@[expose] def blockingAncestor? (fs : FsState) (p : String) : Option (Option FsEntry) :=
  ((ancestors p).find? fun q => match fs.files q with | some .dir => false | _ => true).map
    fs.files

/-! ## Results -/

/-- Return `Ok(())` (`x0 := 0`) or `Err(IoError)` (`x0 := 1`) of a `Result<(), IoError>`
(measured on the compiled `write_file` / `write_stdout`: `cset w0, ne`). -/
@[expose] def unitResult (ok : Bool) : State → State :=
  retHook fun s => s.writeReg64 .x0 (if ok then 0#64 else 1#64)

/-- Stop with an `.Exception` (`outcomeOf` is then `none`): the hook's inputs are outside what it
models. -/
@[expose] def unmodelled (msg : String) (s : State) : State := s.setStatus (.Exception msg)

/-! ## Legacy write I/O hooks (`libsignal-cli-io`) -/

/-- `libsignal_cli_io::write_file(path: &str = (x0, x1), bytes: &[u8] = (x2, x3))
-> Result<(), IoError>` (`x0`): 0-allocation C-ABI musl `open`/`write`/`close`/`__errno_location`
loop (`O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC`, mode `0o666`, `< 4096`-byte NUL-free stack path
copy, `EINTR` retry on `open` and `write`, `n == 0` treated as `Err`, `close` on every exit after
`open`), i.e. create or truncate, then write all of `bytes`.
* `.Exception` if the path or the bytes are not readable, or (after the length / interior-NUL
  check) the path is not `PathOk`;
* path byte length `≥ cliPathMaxBytes` (`4096`, `PATH_MAX`) or containing an interior `0` byte:
  `Err` (`unitResult false`, before `openat` and before emitting `TraceEvent.fileChanged`);
* a proper ancestor is not a directory (a regular file: `ENOTDIR`; missing: `ENOENT`, the CLI
  never creates a directory): `Err`, nothing changes in `fs.files`;
* `fs.files path` is a directory: `Err` (`EISDIR`), nothing changes in `fs.files`;
* otherwise (a regular file, or nothing): `fs.files path := file bytes`, `Ok`.
In the three `PathOk` `< 4096`-byte cases it first appends the event `TraceEvent.fileChanged p` to
the trace (not output; module docstring). -/
@[expose] def writeFileHook (s : State) : State :=
  let ptr := s.readReg64 .x0
  let len := s.readReg64 .x1
  let buf := s.readReg64 .x2
  let n := s.readReg64 .x3
  if !(s.mem.canRead ptr len.toNat && s.mem.canRead buf n.toNat) then
    unmodelled "write_file: unreadable path or bytes" s
  else
    let raw := s.mem.readBytes ptr len.toNat
    if cliPathMaxBytes ≤ len.toNat || raw.contains 0#8 then
      unitResult false s
    else
      let p := readPath s.mem ptr len
      if !PathOk p then unmodelled "write_file: path outside the model" s
      else
        let s := s.appendTrace [.fileChanged p]
        match blockingAncestor? s.fs p, s.fs.files p with
        | some _, _ => unitResult false s
        | none, some .dir => unitResult false s
        | none, _ =>
          unitResult true (s.setFs (s.fs.setFile p (some (.file (s.mem.readBytes buf n.toNat)))))

/-- `libsignal_cli_io::write_stdout(bytes: &[u8] = (x0, x1)) -> Result<(), IoError>` (`x0`):
0-allocation C-ABI musl `write(1, …)` / `__errno_location` loop (`EINTR` retry, `n == 0` treated
as `Err`, and `EBADF` on a closed file descriptor 1 treated as `Ok(())` matching `std`'s
`handle_ebadf` and `read_stdin`; in `processInputs` file descriptor 1 is open `.stdio` stdout),
i.e. the engine's `write(1, …)`, which appends the bytes to the trace as stdout events
(`TraceEvent.ofBytes .stdout`) and leaves the file system unchanged. `Ok`.
`.Exception` if the bytes are not readable. -/
@[expose] def writeStdoutHook (s : State) : State :=
  let buf := s.readReg64 .x0
  let n := s.readReg64 .x1
  if !s.mem.canRead buf n.toNat then unmodelled "write_stdout: unreadable bytes" s
  else unitResult true (s.appendTrace (TraceEvent.ofBytes .stdout (s.mem.readBytes buf n.toNat)))

end CryptoVerification.SignalSession

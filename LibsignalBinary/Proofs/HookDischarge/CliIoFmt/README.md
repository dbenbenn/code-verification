# `CliIoFmt`: CLI Output I/O & Rust Formatting Machine-Code Proofs

Untrusted (`**Checked by Lean.**`) ARM64 `MultiPlacedLib` machine-code proofs and `mallocng`
(`RustCliAllocBudget`) bridges for the four non-crypto I/O and formatting routines executed
directly by the `libsignal-cli` ELF (`cliElfBytes`):

| Routine | Object blocks | Peak stack | Heap events |
|---|---|---:|---|
| `libsignal_cli_io::write_stdout` | `signalSessionIoMultiLib` block `2` (`184` B) + `muslSysPlacedLib` block `7` (`write`) | `96` B | none (`[]`) |
| `libsignal_cli_io::write_file` | `signalSessionIoMultiLib` block `1` (`304` B) + `muslSysPlacedLib` blocks `4, 7, 1, 0` (`open`, `write`, `close`, `__errno_location`) | `4,304` B | none (`[]`) |
| `core::fmt::write` | `VerifiedLibraries.RustStd.coreMultiLib` block `0` (`436` B) + `coreFmtMultiLib` + `allocMultiLib` blocks `1, 2, 6, 7` | `4,544` B | `fmtWriteKnownEvents` |
| `alloc::fmt::format::format_inner` | `VerifiedLibraries.RustStd.allocMultiLib` block `3` (`432` B) + `coreMultiLib` block `0` + `allocMultiLib` blocks `1, 2, 6, 7` | `4,640` B | `formatInnerKnownEvents` |

`write_stdout` and `write_file` prove Linux `Syscall.standard` (`openat`, `write`, `close`)
refinement directly against `IoHonestSpecs` (matching `read_stdin` and `read_file` in
`LibsignalBinary/Proofs/SignalSession/CliIo/`). `core::fmt::write` and
`alloc::fmt::format::format_inner` prove memory, stack, and `RustCliAllocBudget` safety for all
reachable CLI formatting templates and `Display::fmt` call sites.

## Module Layout

- **`MuslWrite.lean`, `WriteStdoutSteps.lean`, `WriteStdoutProof.lean`**: musl `write(1, ...)`
  chunked-loop (`0x7fff_f000`) and `write_stdout` proofs, bridging `PoolErrnoSplit` user-VA bounds
  into `IoHonestSpecs.writeStdoutSpecPlacedSat`.
- **`WriteFileOpenSteps.lean`, `WriteFileLoop.lean`, `WriteFileProof.lean`**: `< 4096`-byte path
  NUL-scan, `openat` (`O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC`, `0o666`), `__errno_location` error
  exits, chunked `write` loop up to `Arm64.FS_SAFE_MAX_FILESIZE`, and `close`, discharging
  `writeFileSpecPlacedSatClamped`.
- **`FmtPlacedObj.lean`**: adapts `LibsignalBinary.Heap.RustCliAllocBudget` to
  `VerifiedLibraries.RustStd.RustAllocBudget` and provides 1- and 2-hop branch-stub lifts.
- **`FmtWriteProof.lean` & `FormatInnerProof.lean`**: general and call-site-specialized
  `core::fmt::write` and `alloc::fmt::format::format_inner` proofs (0-arg templates, `u8`/`u32`/
  `&str` `Display::fmt`, and `<ProtocolAddress as Display>::fmt` `"{}.{}"`).
- **`CliIoFmt.lean`**: umbrella module re-exporting all 9 modules.

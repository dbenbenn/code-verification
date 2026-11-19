# `CryptoSha512`: `sha2::sha512::compress512` ARM64 Machine-Code Proofs

Untrusted (`**Checked by Lean.**`) pure FIPS 180-4 SHA-512 reference specification, NIST vector
checks, and layout-generic ARM64 `Obj.PlacedLib` machine-code proofs for
`sha2::sha512::compress512` (`sha2 0.11.0`, compiled with `--cfg sha2_backend="soft"` under pinned
`rustc 1.98.1`), executed directly by the `libsignal-cli` ELF (`cliElfBytes`).

## Target Routine Summary

- **Symbol**: `_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512` (`9,652` B = `2,413` AArch64 words,
  `.rodata` `K64` `640` B = `80` LE `u64` words).
- **Relocations**: `0x48`/`0x4c` → `K64` (`0` external calls; proofs cover both unrelaxed
  `ADRP`+`ADD` and linker-relaxed `NOP`+`ADR`).
- **Resources**: `256`-byte stack frame (`0` bytes touched when `x2 = 0`); saves/restores
  `x19..x28, x30`; leaves `x29`, `sp`, SIMD/FP `v0..v31`, `tpidr_el0`, `heapBreak`, `anonMaps`,
  and syscall `trace` untouched; zero heap allocations.

## Module Layout

- **Pure FIPS 180-4 SHA-512 & vectors**: `Sha512Ref.lean` (`sha512K`, 80-round schedule and
  `sha512CompressState`), `Sha512Cells.lean` (64-bit `rev64` and 128-byte block / 640-byte `K64` /
  256-byte frame bridges), `Sha512RoundDefs.lean` (linear recurrences and step-folding lemmas), and
  `Sha512Math.lean` (NIST FIPS 180-4 `#guard` vectors and compatibility with `SignalPqxdh.sha512Ref`).
- **`Obj.PlacedLib` extraction & loop proof**: `Compress512Bytes.lean` (hex-embedded `.text` bytes
  from `RustCrypto/hashes`, MIT/Apache-2.0), `Compress512Code.lean` (`compress512Lib`, opcode
  exclusion), `Compress512Fetch.lean` (placed instruction fetches including relaxed/unrelaxed `K64`
  addressing), `Compress512Step.lean` (single-block 80-round loop body), and `Compress512Loop.lean`
  (multi-block induction, prologue/epilogue, and `cbz x2` fast exit).
- **Consumer bridges**: `StepsLift.lean` (`ProcessFieldsPreserved` / `VmPreserved` lifts),
  `Compress512.lean` (CLI and PQXDH consumer contracts), and `CryptoSha512.lean` (umbrella import).

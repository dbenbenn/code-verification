# `CryptoSha256`: `sha2::compress256` & `libcrux_hmac::hmac` Machine-Code Proofs

Untrusted (`**Checked by Lean.**`) ARM64 machine-code proofs for the SHA-256 and HMAC-SHA-256
routines executed directly by the `libsignal-cli` ELF (`cliElfBytes`):

- `sha2::sha256::compress256` (`sha2 0.11.0`, `1,909` instructions / `7,636` B + 256-byte `.rodata`
  `K32`, `176`-byte stack frame, compiled with `--cfg sha2_backend="soft"` under pinned `rustc 1.98.1`).
- `libcrux_hmac::hmac` (`libcrux-hmac 0.0.8` + `libcrux-sha2 0.0.8` HACL SHA-256 helpers, `w0 = 0`
  `Algorithm::Sha256` arm, `3,153` instructions / `12,612` B total).

Both routines are proved against the identical FIPS 180-4 SHA-256 block-compression function
`sha256CompressState` (wrapping `Sha256Ref.sha256CompressBlock`), matching `CryptoGames.HMAC`'s
`sha256With` and `hmacWith`.

## Module Layout

- **Pure FIPS 180-4 SHA-256 reference & vectors**: `Sha256Ref.lean` (round constants `sha256K`,
  schedule, and compression), `Sha256Cells.lean` (32-bit cell and 176-byte frame lemmas),
  `Sha256RoundDefs.lean` (linear recurrence and step-folding lemmas), and `Sha256Math.lean` (NIST
  FIPS 180-4 SHA-256 and RFC 4231 HMAC-SHA-256 `#guard` vectors plus state-memory bridges).
- **`sha2::sha256::compress256` binary proofs**: `Compress256Bytes.lean`, `Compress256Code.lean`,
  `Compress256Fetch.lean` (`Obj.PlacedLib` extraction with `K32` relocation and opcode-exclusion
  checks), `Compress256Step.lean` (single-block 64-round stepping), `Compress256Loop.lean`
  (multi-block loop + `cbz x2` fast exit), `StepsLift.lean` (`ProcessFieldsPreserved` / `VmPreserved`),
  and `Compress256.lean` (stacked consumer contract bridges with `≥ 176` B stack slack).
- **`libcrux_sha2::hacl` & `libcrux_hmac::hmac` binary proofs**: `HaclPure.lean` (pure streaming
  equivalence to `CryptoGames.HMAC.sha256With`), `HaclCode.lean`, `HaclUpdateStep.lean`,
  `HaclSha256.lean` (`sha256_init`, `sha256_update`, `sha256_update_nblocks`, `sha256_update_last`,
  `sha256_finish`, `hash_256`), `LibcruxHmacStep.lean`, and `LibcruxHmac.lean` (including `u32`
  length-overflow panic paths and the 7 `mallocng` alloc/dealloc calls + `memcpy`).

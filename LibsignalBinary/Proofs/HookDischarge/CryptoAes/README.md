# `CryptoAes`: `signal_crypto::aes_cbc` & ARMv8 Hardware AES Machine-Code Proofs

Untrusted (`**Checked by Lean.**`) ARM64 machine-code and algebraic equivalence proofs for
`signal_crypto::aes_cbc::aes_256_cbc_encrypt` and `signal_crypto::aes_cbc::aes_256_cbc_decrypt`
as compiled by pinned `rustc 1.98.1` (`aes 0.9.1` with `aes::autodetect::Aes256` and `cpufeatures`).

Without `--cfg aes_backend="soft"`, `aes::autodetect::Aes256` lazily queries `AT_HWCAP` via
`cpufeatures::aarch64::getauxval_hwcap` (musl `getauxval(16)`), caches `(hwcap & 0x18) != 0` in the
1-byte `.data` static `aes::armv8::features::features_aes::STORAGE`, and dispatches to ARMv8
hardware AES (`AESE`/`AESD`/`AESMC`/`AESIMC`, including 17-block parallel `decrypt_par<15, U17>`)
when `STORAGE == 1` (the path selected at `AT_HWCAP = 0x1b`, DEV-CLI10) or to the 64-bit 4-block
`aes::soft::fixslice` (`fixslice64`) fallback when `STORAGE == 0`. Both backends are proved
equivalent to the trusted FIPS 197 specification `CryptoGames.AES256.{aes256Enc, aes256Dec}`
(`LibsignalBinary/Specifications/CryptoGames/AEAD/Aes256.lean`).

## Module Layout

- **FIPS 197 specification & vectors**: `Spec/Aes256.lean` (re-exporting `CryptoGames.AES256`),
  `Aes256Vectors.lean` (FIPS 197 Appendix C.3, NIST SP 800-38A F.2.5, and `signal_crypto::aes_cbc`
  `#guard` checks), and `Aes256Roundtrip.lean` (`aes256Dec k (aes256Enc k b) = b`,
  `aes256Enc k (aes256Dec k b) = b`, and CBC-PKCS#7 round-trip corollaries).
- **64-bit Fixslice fallback (`Fixslice64/`)**: pure `BitVec 64` model (`Model.lean`), algebraic
  equivalence to 4-lane FIPS 197 (`Equiv.lean`), and placement-generic machine-code proofs
  (`Bitslice.lean`, `SboxCode.lean`, `MixCode.lean`, `KsHelpers.lean`, `KeySchedule.lean`,
  `BlockEnc.lean`, `BlockDec.lean`).
- **ARMv8 hardware AES & CPU feature detection (`Armv8/`)**:
  - `Armv8/Defs.lean`, `Armv8/Pure/OpsEquiv.lean`, `Armv8/Pure/CipherEquiv.lean`: algebraic
    identities linking `Arm64.evalAesOp` (`.aese`, `.aesd`, `.aesmc`, `.aesimc`) to FIPS 197
    `SubBytes`/`ShiftRows`/`MixColumns`, the Equivalent Inverse Cipher (`inv_expanded_keys<15>`),
    and 17-block parallel decryption (`armv8DecryptPar17`).
  - `Armv8/{GetauxvalCode,GetauxvalHwcap,KeyScheduleAux,KeySchedule,InvExpand,BlockEnc,BlockDec,BlockDecPar17Aux,BlockDecPar17Rounds,BlockDecPar17,DropDecryptor}.lean`:
    placement-generic `subroutine_ok` proofs for `__errno_location`, non-`AT_SECURE` `getauxval`,
    `cpufeatures::aarch64::getauxval_hwcap`, `features_aes::init_get::init_inner`, key expansion,
    block encryption/decryption, 17-block parallel decryption, and `Decryptor` drop zeroization.
- **CBC-PKCS#7 entrypoints (`CbcEnc/`, `CbcDec/`, `CbcEncrypt.lean`, `CbcDecrypt.lean`)**:
  end-to-end `subroutine_ok` and `RustCliAllocBudget` (`mallocng`) proofs for
  `aes_256_cbc_encrypt` and `aes_256_cbc_decrypt` across lazy `STORAGE = 0xff` initialization,
  `STORAGE = 1` (ARMv8 hardware AES), and `STORAGE != 1` (`fixslice64` fallback).

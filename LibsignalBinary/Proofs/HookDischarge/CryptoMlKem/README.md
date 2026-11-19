# `CryptoMlKem`: `libcrux-ml-kem` ARM64 Machine-Code Proofs

Untrusted (`**Checked by Lean.**`) ARM64 machine-code verification (`Obj.MultiPlacedLib`) of the
7 `libcrux-ml-kem` `0.0.10` (with monomorphized `libcrux-sha3` `0.0.10`) entry points executed
directly by the `libsignal-cli` ELF (`cliElfBytes`):

1. `libcrux_ml_kem::mlkem1024::kyber::encapsulate` (`kemEncaps`)
2. `libcrux_ml_kem::mlkem1024::kyber::decapsulate` (`kemDecaps`)
3. `libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes::from_seed` (`mlkemFromSeed`)
4. `libcrux_ml_kem::mlkem768::incremental::encapsulate1` (`mlkemEncaps1`)
5. `libcrux_ml_kem::mlkem768::incremental::encapsulate2` (`mlkemEncaps2`)
6. `libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key` (`mlkemDecaps`)
7. `libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes` (`mlkemValidatePk`)

All 7 entry points target the trusted pure FIPS 202 / FIPS 203 / Round-3 Kyber-1024 specifications
in `LibsignalBinary/Specifications/CryptoGames/KEM/MlKem.lean` (`CryptoGames.MLKEM`).

## Committed Object Bundle (Provenance & Licenses)

- **`MlKemPlacedObj.bin`** (`235,352` bytes, loaded by `PlacedObjDefs.lean` via `include_bytes%`):
  extracted from the pinned `rustc 1.98.1` (`aarch64-unknown-linux-musl`, AdvSIMD/NEON enabled)
  build of `third_party/libsignal/libsignal-session`. Contains `28` `.text.*` blocks (`234,048` B /
  `58,512` AArch64 instructions) and `11` read-only `.rodata` constants (`ZETA_TABLE`, `KECCAK_RC`,
  and `9` deduplicated 16-byte NEON constants) from `libcrux-ml-kem 0.0.10` and `libcrux-sha3 0.0.10`
  (`Apache-2.0`), plus `4` stock `musl 1.2.5` (`MIT`) memory-operation blocks (`memcpy`, `memset`,
  `bcmp`, `memcmp`), assembled as `mlkemMultiLib : Obj.MultiPlacedLib` (`32` blocks, `58,690`
  instruction words, zero heap allocations). Verified against the linked `libsignal-cli` ELF via
  `MultiPlacedLib.checkInElf`.

## Termination & `SampleNTT` (`DEV-CLI22`)

- `validate_pk_bytes` (`B21`, `5,824` B stack) and `encapsulate2` (`B20`, `6,128` B stack) have
  bounded loops and satisfy unconditional `subroutine_ok`.
- The 5 matrix-generating entry points (`from_seed`, `encapsulate1`, `decapsulate_compressed_key`,
  `kyber::encapsulate`, `kyber::decapsulate`; stack budgets `18,304`–`35,968` B including
  `-fstack-clash-protection` probes, all within `65,536` B) run `libcrux-ml-kem`'s unbounded
  `SampleNTT` (`sample_from_xof`) rejection loop over `SHAKE-128(ρ ‖ [j, i])`. For each of these 5
  entry points, the proofs establish both:
  1. **Unconditional `safe_subroutine_ok`** across all inputs (never faults; whenever a call
     returns, its output matches the FIPS 203 / Kyber-1024 spec); and
  2. **Per-input `*Terminates → subroutine_ok`**, attributing any non-termination solely to a
     34-byte `SHAKE-128` matrix seed that never yields 256 samples `< 3329` (see `DEV-CLI22` in
     `Computational/docs/DEVIATIONS.md`).

## Module Layout

- **Object bundle & SIMD base**: `PlacedObjDefs.lean`, `PlacedCodeBase.lean`, `RoTables.lean`,
  `SimdSteps.lean`, and `Layer0/` (`memcpy`/`memset`/`bcmp`, constant-time comparisons/selects,
  portable deserializers, `EncapsState::to_bytes`).
- **Specifications & KATs (`Spec/`)**: re-exports of `CryptoGames.MLKEM` / FIPS 202 Keccak,
  implementation differential KATs (`Spec/MlKemKat.lean`, generator `Spec/kat_gen/`), and official
  NIST FIPS 203 ACVP + Round-3 Kyber-1024 KATs (`Spec/MlKemOfficialKat.lean`, generator
  `Spec/official_kat_gen/`).
- **Dual-lane NEON Keccak (`Keccak/`)**: proofs of `load_block`, `squeeze2`, and `keccak2`
  (SHA3-256×2, SHA3-512×2, SHAKE-256×2) plus inlined `SHAKE-128×2` absorb/squeeze steps.
- **Ring, NTT, CBD, sampling, & codecs (`Poly/`)**: bit-exact NEON equivalence proofs for Barrett
  and Montgomery reductions, NTT / inverse NTT layers, base multiplication, `compress`/`decompress`,
  `serialize`/`deserialize`, `cbd2`, and `SampleNTT` rejection sampling.
- **Entrypoint machine proofs (`Mlkem768/` & `Mlkem1024/`)**: segmented `subroutine_ok` and
  `safe_subroutine_ok` proofs for all 7 entry points.
- **Consumer bridges**: `ConsumerBridgesBase.lean`, `ConsumerBridges.lean`, `MlKemEncaps2Fips.lean`,
  and `MlKemCorrectProofs.lean` (including `mlkem768Incremental_encaps2_of_encaps1` showing that on
  every well-formed `encaps1` state, `libcrux`'s NEON `encapsulate2` matches textbook FIPS 203 over
  $\mathbb{Z}_{3329}$).

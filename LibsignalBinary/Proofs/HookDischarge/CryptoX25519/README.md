# `CryptoX25519`: `x25519-dalek` ARM64 Machine-Code Proofs

Untrusted (`**Checked by Lean.**`) ARM64 machine-code and RFC 7748 mathematical equivalence proofs
for the two `x25519-dalek` `3.0.0` entry points executed directly by the `libsignal-cli` ELF
(`cliElfBytes`):

1. `<x25519_dalek::x25519::PublicKey as From<&StaticSecret>>::from` (`17` insns, `1,904` B peak stack)
2. `<x25519_dalek::x25519::StaticSecret>::diffie_hellman` (`13` insns, `1,808` B peak stack)

Both entry points target the trusted RFC 7748 functions `x25519PubFromSecretRef` and `x25519Ref`
in `LibsignalBinary/Specifications/CryptoGames/X25519/X25519Ref.lean`, with zero heap allocations
and zero `SVC` / `MSR TPIDR_EL0` instructions across all 19 blocks in the transitive call closure.

## Committed Object Bundle (Provenance & Licenses)

- **`CryptoX25519PlacedObj.bin`** (`39,308` bytes, loaded by `PlacedObjDefs.lean` via `include_bytes%`):
  extracted from the pinned `rustc 1.98.1` (`aarch64-unknown-linux-musl`) build of
  `third_party/libsignal/libsignal-session`. Contains `19` `.text.*` blocks (`2,127` words =
  `8,508` B) and `3` `.rodata` sections (`30,800` B: `FieldElement51::ONE`, `a24 = 121666`, and
  `ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN`) from `x25519-dalek 3.0.0` (`BSD-3-Clause`) and
  `curve25519-dalek 5.0.0` (`BSD-3-Clause`), assembled as `x25519CliMultiLib : Obj.MultiPlacedLib`
  and verified against the linked `libsignal-cli` ELF via `MultiPlacedLib.checkInElf`.

## Module Layout

- **Object bundle & reference spec**: `PlacedObjDefs.lean`, `PlacedCodeBase.lean`, and
  `X25519Ref.lean` (re-exporting the RFC 7748 specification).
- **Algebraic & curve proofs (`Shared51/Math/`, `MontgomeryLadder.lean`, `PubFromSecretMath.lean`)**:
  field arithmetic over $\mathbb{F}_{2^{255}-19}$, Edwards and quadratic-twist group laws,
  255-step Kummer-line Montgomery ladder invariant uniformly on $E(\mathbb{F}_p)$ and
  $E'(\mathbb{F}_p)$, birational equivalence between clamped Edwards basepoint multiplication and
  `x25519Ref sk 9`, DH commutativity, and characterization of all-zero outputs via `lowOrderUs`.
- **ARM64 block proofs (`Shared51/`, `DiffieHellmanProof.lean`, `PubFromSecretProof.lean`)**:
  machine-code proofs for all 19 relocatable blocks (`subtle::black_box::<u8>`, `FieldElement51`,
  `Scalar::as_radix_16`, `LookupTable<AffineNielsPoint>`, `EdwardsPoint` / `MontgomeryPoint`
  operations, and the two `x25519_dalek` entry points).
- **Consumer bridges**: `ConsumerBridges.lean` and `Phase4GhostHooks.lean` (`ProcessFieldsPreserved`,
  `VmPreserved`, `keepsFs`, and `MultiPlacedLib.subroutineOk` contracts wired into the CLI proofs).

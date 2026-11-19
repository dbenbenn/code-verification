# Official NIST KAT generator for the ML-KEM-768 / Kyber-1024 specs

`gen_official_kat.py` writes `../MlKemOfficialVectors.lean`. `../MlKemOfficialKat.lean` checks those
vectors with `#guard` against the trusted `CryptoGames.MLKEM` definitions
(`LibsignalBinary/Specifications/CryptoGames/KEM/MlKem.lean`). `../kat_gen/` takes its vectors from
`libcrux-ml-kem` 0.0.10, the library linked into the binary; these come from NIST instead.

| Vectors | Source |
|---|---|
| ML-KEM-768 `keyGen` (25 cases) | [ACVP-Server `v1.1.0.43`](https://github.com/usnistgov/ACVP-Server/tree/975de31eb83d87039ec88934fdc47d8c312b892d/gen-val/json-files) `ML-KEM-keyGen-FIPS203/internalProjection.json` |
| ML-KEM-768 `encapsulation` (25), `decapsulation` (10), `encapsulationKeyCheck` (10) | same tag, `ML-KEM-encapDecap-FIPS203/internalProjection.json` |
| Kyber-1024 Round 3, counts 0–9 | `KAT/kyber1024/PQCkemKAT_3168.rsp` in the NIST Round 3 submission [`Kyber-Round3.zip`](https://csrc.nist.gov/CSRC/media/Projects/post-quantum-cryptography/documents/round-3/submissions/Kyber-Round3.zip) |

The script pins the SHA-256 of every download (and of the `.rsp` inside the zip) and refuses a
mismatch.

The `.rsp` file records only each case's 48-byte DRBG seed. To get the inputs, the script re-runs
the NIST `rng.c` AES-256 CTR DRBG and recovers what `PQCgenKAT_kem.c` drew from `randombytes`: `d`
and `z` for the key pair, and the 32 bytes passed to `crypto_kem_enc`. It checks that `z` is the last
32 bytes of the official `sk`.

To regenerate (needs network access and the `cryptography` Python package):

```sh
cd LibsignalBinary/Proofs/HookDischarge/CryptoMlKem/Spec/official_kat_gen
python3 gen_official_kat.py --cache /tmp/mlkem-kat-cache > ../MlKemOfficialVectors.lean
```

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem

/-!
# Round-3 CRYSTALS-Kyber-1024 Key Generation and Noise-Explicit K-PKE Failure Specification

**Trusted: definitions used by the statement.** Extends `CryptoGames.MLKEM`
(`LibsignalBinary/Specifications/CryptoGames/KEM/MlKem.lean`) with Round-3 CRYSTALS-Kyber-1024 key
generation (`kyber1024KeyPairWith`, `kyber1024KeyPair`, and the `UInt8` adapter
`kyber1024KemKeyGen`, matching `libcrux_ml_kem::mlkem1024::portable::kyber_generate_key_pair` and
the official Round-3 NIST `PQCkemKAT_3168.rsp` vectors) together with the single noise-explicit
honest K-PKE decryption-failure predicate `kyber1024KpkeFailsWith` and real `SHAKE-256` noise
extractors (`kyber1024RealNoiseKG`, `kyber1024RealNoiseEnc`) read by `SignalPqxdh.KyberNoiseGap`
(`Computational/Specifications/Assumptions/Kyber1024Correct.lean`). See
`Computational/docs/TRUSTED_BASE.md` and `Computational/docs/DEVIATIONS.md` (DEV-PQ21).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoGames.MLKEM

open CryptoGames.SHA3 (sha3_256List sha3_512List shake256List)

/-! ### Round-3 CRYSTALS-Kyber-1024 Key Generation (`K = 4, η_1 = 2`) -/

/-- `mlkem1024::kyber::generate_key_pair` (`(pk [1568B], sk [3168B])`) parameterized by `sampler`.
Models Round-3 CRYSTALS-Kyber-1024 (`Kyber v3.02` Algorithms 4 and 7; `libcrux` `variant::Kyber`):
expands `(ρ, σ) = SHA3-512(d)` without the FIPS 203 domain-separation byte `k = 4`, samples `Â` via
`sampleMatrixWith sampler 4 ρ true`, samples `s, e` via `sampleVecCbd2`, and packs
`pk = ByteEncode_12(t̂) ‖ ρ` (`1568` bytes) and `sk = ByteEncode_12(ŝ) ‖ pk ‖ SHA3-256(pk) ‖ z`
(`3168` bytes). -/
def kyber1024KeyPairWith (sampler : List (BitVec 8) → Poly)
    (seed64 : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) :=
  let d := seed64.take 32
  let z := (seed64.drop 32).take 32
  let g := sha3_512List d
  let rho := g.take 32
  let sigma := (g.drop 32).take 32
  let aMat := sampleMatrixWith sampler 4 rho true
  let sHat := (sampleVecCbd2 4 sigma 0).map polyNtt
  let eHat := (sampleVecCbd2 4 sigma 4).map polyNtt
  let tHat : Array Poly := Array.ofFn (n := 4) fun ⟨i, _⟩ =>
    polyAdd (vecDotNtt 4 (aMat.getD i #[]) sHat) (eHat.getD i zeroPoly)
  let skPke := ((List.range 4).map fun i => byteEncode 12 (sHat.getD i zeroPoly)).flatten
  let pk2 := ((List.range 4).map fun i => byteEncode 12 (tHat.getD i zeroPoly)).flatten
  let pk := pk2 ++ rho
  let hPk := sha3_256List pk
  (pk, skPke ++ pk ++ hPk ++ z)

/-- Closed Round-3 CRYSTALS-Kyber-1024 key generation (`List (BitVec 8)` view), normalizing the
input seed to 64 bytes via `toByteVec 64` and the output `(pk, sk)` to `(1568B, 3168B)` via
`toByteVec`, using the same unbounded `sampleNtt` matrix sampler as `kyber1024Encaps` and
`kyber1024Decaps`. -/
noncomputable def kyber1024KeyPair (seed64 : List (BitVec 8)) :
    List (BitVec 8) × List (BitVec 8) :=
  let (pk, sk) := kyber1024KeyPairWith sampleNtt (toByteVec 64 seed64).toList
  ((toByteVec 1568 pk).toList, (toByteVec 3168 sk).toList)

/-- `UInt8` byte-list adapter for Round-3 CRYSTALS-Kyber-1024 key generation (`List UInt8 →
List UInt8 × List UInt8`), matching `SignalPqxdh.Primitives.kemKeyGen` and
`CryptoVerification.E2E.UnreachedPqxdhPrimitives.kemKeyGen` with exact wire lengths
`(1568, 3168)`. -/
noncomputable def kyber1024KemKeyGen (seed : List UInt8) : List UInt8 × List UInt8 :=
  let (pk, sk) := kyber1024KeyPair (seed.map UInt8.toBitVec)
  (pk.map UInt8.ofBitVec, sk.map UInt8.ofBitVec)

/-! ### Noise-Explicit Honest K-PKE Failure Event (`kyber1024KpkeFailsWith`) -/

/-- Real `SHAKE-256` `CBD_2` input blocks (`8 × 128` bytes: nonces `0..3` for `s`, `4..7` for `e`)
derived in `kyber1024KeyPairWith` from `σ = SHA3-512(seed64[0..32])[32..64]`. -/
def kyber1024RealNoiseKG (seed64 : List (BitVec 8)) (i : Fin 8) : List (BitVec 8) :=
  let sigma := ((sha3_512List (seed64.take 32)).drop 32).take 32
  shake256List 128 (sigma ++ [BitVec.ofNat 8 i.val])

/-- Real `SHAKE-256` `CBD_2` input blocks (`9 × 128` bytes: nonces `0..3` for `r`, `4..7` for `e_1`,
`8` for `e_2`) derived in `kyber1024EncapsWith` from `pk1568` and `rand32` via
`m = SHA3-256(rand32[0..32])` and `coins = SHA3-512(m ‖ SHA3-256(pk1568[0..1568]))[32..64]`. -/
def kyber1024RealNoiseEnc (pk1568 rand32 : List (BitVec 8)) (j : Fin 9) : List (BitVec 8) :=
  let m := sha3_256List (rand32.take 32)
  let hPk := sha3_256List (pk1568.take 1568)
  let coins := ((sha3_512List (m ++ hPk)).drop 32).take 32
  shake256List 128 (coins ++ [BitVec.ofNat 8 j.val])

/-- Single noise-explicit Round-3 CRYSTALS-Kyber-1024 K-PKE honest decryption-failure predicate,
used identically for both worlds of `SignalPqxdh.KyberNoiseGap`: runs key generation from `seed64`
with explicit `CBD_2` byte blocks `nKG` (`0..3` for `s`, `4..7` for `e`), encrypts
`m = SHA3-256(rand32[0..32])` under the resulting `pk` with explicit `CBD_2` byte blocks `nEnc`
(`0..3` for `r`, `4..7` for `e_1`, `8` for `e_2`), and tests whether `indCpaDecrypt 4 11 5` fails
to recover `m`. -/
def kyber1024KpkeFailsWith (sampler : List (BitVec 8) → Poly)
    (seed64 rand32 : List (BitVec 8))
    (nKG : Fin 8 → List (BitVec 8)) (nEnc : Fin 9 → List (BitVec 8)) : Bool :=
  let d := seed64.take 32
  let rho := (sha3_512List d).take 32
  let aMat := sampleMatrixWith sampler 4 rho true
  let sHat : Array Poly := Array.ofFn (n := 4) fun ⟨i, hi⟩ =>
    polyNtt (samplePolyCbd2 (nKG ⟨i, by omega⟩))
  let eHat : Array Poly := Array.ofFn (n := 4) fun ⟨i, hi⟩ =>
    polyNtt (samplePolyCbd2 (nKG ⟨4 + i, by omega⟩))
  let tHat : Array Poly := Array.ofFn (n := 4) fun ⟨i, _⟩ =>
    polyAdd (vecDotNtt 4 (aMat.getD i #[]) sHat) (eHat.getD i zeroPoly)
  let skPke := ((List.range 4).map fun i => byteEncode 12 (sHat.getD i zeroPoly)).flatten
  let pk := ((List.range 4).map fun i => byteEncode 12 (tHat.getD i zeroPoly)).flatten ++ rho
  let m := sha3_256List (rand32.take 32)
  let tHatEnc : Array Poly := Array.ofFn (n := 4) fun ⟨i, _⟩ =>
    byteDecodeMod 12 ((pk.drop (384 * i)).take 384)
  let rhoEnc := (pk.drop 1536).take 32
  let aTrans := sampleMatrixWith sampler 4 rhoEnc false
  let rHat : Array Poly := Array.ofFn (n := 4) fun ⟨i, hi⟩ =>
    polyNtt (samplePolyCbd2 (nEnc ⟨i, by omega⟩))
  let e1 : Array Poly := Array.ofFn (n := 4) fun ⟨i, hi⟩ =>
    samplePolyCbd2 (nEnc ⟨4 + i, by omega⟩)
  let e2 : Poly := samplePolyCbd2 (nEnc ⟨8, by decide⟩)
  let uVec : Array Poly := Array.ofFn (n := 4) fun ⟨i, _⟩ =>
    polyAdd (polyInvNtt (vecDotNtt 4 (aTrans.getD i #[]) rHat)) (e1.getD i zeroPoly)
  let mPoly := decodeAndDecompress 1 (m.take 32)
  let vPoly := polyAdd (polyAdd (polyInvNtt (vecDotNtt 4 tHatEnc rHat)) e2) mPoly
  let c1 := ((List.range 4).map fun i => compressAndEncode 11 (uVec.getD i zeroPoly)).flatten
  let c2 := compressAndEncode 5 vPoly
  indCpaDecrypt 4 11 5 skPke (c1 ++ c2) != m

end CryptoGames.MLKEM

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.KemCorrect
public import LibsignalBinary.Specifications.CryptoGames.KEM.Kyber1024KeyGen

/-!
# CBD-Noise Idealization Hypothesis for Round-3 CRYSTALS-Kyber-1024 (`KyberNoiseGap`)

**Trusted: definitions used by the statement.** Defines `sampleNoise128`, `sampleNoiseVec`,
`kyber1024RealKpkeFailsExp`, `kyber1024IdealKpkeFailsExp`, and `KyberNoiseGap` for proving the
concrete Kyber-1024 `δ_kem ≤ ε + 1 / 2 ^ 112` bound (`Kyber1024KemDeltaCorrect` in
`Computational/Specifications/LibsignalCli/Kyber1024Delta.lean`; see DEV-PQ21 in
`Computational/docs/DEVIATIONS.md` and `Computational/docs/TRUSTED_BASE.md`).

In deterministic Kyber-1024, the `8 + 9` `CBD_2` noise blocks of key generation and encapsulation
are pseudorandomly expanded by `SHA3-512` (`G`) and `SHAKE-256` (`PRF`) from the 64-byte seed and
32-byte encapsulation randomness, so no cryptographically small bound can be proved without a
pseudorandomness or random-oracle assumption on `SHA3-512` / `SHAKE-256`. `KyberNoiseGap ε` isolates
that single pseudorandomness step on the fixed efficient test `kyber1024KpkeFailsWith sampleNtt`,
leaving the `SHAKE-128` matrix `Â` (`sampleNtt`), `SHA3-256` message hash `H(r)`, polynomial
arithmetic, compression rounding, and Fujisaki–Okamoto re-encryption completely concrete.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open scoped ENNReal
open OracleComp OracleSpec ENNReal

/-- Sample 128 uniform bytes (`4 × 32` bytes via `sampleBytes32`) as `List (BitVec 8)`, matching the
128-byte input length of `CryptoGames.MLKEM.samplePolyCbd2`. -/
def sampleNoise128 : ProbComp (List (BitVec 8)) := do
  let b0 ← sampleBytes32
  let b1 ← sampleBytes32
  let b2 ← sampleBytes32
  let b3 ← sampleBytes32
  return (b0 ++ b1 ++ b2 ++ b3).map UInt8.toBitVec

/-- Sample `n` independent 128-byte uniform `CBD_2` input blocks, indexed as
`Fin n → List (BitVec 8)`. -/
def sampleNoiseVec (n : Nat) : ProbComp (Fin n → List (BitVec 8)) := do
  let blocks ← (List.range n).mapM fun _ => sampleNoise128
  return fun i => blocks.getD i.val []

/-- Real-noise honest K-PKE decryption-failure experiment: draws uniform 64-byte `seed` and 32-byte
`r` as in `KemDeltaCorrect` and evaluates `kyber1024KpkeFailsWith sampleNtt` on the concrete
`SHA3-512` / `SHAKE-256` `CBD_2` blocks `kyber1024RealNoiseKG` and `kyber1024RealNoiseEnc`. -/
noncomputable def kyber1024RealKpkeFailsExp : ProbComp Bool := do
  let seed ← sampleRandom64
  let r ← sampleCoins32
  let seed64 := seed.map UInt8.toBitVec
  let rand32 := r.map UInt8.toBitVec
  let (pk, _) := CryptoGames.MLKEM.kyber1024KeyPairWith CryptoGames.MLKEM.sampleNtt seed64
  let nKG := CryptoGames.MLKEM.kyber1024RealNoiseKG seed64
  let nEnc := CryptoGames.MLKEM.kyber1024RealNoiseEnc pk rand32
  pure (CryptoGames.MLKEM.kyber1024KpkeFailsWith
    CryptoGames.MLKEM.sampleNtt seed64 rand32 nKG nEnc)

/-- Ideal-noise honest K-PKE decryption-failure experiment: draws uniform 64-byte `seed` and 32-byte
`r` together with independent uniform 128-byte `CBD_2` blocks `nKG` (`8` blocks) and `nEnc` (`9`
blocks), and evaluates the identical `kyber1024KpkeFailsWith sampleNtt` predicate. -/
noncomputable def kyber1024IdealKpkeFailsExp : ProbComp Bool := do
  let seed ← sampleRandom64
  let r ← sampleCoins32
  let seed64 := seed.map UInt8.toBitVec
  let rand32 := r.map UInt8.toBitVec
  let nKG ← sampleNoiseVec 8
  let nEnc ← sampleNoiseVec 9
  pure (CryptoGames.MLKEM.kyber1024KpkeFailsWith
    CryptoGames.MLKEM.sampleNtt seed64 rand32 nKG nEnc)

/-- Pseudorandomness idealization gap of `SHA3-512` (`G`) and `SHAKE-256` (`PRF`) for the single
fixed efficient test of honest Round-3 CRYSTALS-Kyber-1024 K-PKE decryption failure (DEV-PQ21):
bounds the failure probability under real `SHA3-512`/`SHAKE-256` `CBD_2` noise by that under uniform
`CBD_2` noise plus `ε`. If `SHAKE-256` is modeled as a random oracle, the real and ideal experiments
coincide unless `σ = coins`, giving `ε ≤ Pr[σ = coins]` (`= 2^-256` when `SHA3-512` is also modeled
as a random oracle, since its 32-byte input `d` and 64-byte input `m ‖ H(pk)` have distinct lengths;
`ε = 0` when the key-generation and encapsulation `PRF` calls are modeled as independent random
functions, analogous to `ε_ro` in `KeyIndRoGap`, DEV-CLI16). Without random oracles, the
key-generation noise blocks reduce to PRG security of `SHA3-512` on uniform 32-byte `d` plus PRF
security of `SHAKE-256` keyed by `σ`, whereas on the encapsulation side `m = SHA3-256(r)` enters the
decryption check alongside `coins = SHA3-512(m ‖ H(pk))[32..64]` (a public unkeyed hash of `m` and
`H(pk)`), so `KyberNoiseGap ε` directly states that replacing those `SHA3-512`/`SHAKE-256`-derived
blocks by uniform bytes changes the fixed `kyber1024KpkeFailsWith sampleNtt` failure probability by
at most `ε`. -/
def KyberNoiseGap (ε : ℝ≥0∞) : Prop :=
  𝒟[kyber1024RealKpkeFailsExp] {true} ≤ 𝒟[kyber1024IdealKpkeFailsExp] {true} + ε

end SignalPqxdh

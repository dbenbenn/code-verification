/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem
public meta import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem
public meta import LibsignalBinary.Specifications.CryptoGames.Hash.Keccak
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import

/-!
# FIPS 203 ML-KEM-768 (Incremental) & Round-3 CRYSTALS-Kyber-1024 Re-Export & Proof Helpers (`CryptoMlKem.Spec.MlKem`)

Re-exports the trusted FIPS 203 / Round-3 Kyber-1024 definitions and `SampleNTT` matrix/entrypoint
termination predicates (`Shake128MatrixTerminates`, `Mlkem768FromSeedTerminates`,
`Mlkem768Encaps1Terminates`, `Mlkem768DecapsTerminates`, `Kyber1024EncapsTerminates`,
`Kyber1024DecapsTerminates`) from `LibsignalBinary.Specifications.CryptoGames.KEM.MlKem`
(`CryptoGames.MLKEM`), and retains the proof-only bounded-fuel `SampleNTT` (`sampleNttBounded`,
`sampleNttFuel`), compile-time `#guard` checks, and `@[simp]` output-length lemmas.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem

open CryptoVerification.LibsignalSpqrV1 (MlKem Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  keccakAbsorb keccakSqueezeBlocks sha3_256List sha3_512List shake256List)

export CryptoGames.MLKEM (mlkemQ Poly Poly16 zeroPoly bitRev7)
export CryptoGames.MLKEM (fipsZetas zetasTimesMontgomeryR polyAdd polySub nttStage)
export CryptoGames.MLKEM (polyNtt invNttStage polyInvNtt polyNttMul bytesToBits)
export CryptoGames.MLKEM (bitsToBytes byteEncode byteDecodeRaw byteDecodeMod compressCoeff)
export CryptoGames.MLKEM (decompressCoeff compressAndEncode decodeAndDecompress samplePolyCbd2 parseRej12Candidates)
export CryptoGames.MLKEM (shake128FirstBlocks Shake128SeedTerminates sampleNtt sampleMatrixWith vecDotNtt)
export CryptoGames.MLKEM (sampleVecCbd2 polyToCenteredI16Bytes sqdmulh16 sqdmulh32 neonBarrettReduce16)
export CryptoGames.MLKEM (neonMontgomeryReduce16 neonMontgomeryMul16 neonPolyNttMul16 neonInvNttStage16 neonInvNttMontgomery16)
export CryptoGames.MLKEM (bytesToPoly16 neonCompressSerialize4 mlkem768Encaps2List indCpaEncryptWith indCpaDecrypt)
export CryptoGames.MLKEM (mlkem768KeyPairWith mlkem768Encaps1With mlkem768DecapsWith mlkem768ValidPk kyber1024EncapsWith)
export CryptoGames.MLKEM (kyber1024DecapsWith toByteVec mlkem768Incremental kyber1024Encaps kyber1024Decaps)
export CryptoGames.MLKEM (Shake128MatrixTerminates Mlkem768FromSeedTerminates Mlkem768Encaps1Terminates)
export CryptoGames.MLKEM (Mlkem768DecapsTerminates Kyber1024EncapsTerminates Kyber1024DecapsTerminates)

-- Spot-check `zetasTimesMontgomeryR` against `libcrux_ml_kem::polynomial::ZETAS_TIMES_MONTGOMERY_R`:
#guard zetasTimesMontgomeryR.getD 0 0#16 == BitVec.ofInt 16 (-1044)
#guard zetasTimesMontgomeryR.getD 1 0#16 == BitVec.ofInt 16 (-758)
#guard zetasTimesMontgomeryR.getD 64 0#16 == BitVec.ofInt 16 (-1103)
#guard zetasTimesMontgomeryR.getD 127 0#16 == BitVec.ofInt 16 1628

-- Compile-time roundtrip check `polyInvNtt (polyNtt f) == f`:
#guard polyInvNtt (polyNtt (Array.ofFn (n := 256) fun ⟨i, _⟩ => (19 * i + 7) % mlkemQ)) ==
  (Array.ofFn (n := 256) fun ⟨i, _⟩ => (19 * i + 7) % mlkemQ)

/-- Computable bounded-fuel `SampleNTT` (`maxExtraBlocks` extra 168-byte SHAKE-128 blocks past the
initial 3 blocks). Returns `some poly` as soon as `≥ 256` coefficients `< 3329` are accepted. -/
@[expose] def sampleNttBounded (maxExtraBlocks : Nat) (seed34 : List (BitVec 8)) : Option Poly :=
  let rec loop (fuel extra : Nat) : Option Poly :=
    let cands := parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))
    if 256 ≤ cands.length then
      some (cands.take 256).toArray
    else
      match fuel with
      | 0 => none
      | fuel' + 1 => loop fuel' (extra + 1)
  loop maxExtraBlocks 0

/-- Default computable `SampleNTT` (`32` extra blocks = `35` SHAKE-128 blocks, failure `< 2^-2000`)
used ONLY for `#eval` / `#guard` KAT checks; `sampleNtt_eq_fuel` bridges to `sampleNtt`. -/
@[expose] def sampleNttFuel (seed34 : List (BitVec 8)) : Poly :=
  (sampleNttBounded 32 seed34).getD zeroPoly

/-! ### Output-Length Lemmas -/

theorem list_pad_len (bs : List (BitVec 8)) (n : Nat) :
    ((List.range n).map fun i => bs.getD i 0#8).length = n := by
  simp

@[simp] theorem kyber1024Encaps_ct_len (pk rand : List (BitVec 8)) :
    (kyber1024Encaps pk rand).1.length = 1568 := by
  simp [kyber1024Encaps, toByteVec]

@[simp] theorem kyber1024Encaps_ss_len (pk rand : List (BitVec 8)) :
    (kyber1024Encaps pk rand).2.length = 32 := by
  simp [kyber1024Encaps, toByteVec]

@[simp] theorem kyber1024Decaps_len (sk ct : List (BitVec 8)) :
    (kyber1024Decaps sk ct).length = 32 := by
  simp [kyber1024Decaps, toByteVec]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem

-- AUTO-BRIDGE BEGIN
namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
export MlKem (
  mlkemQ
  Poly
  Poly16
  zeroPoly
  bitRev7
  fipsZetas
  zetasTimesMontgomeryR
  polyAdd
  polySub
  nttStage
  polyNtt
  invNttStage
  polyInvNtt
  polyNttMul
  bytesToBits
  bitsToBytes
  byteEncode
  byteDecodeRaw
  byteDecodeMod
  compressCoeff
  decompressCoeff
  compressAndEncode
  decodeAndDecompress
  samplePolyCbd2
  parseRej12Candidates
  shake128FirstBlocks
  Shake128SeedTerminates
  Shake128MatrixTerminates
  sampleNttBounded
  sampleNtt
  sampleNttFuel
  sampleMatrixWith
  vecDotNtt
  sampleVecCbd2
  polyToCenteredI16Bytes
  sqdmulh16
  sqdmulh32
  neonBarrettReduce16
  neonMontgomeryReduce16
  neonMontgomeryMul16
  neonPolyNttMul16
  neonInvNttStage16
  neonInvNttMontgomery16
  bytesToPoly16
  neonCompressSerialize4
  mlkem768Encaps2List
  indCpaEncryptWith
  indCpaDecrypt
  mlkem768KeyPairWith
  mlkem768Encaps1With
  mlkem768DecapsWith
  mlkem768ValidPk
  kyber1024EncapsWith
  kyber1024DecapsWith
  Mlkem768FromSeedTerminates
  Mlkem768Encaps1Terminates
  Mlkem768DecapsTerminates
  Kyber1024EncapsTerminates
  Kyber1024DecapsTerminates
  list_pad_len
  toByteVec
  mlkem768Incremental
  kyber1024Encaps
  kyber1024Decaps
  kyber1024Encaps_ct_len
  kyber1024Encaps_ss_len
  kyber1024Decaps_len
)
end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
-- AUTO-BRIDGE END

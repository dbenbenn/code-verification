/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.Kyber1024Delta
import Computational.Proofs.Kyber1024Delta.KpkeIdealBound
import VCVio.CryptoFoundations.SecExp.Measure

/-!
# Concrete Round-3 CRYSTALS-Kyber-1024 `δ_kem` Proof (`HeadlineProof`)

Proves `Kyber1024KemDeltaCorrect` (`kyber1024_kem_delta_correct_proof`):
1. Unconditional `(1568B, 3168B)` wire-length validity of `kyber1024KemKeyGen`.
2. Fujisaki–Okamoto recovery and `modelPrims` reduction from `kemHonestExchangeFails` at
   `modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams` to the noise-explicit K-PKE
   failure predicate `kyber1024KpkeFailsWith sampleNtt` on `(kyber1024RealNoiseKG, kyber1024RealNoiseEnc)`.
3. Composition of `KyberNoiseGap ε` with the ideal `CBD_2` tail bound
   `KpkeIdealBound.kpkeBodyFails_sampleNtt_full_exp_le_two_pow_neg_112` (`≤ 1 / 2 ^ 112`), yielding
   `KemDeltaCorrect (modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams) (ε + 1 / 2 ^ 112)`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Kyber1024Delta.HeadlineProof

open scoped ENNReal
open OracleComp OracleSpec
open MeasureTheory (Measure lintegral_mono)
open CryptoGames.MLKEM (
  Poly
  bitsToBytes
  byteDecodeMod
  byteEncode
  compressAndEncode
  compressCoeff
  decodeAndDecompress
  indCpaDecrypt
  indCpaEncryptWith
  kyber1024Decaps
  kyber1024DecapsVec
  kyber1024DecapsWith
  kyber1024Encaps
  kyber1024EncapsVec
  kyber1024EncapsWith
  kyber1024KemKeyGen
  kyber1024KeyPair
  kyber1024KeyPairWith
  kyber1024KpkeFailsWith
  kyber1024RealNoiseEnc
  kyber1024RealNoiseKG
  polyAdd
  polyInvNtt
  polyNtt
  polySub
  sampleMatrixWith
  sampleNtt
  samplePolyCbd2
  sampleVecCbd2
  toByteVec
  vecDotNtt
  zeroPoly
)
open CryptoGames.SHA3 (
  keccakSponge
  sha3_256List
  sha3_512List
  shake256List
)
open CryptoVerification.E2E (
  Kyber1024KemDeltaCorrect
  blockLevelPrims
  modelPrims
  ofU8
  realUnreachedPrims
  toU8
  u8Vec
  vecU8
)
open CryptoVerification.SignalSession (
  realPEParams
  realPqxdhPrims
)
open SignalPqxdh (
  KemDeltaCorrect
  KyberNoiseGap
  kemHonestExchangeFails
  kyber1024IdealKpkeFailsExp
  kyber1024RealKpkeFailsExp
  sampleBytes32
  sampleCoins32
  sampleRandom64
  word256ToBytes
)
open Computational.Proofs.Kyber1024Delta.KpkeIdealBound (
  kpkeBodyFails_sampleNtt_full_exp_le_two_pow_neg_112
)

/-! ## 1. Ideal-Noise K-PKE Tail Bound (`≤ 1 / 2 ^ 112`) -/

/-- `SignalPqxdh.kyber1024IdealKpkeFailsExp` is definitionally identical to `KpkeIdealBound`'s
`cbdNoiseVec` + `kpkeBodyFails sampleNtt` experiment, yielding the `1 / 2 ^ 112` bound. -/
theorem kyber1024IdealKpkeFailsExp_le_two_pow_neg_112 :
    𝒟[kyber1024IdealKpkeFailsExp] {true} ≤ 1 / (2 : ℝ≥0∞) ^ 112 :=
  kpkeBodyFails_sampleNtt_full_exp_le_two_pow_neg_112

/-! ## 2. Byte-List, Codec, and Keccak Length Helpers -/

private theorem ofU8_toU8_eq (bs : List (BitVec 8)) : ofU8 (toU8 bs) = bs := by
  simp [toU8, ofU8, List.map_map, Function.comp_def]

private theorem toByteVec_toList_length (n : Nat) (bs : List (BitVec 8)) :
    (toByteVec n bs).toList.length = n := by
  change ((List.range n).map fun i => bs.getD i 0#8).length = n
  rw [List.length_map, List.length_range]

private theorem toByteVec_toList_of_length {n : Nat} {bs : List (BitVec 8)} (h : bs.length = n) :
    (toByteVec n bs).toList = bs := by
  change ((List.range n).map fun i => bs.getD i 0#8) = bs
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, h]
  · intro i hi1 hi2
    simp [List.getD_eq_getElem?_getD, hi2]

private theorem u8Vec_toList_of_length {n : Nat} {bs : List UInt8} (h : bs.length = n) :
    (u8Vec n bs).toList = ofU8 bs := by
  change (ofU8 bs ++ List.replicate n 0#8).take n = ofU8 bs
  rw [List.take_append_of_le_length (by simp [ofU8, h]),
    List.take_of_length_le (by simp [ofU8, h])]

private theorem byteEncode_length (d : Nat) (f : Poly) :
    (byteEncode d f).length = 32 * d := by
  simp only [byteEncode, bitsToBytes, List.length_map, List.length_range, Array.size_ofFn]
  omega

private theorem compressAndEncode_length (d : Nat) (f : Poly) :
    (compressAndEncode d f).length = 32 * d :=
  byteEncode_length d (f.map (compressCoeff d))

private theorem sha3_256List_length (msg : List (BitVec 8)) :
    (sha3_256List msg).length = 32 := by
  simp [sha3_256List, keccakSponge]

private theorem sha3_512List_length (msg : List (BitVec 8)) :
    (sha3_512List msg).length = 64 := by
  simp [sha3_512List, keccakSponge]

private theorem shake256List_length (outLen : Nat) (msg : List (BitVec 8)) :
    (shake256List outLen msg).length = outLen := by
  simp [shake256List, keccakSponge]

-- Seal concrete Keccak, NTT, CBD, and codec internals so FO and `modelPrims` unfolding never
-- trigger kernel reduction of 24-round Keccak or 7-stage NTT butterflies.
attribute [local irreducible]
  polyNtt polyInvNtt vecDotNtt polyAdd polySub samplePolyCbd2 sampleNtt
  sha3_256List sha3_512List shake256List
  byteEncode byteDecodeMod compressAndEncode decodeAndDecompress indCpaDecrypt
  toByteVec u8Vec

private theorem range4_eq : List.range 4 = [0, 1, 2, 3] := rfl

/-! ## 3. Wire Lengths and `kyber1024KemKeyGen_valid` -/

private theorem kyber1024KeyPairWith_pk_length (sampler : List (BitVec 8) → Poly)
    (seed64 : List (BitVec 8)) :
    (kyber1024KeyPairWith sampler seed64).1.length = 1568 := by
  unfold kyber1024KeyPairWith
  dsimp only
  rw [range4_eq]
  simp [byteEncode_length, sha3_512List_length]

private theorem kyber1024KeyPairWith_sk_length (sampler : List (BitVec 8) → Poly)
    {seed64 : List (BitVec 8)} (hSeed : seed64.length = 64) :
    (kyber1024KeyPairWith sampler seed64).2.length = 3168 := by
  unfold kyber1024KeyPairWith
  dsimp only
  rw [range4_eq]
  simp [byteEncode_length, sha3_256List_length, sha3_512List_length, hSeed]

private theorem kyber1024KeyPair_eq_of_length {seed64 : List (BitVec 8)}
    (hSeed : seed64.length = 64) :
    kyber1024KeyPair seed64 = kyber1024KeyPairWith sampleNtt seed64 := by
  unfold kyber1024KeyPair
  rw [toByteVec_toList_of_length hSeed]
  have hpk := kyber1024KeyPairWith_pk_length sampleNtt seed64
  have hsk := kyber1024KeyPairWith_sk_length sampleNtt hSeed
  generalize kyber1024KeyPairWith sampleNtt seed64 = kp at hpk hsk ⊢
  rcases kp with ⟨pk, sk⟩
  dsimp only at hpk hsk ⊢
  rw [toByteVec_toList_of_length hpk, toByteVec_toList_of_length hsk]

/-- First conjunct of `Kyber1024KemDeltaCorrect`: `kyber1024KemKeyGen` always outputs a 1568-byte
public key and 3168-byte secret key. -/
theorem kyber1024KemKeyGen_valid (seed : List UInt8) :
    (kyber1024KemKeyGen seed).1.length = SignalPqxdh.kyberPkLen ∧
    (kyber1024KemKeyGen seed).2.length = 3168 := by
  unfold kyber1024KemKeyGen kyber1024KeyPair
  generalize kyber1024KeyPairWith sampleNtt (toByteVec 64 (seed.map UInt8.toBitVec)).toList = kp
  rcases kp with ⟨pk, sk⟩
  dsimp only [SignalPqxdh.kyberPkLen]
  rw [List.length_map, List.length_map, toByteVec_toList_length, toByteVec_toList_length]
  exact ⟨rfl, rfl⟩

private theorem indCpaEncryptWith_kyber1024_lengths (sampler : List (BitVec 8) → Poly)
    (pk m coins : List (BitVec 8)) :
    (indCpaEncryptWith sampler 4 11 5 pk m coins).1.length = 1408 ∧
    (indCpaEncryptWith sampler 4 11 5 pk m coins).2.1.length = 160 := by
  unfold indCpaEncryptWith
  dsimp only
  rw [range4_eq]
  simp [compressAndEncode_length]

private theorem kyber1024EncapsWith_lengths (sampler : List (BitVec 8) → Poly)
    (pk1568 rand32 : List (BitVec 8)) :
    (kyber1024EncapsWith sampler pk1568 rand32).1.length = 1568 ∧
    (kyber1024EncapsWith sampler pk1568 rand32).2.length = 32 := by
  unfold kyber1024EncapsWith
  dsimp only
  have ⟨hc1, hc2⟩ := indCpaEncryptWith_kyber1024_lengths sampler
    (pk1568.take 1568) (sha3_256List (rand32.take 32))
    (((sha3_512List (sha3_256List (rand32.take 32) ++ sha3_256List (pk1568.take 1568))).drop 32).take 32)
  generalize indCpaEncryptWith sampler 4 11 5
      (pk1568.take 1568) (sha3_256List (rand32.take 32))
      (((sha3_512List (sha3_256List (rand32.take 32) ++ sha3_256List (pk1568.take 1568))).drop 32).take 32) =
    eo at hc1 hc2 ⊢
  rcases eo with ⟨c1, c2, _, _⟩
  dsimp only at hc1 hc2 ⊢
  exact ⟨by rw [List.length_append, hc1, hc2], shake256List_length _ _⟩

private theorem kyber1024DecapsWith_length (sampler : List (BitVec 8) → Poly)
    (sk3168 ct1568 : List (BitVec 8)) :
    (kyber1024DecapsWith sampler sk3168 ct1568).length = 32 := by
  unfold kyber1024DecapsWith
  dsimp only
  split <;> exact shake256List_length _ _

private theorem kyber1024Encaps_eq (pk rand : List (BitVec 8)) :
    kyber1024Encaps pk rand = kyber1024EncapsWith sampleNtt pk rand := by
  unfold kyber1024Encaps
  have ⟨hct, hss⟩ := kyber1024EncapsWith_lengths sampleNtt pk rand
  generalize kyber1024EncapsWith sampleNtt pk rand = ep at hct hss ⊢
  rcases ep with ⟨ct, ss⟩
  dsimp only at hct hss ⊢
  rw [toByteVec_toList_of_length hct, toByteVec_toList_of_length hss]

private theorem kyber1024Decaps_eq (sk ct : List (BitVec 8)) :
    kyber1024Decaps sk ct = kyber1024DecapsWith sampleNtt sk ct := by
  unfold kyber1024Decaps
  exact toByteVec_toList_of_length (kyber1024DecapsWith_length sampleNtt sk ct)

/-! ## 4. Noise-Explicit Unfolding and Fujisaki–Okamoto Recovery -/

private theorem take_append_eq_left {α : Type} (a b : List α) {n : Nat} (ha : a.length = n) :
    (a ++ b).take n = a := by
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

private theorem drop_append_eq_right {α : Type} (a b : List α) {n : Nat} (ha : a.length = n) :
    (a ++ b).drop n = b := by
  rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]

private theorem map_ofFn_4 {α β : Type} (g : α → β) (f : Fin 4 → α) :
    (Array.ofFn f).map g = Array.ofFn (fun i => g (f i)) := by
  apply Array.ext
  · simp
  · intro i hi1 hi2
    simp

private theorem sampleVecCbd2_4_0_map_polyNtt {sigma : List (BitVec 8)}
    (hSig : sigma.take 32 = sigma) {nBlk : Fin 8 → List (BitVec 8)}
    (hBlk : ∀ i : Fin 4, shake256List 128 (sigma ++ [BitVec.ofNat 8 i.val]) =
      nBlk ⟨i.val, by omega⟩) :
    (sampleVecCbd2 4 sigma 0).map polyNtt =
      Array.ofFn (n := 4) fun ⟨i, hi⟩ => polyNtt (samplePolyCbd2 (nBlk ⟨i, by omega⟩)) := by
  unfold sampleVecCbd2
  dsimp only
  rw [hSig, map_ofFn_4]
  exact congrArg (Array.ofFn (n := 4)) (funext fun ⟨i, hi⟩ => by
    dsimp only
    rw [Nat.zero_add, hBlk ⟨i, hi⟩])

private theorem sampleVecCbd2_4_4_map_polyNtt {sigma : List (BitVec 8)}
    (hSig : sigma.take 32 = sigma) {nBlk : Fin 8 → List (BitVec 8)}
    (hBlk : ∀ i : Fin 4, shake256List 128 (sigma ++ [BitVec.ofNat 8 (4 + i.val)]) =
      nBlk ⟨4 + i.val, by omega⟩) :
    (sampleVecCbd2 4 sigma 4).map polyNtt =
      Array.ofFn (n := 4) fun ⟨i, hi⟩ => polyNtt (samplePolyCbd2 (nBlk ⟨4 + i, by omega⟩)) := by
  unfold sampleVecCbd2
  dsimp only
  rw [hSig, map_ofFn_4]
  exact congrArg (Array.ofFn (n := 4)) (funext fun ⟨i, hi⟩ => by
    dsimp only
    rw [hBlk ⟨i, hi⟩])

private theorem sampleVecCbd2_4_0_enc_map_polyNtt {coins : List (BitVec 8)}
    (hCoins : coins.take 32 = coins) {nEnc : Fin 9 → List (BitVec 8)}
    (hBlk : ∀ i : Fin 4, shake256List 128 (coins ++ [BitVec.ofNat 8 i.val]) =
      nEnc ⟨i.val, by omega⟩) :
    (sampleVecCbd2 4 coins 0).map polyNtt =
      Array.ofFn (n := 4) fun ⟨i, hi⟩ => polyNtt (samplePolyCbd2 (nEnc ⟨i, by omega⟩)) := by
  unfold sampleVecCbd2
  dsimp only
  rw [hCoins, map_ofFn_4]
  exact congrArg (Array.ofFn (n := 4)) (funext fun ⟨i, hi⟩ => by
    dsimp only
    rw [Nat.zero_add, hBlk ⟨i, hi⟩])

private theorem sampleVecCbd2_4_4_enc {coins : List (BitVec 8)}
    (hCoins : coins.take 32 = coins) {nEnc : Fin 9 → List (BitVec 8)}
    (hBlk : ∀ i : Fin 4, shake256List 128 (coins ++ [BitVec.ofNat 8 (4 + i.val)]) =
      nEnc ⟨4 + i.val, by omega⟩) :
    sampleVecCbd2 4 coins 4 =
      Array.ofFn (n := 4) fun ⟨i, hi⟩ => samplePolyCbd2 (nEnc ⟨4 + i, by omega⟩) := by
  unfold sampleVecCbd2
  dsimp only
  rw [hCoins]
  exact congrArg (Array.ofFn (n := 4)) (funext fun ⟨i, hi⟩ => by
    dsimp only
    rw [hBlk ⟨i, hi⟩])

private theorem take_1536_sk_append (skPke pk hPk z : List (BitVec 8))
    (hLen : skPke.length = 1536) :
    (skPke ++ pk ++ hPk ++ z).take 1536 = skPke := by
  simp only [List.append_assoc]
  exact take_append_eq_left skPke (pk ++ (hPk ++ z)) hLen

private theorem kyber1024KpkeFailsWith_real_eq (sampler : List (BitVec 8) → Poly)
    (seed64 rand32 : List (BitVec 8)) :
    let (pk, sk) := kyber1024KeyPairWith sampler seed64
    let m := sha3_256List (rand32.take 32)
    let coins := ((sha3_512List (m ++ sha3_256List pk)).drop 32).take 32
    let enc := indCpaEncryptWith sampler 4 11 5 pk m coins
    kyber1024KpkeFailsWith sampler seed64 rand32
      (kyber1024RealNoiseKG seed64) (kyber1024RealNoiseEnc pk rand32) =
    (indCpaDecrypt 4 11 5 (sk.take 1536) (enc.1 ++ enc.2.1) != m) := by
  have hPkLen : (kyber1024KeyPairWith sampler seed64).1.length = 1568 :=
    kyber1024KeyPairWith_pk_length sampler seed64
  have hSigLen : (((sha3_512List (seed64.take 32)).drop 32).take 32).take 32 =
      ((sha3_512List (seed64.take 32)).drop 32).take 32 := List.take_take
  have hsHat := sampleVecCbd2_4_0_map_polyNtt hSigLen
    (nBlk := kyber1024RealNoiseKG seed64) (fun _ => rfl)
  have heHat := sampleVecCbd2_4_4_map_polyNtt hSigLen
    (nBlk := kyber1024RealNoiseKG seed64) (fun _ => rfl)
  dsimp only [kyber1024KeyPairWith] at hPkLen ⊢
  have hSkPkeLen :
      (((List.range 4).map fun i =>
        byteEncode 12 (((sampleVecCbd2 4 (((sha3_512List (seed64.take 32)).drop 32).take 32) 0).map polyNtt).getD i zeroPoly)).flatten).length =
      1536 := by
    rw [range4_eq]; simp [byteEncode_length]
  rw [take_1536_sk_append _ _ _ _ hSkPkeLen]
  unfold kyber1024KpkeFailsWith indCpaEncryptWith
  dsimp only
  rw [← hsHat, ← heHat]
  set pkVal :=
    ((List.range 4).map fun i =>
      byteEncode 12 ((Array.ofFn (n := 4) fun ⟨j, _⟩ =>
        polyAdd
          (vecDotNtt 4 ((sampleMatrixWith sampler 4 ((sha3_512List (seed64.take 32)).take 32) true).getD j #[])
            ((sampleVecCbd2 4 (((sha3_512List (seed64.take 32)).drop 32).take 32) 0).map polyNtt))
          (((sampleVecCbd2 4 (((sha3_512List (seed64.take 32)).drop 32).take 32) 4).map polyNtt).getD j zeroPoly)).getD i zeroPoly)).flatten ++
      (sha3_512List (seed64.take 32)).take 32
  have hPkTake : pkVal.take 1568 = pkVal := List.take_of_length_le (by omega)
  set coinsVal := ((sha3_512List (sha3_256List (rand32.take 32) ++ sha3_256List pkVal)).drop 32).take 32
  have hCoinsTake : coinsVal.take 32 = coinsVal := List.take_take
  have hEncBlk : ∀ idx : Fin 9,
      kyber1024RealNoiseEnc pkVal rand32 idx =
        shake256List 128 (coinsVal ++ [BitVec.ofNat 8 idx.val]) := by
    intro idx
    unfold kyber1024RealNoiseEnc
    dsimp only
    rw [hPkTake]
  have hrHat := sampleVecCbd2_4_0_enc_map_polyNtt hCoinsTake
    (nEnc := kyber1024RealNoiseEnc pkVal rand32) (fun i => (hEncBlk ⟨i.val, by omega⟩).symm)
  have he1 := sampleVecCbd2_4_4_enc hCoinsTake
    (nEnc := kyber1024RealNoiseEnc pkVal rand32) (fun i => (hEncBlk ⟨4 + i.val, by omega⟩).symm)
  have he2 :
      samplePolyCbd2 (kyber1024RealNoiseEnc pkVal rand32 ⟨8, by decide⟩) =
      samplePolyCbd2 (shake256List 128 (coinsVal.take 32 ++ [BitVec.ofNat 8 (2 * 4)])) := by
    rw [hCoinsTake, hEncBlk ⟨8, by decide⟩]
  rw [← hrHat, ← he1, he2]

private theorem kyber1024DecapsWith_eq_of_kpkeFailsWith_false (sampler : List (BitVec 8) → Poly)
    (seed64 rand32 : List (BitVec 8))
    (hNoFail :
      kyber1024KpkeFailsWith sampler seed64 rand32
        (kyber1024RealNoiseKG seed64)
        (kyber1024RealNoiseEnc (kyber1024KeyPairWith sampler seed64).1 rand32) = false) :
    let (pk, sk) := kyber1024KeyPairWith sampler seed64
    let (ct, ss) := kyber1024EncapsWith sampler pk rand32
    kyber1024DecapsWith sampler sk ct = ss := by
  have hUnf := kyber1024KpkeFailsWith_real_eq sampler seed64 rand32
  have hPkLen := kyber1024KeyPairWith_pk_length sampler seed64
  have hKP : ∃ skPke hPk z : List (BitVec 8),
      skPke.length = 1536 ∧
      hPk = sha3_256List (kyber1024KeyPairWith sampler seed64).1 ∧
      (kyber1024KeyPairWith sampler seed64).2 =
        skPke ++ (kyber1024KeyPairWith sampler seed64).1 ++ hPk ++ z := by
    unfold kyber1024KeyPairWith
    refine ⟨_, _, _, ?_, rfl, rfl⟩
    rw [range4_eq]
    simp [byteEncode_length]
  rcases hKP with ⟨skPke, hPk, z, hSkPkeLen, hhPkEq, hSkEq⟩
  generalize kyber1024KeyPairWith sampler seed64 = kp at hUnf hPkLen hhPkEq hSkEq hNoFail ⊢
  rcases kp with ⟨pk, sk⟩
  dsimp only at hUnf hPkLen hhPkEq hSkEq hNoFail ⊢
  have hPkTake : pk.take 1568 = pk := List.take_of_length_le (by omega)
  have hHPkLen : hPk.length = 32 := by rw [hhPkEq]; exact sha3_256List_length pk
  have hSkDrop1 : sk.drop 1536 = pk ++ (hPk ++ z) := by
    rw [hSkEq]
    simp only [List.append_assoc]
    exact drop_append_eq_right skPke (pk ++ (hPk ++ z)) hSkPkeLen
  have hSkSlice2 : (sk.drop 1536).take 1568 = pk := by
    rw [hSkDrop1]; exact take_append_eq_left pk (hPk ++ z) hPkLen
  have hSkSlice3 : (sk.drop 3104).take 32 = hPk := by
    have h3104 : sk.drop 3104 = hPk ++ z := by
      have : (3104 : Nat) = 1536 + 1568 := rfl
      rw [this, ← List.drop_drop, hSkDrop1, drop_append_eq_right pk (hPk ++ z) hPkLen]
    rw [h3104]; exact take_append_eq_left hPk z hHPkLen
  rw [hNoFail] at hUnf
  have hDecM :
      indCpaDecrypt 4 11 5 (sk.take 1536)
        ((indCpaEncryptWith sampler 4 11 5 pk (sha3_256List (rand32.take 32))
            (((sha3_512List (sha3_256List (rand32.take 32) ++ sha3_256List pk)).drop 32).take 32)).1 ++
         (indCpaEncryptWith sampler 4 11 5 pk (sha3_256List (rand32.take 32))
            (((sha3_512List (sha3_256List (rand32.take 32) ++ sha3_256List pk)).drop 32).take 32)).2.1) =
      sha3_256List (rand32.take 32) :=
    bne_eq_false_iff_eq.mp hUnf.symm
  unfold kyber1024EncapsWith
  dsimp only
  rw [hPkTake]
  have ⟨hc1Len, hc2Len⟩ := indCpaEncryptWith_kyber1024_lengths sampler pk
    (sha3_256List (rand32.take 32))
    (((sha3_512List (sha3_256List (rand32.take 32) ++ sha3_256List pk)).drop 32).take 32)
  generalize hEO :
    indCpaEncryptWith sampler 4 11 5 pk (sha3_256List (rand32.take 32))
      (((sha3_512List (sha3_256List (rand32.take 32) ++ sha3_256List pk)).drop 32).take 32) =
    eo at hDecM hc1Len hc2Len ⊢
  rcases eo with ⟨c1, c2, rHatOut, e2Out⟩
  dsimp only at hDecM hc1Len hc2Len ⊢
  have hCtTake : (c1 ++ c2).take 1568 = c1 ++ c2 :=
    List.take_of_length_le (by rw [List.length_append, hc1Len, hc2Len])
  unfold kyber1024DecapsWith
  dsimp only
  rw [hSkSlice2, hSkSlice3, hhPkEq, hCtTake, hDecM, hEO]
  dsimp only
  simp only [beq_self_eq_true, ↓reduceIte]

private theorem kemHonestExchangeFails_imp_kpkeFailsWith {seed r : List UInt8}
    (hSeed : seed.length = 64) (hR : r.length = 32)
    (hFail :
      kemHonestExchangeFails
        (modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams) seed r = true) :
    let seed64 := seed.map UInt8.toBitVec
    let rand32 := r.map UInt8.toBitVec
    let (pk, _) := kyber1024KeyPairWith sampleNtt seed64
    kyber1024KpkeFailsWith sampleNtt seed64 rand32
      (kyber1024RealNoiseKG seed64) (kyber1024RealNoiseEnc pk rand32) = true := by
  dsimp only
  have hSeed64 : (seed.map UInt8.toBitVec).length = 64 := by rw [List.length_map, hSeed]
  have hKP : kyber1024KemKeyGen seed =
      (toU8 (kyber1024KeyPairWith sampleNtt (seed.map UInt8.toBitVec)).1,
       toU8 (kyber1024KeyPairWith sampleNtt (seed.map UInt8.toBitVec)).2) := by
    unfold kyber1024KemKeyGen
    rw [kyber1024KeyPair_eq_of_length hSeed64]
    rfl
  have hPkLen : (kyber1024KeyPairWith sampleNtt (seed.map UInt8.toBitVec)).1.length = 1568 :=
    kyber1024KeyPairWith_pk_length sampleNtt _
  have hSkLen : (kyber1024KeyPairWith sampleNtt (seed.map UInt8.toBitVec)).2.length = 3168 :=
    kyber1024KeyPairWith_sk_length sampleNtt hSeed64
  generalize hPair : kyber1024KeyPairWith sampleNtt (seed.map UInt8.toBitVec) = kp
    at hKP hPkLen hSkLen ⊢
  rcases kp with ⟨pk, sk⟩
  dsimp only at hKP hPkLen hSkLen ⊢
  have hPkU8Len : (toU8 pk).length = 1568 := by rw [toU8, List.length_map, hPkLen]
  have hSkU8Len : (toU8 sk).length = 3168 := by rw [toU8, List.length_map, hSkLen]
  have ⟨hCtLen, _⟩ := kyber1024EncapsWith_lengths sampleNtt pk (r.map UInt8.toBitVec)
  have hEncEq := kyber1024Encaps_eq pk (r.map UInt8.toBitVec)
  generalize hEncPair : kyber1024EncapsWith sampleNtt pk (r.map UInt8.toBitVec) = ep
    at hCtLen hEncEq
  rcases ep with ⟨ct, ss⟩
  dsimp only at hCtLen
  have hCtU8Len : (toU8 ct).length = 1568 := by rw [toU8, List.length_map, hCtLen]
  have hEncModel :
      (modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams).kemEncaps (toU8 pk) r =
      some (toU8 ss, toU8 ct) := by
    unfold modelPrims blockLevelPrims realPEParams realPqxdhPrims SignalPqxdh.kyberPkLen
    dsimp only
    rw [hPkU8Len, beq_self_eq_true]
    dsimp only [↓reduceIte, kyber1024EncapsVec]
    have hVecEq : ∀ {n : Nat} (l : List (BitVec 8)) (hl : l.length = n),
        vecU8 (⟨l, hl⟩ : List.Vector (BitVec 8) n) = toU8 l := fun _ _ => rfl
    rw [hVecEq, hVecEq]
    have huPk : (u8Vec 1568 (toU8 pk)).toList = pk := by
      rw [u8Vec_toList_of_length hPkU8Len, ofU8_toU8_eq]
    have huR : (u8Vec 32 r).toList = r.map UInt8.toBitVec := u8Vec_toList_of_length hR
    rw [huPk, huR, hEncEq]
    rfl
  have hDecModel :
      (modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams).kemDecaps
        (toU8 sk) (toU8 ct) =
      some (toU8 (kyber1024DecapsWith sampleNtt sk ct)) := by
    unfold modelPrims blockLevelPrims realPEParams realPqxdhPrims SignalPqxdh.kyberCtLen
    dsimp only
    rw [hCtU8Len, beq_self_eq_true]
    dsimp only [↓reduceIte, kyber1024DecapsVec]
    have hVecEq : ∀ {n : Nat} (l : List (BitVec 8)) (hl : l.length = n),
        vecU8 (⟨l, hl⟩ : List.Vector (BitVec 8) n) = toU8 l := fun _ _ => rfl
    rw [hVecEq]
    have huSk : (u8Vec 3168 (toU8 sk)).toList = sk := by
      rw [u8Vec_toList_of_length hSkU8Len, ofU8_toU8_eq]
    have huCt : (u8Vec 1568 (toU8 ct)).toList = ct := by
      rw [u8Vec_toList_of_length hCtU8Len, ofU8_toU8_eq]
    rw [huSk, huCt, kyber1024Decaps_eq]
    rfl
  by_contra hNotTrue
  have hFalse :
      kyber1024KpkeFailsWith sampleNtt (seed.map UInt8.toBitVec) (r.map UInt8.toBitVec)
        (kyber1024RealNoiseKG (seed.map UInt8.toBitVec))
        (kyber1024RealNoiseEnc pk (r.map UInt8.toBitVec)) = false :=
    Bool.eq_false_iff.mpr hNotTrue
  have hDecRaw := kyber1024DecapsWith_eq_of_kpkeFailsWith_false sampleNtt
    (seed.map UInt8.toBitVec) (r.map UInt8.toBitVec) (by rw [hPair]; exact hFalse)
  rw [hPair] at hDecRaw
  dsimp only at hDecRaw
  rw [hEncPair] at hDecRaw
  dsimp only at hDecRaw
  unfold kemHonestExchangeFails at hFail
  have hKgModel :
      (modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams).kemKeyGen seed =
      (toU8 pk, toU8 sk) := hKP
  rw [hKgModel] at hFail
  dsimp only at hFail
  rw [hEncModel] at hFail
  dsimp only at hFail
  rw [hDecModel, hDecRaw] at hFail
  simp at hFail

/-! ## 5. Final Assembly: `kyber1024_kem_delta_correct_proof` -/

private theorem mem_support_sampleBytes32_len {b : List UInt8} (h : b ∈ support sampleBytes32) :
    b.length = 32 := by
  simp only [sampleBytes32, support_map, Set.mem_image] at h
  rcases h with ⟨w, _, rfl⟩
  simp [word256ToBytes]

private theorem mem_support_sampleRandom64_len {r : List UInt8} (h : r ∈ support sampleRandom64) :
    r.length = 64 := by
  simp only [sampleRandom64, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h
  rcases h with ⟨b1, hb1, b2, hb2, rfl⟩
  simp [mem_support_sampleBytes32_len hb1, mem_support_sampleBytes32_len hb2]

private theorem evalDist_bind_true_mono {α : Type}
    (mx : ProbComp α) (f g : α → ProbComp Bool)
    (hfg : ∀ a, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) :
    𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace Bool := ⊤
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
    evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  exact lintegral_mono hfg

private theorem evalDist_pure_bool_mono {b1 b2 : Bool} (h : b1 = true → b2 = true) :
    𝒟[(pure b1 : ProbComp Bool)] {true} ≤ 𝒟[(pure b2 : ProbComp Bool)] {true} := by
  cases b1 <;> cases b2 <;> simp at h ⊢

private theorem kemHonestExchangeFails_prob_le_realKpkeFailsExp :
    𝒟[do
        let seed ← sampleRandom64
        let r ← sampleCoins32
        pure (kemHonestExchangeFails
          (modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams) seed r)] {true} ≤
      𝒟[kyber1024RealKpkeFailsExp] {true} := by
  have hGuard :
      𝒟[do
          let seed ← sampleRandom64
          let r ← sampleCoins32
          pure (kemHonestExchangeFails
            (modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams) seed r)] =
      𝒟[do
          let seed ← sampleRandom64
          let r ← sampleCoins32
          pure (decide (seed.length = 64 ∧ r.length = 32) &&
            kemHonestExchangeFails
              (modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams) seed r)] := by
    refine OracleComp.evalDist_bind_congr_of_support sampleRandom64 _ _ fun seed hSeed => ?_
    refine OracleComp.evalDist_bind_congr_of_support sampleCoins32 _ _ fun r hR => ?_
    have hs : seed.length = 64 := mem_support_sampleRandom64_len hSeed
    have hr : r.length = 32 := mem_support_sampleBytes32_len hR
    have hdec : decide (seed.length = 64 ∧ r.length = 32) = true := decide_eq_true ⟨hs, hr⟩
    rw [hdec, Bool.true_and]
  rw [hGuard]
  unfold kyber1024RealKpkeFailsExp
  refine evalDist_bind_true_mono sampleRandom64 _ _ fun seed => ?_
  refine evalDist_bind_true_mono sampleCoins32 _ _ fun r => ?_
  refine evalDist_pure_bool_mono fun h => ?_
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact kemHonestExchangeFails_imp_kpkeFailsWith h.1.1 h.1.2 h.2

/-- Reduction from `KyberNoiseGap ε` and any ideal-noise K-PKE failure bound `δ` to
`KemDeltaCorrect` at `kyber1024KemKeyGen` with `ε + δ`. -/
theorem kemDeltaCorrect_of_ideal_kpke_bound {ε δ : ℝ≥0∞}
    (hGap : KyberNoiseGap ε)
    (hIdeal : 𝒟[kyber1024IdealKpkeFailsExp] {true} ≤ δ) :
    KemDeltaCorrect
      (modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams) (ε + δ) := by
  unfold KemDeltaCorrect
  calc 𝒟[do
          let seed ← sampleRandom64
          let r ← sampleCoins32
          pure (kemHonestExchangeFails
            (modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams) seed r)] {true}
      ≤ 𝒟[kyber1024RealKpkeFailsExp] {true} := kemHonestExchangeFails_prob_le_realKpkeFailsExp
    _ ≤ 𝒟[kyber1024IdealKpkeFailsExp] {true} + ε := hGap
    _ ≤ δ + ε := by gcongr
    _ = ε + δ := add_comm δ ε

/-- Concrete Round-3 CRYSTALS-Kyber-1024 `(1568B, 3168B)` key-generation length validity and
`δ_kem = ε + 1 / 2 ^ 112` decapsulation-failure bound under `KyberNoiseGap ε`. -/
theorem kyber1024_kem_delta_correct_proof : Kyber1024KemDeltaCorrect :=
  ⟨kyber1024KemKeyGen_valid,
   fun _ hGap =>
     kemDeltaCorrect_of_ideal_kpke_bound hGap kyber1024IdealKpkeFailsExp_le_two_pow_neg_112⟩

end Computational.Proofs.Kyber1024Delta.HeadlineProof

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Kyber1024Delta.Common -- proof-setup: allow-public-import
public import Computational.Specifications.Pqxdh.Game
public import VCVio.EvalDist.EvalDistEq
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.Monad.Measure
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `CBD_2` Byte Sampling, Independence, and Rational W2 Chernoff Bound (`CbdProbability`)

Connects uniform 128-byte noise blocks sampled via `SignalPqxdh.sampleBytes32` and mapped through
`CryptoGames.MLKEM.samplePolyCbd2` to i.i.d. rational `CBD_2` expectations and the conditioned W2
Chernoff tail bound over `(8 + 9)` independent 128-byte blocks.
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.Kyber1024Delta.CbdProbability

open scoped ENNReal
open OracleComp OracleSpec
open CryptoGames.MLKEM (
  Poly
  bytesToBits
  compressCoeff
  decompressCoeff
  mlkemQ
  samplePolyCbd2
)
open Computational.Proofs.Kyber1024Delta.Common (
  IsCanonicalPoly
  ZPoly
  cbd2Support
  cbd2WeightQ
  centeredZMod
  centeredZMod_cast_eq
  centeredZMod_of_int_bounds
  compressErrZMod
  getD_ofFn_nat
  negacyclicMul
  negacyclicMulInt
  negacyclicMulInt_cast
  ofZPoly
  ofZPoly_toZPoly
  toZPoly
)

/-! ## 1. Uniform 128-Byte and `n`-Block Samplers -/

/-- Sample 128 uniform bytes (`4 × 32` bytes via `SignalPqxdh.sampleBytes32`) as `List (BitVec 8)`. -/
@[expose] def cbdNoise128 : ProbComp (List (BitVec 8)) := do
  let b0 ← SignalPqxdh.sampleBytes32
  let b1 ← SignalPqxdh.sampleBytes32
  let b2 ← SignalPqxdh.sampleBytes32
  let b3 ← SignalPqxdh.sampleBytes32
  return (b0 ++ b1 ++ b2 ++ b3).map UInt8.toBitVec

/-- Sample `n` independent 128-byte uniform `CBD_2` input blocks, indexed as
`Fin n → List (BitVec 8)`. -/
@[expose] def cbdNoiseVec (n : Nat) : ProbComp (Fin n → List (BitVec 8)) := do
  let blocks ← (List.range n).mapM fun _ => cbdNoise128
  return fun i => blocks.getD i.val []

/-! ## 2. Centered `CBD_2` Integer Polynomial and Canonicality -/

/-- Centered `CBD_2` integer polynomial extracted from a 128-byte input block. -/
@[expose] def cbd2IntPoly (bs : List (BitVec 8)) : Fin 256 → Int :=
  fun i => centeredZMod (toZPoly (samplePolyCbd2 bs) i)

/-- Single-nibble `CBD_2` sample `(b_0 + b_1) - (b_2 + b_3) ∈ [-2, 2]` for `u : Fin 16`. -/
@[expose] def nibbleToCbd2 (u : Fin 16) : Int :=
  let v := u.val
  (((v &&& 1) + ((v >>> 1) &&& 1) : Nat) : Int) -
    ((((v >>> 2) &&& 1) + ((v >>> 3) &&& 1) : Nat) : Int)

/-- Extract the 256 4-bit nibbles (low nibble at `2 * k`, high nibble at `2 * k + 1`) of a
128-byte block `Fin 128 → BitVec 8`. -/
@[expose] def nibblesOfBlock128 (f : Fin 128 → BitVec 8) (i : Fin 256) : Fin 16 :=
  let b := (f ⟨i.val / 2, by omega⟩).toNat
  if i.val % 2 = 0 then
    ⟨b % 16, by omega⟩
  else
    ⟨b / 16, by have hb := (f ⟨i.val / 2, by omega⟩).isLt; omega⟩

theorem samplePolyCbd2_isCanonical (bs : List (BitVec 8)) :
    IsCanonicalPoly (samplePolyCbd2 bs) := by
  refine ⟨by simp [samplePolyCbd2], fun i hi => ?_⟩
  rw [samplePolyCbd2, getD_ofFn_nat _ _ _ hi]
  exact Nat.mod_lt _ (by decide)

theorem cbd2IntPoly_cast_eq (bs : List (BitVec 8)) (i : Fin 256) :
    ((cbd2IntPoly bs i : Int) : ZMod mlkemQ) = toZPoly (samplePolyCbd2 bs) i :=
  centeredZMod_cast_eq _

theorem samplePolyCbd2_eq_ofZPoly_cbd2IntPoly (bs : List (BitVec 8)) :
    samplePolyCbd2 bs = ofZPoly (fun i => (cbd2IntPoly bs i : ZMod mlkemQ)) := by
  simp_rw [cbd2IntPoly_cast_eq]
  exact (ofZPoly_toZPoly (samplePolyCbd2_isCanonical bs)).symm

private theorem bytesToBits_getD_le_one (bs : List (BitVec 8)) (k : Nat) :
    (bytesToBits bs).getD k 0 ≤ 1 := by
  unfold bytesToBits
  by_cases hk : k < 8 * bs.length
  · rw [getD_ofFn_nat _ _ _ hk]
    dsimp only
    rw [Nat.and_one_is_mod]
    omega
  · simp [Array.getD, hk]

theorem cbd2IntPoly_eq_sub_bits (bs : List (BitVec 8)) (i : Fin 256) :
    let bits := bytesToBits bs
    let a := bits.getD (4 * i.val) 0 + bits.getD (4 * i.val + 1) 0
    let b := bits.getD (4 * i.val + 2) 0 + bits.getD (4 * i.val + 3) 0
    cbd2IntPoly bs i = (a : Int) - (b : Int) := by
  dsimp only
  set bits := bytesToBits bs
  set a := bits.getD (4 * i.val) 0 + bits.getD (4 * i.val + 1) 0
  set b := bits.getD (4 * i.val + 2) 0 + bits.getD (4 * i.val + 3) 0
  have ha0 : bits.getD (4 * i.val) 0 ≤ 1 := bytesToBits_getD_le_one bs _
  have ha1 : bits.getD (4 * i.val + 1) 0 ≤ 1 := bytesToBits_getD_le_one bs _
  have hb0 : bits.getD (4 * i.val + 2) 0 ≤ 1 := bytesToBits_getD_le_one bs _
  have hb1 : bits.getD (4 * i.val + 3) 0 ≤ 1 := bytesToBits_getD_le_one bs _
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 2 := by omega
  have hle : b ≤ a + mlkemQ := by dsimp [mlkemQ]; omega
  have htoZ : toZPoly (samplePolyCbd2 bs) i = (((a : Int) - (b : Int) : Int) : ZMod mlkemQ) := by
    rw [toZPoly, samplePolyCbd2, getD_ofFn_nat _ _ _ i.isLt]
    change (((a + mlkemQ - b) % mlkemQ : Nat) : ZMod mlkemQ) = _
    rw [ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_add]
    have hq : ((mlkemQ : Nat) : ZMod mlkemQ) = 0 := ZMod.natCast_self mlkemQ
    rw [hq, add_zero]
    push_cast
    rfl
  rw [cbd2IntPoly, htoZ]
  exact centeredZMod_of_int_bounds (by omega) (by omega)

theorem cbd2IntPoly_bounds (bs : List (BitVec 8)) (i : Fin 256) :
    -2 ≤ cbd2IntPoly bs i ∧ cbd2IntPoly bs i ≤ 2 := by
  rw [cbd2IntPoly_eq_sub_bits]
  have h0 := bytesToBits_getD_le_one bs (4 * i.val)
  have h1 := bytesToBits_getD_le_one bs (4 * i.val + 1)
  have h2 := bytesToBits_getD_le_one bs (4 * i.val + 2)
  have h3 := bytesToBits_getD_le_one bs (4 * i.val + 3)
  omega

theorem cbd2IntPoly_mem_support (bs : List (BitVec 8)) (i : Fin 256) :
    cbd2IntPoly bs i ∈ cbd2Support := by
  have hb := cbd2IntPoly_bounds bs i
  have hcases :
      cbd2IntPoly bs i = -2 ∨ cbd2IntPoly bs i = -1 ∨ cbd2IntPoly bs i = 0 ∨
        cbd2IntPoly bs i = 1 ∨ cbd2IntPoly bs i = 2 := by omega
  rcases hcases with h | h | h | h | h <;> simp [h, cbd2Support]

private theorem bytesToBits_ofFn_nibble (f : Fin 128 → BitVec 8) (i : Fin 256)
    (r : Nat) (hr : r < 4) :
    (bytesToBits (List.ofFn f)).getD (4 * i.val + r) 0 =
      ((nibblesOfBlock128 f i).val >>> r) &&& 1 := by
  have hlen : (List.ofFn f).length = 128 := List.length_ofFn
  have hidx : 4 * i.val + r < 8 * (List.ofFn f).length := by omega
  rw [bytesToBits, getD_ofFn_nat _ _ _ hidx]
  dsimp only
  have hdiv : (4 * i.val + r) / 8 = i.val / 2 := by omega
  have hmod : (4 * i.val + r) % 8 = 4 * (i.val % 2) + r := by omega
  have harr : ((List.ofFn f).toArray).getD (i.val / 2) 0#8 = f ⟨i.val / 2, by omega⟩ := by
    rw [List.toArray_ofFn, getD_ofFn_nat f (i.val / 2) 0#8 (by omega)]
  rw [hdiv, hmod, harr]
  unfold nibblesOfBlock128
  dsimp only
  set b := (f ⟨i.val / 2, by omega⟩).toNat
  have hb : b < 256 := (f ⟨i.val / 2, by omega⟩).isLt
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  split_ifs with hpar
  · rw [hpar]
    rcases hr_cases with rfl | rfl | rfl | rfl <;>
      simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] <;> omega
  · have hpar1 : i.val % 2 = 1 := by omega
    rw [hpar1]
    rcases hr_cases with rfl | rfl | rfl | rfl <;>
      simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] <;> omega

theorem cbd2IntPoly_ofFn_eq_nibble (f : Fin 128 → BitVec 8) (i : Fin 256) :
    cbd2IntPoly (List.ofFn f) i = nibbleToCbd2 (nibblesOfBlock128 f i) := by
  rw [cbd2IntPoly_eq_sub_bits]
  have h0 := bytesToBits_ofFn_nibble f i 0 (by decide)
  have h1 := bytesToBits_ofFn_nibble f i 1 (by decide)
  have h2 := bytesToBits_ofFn_nibble f i 2 (by decide)
  have h3 := bytesToBits_ofFn_nibble f i 3 (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3]
  simp [nibbleToCbd2]

/-! ## 3. Uniform Byte/Nibble Bijections and Sampler Transport -/

/-- Tuple of four 256-bit words underlying a single `cbdNoise128` draw. -/
abbrev Words4 := BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256

/-- Convert a 256-bit word to its 32 little-endian bytes (`Fin 32 → BitVec 8`). -/
@[expose] def word256ToByteFn (w : BitVec 256) (i : Fin 32) : BitVec 8 :=
  BitVec.ofNat 8 ((w.toNat >>> (8 * i.val)) % 256)

/-- Pack four 256-bit words into an indexed 128-byte block `Fin 128 → BitVec 8`. -/
@[expose] def words4ToBlock128 (w : Words4) (j : Fin 128) : BitVec 8 :=
  let q := j.val / 32
  let r : Fin 32 := ⟨j.val % 32, by omega⟩
  if q = 0 then word256ToByteFn w.1 r
  else if q = 1 then word256ToByteFn w.2.1 r
  else if q = 2 then word256ToByteFn w.2.2.1 r
  else word256ToByteFn w.2.2.2 r

/-- Convert four 256-bit words to the 128-byte `List (BitVec 8)` returned by `cbdNoise128`. -/
@[expose] def words4ToBytes128 (w : Words4) : List (BitVec 8) :=
  List.ofFn (words4ToBlock128 w)

private theorem word256ToBytes_map_toBitVec (w : BitVec 256) :
    (SignalPqxdh.word256ToBytes w).map UInt8.toBitVec = List.ofFn (word256ToByteFn w) := by
  rw [SignalPqxdh.word256ToBytes, List.map_ofFn]
  rfl

private theorem words4ToBytes128_eq_append (w0 w1 w2 w3 : BitVec 256) :
    (SignalPqxdh.word256ToBytes w0 ++ SignalPqxdh.word256ToBytes w1 ++
      SignalPqxdh.word256ToBytes w2 ++ SignalPqxdh.word256ToBytes w3).map UInt8.toBitVec =
      words4ToBytes128 (w0, w1, w2, w3) := by
  simp only [List.map_append, word256ToBytes_map_toBitVec, words4ToBytes128]
  apply List.ext_getElem
  · simp only [List.length_append, List.length_ofFn]
  · intro j hj1 hj2
    simp only [List.length_ofFn] at hj2
    simp only [List.getElem_ofFn, words4ToBlock128]
    by_cases h0 : j < 32
    · have hq : j / 32 = 0 := by omega
      have hr : j % 32 = j := by omega
      have h64 : j < 64 := by omega
      have h96 : j < 96 := by omega
      simp only [List.getElem_append, List.length_append, List.length_ofFn, Nat.reduceAdd,
        List.getElem_ofFn, h0, h64, h96, ↓reduceDIte, hq, ↓reduceIte, hr]
    · by_cases h1 : j < 64
      · have hq : j / 32 = 1 := by omega
        have hr : j % 32 = j - 32 := by omega
        have h96 : j < 96 := by omega
        simp only [List.getElem_append, List.length_append, List.length_ofFn, Nat.reduceAdd,
          List.getElem_ofFn, h0, h1, h96, ↓reduceDIte, hq, one_ne_zero, ↓reduceIte, hr]
      · by_cases h2 : j < 96
        · have hq : j / 32 = 2 := by omega
          have hr : j % 32 = j - 64 := by omega
          have hne0 : (2 : Nat) ≠ 0 := by decide
          have hne1 : (2 : Nat) ≠ 1 := by decide
          simp only [List.getElem_append, List.length_append, List.length_ofFn, Nat.reduceAdd,
            List.getElem_ofFn, h1, h2, ↓reduceDIte, hq, hne0, hne1, ↓reduceIte, hr]
        · have hq : j / 32 = 3 := by omega
          have hr : j % 32 = j - 96 := by omega
          have hne0 : (3 : Nat) ≠ 0 := by decide
          have hne1 : (3 : Nat) ≠ 1 := by decide
          have hne2 : (3 : Nat) ≠ 2 := by decide
          simp only [List.getElem_append, List.length_append, List.length_ofFn, Nat.reduceAdd,
            List.getElem_ofFn, h2, ↓reduceDIte, hq, hne0, hne1, hne2, ↓reduceIte, hr]

theorem word256ToByteFn_bijective : Function.Bijective word256ToByteFn := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro w₁ w₂ h
    apply BitVec.eq_of_toNat_eq
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 256
    · have hi := congrArg BitVec.toNat (congrFun h ⟨k / 8, by omega⟩)
      simp only [word256ToByteFn, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod] at hi
      have hi' : (w₁.toNat >>> (8 * (k / 8))) % 2 ^ 8 = (w₂.toNat >>> (8 * (k / 8))) % 2 ^ 8 := hi
      have htb := congrArg (fun n => n.testBit (k % 8)) hi'
      have hr : k % 8 < 8 := by omega
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at htb
      simp only [hr, decide_true, Bool.true_and, Nat.testBit_shiftRight] at htb
      have heq : 8 * (k / 8) + k % 8 = k := by omega
      rwa [heq] at htb
    · have h1 : w₁.toNat < 2 ^ k :=
        Nat.lt_of_lt_of_le w₁.isLt (Nat.pow_le_pow_right (by decide) (by omega))
      have h2 : w₂.toNat < 2 ^ k :=
        Nat.lt_of_lt_of_le w₂.isLt (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
  · simp [Fintype.card_bitVec, Fintype.card_fin]

theorem words4ToBlock128_bijective : Function.Bijective words4ToBlock128 := by
  have hinj_word := word256ToByteFn_bijective.1
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩ h
    have h1 : word256ToByteFn a1 = word256ToByteFn b1 := by
      funext r
      have hr := congrFun h ⟨r.val, by omega⟩
      have hq : r.val / 32 = 0 := by omega
      have hm : r.val % 32 = r.val := by omega
      simpa [words4ToBlock128, hq, hm] using hr
    have h2 : word256ToByteFn a2 = word256ToByteFn b2 := by
      funext r
      have hr := congrFun h ⟨32 + r.val, by omega⟩
      have hq : (32 + r.val) / 32 = 1 := by omega
      have hm : (32 + r.val) % 32 = r.val := by omega
      simpa [words4ToBlock128, hq, hm] using hr
    have h3 : word256ToByteFn a3 = word256ToByteFn b3 := by
      funext r
      have hr := congrFun h ⟨64 + r.val, by omega⟩
      have hq : (64 + r.val) / 32 = 2 := by omega
      have hm : (64 + r.val) % 32 = r.val := by omega
      simpa [words4ToBlock128, hq, hm] using hr
    have h4 : word256ToByteFn a4 = word256ToByteFn b4 := by
      funext r
      have hr := congrFun h ⟨96 + r.val, by omega⟩
      have hq : (96 + r.val) / 32 = 3 := by omega
      have hm : (96 + r.val) % 32 = r.val := by omega
      simpa [words4ToBlock128, hq, hm] using hr
    rw [hinj_word h1, hinj_word h2, hinj_word h3, hinj_word h4]
  · have hc_word : Fintype.card (BitVec 256) = Fintype.card (Fin 32 → BitVec 8) :=
      Fintype.card_of_bijective word256ToByteFn_bijective
    simp only [Words4, Fintype.card_prod, hc_word, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bitVec]
    ring

theorem nibblesOfBlock128_bijective : Function.Bijective nibblesOfBlock128 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro f g h
    funext j
    apply BitVec.eq_of_toNat_eq
    have hlo := congrArg Fin.val (congrFun h ⟨2 * j.val, by omega⟩)
    have hhi := congrArg Fin.val (congrFun h ⟨2 * j.val + 1, by omega⟩)
    have hj0 : (⟨(2 * j.val) / 2, by omega⟩ : Fin 128) = j := by ext; dsimp only; omega
    have hm0 : (2 * j.val) % 2 = 0 := by omega
    have hj1 : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin 128) = j := by ext; dsimp only; omega
    have hm1 : (2 * j.val + 1) % 2 = 1 := by omega
    simp only [nibblesOfBlock128, hm0, ↓reduceIte, hj0] at hlo
    simp only [nibblesOfBlock128, hm1, one_ne_zero, ↓reduceIte, hj1] at hhi
    omega
  · simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
    change (2 ^ 8) ^ 128 = (2 ^ 4) ^ 256
    simp

private def words4ToNibbles (w : Words4) : Fin 256 → Fin 16 :=
  nibblesOfBlock128 (words4ToBlock128 w)

private theorem words4ToNibbles_bijective : Function.Bijective words4ToNibbles :=
  nibblesOfBlock128_bijective.comp words4ToBlock128_bijective

private theorem cbd2IntPoly_words4ToBytes128 (w : Words4) (i : Fin 256) :
    cbd2IntPoly (words4ToBytes128 w) i = nibbleToCbd2 (words4ToNibbles w i) :=
  cbd2IntPoly_ofFn_eq_nibble (words4ToBlock128 w) i

theorem cbdNoise128_eq_map_words4 :
    cbdNoise128 = words4ToBytes128 <$> ($ᵗ Words4) := by
  dsimp only [Words4]
  rw [SampleableType.uniformSample_prod_eq_bind,
      SampleableType.uniformSample_prod_eq_bind,
      SampleableType.uniformSample_prod_eq_bind]
  simp only [cbdNoise128, SignalPqxdh.sampleBytes32, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def, words4ToBytes128_eq_append]

theorem cbdNoise128_evalDistEq_map_block128 :
    cbdNoise128 =ᵈ (List.ofFn <$> ($ᵗ (Fin 128 → BitVec 8))) := by
  let _ : MeasurableSpace (List (BitVec 8)) := ⊤
  let _ : MeasurableSpace (Fin 128 → BitVec 8) := ⊤
  refine EvalDistEq.of_evalDist_eq ?_
  have hmap : words4ToBytes128 <$> ($ᵗ Words4) =
      List.ofFn <$> (words4ToBlock128 <$> ($ᵗ Words4)) := by
    simp only [Functor.map_map]
    rfl
  have hbij := evalDistEq_iff_evalDist_eq.mp
    (SampleableType.map_uniformSample_evalDistEq_of_bijective words4ToBlock128_bijective)
  rw [cbdNoise128_eq_map_words4, hmap]
  conv_lhs => rw [evalDist_map_of_discrete]
  conv_rhs => rw [evalDist_map_of_discrete]
  rw [hbij]

private def WordsVec1 : Nat → Type
  | 0 => Words4
  | m + 1 => WordsVec1 m × Words4

private instance instSampleableTypeWordsVec1 : ∀ m : Nat, SampleableType (WordsVec1 m)
  | 0 => inferInstanceAs (SampleableType Words4)
  | m + 1 =>
    letI : SampleableType (WordsVec1 m) := instSampleableTypeWordsVec1 m
    inferInstanceAs (SampleableType (WordsVec1 m × Words4))

private def wordsVec1ToList : (m : Nat) → WordsVec1 m → List (List (BitVec 8))
  | 0, w => [words4ToBytes128 w]
  | m + 1, (rest, w) => wordsVec1ToList m rest ++ [words4ToBytes128 w]

private def wordsVec1Get : {m : Nat} → WordsVec1 m → Fin (m + 1) → Words4
  | 0, w, _ => w
  | m + 1, (rest, w), i =>
    if hlt : i.val < m + 1 then wordsVec1Get rest ⟨i.val, hlt⟩ else w

private def wordsVec1OfFn : (m : Nat) → (Fin (m + 1) → Words4) → WordsVec1 m
  | 0, F => F 0
  | m + 1, F => (wordsVec1OfFn m (fun i => F ⟨i.val, by omega⟩), F ⟨m + 1, by omega⟩)

private theorem wordsVec1Get_ofFn :
    ∀ (m : Nat) (F : Fin (m + 1) → Words4) (i : Fin (m + 1)),
      wordsVec1Get (wordsVec1OfFn m F) i = F i
  | 0, F, i => by
    have hi : i = 0 := Fin.ext (by omega)
    subst hi
    rfl
  | m + 1, F, i => by
    simp only [wordsVec1OfFn, wordsVec1Get]
    split_ifs with hlt
    · rw [wordsVec1Get_ofFn m]
    · congr 1
      ext
      dsimp only
      omega

private theorem wordsVec1OfFn_get :
    ∀ (m : Nat) (v : WordsVec1 m), wordsVec1OfFn m (wordsVec1Get v) = v
  | 0, _ => rfl
  | m + 1, (rest, w) => by
    apply Prod.ext
    · change wordsVec1OfFn m (fun i => wordsVec1Get (m := m + 1) (rest, w) ⟨i.val, by omega⟩) = rest
      have hfn : (fun i : Fin (m + 1) => wordsVec1Get (m := m + 1) (rest, w) ⟨i.val, by omega⟩) =
          wordsVec1Get rest := by
        funext i
        simp [wordsVec1Get, i.isLt]
      rw [hfn, wordsVec1OfFn_get m rest]
    · change wordsVec1Get (m := m + 1) (rest, w) ⟨m + 1, by omega⟩ = w
      simp [wordsVec1Get]

private theorem wordsVec1ToList_length :
    ∀ (m : Nat) (v : WordsVec1 m), (wordsVec1ToList m v).length = m + 1
  | 0, _ => rfl
  | m + 1, (rest, _) => by simp [wordsVec1ToList, wordsVec1ToList_length m rest]

private theorem wordsVec1ToList_getD :
    ∀ (m : Nat) (v : WordsVec1 m) (i : Fin (m + 1)),
      (wordsVec1ToList m v).getD i.val [] = words4ToBytes128 (wordsVec1Get v i)
  | 0, w, i => by
    have hi : i.val = 0 := by omega
    simp only [wordsVec1ToList, wordsVec1Get, hi, List.getD, List.getElem?_cons_zero,
      Option.getD_some]
  | m + 1, (rest, w), i => by
    simp only [wordsVec1ToList, wordsVec1Get]
    have hlen : (wordsVec1ToList m rest).length = m + 1 := wordsVec1ToList_length m rest
    split_ifs with hlt
    · have hlt' : i.val < (wordsVec1ToList m rest).length := by omega
      have hget :
          (wordsVec1ToList m rest ++ [words4ToBytes128 w]).getD i.val [] =
            (wordsVec1ToList m rest).getD i.val [] := by
        simp [List.getD, List.getElem?_append_left hlt']
      rw [hget]
      exact wordsVec1ToList_getD m rest ⟨i.val, hlt⟩
    · have hge : (wordsVec1ToList m rest).length ≤ i.val := by omega
      have hsub : i.val - (wordsVec1ToList m rest).length = 0 := by omega
      simp [List.getD, List.getElem?_append_right hge, hsub]

private theorem mapM_range_succ_cbdNoise128 :
    ∀ m : Nat,
      ((List.range (m + 1)).mapM fun _ => cbdNoise128) =
        wordsVec1ToList m <$> ($ᵗ (WordsVec1 m))
  | 0 => by
    change ([0].mapM fun _ => cbdNoise128) =
      (fun w : Words4 => [words4ToBytes128 w]) <$> ($ᵗ Words4)
    simp only [List.mapM_cons, List.mapM_nil, cbdNoise128_eq_map_words4,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  | m + 1 => by
    rw [List.range_succ, List.mapM_append, mapM_range_succ_cbdNoise128 m]
    have hv : ($ᵗ (WordsVec1 (m + 1))) =
        (do let rest ← $ᵗ (WordsVec1 m); let w ← $ᵗ Words4; pure (rest, w)) :=
      SampleableType.uniformSample_prod_eq_bind (WordsVec1 m) Words4
    rw [hv]
    simp only [List.mapM_cons, List.mapM_nil, cbdNoise128_eq_map_words4,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    refine congrArg (Bind.bind ($ᵗ (WordsVec1 m))) (funext fun rest => ?_)
    refine congrArg (Bind.bind ($ᵗ Words4)) (funext fun w => ?_)
    rfl

private def vecWords1ToNoiseVec (m : Nat) (v : WordsVec1 m) (i : Fin (m + 1)) : List (BitVec 8) :=
  words4ToBytes128 (wordsVec1Get v i)

private theorem cbdNoiseVec_succ_eq_map (m : Nat) :
    cbdNoiseVec (m + 1) = vecWords1ToNoiseVec m <$> ($ᵗ (WordsVec1 m)) := by
  unfold cbdNoiseVec
  rw [mapM_range_succ_cbdNoise128 m]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  congr 1
  funext v
  congr 1
  funext i
  exact wordsVec1ToList_getD m v i

/-! ## 4. Exact Rational Uniform Expectation and `cbdNoise128` Factorization -/

/-- Exact rational uniform expectation `(∑ ω : Ω, f ω) / |Ω|` over a finite sample space `Ω`. -/
@[expose] def unifExpectQ {Ω : Type} [Fintype Ω] (f : Ω → Rat) : Rat :=
  (∑ ω : Ω, f ω) / (Fintype.card Ω : Rat)

theorem unifExpectQ_const {Ω : Type} [Fintype Ω] [Nonempty Ω] (c : Rat) :
    unifExpectQ (fun _ : Ω => c) = c := by
  have hcard : (Fintype.card Ω : Rat) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [unifExpectQ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard]

theorem unifExpectQ_add {Ω : Type} [Fintype Ω] (f g : Ω → Rat) :
    unifExpectQ (fun ω => f ω + g ω) = unifExpectQ f + unifExpectQ g := by
  simp [unifExpectQ, Finset.sum_add_distrib, add_div]

theorem unifExpectQ_sum {Ω ι : Type} [Fintype Ω] (s : Finset ι) (f : ι → Ω → Rat) :
    unifExpectQ (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, unifExpectQ (f i) := by
  unfold unifExpectQ
  rw [Finset.sum_comm, Finset.sum_div]

theorem unifExpectQ_const_mul {Ω : Type} [Fintype Ω] (c : Rat) (f : Ω → Rat) :
    unifExpectQ (fun ω => c * f ω) = c * unifExpectQ f := by
  simp [unifExpectQ, ← Finset.mul_sum, mul_div_assoc]

theorem unifExpectQ_mul_const {Ω : Type} [Fintype Ω] (f : Ω → Rat) (c : Rat) :
    unifExpectQ (fun ω => f ω * c) = unifExpectQ f * c := by
  simp [unifExpectQ, ← Finset.sum_mul, mul_div_right_comm]

theorem unifExpectQ_mono {Ω : Type} [Fintype Ω] {f g : Ω → Rat} (h : ∀ ω, f ω ≤ g ω) :
    unifExpectQ f ≤ unifExpectQ g := by
  unfold unifExpectQ
  have hpos : (0 : Rat) ≤ Fintype.card Ω := Nat.cast_nonneg _
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω) hpos

theorem unifExpectQ_nonneg {Ω : Type} [Fintype Ω] {f : Ω → Rat} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ unifExpectQ f := by
  unfold unifExpectQ
  exact div_nonneg (Finset.sum_nonneg fun ω _ => h ω) (Nat.cast_nonneg _)

theorem unifExpectQ_congr_bijective {Ω₁ Ω₂ : Type} [Fintype Ω₁] [Fintype Ω₂]
    {φ : Ω₁ → Ω₂} (hφ : Function.Bijective φ) (f : Ω₂ → Rat) :
    unifExpectQ (fun ω => f (φ ω)) = unifExpectQ f := by
  unfold unifExpectQ
  rw [Fintype.sum_bijective φ hφ _ _ (fun _ => rfl), Fintype.card_of_bijective hφ]

theorem unifExpectQ_prod {α β : Type} [Fintype α] [Fintype β] (f : α × β → Rat) :
    unifExpectQ f = unifExpectQ (fun a => unifExpectQ (fun b => f (a, b))) := by
  unfold unifExpectQ
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, mul_comm (Fintype.card α : Rat),
    ← div_div, Finset.sum_div]

theorem unifExpectQ_prod_swap {α β : Type} [Fintype α] [Fintype β] (f : α × β → Rat) :
    unifExpectQ f = unifExpectQ (fun b => unifExpectQ (fun a => f (a, b))) := by
  rw [← unifExpectQ_congr_bijective (Equiv.prodComm β α).bijective f, unifExpectQ_prod]
  rfl

theorem unifExpectQ_pi_prod {n : Nat} {α : Type} [Fintype α] (g : Fin n → α → Rat) :
    unifExpectQ (fun u : Fin n → α => ∏ i : Fin n, g i (u i)) =
      ∏ i : Fin n, unifExpectQ (fun a => g i a) := by
  unfold unifExpectQ
  rw [← Fintype.prod_sum]
  have hcard : (Fintype.card (Fin n → α) : Rat) = ∏ _i : Fin n, (Fintype.card α : Rat) := by
    simp [Fintype.card_fin]
  rw [hcard, Finset.prod_div_distrib]

theorem unifExpectQ_nibbleToCbd2 (h : Int → Rat) :
    unifExpectQ (fun u : Fin 16 => h (nibbleToCbd2 u)) =
      (cbd2Support.map fun x => cbd2WeightQ x * h x).sum := by
  unfold unifExpectQ
  have hsum :
      (∑ u : Fin 16, h (nibbleToCbd2 u)) =
        h (nibbleToCbd2 0) + (h (nibbleToCbd2 1) + (h (nibbleToCbd2 2) + (h (nibbleToCbd2 3) +
        (h (nibbleToCbd2 4) + (h (nibbleToCbd2 5) + (h (nibbleToCbd2 6) + (h (nibbleToCbd2 7) +
        (h (nibbleToCbd2 8) + (h (nibbleToCbd2 9) + (h (nibbleToCbd2 10) + (h (nibbleToCbd2 11) +
        (h (nibbleToCbd2 12) + (h (nibbleToCbd2 13) + (h (nibbleToCbd2 14) +
          (h (nibbleToCbd2 15) + 0))))))))))))))) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  rw [hsum]
  have h0 : nibbleToCbd2 0 = 0 := rfl
  have h1 : nibbleToCbd2 1 = 1 := rfl
  have h2 : nibbleToCbd2 2 = 1 := rfl
  have h3 : nibbleToCbd2 3 = 2 := rfl
  have h4 : nibbleToCbd2 4 = -1 := rfl
  have h5 : nibbleToCbd2 5 = 0 := rfl
  have h6 : nibbleToCbd2 6 = 0 := rfl
  have h7 : nibbleToCbd2 7 = 1 := rfl
  have h8 : nibbleToCbd2 8 = -1 := rfl
  have h9 : nibbleToCbd2 9 = 0 := rfl
  have h10 : nibbleToCbd2 10 = 0 := rfl
  have h11 : nibbleToCbd2 11 = 1 := rfl
  have h12 : nibbleToCbd2 12 = -2 := rfl
  have h13 : nibbleToCbd2 13 = -1 := rfl
  have h14 : nibbleToCbd2 14 = -1 := rfl
  have h15 : nibbleToCbd2 15 = 0 := rfl
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  simp only [Fintype.card_fin, Nat.cast_ofNat, cbd2Support, cbd2WeightQ, List.map, List.sum_cons,
    List.sum_nil]
  norm_num
  ring

theorem unifExpectQ_nibblePoly_prod (g : Fin 256 → Int → Rat) :
    unifExpectQ (fun u : Fin 256 → Fin 16 => ∏ i : Fin 256, g i (nibbleToCbd2 (u i))) =
      ∏ i : Fin 256, (cbd2Support.map fun x => cbd2WeightQ x * g i x).sum := by
  rw [unifExpectQ_pi_prod (g := fun i a => g i (nibbleToCbd2 a))]
  simp_rw [unifExpectQ_nibbleToCbd2]

/-- Exact 256-coefficient `CBD_2` product expectation factorization over uniform 128-byte blocks
`Fin 128 → BitVec 8`. -/
theorem block128_cbd2IntPoly_prod_expect (g : Fin 256 → Int → Rat) :
    unifExpectQ (fun f : Fin 128 → BitVec 8 => ∏ i : Fin 256, g i (cbd2IntPoly (List.ofFn f) i)) =
      ∏ i : Fin 256, (cbd2Support.map fun x => cbd2WeightQ x * g i x).sum := by
  simp_rw [cbd2IntPoly_ofFn_eq_nibble]
  rw [unifExpectQ_congr_bijective nibblesOfBlock128_bijective
    (fun u : Fin 256 → Fin 16 => ∏ i : Fin 256, g i (nibbleToCbd2 (u i)))]
  exact unifExpectQ_nibblePoly_prod g

/-- Exact 256-coefficient `CBD_2` product expectation factorization over the four 256-bit words of
`cbdNoise128`. -/
theorem cbdNoise128_prod_expect (g : Fin 256 → Int → Rat) :
    unifExpectQ (fun w : Words4 => ∏ i : Fin 256, g i (cbd2IntPoly (words4ToBytes128 w) i)) =
      ∏ i : Fin 256, (cbd2Support.map fun x => cbd2WeightQ x * g i x).sum := by
  simp_rw [cbd2IntPoly_words4ToBytes128]
  rw [unifExpectQ_congr_bijective words4ToNibbles_bijective
    (fun u : Fin 256 → Fin 16 => ∏ i : Fin 256, g i (nibbleToCbd2 (u i)))]
  exact unifExpectQ_nibblePoly_prod g

private theorem unifExpectQ_nibbleVec4_prod (g : Fin 4 → Fin 256 → Int → Rat) :
    unifExpectQ
        (fun U : Fin 4 → Fin 256 → Fin 16 =>
          ∏ k : Fin 4, ∏ i : Fin 256, g k i (nibbleToCbd2 (U k i))) =
      ∏ k : Fin 4, ∏ i : Fin 256, (cbd2Support.map fun x => cbd2WeightQ x * g k i x).sum := by
  rw [unifExpectQ_pi_prod
    (g := fun k (u : Fin 256 → Fin 16) => ∏ i : Fin 256, g k i (nibbleToCbd2 (u i)))]
  simp_rw [unifExpectQ_nibblePoly_prod]

/-! ## 5. Negacyclic Permutation, `CBD_2` Symmetry, and W2 Noise Definitions -/

/-- Extract secret-key polynomial vector `s` (`blocks 0..3`) from `nKG : Fin 8 → List (BitVec 8)`. -/
@[expose] def kgS (nKG : Fin 8 → List (BitVec 8)) (k : Fin 4) : Fin 256 → Int :=
  cbd2IntPoly (nKG ⟨k.val, by omega⟩)

/-- Extract key-generation error vector `e` (`blocks 4..7`) from `nKG : Fin 8 → List (BitVec 8)`. -/
@[expose] def kgE (nKG : Fin 8 → List (BitVec 8)) (k : Fin 4) : Fin 256 → Int :=
  cbd2IntPoly (nKG ⟨4 + k.val, by omega⟩)

/-- Extract encryption randomness vector `r` (`blocks 0..3`) from `nEnc : Fin 9 → List (BitVec 8)`. -/
@[expose] def encR (nEnc : Fin 9 → List (BitVec 8)) (k : Fin 4) : Fin 256 → Int :=
  cbd2IntPoly (nEnc ⟨k.val, by omega⟩)

/-- Extract ciphertext `u`-error vector `e_1` (`blocks 4..7`) from `nEnc : Fin 9 → List (BitVec 8)`. -/
@[expose] def encE1 (nEnc : Fin 9 → List (BitVec 8)) (k : Fin 4) : Fin 256 → Int :=
  cbd2IntPoly (nEnc ⟨4 + k.val, by omega⟩)

/-- Extract ciphertext `v`-error polynomial `e_2` (`block 8`) from `nEnc : Fin 9 → List (BitVec 8)`. -/
@[expose] def encE2 (nEnc : Fin 9 → List (BitVec 8)) : Fin 256 → Int :=
  cbd2IntPoly (nEnc ⟨8, by decide⟩)

/-- K-PKE `eᵀ r` integer noise component at coefficient `j`. -/
@[expose] def erTerm (e r : Fin 4 → Fin 256 → Int) (j : Fin 256) : Int :=
  ∑ k : Fin 4, negacyclicMulInt (e k) (r k) j

/-- K-PKE `sᵀ (e_1 + Δu)` integer noise component at coefficient `j`. -/
@[expose] def sdTerm (wVec : Fin 4 → ZPoly) (s e1 : Fin 4 → Fin 256 → Int) (j : Fin 256) : Int :=
  ∑ k : Fin 4,
    negacyclicMulInt (s k)
      (fun i => e1 k i + compressErrZMod 11 (wVec k i + (e1 k i : ZMod mlkemQ))) j

/-- K-PKE `v`-compression + `e_2` integer noise component at coefficient `j`. -/
@[expose] def vTerm (v0 : ZPoly) (e2 : Fin 256 → Int) (j : Fin 256) : Int :=
  centeredZMod
    ((decompressCoeff 5 (compressCoeff 5 (v0 j + (e2 j : ZMod mlkemQ)).val) : ZMod mlkemQ) - v0 j)

/-- Total K-PKE integer decryption noise `eᵀ r - sᵀ (e_1 + Δu) + (Dec_5(Comp_5(v_0 + e_2)) - v_0)`
at coefficient `j : Fin 256`. -/
@[expose] def intNoise (wVec : Fin 4 → ZPoly) (v0 : ZPoly)
    (s e r e1 : Fin 4 → Fin 256 → Int) (e2 : Fin 256 → Int) (j : Fin 256) : Int :=
  erTerm e r j - sdTerm wVec s e1 j + vTerm v0 e2 j

/-- Rational `CBD_2` moment-generating function at base `λ = 5/4`:
`E_{x ~ CBD_2}[(5/4)^{t x}]`. -/
@[expose] def cbd2Mgf54 (t : Int) : Rat :=
  (cbd2Support.map fun x => cbd2WeightQ x * (5 / 4 : Rat) ^ (t * x)).sum

theorem vTerm_cast_eq (v0 : ZPoly) (e2 : Fin 256 → Int) (j : Fin 256) :
    ((vTerm v0 e2 j : Int) : ZMod mlkemQ) =
      (e2 j : ZMod mlkemQ) +
        (compressErrZMod 5 (v0 j + (e2 j : ZMod mlkemQ)) : ZMod mlkemQ) := by
  unfold vTerm compressErrZMod
  rw [centeredZMod_cast_eq, centeredZMod_cast_eq]
  ring

theorem intNoise_cast_eq (wVec : Fin 4 → ZPoly) (v0 : ZPoly)
    (s e r e1 : Fin 4 → Fin 256 → Int) (e2 : Fin 256 → Int) (j : Fin 256) :
    ((intNoise wVec v0 s e r e1 e2 j : Int) : ZMod mlkemQ) =
      (∑ k : Fin 4,
        negacyclicMul (fun i => (e k i : ZMod mlkemQ)) (fun i => (r k i : ZMod mlkemQ)) j) -
      (∑ k : Fin 4,
        negacyclicMul (fun i => (s k i : ZMod mlkemQ))
          (fun i => (e1 k i : ZMod mlkemQ) +
            (compressErrZMod 11 (wVec k i + (e1 k i : ZMod mlkemQ)) : ZMod mlkemQ)) j) +
      ((decompressCoeff 5 (compressCoeff 5 (v0 j + (e2 j : ZMod mlkemQ)).val) : ZMod mlkemQ) -
        v0 j) := by
  unfold intNoise erTerm sdTerm vTerm
  push_cast
  simp_rw [negacyclicMulInt_cast, centeredZMod_cast_eq]
  have hsd :
      (∑ k : Fin 4,
        negacyclicMul (fun i => (s k i : ZMod mlkemQ))
          (fun i =>
            ((e1 k i + compressErrZMod 11 (wVec k i + (e1 k i : ZMod mlkemQ)) : Int) :
              ZMod mlkemQ)) j) =
      (∑ k : Fin 4,
        negacyclicMul (fun i => (s k i : ZMod mlkemQ))
          (fun i => (e1 k i : ZMod mlkemQ) +
            (compressErrZMod 11 (wVec k i + (e1 k i : ZMod mlkemQ)) : ZMod mlkemQ)) j) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hfn :
        (fun i : Fin 256 =>
          ((e1 k i + compressErrZMod 11 (wVec k i + (e1 k i : ZMod mlkemQ)) : Int) :
            ZMod mlkemQ)) =
        (fun i : Fin 256 =>
          (e1 k i : ZMod mlkemQ) +
            (compressErrZMod 11 (wVec k i + (e1 k i : ZMod mlkemQ)) : ZMod mlkemQ)) := by
      funext i
      push_cast
      rfl
    rw [hfn]
  rw [hsd]

/-- Sign factor `+1` (`i ≤ j`) or `-1` (`i > j`) in negacyclic convolution at index `j`. -/
@[expose] def negacyclicSign (j i : Fin 256) : Int :=
  if i.val ≤ j.val then 1 else -1

/-- Index involution `i ↦ (j - i) mod 256` pairing `a_i` with `b_{negacyclicPerm j i}` in
`negacyclicMulInt a b j`. -/
@[expose] def negacyclicPerm (j i : Fin 256) : Fin 256 :=
  if _ : i.val ≤ j.val then
    ⟨j.val - i.val, by omega⟩
  else
    ⟨256 + j.val - i.val, by omega⟩

theorem negacyclicMulInt_eq_sum_sign_perm (a b : Fin 256 → Int) (j : Fin 256) :
    negacyclicMulInt a b j = ∑ i : Fin 256, negacyclicSign j i * a i * b (negacyclicPerm j i) := by
  unfold negacyclicMulInt negacyclicSign negacyclicPerm
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

theorem negacyclicPerm_involutive (j : Fin 256) : Function.Involutive (negacyclicPerm j) := by
  intro i
  by_cases h1 : i.val ≤ j.val
  · have hp1 : negacyclicPerm j i = ⟨j.val - i.val, by omega⟩ := by
      simp only [negacyclicPerm, h1, ↓reduceDIte]
    rw [hp1]
    have h2 : (⟨j.val - i.val, by omega⟩ : Fin 256).val ≤ j.val := by dsimp only; omega
    simp only [negacyclicPerm, h2, ↓reduceDIte]
    ext
    dsimp only
    omega
  · have hp1 : negacyclicPerm j i = ⟨256 + j.val - i.val, by omega⟩ := by
      simp only [negacyclicPerm, h1, ↓reduceDIte]
    rw [hp1]
    have h2 : ¬ ((⟨256 + j.val - i.val, by omega⟩ : Fin 256).val ≤ j.val) := by
      dsimp only
      omega
    simp only [negacyclicPerm, h2, ↓reduceDIte]
    ext
    dsimp only
    omega

/-- Equivalence `Fin 256 ≃ Fin 256` induced by the involution `negacyclicPerm j`. -/
@[expose] def negacyclicPermEquiv (j : Fin 256) : Fin 256 ≃ Fin 256 :=
  (negacyclicPerm_involutive j).toPerm

private theorem cbd2WeightQ_nonneg (x : Int) : 0 ≤ cbd2WeightQ x := by
  unfold cbd2WeightQ
  split_ifs <;> norm_num

private theorem cbd2WeightQ_sum_one : (cbd2Support.map cbd2WeightQ).sum = 1 := by
  simp only [cbd2Support, cbd2WeightQ, List.map, List.sum_cons, List.sum_nil]
  norm_num

private theorem cbd2Support_sum_nonneg (f : Int → Rat) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ (cbd2Support.map fun x => cbd2WeightQ x * f x).sum := by
  simp only [cbd2Support, List.map, List.sum_cons, List.sum_nil]
  have h1 := mul_nonneg (cbd2WeightQ_nonneg (-2)) (hf (-2))
  have h2 := mul_nonneg (cbd2WeightQ_nonneg (-1)) (hf (-1))
  have h3 := mul_nonneg (cbd2WeightQ_nonneg 0) (hf 0)
  have h4 := mul_nonneg (cbd2WeightQ_nonneg 1) (hf 1)
  have h5 := mul_nonneg (cbd2WeightQ_nonneg 2) (hf 2)
  linarith

theorem cbd2Mgf54_nonneg (t : Int) : 0 ≤ cbd2Mgf54 t :=
  cbd2Support_sum_nonneg _ fun _ => zpow_nonneg (by norm_num) _

theorem cbd2Mgf54_neg (t : Int) : cbd2Mgf54 (-t) = cbd2Mgf54 t := by
  unfold cbd2Mgf54
  simp only [cbd2Support, cbd2WeightQ, List.map, List.sum_cons, List.sum_nil]
  have e1 : -t * -2 = t * 2 := by ring
  have e2 : -t * -1 = t * 1 := by ring
  have e3 : -t * 0 = t * 0 := by ring
  have e4 : -t * 1 = t * -1 := by ring
  have e5 : -t * 2 = t * -2 := by ring
  rw [e1, e2, e3, e4, e5]
  norm_num
  ring

theorem cbd2Mgf54_sign_mul {τ : Int} (hτ : τ = 1 ∨ τ = -1) (t : Int) :
    cbd2Mgf54 (τ * t) = cbd2Mgf54 t := by
  rcases hτ with rfl | rfl
  · simp
  · simpa using cbd2Mgf54_neg t

private theorem pow54_sum {ι : Type} (s : Finset ι) (f : ι → Int) :
    (5 / 4 : Rat) ^ (∑ i ∈ s, f i) = ∏ i ∈ s, (5 / 4 : Rat) ^ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ (by norm_num : (5 / 4 : Rat) ≠ 0), ih]

/-! ## 6. Conditioned W2 MGF and Full Tail Bound -/

private abbrev NibblePoly := Fin 256 → Fin 16
private abbrev NibbleVec4 := Fin 4 → Fin 256 → Fin 16
private abbrev W2SampleSpace :=
  NibbleVec4 × NibbleVec4 × NibbleVec4 × NibbleVec4 × NibblePoly

private def cbdPolyOfNibbles (u : NibblePoly) : Fin 256 → Int :=
  fun i => nibbleToCbd2 (u i)

private def cbdVec4OfNibbles (U : NibbleVec4) : Fin 4 → Fin 256 → Int :=
  fun k i => nibbleToCbd2 (U k i)

private theorem expect_vTerm_le (v0 : ZPoly) (j : Fin 256) {σ : Int}
    (hσ : σ ∈ ([1, -1] : List Int)) {H_ub : Rat}
    (hH : ∀ v0c : ZMod mlkemQ, ∀ σ' ∈ ([1, -1] : List Int),
      (cbd2Support.map fun e =>
        cbd2WeightQ e *
          (5 / 4 : Rat) ^ (σ' * centeredZMod
            ((decompressCoeff 5 (compressCoeff 5 (v0c + (e : ZMod mlkemQ)).val) : ZMod mlkemQ) -
              v0c))).sum ≤ H_ub) :
    unifExpectQ (fun u_e2 : NibblePoly =>
      (5 / 4 : Rat) ^ (σ * vTerm v0 (cbdPolyOfNibbles u_e2) j)) ≤ H_ub := by
  have hprod :
      (fun u_e2 : NibblePoly => (5 / 4 : Rat) ^ (σ * vTerm v0 (cbdPolyOfNibbles u_e2) j)) =
        (fun u_e2 : NibblePoly =>
          ∏ i : Fin 256,
            (if i = j then
              (5 / 4 : Rat) ^ (σ * centeredZMod
                ((decompressCoeff 5
                    (compressCoeff 5 (v0 j + (nibbleToCbd2 (u_e2 i) : ZMod mlkemQ)).val) :
                  ZMod mlkemQ) - v0 j))
             else 1)) := by
    funext u_e2
    rw [Finset.prod_ite_eq']
    simp [vTerm, cbdPolyOfNibbles]
  rw [hprod,
    unifExpectQ_nibblePoly_prod
      (g := fun i x =>
        if i = j then
          (5 / 4 : Rat) ^ (σ * centeredZMod
            ((decompressCoeff 5 (compressCoeff 5 (v0 j + (x : ZMod mlkemQ)).val) :
              ZMod mlkemQ) - v0 j))
        else 1)]
  have hfactor :
      (∏ i : Fin 256,
        (cbd2Support.map fun x =>
          cbd2WeightQ x *
            (if i = j then
              (5 / 4 : Rat) ^ (σ * centeredZMod
                ((decompressCoeff 5 (compressCoeff 5 (v0 j + (x : ZMod mlkemQ)).val) :
                  ZMod mlkemQ) - v0 j))
             else 1)).sum) =
      (cbd2Support.map fun x =>
        cbd2WeightQ x *
          (5 / 4 : Rat) ^ (σ * centeredZMod
            ((decompressCoeff 5 (compressCoeff 5 (v0 j + (x : ZMod mlkemQ)).val) :
              ZMod mlkemQ) - v0 j))).sum := by
    have hite : ∀ i : Fin 256,
        (cbd2Support.map fun x =>
          cbd2WeightQ x *
            (if i = j then
              (5 / 4 : Rat) ^ (σ * centeredZMod
                ((decompressCoeff 5 (compressCoeff 5 (v0 j + (x : ZMod mlkemQ)).val) :
                  ZMod mlkemQ) - v0 j))
             else 1)).sum =
        if i = j then
          (cbd2Support.map fun x =>
            cbd2WeightQ x *
              (5 / 4 : Rat) ^ (σ * centeredZMod
                ((decompressCoeff 5 (compressCoeff 5 (v0 j + (x : ZMod mlkemQ)).val) :
                  ZMod mlkemQ) - v0 j))).sum
        else 1 := by
      intro i
      split_ifs with hij
      · rfl
      · simp [cbd2WeightQ_sum_one]
    simp_rw [hite]
    simp [Finset.prod_ite_eq']
  rw [hfactor]
  exact hH (v0 j) σ hσ

private theorem rat_prod_le_prod {ι : Type} (s : Finset ι) {f g : ι → Rat}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    (∏ i ∈ s, f i) ≤ ∏ i ∈ s, g i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    have hfa : 0 ≤ f a := h0 a (Finset.mem_cons_self a s)
    have hga : 0 ≤ g a := le_trans hfa (h1 a (Finset.mem_cons_self a s))
    have hps : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg fun i hi => h0 i (Finset.mem_cons_of_mem hi)
    exact mul_le_mul (h1 a (Finset.mem_cons_self a s))
      (ih (fun i hi => h0 i (Finset.mem_cons_of_mem hi))
          (fun i hi => h1 i (Finset.mem_cons_of_mem hi)))
      hps hga

private theorem expect_sdTerm_le (w : Fin 4 → ZPoly) (j : Fin 256) {σ : Int}
    (hσ : σ = 1 ∨ σ = -1) {G_ub : Rat}
    (hG : ∀ wc : ZMod mlkemQ,
      (cbd2Support.map fun e =>
        cbd2WeightQ e * cbd2Mgf54 (e + compressErrZMod 11 (wc + (e : ZMod mlkemQ)))).sum ≤ G_ub) :
    unifExpectQ (fun p : NibbleVec4 × NibbleVec4 =>
      (5 / 4 : Rat) ^ (-(σ * sdTerm w (cbdVec4OfNibbles p.1) (cbdVec4OfNibbles p.2) j))) ≤
      G_ub ^ 1024 := by
  rw [unifExpectQ_prod_swap]
  have hinner : ∀ u_e1 : NibbleVec4,
      unifExpectQ (fun u_s : NibbleVec4 =>
        (5 / 4 : Rat) ^ (-(σ * sdTerm w (cbdVec4OfNibbles u_s) (cbdVec4OfNibbles u_e1) j))) =
        ∏ k : Fin 4, ∏ m : Fin 256,
          cbd2Mgf54 (nibbleToCbd2 (u_e1 k m) +
            compressErrZMod 11 (w k m + (nibbleToCbd2 (u_e1 k m) : ZMod mlkemQ))) := by
    intro u_e1
    let d : Fin 4 → Fin 256 → Int := fun k m =>
      nibbleToCbd2 (u_e1 k m) +
        compressErrZMod 11 (w k m + (nibbleToCbd2 (u_e1 k m) : ZMod mlkemQ))
    have hexp : ∀ u_s : NibbleVec4,
        -(σ * sdTerm w (cbdVec4OfNibbles u_s) (cbdVec4OfNibbles u_e1) j) =
          ∑ k : Fin 4, ∑ i : Fin 256,
            ((-(σ * negacyclicSign j i)) * d k (negacyclicPerm j i)) *
              nibbleToCbd2 (u_s k i) := by
      intro u_s
      unfold sdTerm cbdVec4OfNibbles
      simp_rw [negacyclicMulInt_eq_sum_sign_perm, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      dsimp only [d]
      ring
    simp_rw [hexp, pow54_sum]
    rw [unifExpectQ_nibbleVec4_prod
      (g := fun k i x =>
        (5 / 4 : Rat) ^ (((-(σ * negacyclicSign j i)) * d k (negacyclicPerm j i)) * x))]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hsign : ∀ i : Fin 256,
        (cbd2Support.map fun x =>
          cbd2WeightQ x *
            (5 / 4 : Rat) ^
              (((-(σ * negacyclicSign j i)) * d k (negacyclicPerm j i)) * x)).sum =
          cbd2Mgf54 (d k (negacyclicPerm j i)) := by
      intro i
      have hτ : -(σ * negacyclicSign j i) = 1 ∨ -(σ * negacyclicSign j i) = -1 := by
        unfold negacyclicSign
        rcases hσ with rfl | rfl <;> split_ifs <;> simp
      exact cbd2Mgf54_sign_mul hτ (d k (negacyclicPerm j i))
    simp_rw [hsign]
    exact Equiv.prod_comp (negacyclicPermEquiv j) (fun m => cbd2Mgf54 (d k m))
  simp_rw [hinner]
  rw [unifExpectQ_nibbleVec4_prod
    (g := fun k m x => cbd2Mgf54 (x + compressErrZMod 11 (w k m + (x : ZMod mlkemQ))))]
  have hle1 :
      (∏ k : Fin 4, ∏ m : Fin 256,
        (cbd2Support.map fun x =>
          cbd2WeightQ x *
            cbd2Mgf54 (x + compressErrZMod 11 (w k m + (x : ZMod mlkemQ)))).sum) ≤
        ∏ _k : Fin 4, ∏ _m : Fin 256, G_ub := by
    apply rat_prod_le_prod
    · intro k _
      exact Finset.prod_nonneg fun m _ =>
        cbd2Support_sum_nonneg _ fun _ => cbd2Mgf54_nonneg _
    · intro k _
      apply rat_prod_le_prod
      · intro m _
        exact cbd2Support_sum_nonneg _ fun _ => cbd2Mgf54_nonneg _
      · intro m _
        exact hG (w k m)
  calc
    (∏ k : Fin 4, ∏ m : Fin 256,
        (cbd2Support.map fun x =>
          cbd2WeightQ x *
            cbd2Mgf54 (x + compressErrZMod 11 (w k m + (x : ZMod mlkemQ)))).sum)
      ≤ ∏ _k : Fin 4, ∏ _m : Fin 256, G_ub := hle1
    _ = G_ub ^ 1024 := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

private theorem expect_erTerm_le (j : Fin 256) {σ : Int}
    (hσ : σ = 1 ∨ σ = -1) {A : Rat}
    (hA : (cbd2Support.map fun x => cbd2WeightQ x * cbd2Mgf54 x).sum ≤ A) :
    unifExpectQ (fun p : NibbleVec4 × NibbleVec4 =>
      (5 / 4 : Rat) ^ (σ * erTerm (cbdVec4OfNibbles p.1) (cbdVec4OfNibbles p.2) j)) ≤
      A ^ 1024 := by
  rw [unifExpectQ_prod_swap]
  have hinner : ∀ u_r : NibbleVec4,
      unifExpectQ (fun u_e : NibbleVec4 =>
        (5 / 4 : Rat) ^ (σ * erTerm (cbdVec4OfNibbles u_e) (cbdVec4OfNibbles u_r) j)) =
        ∏ k : Fin 4, ∏ m : Fin 256, cbd2Mgf54 (nibbleToCbd2 (u_r k m)) := by
    intro u_r
    have hexp : ∀ u_e : NibbleVec4,
        σ * erTerm (cbdVec4OfNibbles u_e) (cbdVec4OfNibbles u_r) j =
          ∑ k : Fin 4, ∑ i : Fin 256,
            ((σ * negacyclicSign j i) * nibbleToCbd2 (u_r k (negacyclicPerm j i))) *
              nibbleToCbd2 (u_e k i) := by
      intro u_e
      unfold erTerm cbdVec4OfNibbles
      simp_rw [negacyclicMulInt_eq_sum_sign_perm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    simp_rw [hexp, pow54_sum]
    rw [unifExpectQ_nibbleVec4_prod
      (g := fun k i x =>
        (5 / 4 : Rat) ^
          (((σ * negacyclicSign j i) * nibbleToCbd2 (u_r k (negacyclicPerm j i))) * x))]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hsign : ∀ i : Fin 256,
        (cbd2Support.map fun x =>
          cbd2WeightQ x *
            (5 / 4 : Rat) ^
              (((σ * negacyclicSign j i) * nibbleToCbd2 (u_r k (negacyclicPerm j i))) * x)).sum =
          cbd2Mgf54 (nibbleToCbd2 (u_r k (negacyclicPerm j i))) := by
      intro i
      have hτ : σ * negacyclicSign j i = 1 ∨ σ * negacyclicSign j i = -1 := by
        unfold negacyclicSign
        rcases hσ with rfl | rfl <;> split_ifs <;> simp
      exact cbd2Mgf54_sign_mul hτ _
    simp_rw [hsign]
    exact Equiv.prod_comp (negacyclicPermEquiv j) (fun m => cbd2Mgf54 (nibbleToCbd2 (u_r k m)))
  simp_rw [hinner]
  rw [unifExpectQ_nibbleVec4_prod (g := fun _ _ x => cbd2Mgf54 x)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  exact pow_le_pow_left₀ (cbd2Support_sum_nonneg _ fun _ => cbd2Mgf54_nonneg _) hA 1024

private def w2ReorderEquiv :
    W2SampleSpace ≃ ((NibbleVec4 × NibbleVec4) × ((NibbleVec4 × NibbleVec4) × NibblePoly)) where
  toFun ω := ((ω.2.1, ω.2.2.1), ((ω.1, ω.2.2.2.1), ω.2.2.2.2))
  invFun p := (p.2.1.1, p.1.1, p.1.2, p.2.1.2, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def w2NoiseOnSpace
    (wVecFn : (Fin 4 → Fin 256 → Int) → Fin 4 → ZPoly)
    (v0Fn : (Fin 4 → Fin 256 → Int) → (Fin 4 → Fin 256 → Int) → (Fin 4 → Fin 256 → Int) → ZPoly)
    (ω : W2SampleSpace) : Fin 256 → Int :=
  let s := cbdVec4OfNibbles ω.1
  let e := cbdVec4OfNibbles ω.2.1
  let r := cbdVec4OfNibbles ω.2.2.1
  let e1 := cbdVec4OfNibbles ω.2.2.2.1
  let e2 := cbdPolyOfNibbles ω.2.2.2.2
  intNoise (wVecFn r) (v0Fn s e r) s e r e1 e2

private theorem w2_mgf_bound_per_coeff
    (wVecFn : (Fin 4 → Fin 256 → Int) → Fin 4 → ZPoly)
    (v0Fn : (Fin 4 → Fin 256 → Int) → (Fin 4 → Fin 256 → Int) → (Fin 4 → Fin 256 → Int) → ZPoly)
    (j : Fin 256) {σ : Int} (hσ_mem : σ ∈ ([1, -1] : List Int))
    {A G_ub H_ub : Rat}
    (hA : (cbd2Support.map fun x => cbd2WeightQ x * cbd2Mgf54 x).sum ≤ A)
    (hG : ∀ wc : ZMod mlkemQ,
      (cbd2Support.map fun e =>
        cbd2WeightQ e * cbd2Mgf54 (e + compressErrZMod 11 (wc + (e : ZMod mlkemQ)))).sum ≤ G_ub)
    (hH : ∀ v0c : ZMod mlkemQ, ∀ σ' ∈ ([1, -1] : List Int),
      (cbd2Support.map fun e =>
        cbd2WeightQ e *
          (5 / 4 : Rat) ^ (σ' * centeredZMod
            ((decompressCoeff 5 (compressCoeff 5 (v0c + (e : ZMod mlkemQ)).val) : ZMod mlkemQ) -
              v0c))).sum ≤ H_ub) :
    unifExpectQ (fun ω : W2SampleSpace => (5 / 4 : Rat) ^ (σ * w2NoiseOnSpace wVecFn v0Fn ω j)) ≤
      A ^ 1024 * G_ub ^ 1024 * H_ub := by
  have hσ : σ = 1 ∨ σ = -1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ_mem
    exact hσ_mem
  have hG_nonneg : 0 ≤ G_ub :=
    le_trans (cbd2Support_sum_nonneg _ fun _ => cbd2Mgf54_nonneg _) (hG 0)
  have hH_nonneg : 0 ≤ H_ub :=
    le_trans (cbd2Support_sum_nonneg _ fun _ => zpow_nonneg (by norm_num) _) (hH 0 σ hσ_mem)
  rw [← unifExpectQ_congr_bijective w2ReorderEquiv.symm.bijective]
  rw [unifExpectQ_prod]
  have houter : ∀ er : NibbleVec4 × NibbleVec4,
      unifExpectQ (fun se : (NibbleVec4 × NibbleVec4) × NibblePoly =>
        (5 / 4 : Rat) ^
          (σ * w2NoiseOnSpace wVecFn v0Fn (w2ReorderEquiv.symm (er, se)) j)) ≤
        ((5 / 4 : Rat) ^ (σ * erTerm (cbdVec4OfNibbles er.1) (cbdVec4OfNibbles er.2) j)) *
          (G_ub ^ 1024 * H_ub) := by
    intro er
    rw [unifExpectQ_prod]
    have hmid : ∀ se1 : NibbleVec4 × NibbleVec4,
        unifExpectQ (fun u_e2 : NibblePoly =>
          (5 / 4 : Rat) ^
            (σ * w2NoiseOnSpace wVecFn v0Fn (w2ReorderEquiv.symm (er, (se1, u_e2))) j)) ≤
          (((5 / 4 : Rat) ^ (σ * erTerm (cbdVec4OfNibbles er.1) (cbdVec4OfNibbles er.2) j)) *
            ((5 / 4 : Rat) ^
              (-(σ * sdTerm (wVecFn (cbdVec4OfNibbles er.2))
                (cbdVec4OfNibbles se1.1) (cbdVec4OfNibbles se1.2) j)))) * H_ub := by
      intro se1
      have hsplit : ∀ u_e2 : NibblePoly,
          (5 / 4 : Rat) ^
            (σ * w2NoiseOnSpace wVecFn v0Fn (w2ReorderEquiv.symm (er, (se1, u_e2))) j) =
          (((5 / 4 : Rat) ^ (σ * erTerm (cbdVec4OfNibbles er.1) (cbdVec4OfNibbles er.2) j)) *
            ((5 / 4 : Rat) ^
              (-(σ * sdTerm (wVecFn (cbdVec4OfNibbles er.2))
                (cbdVec4OfNibbles se1.1) (cbdVec4OfNibbles se1.2) j)))) *
            ((5 / 4 : Rat) ^
              (σ * vTerm (v0Fn (cbdVec4OfNibbles se1.1) (cbdVec4OfNibbles er.1)
                (cbdVec4OfNibbles er.2)) (cbdPolyOfNibbles u_e2) j)) := by
        intro u_e2
        dsimp only [w2NoiseOnSpace, w2ReorderEquiv, intNoise, Equiv.symm_mk, Equiv.coe_fn_mk]
        have hexp :
            σ * (erTerm (cbdVec4OfNibbles er.1) (cbdVec4OfNibbles er.2) j -
              sdTerm (wVecFn (cbdVec4OfNibbles er.2))
                (cbdVec4OfNibbles se1.1) (cbdVec4OfNibbles se1.2) j +
              vTerm (v0Fn (cbdVec4OfNibbles se1.1) (cbdVec4OfNibbles er.1)
                (cbdVec4OfNibbles er.2)) (cbdPolyOfNibbles u_e2) j) =
            (σ * erTerm (cbdVec4OfNibbles er.1) (cbdVec4OfNibbles er.2) j +
              -(σ * sdTerm (wVecFn (cbdVec4OfNibbles er.2))
                (cbdVec4OfNibbles se1.1) (cbdVec4OfNibbles se1.2) j)) +
              σ * vTerm (v0Fn (cbdVec4OfNibbles se1.1) (cbdVec4OfNibbles er.1)
                (cbdVec4OfNibbles er.2)) (cbdPolyOfNibbles u_e2) j := by ring
        rw [hexp, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
      simp_rw [hsplit]
      rw [unifExpectQ_const_mul]
      refine mul_le_mul_of_nonneg_left (expect_vTerm_le _ j hσ_mem hH) ?_
      exact mul_nonneg (zpow_nonneg (by norm_num) _) (zpow_nonneg (by norm_num) _)
    calc
      unifExpectQ (fun se1 : NibbleVec4 × NibbleVec4 =>
          unifExpectQ (fun u_e2 : NibblePoly =>
            (5 / 4 : Rat) ^
              (σ * w2NoiseOnSpace wVecFn v0Fn (w2ReorderEquiv.symm (er, (se1, u_e2))) j)))
        ≤ unifExpectQ (fun se1 : NibbleVec4 × NibbleVec4 =>
            (((5 / 4 : Rat) ^ (σ * erTerm (cbdVec4OfNibbles er.1) (cbdVec4OfNibbles er.2) j)) *
              ((5 / 4 : Rat) ^
                (-(σ * sdTerm (wVecFn (cbdVec4OfNibbles er.2))
                  (cbdVec4OfNibbles se1.1) (cbdVec4OfNibbles se1.2) j)))) * H_ub) :=
          unifExpectQ_mono hmid
      _ = ((5 / 4 : Rat) ^ (σ * erTerm (cbdVec4OfNibbles er.1) (cbdVec4OfNibbles er.2) j)) *
            (unifExpectQ (fun se1 : NibbleVec4 × NibbleVec4 =>
              (5 / 4 : Rat) ^
                (-(σ * sdTerm (wVecFn (cbdVec4OfNibbles er.2))
                  (cbdVec4OfNibbles se1.1) (cbdVec4OfNibbles se1.2) j))) * H_ub) := by
          rw [unifExpectQ_mul_const, unifExpectQ_const_mul, mul_assoc]
      _ ≤ ((5 / 4 : Rat) ^ (σ * erTerm (cbdVec4OfNibbles er.1) (cbdVec4OfNibbles er.2) j)) *
            (G_ub ^ 1024 * H_ub) := by
          refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg (by norm_num) _)
          exact mul_le_mul_of_nonneg_right (expect_sdTerm_le _ j hσ hG) hH_nonneg
  calc
    unifExpectQ (fun er : NibbleVec4 × NibbleVec4 =>
        unifExpectQ (fun se : (NibbleVec4 × NibbleVec4) × NibblePoly =>
          (5 / 4 : Rat) ^
            (σ * w2NoiseOnSpace wVecFn v0Fn (w2ReorderEquiv.symm (er, se)) j)))
      ≤ unifExpectQ (fun er : NibbleVec4 × NibbleVec4 =>
          ((5 / 4 : Rat) ^ (σ * erTerm (cbdVec4OfNibbles er.1) (cbdVec4OfNibbles er.2) j)) *
            (G_ub ^ 1024 * H_ub)) := unifExpectQ_mono houter
    _ = unifExpectQ (fun er : NibbleVec4 × NibbleVec4 =>
          (5 / 4 : Rat) ^ (σ * erTerm (cbdVec4OfNibbles er.1) (cbdVec4OfNibbles er.2) j)) *
          (G_ub ^ 1024 * H_ub) := unifExpectQ_mul_const _ _
    _ ≤ A ^ 1024 * (G_ub ^ 1024 * H_ub) := by
        refine mul_le_mul_of_nonneg_right (expect_erTerm_le j hσ hA) ?_
        exact mul_nonneg (pow_nonneg hG_nonneg 1024) hH_nonneg
    _ = A ^ 1024 * G_ub ^ 1024 * H_ub := by ring

private theorem markov_indicator_le (z : Int) :
    (if 832 ≤ z then (1 : Rat) else 0) ≤ (5 / 4 : Rat) ^ (-832 : Int) * (5 / 4 : Rat) ^ z := by
  split_ifs with hz
  · rw [← zpow_add₀ (by norm_num : (5 / 4 : Rat) ≠ 0)]
    exact one_le_zpow₀ (by norm_num : (1 : Rat) ≤ 5 / 4) (by omega)
  · exact mul_nonneg (zpow_nonneg (by norm_num) _) (zpow_nonneg (by norm_num) _)

private theorem union_indicator_le (noise : Fin 256 → Int)
    [Decidable (∃ j : Fin 256, 832 ≤ |noise j|)] :
    (if (∃ j : Fin 256, 832 ≤ |noise j|) then (1 : Rat) else 0) ≤
      ∑ j : Fin 256,
        ((if 832 ≤ 1 * noise j then (1 : Rat) else 0) +
          (if 832 ≤ (-1) * noise j then (1 : Rat) else 0)) := by
  split_ifs with hex
  · rcases hex with ⟨j₀, hj₀⟩
    have hterm_nonneg : ∀ j : Fin 256,
        (0 : Rat) ≤
          (if 832 ≤ 1 * noise j then (1 : Rat) else 0) +
            (if 832 ≤ (-1) * noise j then (1 : Rat) else 0) := by
      intro j
      split_ifs <;> norm_num
    have hj₀_ge :
        (1 : Rat) ≤
          (if 832 ≤ 1 * noise j₀ then (1 : Rat) else 0) +
            (if 832 ≤ (-1) * noise j₀ then (1 : Rat) else 0) := by
      rcases le_total 0 (noise j₀) with hpos | hneg
      · rw [abs_of_nonneg hpos] at hj₀
        have h1 : 832 ≤ 1 * noise j₀ := by omega
        simp only [h1, ↓reduceIte]
        split_ifs <;> norm_num
      · rw [abs_of_nonpos hneg] at hj₀
        have h2 : 832 ≤ (-1) * noise j₀ := by omega
        simp only [h2, ↓reduceIte]
        split_ifs <;> norm_num
    exact le_trans hj₀_ge
      (Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_univ j₀))
  · refine Finset.sum_nonneg fun j _ => ?_
    split_ifs <;> norm_num

private def toW2Sample (p : WordsVec1 7 × WordsVec1 8) : W2SampleSpace :=
  (fun k => words4ToNibbles (wordsVec1Get p.1 ⟨k.val, by omega⟩),
   fun k => words4ToNibbles (wordsVec1Get p.1 ⟨4 + k.val, by omega⟩),
   fun k => words4ToNibbles (wordsVec1Get p.2 ⟨k.val, by omega⟩),
   fun k => words4ToNibbles (wordsVec1Get p.2 ⟨4 + k.val, by omega⟩),
   words4ToNibbles (wordsVec1Get p.2 ⟨8, by decide⟩))

private theorem toW2Sample_bijective : Function.Bijective toW2Sample := by
  classical
  let e : Words4 ≃ NibblePoly := Equiv.ofBijective words4ToNibbles words4ToNibbles_bijective
  refine ⟨?_, ?_⟩
  · rintro ⟨v1, v2⟩ ⟨w1, w2⟩ h
    simp only [toW2Sample, Prod.mk.injEq] at h
    rcases h with ⟨hs, he, hr, he1, he2⟩
    apply Prod.ext
    · rw [← wordsVec1OfFn_get 7 v1, ← wordsVec1OfFn_get 7 w1]
      refine congrArg (wordsVec1OfFn 7) (funext fun idx => ?_)
      by_cases hlt : idx.val < 4
      · exact e.injective (congrFun hs ⟨idx.val, hlt⟩)
      · have hge := congrFun he ⟨idx.val - 4, by omega⟩
        have hidx : (⟨4 + (idx.val - 4), by omega⟩ : Fin 8) = idx := by ext; dsimp only; omega
        simpa only [hidx] using e.injective hge
    · rw [← wordsVec1OfFn_get 8 v2, ← wordsVec1OfFn_get 8 w2]
      refine congrArg (wordsVec1OfFn 8) (funext fun idx => ?_)
      by_cases hlt4 : idx.val < 4
      · exact e.injective (congrFun hr ⟨idx.val, hlt4⟩)
      · by_cases hlt8 : idx.val < 8
        · have hge := congrFun he1 ⟨idx.val - 4, by omega⟩
          have hidx : (⟨4 + (idx.val - 4), by omega⟩ : Fin 9) = idx := by ext; dsimp only; omega
          simpa only [hidx] using e.injective hge
        · have hidx : idx = ⟨8, by decide⟩ := by ext; dsimp only; omega
          subst hidx
          exact e.injective he2
  · rintro ⟨u_s, u_e, u_r, u_e1, u_e2⟩
    let v1 : WordsVec1 7 := wordsVec1OfFn 7 fun i : Fin 8 =>
      if hlt : i.val < 4 then e.symm (u_s ⟨i.val, hlt⟩)
      else e.symm (u_e ⟨i.val - 4, by omega⟩)
    let v2 : WordsVec1 8 := wordsVec1OfFn 8 fun i : Fin 9 =>
      if hlt4 : i.val < 4 then e.symm (u_r ⟨i.val, hlt4⟩)
      else if hlt8 : i.val < 8 then e.symm (u_e1 ⟨i.val - 4, by omega⟩)
      else e.symm u_e2
    refine ⟨(v1, v2), ?_⟩
    have he_app : ∀ y : NibblePoly, words4ToNibbles (e.symm y) = y := e.apply_symm_apply
    simp only [toW2Sample, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · funext k
      simp [v1, wordsVec1Get_ofFn, k.isLt, he_app]
    · funext k
      have hnot : ¬ (4 + k.val < 4) := by omega
      have hsub : (⟨4 + k.val - 4, by omega⟩ : Fin 4) = k := by ext; dsimp only; omega
      simp [v1, wordsVec1Get_ofFn, hnot, he_app]
    · funext k
      simp [v2, wordsVec1Get_ofFn, k.isLt, he_app]
    · funext k
      have hnot4 : ¬ (4 + k.val < 4) := by omega
      have hlt8 : 4 + k.val < 8 := by omega
      have hsub : (⟨4 + k.val - 4, by omega⟩ : Fin 4) = k := by ext; dsimp only; omega
      simp [v2, wordsVec1Get_ofFn, hnot4, hlt8, he_app]
    · simp [v2, wordsVec1Get_ofFn, he_app]

private theorem unifExpectQ_indicator_le_ennreal {Ω : Type} [SampleableType Ω] [Fintype Ω]
    (P : Ω → Prop) [DecidablePred P] {B : Rat}
    (hB : unifExpectQ (fun ω : Ω => if P ω then (1 : Rat) else 0) ≤ B) :
    Pr{let ω ← $ᵗ Ω}[P ω] ≤ (B.toNNRat : ℝ≥0∞) := by
  rw [SampleableType.prEvent_uniformSample]
  set c : Nat := (Finset.univ.filter P).card
  set N : Nat := Fintype.card Ω
  have hN_pos : 0 < N := Fintype.card_pos
  have hsum : (∑ ω : Ω, if P ω then (1 : Rat) else 0) = (c : Rat) := by
    simp [c, Finset.sum_boole]
  have hB_q : (c : Rat) / (N : Rat) ≤ B := by
    rwa [unifExpectQ, hsum] at hB
  have hB_nonneg : 0 ≤ B :=
    le_trans (div_nonneg (Nat.cast_nonneg c) (Nat.cast_nonneg N)) hB_q
  have hnnrat : (c : NNRat) / (N : NNRat) ≤ B.toNNRat := by
    rw [Rat.le_toNNRat_iff_coe_le hB_nonneg]
    simpa [NNRat.cast_div, NNRat.cast_natCast] using hB_q
  have hnnreal : (((c : NNRat) / (N : NNRat) : NNRat) : NNReal) ≤ (B.toNNRat : NNReal) :=
    NNRat.cast_le.mpr hnnrat
  have hennreal :
      ENNReal.ofNNReal (((c : NNRat) / (N : NNRat) : NNRat) : NNReal) ≤
        ENNReal.ofNNReal (B.toNNRat : NNReal) :=
    ENNReal.coe_le_coe.mpr hnnreal
  have hrhs : ENNReal.ofNNReal (B.toNNRat : NNReal) = (B.toNNRat : ℝ≥0∞) :=
    ENNReal.coe_nnratCast B.toNNRat
  have hlhs :
      ENNReal.ofNNReal (((c : NNRat) / (N : NNRat) : NNRat) : NNReal) =
        (c : ℝ≥0∞) / (N : ℝ≥0∞) := by
    have hN_ne : (N : NNReal) ≠ 0 := by exact_mod_cast hN_pos.ne'
    rw [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast, ENNReal.coe_div hN_ne,
      ENNReal.coe_natCast, ENNReal.coe_natCast]
  rwa [hlhs, hrhs] at hennreal

/-- Full W2 conditioned-expectation and Chernoff union-bound theorem over `(8 + 9)` independent
128-byte `CBD_2` noise blocks (`cbdNoiseVec 8` and `cbdNoiseVec 9`), reducing the K-PKE decryption
noise tail event `∃ j : Fin 256, 832 ≤ |intNoise ... j|` to the rational W2 bound
`512 * (5/4)^{-832} * A^{1024} * G_ub^{1024} * H_ub`. -/
theorem w2_intNoise_tail_bound
    (wVecFn : (Fin 4 → Fin 256 → Int) → Fin 4 → ZPoly)
    (v0Fn : (Fin 4 → Fin 256 → Int) → (Fin 4 → Fin 256 → Int) → (Fin 4 → Fin 256 → Int) → ZPoly)
    {A G_ub H_ub : Rat}
    (hA : (cbd2Support.map fun x => cbd2WeightQ x * cbd2Mgf54 x).sum ≤ A)
    (hG : ∀ w : ZMod mlkemQ,
      (cbd2Support.map fun e =>
        cbd2WeightQ e * cbd2Mgf54 (e + compressErrZMod 11 (w + (e : ZMod mlkemQ)))).sum ≤ G_ub)
    (hH : ∀ v0 : ZMod mlkemQ, ∀ σ ∈ ([1, -1] : List Int),
      (cbd2Support.map fun e =>
        cbd2WeightQ e *
          (5 / 4 : Rat) ^ (σ * centeredZMod
            ((decompressCoeff 5 (compressCoeff 5 (v0 + (e : ZMod mlkemQ)).val) : ZMod mlkemQ) -
              v0))).sum ≤ H_ub) :
    𝒟[do
        let nKG ← cbdNoiseVec 8
        let nEnc ← cbdNoiseVec 9
        pure (decide (∃ j : Fin 256,
          832 ≤ |intNoise (wVecFn (encR nEnc)) (v0Fn (kgS nKG) (kgE nKG) (encR nEnc))
            (kgS nKG) (kgE nKG) (encR nEnc) (encE1 nEnc) (encE2 nEnc) j|))] {true} ≤
      ((512 * (5 / 4 : Rat) ^ (-832 : Int) * A ^ 1024 * G_ub ^ 1024 * H_ub).toNNRat : ℝ≥0∞) := by
  have hcomp :
      (do
        let nKG ← cbdNoiseVec 8
        let nEnc ← cbdNoiseVec 9
        pure (decide (∃ j : Fin 256,
          832 ≤ |intNoise (wVecFn (encR nEnc)) (v0Fn (kgS nKG) (kgE nKG) (encR nEnc))
            (kgS nKG) (kgE nKG) (encR nEnc) (encE1 nEnc) (encE2 nEnc) j|))) =
      (do
        let p ← $ᵗ (WordsVec1 7 × WordsVec1 8)
        pure (decide (∃ j : Fin 256, 832 ≤ |w2NoiseOnSpace wVecFn v0Fn (toW2Sample p) j|))) := by
    rw [cbdNoiseVec_succ_eq_map 7, cbdNoiseVec_succ_eq_map 8,
      SampleableType.uniformSample_prod_eq_bind]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    refine congrArg (Bind.bind ($ᵗ (WordsVec1 7))) (funext fun vKG => ?_)
    refine congrArg (Bind.bind ($ᵗ (WordsVec1 8))) (funext fun vEnc => ?_)
    have hnoise :
        intNoise (wVecFn (encR (vecWords1ToNoiseVec 8 vEnc)))
          (v0Fn (kgS (vecWords1ToNoiseVec 7 vKG)) (kgE (vecWords1ToNoiseVec 7 vKG))
            (encR (vecWords1ToNoiseVec 8 vEnc)))
          (kgS (vecWords1ToNoiseVec 7 vKG)) (kgE (vecWords1ToNoiseVec 7 vKG))
          (encR (vecWords1ToNoiseVec 8 vEnc)) (encE1 (vecWords1ToNoiseVec 8 vEnc))
          (encE2 (vecWords1ToNoiseVec 8 vEnc)) =
        w2NoiseOnSpace wVecFn v0Fn (toW2Sample (vKG, vEnc)) := by
      have hs : kgS (vecWords1ToNoiseVec 7 vKG) = cbdVec4OfNibbles (toW2Sample (vKG, vEnc)).1 := by
        funext k i
        exact cbd2IntPoly_words4ToBytes128 _ i
      have he : kgE (vecWords1ToNoiseVec 7 vKG) =
          cbdVec4OfNibbles (toW2Sample (vKG, vEnc)).2.1 := by
        funext k i
        exact cbd2IntPoly_words4ToBytes128 _ i
      have hr : encR (vecWords1ToNoiseVec 8 vEnc) =
          cbdVec4OfNibbles (toW2Sample (vKG, vEnc)).2.2.1 := by
        funext k i
        exact cbd2IntPoly_words4ToBytes128 _ i
      have he1 : encE1 (vecWords1ToNoiseVec 8 vEnc) =
          cbdVec4OfNibbles (toW2Sample (vKG, vEnc)).2.2.2.1 := by
        funext k i
        exact cbd2IntPoly_words4ToBytes128 _ i
      have he2 : encE2 (vecWords1ToNoiseVec 8 vEnc) =
          cbdPolyOfNibbles (toW2Sample (vKG, vEnc)).2.2.2.2 := by
        funext i
        exact cbd2IntPoly_words4ToBytes128 _ i
      rw [hs, he, hr, he1, he2]
      rfl
    simp_rw [hnoise]
  rw [hcomp, ← prEvent_eq_evalDist_decide,
    SampleableType.prEvent_uniformSample_comp_of_bijective toW2Sample_bijective
      (fun ω : W2SampleSpace => ∃ j : Fin 256, 832 ≤ |w2NoiseOnSpace wVecFn v0Fn ω j|)]
  refine unifExpectQ_indicator_le_ennreal _ ?_
  have hunion :
      unifExpectQ
        (fun ω : W2SampleSpace =>
          if (∃ j : Fin 256, 832 ≤ |w2NoiseOnSpace wVecFn v0Fn ω j|) then (1 : Rat) else 0) ≤
      ∑ j : Fin 256,
        (unifExpectQ (fun ω : W2SampleSpace =>
            if 832 ≤ 1 * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0) +
          unifExpectQ (fun ω : W2SampleSpace =>
            if 832 ≤ (-1) * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0)) := by
    calc
      unifExpectQ
          (fun ω : W2SampleSpace =>
            if (∃ j : Fin 256, 832 ≤ |w2NoiseOnSpace wVecFn v0Fn ω j|) then (1 : Rat) else 0)
        ≤ unifExpectQ
            (fun ω : W2SampleSpace =>
              ∑ j : Fin 256,
                ((if 832 ≤ 1 * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0) +
                  (if 832 ≤ (-1) * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0))) :=
          unifExpectQ_mono fun ω => union_indicator_le (w2NoiseOnSpace wVecFn v0Fn ω)
      _ = ∑ j : Fin 256,
            (unifExpectQ (fun ω : W2SampleSpace =>
                if 832 ≤ 1 * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0) +
              unifExpectQ (fun ω : W2SampleSpace =>
                if 832 ≤ (-1) * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0)) := by
          rw [unifExpectQ_sum]
          exact Finset.sum_congr rfl fun j _ => unifExpectQ_add _ _
  have hper_j : ∀ j : Fin 256,
      unifExpectQ (fun ω : W2SampleSpace =>
          if 832 ≤ 1 * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0) +
        unifExpectQ (fun ω : W2SampleSpace =>
          if 832 ≤ (-1) * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0) ≤
        2 * ((5 / 4 : Rat) ^ (-832 : Int) * (A ^ 1024 * G_ub ^ 1024 * H_ub)) := by
    intro j
    have hm1 :
        unifExpectQ (fun ω : W2SampleSpace =>
          if 832 ≤ 1 * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0) ≤
          (5 / 4 : Rat) ^ (-832 : Int) * (A ^ 1024 * G_ub ^ 1024 * H_ub) := by
      calc
        unifExpectQ (fun ω : W2SampleSpace =>
            if 832 ≤ 1 * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0)
          ≤ unifExpectQ (fun ω : W2SampleSpace =>
              (5 / 4 : Rat) ^ (-832 : Int) *
                (5 / 4 : Rat) ^ (1 * w2NoiseOnSpace wVecFn v0Fn ω j)) :=
            unifExpectQ_mono fun ω => markov_indicator_le _
        _ = (5 / 4 : Rat) ^ (-832 : Int) *
              unifExpectQ (fun ω : W2SampleSpace =>
                (5 / 4 : Rat) ^ (1 * w2NoiseOnSpace wVecFn v0Fn ω j)) :=
            unifExpectQ_const_mul _ _
        _ ≤ (5 / 4 : Rat) ^ (-832 : Int) * (A ^ 1024 * G_ub ^ 1024 * H_ub) :=
            mul_le_mul_of_nonneg_left
              (w2_mgf_bound_per_coeff wVecFn v0Fn j (by simp) hA hG hH)
              (zpow_nonneg (by norm_num) _)
    have hm2 :
        unifExpectQ (fun ω : W2SampleSpace =>
          if 832 ≤ (-1) * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0) ≤
          (5 / 4 : Rat) ^ (-832 : Int) * (A ^ 1024 * G_ub ^ 1024 * H_ub) := by
      calc
        unifExpectQ (fun ω : W2SampleSpace =>
            if 832 ≤ (-1) * w2NoiseOnSpace wVecFn v0Fn ω j then (1 : Rat) else 0)
          ≤ unifExpectQ (fun ω : W2SampleSpace =>
              (5 / 4 : Rat) ^ (-832 : Int) *
                (5 / 4 : Rat) ^ ((-1) * w2NoiseOnSpace wVecFn v0Fn ω j)) :=
            unifExpectQ_mono fun ω => markov_indicator_le _
        _ = (5 / 4 : Rat) ^ (-832 : Int) *
              unifExpectQ (fun ω : W2SampleSpace =>
                (5 / 4 : Rat) ^ ((-1) * w2NoiseOnSpace wVecFn v0Fn ω j)) :=
            unifExpectQ_const_mul _ _
        _ ≤ (5 / 4 : Rat) ^ (-832 : Int) * (A ^ 1024 * G_ub ^ 1024 * H_ub) :=
            mul_le_mul_of_nonneg_left
              (w2_mgf_bound_per_coeff wVecFn v0Fn j (by simp) hA hG hH)
              (zpow_nonneg (by norm_num) _)
    linarith
  calc
    unifExpectQ
        (fun ω : W2SampleSpace =>
          if (∃ j : Fin 256, 832 ≤ |w2NoiseOnSpace wVecFn v0Fn ω j|) then (1 : Rat) else 0)
      ≤ ∑ _j : Fin 256,
          (2 * ((5 / 4 : Rat) ^ (-832 : Int) * (A ^ 1024 * G_ub ^ 1024 * H_ub))) :=
        le_trans hunion (Finset.sum_le_sum fun j _ => hper_j j)
    _ = 512 * (5 / 4 : Rat) ^ (-832 : Int) * A ^ 1024 * G_ub ^ 1024 * H_ub := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
        generalize (5 / 4 : Rat) ^ (-832 : Int) = p832
        generalize A ^ 1024 = pA
        generalize G_ub ^ 1024 = pG
        ring

/-- Direct `1 / 2 ^ 112` corollary of `w2_intNoise_tail_bound` ready to consume
`RationalCertificate.w2_certificate_lt_two_pow_neg_112`. -/
theorem w2_intNoise_tail_bound_le_two_pow_neg_112
    (wVecFn : (Fin 4 → Fin 256 → Int) → Fin 4 → ZPoly)
    (v0Fn : (Fin 4 → Fin 256 → Int) → (Fin 4 → Fin 256 → Int) → (Fin 4 → Fin 256 → Int) → ZPoly)
    {A G_ub H_ub : Rat}
    (hA : (cbd2Support.map fun x => cbd2WeightQ x * cbd2Mgf54 x).sum ≤ A)
    (hG : ∀ w : ZMod mlkemQ,
      (cbd2Support.map fun e =>
        cbd2WeightQ e * cbd2Mgf54 (e + compressErrZMod 11 (w + (e : ZMod mlkemQ)))).sum ≤ G_ub)
    (hH : ∀ v0 : ZMod mlkemQ,
      (cbd2Support.map fun e =>
        cbd2WeightQ e *
          (5 / 4 : Rat) ^ ((1 : Int) * centeredZMod
            ((decompressCoeff 5 (compressCoeff 5 (v0 + (e : ZMod mlkemQ)).val) : ZMod mlkemQ) -
              v0))).sum ≤ H_ub ∧
      (cbd2Support.map fun e =>
        cbd2WeightQ e *
          (5 / 4 : Rat) ^ ((-1 : Int) * centeredZMod
            ((decompressCoeff 5 (compressCoeff 5 (v0 + (e : ZMod mlkemQ)).val) : ZMod mlkemQ) -
              v0))).sum ≤ H_ub)
    (hCert :
      512 * (5 / 4 : Rat) ^ (-832 : Int) * A ^ 1024 * G_ub ^ 1024 * H_ub ≤
        1 / (2 : Rat) ^ 112) :
    𝒟[do
        let nKG ← cbdNoiseVec 8
        let nEnc ← cbdNoiseVec 9
        pure (decide (∃ j : Fin 256,
          832 ≤ |intNoise (wVecFn (encR nEnc)) (v0Fn (kgS nKG) (kgE nKG) (encR nEnc))
            (kgS nKG) (kgE nKG) (encR nEnc) (encE1 nEnc) (encE2 nEnc) j|))] {true} ≤
      1 / (2 : ℝ≥0∞) ^ 112 := by
  have hH_list : ∀ v0 : ZMod mlkemQ, ∀ σ ∈ ([1, -1] : List Int),
      (cbd2Support.map fun e =>
        cbd2WeightQ e *
          (5 / 4 : Rat) ^ (σ * centeredZMod
            ((decompressCoeff 5 (compressCoeff 5 (v0 + (e : ZMod mlkemQ)).val) : ZMod mlkemQ) -
              v0))).sum ≤ H_ub := by
    intro v0 σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl
    · exact (hH v0).1
    · exact (hH v0).2
  refine le_trans (w2_intNoise_tail_bound wVecFn v0Fn hA hG hH_list) ?_
  set B : Rat := 512 * (5 / 4 : Rat) ^ (-832 : Int) * A ^ 1024 * G_ub ^ 1024 * H_ub
  have hnn : B.toNNRat ≤ (1 : NNRat) / (2 : NNRat) ^ 112 := by
    by_cases hpos : 0 ≤ B
    · rw [← @NNRat.cast_le Rat _ _ _, Rat.coe_toNNRat B hpos]
      simpa [NNRat.cast_div, NNRat.cast_pow] using hCert
    · rw [Rat.toNNRat_of_nonpos (le_of_not_ge hpos)]
      positivity
  have hnnreal : (B.toNNRat : NNReal) ≤ (((1 : NNRat) / (2 : NNRat) ^ 112 : NNRat) : NNReal) :=
    NNRat.cast_le.mpr hnn
  have henn :
      ENNReal.ofNNReal (B.toNNRat : NNReal) ≤
        ENNReal.ofNNReal (((1 : NNRat) / (2 : NNRat) ^ 112 : NNRat) : NNReal) :=
    ENNReal.coe_le_coe.mpr hnnreal
  have hlhs : ENNReal.ofNNReal (B.toNNRat : NNReal) = (B.toNNRat : ℝ≥0∞) :=
    ENNReal.coe_nnratCast B.toNNRat
  have hrhs :
      ENNReal.ofNNReal (((1 : NNRat) / (2 : NNRat) ^ 112 : NNRat) : NNReal) =
        1 / (2 : ℝ≥0∞) ^ 112 := by
    have h2ne : ((2 : NNReal) ^ 112) ≠ 0 := pow_ne_zero 112 (by norm_num)
    rw [NNRat.cast_div, NNRat.cast_one, NNRat.cast_pow, NNRat.cast_ofNat, ENNReal.coe_div h2ne,
      ENNReal.coe_one, ENNReal.coe_pow, ENNReal.coe_ofNat]
  rwa [hlhs, hrhs] at henn

end Computational.Proofs.Kyber1024Delta.CbdProbability

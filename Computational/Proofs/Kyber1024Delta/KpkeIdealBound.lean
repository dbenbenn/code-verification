/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Kyber1024Delta.Common -- proof-setup: allow-public-import
public import Computational.Proofs.Kyber1024Delta.CbdProbability -- proof-setup: allow-public-import
import Computational.Proofs.Kyber1024Delta.NttAlgebra
import Computational.Proofs.Kyber1024Delta.CodecAndCompress
import Computational.Proofs.Kyber1024Delta.RationalCertificate
import VCVio.EvalDist.Monad.Measure
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Ideal Kyber-1024 K-PKE Decryption Error Identity & `2^-112` Tail Bound (`KpkeIdealBound`)

Defines the noise-explicit ideal K-PKE failure predicate `kpkeBodyFails`, proves the commutative
ring laws of `negacyclicMul` on `ZPoly`, establishes the exact algebraic cancellation of `A` in
K-PKE decryption and the `831` threshold contrapositive, and derives the `≤ 1 / 2^112` failure
probability bounds under `cbdNoiseVec` and full `(seed, r)` sampling.
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.Kyber1024Delta.KpkeIdealBound

open scoped ENNReal
open OracleComp OracleSpec
open MeasureTheory (Measure lintegral_const lintegral_mono)
open CryptoGames.SHA3 (
  keccakSponge
  sha3_256List
  sha3_512List
)
open CryptoGames.MLKEM (
  Poly
  byteDecodeMod
  byteDecodeRaw
  byteEncode
  compressAndEncode
  compressCoeff
  decodeAndDecompress
  decompressCoeff
  fipsZetas
  indCpaDecrypt
  mlkemQ
  polyAdd
  polyInvNtt
  polyNtt
  polyNttMul
  polySub
  sampleMatrixWith
  sampleNtt
  samplePolyCbd2
  vecDotNtt
  zeroPoly
)
open Computational.Proofs.Kyber1024Delta.Common (
  IsCanonicalPoly
  ZPoly
  centeredZMod
  centeredZMod_cast_eq
  centeredZMod_of_int_bounds
  compressErrZMod
  getD_ofFn_nat
  negacyclicMul
  ofZPoly
  ofZPoly_isCanonical
  toZPoly
  toZPoly_ofZPoly
)
open Computational.Proofs.Kyber1024Delta.NttAlgebra (
  polyAdd_isCanonical
  polyInvNtt_isCanonical
  polyNtt_isCanonical
  polyNttMul_isCanonical
  toZPoly_polyAdd
  toZPoly_polyInvNtt_congr
  toZPoly_polyInvNtt_polyAdd
  toZPoly_polyInvNtt_polyNtt
  toZPoly_polyInvNtt_polyNttMul
  toZPoly_polyInvNtt_vecDotNtt
  toZPoly_polyNtt_congr
  toZPoly_polyNtt_polyInvNtt
  toZPoly_polyNttMul_congr
  toZPoly_polySub
  vecDotNtt_isCanonical
)
open Computational.Proofs.Kyber1024Delta.CodecAndCompress (
  byteDecodeMod_12_byteEncode_12
  byteEncode_length
  compressAndEncode_1_eq_of_noise_le_831
  compressAndEncode_length
  sampleMatrixWith_transpose
  sampleNtt_isCanonical
  toZPoly_decodeAndDecompress_compressAndEncode
)
open Computational.Proofs.Kyber1024Delta.CbdProbability (
  cbd2IntPoly_cast_eq
  cbdNoiseVec
  encE1
  encE2
  encR
  intNoise
  intNoise_cast_eq
  kgE
  kgS
  samplePolyCbd2_isCanonical
  w2_intNoise_tail_bound_le_two_pow_neg_112
)
open Computational.Proofs.Kyber1024Delta.RationalCertificate (
  termA_eq
  termGAt_le_constG
  termHAt_le_constH
  w2_certificate_lt_two_pow_neg_112
)

attribute [local irreducible] fipsZetas

/-! ## 1. Noise-Explicit Ideal K-PKE Failure Predicate -/

/-- Noise-explicit Round-3 Kyber-1024 K-PKE failure predicate parameterized by matrix XOF `sampler`.
Matches `CryptoGames.MLKEM.kyber1024KpkeFailsWith` by `rfl`. -/
@[expose] def kpkeBodyFails (sampler : List (BitVec 8) → Poly)
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

/-! ## 2. Commutative Ring Laws of `negacyclicMul` on `ZPoly` -/

theorem negacyclicMul_comm (a b : ZPoly) : negacyclicMul a b = negacyclicMul b a :=
  NttAlgebra.negacyclicMul_comm a b

theorem negacyclicMul_add (a b c : ZPoly) :
    negacyclicMul a (b + c) = negacyclicMul a b + negacyclicMul a c :=
  NttAlgebra.negacyclicMul_add_right a b c

theorem add_negacyclicMul (a b c : ZPoly) :
    negacyclicMul (a + b) c = negacyclicMul a c + negacyclicMul b c :=
  NttAlgebra.negacyclicMul_add_left a b c

private theorem natCast_mod_mlkemQ (n : Nat) :
    ((n % mlkemQ : Nat) : ZMod mlkemQ) = (n : ZMod mlkemQ) :=
  ZMod.natCast_mod n mlkemQ

private theorem toZPoly_polyNttMul_pair (f g : Poly) (p : Nat) (hp : p < 128) :
    let baseZeta := fipsZetas.getD (64 + p / 2) 0
    let γ : ZMod mlkemQ :=
      ((if p % 2 == 0 then baseZeta else (mlkemQ - baseZeta) % mlkemQ : Nat) : ZMod mlkemQ)
    let a0 := toZPoly f ⟨2 * p, by omega⟩
    let a1 := toZPoly f ⟨2 * p + 1, by omega⟩
    let b0 := toZPoly g ⟨2 * p, by omega⟩
    let b1 := toZPoly g ⟨2 * p + 1, by omega⟩
    toZPoly (polyNttMul f g) ⟨2 * p, by omega⟩ = a0 * b0 + a1 * b1 * γ ∧
      toZPoly (polyNttMul f g) ⟨2 * p + 1, by omega⟩ = a0 * b1 + a1 * b0 := by
  dsimp only
  have h2p_lt : 2 * p < 256 := by omega
  have h2p1_lt : 2 * p + 1 < 256 := by omega
  have hdiv0 : (2 * p) / 2 = p := by omega
  have hdiv1 : (2 * p + 1) / 2 = p := by omega
  have hmod0 : ((2 * p) % 2 == 0) = true := by
    have : (2 * p) % 2 = 0 := by omega
    simp [this]
  have hmod1 : ((2 * p + 1) % 2 == 0) = false := by
    have : (2 * p + 1) % 2 = 1 := by omega
    simp [this]
  constructor
  · simp only [toZPoly, polyNttMul, getD_ofFn_nat _ _ _ h2p_lt, hdiv0, hmod0, ↓reduceIte,
      natCast_mod_mlkemQ]
    push_cast
    rw [natCast_mod_mlkemQ]
    push_cast
    rfl
  · simp only [toZPoly, polyNttMul, getD_ofFn_nat _ _ _ h2p1_lt, hdiv1, hmod1,
      Bool.false_eq_true, ↓reduceIte, natCast_mod_mlkemQ]
    push_cast
    rfl

private theorem toZPoly_polyNttMul_assoc (f g h : Poly) :
    toZPoly (polyNttMul (polyNttMul f g) h) = toZPoly (polyNttMul f (polyNttMul g h)) := by
  funext idx
  set p := idx.val / 2
  have hp : p < 128 := by omega
  obtain ⟨hfg0, hfg1⟩ := toZPoly_polyNttMul_pair f g p hp
  obtain ⟨hgh0, hgh1⟩ := toZPoly_polyNttMul_pair g h p hp
  obtain ⟨hl0, hl1⟩ := toZPoly_polyNttMul_pair (polyNttMul f g) h p hp
  obtain ⟨hr0, hr1⟩ := toZPoly_polyNttMul_pair f (polyNttMul g h) p hp
  by_cases heven : idx.val % 2 = 0
  · have hidx : idx = ⟨2 * p, by omega⟩ := by ext; dsimp [p]; omega
    rw [hidx, hl0, hr0, hfg0, hfg1, hgh0, hgh1]
    ring
  · have hidx : idx = ⟨2 * p + 1, by omega⟩ := by ext; dsimp [p]; omega
    rw [hidx, hl1, hr1, hfg0, hfg1, hgh0, hgh1]
    ring

private theorem toZPoly_polyNtt_ofZPoly_negacyclicMul (a b : ZPoly) :
    toZPoly (polyNtt (ofZPoly (negacyclicMul a b))) =
      toZPoly (polyNttMul (polyNtt (ofZPoly a)) (polyNtt (ofZPoly b))) := by
  have ha : (ofZPoly a).size = 256 := (ofZPoly_isCanonical a).1
  have hb : (ofZPoly b).size = 256 := (ofZPoly_isCanonical b).1
  have hmul_eq : negacyclicMul a b =
      toZPoly (polyInvNtt (polyNttMul (polyNtt (ofZPoly a)) (polyNtt (ofZPoly b)))) := by
    simpa only [toZPoly_ofZPoly] using (toZPoly_polyInvNtt_polyNttMul ha hb).symm
  rw [hmul_eq]
  have hinv_can :
      IsCanonicalPoly (polyInvNtt (polyNttMul (polyNtt (ofZPoly a)) (polyNtt (ofZPoly b)))) :=
    polyInvNtt_isCanonical (polyNttMul_isCanonical _ _).1
  rw [toZPoly_polyNtt_congr (ofZPoly_isCanonical _).1 hinv_can.1 (toZPoly_ofZPoly _)]
  exact toZPoly_polyNtt_polyInvNtt (polyNttMul_isCanonical _ _)

theorem negacyclicMul_assoc (a b c : ZPoly) :
    negacyclicMul (negacyclicMul a b) c = negacyclicMul a (negacyclicMul b c) := by
  have ha : (ofZPoly a).size = 256 := (ofZPoly_isCanonical a).1
  have hb : (ofZPoly b).size = 256 := (ofZPoly_isCanonical b).1
  have hc : (ofZPoly c).size = 256 := (ofZPoly_isCanonical c).1
  have hab : (ofZPoly (negacyclicMul a b)).size = 256 := (ofZPoly_isCanonical _).1
  have hbc : (ofZPoly (negacyclicMul b c)).size = 256 := (ofZPoly_isCanonical _).1
  have hlhs : negacyclicMul (negacyclicMul a b) c =
      toZPoly (polyInvNtt
        (polyNttMul (polyNtt (ofZPoly (negacyclicMul a b))) (polyNtt (ofZPoly c)))) := by
    simpa only [toZPoly_ofZPoly] using (toZPoly_polyInvNtt_polyNttMul hab hc).symm
  have hrhs : negacyclicMul a (negacyclicMul b c) =
      toZPoly (polyInvNtt
        (polyNttMul (polyNtt (ofZPoly a)) (polyNtt (ofZPoly (negacyclicMul b c))))) := by
    simpa only [toZPoly_ofZPoly] using (toZPoly_polyInvNtt_polyNttMul ha hbc).symm
  rw [hlhs, hrhs]
  apply toZPoly_polyInvNtt_congr (polyNttMul_isCanonical _ _) (polyNttMul_isCanonical _ _)
  calc
    toZPoly (polyNttMul (polyNtt (ofZPoly (negacyclicMul a b))) (polyNtt (ofZPoly c)))
      = toZPoly (polyNttMul
          (polyNttMul (polyNtt (ofZPoly a)) (polyNtt (ofZPoly b))) (polyNtt (ofZPoly c))) :=
        toZPoly_polyNttMul_congr (toZPoly_polyNtt_ofZPoly_negacyclicMul a b) rfl
    _ = toZPoly (polyNttMul
          (polyNtt (ofZPoly a)) (polyNttMul (polyNtt (ofZPoly b)) (polyNtt (ofZPoly c)))) :=
        toZPoly_polyNttMul_assoc _ _ _
    _ = toZPoly (polyNttMul (polyNtt (ofZPoly a)) (polyNtt (ofZPoly (negacyclicMul b c)))) :=
        toZPoly_polyNttMul_congr rfl (toZPoly_polyNtt_ofZPoly_negacyclicMul b c).symm

private theorem negacyclicMul_sum {ι : Type} (s : Finset ι) (a : ZPoly) (f : ι → ZPoly) :
    negacyclicMul a (∑ i ∈ s, f i) = ∑ i ∈ s, negacyclicMul a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext j
    simp [negacyclicMul]
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx, negacyclicMul_add, ih, Finset.sum_insert hx]

private theorem sum_negacyclicMul {ι : Type} (s : Finset ι) (f : ι → ZPoly) (b : ZPoly) :
    negacyclicMul (∑ i ∈ s, f i) b = ∑ i ∈ s, negacyclicMul (f i) b := by
  rw [negacyclicMul_comm, negacyclicMul_sum]
  exact Finset.sum_congr rfl fun i _ => negacyclicMul_comm b (f i)

/-! ## 3. Exact K-PKE Decryption Error Identity & `831` Threshold Implication -/

/-- Conditioning-compatible `u`-pre-noise polynomial vector `Aᵀ r` depending only on
`(sampler, seed64, r)` (independent of `s, e, e1, e2`). -/
def wVecFn (sampler : List (BitVec 8) → Poly) (seed64 : List (BitVec 8))
    (r : Fin 4 → Fin 256 → Int) (k : Fin 4) : ZPoly :=
  let rho := (sha3_512List (seed64.take 32)).take 32
  let aMat := sampleMatrixWith sampler 4 rho true
  ∑ i : Fin 4,
    negacyclicMul
      (toZPoly (polyInvNtt ((aMat.getD i.val #[]).getD k.val zeroPoly)))
      (fun j => (r i j : ZMod mlkemQ))

/-- Conditioning-compatible `v`-pre-noise polynomial `tᵀ r + Decompress_1(m)` depending only on
`(sampler, seed64, rand32, s, e, r)` (independent of `e1, e2`). -/
def v0Fn (sampler : List (BitVec 8) → Poly) (seed64 rand32 : List (BitVec 8))
    (s e r : Fin 4 → Fin 256 → Int) : ZPoly :=
  let rho := (sha3_512List (seed64.take 32)).take 32
  let aMat := sampleMatrixWith sampler 4 rho true
  let m := sha3_256List (rand32.take 32)
  let mPoly := decodeAndDecompress 1 (m.take 32)
  (∑ i : Fin 4,
    negacyclicMul
      ((∑ k : Fin 4,
          negacyclicMul
            (toZPoly (polyInvNtt ((aMat.getD i.val #[]).getD k.val zeroPoly)))
            (fun j => (s k j : ZMod mlkemQ))) +
        (fun j => (e i j : ZMod mlkemQ)))
      (fun j => (r i j : ZMod mlkemQ))) +
    toZPoly mPoly

private theorem sha3_256List_length (msg : List (BitVec 8)) :
    (sha3_256List msg).length = 32 := by
  simp [sha3_256List, keccakSponge]

private theorem sha3_512List_length (msg : List (BitVec 8)) :
    (sha3_512List msg).length = 64 := by
  simp [sha3_512List, keccakSponge]

private theorem flatten_range4_eq {α : Type} (g : Nat → List α) :
    ((List.range 4).map g).flatten = g 0 ++ (g 1 ++ (g 2 ++ (g 3 ++ []))) := by
  have hr4 : List.range 4 = [0, 1, 2, 3] := by decide
  rw [hr4]
  rfl

private theorem flatten_range4_append_eq {α : Type} (g : Nat → List α) (tail : List α) :
    ((List.range 4).map g).flatten ++ tail = g 0 ++ (g 1 ++ (g 2 ++ (g 3 ++ tail))) := by
  rw [flatten_range4_eq]
  simp [List.append_assoc]

private theorem flatten_range4_append_slice {α : Type} {L : Nat} (g : Nat → List α)
    (tail : List α) (hg : ∀ i < 4, (g i).length = L) {i : Nat} (hi : i < 4) :
    ((((List.range 4).map g).flatten ++ tail).drop (L * i)).take L = g i := by
  rw [flatten_range4_append_eq]
  have h0 : (g 0).length = L := hg 0 (by omega)
  have h1 : (g 1).length = L := hg 1 (by omega)
  have h2 : (g 2).length = L := hg 2 (by omega)
  have h3 : (g 3).length = L := hg 3 (by omega)
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  · simp [List.take_left' h0]
  · rw [Nat.mul_one, List.drop_left' h0, List.take_left' h1]
  · have h2L : L * 2 = L + L := by omega
    rw [h2L, ← List.drop_drop, List.drop_left' h0, List.drop_left' h1, List.take_left' h2]
  · have h3L : L * 3 = (L + L) + L := by omega
    rw [h3L, ← List.drop_drop, ← List.drop_drop, List.drop_left' h0, List.drop_left' h1,
      List.drop_left' h2, List.take_left' h3]

private theorem flatten_range4_slice {α : Type} {L : Nat} (g : Nat → List α)
    (hg : ∀ i < 4, (g i).length = L) {i : Nat} (hi : i < 4) :
    ((((List.range 4).map g).flatten).drop (L * i)).take L = g i := by
  simpa using flatten_range4_append_slice g [] hg hi

private theorem flatten_range4_append_drop {α : Type} {L : Nat} (g : Nat → List α)
    (tail : List α) (hg : ∀ i < 4, (g i).length = L) :
    (((List.range 4).map g).flatten ++ tail).drop (4 * L) = tail := by
  rw [flatten_range4_append_eq]
  have h0 : (g 0).length = L := hg 0 (by omega)
  have h1 : (g 1).length = L := hg 1 (by omega)
  have h2 : (g 2).length = L := hg 2 (by omega)
  have h3 : (g 3).length = L := hg 3 (by omega)
  have h4L : 4 * L = ((L + L) + L) + L := by omega
  rw [h4L, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop,
    List.drop_left' h0, List.drop_left' h1, List.drop_left' h2, List.drop_left' h3]

private theorem toZPoly_polyInvNtt_polyNttMul_left {a b : Poly}
    (ha : IsCanonicalPoly a) (hb : b.size = 256) :
    toZPoly (polyInvNtt (polyNttMul a (polyNtt b))) =
      negacyclicMul (toZPoly (polyInvNtt a)) (toZPoly b) := by
  have ha_inv : IsCanonicalPoly (polyInvNtt a) := polyInvNtt_isCanonical ha.1
  have hmul_eq :
      toZPoly (polyNttMul a (polyNtt b)) =
        toZPoly (polyNttMul (polyNtt (polyInvNtt a)) (polyNtt b)) :=
    toZPoly_polyNttMul_congr (toZPoly_polyNtt_polyInvNtt ha).symm rfl
  rw [toZPoly_polyInvNtt_congr (polyNttMul_isCanonical _ _) (polyNttMul_isCanonical _ _) hmul_eq]
  exact toZPoly_polyInvNtt_polyNttMul ha_inv.1 hb

private theorem sampleMatrixWith_entry_isCanonical {sampler : List (BitVec 8) → Poly}
    (hSampler : ∀ s, IsCanonicalPoly (sampler s)) (rho : List (BitVec 8)) (transpose : Bool)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    IsCanonicalPoly (((sampleMatrixWith sampler 4 rho transpose).getD i #[]).getD j zeroPoly) := by
  unfold sampleMatrixWith
  rw [getD_ofFn_nat _ i #[] hi, getD_ofFn_nat _ j zeroPoly hj]
  exact hSampler _

private theorem toZPoly_samplePolyCbd2_eq (bs : List (BitVec 8)) :
    toZPoly (samplePolyCbd2 bs) = fun j => (CbdProbability.cbd2IntPoly bs j : ZMod mlkemQ) := by
  funext j
  exact (cbd2IntPoly_cast_eq bs j).symm

private theorem decodeAndDecompress_size (d : Nat) (bs : List (BitVec 8)) :
    (decodeAndDecompress d bs).size = 256 := by
  simp [decodeAndDecompress, byteDecodeRaw]

private theorem toZPoly_decodeAndDecompress_5_compressAndEncode_5 (f : Poly) (j : Fin 256) :
    toZPoly (decodeAndDecompress 5 (compressAndEncode 5 f)) j =
      (decompressCoeff 5 (compressCoeff 5 (toZPoly f j).val) : ZMod mlkemQ) := by
  rw [toZPoly_decodeAndDecompress_compressAndEncode (by decide : 0 < 5) (by decide : 5 ≤ 12) f j]
  unfold compressErrZMod
  rw [centeredZMod_cast_eq, add_sub_cancel]

private theorem cancel_matrix_quadratic_form (A : Fin 4 → Fin 4 → ZPoly)
    (s e r : Fin 4 → ZPoly) :
    (∑ i : Fin 4, negacyclicMul ((∑ k : Fin 4, negacyclicMul (A i k) (s k)) + e i) (r i)) -
      (∑ k : Fin 4, negacyclicMul (s k) (∑ i : Fin 4, negacyclicMul (A i k) (r i))) =
      ∑ i : Fin 4, negacyclicMul (e i) (r i) := by
  have hlhs :
      (∑ i : Fin 4, negacyclicMul ((∑ k : Fin 4, negacyclicMul (A i k) (s k)) + e i) (r i)) =
        (∑ i : Fin 4, ∑ k : Fin 4, negacyclicMul (negacyclicMul (A i k) (s k)) (r i)) +
          (∑ i : Fin 4, negacyclicMul (e i) (r i)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_negacyclicMul, sum_negacyclicMul]
  have hrhs :
      (∑ k : Fin 4, negacyclicMul (s k) (∑ i : Fin 4, negacyclicMul (A i k) (r i))) =
        ∑ i : Fin 4, ∑ k : Fin 4, negacyclicMul (negacyclicMul (A i k) (s k)) (r i) := by
    calc
      (∑ k : Fin 4, negacyclicMul (s k) (∑ i : Fin 4, negacyclicMul (A i k) (r i)))
        = ∑ k : Fin 4, ∑ i : Fin 4, negacyclicMul (s k) (negacyclicMul (A i k) (r i)) :=
          Finset.sum_congr rfl fun k _ => negacyclicMul_sum _ _ _
      _ = ∑ i : Fin 4, ∑ k : Fin 4, negacyclicMul (s k) (negacyclicMul (A i k) (r i)) :=
          Finset.sum_comm
      _ = ∑ i : Fin 4, ∑ k : Fin 4, negacyclicMul (negacyclicMul (A i k) (s k)) (r i) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          rw [negacyclicMul_comm (A i k) (s k), negacyclicMul_assoc]
  rw [hlhs, hrhs, add_comm, add_sub_cancel_right]

theorem kpkeBodyFails_imp_exists_noise_ge_832
    {sampler : List (BitVec 8) → Poly}
    (hSampler : ∀ s, IsCanonicalPoly (sampler s))
    (seed64 rand32 : List (BitVec 8))
    (nKG : Fin 8 → List (BitVec 8)) (nEnc : Fin 9 → List (BitVec 8))
    (hFail : kpkeBodyFails sampler seed64 rand32 nKG nEnc = true) :
    ∃ j : Fin 256,
      832 ≤
        |intNoise (wVecFn sampler seed64 (encR nEnc))
          (v0Fn sampler seed64 rand32 (kgS nKG) (kgE nKG) (encR nEnc))
          (kgS nKG) (kgE nKG) (encR nEnc) (encE1 nEnc) (encE2 nEnc) j| := by
  unfold kpkeBodyFails at hFail
  extract_lets d rho aMat sHat eHat tHat skPke pk m tHatEnc rhoEnc aTrans rHat e1 e2 uVec mPoly
    vPoly c1 c2 at hFail
  set ct := c1 ++ c2
  change (indCpaDecrypt 4 11 5 skPke ct != m) = true at hFail
  unfold indCpaDecrypt at hFail
  extract_lets c1Block c1Len sHatDec uHat vDec wPoly at hFail
  let A : Fin 4 → Fin 4 → ZPoly := fun i k =>
    toZPoly (polyInvNtt ((aMat.getD i.val #[]).getD k.val zeroPoly))
  let sZ : Fin 4 → ZPoly := fun k j => (kgS nKG k j : ZMod mlkemQ)
  let eZ : Fin 4 → ZPoly := fun i j => (kgE nKG i j : ZMod mlkemQ)
  let rZ : Fin 4 → ZPoly := fun i j => (encR nEnc i j : ZMod mlkemQ)
  let e1Z : Fin 4 → ZPoly := fun k j => (encE1 nEnc k j : ZMod mlkemQ)
  let e2Z : ZPoly := fun j => (encE2 nEnc j : ZMod mlkemQ)
  let wVec : Fin 4 → ZPoly := fun k => ∑ i : Fin 4, negacyclicMul (A i k) (rZ i)
  let v0 : ZPoly :=
    (∑ i : Fin 4, negacyclicMul ((∑ k : Fin 4, negacyclicMul (A i k) (sZ k)) + eZ i) (rZ i)) +
      toZPoly mPoly
  have hwVec_def : wVecFn sampler seed64 (encR nEnc) = wVec := rfl
  have hv0_def : v0Fn sampler seed64 rand32 (kgS nKG) (kgE nKG) (encR nEnc) = v0 := rfl
  rw [hwVec_def, hv0_def]
  have hrho_len : rho.length = 32 := by
    dsimp only [rho]
    rw [List.length_take, sha3_512List_length]
    omega
  have hm_len : m.length = 32 := sha3_256List_length _
  clear_value rho m
  -- Slice roundtrips for `skPke`, `pk`, and `ct = c1 ++ c2`
  have hsHat_can : ∀ i : Fin 4, IsCanonicalPoly (sHat.getD i.val zeroPoly) := by
    intro i
    dsimp only [sHat]
    rw [getD_ofFn_nat _ i.val zeroPoly i.isLt]
    exact polyNtt_isCanonical (samplePolyCbd2_isCanonical _).1
  have htHat_can : ∀ i : Fin 4, IsCanonicalPoly (tHat.getD i.val zeroPoly) := by
    intro i
    dsimp only [tHat]
    rw [getD_ofFn_nat _ i.val zeroPoly i.isLt]
    exact polyAdd_isCanonical _ _
  have hsHatDec_getD : ∀ k : Fin 4, sHatDec.getD k.val zeroPoly = sHat.getD k.val zeroPoly := by
    intro k
    dsimp only [sHatDec]
    rw [getD_ofFn_nat _ k.val zeroPoly k.isLt]
    have hslice :
        ((skPke.drop (384 * k.val)).take 384) = byteEncode 12 (sHat.getD k.val zeroPoly) :=
      flatten_range4_slice (L := 384) (fun i => byteEncode 12 (sHat.getD i zeroPoly))
        (fun i _ => byteEncode_length 12 _) k.isLt
    rw [hslice]
    exact byteDecodeMod_12_byteEncode_12 (hsHat_can k)
  have htHatEnc_getD : ∀ i : Fin 4, tHatEnc.getD i.val zeroPoly = tHat.getD i.val zeroPoly := by
    intro i
    dsimp only [tHatEnc]
    rw [getD_ofFn_nat _ i.val zeroPoly i.isLt]
    have hslice :
        ((pk.drop (384 * i.val)).take 384) = byteEncode 12 (tHat.getD i.val zeroPoly) :=
      flatten_range4_append_slice (L := 384) (fun j => byteEncode 12 (tHat.getD j zeroPoly)) rho
        (fun j _ => byteEncode_length 12 _) i.isLt
    rw [hslice]
    exact byteDecodeMod_12_byteEncode_12 (htHat_can i)
  have hrhoEnc_eq : rhoEnc = rho := by
    dsimp only [rhoEnc]
    have hdrop : pk.drop (4 * 384) = rho :=
      flatten_range4_append_drop (L := 384) (fun j => byteEncode 12 (tHat.getD j zeroPoly)) rho
        (fun j _ => byteEncode_length 12 _)
    rw [show (1536 : Nat) = 4 * 384 by decide, hdrop]
    exact List.take_of_length_le (by omega)
  have huHat_getD : ∀ k : Fin 4,
      uHat.getD k.val zeroPoly =
        polyNtt (decodeAndDecompress 11 (compressAndEncode 11 (uVec.getD k.val zeroPoly))) := by
    intro k
    dsimp only [uHat, c1Block]
    rw [getD_ofFn_nat _ k.val zeroPoly k.isLt]
    have hmul : k.val * (32 * 11) = 352 * k.val := by omega
    have hslice :
        ((ct.drop (352 * k.val)).take 352) = compressAndEncode 11 (uVec.getD k.val zeroPoly) :=
      flatten_range4_append_slice (L := 352)
        (fun j => compressAndEncode 11 (uVec.getD j zeroPoly)) c2
        (fun j _ => compressAndEncode_length 11 _) k.isLt
    rw [hmul, show 32 * 11 = 352 by decide, hslice]
  have hvDec_eq : vDec = decodeAndDecompress 5 (compressAndEncode 5 vPoly) := by
    dsimp only [vDec, c1Len, c1Block]
    have hdrop : ct.drop (4 * 352) = c2 :=
      flatten_range4_append_drop (L := 352)
        (fun j => compressAndEncode 11 (uVec.getD j zeroPoly)) c2
        (fun j _ => compressAndEncode_length 11 _)
    have hc2_len : c2.length = 160 := compressAndEncode_length 5 vPoly
    rw [show 4 * (32 * 11) = 4 * 352 by decide, show 32 * 5 = 160 by decide, hdrop,
      List.take_of_length_le (by omega : c2.length ≤ 160)]
  -- Express `tHat`, `uVec`, `vPoly`, and `sᵀ uDec` in `ZPoly`
  have htPoly_eq : ∀ i : Fin 4,
      toZPoly (polyInvNtt (tHat.getD i.val zeroPoly)) =
        (∑ k : Fin 4, negacyclicMul (A i k) (sZ k)) + eZ i := by
    intro i
    have ht_get : tHat.getD i.val zeroPoly =
        polyAdd (vecDotNtt 4 (aMat.getD i.val #[]) sHat) (eHat.getD i.val zeroPoly) := by
      dsimp only [tHat]
      exact getD_ofFn_nat _ i.val zeroPoly i.isLt
    have heHat_get : eHat.getD i.val zeroPoly =
        polyNtt (samplePolyCbd2 (nKG ⟨4 + i.val, by omega⟩)) := by
      dsimp only [eHat]
      exact getD_ofFn_nat _ i.val zeroPoly i.isLt
    have heHat_can : IsCanonicalPoly (eHat.getD i.val zeroPoly) := by
      rw [heHat_get]
      exact polyNtt_isCanonical (samplePolyCbd2_isCanonical _).1
    rw [ht_get, toZPoly_polyInvNtt_polyAdd (vecDotNtt_isCanonical 4 _ _) heHat_can]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [toZPoly_polyInvNtt_vecDotNtt, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hs_get : sHat.getD k.val zeroPoly =
          polyNtt (samplePolyCbd2 (nKG ⟨k.val, by omega⟩)) := by
        dsimp only [sHat]
        exact getD_ofFn_nat _ k.val zeroPoly k.isLt
      rw [hs_get, toZPoly_polyInvNtt_polyNttMul_left
        (sampleMatrixWith_entry_isCanonical hSampler rho true i.isLt k.isLt)
        (samplePolyCbd2_isCanonical _).1]
      rw [toZPoly_samplePolyCbd2_eq]
      rfl
    · rw [heHat_get, toZPoly_polyInvNtt_polyNtt (samplePolyCbd2_isCanonical _).1,
        toZPoly_samplePolyCbd2_eq]
      rfl
  have hwVec_eq : ∀ k : Fin 4,
      toZPoly (polyInvNtt (vecDotNtt 4 (aTrans.getD k.val #[]) rHat)) = wVec k := by
    intro k
    rw [toZPoly_polyInvNtt_vecDotNtt, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hr_get : rHat.getD i.val zeroPoly =
        polyNtt (samplePolyCbd2 (nEnc ⟨i.val, by omega⟩)) := by
      dsimp only [rHat]
      exact getD_ofFn_nat _ i.val zeroPoly i.isLt
    have haTrans_get :
        ((aTrans.getD k.val #[]).getD i.val zeroPoly) =
          ((aMat.getD i.val #[]).getD k.val zeroPoly) := by
      dsimp only [aTrans, aMat]
      rw [hrhoEnc_eq]
      exact sampleMatrixWith_transpose sampler 4 rho k.val i.val k.isLt i.isLt
    rw [haTrans_get, hr_get, toZPoly_polyInvNtt_polyNttMul_left
      (sampleMatrixWith_entry_isCanonical hSampler rho true i.isLt k.isLt)
      (samplePolyCbd2_isCanonical _).1]
    rw [toZPoly_samplePolyCbd2_eq]
    rfl
  have huVec_toZ : ∀ k : Fin 4, toZPoly (uVec.getD k.val zeroPoly) = wVec k + e1Z k := by
    intro k
    have hu_get : uVec.getD k.val zeroPoly =
        polyAdd (polyInvNtt (vecDotNtt 4 (aTrans.getD k.val #[]) rHat))
          (e1.getD k.val zeroPoly) := by
      dsimp only [uVec]
      exact getD_ofFn_nat _ k.val zeroPoly k.isLt
    have he1_get : e1.getD k.val zeroPoly = samplePolyCbd2 (nEnc ⟨4 + k.val, by omega⟩) := by
      dsimp only [e1]
      exact getD_ofFn_nat _ k.val zeroPoly k.isLt
    rw [hu_get, toZPoly_polyAdd, hwVec_eq k, he1_get, toZPoly_samplePolyCbd2_eq]
    rfl
  have htR_eq :
      toZPoly (polyInvNtt (vecDotNtt 4 tHatEnc rHat)) =
        ∑ i : Fin 4, negacyclicMul ((∑ k : Fin 4, negacyclicMul (A i k) (sZ k)) + eZ i) (rZ i) := by
    rw [toZPoly_polyInvNtt_vecDotNtt, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hr_get : rHat.getD i.val zeroPoly =
        polyNtt (samplePolyCbd2 (nEnc ⟨i.val, by omega⟩)) := by
      dsimp only [rHat]
      exact getD_ofFn_nat _ i.val zeroPoly i.isLt
    rw [htHatEnc_getD i, hr_get, toZPoly_polyInvNtt_polyNttMul_left (htHat_can i)
      (samplePolyCbd2_isCanonical _).1, htPoly_eq i, toZPoly_samplePolyCbd2_eq]
    rfl
  have hvPoly_toZ : ∀ j : Fin 256, toZPoly vPoly j = v0 j + e2Z j := by
    intro j
    dsimp only [vPoly, v0]
    rw [toZPoly_polyAdd, toZPoly_polyAdd, htR_eq]
    have he2_eq : toZPoly e2 j = e2Z j := by
      dsimp only [e2]
      rw [toZPoly_samplePolyCbd2_eq]
      rfl
    simp only [Pi.add_apply, he2_eq]
    ring
  have hsU_eq :
      toZPoly (polyInvNtt (vecDotNtt 4 sHatDec uHat)) =
        (∑ k : Fin 4, negacyclicMul (sZ k) (wVec k)) +
          ∑ k : Fin 4,
            negacyclicMul (sZ k)
              (fun idx => e1Z k idx +
                (compressErrZMod 11 (wVec k idx + e1Z k idx) : ZMod mlkemQ)) := by
    rw [toZPoly_polyInvNtt_vecDotNtt, ← Fin.sum_univ_eq_sum_range, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hs_get : sHat.getD k.val zeroPoly =
        polyNtt (samplePolyCbd2 (nKG ⟨k.val, by omega⟩)) := by
      dsimp only [sHat]
      exact getD_ofFn_nat _ k.val zeroPoly k.isLt
    rw [hsHatDec_getD k, hs_get, huHat_getD k,
      toZPoly_polyInvNtt_polyNttMul (samplePolyCbd2_isCanonical _).1 (decodeAndDecompress_size 11 _),
      toZPoly_samplePolyCbd2_eq]
    have huDec_toZ :
        toZPoly (decodeAndDecompress 11 (compressAndEncode 11 (uVec.getD k.val zeroPoly))) =
          wVec k +
            (fun idx => e1Z k idx +
              (compressErrZMod 11 (wVec k idx + e1Z k idx) : ZMod mlkemQ)) := by
      funext idx
      rw [toZPoly_decodeAndDecompress_compressAndEncode
        (by decide : 0 < 11) (by decide : 11 ≤ 12) _ idx, huVec_toZ k]
      simp only [Pi.add_apply]
      ring
    rw [huDec_toZ, ← negacyclicMul_add]
    rfl
  have hw_sub_m : ∀ j : Fin 256,
      toZPoly wPoly j - toZPoly mPoly j =
        (intNoise wVec v0 (kgS nKG) (kgE nKG) (encR nEnc) (encE1 nEnc) (encE2 nEnc) j :
          ZMod mlkemQ) := by
    intro j
    rw [intNoise_cast_eq]
    have hw_toZ : toZPoly wPoly j =
        toZPoly vDec j - toZPoly (polyInvNtt (vecDotNtt 4 sHatDec uHat)) j := by
      dsimp only [wPoly]
      rw [toZPoly_polySub]
      rfl
    have hvDec_j : toZPoly vDec j =
        (decompressCoeff 5 (compressCoeff 5 (v0 j + e2Z j).val) : ZMod mlkemQ) := by
      rw [hvDec_eq, toZPoly_decodeAndDecompress_5_compressAndEncode_5, hvPoly_toZ j]
    have hcancel := congrFun (cancel_matrix_quadratic_form A sZ eZ rZ) j
    simp only [Pi.sub_apply, Finset.sum_apply] at hcancel
    rw [hw_toZ, hsU_eq, hvDec_j]
    dsimp only [v0]
    simp only [Pi.add_apply, Finset.sum_apply]
    linear_combination hcancel
  by_contra hNo
  have hBound : ∀ j : Fin 256,
      |centeredZMod (toZPoly wPoly j - toZPoly mPoly j)| ≤ 831 := by
    intro j
    set N := intNoise wVec v0 (kgS nKG) (kgE nKG) (encR nEnc) (encE1 nEnc) (encE2 nEnc) j
    have hN_lt : ¬ (832 ≤ |N|) := fun hge => hNo ⟨j, hge⟩
    have hN_le : |N| ≤ 831 := by omega
    have hN_bnds : -831 ≤ N ∧ N ≤ 831 := abs_le.mp hN_le
    rw [hw_sub_m j, centeredZMod_of_int_bounds (by omega) (by omega)]
    exact hN_le
  have hDec_ok : compressAndEncode 1 wPoly = m :=
    compressAndEncode_1_eq_of_noise_le_831 hm_len wPoly hBound
  rw [hDec_ok, bne_self_eq_false] at hFail
  exact Bool.false_ne_true hFail

/-! ## 4. Pointwise & Sampled Ideal K-PKE Tail Bounds (`≤ 1 / 2^112`) -/

private theorem evalDist_bind_apply_mono_prob {α : Type} (oa : ProbComp α)
    (f g : α → ProbComp Bool) (hfg : ∀ a, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) :
    𝒟[oa >>= f] {true} ≤ 𝒟[oa >>= g] {true} := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  exact evalDist_bind_apply_mono_of_discrete oa f g MeasurableSet.of_discrete hfg

private theorem evalDist_bind_apply_le_const_prob {α : Type} (oa : ProbComp α)
    (f : α → ProbComp Bool) (c : ℝ≥0∞) (hf : ∀ a, 𝒟[f a] {true} ≤ c) :
    𝒟[oa >>= f] {true} ≤ c := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  calc ∫⁻ a, 𝒟[f a] {true} ∂𝒟[oa]
      ≤ ∫⁻ _a, c ∂𝒟[oa] := lintegral_mono hf
    _ = c := by rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

theorem kpkeBodyFails_prob_le_two_pow_neg_112
    {sampler : List (BitVec 8) → Poly}
    (hSampler : ∀ s, IsCanonicalPoly (sampler s))
    (seed64 rand32 : List (BitVec 8)) :
    𝒟[do
        let nKG ← cbdNoiseVec 8
        let nEnc ← cbdNoiseVec 9
        pure (kpkeBodyFails sampler seed64 rand32 nKG nEnc)] {true} ≤
      1 / (2 : ℝ≥0∞) ^ 112 := by
  have hmono :
      𝒟[do
          let nKG ← cbdNoiseVec 8
          let nEnc ← cbdNoiseVec 9
          pure (kpkeBodyFails sampler seed64 rand32 nKG nEnc)] {true} ≤
      𝒟[do
          let nKG ← cbdNoiseVec 8
          let nEnc ← cbdNoiseVec 9
          pure (decide (∃ j : Fin 256,
            832 ≤ |intNoise (wVecFn sampler seed64 (encR nEnc))
              (v0Fn sampler seed64 rand32 (kgS nKG) (kgE nKG) (encR nEnc))
              (kgS nKG) (kgE nKG) (encR nEnc) (encE1 nEnc) (encE2 nEnc) j|))] {true} := by
    refine evalDist_bind_apply_mono_prob _ _ _ fun nKG => ?_
    refine evalDist_bind_apply_mono_prob _ _ _ fun nEnc => ?_
    refine evalDist_pure_apply_le_of_imp _ _ fun hFail => ?_
    exact decide_eq_true (kpkeBodyFails_imp_exists_noise_ge_832 hSampler seed64 rand32 nKG nEnc hFail)
  exact le_trans hmono
    (w2_intNoise_tail_bound_le_two_pow_neg_112
      (wVecFn sampler seed64)
      (v0Fn sampler seed64 rand32)
      (le_of_eq termA_eq)
      termGAt_le_constG
      termHAt_le_constH
      (le_of_lt w2_certificate_lt_two_pow_neg_112))

theorem kpkeBodyFails_sampleNtt_prob_le_two_pow_neg_112
    (seed64 rand32 : List (BitVec 8)) :
    𝒟[do
        let nKG ← cbdNoiseVec 8
        let nEnc ← cbdNoiseVec 9
        pure (kpkeBodyFails sampleNtt seed64 rand32 nKG nEnc)] {true} ≤
      1 / (2 : ℝ≥0∞) ^ 112 :=
  kpkeBodyFails_prob_le_two_pow_neg_112 sampleNtt_isCanonical seed64 rand32

theorem kpkeBodyFails_sampleNtt_full_exp_le_two_pow_neg_112 :
    𝒟[do
        let seed ← SignalPqxdh.sampleRandom64
        let r ← SignalPqxdh.sampleCoins32
        let seed64 := seed.map UInt8.toBitVec
        let rand32 := r.map UInt8.toBitVec
        let nKG ← cbdNoiseVec 8
        let nEnc ← cbdNoiseVec 9
        pure (kpkeBodyFails sampleNtt seed64 rand32 nKG nEnc)] {true} ≤
      1 / (2 : ℝ≥0∞) ^ 112 := by
  refine evalDist_bind_apply_le_const_prob _ _ _ fun seed => ?_
  refine evalDist_bind_apply_le_const_prob _ _ _ fun r => ?_
  exact kpkeBodyFails_sampleNtt_prob_le_two_pow_neg_112 (seed.map UInt8.toBitVec)
    (r.map UInt8.toBitVec)

end Computational.Proofs.Kyber1024Delta.KpkeIdealBound

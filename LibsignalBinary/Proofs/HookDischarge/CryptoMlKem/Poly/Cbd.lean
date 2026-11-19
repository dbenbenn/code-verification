/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import

/-!
# Centered binomial distribution sampling (`cbd2` and `cbd3`)

1. SWAR 32-bit `cbd2` (`((t >>> 1) &&& 0x55555555) + (t &&& 0x55555555)`, extracting 8 signed `i16`
   coefficients in `[-2, 2]` per little-endian `u32`, matching `B03 +0x36b4..+0x3750` / `B05`)
   proved equivalent to `Spec.samplePolyCbd2` (`PolyBounded16 2` and `PolyRepresents`).
2. FIPS 203 Algorithm 7 `samplePolyCbd3` (`192` bytes → `Poly`) and SWAR 24-bit `cbd3`
   (`(t &&& 0x249249) + ((t >>> 1) &&& 0x249249) + ((t >>> 2) &&& 0x249249)`, extracting 4 signed
   `i16` coefficients in `[-3, 3]` per 3-byte chunk) proved equivalent (`PolyBounded16 3` and
   `PolyRepresents`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 mlkemQ bytesToBits samplePolyCbd2
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  fin8_cases
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents
)

private theorem getD_ofFn {α : Type} {n : Nat} (g : Fin n → α) (i : Nat) (d : α) (hi : i < n) :
    (Array.ofFn g).getD i d = g ⟨i, hi⟩ := by
  simp [Array.getD, hi]

private theorem bytesToBits_getD (bs : List (BitVec 8)) (idx : Nat) (h : idx < 8 * bs.length) :
    (bytesToBits bs).getD idx 0 =
      (((bs.toArray.getD (idx / 8) 0#8).toNat >>> (idx % 8)) &&& 1) := by
  unfold bytesToBits
  rw [getD_ofFn _ _ _ h]

private theorem shr_and1_eq_getLsbD {w : Nat} (x : BitVec w) (k : Nat) :
    ((x.toNat >>> k) &&& 1) = if x.getLsbD k then 1 else 0 := by
  simp only [BitVec.getLsbD, Nat.testBit, Nat.and_comm 1, Nat.and_one_is_mod, bne_iff_ne, ne_eq]
  by_cases hz : (x.toNat >>> k) % 2 = 0 <;> (simp [hz]; try omega)

private theorem nat_and_3 (x : Nat) : x &&& 3 = x % 4 :=
  Nat.and_two_pow_sub_one_eq_mod x 2

private theorem nat_and_7 (x : Nat) : x &&& 7 = x % 8 :=
  Nat.and_two_pow_sub_one_eq_mod x 3

private theorem toNat_append_eq {m n : Nat} (hi : BitVec m) (lo : BitVec n)
    (hpow : 2 ^ m * 2 ^ n = 2 ^ (m + n)) (hn1 : 1 ≤ 2 ^ n := by decide) :
    (hi ++ lo).toNat = hi.toNat * 2 ^ n + lo.toNat := by
  have hdisj : ((hi.setWidth (m + n) <<< n) &&& lo.setWidth (m + n)) = 0#(m + n) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi_lt
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_zero, hi_lt, decide_true, Bool.true_and]
    by_cases hn : i < n
    · simp [hn]
    · simp [hn, BitVec.getLsbD_of_ge lo i (by omega)]
  have hsplit : (hi ++ lo) = (hi.setWidth (m + n) <<< n) + lo.setWidth (m + n) := by
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdisj]
    apply BitVec.eq_of_getLsbD_eq; intro i hi_lt
    simp only [BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, hi_lt, decide_true, Bool.true_and]
    by_cases hn : i < n
    · simp [hn]
    · simp [hn, BitVec.getLsbD_of_ge lo i (by omega), show i - n < m + n by omega]
  have h1 := hi.isLt; have h2 := lo.isLt
  have hbound : hi.toNat * 2 ^ n + lo.toNat < 2 ^ (m + n) := by
    have hmul : (hi.toNat + 1) * 2 ^ n ≤ 2 ^ m * 2 ^ n := Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul, hpow] at hmul
    omega
  have hhi_lt : hi.toNat < 2 ^ (m + n) := by
    have := Nat.le_mul_of_pos_right hi.toNat hn1
    omega
  rw [hsplit, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt hhi_lt, Nat.mod_eq_of_lt (by omega : hi.toNat * 2 ^ n < 2 ^ (m + n)),
    Nat.mod_eq_of_lt (by omega : lo.toNat < 2 ^ (m + n)), Nat.mod_eq_of_lt hbound]

/-! ## 1. `cbd2` (`η = 2`, `128` bytes = `32 × u32` → `256` signed `i16` in `[-2, 2]`) -/

/-- Byte-level SWAR bit-pair sum `((b >>> 1) &&& 0x55) + (b &&& 0x55)`. -/
@[expose] def cbd2SwarByte (b : BitVec 8) : BitVec 8 :=
  ((b >>> 1) &&& 0x55#8) + (b &&& 0x55#8)

/-- Extract coefficient `half ∈ {0, 1}` from a single byte's SWAR bit-pair sum. -/
@[expose] def cbd2CoeffFromByte (b : BitVec 8) (half : Fin 2) : BitVec 16 :=
  let s : BitVec 32 := (cbd2SwarByte b).zeroExtend 32
  let a := (s >>> (4 * half.val)) &&& 3#32
  let c := (s >>> (4 * half.val + 2)) &&& 3#32
  (a - c).truncate 16

/-- 32-bit SWAR bit-pair sum matching `B03 +0x36bc..+0x36c4` (`w19 = 0x55555555`). -/
@[expose] def cbd2SwarSum (t : BitVec 32) : BitVec 32 :=
  ((t >>> 1) &&& 0x55555555#32) + (t &&& 0x55555555#32)

/-- Extract the `j`-th (`j : Fin 8`) signed `i16` coefficient from a 32-bit SWAR word `t`. -/
@[expose] def cbd2CoeffFromWord (t : BitVec 32) (j : Fin 8) : BitVec 16 :=
  let d := cbd2SwarSum t
  let a := (d >>> (4 * j.val)) &&& 3#32
  let b := (d >>> (4 * j.val + 2)) &&& 3#32
  (a - b).truncate 16

/-- Assemble a little-endian `u32` from 4 bytes of `bs` starting at byte offset `4 * w`. -/
@[expose] def readU32LE (bs : List (BitVec 8)) (w : Nat) : BitVec 32 :=
  let arr := bs.toArray
  (arr.getD (4 * w + 3) 0#8) ++ (arr.getD (4 * w + 2) 0#8) ++
  (arr.getD (4 * w + 1) 0#8) ++ (arr.getD (4 * w) 0#8)

/-- Full 32-iteration scalar SWAR `cbd2` producing `Poly16` (`256 × BitVec 16`). -/
@[expose] def neonCbd2Poly16 (bs : List (BitVec 8)) : Poly16 :=
  Array.ofFn (n := 256) fun k =>
    cbd2CoeffFromWord (readU32LE bs (k.val / 8)) ⟨k.val % 8, by omega⟩

@[expose] def cbd2ByteProps (n : Fin 256) : Bool :=
  let b : BitVec 8 := BitVec.ofNat 8 n.val
  let u := (b >>> 1) &&& 0x55#8
  let v := b &&& 0x55#8
  let noCarry := decide (u.toNat + v.toNat < 256)
  let c0 := cbd2CoeffFromByte b 0
  let c1 := cbd2CoeffFromByte b 1
  let bit (k : Nat) := (b.toNat >>> k) &&& 1
  let f0 : Nat := ((bit 0 + bit 1) + 3329 - (bit 2 + bit 3)) % 3329
  let f1 : Nat := ((bit 4 + bit 5) + 3329 - (bit 6 + bit 7)) % 3329
  noCarry &&
  decide (-2 ≤ c0.toInt ∧ c0.toInt ≤ 2) &&
  decide (-2 ≤ c1.toInt ∧ c1.toInt ≤ 2) &&
  decide (c0.toInt % 3329 = (f0 : Int) % 3329) &&
  decide (c1.toInt % 3329 = (f1 : Int) % 3329)

private theorem cbd2ByteProps_all : ∀ n : Fin 256, cbd2ByteProps n = true := by
  decide +kernel

private theorem cbd2_byte_noCarry (b : BitVec 8) :
    ((b >>> 1) &&& 0x55#8).toNat + (b &&& 0x55#8).toNat < 256 := by
  have h := cbd2ByteProps_all ⟨b.toNat, b.isLt⟩
  unfold cbd2ByteProps at h
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

private theorem getLsbD_append4_u8 (x3 x2 x1 x0 : BitVec 8) (k : Nat) (hk : k < 32) :
    (x3 ++ x2 ++ x1 ++ x0).getLsbD k =
      (match k / 8 with | 0 => x0 | 1 => x1 | 2 => x2 | _ => x3).getLsbD (k % 8) := by
  simp only [BitVec.getLsbD_append]
  by_cases h8 : k < 8
  · have hd : k / 8 = 0 := by omega
    have hm : k % 8 = k := by omega
    simp [h8, hd, hm]
  · by_cases h16 : k < 16
    · have hd : k / 8 = 1 := by omega
      have hm : k - 8 = k % 8 := by omega
      have hc : k % 8 < 8 := by omega
      simp [h8, hd, hm, hc]
    · by_cases h24 : k < 24
      · have hd : k / 8 = 2 := by omega
        have hm1 : ¬ (k - 8 < 8) := by omega
        have hm2 : k - 8 - 8 = k % 8 := by omega
        have hc : k % 8 < 8 := by omega
        simp [h8, hd, hm1, hm2, hc]
      · have hd : k / 8 = 3 := by omega
        have hm1 : ¬ (k - 8 < 8) := by omega
        have hm2 : ¬ (k - 8 - 8 < 8) := by omega
        have hm3 : k - 8 - 8 - 8 = k % 8 := by omega
        simp [h8, hd, hm1, hm2, hm3]

private theorem mask32_0x55 :
    ∀ i : Fin 32,
      (0x55555555#32).getLsbD i.val = (0x55#8).getLsbD (i.val % 8) ∧
      (i.val % 8 = 7 → (0x55555555#32).getLsbD i.val = false) := by
  decide +kernel

private theorem append4_u8_shr_and_0x55555555 (b3 b2 b1 b0 : BitVec 8) (s : Nat) (hs : s ≤ 1) :
    (((b3 ++ b2 ++ b1 ++ b0) >>> s) &&& 0x55555555#32) =
      (((b3 >>> s) &&& 0x55#8) ++ ((b2 >>> s) &&& 0x55#8) ++
       ((b1 >>> s) &&& 0x55#8) ++ ((b0 >>> s) &&& 0x55#8)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_append4_u8 _ _ _ _ i hi]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  have hm := mask32_0x55 ⟨i, hi⟩
  dsimp only at hm
  rcases s with _ | _ | s <;> try omega
  · simp only [Nat.zero_add, hm.1, getLsbD_append4_u8 b3 b2 b1 b0 i hi]
    have hrem : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
    rcases hrem with h | h | h | h <;> simp [h]
  · by_cases h7 : i % 8 = 7
    · rw [hm.2 h7, h7, Bool.and_false]
      have hrem : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
      rcases hrem with h | h | h | h <;> simp [h]
    · have hi1 : 1 + i < 32 := by omega
      have hdiv : (1 + i) / 8 = i / 8 := by omega
      have hmod : (1 + i) % 8 = 1 + i % 8 := by omega
      rw [getLsbD_append4_u8 b3 b2 b1 b0 (1 + i) hi1, hdiv, hmod, hm.1]
      have hrem : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
      rcases hrem with h | h | h | h <;> simp [h]

private theorem toNat_append4_u8 (x3 x2 x1 x0 : BitVec 8) :
    (x3 ++ x2 ++ x1 ++ x0).toNat =
      x0.toNat + 256 * x1.toNat + 65536 * x2.toNat + 16777216 * x3.toNat := by
  rw [toNat_append_eq _ x0 (by decide), toNat_append_eq _ x1 (by decide),
    toNat_append_eq x3 x2 (by decide)]
  omega

theorem cbd2SwarSum_append4 (b3 b2 b1 b0 : BitVec 8) :
    cbd2SwarSum (b3 ++ b2 ++ b1 ++ b0) =
      cbd2SwarByte b3 ++ cbd2SwarByte b2 ++ cbd2SwarByte b1 ++ cbd2SwarByte b0 := by
  unfold cbd2SwarSum
  have h1 := append4_u8_shr_and_0x55555555 b3 b2 b1 b0 1 (by omega)
  have h0 := append4_u8_shr_and_0x55555555 b3 b2 b1 b0 0 (by omega)
  simp only [BitVec.ushiftRight_zero] at h0
  rw [h1, h0]
  apply BitVec.eq_of_toNat_eq
  have hc0 := cbd2_byte_noCarry b0
  have hc1 := cbd2_byte_noCarry b1
  have hc2 := cbd2_byte_noCarry b2
  have hc3 := cbd2_byte_noCarry b3
  rw [BitVec.toNat_add, toNat_append4_u8, toNat_append4_u8, toNat_append4_u8]
  simp only [cbd2SwarByte, BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
  omega

private theorem shr_byte_and3_eq (s3 s2 s1 s0 : BitVec 8) (j : Fin 8) (sh : Nat) (hsh : sh = 0 ∨ sh = 2) :
    let d : BitVec 32 := s3 ++ s2 ++ s1 ++ s0
    let sb : BitVec 8 :=
      if j.val / 2 = 0 then s0 else if j.val / 2 = 1 then s1 else if j.val / 2 = 2 then s2 else s3
    ((d >>> (4 * j.val + sh)) &&& 3#32) = ((sb.zeroExtend 32 >>> (4 * (j.val % 2) + sh)) &&& 3#32) := by
  dsimp only
  apply BitVec.eq_of_toNat_eq
  have h3 : (3#32 : BitVec 32).toNat = 3 := rfl
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.zeroExtend, BitVec.toNat_setWidth,
    h3, nat_and_3, toNat_append4_u8]
  have hs0 := s0.isLt; have hs1 := s1.isLt; have hs2 := s2.isLt; have hs3 := s3.isLt
  rcases j with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hj⟩ <;> try omega
  all_goals
    rcases hsh with rfl | rfl <;>
    (dsimp only;
     simp only [Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceEqDiff,
       Nat.shiftRight_eq_div_pow, Nat.reducePow, ↓reduceIte];
     rw [Nat.mod_eq_of_lt (by omega : _ < 4294967296)];
     omega)

theorem cbd2CoeffFromWord_eq_byte (b3 b2 b1 b0 : BitVec 8) (j : Fin 8) :
    cbd2CoeffFromWord (b3 ++ b2 ++ b1 ++ b0) j =
      cbd2CoeffFromByte
        (if j.val / 2 = 0 then b0 else if j.val / 2 = 1 then b1 else if j.val / 2 = 2 then b2 else b3)
        ⟨j.val % 2, by omega⟩ := by
  unfold cbd2CoeffFromWord cbd2CoeffFromByte
  rw [cbd2SwarSum_append4]
  have h0 := shr_byte_and3_eq (cbd2SwarByte b3) (cbd2SwarByte b2) (cbd2SwarByte b1) (cbd2SwarByte b0) j 0 (Or.inl rfl)
  have h2 := shr_byte_and3_eq (cbd2SwarByte b3) (cbd2SwarByte b2) (cbd2SwarByte b1) (cbd2SwarByte b0) j 2 (Or.inr rfl)
  simp only [Nat.add_zero] at h0 ⊢
  dsimp only at h0 h2 ⊢
  rw [h0, h2]
  induction j using fin8_cases <;> rfl

theorem neonCbd2Poly16_spec {bs : List (BitVec 8)} (hbs : bs.length = 128) :
    PolyBounded16 2 (neonCbd2Poly16 bs) ∧
    PolyRepresents (neonCbd2Poly16 bs) (samplePolyCbd2 bs) := by
  have hsize : (neonCbd2Poly16 bs).size = 256 := by simp [neonCbd2Poly16]
  suffices hlane : ∀ i < 256,
      let out := (neonCbd2Poly16 bs).getD i 0#16
      (-2 ≤ out.toInt ∧ out.toInt ≤ 2) ∧
      out.toInt % 3329 = (((samplePolyCbd2 bs).getD i 0 : Nat) : Int) % 3329 by
    refine ⟨⟨hsize, fun i hi => (hlane i hi).1⟩, ⟨hsize, fun i hi => (hlane i hi).2⟩⟩
  intro i hi
  dsimp only
  rw [neonCbd2Poly16, getD_ofFn _ _ _ hi, samplePolyCbd2, getD_ofFn _ _ _ hi]
  dsimp only [readU32LE]
  rw [cbd2CoeffFromWord_eq_byte]
  dsimp only
  have hsel :
      (if (i % 8) / 2 = 0 then bs.toArray.getD (4 * (i / 8)) 0#8
       else if (i % 8) / 2 = 1 then bs.toArray.getD (4 * (i / 8) + 1) 0#8
       else if (i % 8) / 2 = 2 then bs.toArray.getD (4 * (i / 8) + 2) 0#8
       else bs.toArray.getD (4 * (i / 8) + 3) 0#8) = bs.toArray.getD (i / 2) 0#8 := by
    have hdiv : i / 2 = 4 * (i / 8) + (i % 8) / 2 := by omega
    rw [hdiv]
    have hrem : (i % 8) / 2 = 0 ∨ (i % 8) / 2 = 1 ∨ (i % 8) / 2 = 2 ∨ (i % 8) / 2 = 3 := by omega
    rcases hrem with h | h | h | h <;> simp [h]
  have hfin : (⟨(i % 8) % 2, by omega⟩ : Fin 2) = ⟨i % 2, by omega⟩ := by ext; simp
  rw [hsel, hfin]
  let b := bs.toArray.getD (i / 2) 0#8
  have hprop := cbd2ByteProps_all ⟨b.toNat, b.isLt⟩
  unfold cbd2ByteProps at hprop
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.and_eq_true, decide_eq_true_eq] at hprop
  rw [bytesToBits_getD bs (4 * i) (by omega), bytesToBits_getD bs (4 * i + 1) (by omega),
    bytesToBits_getD bs (4 * i + 2) (by omega), bytesToBits_getD bs (4 * i + 3) (by omega)]
  have hd0 : (4 * i) / 8 = i / 2 := by omega
  have hd1 : (4 * i + 1) / 8 = i / 2 := by omega
  have hd2 : (4 * i + 2) / 8 = i / 2 := by omega
  have hd3 : (4 * i + 3) / 8 = i / 2 := by omega
  rw [hd0, hd1, hd2, hd3]
  by_cases heven : i % 2 = 0
  · have hm0 : (4 * i) % 8 = 0 := by omega
    have hm1 : (4 * i + 1) % 8 = 1 := by omega
    have hm2 : (4 * i + 2) % 8 = 2 := by omega
    have hm3 : (4 * i + 3) % 8 = 3 := by omega
    have hf0 : (⟨i % 2, by omega⟩ : Fin 2) = 0 := by ext; exact heven
    rw [hf0, hm0, hm1, hm2, hm3]
    exact ⟨hprop.1.1.1.2, hprop.1.2⟩
  · have hodd : i % 2 = 1 := by omega
    have hm0 : (4 * i) % 8 = 4 := by omega
    have hm1 : (4 * i + 1) % 8 = 5 := by omega
    have hm2 : (4 * i + 2) % 8 = 6 := by omega
    have hm3 : (4 * i + 3) % 8 = 7 := by omega
    have hf1 : (⟨i % 2, by omega⟩ : Fin 2) = 1 := by ext; exact hodd
    rw [hf1, hm0, hm1, hm2, hm3]
    exact ⟨hprop.1.1.2, hprop.2⟩

/-! ## 2. `cbd3` (`η = 3`, `192` bytes = `64 × 24`-bit words → `256` signed `i16` in `[-3, 3]`) -/

/-- FIPS 203 Algorithm 7 (`SamplePolyCBD_3`, `192` bytes → `Poly`). -/
@[expose] def samplePolyCbd3 (bs : List (BitVec 8)) : Poly :=
  let bits := bytesToBits bs
  Array.ofFn (n := 256) fun ⟨i, _⟩ =>
    let a := bits.getD (6 * i) 0 + bits.getD (6 * i + 1) 0 + bits.getD (6 * i + 2) 0
    let b := bits.getD (6 * i + 3) 0 + bits.getD (6 * i + 4) 0 + bits.getD (6 * i + 5) 0
    (a + mlkemQ - b) % mlkemQ

@[expose] def cbd3SwarHalf12 (h : BitVec 12) : BitVec 12 :=
  (h &&& 0x249#12) + ((h >>> 1) &&& 0x249#12) + ((h >>> 2) &&& 0x249#12)

@[expose] def cbd3CoeffFromHalf12 (h : BitVec 12) (half : Fin 2) : BitVec 16 :=
  let s : BitVec 32 := (cbd3SwarHalf12 h).zeroExtend 32
  let a := (s >>> (6 * half.val)) &&& 7#32
  let b := (s >>> (6 * half.val + 3)) &&& 7#32
  (a - b).truncate 16

@[expose] def cbd3SwarSum24 (t : BitVec 24) : BitVec 24 :=
  (t &&& 0x00249249#24) + ((t >>> 1) &&& 0x00249249#24) + ((t >>> 2) &&& 0x00249249#24)

@[expose] def cbd3CoeffFromWord24 (t : BitVec 24) (j : Fin 4) : BitVec 16 :=
  let d : BitVec 32 := (cbd3SwarSum24 t).zeroExtend 32
  let a := (d >>> (6 * j.val)) &&& 7#32
  let b := (d >>> (6 * j.val + 3)) &&& 7#32
  (a - b).truncate 16

@[expose] def readU24LE (bs : List (BitVec 8)) (w : Nat) : BitVec 24 :=
  let arr := bs.toArray
  (arr.getD (3 * w + 2) 0#8) ++ (arr.getD (3 * w + 1) 0#8) ++ (arr.getD (3 * w) 0#8)

@[expose] def swarCbd3Poly16 (bs : List (BitVec 8)) : Poly16 :=
  Array.ofFn (n := 256) fun k =>
    cbd3CoeffFromWord24 (readU24LE bs (k.val / 4)) ⟨k.val % 4, by omega⟩

@[expose] def cbd3Half12Props (n : Nat) : Bool :=
  let h : BitVec 12 := BitVec.ofNat 12 n
  let u := h &&& 0x249#12
  let v := (h >>> 1) &&& 0x249#12
  let w := (h >>> 2) &&& 0x249#12
  let noCarry := decide (u.toNat + v.toNat + w.toNat < 4096)
  let c0 := cbd3CoeffFromHalf12 h 0
  let c1 := cbd3CoeffFromHalf12 h 1
  let bit (k : Nat) := (h.toNat >>> k) &&& 1
  let f0 : Nat := ((bit 0 + bit 1 + bit 2) + 3329 - (bit 3 + bit 4 + bit 5)) % 3329
  let f1 : Nat := ((bit 6 + bit 7 + bit 8) + 3329 - (bit 9 + bit 10 + bit 11)) % 3329
  noCarry &&
  decide (-3 ≤ c0.toInt ∧ c0.toInt ≤ 3) &&
  decide (-3 ≤ c1.toInt ∧ c1.toInt ≤ 3) &&
  decide (c0.toInt % 3329 = (f0 : Int) % 3329) &&
  decide (c1.toInt % 3329 = (f1 : Int) % 3329)

private theorem cbd3Half12Props_blocks :
    ∀ hi : Fin 16, ∀ lo : Fin 256, cbd3Half12Props (256 * hi.val + lo.val) = true := by
  decide +kernel

private theorem cbd3Half12Props_of_bv (h : BitVec 12) : cbd3Half12Props h.toNat = true := by
  have hlt := h.isLt
  have hdiv : 256 * (h.toNat / 256) + h.toNat % 256 = h.toNat := Nat.div_add_mod h.toNat 256
  rw [← hdiv]
  exact cbd3Half12Props_blocks ⟨h.toNat / 256, by omega⟩ ⟨h.toNat % 256, by omega⟩

private theorem cbd3_half12_noCarry (h : BitVec 12) :
    (h &&& 0x249#12).toNat + ((h >>> 1) &&& 0x249#12).toNat + ((h >>> 2) &&& 0x249#12).toNat < 4096 := by
  have hp := cbd3Half12Props_of_bv h
  unfold cbd3Half12Props at hp
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.and_eq_true, decide_eq_true_eq] at hp
  exact hp.1.1.1.1

private theorem mask24_0x249249 :
    ∀ i : Fin 24,
      (0x00249249#24).getLsbD i.val = (0x249#12).getLsbD (i.val % 12) ∧
      (10 ≤ i.val % 12 → (0x00249249#24).getLsbD i.val = false) := by
  decide +kernel

private theorem append2_u12_shr_and_0x249249 (hi lo : BitVec 12) (s : Nat) (hs : s ≤ 2) :
    (((hi ++ lo) >>> s) &&& 0x00249249#24) =
      (((hi >>> s) &&& 0x249#12) ++ ((lo >>> s) &&& 0x249#12)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hlt
  have hm := mask24_0x249249 ⟨i, hlt⟩
  dsimp only at hm
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  by_cases h12 : i < 12
  · have hmod : i % 12 = i := by omega
    rw [hm.1, hmod]
    simp only [h12, ↓reduceIte]
    by_cases hcross : s + i < 12
    · simp [hcross]
    · have h10 : 10 ≤ i % 12 := by omega
      have hmf := hm.2 h10; rw [hm.1, hmod] at hmf
      simp [hmf]
  · have hmod : i % 12 = i - 12 := by omega
    rw [hm.1, hmod]
    simp only [h12, ↓reduceIte]
    have hge : ¬ (s + i < 12) := by omega
    have hidx : s + i - 12 = s + (i - 12) := by omega
    simp [hge, hidx]

theorem cbd3SwarSum24_append2 (hi lo : BitVec 12) :
    cbd3SwarSum24 (hi ++ lo) = cbd3SwarHalf12 hi ++ cbd3SwarHalf12 lo := by
  unfold cbd3SwarSum24
  have h0 := append2_u12_shr_and_0x249249 hi lo 0 (by omega)
  have h1 := append2_u12_shr_and_0x249249 hi lo 1 (by omega)
  have h2 := append2_u12_shr_and_0x249249 hi lo 2 (by omega)
  simp only [BitVec.ushiftRight_zero] at h0
  rw [h0, h1, h2]
  apply BitVec.eq_of_toNat_eq
  have hcl := cbd3_half12_noCarry lo
  have hch := cbd3_half12_noCarry hi
  have hcl2 : (lo &&& 0x249#12).toNat + ((lo >>> 1) &&& 0x249#12).toNat < 4096 := by omega
  have hch2 : (hi &&& 0x249#12).toNat + ((hi >>> 1) &&& 0x249#12).toNat < 4096 := by omega
  simp only [cbd3SwarHalf12, BitVec.toNat_add, toNat_append_eq _ _ (by decide : 2 ^ 12 * 2 ^ 12 = 2 ^ (12 + 12))]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt hcl2, Nat.mod_eq_of_lt hch2, Nat.mod_eq_of_lt hcl, Nat.mod_eq_of_lt hch]
  omega

private theorem shr_half12_and7_eq (hi lo : BitVec 12) (j : Fin 4) (sh : Nat)
    (hsh : sh = 0 ∨ sh = 3) :
    let d : BitVec 32 := (hi ++ lo).zeroExtend 32
    let shalf : BitVec 32 := (if j.val / 2 = 0 then lo else hi).zeroExtend 32
    ((d >>> (6 * j.val + sh)) &&& 7#32) = ((shalf >>> (6 * (j.val % 2) + sh)) &&& 7#32) := by
  dsimp only
  apply BitVec.eq_of_toNat_eq
  have h7 : (7#32 : BitVec 32).toNat = 7 := rfl
  have hll := lo.isLt
  have hhl := hi.isLt
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.zeroExtend, BitVec.toNat_setWidth,
    h7, nat_and_7, toNat_append_eq _ _ (by decide : 2 ^ 12 * 2 ^ 12 = 2 ^ (12 + 12))]
  rcases j with ⟨_ | _ | _ | _ | n, hj⟩ <;> try omega
  all_goals
    rcases hsh with rfl | rfl <;>
    (dsimp only;
     simp only [Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceEqDiff,
       Nat.shiftRight_eq_div_pow, Nat.reducePow, ↓reduceIte];
     rw [Nat.mod_eq_of_lt (by omega : _ < 4294967296),
       Nat.mod_eq_of_lt (by omega : _ < 4294967296)];
     omega)

private theorem cbd3CoeffFromWord24_eq_half12 (hi lo : BitVec 12) (j : Fin 4) :
    cbd3CoeffFromWord24 (hi ++ lo) j =
      cbd3CoeffFromHalf12 (if j.val / 2 = 0 then lo else hi) ⟨j.val % 2, by omega⟩ := by
  unfold cbd3CoeffFromWord24 cbd3CoeffFromHalf12
  rw [cbd3SwarSum24_append2]
  have h0 := shr_half12_and7_eq (cbd3SwarHalf12 hi) (cbd3SwarHalf12 lo) j 0 (Or.inl rfl)
  have h3 := shr_half12_and7_eq (cbd3SwarHalf12 hi) (cbd3SwarHalf12 lo) j 3 (Or.inr rfl)
  simp only [Nat.add_zero] at h0 ⊢
  dsimp only at h0 h3 ⊢
  rw [h0, h3]
  by_cases h : j.val / 2 = 0 <;> simp [h]

theorem swarCbd3Poly16_spec {bs : List (BitVec 8)} (hbs : bs.length = 192) :
    PolyBounded16 3 (swarCbd3Poly16 bs) ∧
    PolyRepresents (swarCbd3Poly16 bs) (samplePolyCbd3 bs) := by
  have hsize : (swarCbd3Poly16 bs).size = 256 := by simp [swarCbd3Poly16]
  suffices hlane : ∀ i < 256,
      let out := (swarCbd3Poly16 bs).getD i 0#16
      (-3 ≤ out.toInt ∧ out.toInt ≤ 3) ∧
      out.toInt % 3329 = (((samplePolyCbd3 bs).getD i 0 : Nat) : Int) % 3329 by
    refine ⟨⟨hsize, fun i hi => (hlane i hi).1⟩, ⟨hsize, fun i hi => (hlane i hi).2⟩⟩
  intro i hi
  dsimp only
  rw [swarCbd3Poly16, getD_ofFn _ _ _ hi, samplePolyCbd3, getD_ofFn _ _ _ hi]
  dsimp only
  let w := i / 4
  let t24 := readU24LE bs w
  let lo12 : BitVec 12 := t24.extractLsb' 0 12
  let hi12 : BitVec 12 := t24.extractLsb' 12 12
  have ht24 : t24 = hi12 ++ lo12 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [hi12, lo12, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', Nat.zero_add]
    by_cases h12 : k < 12
    · simp [h12]
    · simp [h12, show k - 12 < 12 by omega, Nat.add_sub_cancel' (by omega : 12 ≤ k)]
  have hword : cbd3CoeffFromWord24 t24 ⟨i % 4, by omega⟩ =
      cbd3CoeffFromHalf12 (if (i % 4) / 2 = 0 then lo12 else hi12) ⟨i % 2, by omega⟩ := by
    rw [ht24, cbd3CoeffFromWord24_eq_half12]
    apply congrArg (cbd3CoeffFromHalf12 _); ext; simp
  rw [hword]
  let hsel := if (i % 4) / 2 = 0 then lo12 else hi12
  have hp := cbd3Half12Props_of_bv hsel
  unfold cbd3Half12Props at hp
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.and_eq_true, decide_eq_true_eq] at hp
  have hbit : ∀ m : Nat, m < 6 →
      (bytesToBits bs).getD (6 * i + m) 0 = ((hsel.toNat >>> (6 * (i % 2) + m)) &&& 1) := by
    intro m hm
    rw [bytesToBits_getD bs (6 * i + m) (by omega), shr_and1_eq_getLsbD, shr_and1_eq_getLsbD]
    apply congrArg (fun b : Bool => if b then 1 else 0)
    have h1 : (bs.toArray.getD ((6 * i + m) / 8) 0#8).getLsbD ((6 * i + m) % 8) =
        t24.getLsbD (6 * (i % 4) + m) := by
      dsimp only [t24, readU24LE]
      simp only [BitVec.getLsbD_append]
      have hdiv_eq : (6 * i + m) / 8 = 3 * w + (6 * (i % 4) + m) / 8 := by dsimp [w]; omega
      have hmod_eq : (6 * i + m) % 8 = (6 * (i % 4) + m) % 8 := by omega
      rw [hdiv_eq, hmod_eq]
      by_cases h8 : 6 * (i % 4) + m < 8
      · have hd : (6 * (i % 4) + m) / 8 = 0 := by omega
        have hr : (6 * (i % 4) + m) % 8 = 6 * (i % 4) + m := by omega
        simp [h8, hd, hr]
      · by_cases h16 : 6 * (i % 4) + m < 16
        · have hd : (6 * (i % 4) + m) / 8 = 1 := by omega
          have hc : 6 * (i % 4) + m - 8 < 8 := by omega
          have hr : (6 * (i % 4) + m) % 8 = 6 * (i % 4) + m - 8 := by omega
          simp [h8, hd, hc, hr]
        · have hd : (6 * (i % 4) + m) / 8 = 2 := by omega
          have hc : ¬ (6 * (i % 4) + m - 8 < 8) := by omega
          have hr : (6 * (i % 4) + m) % 8 = 6 * (i % 4) + m - 8 - 8 := by omega
          simp [h8, hd, hc, hr]
    rw [h1]
    by_cases hhalf : (i % 4) / 2 = 0
    · have hsel_eq : hsel = lo12 := by simp [hsel, hhalf]
      have hlt12 : 6 * (i % 2) + m < 12 := by omega
      have hpos : 6 * (i % 4) + m = 6 * (i % 2) + m := by omega
      rw [hsel_eq, hpos]; simp [lo12, hlt12]
    · have hsel_eq : hsel = hi12 := by simp [hsel, hhalf]
      have hlt12 : 6 * (i % 2) + m < 12 := by omega
      have hpos : 6 * (i % 4) + m = 12 + (6 * (i % 2) + m) := by omega
      rw [hsel_eq, hpos]; simp [hi12, hlt12]
  have hb0 := hbit 0 (by omega); simp only [Nat.add_zero] at hb0
  rw [hb0, hbit 1 (by omega), hbit 2 (by omega),
    hbit 3 (by omega), hbit 4 (by omega), hbit 5 (by omega)]
  by_cases heven : i % 2 = 0
  · have hf0 : (⟨i % 2, by omega⟩ : Fin 2) = 0 := by ext; exact heven
    rw [hf0]; simp only [heven, Nat.mul_zero, Nat.zero_add]
    exact ⟨hp.1.1.1.2, hp.1.2⟩
  · have hodd : i % 2 = 1 := by omega
    have hf1 : (⟨i % 2, by omega⟩ : Fin 2) = 1 := by ext; exact hodd
    rw [hf1]; simp only [hodd, Nat.mul_one]
    exact ⟨hp.1.1.2, hp.2⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd

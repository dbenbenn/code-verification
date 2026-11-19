/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Kyber1024Delta.Common -- proof-setup: allow-public-import

/-!
# Serialization, Compression & Matrix Transpose (`Kyber1024Delta.CodecAndCompress`)

Bit/byte serialization roundtrips, compression/decompression error decomposition, the sharp `831`
decoding threshold for `Compress_1`, `sampleMatrixWith` transpose symmetry, and `sampleNtt`
canonicality for the Kyber-1024 `δ_kem` correctness proof.
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.Kyber1024Delta.CodecAndCompress

open CryptoGames.MLKEM (
  Poly
  Shake128SeedTerminates
  bitsToBytes
  byteDecodeMod
  byteDecodeRaw
  byteEncode
  compressAndEncode
  compressCoeff
  decodeAndDecompress
  decompressCoeff
  bytesToBits
  mlkemQ
  parseRej12Candidates
  sampleMatrixWith
  sampleNtt
  shake128FirstBlocks
  zeroPoly
)
open Computational.Proofs.Kyber1024Delta.Common (
  IsCanonicalPoly
  centeredZMod
  centeredZMod_cast_eq
  compressErrZMod
  getD_ofFn_nat
  toZPoly
)

/-! ## 1. Internal Bit/List/Array Helpers -/

private theorem toArray_getD_eq {α : Type} (xs : List α) (i : Nat) (d : α) :
    xs.toArray.getD i d = xs.getD i d := by
  unfold Array.getD
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    have hi : i < xs.length := by simpa using h
    change xs.toArray[i]'h = xs[i]?.getD d
    rw [List.getElem_toArray, List.getElem?_eq_getElem hi]
    rfl
  · rename_i h
    have hi : xs.length ≤ i := by simpa using h
    rw [List.getElem?_eq_none hi]
    rfl

private theorem list_getD_map_range {α : Type} (n : Nat) (f : Nat → α) (k : Nat) (d : α)
    (hk : k < n) : ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

private theorem and_one_lt_two (x : Nat) : (x &&& 1) < 2 := by
  rw [Nat.and_one_is_mod]
  omega

private theorem testBit_and_one (x r : Nat) :
    Nat.testBit (x &&& 1) r = (decide (r = 0) && Nat.testBit x 0) := by
  rw [Nat.testBit_and]
  cases r with
  | zero => simp
  | succ r' =>
    have h1 : Nat.testBit 1 (r' + 1) = false := by
      rw [Nat.testBit_succ]
      simp
    rw [h1, Bool.and_false]
    rfl

private theorem testBit_lt_two_shift (x s b : Nat) (hx : x < 2) :
    Nat.testBit (x <<< s) b = (decide (b = s) && Nat.testBit x 0) := by
  have hx1 : x = x &&& 1 := by
    rw [Nat.and_one_is_mod]
    omega
  rw [hx1, Nat.testBit_shiftLeft, testBit_and_one]
  by_cases hbs : s ≤ b
  · by_cases heq : b = s
    · subst heq
      simp
    · have hne : b - s ≠ 0 := by omega
      simp [hbs, heq, hne]
  · have hne : b ≠ s := by omega
    simp [hbs, hne]

private theorem eq_of_lt_two_of_testBit_zero {a b : Nat} (ha : a < 2) (hb : b < 2)
    (h : Nat.testBit a 0 = Nat.testBit b 0) : a = b := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
    simp_all

private theorem testBit_foldl_bits (m : Nat) (bitFn : Nat → Nat) (b : Nat) :
    Nat.testBit ((List.range m).foldl (fun acc k => acc ||| ((bitFn k &&& 1) <<< k)) 0) b =
      if b < m then Nat.testBit (bitFn b) 0 else false := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Nat.testBit_or, ih, Nat.testBit_shiftLeft, testBit_and_one]
    by_cases hbm : b < m
    · have hge : ¬(m ≤ b) := by omega
      have hlt : b < m + 1 := by omega
      simp [hbm, hge, hlt]
    · by_cases heq : b = m
      · subst heq
        simp
      · have hlt : ¬(b < m + 1) := by omega
        have hsub : ¬(b - m = 0) := by omega
        simp [hbm, hlt, hsub]

/-! ## 2. Byte / Bit Codec Roundtrips & Lengths -/

theorem bitsToBytes_length (bits : Array Nat) :
    (bitsToBytes bits).length = bits.size / 8 := by
  simp [bitsToBytes]

theorem byteEncode_length (d : Nat) (f : Poly) :
    (byteEncode d f).length = 32 * d := by
  unfold byteEncode
  rw [bitsToBytes_length, Array.size_ofFn]
  omega

theorem compressAndEncode_length (d : Nat) (f : Poly) :
    (compressAndEncode d f).length = 32 * d := by
  unfold compressAndEncode
  exact byteEncode_length d (f.map (compressCoeff d))

private theorem getLsbD_bitsToBytes {bits : Array Nat}
    (h01 : ∀ i < bits.size, bits.getD i 0 < 2)
    (k r : Nat) (hk : k < bits.size / 8) (hr : r < 8) :
    ((bitsToBytes bits).getD k 0#8).getLsbD r = Nat.testBit (bits.getD (8 * k + r) 0) 0 := by
  unfold bitsToBytes
  rw [list_getD_map_range _ _ k 0#8 hk]
  dsimp only
  rw [BitVec.getLsbD_ofNat]
  simp only [hr, decide_true, Bool.true_and]
  have hlt : ∀ j < 8, bits.getD (8 * k + j) 0 < 2 := fun j hj => h01 (8 * k + j) (by omega)
  simp only [Nat.testBit_or,
    testBit_lt_two_shift _ 0 r (hlt 0 (by omega)),
    testBit_lt_two_shift _ 1 r (hlt 1 (by omega)),
    testBit_lt_two_shift _ 2 r (hlt 2 (by omega)),
    testBit_lt_two_shift _ 3 r (hlt 3 (by omega)),
    testBit_lt_two_shift _ 4 r (hlt 4 (by omega)),
    testBit_lt_two_shift _ 5 r (hlt 5 (by omega)),
    testBit_lt_two_shift _ 6 r (hlt 6 (by omega)),
    testBit_lt_two_shift _ 7 r (hlt 7 (by omega))]
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> try simp
  omega

theorem bytesToBits_bitsToBytes {bits : Array Nat} (hdiv : 8 ∣ bits.size)
    (h01 : ∀ i < bits.size, bits.getD i 0 < 2) :
    bytesToBits (bitsToBytes bits) = bits := by
  have hsize : 8 * (bits.size / 8) = bits.size := Nat.mul_div_cancel' hdiv
  apply Array.ext
  · simp [bytesToBits, bitsToBytes_length, hsize]
  · intro idx hi1 hi2
    have hget_lhs : (bytesToBits (bitsToBytes bits))[idx] =
        (bytesToBits (bitsToBytes bits)).getD idx 0 := by
      simp [Array.getD, hi1]
    have hget_rhs : bits[idx] = bits.getD idx 0 := by simp [Array.getD, hi2]
    rw [hget_lhs, hget_rhs]
    have hidx_len : idx < 8 * (bitsToBytes bits).length := by
      rw [bitsToBytes_length, hsize]
      exact hi2
    unfold bytesToBits
    dsimp only
    rw [getD_ofFn_nat _ idx 0 hidx_len]
    dsimp only
    rw [toArray_getD_eq]
    apply eq_of_lt_two_of_testBit_zero (and_one_lt_two _) (h01 idx hi2)
    simp only [testBit_and_one, decide_true, Bool.true_and, Nat.testBit_shiftRight, Nat.add_zero]
    rw [BitVec.testBit_toNat]
    have hk : idx / 8 < bits.size / 8 := by omega
    have hr : idx % 8 < 8 := by omega
    rw [getLsbD_bitsToBytes h01 (idx / 8) (idx % 8) hk hr]
    have hidx : 8 * (idx / 8) + idx % 8 = idx := Nat.div_add_mod idx 8
    rw [hidx]

theorem bitsToBytes_bytesToBits (bs : List (BitVec 8)) :
    bitsToBytes (bytesToBits bs) = bs := by
  have hbits_sz : (bytesToBits bs).size = 8 * bs.length := by simp [bytesToBits]
  have hbits_01 : ∀ i < (bytesToBits bs).size, (bytesToBits bs).getD i 0 < 2 := by
    intro i hi
    rw [hbits_sz] at hi
    unfold bytesToBits
    rw [getD_ofFn_nat _ i 0 hi]
    exact and_one_lt_two _
  apply List.ext_getElem
  · rw [bitsToBytes_length, hbits_sz]
    omega
  · intro k hk1 hk2
    have hget_lhs : (bitsToBytes (bytesToBits bs))[k] =
        (bitsToBytes (bytesToBits bs)).getD k 0#8 := by
      simp [List.getD_eq_getElem?_getD, hk1]
    rw [hget_lhs]
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    have hk' : k < (bytesToBits bs).size / 8 := by
      rw [hbits_sz]
      omega
    rw [getLsbD_bitsToBytes hbits_01 k r hk' hr]
    have hidx : 8 * k + r < 8 * bs.length := by omega
    unfold bytesToBits
    dsimp only
    rw [getD_ofFn_nat _ (8 * k + r) 0 hidx]
    dsimp only
    rw [toArray_getD_eq]
    have hdiv : (8 * k + r) / 8 = k := by omega
    have hmod : (8 * k + r) % 8 = r := by omega
    have hbs_getD : bs.getD k 0#8 = bs[k] := by simp [List.getD_eq_getElem?_getD, hk2]
    simp only [hdiv, hmod, hbs_getD, testBit_and_one, decide_true, Bool.true_and,
      Nat.testBit_shiftRight, Nat.add_zero]
    exact BitVec.testBit_toNat _

theorem byteDecodeRaw_byteEncode {d : Nat} (hd : 0 < d) (f : Poly)
    (hf : ∀ i < 256, f.getD i 0 < 1 <<< d) :
    byteDecodeRaw d (byteEncode d f) = Array.ofFn (n := 256) fun ⟨i, _⟩ => f.getD i 0 := by
  let encBits : Array Nat := Array.ofFn (n := 256 * d) fun ⟨idx, _⟩ =>
    (f.getD (idx / d) 0 >>> (idx % d)) &&& 1
  have henc_div : 8 ∣ encBits.size := by
    rw [Array.size_ofFn]
    exact ⟨32 * d, by omega⟩
  have henc_01 : ∀ idx < encBits.size, encBits.getD idx 0 < 2 := by
    intro idx hidx
    rw [Array.size_ofFn] at hidx
    rw [getD_ofFn_nat _ idx 0 hidx]
    exact and_one_lt_two _
  have hrt : bytesToBits (byteEncode d f) = encBits :=
    bytesToBits_bitsToBytes henc_div henc_01
  unfold byteDecodeRaw
  dsimp only
  rw [hrt]
  apply Array.ext
  · simp
  · intro i hi1 _hi2
    have hi : i < 256 := by simpa using hi1
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    have hfold_eq :
        (List.range d).foldl (fun acc k => acc ||| (encBits.getD (i * d + k) 0 <<< k)) 0 =
        (List.range d).foldl (fun acc k => acc ||| (((f.getD i 0 >>> k) &&& 1) <<< k)) 0 := by
      have hcongr : ∀ (xs : List Nat) (init : Nat), (∀ k ∈ xs, k < d) →
          xs.foldl (fun acc k => acc ||| (encBits.getD (i * d + k) 0 <<< k)) init =
          xs.foldl (fun acc k => acc ||| (((f.getD i 0 >>> k) &&& 1) <<< k)) init := by
        intro xs
        induction xs with
        | nil => intros; rfl
        | cons x xs ih =>
          intro init hmem
          have hx : x < d := hmem x List.mem_cons_self
          have hidx : i * d + x < 256 * d := by
            have h1 : i * d + x < (i + 1) * d := by rw [Nat.succ_mul]; omega
            have h2 : (i + 1) * d ≤ 256 * d := Nat.mul_le_mul_right d (by omega)
            omega
          have hdiv : (i * d + x) / d = i := by
            rw [Nat.mul_comm i d, Nat.mul_add_div hd, Nat.div_eq_of_lt hx, Nat.add_zero]
          have hmod : (i * d + x) % d = x := by
            rw [Nat.mul_comm i d, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
          have henc_x : encBits.getD (i * d + x) 0 = (f.getD i 0 >>> x) &&& 1 := by
            dsimp only [encBits]
            rw [getD_ofFn_nat _ (i * d + x) 0 hidx, hdiv, hmod]
          simp only [List.foldl_cons, henc_x]
          exact ih _ fun k hk => hmem k (List.mem_cons_of_mem x hk)
      exact hcongr (List.range d) 0 fun k hk => List.mem_range.mp hk
    rw [hfold_eq]
    apply Nat.eq_of_testBit_eq
    intro b
    rw [testBit_foldl_bits d (fun k => f.getD i 0 >>> k) b]
    by_cases hbd : b < d
    · simp [hbd]
    · simp only [hbd, ↓reduceIte]
      have hpow : f.getD i 0 < 2 ^ b := by
        have hlt_d : f.getD i 0 < 2 ^ d := by
          rw [← Nat.one_shiftLeft]
          exact hf i hi
        exact Nat.lt_of_lt_of_le hlt_d (Nat.pow_le_pow_right (by decide) (by omega))
      exact (Nat.testBit_lt_two_pow hpow).symm

theorem byteDecodeMod_12_byteEncode_12 {f : Poly} (hf : IsCanonicalPoly f) :
    byteDecodeMod 12 (byteEncode 12 f) = f := by
  rcases hf with ⟨hsz, hlt⟩
  have hlt12 : ∀ i < 256, f.getD i 0 < 1 <<< 12 := by
    intro i hi
    have hq := hlt i hi
    dsimp only [mlkemQ] at hq
    omega
  unfold byteDecodeMod
  rw [byteDecodeRaw_byteEncode (by decide) f hlt12]
  apply Array.ext
  · simp [hsz]
  · intro i _hi1 hi2
    have hi : i < 256 := by simpa [hsz] using hi2
    have hf_getD : f.getD i 0 = f[i] := by simp [Array.getD, hi2]
    simp only [Array.getElem_map, Array.getElem_ofFn, hf_getD]
    exact Nat.mod_eq_of_lt (hf_getD ▸ hlt i hi)

theorem toZPoly_byteDecodeMod_12_byteEncode_12 {f : Poly}
    (hf : ∀ i < 256, f.getD i 0 < mlkemQ) :
    toZPoly (byteDecodeMod 12 (byteEncode 12 f)) = toZPoly f := by
  have hlt12 : ∀ i < 256, f.getD i 0 < 1 <<< 12 := by
    intro i hi
    have hq := hf i hi
    dsimp only [mlkemQ] at hq
    omega
  unfold byteDecodeMod
  rw [byteDecodeRaw_byteEncode (by decide) f hlt12]
  funext j
  simp [toZPoly, Array.getD, j.isLt]

private theorem byteDecodeRaw_1_getD {m : List (BitVec 8)} (i : Nat) (hi : i < 256) :
    (byteDecodeRaw 1 m).getD i 0 = (bytesToBits m).getD i 0 := by
  unfold byteDecodeRaw
  rw [getD_ofFn_nat _ i 0 hi]
  simp [List.range_one]

theorem byteEncode_1_byteDecodeRaw_1 {m : List (BitVec 8)} (hm : m.length = 32) :
    byteEncode 1 (byteDecodeRaw 1 m) = m := by
  unfold byteEncode
  have hbits_eq :
      (Array.ofFn (n := 256 * 1) fun ⟨idx, _⟩ =>
        ((byteDecodeRaw 1 m).getD (idx / 1) 0 >>> (idx % 1)) &&& 1) =
      bytesToBits m := by
    apply Array.ext
    · simp [bytesToBits, hm]
    · intro idx hi1 hi2
      have hidx : idx < 256 := by simpa using hi1
      rw [Array.getElem_ofFn]
      simp only [Nat.div_one, Nat.mod_one, Nat.shiftRight_zero,
        byteDecodeRaw_1_getD idx hidx]
      have hget_rhs : (bytesToBits m)[idx] = (bytesToBits m).getD idx 0 := by
        simp [Array.getD, hi2]
      rw [hget_rhs]
      have hidx_len : idx < 8 * m.length := by omega
      unfold bytesToBits
      dsimp only
      rw [getD_ofFn_nat _ idx 0 hidx_len]
      dsimp only
      rw [Nat.and_assoc]
      rfl
  rw [hbits_eq]
  exact bitsToBytes_bytesToBits m

theorem byteDecodeRaw_1_lt_two {m : List (BitVec 8)} (hm : m.length = 32)
    (i : Nat) (hi : i < 256) :
    (byteDecodeRaw 1 m).getD i 0 < 2 := by
  rw [byteDecodeRaw_1_getD i hi]
  have hi' : i < 8 * m.length := by omega
  unfold bytesToBits
  rw [getD_ofFn_nat _ i 0 hi']
  exact and_one_lt_two _

/-! ## 3. Compression / Decompression Roundtrip & `Compress_1` Decoding Threshold (`831`) -/

theorem compressCoeff_lt (d x : Nat) (hd : 0 < d) :
    compressCoeff d x < 1 <<< d := by
  let _ := hd
  unfold compressCoeff
  exact Nat.mod_lt _ (by rw [Nat.one_shiftLeft]; exact Nat.two_pow_pos d)

theorem decompressCoeff_lt_mlkemQ {d y : Nat} (hd : 0 < d) (hd12 : d ≤ 12) (hy : y < 1 <<< d) :
    decompressCoeff d y < mlkemQ := by
  unfold decompressCoeff
  have hd0 : (d == 0) = false := beq_false_of_ne (by omega)
  rw [hd0]
  dsimp only [Bool.false_eq_true, ↓reduceIte, mlkemQ]
  let P : Nat := 2 ^ (d - 1)
  have hP_pos : 0 < P := Nat.two_pow_pos (d - 1)
  have hP_le : P ≤ 2048 := by
    have h11 : (2 : Nat) ^ 11 = 2048 := by decide
    rw [← h11]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have h2d : 2 ^ d = 2 * P := by
    have hd_eq : d = (d - 1) + 1 := by omega
    conv_lhs => rw [hd_eq, Nat.pow_succ]
    dsimp only [P]
    omega
  have hsh_d : 1 <<< d = 2 * P := by rw [Nat.one_shiftLeft, h2d]
  have hsh_dm1 : 1 <<< (d - 1) = P := Nat.one_shiftLeft (d - 1)
  rw [hsh_d] at hy
  rw [hsh_dm1, Nat.shiftRight_eq_div_pow, h2d]
  exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)

private theorem compressCoeff_zero (d : Nat) : compressCoeff d 0 = 0 := by
  unfold compressCoeff mlkemQ
  simp

private theorem map_compressCoeff_getD (d : Nat) (f : Poly) (i : Nat) :
    (f.map (compressCoeff d)).getD i 0 = compressCoeff d (f.getD i 0) := by
  by_cases hi : i < f.size
  · simp [Array.getD, hi]
  · simp [Array.getD, hi, compressCoeff_zero]

private theorem compressCoeff_mod_mlkemQ (d x : Nat) :
    compressCoeff d (x % mlkemQ) = compressCoeff d x := by
  unfold compressCoeff
  rw [Nat.mod_mod]

theorem decodeAndDecompress_compressAndEncode {d : Nat} (hd : 0 < d) (hd12 : d ≤ 12) (f : Poly) :
    decodeAndDecompress d (compressAndEncode d f) =
      Array.ofFn (n := 256) fun ⟨i, _⟩ => decompressCoeff d (compressCoeff d (f.getD i 0)) := by
  let _ := hd12
  unfold decodeAndDecompress compressAndEncode
  have hlt : ∀ i < 256, (f.map (compressCoeff d)).getD i 0 < 1 <<< d := by
    intro i _hi
    rw [map_compressCoeff_getD]
    exact compressCoeff_lt d (f.getD i 0) hd
  rw [byteDecodeRaw_byteEncode hd (f.map (compressCoeff d)) hlt]
  apply Array.ext
  · simp
  · intro i _hi1 _hi2
    rw [Array.getElem_map, Array.getElem_ofFn, Array.getElem_ofFn]
    dsimp only
    rw [map_compressCoeff_getD]

theorem toZPoly_decodeAndDecompress_compressAndEncode {d : Nat} (hd : 0 < d) (hd12 : d ≤ 12)
    (f : Poly) (j : Fin 256) :
    toZPoly (decodeAndDecompress d (compressAndEncode d f)) j =
      toZPoly f j + (compressErrZMod d (toZPoly f j) : ZMod mlkemQ) := by
  rw [decodeAndDecompress_compressAndEncode hd hd12 f]
  unfold compressErrZMod
  rw [centeredZMod_cast_eq, add_sub_cancel]
  have hval : (toZPoly f j).val = f.getD j.val 0 % mlkemQ := by
    unfold toZPoly
    exact ZMod.val_natCast mlkemQ (f.getD j.val 0)
  rw [hval, compressCoeff_mod_mlkemQ]
  simp [toZPoly, getD_ofFn_nat _ j.val 0 j.isLt]

theorem compressCoeff_1_of_centered_err {b : Nat} (hb : b < 2) (w : ZMod mlkemQ)
    (herr : |centeredZMod (w - (decompressCoeff 1 b : ZMod mlkemQ))| ≤ 831) :
    compressCoeff 1 w.val = b := by
  have hw : w.val < 3329 := ZMod.val_lt w
  have hsh : ∀ x : Nat, (x <<< 1) = 2 * x := fun x => by
    rw [Nat.shiftLeft_eq]
    omega
  have habs : ∀ z : Int, |z| ≤ 831 ↔ -831 ≤ z ∧ z ≤ 831 := fun z => abs_le
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · have hdec0 : decompressCoeff 1 0 = 0 := by decide
    rw [hdec0, Nat.cast_zero, sub_zero, habs] at herr
    unfold centeredZMod at herr
    dsimp only at herr
    unfold compressCoeff mlkemQ
    rw [Nat.mod_eq_of_lt hw, hsh, show (1 <<< 1) = 2 from rfl]
    split_ifs at herr <;> omega
  · have hdec1 : decompressCoeff 1 1 = 1665 := by decide
    let dNat : Nat := if 1665 ≤ w.val then w.val - 1665 else w.val + 1664
    have hd_lt : dNat < mlkemQ := by
      dsimp only [dNat, mlkemQ]
      split_ifs <;> omega
    have hd_cast : ((dNat : Nat) : ZMod mlkemQ) = w - (1665 : ZMod mlkemQ) := by
      dsimp only [dNat]
      split_ifs with hge
      · rw [Nat.cast_sub hge, ZMod.natCast_zmod_val]
        rfl
      · apply eq_sub_of_add_eq
        have hsum : w.val + 1664 + 1665 = w.val + 3329 := by omega
        have hq : (3329 : ZMod mlkemQ) = 0 := by decide
        calc
          ((w.val + 1664 : Nat) : ZMod mlkemQ) + 1665
              = ((w.val + 1664 + 1665 : Nat) : ZMod mlkemQ) := by norm_cast
          _ = ((w.val + 3329 : Nat) : ZMod mlkemQ) := by rw [hsum]
          _ = (w.val : ZMod mlkemQ) + (3329 : ZMod mlkemQ) := by push_cast; rfl
          _ = w := by rw [hq, add_zero, ZMod.natCast_zmod_val]
    have hd_val : (w - (decompressCoeff 1 1 : ZMod mlkemQ)).val = dNat := by
      rw [hdec1, show ((1665 : Nat) : ZMod mlkemQ) = (1665 : ZMod mlkemQ) from rfl, ← hd_cast]
      exact ZMod.val_cast_of_lt hd_lt
    rw [habs] at herr
    unfold centeredZMod at herr
    dsimp only at herr
    rw [hd_val] at herr
    dsimp only [dNat] at herr
    unfold compressCoeff mlkemQ
    rw [Nat.mod_eq_of_lt hw, hsh, show (1 <<< 1) = 2 from rfl]
    split_ifs at herr <;> omega

private theorem byteEncode_congr_256 {d : Nat} (hd : 0 < d) {f g : Poly}
    (hfg : ∀ i < 256, f.getD i 0 = g.getD i 0) :
    byteEncode d f = byteEncode d g := by
  unfold byteEncode
  dsimp only
  congr 1
  apply Array.ext
  · simp
  · intro idx hi1 _hi2
    have hidx : idx < 256 * d := by simpa using hi1
    have hdiv : idx / d < 256 := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
    rw [Array.getElem_ofFn, Array.getElem_ofFn, hfg (idx / d) hdiv]

theorem compressAndEncode_1_eq_of_noise_le_831 {m : List (BitVec 8)} (hm : m.length = 32)
    (wPoly : Poly)
    (hnoise :
      ∀ j : Fin 256,
        |centeredZMod (toZPoly wPoly j - toZPoly (decodeAndDecompress 1 (m.take 32)) j)| ≤ 831) :
    compressAndEncode 1 wPoly = m := by
  have htake : m.take 32 = m := List.take_of_length_le (by omega)
  unfold compressAndEncode
  rw [byteEncode_congr_256 (by decide : 0 < 1) (g := byteDecodeRaw 1 m)]
  · exact byteEncode_1_byteDecodeRaw_1 hm
  · intro i hi
    rw [map_compressCoeff_getD]
    let j : Fin 256 := ⟨i, hi⟩
    have hj_noise := hnoise j
    rw [htake] at hj_noise
    have hdec_getD :
        toZPoly (decodeAndDecompress 1 m) j =
          (decompressCoeff 1 ((byteDecodeRaw 1 m).getD i 0) : ZMod mlkemQ) := by
      unfold toZPoly decodeAndDecompress
      dsimp only [j]
      have hsz : (byteDecodeRaw 1 m).size = 256 := by simp [byteDecodeRaw]
      simp [Array.getD, hsz, hi]
    rw [hdec_getD] at hj_noise
    have hb : (byteDecodeRaw 1 m).getD i 0 < 2 := byteDecodeRaw_1_lt_two hm i hi
    have hcomp := compressCoeff_1_of_centered_err hb (toZPoly wPoly j) hj_noise
    have hval : (toZPoly wPoly j).val = wPoly.getD i 0 % mlkemQ := by
      unfold toZPoly
      exact ZMod.val_natCast mlkemQ (wPoly.getD i 0)
    rw [hval, compressCoeff_mod_mlkemQ] at hcomp
    exact hcomp

/-! ## 4. `sampleMatrixWith` Transpose & `sampleNtt` Canonicality -/

theorem sampleMatrixWith_transpose (sampler : List (BitVec 8) → Poly) (k : Nat)
    (rho : List (BitVec 8)) (i j : Nat) (hi : i < k) (hj : j < k) :
    ((sampleMatrixWith sampler k rho false).getD i #[]).getD j zeroPoly =
      ((sampleMatrixWith sampler k rho true).getD j #[]).getD i zeroPoly := by
  unfold sampleMatrixWith
  rw [getD_ofFn_nat _ i #[] hi, getD_ofFn_nat _ j zeroPoly hj,
    getD_ofFn_nat _ j #[] hj, getD_ofFn_nat _ i zeroPoly hi]
  rfl

theorem parseRej12Candidates_lt_mlkemQ (bs : List (BitVec 8)) :
    ∀ c ∈ parseRej12Candidates bs, c < mlkemQ := by
  intro c hc
  unfold parseRej12Candidates at hc
  simp only [List.mem_flatten, List.mem_map] at hc
  rcases hc with ⟨l, ⟨t, _ht, rfl⟩, hc⟩
  rw [List.mem_append] at hc
  rcases hc with hc | hc <;> split_ifs at hc <;> simp_all

theorem sampleNtt_isCanonical (seed34 : List (BitVec 8)) :
    IsCanonicalPoly (sampleNtt seed34) := by
  unfold IsCanonicalPoly sampleNtt
  split_ifs with h
  · have hlen :
        256 ≤
          (parseRej12Candidates (shake128FirstBlocks seed34 (Classical.choose h + 3))).length :=
      Classical.choose_spec h
    set cands := parseRej12Candidates (shake128FirstBlocks seed34 (Classical.choose h + 3))
    have htake_len : (cands.take 256).length = 256 := by
      rw [List.length_take]
      omega
    refine ⟨by rw [List.size_toArray, htake_len], fun i hi => ?_⟩
    rw [toArray_getD_eq]
    have hi_len : i < (cands.take 256).length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_len, Option.getD_some]
    have hmem_take : (cands.take 256)[i] ∈ cands.take 256 := List.getElem_mem hi_len
    exact parseRej12Candidates_lt_mlkemQ _ _ (List.mem_of_mem_take hmem_take)
  · refine ⟨by simp [zeroPoly], fun i hi => ?_⟩
    simp [zeroPoly, Array.getD, hi, mlkemQ]

end Computational.Proofs.Kyber1024Delta.CodecAndCompress

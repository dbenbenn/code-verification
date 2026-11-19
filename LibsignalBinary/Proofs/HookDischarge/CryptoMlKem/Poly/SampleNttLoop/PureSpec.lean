/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import

/-!
# Pure `SampleNTT` Step, Chunk, Squeeze, and Slot Invariants (`SampleNttLoop.PureSpec`)

Pure equivalences connecting compiled `sample_from_xof` (`B03`–`B07`) operations to `Spec.MlKem`:
1. 12-bit candidate extraction (`rej12D1W32`, `rej12D2W32`) and `< 3329` / `≤ 3328` bounds;
2. 3-byte triple and 24-byte chunk decomposition of `parseRej12Candidates`;
3. `SHAKE-128` multi-block squeeze decomposition (`shake128FirstBlocks`, `shake128BlockAt`);
4. `sampleNttAt`, `sampleNttBounded`, `sampleNttClassical`, and `*Terminates` lemmas;
5. `272`-halfword (`544`-byte) scratch-slot invariants (`RejSlotRawInv`, `RejSlotClampedInv`)
   and `bytesToPoly16` exit characterization.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec

open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
  (KeccakState Poly Poly16 mlkemQ zeroPoly
   keccakF1600 keccakAbsorb keccakExtractRate keccakSqueezeBlocks keccakPermuteN
   shake128BlockAt parseRej12Candidates shake128FirstBlocks
   Shake128SeedTerminates Shake128MatrixTerminates
   sampleNttBounded sampleNtt bytesToPoly16
   Mlkem768FromSeedTerminates Mlkem768Encaps1Terminates Mlkem768DecapsTerminates
   Kyber1024EncapsTerminates Kyber1024DecapsTerminates)

/-! ## 1. 12-Bit Candidate Extraction (`rej12D1`, `rej12D2`, `rej12D1W32`, `rej12D2W32`) -/

/-- First 12-bit candidate `d₁ = b₀ + 256 · (b₁ mod 16)` from a 3-byte FIPS 203 Alg. 6 triple. -/
@[expose] def rej12D1 (b0 b1 : BitVec 8) : Nat :=
  b0.toNat + 256 * (b1.toNat % 16)

/-- Second 12-bit candidate `d₂ = ⌊b₁ / 16⌋ + 16 · b₂` from a 3-byte FIPS 203 Alg. 6 triple. -/
@[expose] def rej12D2 (b1 b2 : BitVec 8) : Nat :=
  b1.toNat / 16 + 16 * b2.toNat

/-- 32-bit hardware bitfield word produced by `bfi w_b0, w_b1, #8, #4` on zero-extended bytes. -/
@[expose] def rej12D1W32 (b0 b1 : BitVec 8) : BitVec 32 :=
  b0.zeroExtend 32 ||| ((b1.zeroExtend 32 &&& 0xf#32) <<< 8)

/-- 32-bit hardware word produced by `lsr w_t, w_b1, #4; orr w_t, w_t, w_b2, lsl #4`. -/
@[expose] def rej12D2W32 (b1 b2 : BitVec 8) : BitVec 32 :=
  (b1.zeroExtend 32 >>> 4) ||| (b2.zeroExtend 32 <<< 4)

theorem rej12D1_lt_4096 (b0 b1 : BitVec 8) : rej12D1 b0 b1 < 4096 := by
  have h0 : b0.toNat < 256 := b0.isLt
  have h1 : b1.toNat < 256 := b1.isLt
  unfold rej12D1
  omega

theorem rej12D2_lt_4096 (b1 b2 : BitVec 8) : rej12D2 b1 b2 < 4096 := by
  have h1 : b1.toNat < 256 := b1.isLt
  have h2 : b2.toNat < 256 := b2.isLt
  unfold rej12D2
  omega

theorem rej12D1W32_toNat (b0 b1 : BitVec 8) :
    (rej12D1W32 b0 b1).toNat = rej12D1 b0 b1 := by
  unfold rej12D1W32 rej12D1
  have hz0 : (b0.zeroExtend 32).toNat = b0.toNat :=
    BitVec.toNat_setWidth_of_le (by omega)
  have hand : (b1.zeroExtend 32 &&& 0xf#32).toNat = b1.toNat % 16 := by
    rw [BitVec.toNat_and, BitVec.zeroExtend, BitVec.toNat_setWidth_of_le (by omega)]
    exact Nat.and_two_pow_sub_one_eq_mod b1.toNat 4
  have hshl : ((b1.zeroExtend 32 &&& 0xf#32) <<< 8).toNat = (b1.toNat % 16) <<< 8 := by
    rw [BitVec.toNat_shiftLeft, hand]
    simp only [Nat.shiftLeft_eq]
    omega
  rw [BitVec.toNat_or, hz0, hshl, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt b0.isLt (b1.toNat % 16), Nat.shiftLeft_eq]
  omega

theorem rej12D2W32_toNat (b1 b2 : BitVec 8) :
    (rej12D2W32 b1 b2).toNat = rej12D2 b1 b2 := by
  unfold rej12D2W32 rej12D2
  have h1 : b1.toNat < 256 := b1.isLt
  have h2 : b2.toNat < 256 := b2.isLt
  have hshr : (b1.zeroExtend 32 >>> 4).toNat = b1.toNat / 16 := by
    rw [BitVec.toNat_ushiftRight, BitVec.zeroExtend,
      BitVec.toNat_setWidth_of_le (by omega), Nat.shiftRight_eq_div_pow]
  have hshl : (b2.zeroExtend 32 <<< 4).toNat = b2.toNat <<< 4 := by
    rw [BitVec.toNat_shiftLeft, BitVec.zeroExtend,
      BitVec.toNat_setWidth_of_le (by omega)]
    simp only [Nat.shiftLeft_eq]
    omega
  have hlt4 : b1.toNat / 16 < 2 ^ 4 := by omega
  rw [BitVec.toNat_or, hshr, hshl, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt hlt4 b2.toNat, Nat.shiftLeft_eq]
  omega

theorem rej12D1W32_truncate16 (b0 b1 : BitVec 8) :
    (rej12D1W32 b0 b1).truncate 16 = BitVec.ofNat 16 (rej12D1 b0 b1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.toNat_setWidth, rej12D1W32_toNat, BitVec.toNat_ofNat]

theorem rej12D2W32_truncate16 (b1 b2 : BitVec 8) :
    (rej12D2W32 b1 b2).truncate 16 = BitVec.ofNat 16 (rej12D2 b1 b2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.toNat_setWidth, rej12D2W32_toNat, BitVec.toNat_ofNat]

theorem rej12D1W32_ult_3329 (b0 b1 : BitVec 8) :
    (rej12D1W32 b0 b1 < 3329#32) ↔ rej12D1 b0 b1 < mlkemQ := by
  simp [BitVec.lt_def, rej12D1W32_toNat, mlkemQ]

theorem rej12D1W32_ule_3328 (b0 b1 : BitVec 8) :
    (rej12D1W32 b0 b1 ≤ 3328#32) ↔ rej12D1 b0 b1 < mlkemQ := by
  simp [BitVec.le_def, rej12D1W32_toNat, mlkemQ]
  omega

theorem rej12D2W32_ult_3329 (b1 b2 : BitVec 8) :
    (rej12D2W32 b1 b2 < 3329#32) ↔ rej12D2 b1 b2 < mlkemQ := by
  simp [BitVec.lt_def, rej12D2W32_toNat, mlkemQ]

theorem rej12D2W32_ule_3328 (b1 b2 : BitVec 8) :
    (rej12D2W32 b1 b2 ≤ 3328#32) ↔ rej12D2 b1 b2 < mlkemQ := by
  simp [BitVec.le_def, rej12D2W32_toNat, mlkemQ]
  omega

/-! ## 2. 3-Byte Triple & 24-Byte Chunk Decomposition of `parseRej12Candidates` -/

/-- Candidates (`0`, `1`, or `2` values `< 3329`) extracted from a 3-byte triple `(b0, b1, b2)`. -/
@[expose] def parseRej12Triple (b0 b1 b2 : BitVec 8) : List Nat :=
  (if rej12D1 b0 b1 < mlkemQ then [rej12D1 b0 b1] else []) ++
  (if rej12D2 b1 b2 < mlkemQ then [rej12D2 b1 b2] else [])

theorem parseRej12Triple_length_le_2 (b0 b1 b2 : BitVec 8) :
    (parseRej12Triple b0 b1 b2).length ≤ 2 := by
  unfold parseRej12Triple
  split <;> split <;> simp

/-- Candidates (`≤ 16` values `< 3329`) extracted from a 24-byte (`8 × 3`B) `rej_sample` chunk. -/
@[expose] def parseRej12Chunk24 (bs : List (BitVec 8)) : List Nat :=
  parseRej12Triple (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) ++
  parseRej12Triple (bs.getD 3 0#8) (bs.getD 4 0#8) (bs.getD 5 0#8) ++
  parseRej12Triple (bs.getD 6 0#8) (bs.getD 7 0#8) (bs.getD 8 0#8) ++
  parseRej12Triple (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8) ++
  parseRej12Triple (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8) ++
  parseRej12Triple (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) ++
  parseRej12Triple (bs.getD 18 0#8) (bs.getD 19 0#8) (bs.getD 20 0#8) ++
  parseRej12Triple (bs.getD 21 0#8) (bs.getD 22 0#8) (bs.getD 23 0#8)

theorem parseRej12Chunk24_length_le_16 (bs : List (BitVec 8)) :
    (parseRej12Chunk24 bs).length ≤ 16 := by
  unfold parseRej12Chunk24
  have h0 := parseRej12Triple_length_le_2 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8)
  have h1 := parseRej12Triple_length_le_2 (bs.getD 3 0#8) (bs.getD 4 0#8) (bs.getD 5 0#8)
  have h2 := parseRej12Triple_length_le_2 (bs.getD 6 0#8) (bs.getD 7 0#8) (bs.getD 8 0#8)
  have h3 := parseRej12Triple_length_le_2 (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8)
  have h4 := parseRej12Triple_length_le_2 (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8)
  have h5 := parseRej12Triple_length_le_2 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8)
  have h6 := parseRej12Triple_length_le_2 (bs.getD 18 0#8) (bs.getD 19 0#8) (bs.getD 20 0#8)
  have h7 := parseRej12Triple_length_le_2 (bs.getD 21 0#8) (bs.getD 22 0#8) (bs.getD 23 0#8)
  simp only [List.length_append]
  omega

private theorem toArray_getD_eq (bs : List (BitVec 8)) (i : Nat) :
    bs.toArray.getD i 0#8 = bs.getD i 0#8 := by
  simp only [Array.getD, List.size_toArray, List.getD]
  by_cases h : i < bs.length <;> simp [h]

private theorem parseRej12Candidates_eq_range_triples (bs : List (BitVec 8)) :
    parseRej12Candidates bs =
      ((List.range (bs.length / 3)).map fun t =>
        parseRej12Triple (bs.getD (3 * t) 0#8) (bs.getD (3 * t + 1) 0#8)
          (bs.getD (3 * t + 2) 0#8)).flatten := by
  unfold parseRej12Candidates parseRej12Triple rej12D1 rej12D2
  simp [toArray_getD_eq, -Array.getD_eq_getD_getElem?]

@[simp] theorem parseRej12Candidates_nil : parseRej12Candidates [] = [] := by
  simp [parseRej12Candidates_eq_range_triples]

theorem parseRej12Candidates_append {xs ys : List (BitVec 8)} (hx : xs.length % 3 = 0) :
    parseRej12Candidates (xs ++ ys) =
      parseRej12Candidates xs ++ parseRej12Candidates ys := by
  rw [parseRej12Candidates_eq_range_triples, parseRej12Candidates_eq_range_triples,
    parseRej12Candidates_eq_range_triples]
  have hdiv : (xs ++ ys).length / 3 = xs.length / 3 + ys.length / 3 := by
    rw [List.length_append]
    omega
  rw [hdiv, List.range_add, List.map_append, List.flatten_append]
  congr 1
  · apply congrArg List.flatten
    apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    have h0 : 3 * t < xs.length := by omega
    have h1 : 3 * t + 1 < xs.length := by omega
    have h2 : 3 * t + 2 < xs.length := by omega
    simp [List.getD, List.getElem?_append, h0, h1, h2]
  · rw [List.map_map]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro t _ht
    have getD_right : ∀ k, (xs ++ ys).getD (xs.length + k) 0#8 = ys.getD k 0#8 := by
      intro k
      simp [List.getD, List.getElem?_append_right]
    dsimp [Function.comp]
    have e0 : 3 * (xs.length / 3 + t) = xs.length + 3 * t := by omega
    have e1 : xs.length + 3 * t + 1 = xs.length + (3 * t + 1) := by omega
    have e2 : xs.length + 3 * t + 2 = xs.length + (3 * t + 2) := by omega
    rw [e0, e1, e2, getD_right, getD_right, getD_right]

theorem parseRej12Candidates_eq_chunk24 {bs : List (BitVec 8)} (h : bs.length = 24) :
    parseRej12Candidates bs = parseRej12Chunk24 bs := by
  rw [parseRej12Candidates_eq_range_triples, h]
  have hr : List.range (24 / 3) = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  rw [hr]
  simp [parseRej12Chunk24, List.append_assoc]

/-- Decompose `parseRej12Candidates (bs.take (24 * n))` into `n` consecutive 24-byte chunks. -/
theorem parseRej12Candidates_take_chunks (bs : List (BitVec 8)) :
    ∀ n : Nat, 24 * n ≤ bs.length →
      parseRej12Candidates (bs.take (24 * n)) =
        ((List.range n).map fun i => parseRej12Chunk24 ((bs.drop (24 * i)).take 24)).flatten
  | 0, _ => by simp
  | n + 1, hn => by
    have hsplit : bs.take (24 * (n + 1)) = bs.take (24 * n) ++ (bs.drop (24 * n)).take 24 := by
      have hadd : 24 * (n + 1) = 24 * n + 24 := by omega
      rw [hadd, List.take_add]
    have hlen_pre : (bs.take (24 * n)).length = 24 * n := by
      rw [List.length_take]; omega
    have hlen_chk : ((bs.drop (24 * n)).take 24).length = 24 := by
      rw [List.length_take, List.length_drop]; omega
    rw [hsplit, parseRej12Candidates_append (by rw [hlen_pre]; omega),
      parseRej12Candidates_take_chunks bs n (by omega),
      parseRej12Candidates_eq_chunk24 hlen_chk,
      List.range_succ, List.map_append, List.flatten_append]
    simp

/-! ## 3. `SHAKE-128` Squeeze & Block Decomposition (`rate = 168 = 21 × 8`) -/

private theorem keccakExtractRate_21_length (s : KeccakState) :
    (keccakExtractRate 21 s).length = 168 := by
  unfold keccakExtractRate
  have h1 : ∀ l : List (List (BitVec 8)), (∀ x ∈ l, x.length = 8) → l.flatten.length = 8 * l.length := by
    intro l hl
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      have hhd := hl hd List.mem_cons_self
      have htl := ih (fun x hx => hl x (List.mem_cons_of_mem hd hx))
      omega
  rw [h1]
  · simp
  · intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨_, _, rfl⟩
    simp [Spec.unpackLane64]

theorem shake128BlockAt_length (seed34 : List (BitVec 8)) (blkIdx : Nat) :
    (shake128BlockAt seed34 blkIdx).length = 168 := by
  unfold shake128BlockAt
  exact keccakExtractRate_21_length _

theorem keccakPermuteN_succ_right (n : Nat) (s : KeccakState) :
    keccakPermuteN (n + 1) s = keccakF1600 (keccakPermuteN n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [keccakPermuteN]
    exact ih (keccakF1600 s)

theorem keccakSqueezeBlocks_succ (rateLanes : Nat) :
    ∀ (n : Nat) (s : KeccakState),
      keccakSqueezeBlocks rateLanes (n + 1) s =
        keccakSqueezeBlocks rateLanes n s ++ keccakExtractRate rateLanes (keccakPermuteN n s)
  | 0, s => by simp [keccakSqueezeBlocks, keccakPermuteN]
  | 1, s => by simp [keccakSqueezeBlocks, keccakPermuteN]
  | n + 2, s => by
    have ih := keccakSqueezeBlocks_succ rateLanes (n + 1) (keccakF1600 s)
    simp only [keccakSqueezeBlocks] at ih ⊢
    rw [ih, List.append_assoc]
    rfl

@[simp] theorem shake128FirstBlocks_zero (seed34 : List (BitVec 8)) :
    shake128FirstBlocks seed34 0 = [] := rfl

theorem shake128FirstBlocks_succ (seed34 : List (BitVec 8)) (n : Nat) :
    shake128FirstBlocks seed34 (n + 1) =
      shake128FirstBlocks seed34 n ++ shake128BlockAt seed34 n := by
  unfold shake128FirstBlocks shake128BlockAt
  exact keccakSqueezeBlocks_succ 21 n (keccakAbsorb 21 0x1f#8 seed34)

theorem shake128FirstBlocks_length (seed34 : List (BitVec 8)) :
    ∀ n : Nat, (shake128FirstBlocks seed34 n).length = 168 * n
  | 0 => by simp
  | n + 1 => by
    rw [shake128FirstBlocks_succ, List.length_append, shake128FirstBlocks_length seed34 n,
      shake128BlockAt_length]
    omega

theorem shake128FirstBlocks_three (seed34 : List (BitVec 8)) :
    shake128FirstBlocks seed34 3 =
      shake128BlockAt seed34 0 ++ shake128BlockAt seed34 1 ++ shake128BlockAt seed34 2 := by
  rw [shake128FirstBlocks_succ seed34 2, shake128FirstBlocks_succ seed34 1,
    shake128FirstBlocks_succ seed34 0, shake128FirstBlocks_zero]
  simp [List.append_assoc]

theorem parseRej12Candidates_shake128FirstBlocks_succ (seed34 : List (BitVec 8)) (n : Nat) :
    parseRej12Candidates (shake128FirstBlocks seed34 (n + 1)) =
      parseRej12Candidates (shake128FirstBlocks seed34 n) ++
        parseRej12Candidates (shake128BlockAt seed34 n) := by
  rw [shake128FirstBlocks_succ]
  apply parseRej12Candidates_append
  rw [shake128FirstBlocks_length]
  omega

theorem parseRej12Candidates_shake128_prefix {seed34 : List (BitVec 8)} {m n : Nat} (hmn : m ≤ n) :
    ∃ rest : List Nat,
      parseRej12Candidates (shake128FirstBlocks seed34 n) =
        parseRej12Candidates (shake128FirstBlocks seed34 m) ++ rest := by
  induction n with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    exact ⟨[], by simp⟩
  | succ k ih =>
    by_cases hmk : m ≤ k
    · obtain ⟨rest, hrest⟩ := ih hmk
      refine ⟨rest ++ parseRej12Candidates (shake128BlockAt seed34 k), ?_⟩
      rw [parseRej12Candidates_shake128FirstBlocks_succ, hrest, List.append_assoc]
    · have hmeq : m = k + 1 := by omega
      subst hmeq
      exact ⟨[], by simp⟩

theorem parseRej12Candidates_shake128_mono {seed34 : List (BitVec 8)} {m n : Nat} (hmn : m ≤ n) :
    (parseRej12Candidates (shake128FirstBlocks seed34 m)).length ≤
      (parseRej12Candidates (shake128FirstBlocks seed34 n)).length := by
  obtain ⟨rest, hrest⟩ := parseRej12Candidates_shake128_prefix hmn
  rw [hrest, List.length_append]
  omega

/-! ## 4. `sampleNttAt`, `sampleNttBounded`, `sampleNttClassical`, & Termination Unfolding -/

/-- First 256 accepted candidates after `extra + 3` `SHAKE-128` blocks (`extra` extra blocks). -/
@[expose] def sampleNttAt (seed34 : List (BitVec 8)) (extra : Nat) : Poly :=
  ((parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).take 256).toArray

/-- Transparent duplicate of `Spec.sampleNtt` (`rfl`-equal once `Spec.sampleNtt` is `@[expose]`). -/
@[expose] noncomputable def sampleNttClassical (seed34 : List (BitVec 8)) : Poly :=
  by
    classical
    exact
      if h : Shake128SeedTerminates seed34 then
        let extra := Classical.choose h
        ((parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).take 256).toArray
      else
        zeroPoly

theorem shake128SeedTerminates_of_ge256 {seed34 : List (BitVec 8)} {extra : Nat}
    (h : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).length) :
    Shake128SeedTerminates seed34 :=
  ⟨extra, h⟩

theorem extra_lt_of_lt256 {seed34 : List (BitVec 8)} {extra wit : Nat}
    (hlt : (parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).length < 256)
    (hwit : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (wit + 3))).length) :
    extra < wit := by
  by_contra hge
  have hmono := parseRej12Candidates_shake128_mono (seed34 := seed34) (m := wit + 3) (n := extra + 3)
    (by omega)
  omega

theorem sampleNttAt_unique {seed34 : List (BitVec 8)} {e1 e2 : Nat}
    (h1 : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (e1 + 3))).length)
    (h2 : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (e2 + 3))).length) :
    sampleNttAt seed34 e1 = sampleNttAt seed34 e2 := by
  unfold sampleNttAt
  by_cases hle : e1 ≤ e2
  · obtain ⟨rest, hrest⟩ := parseRej12Candidates_shake128_prefix (seed34 := seed34)
      (m := e1 + 3) (n := e2 + 3) (by omega)
    rw [hrest, List.take_append_of_le_length h1]
  · obtain ⟨rest, hrest⟩ := parseRej12Candidates_shake128_prefix (seed34 := seed34)
      (m := e2 + 3) (n := e1 + 3) (by omega)
    rw [hrest, List.take_append_of_le_length h2]

theorem sampleNttClassical_eq_sampleNttAt {seed34 : List (BitVec 8)} {extra : Nat}
    (hge : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).length) :
    sampleNttClassical seed34 = sampleNttAt seed34 extra := by
  have hterm : Shake128SeedTerminates seed34 := ⟨extra, hge⟩
  unfold sampleNttClassical
  simp only [hterm, ↓reduceDIte]
  exact sampleNttAt_unique (Classical.choose_spec hterm) hge

theorem sampler_eq_sampleNttAt {sampler : List (BitVec 8) → Poly}
    (hsampler : ∀ s (h : Shake128SeedTerminates s), sampler s = sampleNttAt s (Classical.choose h))
    {seed34 : List (BitVec 8)} {extra : Nat}
    (hge : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).length) :
    sampler seed34 = sampleNttAt seed34 extra := by
  have hterm : Shake128SeedTerminates seed34 := ⟨extra, hge⟩
  rw [hsampler seed34 hterm]
  exact sampleNttAt_unique (Classical.choose_spec hterm) hge

private theorem sampleNttBounded_loop_eq_some {seed34 : List (BitVec 8)}
    (fuel cur extra : Nat)
    (hle1 : cur ≤ extra)
    (hle2 : extra ≤ cur + fuel)
    (hge : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).length) :
    sampleNttBounded.loop seed34 fuel cur = some (sampleNttAt seed34 extra) := by
  induction fuel generalizing cur with
  | zero =>
    have hce : cur = extra := by omega
    subst hce
    dsimp only [sampleNttBounded.loop]
    simp only [hge, ↓reduceIte]
    rfl
  | succ fuel ih =>
    dsimp only [sampleNttBounded.loop]
    by_cases hcur : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (cur + 3))).length
    · simp only [hcur, ↓reduceIte]
      exact congrArg some (sampleNttAt_unique hcur hge)
    · simp only [hcur, ↓reduceIte]
      have hlt : cur < extra := extra_lt_of_lt256 (Nat.lt_of_not_ge hcur) hge
      exact ih (cur + 1) (by omega) (by omega)

theorem sampleNttBounded_eq_some_of_ge256 {seed34 : List (BitVec 8)} {fuel extra : Nat}
    (hle : extra ≤ fuel)
    (hge : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).length) :
    sampleNttBounded fuel seed34 = some (sampleNttAt seed34 extra) :=
  sampleNttBounded_loop_eq_some fuel 0 extra (by omega) (by omega) hge

/-- Per-pair `(i, j)` projection from `Shake128MatrixTerminates rho k`. -/
theorem Shake128MatrixTerminates_seed {rho : List (BitVec 8)} {k i j : Nat}
    (hmat : Shake128MatrixTerminates rho k) (hi : i < k) (hj : j < k) :
    Shake128SeedTerminates (rho.take 32 ++ [BitVec.ofNat 8 i, BitVec.ofNat 8 j]) :=
  hmat i j hi hj

theorem Shake128MatrixTerminates_seed_len32 {rho : List (BitVec 8)} {k i j : Nat}
    (hmat : Shake128MatrixTerminates rho k) (hlen : rho.length = 32) (hi : i < k) (hj : j < k) :
    Shake128SeedTerminates (rho ++ [BitVec.ofNat 8 i, BitVec.ofNat 8 j]) := by
  have h := hmat i j hi hj
  rwa [List.take_of_length_le (by omega)] at h

theorem Mlkem768FromSeedTerminates_matrix {seed : List.Vector (BitVec 8) 64}
    (h : Mlkem768FromSeedTerminates seed) :
    Shake128MatrixTerminates ((Spec.sha3_512List (seed.toList.take 32 ++ [3#8])).take 32) 3 := h

theorem Mlkem768Encaps1Terminates_matrix {hdr : List (BitVec 8)}
    (h : Mlkem768Encaps1Terminates hdr) (hlen : 64 ≤ hdr.length) :
    Shake128MatrixTerminates (hdr.take 32) 3 := by
  rcases h with hlt | hmat
  · omega
  · exact hmat

theorem Mlkem768DecapsTerminates_matrix {dk : List.Vector (BitVec 8) 2400}
    (h : Mlkem768DecapsTerminates dk) :
    Shake128MatrixTerminates ((dk.toList.drop 2304).take 32) 3 := h

theorem Kyber1024EncapsTerminates_matrix {pk : List (BitVec 8)}
    (h : Kyber1024EncapsTerminates pk) :
    Shake128MatrixTerminates ((pk.drop 1536).take 32) 4 := h

theorem Kyber1024DecapsTerminates_matrix {sk : List (BitVec 8)}
    (h : Kyber1024DecapsTerminates sk) :
    Shake128MatrixTerminates ((sk.drop 3072).take 32) 4 := h

/-! ## 5. Pure `272`-Halfword (`544`-Byte) Scratch Slot Invariants & `bytesToPoly16` Bridge -/

/-- Pack a list of 16-bit halfwords into little-endian bytes (`2 * hws.length` bytes). -/
@[expose] def packHalfwordsLE (hws : List (BitVec 16)) : List (BitVec 8) :=
  (hws.map fun (w : BitVec 16) => [w.truncate 8, (w >>> 8).truncate 8]).flatten

@[simp] theorem packHalfwordsLE_nil : packHalfwordsLE [] = [] := rfl

@[simp] theorem packHalfwordsLE_cons (w : BitVec 16) (ws : List (BitVec 16)) :
    packHalfwordsLE (w :: ws) = [w.truncate 8, (w >>> 8).truncate 8] ++ packHalfwordsLE ws := rfl

theorem packHalfwordsLE_append (xs ys : List (BitVec 16)) :
    packHalfwordsLE (xs ++ ys) = packHalfwordsLE xs ++ packHalfwordsLE ys := by
  simp [packHalfwordsLE, List.map_append, List.flatten_append]

@[simp] theorem packHalfwordsLE_length (hws : List (BitVec 16)) :
    (packHalfwordsLE hws).length = 2 * hws.length := by
  induction hws with
  | nil => simp
  | cons w ws ih => simp [ih]; omega

theorem packHalfwordsLE_take (hws : List (BitVec 16)) (n : Nat) :
    (packHalfwordsLE hws).take (2 * n) = packHalfwordsLE (hws.take n) := by
  induction hws generalizing n with
  | nil => simp
  | cons w ws ih =>
    cases n with
    | zero => simp
    | succ k =>
      have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [h2]
      change (w.truncate 8 :: (w >>> 8).truncate 8 :: packHalfwordsLE ws).take (2 * k + 1 + 1) =
        w.truncate 8 :: (w >>> 8).truncate 8 :: packHalfwordsLE (ws.take k)
      simp only [List.take_succ_cons, ih k]

theorem packHalfwordsLE_replicate_zero (n : Nat) :
    packHalfwordsLE (List.replicate n 0#16) = List.replicate (2 * n) 0#8 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [List.replicate_succ, packHalfwordsLE_cons, ih, h2, List.replicate_succ, List.replicate_succ]
    rfl

theorem getD_packHalfwordsLE_even (hws : List (BitVec 16)) (i : Nat) :
    (packHalfwordsLE hws).getD (2 * i) 0#8 = (hws.getD i 0#16).truncate 8 := by
  induction hws generalizing i with
  | nil => simp [List.getD]
  | cons w ws ih =>
    cases i with
    | zero => simp [List.getD]
    | succ k =>
      have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [h2]
      change (w.truncate 8 :: (w >>> 8).truncate 8 :: packHalfwordsLE ws).getD (2 * k + 1 + 1) 0#8 =
        (ws.getD k 0#16).truncate 8
      simpa only [List.getD, List.getElem?_cons_succ] using ih k

theorem getD_packHalfwordsLE_odd (hws : List (BitVec 16)) (i : Nat) :
    (packHalfwordsLE hws).getD (2 * i + 1) 0#8 = ((hws.getD i 0#16) >>> 8).truncate 8 := by
  induction hws generalizing i with
  | nil => simp [List.getD]
  | cons w ws ih =>
    cases i with
    | zero => simp [List.getD]
    | succ k =>
      have h2 : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
      rw [h2]
      change (w.truncate 8 :: (w >>> 8).truncate 8 :: packHalfwordsLE ws).getD ((2 * k + 1) + 1 + 1) 0#8 =
        ((ws.getD k 0#16) >>> 8).truncate 8
      simpa only [List.getD, List.getElem?_cons_succ] using ih k

private theorem reassemble_u16 (w : BitVec 16) :
    (w.truncate 8).zeroExtend 16 ||| (((w >>> 8).truncate 8).zeroExtend 16 <<< 8) = w := by
  apply BitVec.eq_of_toNat_eq
  have hw : w.toNat < 65536 := w.isLt
  have hlo : ((w.truncate 8).zeroExtend 16).toNat = w.toNat % 256 := by
    simp only [BitVec.truncate, BitVec.zeroExtend,
      BitVec.toNat_setWidth_of_le (by omega : 8 ≤ 16), BitVec.toNat_setWidth]
  have hhi : ((((w >>> 8).truncate 8).zeroExtend 16) <<< 8).toNat = (w.toNat / 256) <<< 8 := by
    simp only [BitVec.toNat_shiftLeft, BitVec.truncate, BitVec.zeroExtend,
      BitVec.toNat_setWidth_of_le (by omega : 8 ≤ 16), BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega
  have hlt8 : w.toNat % 256 < 2 ^ 8 := by omega
  rw [BitVec.toNat_or, hlo, hhi, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt hlt8 (w.toNat / 256), Nat.shiftLeft_eq]
  omega

/-- `bytesToPoly16` on the packed bytes of `256` halfwords recovers `hws.toArray`. -/
theorem bytesToPoly16_packHalfwordsLE {hws : List (BitVec 16)} (hlen : hws.length = 256) :
    bytesToPoly16 (packHalfwordsLE hws) = hws.toArray := by
  unfold bytesToPoly16
  apply Array.ext
  · simp [hlen]
  · intro i hi1 hi2
    simp only [Array.getElem_ofFn, toArray_getD_eq, getD_packHalfwordsLE_even,
      getD_packHalfwordsLE_odd, reassemble_u16]
    simp [List.getD, List.getElem?_eq_getElem (by omega : i < hws.length)]

/-- Sequential halfword writes of accepted candidates starting at index `pos`. -/
@[expose] def rejWriteCandidates (hws : List (BitVec 16)) (pos : Nat) :
    List Nat → List (BitVec 16)
  | [] => hws
  | c :: cs => rejWriteCandidates (hws.set pos (BitVec.ofNat 16 c)) (pos + 1) cs

@[simp] theorem rejWriteCandidates_length (hws : List (BitVec 16)) (pos : Nat) (cs : List Nat) :
    (rejWriteCandidates hws pos cs).length = hws.length := by
  induction cs generalizing hws pos with
  | nil => rfl
  | cons c cs ih => simp [rejWriteCandidates, ih]

private theorem take_set_succ (hws : List (BitVec 16)) (pos : Nat) (v : BitVec 16)
    (hpos : pos < hws.length) :
    (hws.set pos v).take (pos + 1) = hws.take pos ++ [v] := by
  induction hws generalizing pos with
  | nil => simp at hpos
  | cons w ws ih =>
    cases pos with
    | zero => simp
    | succ k =>
      simp only [List.length_cons] at hpos
      simp [List.set, List.take, ih k (by omega)]

theorem rejWriteCandidates_take (hws : List (BitVec 16)) (pos : Nat) (cs : List Nat)
    (hfit : pos + cs.length ≤ hws.length) :
    (rejWriteCandidates hws pos cs).take (pos + cs.length) =
      hws.take pos ++ cs.map (BitVec.ofNat 16) := by
  induction cs generalizing hws pos with
  | nil => simp [rejWriteCandidates]
  | cons c cs ih =>
    simp only [List.length_cons] at hfit
    have hpos : pos < hws.length := by omega
    have hstep := ih (hws.set pos (BitVec.ofNat 16 c)) (pos + 1) (by simp; omega)
    have hadd : pos + 1 + cs.length = pos + (cs.length + 1) := by omega
    rw [hadd] at hstep
    simp only [rejWriteCandidates, List.length_cons, hstep, take_set_succ hws pos _ hpos,
      List.map_cons, List.append_assoc, List.singleton_append]

/-- Pure effect of one 24-byte inner `rej_sample` chunk on `(sampled, hws)`. -/
@[expose] def rejChunkStepPure (sampled : Nat) (hws : List (BitVec 16))
    (chunk24 : List (BitVec 8)) : Nat × List (BitVec 16) :=
  if sampled < 256 then
    let cs := parseRej12Chunk24 chunk24
    (sampled + cs.length, rejWriteCandidates hws sampled cs)
  else
    (sampled, hws)

/-- Pure effect of `n` consecutive 24-byte chunks starting at byte offset `0` of `buf`. -/
@[expose] def rejChunksFoldPure (buf : List (BitVec 8)) (n : Nat)
    (sampled : Nat) (hws : List (BitVec 16)) : Nat × List (BitVec 16) :=
  (List.range n).foldl
    (fun (s, h) i => rejChunkStepPure s h ((buf.drop (24 * i)).take 24))
    (sampled, hws)

/-- Clamping step `if sampled > 255 then 256 else sampled` (`cmp x, #255; csel x, #256, x, hi`). -/
@[expose] def clampSampled (sampled : Nat) : Nat :=
  if 255 < sampled then 256 else sampled

/-- Unclamped `272`-halfword slot invariant (valid throughout `rej_sample`'s inner chunk loop). -/
@[expose] def RejSlotRawInv (cands : List Nat) (sampled : Nat) (hws : List (BitVec 16)) : Prop :=
  hws.length = 272 ∧
  ((sampled < 256 ∧ sampled = cands.length) ∨
   (256 ≤ sampled ∧ sampled ≤ 271 ∧ 256 ≤ cands.length)) ∧
  hws.take (min sampled 256) = (cands.take 256).map (BitVec.ofNat 16)

/-- Clamped `272`-halfword slot invariant (valid at row start and after each clamp pass). -/
@[expose] def RejSlotClampedInv (cands : List Nat) (sampled : Nat)
    (hws : List (BitVec 16)) : Prop :=
  RejSlotRawInv cands sampled hws ∧ sampled = min cands.length 256

theorem rejSlotClampedInv_init :
    RejSlotClampedInv [] 0 (List.replicate 272 0#16) := by
  refine ⟨⟨List.length_replicate, Or.inl ⟨by omega, rfl⟩, ?_⟩, rfl⟩
  simp only [Nat.min_eq_left (by omega : 0 ≤ 256), List.take_zero, List.take_nil, List.map_nil]

theorem RejSlotRawInv.step_cands {cands cs : List Nat} {sampled : Nat} {hws : List (BitVec 16)}
    (hinv : RejSlotRawInv cands sampled hws) (hcs_le : cs.length ≤ 16) :
    let sampled' := if sampled < 256 then sampled + cs.length else sampled
    let hws' := if sampled < 256 then rejWriteCandidates hws sampled cs else hws
    RejSlotRawInv (cands ++ cs) sampled' hws' := by
  rcases hinv with ⟨hlen, hcases, htake⟩
  by_cases hs : sampled < 256
  · simp only [hs, ↓reduceIte]
    rcases hcases with ⟨_, hsc⟩ | ⟨hge, _, _⟩
    · have hfit : sampled + cs.length ≤ hws.length := by omega
      have hwt := rejWriteCandidates_take hws sampled cs hfit
      have hmin_old : min sampled 256 = sampled := by omega
      have htake_old : hws.take sampled = cands.map (BitVec.ofNat 16) := by
        rw [hmin_old] at htake
        have hc_take : cands.take 256 = cands := List.take_of_length_le (by omega)
        rwa [hc_take] at htake
      refine ⟨by rw [rejWriteCandidates_length, hlen], ?_, ?_⟩
      · by_cases hs' : sampled + cs.length < 256
        · exact Or.inl ⟨hs', by rw [List.length_append, ← hsc]⟩
        · exact Or.inr ⟨by omega, by omega, by rw [List.length_append, ← hsc]; omega⟩
      · have hmle : min (sampled + cs.length) 256 ≤ sampled + cs.length := Nat.min_le_left _ _
        have h1 : (rejWriteCandidates hws sampled cs).take (min (sampled + cs.length) 256) =
            ((rejWriteCandidates hws sampled cs).take (sampled + cs.length)).take
              (min (sampled + cs.length) 256) := by
          rw [List.take_take, Nat.min_eq_left hmle]
        rw [h1, hwt, htake_old, ← List.map_append, ← List.map_take]
        congr 1
        have hlen_app : (cands ++ cs).length = sampled + cs.length := by
          rw [List.length_append, ← hsc]
        by_cases h256 : sampled + cs.length ≤ 256
        · rw [Nat.min_eq_left h256, List.take_of_length_le (by omega),
            List.take_of_length_le (by omega)]
        · rw [Nat.min_eq_right (by omega)]
    · omega
  · simp only [hs, ↓reduceIte]
    rcases hcases with ⟨hlt, _⟩ | ⟨hge, hle271, hcge⟩
    · omega
    · refine ⟨hlen, Or.inr ⟨hge, hle271, by rw [List.length_append]; omega⟩, ?_⟩
      rw [htake, List.take_append_of_le_length hcge]

theorem RejSlotRawInv.step_chunk24 {cands : List Nat} {sampled : Nat} {hws : List (BitVec 16)}
    (hinv : RejSlotRawInv cands sampled hws) (chunk24 : List (BitVec 8)) :
    let res := rejChunkStepPure sampled hws chunk24
    RejSlotRawInv (cands ++ parseRej12Chunk24 chunk24) res.1 res.2 := by
  have h := hinv.step_cands (parseRej12Chunk24_length_le_16 chunk24)
  unfold rejChunkStepPure
  by_cases hs : sampled < 256 <;> simpa only [hs, ↓reduceIte] using h

theorem RejSlotRawInv.step_chunks {cands : List Nat} {sampled : Nat} {hws : List (BitVec 16)}
    (hinv : RejSlotRawInv cands sampled hws) (buf : List (BitVec 8)) (n : Nat)
    (hbuf : 24 * n ≤ buf.length) :
    let res := rejChunksFoldPure buf n sampled hws
    RejSlotRawInv (cands ++ parseRej12Candidates (buf.take (24 * n))) res.1 res.2 := by
  induction n generalizing cands sampled hws with
  | zero =>
    simp [rejChunksFoldPure, hinv]
  | succ k ih =>
    unfold rejChunksFoldPure at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hk := ih hinv (by omega)
    have hstep := hk.step_chunk24 ((buf.drop (24 * k)).take 24)
    have hsplit : buf.take (24 * (k + 1)) = buf.take (24 * k) ++ (buf.drop (24 * k)).take 24 := by
      have hadd : 24 * (k + 1) = 24 * k + 24 := by omega
      rw [hadd, List.take_add]
    have hlen_pre : (buf.take (24 * k)).length = 24 * k := by rw [List.length_take]; omega
    have hlen_chk : ((buf.drop (24 * k)).take 24).length = 24 := by
      rw [List.length_take, List.length_drop]; omega
    rw [hsplit, parseRej12Candidates_append (by rw [hlen_pre]; omega),
      parseRej12Candidates_eq_chunk24 hlen_chk, ← List.append_assoc]
    exact hstep

theorem RejSlotRawInv.clamp {cands : List Nat} {sampled : Nat} {hws : List (BitVec 16)}
    (hinv : RejSlotRawInv cands sampled hws) :
    RejSlotClampedInv cands (clampSampled sampled) hws := by
  rcases hinv with ⟨hlen, hcases, htake⟩
  unfold RejSlotClampedInv clampSampled
  rcases hcases with ⟨hlt, hsc⟩ | ⟨hge, _, hcge⟩
  · have hn255 : ¬ (255 < sampled) := by omega
    simp only [hn255, ↓reduceIte]
    refine ⟨⟨hlen, Or.inl ⟨hlt, hsc⟩, htake⟩, ?_⟩
    omega
  · have h255 : 255 < sampled := by omega
    simp only [h255, ↓reduceIte]
    have hmin1 : min sampled 256 = 256 := by omega
    rw [hmin1] at htake
    refine ⟨⟨hlen, Or.inr ⟨by omega, by omega, hcge⟩, by simpa using htake⟩, ?_⟩
    omega

theorem RejSlotClampedInv.sampled_le_256 {cands : List Nat} {sampled : Nat}
    {hws : List (BitVec 16)} (hinv : RejSlotClampedInv cands sampled hws) :
    sampled ≤ 256 := by
  rw [hinv.2]
  exact Nat.min_le_right _ _

theorem RejSlotClampedInv.lt256_iff {cands : List Nat} {sampled : Nat}
    {hws : List (BitVec 16)} (hinv : RejSlotClampedInv cands sampled hws) :
    sampled < 256 ↔ cands.length < 256 := by
  rw [hinv.2]
  omega

theorem RejSlotClampedInv.eq256_iff {cands : List Nat} {sampled : Nat}
    {hws : List (BitVec 16)} (hinv : RejSlotClampedInv cands sampled hws) :
    sampled = 256 ↔ 256 ≤ cands.length := by
  rw [hinv.2]
  omega

/-- When `sampled = 256`, the first `512` bytes of the `544`-byte slot decode via `bytesToPoly16`
    to `(cands.take 256).toArray.map (BitVec.ofNat 16)`. -/
theorem RejSlotClampedInv.bytesToPoly16_take512 {cands : List Nat} {sampled : Nat}
    {hws : List (BitVec 16)} (hinv : RejSlotClampedInv cands sampled hws)
    (hd : sampled = 256) :
    bytesToPoly16 ((packHalfwordsLE hws).take 512) =
      (cands.take 256).toArray.map (BitVec.ofNat 16) := by
  have hcge : 256 ≤ cands.length := (hinv.eq256_iff).mp hd
  rcases hinv.1 with ⟨hlen, _, htake⟩
  rw [hd] at htake
  simp only [Nat.min_self] at htake
  have h512 : (512 : Nat) = 2 * 256 := rfl
  rw [h512, packHalfwordsLE_take,
    bytesToPoly16_packHalfwordsLE (by rw [List.length_take]; omega), htake, List.map_toArray]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec

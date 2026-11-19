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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers

/-!
# NEON Inlined `deserialize_1` and `decompress_1` Soundness (`Poly.Serialize.Decode1`)

Bit-exact equivalence proofs for `deserialize_1` (`dup` + `sshl`/`ushl` `[-7..0]` + `and #1` =
`deserializeChunkCoeff 1`, ignoring bits `8..15` of the source 16-bit lane as in `B07 +0x7d0c`)
and `decompress_1` (`cmeq #0` + `bic 1665` = `Spec.decompressCoeff 1` /
`Spec.decodeAndDecompress 1`), together with the shared `byteDecodeRaw_lt_two_pow` bound.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1

open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  bytesToBits byteDecodeRaw decompressCoeff decodeAndDecompress
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  lane16 dup8x16 fin8_cases ext_lane16 lane16_dup8x16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdSshlElem16 simdSshl8h simdUshlElem16 simdUshl8h simdCmeqZero8h
  lane16_and lane16_not lane16_simdSshl8h lane16_simdUshl8h lane16_simdCmeqZero8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  deserializeChunkCoeff decodeAndDecompress_chunk_eq
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers (
  eq_deserializeChunkCoeff_of_bits
)

private theorem array_getD_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Nat) (d : α)
    (hi : i < n) : (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  unfold Array.getD
  split
  · rename_i h; change (Array.ofFn f)[i]'h = f ⟨i, hi⟩; exact Array.getElem_ofFn h
  · rename_i h; exact False.elim (h (by simp [hi]))

theorem byteDecodeRaw_lt_two_pow (d : Nat) (_hd : d < 16) (bs : List (BitVec 8))
    (idx : Nat) (hidx : idx < 256) :
    (byteDecodeRaw d bs).getD idx 0 < 2 ^ d := by
  unfold byteDecodeRaw
  rw [array_getD_ofFn _ _ _ hidx]; dsimp only
  have hfold : ∀ (xs : List Nat) (init : Nat), init < 2 ^ d → (∀ k ∈ xs, k < d) →
      xs.foldl (fun acc k => acc ||| ((bytesToBits bs).getD (idx * d + k) 0 <<< k)) init < 2 ^ d := by
    intro xs; induction xs with
    | nil => intro init hi _; exact hi
    | cons x xs ih =>
      intro init hi hm
      apply ih
      · dsimp only
        apply Nat.or_lt_two_pow hi
        have hxd : x < d := hm x List.mem_cons_self
        have hbit : (bytesToBits bs).getD (idx * d + x) 0 ≤ 1 := by
          unfold bytesToBits
          by_cases hb : idx * d + x < 8 * bs.length
          · rw [array_getD_ofFn _ _ _ hb]; dsimp only
            rw [Nat.and_one_is_mod]; omega
          · unfold Array.getD; split
            · rename_i h; simp at h; omega
            · omega
        rcases (show (bytesToBits bs).getD (idx * d + x) 0 = 0 ∨
            (bytesToBits bs).getD (idx * d + x) 0 = 1 by omega) with hb0 | hb1
        · rw [hb0, Nat.zero_shiftLeft]; exact Nat.two_pow_pos d
        · rw [hb1, Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by decide) hxd
      · intro k hk; exact hm k (List.mem_cons_of_mem x hk)
  exact hfold (List.range d) 0 (Nat.two_pow_pos d) (fun k hk => List.mem_range.mp hk)

/-! ## `deserialize_1` & `decompress_1` (`B06`, `B07 +0x7d00..+0x7d94`) -/

/-- NEON 1-byte `deserialize_1` (`dup v.8h, w` + `sshl v.8h, v.8h, [-7..0]` + `and #1`). -/
@[expose] def neonDeserialize1_8h (w16 : BitVec 16) : BitVec 128 :=
  simdSshl8h (dup8x16 w16) 0xfff9fffafffbfffcfffdfffeffff0000#128 &&& dup8x16 1#16

/-- Unsigned-shift `ushl` variant of `neonDeserialize1_8h`. -/
@[expose] def neonDeserialize1Ushl_8h (w16 : BitVec 16) : BitVec 128 :=
  simdUshl8h (dup8x16 w16) 0xfff9fffafffbfffcfffdfffeffff0000#128 &&& dup8x16 1#16

/-- NEON `decompress_1` (`cmeq v.8h, raw.8h, #0` + `bic dst.16b, v_1665.16b, v.16b`). -/
@[expose] def neonDecompress1_8h (raw : BitVec 128) : BitVec 128 :=
  dup8x16 1665#16 &&& ~~~simdCmeqZero8h raw

theorem neonDeserialize1Ushl_eq (w16 : BitVec 16) :
    neonDeserialize1Ushl_8h w16 = neonDeserialize1_8h w16 := by
  have hcst : ∀ j : Fin 8,
      ((lane16 0xfff9fffafffbfffcfffdfffeffff0000#128 j).truncate 8).toInt = -(j.val : Int) := by
    intro j; induction j using fin8_cases <;> decide
  have hm1 : ∀ b (hb : b < 16), (1#16)[b]'hb = decide (b = 0) := by
    intro b hb; revert b hb; decide
  apply ext_lane16; intro j
  unfold neonDeserialize1Ushl_8h neonDeserialize1_8h
  rw [lane16_and, lane16_and, lane16_simdUshl8h, lane16_simdSshl8h, lane16_dup8x16, lane16_dup8x16,
    simdUshlElem16, simdSshlElem16, hcst j]
  induction j using fin8_cases <;> {
    ext b hb
    rw [BitVec.getElem_and, BitVec.getElem_and, hm1 b hb]
    rcases b with _ | b <;>
      simp [BitVec.getElem_ushiftRight, BitVec.getElem_sshiftRight]
  }

theorem lane16_neonDeserialize1_8h (w16 : BitVec 16) (j : Fin 8) :
    lane16 (neonDeserialize1_8h w16) j = if (w16.truncate 8).getLsbD j.val then 1#16 else 0#16 := by
  rw [← neonDeserialize1Ushl_eq]
  have hcst : ∀ i : Fin 8,
      ((lane16 0xfff9fffafffbfffcfffdfffeffff0000#128 i).truncate 8).toInt = -(i.val : Int) := by
    intro i; induction i using fin8_cases <;> decide
  have hm1 : ∀ b (hb : b < 16), (1#16)[b]'hb = decide (b = 0) := by
    intro b hb; revert b hb; decide
  unfold neonDeserialize1Ushl_8h
  rw [lane16_and, lane16_simdUshl8h, lane16_dup8x16, lane16_dup8x16]
  have hsh : simdUshlElem16 w16 (lane16 0xfff9fffafffbfffcfffdfffeffff0000#128 j) =
      w16 >>> j.val := by
    induction j using fin8_cases <;> simp [simdUshlElem16, hcst]
  rw [hsh, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth]
  simp only [j.isLt, decide_true, Bool.true_and]
  ext b hb
  rw [BitVec.getElem_and, hm1 b hb]
  rcases b with _ | b
  · simp only [decide_true, Bool.and_true, BitVec.getElem_ushiftRight, Nat.add_zero]
    rw [BitVec.getLsbD_eq_getElem (by omega)]
    cases w16[j.val]
    · simp
    · simp only [↓reduceIte]; exact (hm1 0 hb).symm
  · simp only [show ¬(b + 1 = 0) by omega, decide_false, Bool.and_false]
    cases w16.getLsbD j.val
    · simp
    · simp only [↓reduceIte]; rw [hm1 (b + 1) hb]; simp

theorem lane16_neonDeserialize1_8h_lt (w16 : BitVec 16) (j : Fin 8) :
    (lane16 (neonDeserialize1_8h w16) j).toNat < 2 := by
  rw [lane16_neonDeserialize1_8h]; split <;> decide

theorem lane16_neonDeserialize1_eq_chunk (bs : List (BitVec 8)) (hlen : bs.length = 2)
    (w0 w1 : BitVec 16) (hw0 : w0.truncate 8 = bs.getD 0 0#8)
    (hw1 : w1.truncate 8 = bs.getD 1 0#8) (j : Fin 8) :
    lane16 (neonDeserialize1_8h w0) j = deserializeChunkCoeff 1 bs j.val ∧
    lane16 (neonDeserialize1_8h w1) j = deserializeChunkCoeff 1 bs (8 + j.val) := by
  have hm1 : ∀ b : Fin 16, (1#16).getLsbD b.val = decide (b.val = 0) := by decide +kernel
  constructor
  · rw [lane16_neonDeserialize1_8h, hw0]
    refine eq_deserializeChunkCoeff_of_bits 1 bs hlen j.val (by omega) _ ?_
    intro i hi
    rcases i with _ | i
    · simp only [Nat.mul_one, Nat.add_zero, Nat.lt_one_iff, ↓reduceIte,
        Nat.div_eq_of_lt j.isLt, Nat.mod_eq_of_lt j.isLt]
      cases (bs.getD 0 0#8).getLsbD j.val <;> rfl
    · simp only [show ¬(i + 1 < 1) by omega, ↓reduceIte]
      split
      · exact (hm1 ⟨i + 1, hi⟩).trans (by simp)
      · simp
  · rw [lane16_neonDeserialize1_8h, hw1]
    refine eq_deserializeChunkCoeff_of_bits 1 bs hlen (8 + j.val) (by omega) _ ?_
    intro i hi
    rcases i with _ | i
    · have hdiv : (8 + j.val) / 8 = 1 := by omega
      have hmod : (8 + j.val) % 8 = j.val := by omega
      simp only [Nat.mul_one, Nat.add_zero, Nat.lt_one_iff, ↓reduceIte, hdiv, hmod]
      cases (bs.getD 1 0#8).getLsbD j.val <;> rfl
    · simp only [show ¬(i + 1 < 1) by omega, ↓reduceIte]
      split
      · exact (hm1 ⟨i + 1, hi⟩).trans (by simp)
      · simp

theorem lane16_neonDecompress1_8h (raw : BitVec 128)
    (hraw : ∀ j : Fin 8, (lane16 raw j).toNat < 2) (j : Fin 8) :
    lane16 (neonDecompress1_8h raw) j = BitVec.ofNat 16 (decompressCoeff 1 (lane16 raw j).toNat) := by
  have h1 : ∀ y : Fin 2,
      (1665#16 &&& ~~~(if BitVec.ofNat 16 y.val == 0#16 then 0xffff#16 else 0#16)) =
        BitVec.ofNat 16 (decompressCoeff 1 y.val) := by decide +kernel
  unfold neonDecompress1_8h
  rw [lane16_and, lane16_dup8x16, lane16_not, lane16_simdCmeqZero8h]
  have hy := h1 ⟨(lane16 raw j).toNat, hraw j⟩
  dsimp only at hy
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hy

/-- Full-polynomial chunk bridge for `neonDeserialize1_8h` + `neonDecompress1_8h` (`c < 16`). -/
theorem lane16_neonDecompress1_eq_decodeAndDecompress (fullBs : List (BitVec 8)) (c : Nat)
    (hc : c < 16) (hlen : 2 * (c + 1) ≤ fullBs.length) (w0 w1 : BitVec 16)
    (hw0 : w0.truncate 8 = fullBs.getD (2 * c) 0#8)
    (hw1 : w1.truncate 8 = fullBs.getD (2 * c + 1) 0#8) (j : Fin 8) :
    lane16 (neonDecompress1_8h (neonDeserialize1_8h w0)) j =
      BitVec.ofNat 16 ((decodeAndDecompress 1 fullBs).getD (16 * c + j.val) 0) ∧
    lane16 (neonDecompress1_8h (neonDeserialize1_8h w1)) j =
      BitVec.ofNat 16 ((decodeAndDecompress 1 fullBs).getD (16 * c + (8 + j.val)) 0) := by
  set chunk := (fullBs.drop (2 * c)).take 2
  have hclen : chunk.length = 2 := by simp [chunk]; omega
  have hc0 : chunk.getD 0 0#8 = fullBs.getD (2 * c) 0#8 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by decide), List.getElem?_drop, Nat.add_zero]
  have hc1 : chunk.getD 1 0#8 = fullBs.getD (2 * c + 1) 0#8 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by decide), List.getElem?_drop]
  obtain ⟨h0, h1⟩ := lane16_neonDeserialize1_eq_chunk chunk hclen w0 w1
    (hw0.trans hc0.symm) (hw1.trans hc1.symm) j
  have hcell (idx : Nat) (hidx : idx < 16) :
      decompressCoeff 1 (deserializeChunkCoeff 1 chunk idx).toNat =
        (decodeAndDecompress 1 fullBs).getD (16 * c + idx) 0 := by
    have hlt := byteDecodeRaw_lt_two_pow 1 (by decide) chunk idx (by omega)
    unfold deserializeChunkCoeff
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show chunk = (fullBs.drop (2 * 1 * c)).take (2 * 1) by simp [chunk]]
    exact decodeAndDecompress_chunk_eq 1 fullBs c idx hc hidx (by simpa using hlen)
  rw [lane16_neonDecompress1_8h _ (lane16_neonDeserialize1_8h_lt _),
    lane16_neonDecompress1_8h _ (lane16_neonDeserialize1_8h_lt _),
    h0, h1, hcell j.val (by omega), hcell (8 + j.val) (by omega)]
  exact ⟨rfl, rfl⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1

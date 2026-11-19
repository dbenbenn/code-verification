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

/-!
# Shared Bit-Packing and `Spec.byteEncode` Chunk Helpers (`Poly.Serialize.Common`)

`simdAddv4h` / `simdAddv8h` disjoint-bit OR lemmas, `byteEncodeHalf` / `byteEncodeChunk` bit
characterizations, and full-polynomial slicing and flattening bridges to `Spec.byteEncode`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly bitsToBytes byteEncode compressCoeff compressAndEncode
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16)

/-- AdvSIMD `ADDV Hd, Vn.4H`: sum of the low four 16-bit lanes. -/
@[expose] def simdAddv4h (v : BitVec 128) : BitVec 16 :=
  (lane16 v 0 + lane16 v 1) + (lane16 v 2 + lane16 v 3)

/-- AdvSIMD `ADDV Hd, Vn.8H`: sum of all eight 16-bit lanes. -/
@[expose] def simdAddv8h (v : BitVec 128) : BitVec 16 :=
  ((lane16 v 0 + lane16 v 1) + (lane16 v 2 + lane16 v 3)) +
  ((lane16 v 4 + lane16 v 5) + (lane16 v 6 + lane16 v 7))

theorem add4_eq_or_of_disjoint {a0 a1 a2 a3 : BitVec 16}
    (h01 : a0 &&& a1 = 0#16) (h23 : a2 &&& a3 = 0#16)
    (h0123 : (a0 ||| a1) &&& (a2 ||| a3) = 0#16) :
    (a0 + a1) + (a2 + a3) = (a0 ||| a1) ||| (a2 ||| a3) := by
  rw [BitVec.add_eq_or_of_and_eq_zero a0 a1 h01,
    BitVec.add_eq_or_of_and_eq_zero a2 a3 h23,
    BitVec.add_eq_or_of_and_eq_zero (a0 ||| a1) (a2 ||| a3) h0123]

theorem add8_eq_or_of_disjoint {a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 16}
    (h01 : a0 &&& a1 = 0#16) (h23 : a2 &&& a3 = 0#16)
    (h45 : a4 &&& a5 = 0#16) (h67 : a6 &&& a7 = 0#16)
    (hlo : (a0 ||| a1) &&& (a2 ||| a3) = 0#16)
    (hhi : (a4 ||| a5) &&& (a6 ||| a7) = 0#16)
    (hlh : ((a0 ||| a1) ||| (a2 ||| a3)) &&& ((a4 ||| a5) ||| (a6 ||| a7)) = 0#16) :
    ((a0 + a1) + (a2 + a3)) + ((a4 + a5) + (a6 + a7)) =
      ((a0 ||| a1) ||| (a2 ||| a3)) ||| ((a4 ||| a5) ||| (a6 ||| a7)) := by
  rw [add4_eq_or_of_disjoint h01 h23 hlo,
    add4_eq_or_of_disjoint h45 h67 hhi,
    BitVec.add_eq_or_of_and_eq_zero _ _ hlh]

/-! ## `bitsToBytes` Bit-Level Characterization -/

private theorem array_getD_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Nat) (d : α)
    (hi : i < n) : (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  unfold Array.getD
  split
  · rename_i h
    change (Array.ofFn f)[i]'h = f ⟨i, hi⟩
    exact Array.getElem_ofFn h
  · rename_i h
    exact False.elim (h (by simp [hi]))

private theorem list_getD_map_range {α : Type _} (n : Nat) (f : Nat → α) (k : Nat) (d : α)
    (hk : k < n) : ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

private theorem testBit_and_one_shift (x s b : Nat) :
    Nat.testBit ((x &&& 1) <<< s) b = (decide (b = s) && Nat.testBit x 0) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_and]
  by_cases hbs : s ≤ b
  · by_cases heq : b = s
    · subst heq
      simp
    · have hpos : 0 < b - s := by omega
      rcases hsub : b - s with _ | r
      · omega
      · have h1 : Nat.testBit 1 (r + 1) = false := by rw [Nat.testBit_succ]; simp
        simp [hbs, heq, h1]
  · have hne : b ≠ s := by omega
    simp [hbs, hne]

/-- Exact bit `b < 8` of byte `k < bits.size / 8` of `Spec.bitsToBytes bits` when every entry of
    `bits` is `0`/`1`-masked as `g idx &&& 1`. -/
theorem getElem_bitsToBytes_of_and_one (bits : Array Nat) (g : Nat → Nat)
    (hg : ∀ idx, idx < bits.size → bits.getD idx 0 = g idx &&& 1)
    (k b : Nat) (hk : k < bits.size / 8) (hb : b < 8) :
    ((bitsToBytes bits).getD k 0#8)[b] = Nat.testBit (g (8 * k + b)) 0 := by
  unfold bitsToBytes
  rw [list_getD_map_range _ _ k 0#8 hk]
  dsimp only
  rw [← BitVec.getLsbD_eq_getElem hb, BitVec.getLsbD_ofNat]
  simp only [hb, decide_true, Bool.true_and]
  have h8 : ∀ r, r < 8 → 8 * k + r < bits.size := fun r hr => by omega
  rw [hg _ (h8 0 (by omega)), hg _ (h8 1 (by omega)), hg _ (h8 2 (by omega)),
    hg _ (h8 3 (by omega)), hg _ (h8 4 (by omega)), hg _ (h8 5 (by omega)),
    hg _ (h8 6 (by omega)), hg _ (h8 7 (by omega))]
  simp only [Nat.testBit_or, testBit_and_one_shift]
  rcases b with _ | _ | _ | _ | _ | _ | _ | _ | b <;> try simp
  omega

@[simp] theorem bitsToBytes_length (bits : Array Nat) :
    (bitsToBytes bits).length = bits.size / 8 := by
  simp [bitsToBytes]

/-! ## `byteEncodeHalf` (`8` Lanes → `d` Bytes) and `byteEncodeChunk` (`16` Lanes → `2 * d` Bytes) -/

/-- Encode 8 `d`-bit lanes into `d` little-endian bytes via `Spec.bitsToBytes`. -/
@[expose] def byteEncodeHalf (d : Nat) (lanes : Fin 8 → BitVec 16) : List (BitVec 8) :=
  bitsToBytes (Array.ofFn (n := 8 * d) fun ⟨idx, hidx⟩ =>
    let j : Fin 8 := ⟨idx / d, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩
    ((lanes j).toNat >>> (idx % d)) &&& 1)

/-- Encode 16 `d`-bit coefficients (`coeffs 0 .. coeffs 15`) into `2 * d` bytes via `Spec.bitsToBytes`. -/
@[expose] def byteEncodeChunk (d : Nat) (coeffs : Nat → BitVec 16) : List (BitVec 8) :=
  bitsToBytes (Array.ofFn (n := 16 * d) fun ⟨idx, _⟩ =>
    ((coeffs (idx / d)).toNat >>> (idx % d)) &&& 1)

/-- Encode two 8-lane NEON vectors `(v0, v1)` (`16` lanes total) into `2 * d` bytes. -/
@[expose] def byteEncodeChunkVec (d : Nat) (v0 v1 : BitVec 128) : List (BitVec 8) :=
  byteEncodeChunk d fun j =>
    if h : j < 8 then lane16 v0 ⟨j, h⟩
    else if h2 : j - 8 < 8 then lane16 v1 ⟨j - 8, h2⟩
    else 0#16

@[simp] theorem byteEncodeHalf_length (d : Nat) (lanes : Fin 8 → BitVec 16) :
    (byteEncodeHalf d lanes).length = d := by
  simp [byteEncodeHalf]

@[simp] theorem byteEncodeChunk_length (d : Nat) (coeffs : Nat → BitVec 16) :
    (byteEncodeChunk d coeffs).length = 2 * d := by
  unfold byteEncodeChunk
  rw [bitsToBytes_length, Array.size_ofFn]
  omega

@[simp] theorem byteEncodeChunkVec_length (d : Nat) (v0 v1 : BitVec 128) :
    (byteEncodeChunkVec d v0 v1).length = 2 * d := by
  simp [byteEncodeChunkVec]

/-- Closed-form bit `b < 8` of byte `k < d` of `byteEncodeHalf d lanes`. -/
theorem getElem_byteEncodeHalf (d : Nat) (lanes : Fin 8 → BitVec 16)
    (k b : Nat) (hk : k < d) (hb : b < 8) :
    ((byteEncodeHalf d lanes).getD k 0#8)[b] =
      (lanes ⟨(8 * k + b) / d, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩).getLsbD
        ((8 * k + b) % d) := by
  unfold byteEncodeHalf
  have hk' : k < (Array.ofFn (n := 8 * d) fun ⟨idx, hidx⟩ =>
      let j : Fin 8 := ⟨idx / d, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩
      ((lanes j).toNat >>> (idx % d)) &&& 1).size / 8 := by
    rw [Array.size_ofFn]; omega
  rw [getElem_bitsToBytes_of_and_one _
    (fun idx =>
      if h : idx < 8 * d then
        (lanes ⟨idx / d, (Nat.div_lt_iff_lt_mul (by omega)).mpr h⟩).toNat >>> (idx % d)
      else 0)
    (fun idx hidx => by
      rw [Array.size_ofFn] at hidx
      rw [array_getD_ofFn _ _ _ hidx]
      simp [hidx])
    k b hk' hb]
  have hlt : 8 * k + b < 8 * d := by omega
  simp only [hlt, ↓reduceDIte, Nat.testBit_shiftRight, Nat.add_zero]
  exact BitVec.testBit_toNat _

/-- Bitwise extensionality criterion for proving `bs = byteEncodeHalf d lanes`. -/
theorem eq_byteEncodeHalf_of_bits {d : Nat} {bs : List (BitVec 8)} {lanes : Fin 8 → BitVec 16}
    (hlen : bs.length = d)
    (hbits : ∀ (k b : Nat) (hk : k < d) (hb : b < 8),
      (bs.getD k 0#8)[b] =
        (lanes ⟨(8 * k + b) / d,
          (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩).getLsbD ((8 * k + b) % d)) :
    bs = byteEncodeHalf d lanes := by
  apply ByteSlice.ext_getD
  · simp [hlen]
  · intro k hk
    rw [hlen] at hk
    ext b hb
    rw [hbits k b hk hb, getElem_byteEncodeHalf d lanes k b hk hb]

/-- Closed-form bit `b < 8` of byte `k < 2 * d` of `byteEncodeChunk d coeffs`. -/
theorem getElem_byteEncodeChunk (d : Nat) (coeffs : Nat → BitVec 16)
    (k b : Nat) (hk : k < 2 * d) (hb : b < 8) :
    ((byteEncodeChunk d coeffs).getD k 0#8)[b] =
      (coeffs ((8 * k + b) / d)).getLsbD ((8 * k + b) % d) := by
  unfold byteEncodeChunk
  have hk' : k < (Array.ofFn (n := 16 * d) fun ⟨idx, _⟩ =>
      ((coeffs (idx / d)).toNat >>> (idx % d)) &&& 1).size / 8 := by
    rw [Array.size_ofFn]; omega
  rw [getElem_bitsToBytes_of_and_one _
    (fun idx => (coeffs (idx / d)).toNat >>> (idx % d))
    (fun idx hidx => by
      rw [Array.size_ofFn] at hidx
      exact array_getD_ofFn _ _ _ hidx)
    k b hk' hb]
  rw [Nat.testBit_shiftRight, Nat.add_zero]
  exact BitVec.testBit_toNat _

/-- Every 16-lane `byteEncodeChunk` splits into the concatenation of its two 8-lane halves. -/
theorem byteEncodeChunk_eq_append_half (d : Nat) (coeffs : Nat → BitVec 16) :
    byteEncodeChunk d coeffs =
      byteEncodeHalf d (fun j => coeffs j.val) ++
      byteEncodeHalf d (fun j => coeffs (8 + j.val)) := by
  apply ByteSlice.ext_getD
  · simp [Nat.two_mul]
  · intro k hk
    rw [byteEncodeChunk_length] at hk
    ext b hb
    rw [getElem_byteEncodeChunk d coeffs k b hk hb]
    by_cases hkd : k < d
    · have happ : (byteEncodeHalf d (fun j => coeffs j.val) ++
          byteEncodeHalf d (fun j => coeffs (8 + j.val))).getD k 0#8 =
          (byteEncodeHalf d (fun j => coeffs j.val)).getD k 0#8 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simp [hkd])]
      rw [happ, getElem_byteEncodeHalf d _ k b hkd hb]
    · have hk2 : k - d < d := by omega
      have happ : (byteEncodeHalf d (fun j => coeffs j.val) ++
          byteEncodeHalf d (fun j => coeffs (8 + j.val))).getD k 0#8 =
          (byteEncodeHalf d (fun j => coeffs (8 + j.val))).getD (k - d) 0#8 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simp; omega)]
        simp [byteEncodeHalf_length]
      rw [happ, getElem_byteEncodeHalf d _ (k - d) b hk2 hb]
      have hidx : 8 * k + b = d * 8 + (8 * (k - d) + b) := by
        have hsub : k = d + (k - d) := by omega
        calc 8 * k + b = 8 * (d + (k - d)) + b := by rw [← hsub]
          _ = d * 8 + (8 * (k - d) + b) := by rw [Nat.mul_add, Nat.mul_comm 8 d, Nat.add_assoc]
      have hd_pos : 0 < d := by omega
      have hdiv : (8 * k + b) / d = 8 + (8 * (k - d) + b) / d := by
        rw [hidx, Nat.mul_add_div hd_pos]
      have hmod : (8 * k + b) % d = (8 * (k - d) + b) % d := by
        rw [hidx, Nat.mul_add_mod]
      rw [hdiv, hmod]

theorem byteEncodeChunkVec_eq_append_half (d : Nat) (v0 v1 : BitVec 128) :
    byteEncodeChunkVec d v0 v1 =
      byteEncodeHalf d (lane16 v0) ++ byteEncodeHalf d (lane16 v1) := by
  unfold byteEncodeChunkVec
  rw [byteEncodeChunk_eq_append_half]
  congr 1
  · congr 1; funext j; simp [j.isLt]
  · congr 1; funext j
    have hlt : ¬(8 + j.val < 8) := by omega
    simp [hlt, j.isLt]

/-! ## Slicing and Flattening Bridges to `Spec.byteEncode` and `Spec.compressAndEncode` -/

@[simp] theorem byteEncode_length (d : Nat) (poly : Poly) :
    (byteEncode d poly).length = 32 * d := by
  unfold byteEncode
  rw [bitsToBytes_length, Array.size_ofFn]
  omega

private theorem getElem_byteEncode (d : Nat) (poly : Poly) (k b : Nat)
    (hk : k < 32 * d) (hb : b < 8) :
    ((byteEncode d poly).getD k 0#8)[b] =
      Nat.testBit (poly.getD ((8 * k + b) / d) 0) ((8 * k + b) % d) := by
  unfold byteEncode
  have hk' : k < (Array.ofFn (n := 256 * d) fun ⟨idx, _⟩ =>
      (poly.getD (idx / d) 0 >>> (idx % d)) &&& 1).size / 8 := by
    rw [Array.size_ofFn]; omega
  rw [getElem_bitsToBytes_of_and_one _
    (fun idx => poly.getD (idx / d) 0 >>> (idx % d))
    (fun idx hidx => by
      rw [Array.size_ofFn] at hidx
      exact array_getD_ofFn _ _ _ hidx)
    k b hk' hb]
  rw [Nat.testBit_shiftRight, Nat.add_zero]

/-- Slice `[d * v .. d * (v + 1))` (`v < 32`) of `Spec.byteEncode d poly` (`d ≤ 16`) equals
    `byteEncodeHalf d` on the `v`-th 8-coefficient group. -/
theorem byteEncode_half_slice_eq (d : Nat) (hd16 : d ≤ 16) (poly : Poly) (v : Nat) (hv : v < 32) :
    ((byteEncode d poly).drop (d * v)).take d =
      byteEncodeHalf d (fun j => BitVec.ofNat 16 (poly.getD (8 * v + j.val) 0)) := by
  have hle : d * v + d ≤ 32 * d := by
    calc d * v + d = d * (v + 1) := (Nat.mul_succ d v).symm
      _ = (v + 1) * d := Nat.mul_comm _ _
      _ ≤ 32 * d := Nat.mul_le_mul_right d (by omega)
  have hlen_lhs : (((byteEncode d poly).drop (d * v)).take d).length = d := by
    rw [List.length_take, List.length_drop, byteEncode_length]; omega
  apply ByteSlice.ext_getD
  · rw [hlen_lhs, byteEncodeHalf_length]
  · intro k hk
    rw [hlen_lhs] at hk
    have hget : (((byteEncode d poly).drop (d * v)).take d).getD k 0#8 =
        (byteEncode d poly).getD (d * v + k) 0#8 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt hk, List.getElem?_drop]
    have hdvk : d * v + k < 32 * d := by have : d * v + k < d * (v + 1) := by rw [Nat.mul_succ]; omega
                                         omega
    ext b hb
    rw [hget, getElem_byteEncode d poly (d * v + k) b hdvk hb,
      getElem_byteEncodeHalf d _ k b hk hb, BitVec.getLsbD_ofNat]
    have hd_pos : 0 < d := by omega
    have hidx : 8 * (d * v + k) + b = d * (8 * v) + (8 * k + b) := by
      calc 8 * (d * v + k) + b = 8 * (d * v) + 8 * k + b := by rw [Nat.mul_add]
        _ = d * (8 * v) + (8 * k + b) := by
          rw [← Nat.mul_assoc 8 d v, Nat.mul_comm 8 d, Nat.mul_assoc d 8 v, Nat.add_assoc]
    have hdiv : (8 * (d * v + k) + b) / d = 8 * v + (8 * k + b) / d := by
      rw [hidx, Nat.mul_add_div hd_pos]
    have hmod : (8 * (d * v + k) + b) % d = (8 * k + b) % d := by rw [hidx, Nat.mul_add_mod]
    have hlt16 : (8 * k + b) % d < 16 := Nat.lt_of_lt_of_le (Nat.mod_lt _ hd_pos) hd16
    simp [hdiv, hmod, hlt16]

/-- Slice `[2 * d * c .. 2 * d * (c + 1))` (`c < 16`) of `Spec.byteEncode d poly` (`d ≤ 16`) equals
    `byteEncodeChunk d` on the `c`-th 16-coefficient chunk. -/
theorem byteEncode_chunk_slice_eq (d : Nat) (hd16 : d ≤ 16) (poly : Poly) (c : Nat) (hc : c < 16) :
    ((byteEncode d poly).drop (2 * d * c)).take (2 * d) =
      byteEncodeChunk d (fun j => BitVec.ofNat 16 (poly.getD (16 * c + j) 0)) := by
  have h2d : 2 * d = d + d := Nat.two_mul d
  have hmul1 : 2 * d * c = d * (2 * c) := by
    calc 2 * d * c = d * 2 * c := by rw [Nat.mul_comm 2 d]
      _ = d * (2 * c) := by rw [Nat.mul_assoc]
  rw [hmul1, h2d, List.take_add, List.drop_drop,
    show d * (2 * c) + d = d * (2 * c + 1) by rw [Nat.mul_succ],
    byteEncode_half_slice_eq d hd16 poly (2 * c) (by omega),
    byteEncode_half_slice_eq d hd16 poly (2 * c + 1) (by omega),
    byteEncodeChunk_eq_append_half]
  congr 1
  · congr 1; funext j
    have h1 : 8 * (2 * c) + j.val = 16 * c + j.val := by omega
    rw [h1]
  · congr 1; funext j
    have h2 : 8 * (2 * c + 1) + j.val = 16 * c + (8 + j.val) := by omega
    rw [h2]

private theorem flatten_slices_eq_take {α : Type _} (xs : List α) (step : Nat) :
    ∀ m : Nat, ((List.range m).map fun c => (xs.drop (step * c)).take step).flatten =
      xs.take (step * m)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, flatten_slices_eq_take xs step m]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [Nat.mul_succ, List.take_add]

/-- Full-polynomial decomposition of `Spec.byteEncode d poly` into 32 `byteEncodeHalf` slices. -/
theorem byteEncode_eq_flatten_halves (d : Nat) (hd16 : d ≤ 16) (poly : Poly) :
    byteEncode d poly =
      ((List.range 32).map fun v =>
        byteEncodeHalf d (fun j => BitVec.ofNat 16 (poly.getD (8 * v + j.val) 0))).flatten := by
  have hcongr :
      ((List.range 32).map fun v =>
        byteEncodeHalf d (fun j => BitVec.ofNat 16 (poly.getD (8 * v + j.val) 0))) =
      ((List.range 32).map fun v => ((byteEncode d poly).drop (d * v)).take d) := by
    apply List.map_congr_left
    intro v hv
    exact (byteEncode_half_slice_eq d hd16 poly v (List.mem_range.mp hv)).symm
  rw [hcongr, flatten_slices_eq_take, List.take_of_length_le (by simp [Nat.mul_comm d 32])]

/-- Full-polynomial decomposition of `Spec.byteEncode d poly` into 16 `byteEncodeChunk` slices. -/
theorem byteEncode_eq_flatten_chunks (d : Nat) (hd16 : d ≤ 16) (poly : Poly) :
    byteEncode d poly =
      ((List.range 16).map fun c =>
        byteEncodeChunk d (fun j => BitVec.ofNat 16 (poly.getD (16 * c + j) 0))).flatten := by
  have hcongr :
      ((List.range 16).map fun c =>
        byteEncodeChunk d (fun j => BitVec.ofNat 16 (poly.getD (16 * c + j) 0))) =
      ((List.range 16).map fun c => ((byteEncode d poly).drop (2 * d * c)).take (2 * d)) := by
    apply List.map_congr_left
    intro c hc
    exact (byteEncode_chunk_slice_eq d hd16 poly c (List.mem_range.mp hc)).symm
  have hlen : (byteEncode d poly).length ≤ 2 * d * 16 := by
    rw [byteEncode_length]; omega
  rw [hcongr, flatten_slices_eq_take, List.take_of_length_le hlen]

/-- Full-polynomial decomposition of `Spec.compressAndEncode d poly` into 16 `byteEncodeChunk` slices. -/
theorem compressAndEncode_eq_flatten_chunks (d : Nat) (hd16 : d ≤ 16) (poly : Poly) :
    compressAndEncode d poly =
      ((List.range 16).map fun c =>
        byteEncodeChunk d (fun j =>
          BitVec.ofNat 16 ((poly.map (compressCoeff d)).getD (16 * c + j) 0))).flatten :=
  byteEncode_eq_flatten_chunks d hd16 (poly.map (compressCoeff d))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common

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
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1

/-!
# NEON Inlined `deserialize_10` and `decompress_10` Soundness (`Poly.Serialize.Decode10`)

Equivalence proofs for `deserialize_10` (`B04 +0x05bc..+0x06c4` scalar `bfi`/`lsr`/`orr` unpacking
into 8H lanes = `deserializeChunkCoeff 10` / `Spec.byteDecodeRaw 10`) and fused `decompress_10`
(`B04 +0x06c8..+0x0710` `xtn` + `shrn #16` + `umlal 512, ·, 3329` + `ushr #10` + `trn1.8h` =
`Spec.decompressCoeff 10` / `Spec.decodeAndDecompress 10`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode10

open Arm64
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  mlkemQ decompressCoeff decodeAndDecompress
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  lane16 lane32 pack8x16 pack4x32 dup8x16
  lane16_pack8x16 lane32_pack4x32 lane16_dup8x16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdTrn1_8h lane16_simdTrn1_8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  deserializeChunkCoeff decodeAndDecompress_chunk_eq
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers (
  eq_deserializeChunkCoeff_of_bits getLsbD_8_of_ge
  getLsbD_evalBitfield_w32_ubfm getLsbD_evalBitfield_w32_bfm_lt
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (
  byteDecodeRaw_lt_two_pow
)

/-! ## `deserialize_10` & `decompress_10` (`B04 +0x05bc..+0x0718`) -/

/-- Pure 8-lane NEON `deserialize_10` half-chunk (`10` bytes → `8` 10-bit lanes). -/
@[expose] def neonDeserialize10Half (bs : List (BitVec 8)) (off : Nat) : BitVec 128 :=
  pack8x16 fun j =>
    let g := off + 5 * (j.val / 4)
    match j.val % 4 with
    | 0 => (bs.getD g 0#8).zeroExtend 16 |||
           (((bs.getD (g + 1) 0#8 &&& 0x03#8).zeroExtend 16) <<< 8)
    | 1 => ((bs.getD (g + 1) 0#8 >>> 2).zeroExtend 16) |||
           (((bs.getD (g + 2) 0#8 &&& 0x0f#8).zeroExtend 16) <<< 6)
    | 2 => ((bs.getD (g + 2) 0#8 >>> 4).zeroExtend 16) |||
           (((bs.getD (g + 3) 0#8 &&& 0x3f#8).zeroExtend 16) <<< 4)
    | _ => ((bs.getD (g + 3) 0#8 >>> 6).zeroExtend 16) |||
           (((bs.getD (g + 4) 0#8).zeroExtend 16) <<< 2)

/-- `B04` scalar `bfi`/`lsr`/`orr` instruction equivalences for the 4 lanes of a 5-byte group. -/
theorem deserialize10_scalar_lanes_eq (b0 b1 b2 b3 b4 : BitVec 8) :
    (evalBitfield .W32 .BFM (b0.zeroExtend 64) (b1.zeroExtend 64) 24 1).truncate 16 =
      (b0.zeroExtend 16 ||| (((b1 &&& 0x03#8).zeroExtend 16) <<< 8)) ∧
    (evalBitfield .W32 .BFM (evalBitfield .W32 .UBFM (b1.zeroExtend 64) (b1.zeroExtend 64) 2 31)
        (b2.zeroExtend 64) 26 3).truncate 16 =
      ((b1 >>> 2).zeroExtend 16 ||| (((b2 &&& 0x0f#8).zeroExtend 16) <<< 6)) ∧
    (evalBitfield .W32 .BFM (evalBitfield .W32 .UBFM (b2.zeroExtend 64) (b2.zeroExtend 64) 4 31)
        (b3.zeroExtend 64) 28 5).truncate 16 =
      ((b2 >>> 4).zeroExtend 16 ||| (((b3 &&& 0x3f#8).zeroExtend 16) <<< 4)) ∧
    (evalBitfield .W32 .UBFM (b3.zeroExtend 64) (b3.zeroExtend 64) 6 31 |||
        ((b4.zeroExtend 64) <<< 2)).truncate 16 =
      ((b3 >>> 6).zeroExtend 16 ||| ((b4.zeroExtend 16) <<< 2)) := by
  have hm3 (r : Nat) (hr : decide (r < 8) = true := by decide) :
      (0x03#8).getLsbD r = decide (r < 2) := by
    have := of_decide_eq_true hr
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> first | decide | omega
  have hm15 (r : Nat) (hr : decide (r < 8) = true := by decide) :
      (0x0f#8).getLsbD r = decide (r < 4) := by
    have := of_decide_eq_true hr
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> first | decide | omega
  have hm63 (r : Nat) (hr : decide (r < 8) = true := by decide) :
      (0x3f#8).getLsbD r = decide (r < 6) := by
    have := of_decide_eq_true hr
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> first | decide | omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
    all_goals {
      rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
        getLsbD_evalBitfield_w32_bfm_lt _ _ 24 1 _ (by decide)]
      try simp only [BitVec.zeroExtend]
      try simp only [BitVec.getLsbD_or]
      try simp only [BitVec.getLsbD_shiftLeft]
      try simp only [BitVec.getLsbD_and]
      try simp only [BitVec.getLsbD_setWidth]
      try dsimp only
      try simp only [hm3]
      try simp only [getLsbD_8_of_ge]
      simp
    }
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
    all_goals {
      rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
        getLsbD_evalBitfield_w32_bfm_lt _ _ 26 3 _ (by decide)]
      try rw [getLsbD_evalBitfield_w32_ubfm _ _ 2 31 _ (by decide)]
      try simp only [BitVec.zeroExtend]
      try simp only [BitVec.getLsbD_or]
      try simp only [BitVec.getLsbD_shiftLeft]
      try simp only [BitVec.getLsbD_ushiftRight]
      try simp only [BitVec.getLsbD_and]
      try simp only [BitVec.getLsbD_setWidth]
      try dsimp only
      try simp only [hm15]
      try simp only [getLsbD_8_of_ge]
      simp
    }
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
    all_goals {
      rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
        getLsbD_evalBitfield_w32_bfm_lt _ _ 28 5 _ (by decide)]
      try rw [getLsbD_evalBitfield_w32_ubfm _ _ 4 31 _ (by decide)]
      try simp only [BitVec.zeroExtend]
      try simp only [BitVec.getLsbD_or]
      try simp only [BitVec.getLsbD_shiftLeft]
      try simp only [BitVec.getLsbD_ushiftRight]
      try simp only [BitVec.getLsbD_and]
      try simp only [BitVec.getLsbD_setWidth]
      try dsimp only
      try simp only [hm63]
      try simp only [getLsbD_8_of_ge]
      simp
    }
  · apply BitVec.eq_of_getLsbD_eq; intro k hk
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
    all_goals {
      rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
        getLsbD_evalBitfield_w32_ubfm _ _ 6 31 _ (by decide)]
      try simp only [BitVec.zeroExtend]
      try simp only [BitVec.getLsbD_shiftLeft]
      try simp only [BitVec.getLsbD_ushiftRight]
      try simp only [BitVec.getLsbD_setWidth]
      try dsimp only
      try simp only [getLsbD_8_of_ge]
      simp
    }

theorem lane16_neonDeserialize10Half_eq_chunk (bs : List (BitVec 8)) (hlen : bs.length = 20)
    (j : Fin 8) :
    lane16 (neonDeserialize10Half bs 0) j = deserializeChunkCoeff 10 bs j.val ∧
    lane16 (neonDeserialize10Half bs 10) j = deserializeChunkCoeff 10 bs (8 + j.val) := by
  have hm3 (r : Nat) (hr : decide (r < 8) = true := by decide) :
      (0x03#8).getLsbD r = decide (r < 2) := by
    have := of_decide_eq_true hr
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> first | decide | omega
  have hm15 (r : Nat) (hr : decide (r < 8) = true := by decide) :
      (0x0f#8).getLsbD r = decide (r < 4) := by
    have := of_decide_eq_true hr
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> first | decide | omega
  have hm63 (r : Nat) (hr : decide (r < 8) = true := by decide) :
      (0x3f#8).getLsbD r = decide (r < 6) := by
    have := of_decide_eq_true hr
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> first | decide | omega
  constructor
  · unfold neonDeserialize10Half; rw [lane16_pack8x16]
    refine eq_deserializeChunkCoeff_of_bits 10 bs hlen j.val (by omega) _ ?_
    intro i hi
    rcases j with ⟨_ | _ | _ | _ | _ | _ | _ | _ | j, hj⟩ <;> try omega
    all_goals {
      dsimp only
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> try omega
      all_goals {
        try simp only [BitVec.zeroExtend]
        try simp only [BitVec.getLsbD_or]
        try simp only [BitVec.getLsbD_shiftLeft]
        try simp only [BitVec.getLsbD_ushiftRight]
        try simp only [BitVec.getLsbD_and]
        try simp only [BitVec.getLsbD_setWidth]
        try simp only [hm3]
        try simp only [hm15]
        try simp only [hm63]
        try simp only [getLsbD_8_of_ge]
        simp
      }
    }
  · unfold neonDeserialize10Half; rw [lane16_pack8x16]
    refine eq_deserializeChunkCoeff_of_bits 10 bs hlen (8 + j.val) (by omega) _ ?_
    intro i hi
    rcases j with ⟨_ | _ | _ | _ | _ | _ | _ | _ | j, hj⟩ <;> try omega
    all_goals {
      dsimp only
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> try omega
      all_goals {
        try simp only [BitVec.zeroExtend]
        try simp only [BitVec.getLsbD_or]
        try simp only [BitVec.getLsbD_shiftLeft]
        try simp only [BitVec.getLsbD_ushiftRight]
        try simp only [BitVec.getLsbD_and]
        try simp only [BitVec.getLsbD_setWidth]
        try simp only [hm3]
        try simp only [hm15]
        try simp only [hm63]
        try simp only [getLsbD_8_of_ge]
        simp
      }
    }

theorem lane16_neonDeserialize10Half_lt (bs : List (BitVec 8)) (off : Nat) (j : Fin 8) :
    (lane16 (neonDeserialize10Half bs off) j).toNat < 1024 := by
  let sub : List (BitVec 8) := List.ofFn (fun k : Fin 20 => bs.getD (off + k.val) 0#8)
  have hlen : sub.length = 20 := by simp [sub]
  have heq : lane16 (neonDeserialize10Half bs off) j = lane16 (neonDeserialize10Half sub 0) j := by
    unfold neonDeserialize10Half; rw [lane16_pack8x16, lane16_pack8x16]; simp only [Nat.zero_add]
    have hget : ∀ r : Nat, r < 20 → sub.getD r 0#8 = bs.getD (off + r) 0#8 := by
      intro r hr; dsimp only [sub]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hr, List.getD_eq_getElem?_getD]
    have h0 : sub.getD (5 * (j.val / 4)) 0#8 = bs.getD (off + 5 * (j.val / 4)) 0#8 :=
      hget _ (by omega)
    have h1 : sub.getD (5 * (j.val / 4) + 1) 0#8 = bs.getD (off + 5 * (j.val / 4) + 1) 0#8 := by
      rw [hget _ (by omega), Nat.add_assoc]
    have h2 : sub.getD (5 * (j.val / 4) + 2) 0#8 = bs.getD (off + 5 * (j.val / 4) + 2) 0#8 := by
      rw [hget _ (by omega), Nat.add_assoc]
    have h3 : sub.getD (5 * (j.val / 4) + 3) 0#8 = bs.getD (off + 5 * (j.val / 4) + 3) 0#8 := by
      rw [hget _ (by omega), Nat.add_assoc]
    have h4 : sub.getD (5 * (j.val / 4) + 4) 0#8 = bs.getD (off + 5 * (j.val / 4) + 4) 0#8 := by
      rw [hget _ (by omega), Nat.add_assoc]
    rw [h0, h1, h2, h3, h4]
  rw [heq, (lane16_neonDeserialize10Half_eq_chunk sub hlen j).1]
  have hlt := byteDecodeRaw_lt_two_pow 10 (by decide) sub j.val (by omega)
  unfold deserializeChunkCoeff
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hlt

/-- `xtn vd.4h, vn.4s`: narrows the low 16 bits of each 32-bit lane (even 16-bit lanes `0, 2, 4, 6`). -/
@[expose] def simdXtn4h (vn : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => if h : i.val < 4 then lane16 vn ⟨2 * i.val, by omega⟩ else 0#16

/-- `shrn vd.4h, vn.4s, #16`: narrows the high 16 bits of each 32-bit lane (odd lanes `1, 3, 5, 7`). -/
@[expose] def simdShrn16_4h (vn : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => if h : i.val < 4 then lane16 vn ⟨2 * i.val + 1, by omega⟩ else 0#16

/-- `umlal vd.4s, vn.4h, vm.4h`: unsigned widening multiply-accumulate on low 4 halfword lanes. -/
@[expose] def simdUmlal4sLow (vd vn vm : BitVec 128) : BitVec 128 :=
  pack4x32 fun i =>
    lane32 vd i + (lane16 vn ⟨i.val, by omega⟩).zeroExtend 32 *
      (lane16 vm ⟨i.val, by omega⟩).zeroExtend 32

/-- `ushr vd.4s, vn.4s, #sh`: unsigned 32-bit lane right shift. -/
@[expose] def simdUshr4s (vn : BitVec 128) (sh : Nat) : BitVec 128 :=
  pack4x32 fun i => lane32 vn i >>> sh

/-- `simdXtn4h` ignores odd 16-bit lanes (so `xtn v2.4h, v0.4s` before `mov v0.h[7], w11` at
`B04 +0x06c8` equals `simdXtn4h` on the completed 8-lane vector `v0`). -/
theorem simdXtn4h_eq_of_even_lanes {u v : BitVec 128}
    (h : ∀ r : Fin 4, lane16 u ⟨2 * r.val, by omega⟩ = lane16 v ⟨2 * r.val, by omega⟩) :
    simdXtn4h u = simdXtn4h v := by
  unfold simdXtn4h; congr 1; funext i
  by_cases hi : i.val < 4
  · simp only [hi, ↓reduceDIte]; exact h ⟨i.val, hi⟩
  · simp [hi]

/-- Fused NEON `decompress_10` (`B04 +0x06c8..+0x0710`). -/
@[expose] def neonDecompress10_8h (v : BitVec 128) : BitVec 128 :=
  let bias := pack4x32 fun _ => 512#32
  let qVec := dup8x16 3329#16
  let ev := simdUshr4s (simdUmlal4sLow bias (simdXtn4h v) qVec) 10
  let od := simdUshr4s (simdUmlal4sLow bias (simdShrn16_4h v) qVec) 10
  simdTrn1_8h ev od

private theorem lane16_even_of_pack4x32 (f : Fin 4 → BitVec 32) (r : Fin 4) :
    lane16 (pack4x32 f) ⟨2 * r.val, by omega⟩ = (f r).truncate 16 := by
  have h32 := lane32_pack4x32 f r
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hb32 := congrArg (fun w : BitVec 32 => w.getLsbD b) h32
  simp only [lane32, BitVec.getLsbD_extractLsb', show b < 32 by omega, decide_true,
    Bool.true_and] at hb32
  simp only [lane16, BitVec.getLsbD_extractLsb', BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and]
  rwa [show 16 * (2 * r.val) + b = 32 * r.val + b by omega]

theorem lane16_neonDecompress10_8h (v : BitVec 128)
    (hv : ∀ j : Fin 8, (lane16 v j).toNat < 1024) (j : Fin 8) :
    lane16 (neonDecompress10_8h v) j = BitVec.ofNat 16 (decompressCoeff 10 (lane16 v j).toNat) := by
  have h10 : ∀ x : BitVec 16, x.toNat < 1024 →
      (((512#32 + x.zeroExtend 32 * 3329#32) >>> 10).truncate 16) =
        BitVec.ofNat 16 (decompressCoeff 10 x.toNat) := by
    intro x hx
    apply BitVec.eq_of_toNat_eq
    unfold decompressCoeff mlkemQ
    simp only [show (10 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      show 1 <<< (10 - 1) = 512 from rfl,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega : x.toNat < 4294967296),
      Nat.mod_eq_of_lt (by omega : x.toNat * 3329 < 4294967296),
      Nat.mod_eq_of_lt (by omega : 512 + x.toNat * 3329 < 4294967296),
      Nat.add_comm 512]
  unfold neonDecompress10_8h; dsimp only
  rw [lane16_simdTrn1_8h]
  by_cases hev : j.val % 2 == 0
  · have hmod0 : j.val % 2 = 0 := beq_iff_eq.mp hev
    simp only [hev, ↓reduceIte, simdUshr4s, simdUmlal4sLow]
    have hfin : (⟨j.val / 2 * 2, by omega⟩ : Fin 8) = ⟨2 * (j.val / 2), by omega⟩ := by
      apply Fin.ext; dsimp only; omega
    rw [hfin, lane16_even_of_pack4x32 _ ⟨j.val / 2, by omega⟩]
    simp only [lane32_pack4x32, simdXtn4h, lane16_pack8x16, show j.val / 2 < 4 by omega,
      ↓reduceDIte, lane16_dup8x16]
    have hj : (⟨2 * (j.val / 2), by omega⟩ : Fin 8) = j := by apply Fin.ext; dsimp only; omega
    rw [hj]
    exact h10 (lane16 v j) (hv j)
  · have hmod1 : j.val % 2 = 1 := by
      have := beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hev); omega
    simp only [hev, Bool.false_eq_true, ↓reduceIte, simdUshr4s, simdUmlal4sLow]
    have hfin : (⟨j.val / 2 * 2, by omega⟩ : Fin 8) = ⟨2 * (j.val / 2), by omega⟩ := by
      apply Fin.ext; dsimp only; omega
    rw [hfin, lane16_even_of_pack4x32 _ ⟨j.val / 2, by omega⟩]
    simp only [lane32_pack4x32, simdShrn16_4h, lane16_pack8x16, show j.val / 2 < 4 by omega,
      ↓reduceDIte, lane16_dup8x16]
    have hj : (⟨2 * (j.val / 2) + 1, by omega⟩ : Fin 8) = j := by apply Fin.ext; dsimp only; omega
    rw [hj]
    exact h10 (lane16 v j) (hv j)

/-- Full-polynomial chunk bridge for `neonDeserialize10Half` + `neonDecompress10_8h` (`c < 16`). -/
theorem lane16_neonDecompress10_eq_decodeAndDecompress (fullBs : List (BitVec 8)) (c : Nat)
    (hc : c < 16) (hlen : 20 * (c + 1) ≤ fullBs.length) (j : Fin 8) :
    lane16 (neonDecompress10_8h (neonDeserialize10Half ((fullBs.drop (20 * c)).take 20) 0)) j =
      BitVec.ofNat 16 ((decodeAndDecompress 10 fullBs).getD (16 * c + j.val) 0) ∧
    lane16 (neonDecompress10_8h (neonDeserialize10Half ((fullBs.drop (20 * c)).take 20) 10)) j =
      BitVec.ofNat 16 ((decodeAndDecompress 10 fullBs).getD (16 * c + (8 + j.val)) 0) := by
  set chunk := (fullBs.drop (20 * c)).take 20
  have hclen : chunk.length = 20 := by simp [chunk]; omega
  obtain ⟨h0, h1⟩ := lane16_neonDeserialize10Half_eq_chunk chunk hclen j
  have hcell (idx : Nat) (hidx : idx < 16) :
      decompressCoeff 10 (deserializeChunkCoeff 10 chunk idx).toNat =
        (decodeAndDecompress 10 fullBs).getD (16 * c + idx) 0 := by
    have hlt := byteDecodeRaw_lt_two_pow 10 (by decide) chunk idx (by omega)
    unfold deserializeChunkCoeff
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show chunk = (fullBs.drop (2 * 10 * c)).take (2 * 10) by simp [chunk]]
    exact decodeAndDecompress_chunk_eq 10 fullBs c idx hc hidx
      (by simpa [Nat.mul_assoc] using hlen)
  rw [lane16_neonDecompress10_8h _ (lane16_neonDeserialize10Half_lt chunk 0),
    lane16_neonDecompress10_8h _ (lane16_neonDeserialize10Half_lt chunk 10),
    h0, h1, hcell j.val (by omega), hcell (8 + j.val) (by omega)]
  exact ⟨rfl, rfl⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode10

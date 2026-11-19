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
# NEON Inlined `deserialize_12` Bit-Unpacking Soundness (`Poly.Serialize.Decode12`)

Pure NEON `ldr d` + `ld1.s[2]` + `tbl.16b` + `ushl.8h` + `bic #240, lsl #8` raw 12-bit
unpacking (`= Spec.byteDecodeRaw 12`, `< 4096`) and `cmhs 3329` + `bic #13, lsl #8` + `add.8h`
modular reduction (`= Spec.byteDecodeMod 12`, `< 3329`), covering `B20`, `B21`, `B03`, `B04`,
`B06`, and `B07`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  mlkemQ byteDecodeRaw byteDecodeMod
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  lane8 lane16 pack16x8 pack8x16 dup8x16 fin8_cases
  lane16_pack8x16 lane16_dup8x16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdUshlElem16 simdUshl8h simdTbl16b simdCmhs8h simdAdd8h
  lane16_and lane16_simdUshl8h lane16_simdCmhs8h lane16_simdAdd8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  deserializeChunkCoeff byteDecodeRaw_chunk_eq
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers (
  eq_deserializeChunkCoeff_of_bits
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (
  byteDecodeRaw_lt_two_pow
)

private theorem array_getD_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Nat) (d : α)
    (hi : i < n) : (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  unfold Array.getD
  split
  · rename_i h; change (Array.ofFn f)[i]'h = f ⟨i, hi⟩; exact Array.getElem_ofFn h
  · rename_i h; exact False.elim (h (by simp [hi]))

/-! ## 1. 12-Byte Load (`ldr d` + `ld1 {vt.s}[2]`) & Low-96-Bit Independence -/

/-- 12-byte vector state produced by `LDR Dt, [p]` followed by `LD1 {Vt.S}[2], [p + 8]`. -/
@[expose] def loadVec12 (bs : List (BitVec 8)) (off : Nat) : BitVec 128 :=
  setSimdLane
    ((pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
        (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
        (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)).zeroExtend 128)
    32 2
    ((pack32 (bs.getD (off + 8) 0#8) (bs.getD (off + 9) 0#8)
        (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8)).zeroExtend 128)

/-- Raw 12-bit NEON `deserialize_12` (`tbl` + `ushl` + `& 0x0fff`, before `cmhs 3329`). -/
@[expose] def neonDeserialize12Raw8h (v : BitVec 128) : BitVec 128 :=
  let t := simdTbl16b v 0x0b0a0a09080707060504040302010100#128
  let u := simdUshl8h t 0xfffc0000fffc0000fffc0000fffc0000#128
  u &&& dup8x16 0x0fff#16

/-- Modular-reduced NEON `deserialize_12` (`cmhs 3329` + `bic #13, lsl #8` + `add.8h`). -/
@[expose] def neonDeserialize12ModStep8h (m : BitVec 128) : BitVec 128 :=
  let c := simdCmhs8h m (dup8x16 3329#16)
  let s := c &&& dup8x16 0xf2ff#16
  simdAdd8h s m

/-- Full 6-instruction NEON `deserialize_12` (`B03`, `B04`, `B06`, `B07`, `B20`). -/
@[expose] def neonDeserialize12Mod8h (v : BitVec 128) : BitVec 128 :=
  neonDeserialize12ModStep8h (neonDeserialize12Raw8h v)

private theorem getLsbD_not_lane2_mask128 :
    ∀ k : Fin 128, (~~~(0xffffffff#128 <<< 64)).getLsbD k.val = decide (k.val < 64 ∨ 96 ≤ k.val) := by
  decide +kernel

private theorem getLsbD_0xffffffff128 :
    ∀ k : Fin 128, (0xffffffff#128).getLsbD k.val = decide (k.val < 32) := by
  decide +kernel

theorem loadVec12_eq_bytes (bs : List (BitVec 8)) (off : Nat) :
    loadVec12 bs off =
      0#32 ++
      pack32 (bs.getD (off + 8) 0#8) (bs.getD (off + 9) 0#8)
        (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8) ++
      pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
        (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
        (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8) := by
  unfold loadVec12 setSimdLane
  rw [show (1#128 <<< 32 - 1#128) = 0xffffffff#128 from rfl, show 32 * 2 = 64 from rfl]
  set lo := pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
      (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
      (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)
  set mid := pack32 (bs.getD (off + 8) 0#8) (bs.getD (off + 9) 0#8)
      (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8)
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have hm1 : (~~~(0xffffffff#128 <<< 64)).getLsbD k = decide (k < 64 ∨ 96 ≤ k) :=
    getLsbD_not_lane2_mask128 ⟨k, hk⟩
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, hm1,
    BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
  simp only [BitVec.zeroExtend, BitVec.getLsbD_setWidth]
  repeat rw [BitVec.getLsbD_append]
  by_cases hk64 : k < 64
  · simp [hk64, hk]
  · have hm2 : (0xffffffff#128).getLsbD (k - 64) = decide (k - 64 < 32) :=
      getLsbD_0xffffffff128 ⟨k - 64, by omega⟩
    rw [hm2]
    by_cases hk96 : k < 96
    · simp [hk64, hk, show ¬(96 ≤ k) by omega, show k - 64 < 32 by omega, show k - 64 < 128 by omega]
    · have hlo : lo.getLsbD k = false := BitVec.getLsbD_of_ge lo k (by omega)
      simp [hk64, hk, hlo, show 96 ≤ k by omega, show ¬(k - 64 < 32) by omega]

/-- `neonDeserialize12Raw8h` depends only on the low 12 bytes (`extractLsb' 0 96`) of `v`,
so any garbage in `v.s[3]` (e.g. from `ldur q` / un-cleared upper lane) is ignored. -/
theorem neonDeserialize12Raw8h_eq_of_extract96 {u v : BitVec 128}
    (h96 : u.extractLsb' 0 96 = v.extractLsb' 0 96) :
    neonDeserialize12Raw8h u = neonDeserialize12Raw8h v := by
  have htbl : simdTbl16b u 0x0b0a0a09080707060504040302010100#128 =
      simdTbl16b v 0x0b0a0a09080707060504040302010100#128 := by
    have hidx : ∀ i : Fin 16, (lane8 0x0b0a0a09080707060504040302010100#128 i).toNat < 12 := by
      decide +kernel
    have hlane : ∀ k : Nat, (hk : k < 12) → lane8 u ⟨k, by omega⟩ = lane8 v ⟨k, by omega⟩ := by
      intro k hk
      apply BitVec.eq_of_getLsbD_eq; intro b hb
      have heq := congrArg (fun x : BitVec 96 => x.getLsbD (8 * k + b)) h96
      simp only [BitVec.getLsbD_extractLsb', show 8 * k + b < 96 by omega, decide_true,
        Bool.true_and, Nat.zero_add] at heq
      simp only [lane8, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
      exact heq
    unfold simdTbl16b
    congr 1; funext i
    have hi12 := hidx i
    have hi16 : (lane8 0x0b0a0a09080707060504040302010100#128 i).toNat < 16 := by omega
    simp only [hi16, ↓reduceDIte]
    exact hlane _ hi12
  unfold neonDeserialize12Raw8h
  rw [htbl]

/-! ## 2. Raw 12-Bit Unpacking (`= deserializeChunkCoeff 12` / `Spec.byteDecodeRaw 12`) -/

private theorem lane8_pack12 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : BitVec 8) :
    let v : BitVec 128 := 0#32 ++ pack32 b8 b9 b10 b11 ++ pack64 b0 b1 b2 b3 b4 b5 b6 b7
    lane8 v 0 = b0 ∧ lane8 v 1 = b1 ∧ lane8 v 2 = b2 ∧ lane8 v 3 = b3 ∧
    lane8 v 4 = b4 ∧ lane8 v 5 = b5 ∧ lane8 v 6 = b6 ∧ lane8 v 7 = b7 ∧
    lane8 v 8 = b8 ∧ lane8 v 9 = b9 ∧ lane8 v 10 = b10 ∧ lane8 v 11 = b11 := by
  unfold lane8 pack32 pack64
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals {
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    rw [BitVec.getLsbD_extractLsb']
    repeat rw [BitVec.getLsbD_append]
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
    all_goals simp
  }

private theorem append_pair {n : Nat} (a : BitVec n) (b c : BitVec 8) :
    (a ++ b) ++ c = a ++ (b ++ c) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_append]
  by_cases h8 : k < 8
  · simp [h8, show k < 16 by omega]
  · by_cases h16 : k < 16
    · simp [h8, h16, show k - 8 < 8 by omega]
    · simp [h8, h16, show ¬(k - 8 < 8) by omega, show k - 8 - 8 = k - 16 by omega]

private theorem tbl_loadVec12_eq (bs : List (BitVec 8)) (off : Nat) :
    simdTbl16b (loadVec12 bs off) 0x0b0a0a09080707060504040302010100#128 =
      pack8x16 fun i =>
        let t := i.val / 2
        if i.val % 2 == 0 then
          bs.getD (off + 3 * t + 1) 0#8 ++ bs.getD (off + 3 * t) 0#8
        else
          bs.getD (off + 3 * t + 2) 0#8 ++ bs.getD (off + 3 * t + 1) 0#8 := by
  rw [loadVec12_eq_bytes]
  obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11⟩ :=
    lane8_pack12 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
      (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
      (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8) (bs.getD (off + 8) 0#8)
      (bs.getD (off + 9) 0#8) (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8)
  unfold simdTbl16b pack16x8 pack8x16
  simp only [
    show (lane8 0x0b0a0a09080707060504040302010100#128 0).toNat = 0 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 1).toNat = 1 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 2).toNat = 1 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 3).toNat = 2 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 4).toNat = 3 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 5).toNat = 4 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 6).toNat = 4 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 7).toNat = 5 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 8).toNat = 6 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 9).toNat = 7 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 10).toNat = 7 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 11).toNat = 8 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 12).toNat = 9 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 13).toNat = 10 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 14).toNat = 10 by decide,
    show (lane8 0x0b0a0a09080707060504040302010100#128 15).toNat = 11 by decide,
    Nat.reduceLT, ↓reduceDIte]
  rw [show (⟨0, by decide⟩ : Fin 16) = 0 from rfl, hl0,
      show (⟨1, by decide⟩ : Fin 16) = 1 from rfl, hl1,
      show (⟨2, by decide⟩ : Fin 16) = 2 from rfl, hl2,
      show (⟨3, by decide⟩ : Fin 16) = 3 from rfl, hl3,
      show (⟨4, by decide⟩ : Fin 16) = 4 from rfl, hl4,
      show (⟨5, by decide⟩ : Fin 16) = 5 from rfl, hl5,
      show (⟨6, by decide⟩ : Fin 16) = 6 from rfl, hl6,
      show (⟨7, by decide⟩ : Fin 16) = 7 from rfl, hl7,
      show (⟨8, by decide⟩ : Fin 16) = 8 from rfl, hl8,
      show (⟨9, by decide⟩ : Fin 16) = 9 from rfl, hl9,
      show (⟨10, by decide⟩ : Fin 16) = 10 from rfl, hl10,
      show (⟨11, by decide⟩ : Fin 16) = 11 from rfl, hl11]
  have hf0 : (0 : Fin 8).val = 0 := rfl
  have hf1 : (1 : Fin 8).val = 1 := rfl
  have hf2 : (2 : Fin 8).val = 2 := rfl
  have hf3 : (3 : Fin 8).val = 3 := rfl
  have hf4 : (4 : Fin 8).val = 4 := rfl
  have hf5 : (5 : Fin 8).val = 5 := rfl
  have hf6 : (6 : Fin 8).val = 6 := rfl
  have hf7 : (7 : Fin 8).val = 7 := rfl
  simp only [hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7,
    Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, beq_iff_eq, show (1 = 0) ↔ False by decide,
    ↓reduceIte, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]
  repeat rw [append_pair]

theorem lane16_neonDeserialize12Raw8h_lt (v : BitVec 128) (j : Fin 8) :
    (lane16 (neonDeserialize12Raw8h v) j).toNat < 4096 := by
  unfold neonDeserialize12Raw8h; dsimp only
  rw [lane16_and, lane16_dup8x16, BitVec.toNat_and,
    show (0x0fff#16).toNat = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem lane16_neonDeserialize12Raw8h_loadVec12 (bs : List (BitVec 8)) (off : Nat) (j : Fin 8) :
    lane16 (neonDeserialize12Raw8h (loadVec12 bs off)) j =
      let t := j.val / 2
      if j.val % 2 == 0 then
        (bs.getD (off + 3 * t + 1) 0#8 ++ bs.getD (off + 3 * t) 0#8) &&& 0x0fff#16
      else
        ((bs.getD (off + 3 * t + 2) 0#8 ++ bs.getD (off + 3 * t + 1) 0#8) >>> 4) &&& 0x0fff#16 := by
  have hcst : ∀ i : Fin 8,
      ((lane16 0xfffc0000fffc0000fffc0000fffc0000#128 i).truncate 8).toInt =
        if i.val % 2 == 0 then 0 else -4 := by
    intro i; induction i using fin8_cases <;> decide
  unfold neonDeserialize12Raw8h; dsimp only
  rw [tbl_loadVec12_eq, lane16_and, lane16_simdUshl8h, lane16_pack8x16, lane16_dup8x16,
    simdUshlElem16, hcst j]
  induction j using fin8_cases <;> simp

/-- Exact lane-wise equivalence between `neonDeserialize12Raw8h (loadVec12 bs {0, 12})` and
`deserializeChunkCoeff 12 bs` (`bs.length = 24`). -/
theorem lane16_neonDeserialize12Raw8h_eq_chunk (bs : List (BitVec 8)) (hlen : bs.length = 24)
    (j : Fin 8) :
    lane16 (neonDeserialize12Raw8h (loadVec12 bs 0)) j = deserializeChunkCoeff 12 bs j.val ∧
    lane16 (neonDeserialize12Raw8h (loadVec12 bs 12)) j = deserializeChunkCoeff 12 bs (8 + j.val) := by
  constructor
  · rw [lane16_neonDeserialize12Raw8h_loadVec12]
    refine eq_deserializeChunkCoeff_of_bits 12 bs hlen j.val (by omega) _ ?_
    intro i hi
    rcases j with ⟨_ | _ | _ | _ | _ | _ | _ | _ | j, hj⟩ <;> try omega
    all_goals {
      dsimp only
      try simp only [Nat.reduceAdd]
      simp only [Nat.reduceMod, beq_iff_eq]
      try simp only [show (1 = 0) ↔ False by decide]
      simp only [↓reduceIte]
      rw [BitVec.getLsbD_and]
      try rw [BitVec.getLsbD_ushiftRight]
      rw [BitVec.getLsbD_append]
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
        try omega
      all_goals simp
    }
  · rw [lane16_neonDeserialize12Raw8h_loadVec12]
    refine eq_deserializeChunkCoeff_of_bits 12 bs hlen (8 + j.val) (by omega) _ ?_
    intro i hi
    rcases j with ⟨_ | _ | _ | _ | _ | _ | _ | _ | j, hj⟩ <;> try omega
    all_goals {
      dsimp only
      try simp only [Nat.reduceAdd]
      simp only [Nat.reduceMod, beq_iff_eq]
      try simp only [show (1 = 0) ↔ False by decide]
      simp only [↓reduceIte]
      rw [BitVec.getLsbD_and]
      try rw [BitVec.getLsbD_ushiftRight]
      rw [BitVec.getLsbD_append]
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
        try omega
      all_goals simp
    }

/-! ## 3. Modular Reduction (`cmhs 3329` + `bic #13, lsl #8` + `add.8h` = `% 3329`) -/

private theorem cmhs_reduce12_scalar (m : BitVec 16) (hm : m.toNat < 4096) :
    ((if (3329#16).toNat ≤ m.toNat then 0xffff#16 else 0#16) &&& 0xf2ff#16) + m =
      BitVec.ofNat 16 (m.toNat % mlkemQ) := by
  apply BitVec.eq_of_toNat_eq
  unfold mlkemQ
  by_cases hge : (3329#16).toNat ≤ m.toNat
  · simp only [hge, ↓reduceIte]
    rw [show (0xffff#16 &&& 0xf2ff#16) = 62207#16 from rfl]
    have h3329 : (3329#16).toNat = 3329 := rfl
    rw [h3329] at hge
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  · simp only [hge, ↓reduceIte]
    rw [show (0#16 &&& 0xf2ff#16) = 0#16 from rfl, BitVec.zero_add]
    have h3329 : (3329#16).toNat = 3329 := rfl
    rw [h3329] at hge
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    omega

theorem lane16_neonDeserialize12ModStep8h_eq (m : BitVec 128)
    (hm : ∀ j : Fin 8, (lane16 m j).toNat < 4096) (j : Fin 8) :
    lane16 (neonDeserialize12ModStep8h m) j = BitVec.ofNat 16 ((lane16 m j).toNat % mlkemQ) := by
  unfold neonDeserialize12ModStep8h; dsimp only
  rw [lane16_simdAdd8h, lane16_and, lane16_simdCmhs8h, lane16_dup8x16, lane16_dup8x16]
  exact cmhs_reduce12_scalar (lane16 m j) (hm j)

theorem lane16_neonDeserialize12Mod8h_lt (v : BitVec 128) (j : Fin 8) :
    (lane16 (neonDeserialize12Mod8h v) j).toNat < mlkemQ := by
  unfold neonDeserialize12Mod8h
  rw [lane16_neonDeserialize12ModStep8h_eq _ (lane16_neonDeserialize12Raw8h_lt v)]
  have hlt : (lane16 (neonDeserialize12Raw8h v) j).toNat % mlkemQ < mlkemQ :=
    Nat.mod_lt _ (by decide)
  rw [BitVec.toNat_ofNat, show 2 ^ 16 = 65536 from rfl,
    Nat.mod_eq_of_lt (by unfold mlkemQ at hlt ⊢; omega)]
  exact hlt

/-- Full-polynomial chunk bridge to `Spec.byteDecodeMod 12 fullBs` (`c < 16`, `24 * (c + 1) ≤ len`). -/
theorem lane16_neonDeserialize12Mod8h_eq_byteDecodeMod (fullBs : List (BitVec 8)) (c : Nat)
    (hc : c < 16) (hlen : 24 * (c + 1) ≤ fullBs.length) (j : Fin 8) :
    lane16 (neonDeserialize12Mod8h (loadVec12 ((fullBs.drop (24 * c)).take 24) 0)) j =
      BitVec.ofNat 16 ((byteDecodeMod 12 fullBs).getD (16 * c + j.val) 0) ∧
    lane16 (neonDeserialize12Mod8h (loadVec12 ((fullBs.drop (24 * c)).take 24) 12)) j =
      BitVec.ofNat 16 ((byteDecodeMod 12 fullBs).getD (16 * c + (8 + j.val)) 0) := by
  set chunk := (fullBs.drop (24 * c)).take 24
  have hclen : chunk.length = 24 := by simp [chunk]; omega
  obtain ⟨h0, h1⟩ := lane16_neonDeserialize12Raw8h_eq_chunk chunk hclen j
  have hmod_cell (idx : Nat) (hidx : idx < 16) :
      ((deserializeChunkCoeff 12 chunk idx).toNat % mlkemQ) =
        (byteDecodeMod 12 fullBs).getD (16 * c + idx) 0 := by
    have hraw := byteDecodeRaw_chunk_eq 12 fullBs c idx hc hidx
      (by simpa [Nat.mul_assoc] using hlen)
    have hbound : (byteDecodeRaw 12 chunk).getD idx 0 < 65536 := by
      have := byteDecodeRaw_lt_two_pow 12 (by decide) chunk idx (by omega)
      omega
    unfold deserializeChunkCoeff
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound,
      show chunk = (fullBs.drop (2 * 12 * c)).take (2 * 12) by simp [chunk],
      hraw]
    have hij256 : 16 * c + idx < 256 := by omega
    unfold byteDecodeMod byteDecodeRaw
    rw [Array.map_ofFn, array_getD_ofFn _ _ _ hij256, array_getD_ofFn _ _ _ hij256]
    rfl
  unfold neonDeserialize12Mod8h
  rw [lane16_neonDeserialize12ModStep8h_eq _ (lane16_neonDeserialize12Raw8h_lt _),
    lane16_neonDeserialize12ModStep8h_eq _ (lane16_neonDeserialize12Raw8h_lt _),
    h0, h1, hmod_cell j.val (by omega), hmod_cell (8 + j.val) (by omega)]
  exact ⟨rfl, rfl⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common -- proof-setup: allow-public-import

/-!
# NEON Inlined `serialize_{10, 12}` Bit-Packing Soundness (`Poly.Serialize.EncodeHigh`)

Pure NEON `trn1`/`trn2` + `sli.4s` + `sli.2d` + `ext #8` bit-packing equivalences for
`serialize_10` (`10`B / `20`B, `B03 +0x6c28..+0x6c90`) and `serialize_12` (`12`B / `24`B,
`B21 +0x04f4..+0x0558`, `B05 +0x6290..+0x62f4`), including unmasked `serialize_12` when all
lanes are `< 4096`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  lane8 lane16 lane32 lane64 pack16x8 dup8x16 ext_lane16 lane16_dup8x16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdSli4s simdSli2d simdTrn1_8h simdTrn2_8h simdTrn1_4s simdTrn2_4s simdExt16b
  lane16_and lane32_simdSli4s lane64_simdSli2d
  lane16_simdTrn1_8h lane16_simdTrn2_8h lane32_simdTrn1_4s lane32_simdTrn2_4s
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (
  byteEncodeHalf byteEncodeChunkVec eq_byteEncodeHalf_of_bits byteEncodeChunkVec_eq_append_half
)

/-! ## 1. Sub-Lane & `simdExt16b #8` Bit-Extraction Helpers -/

private theorem getLsbD_lane32_eq_lane16 (u : BitVec 128) (p : Fin 4) (r : Nat) (hr : r < 32) :
    (lane32 u p).getLsbD r =
      if r < 16 then (lane16 u ⟨2 * p.val, by omega⟩).getLsbD r
      else (lane16 u ⟨2 * p.val + 1, by omega⟩).getLsbD (r - 16) := by
  unfold lane32 lane16
  rw [BitVec.getLsbD_extractLsb']
  by_cases h16 : r < 16
  · simp only [h16, ↓reduceIte, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and]
    congr 1; omega
  · have hsub : r - 16 < 16 := by omega
    simp only [h16, ↓reduceIte, BitVec.getLsbD_extractLsb', hr, hsub, decide_true, Bool.true_and]
    congr 1; omega

private theorem getLsbD_lane64_eq_lane32 (u : BitVec 128) (q : Fin 2) (r : Nat) (hr : r < 64) :
    (lane64 u q).getLsbD r =
      if r < 32 then (lane32 u ⟨2 * q.val, by omega⟩).getLsbD r
      else (lane32 u ⟨2 * q.val + 1, by omega⟩).getLsbD (r - 32) := by
  unfold lane64 lane32
  rw [BitVec.getLsbD_extractLsb']
  by_cases h32 : r < 32
  · simp only [h32, ↓reduceIte, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and]
    congr 1; omega
  · have hsub : r - 32 < 32 := by omega
    simp only [h32, ↓reduceIte, BitVec.getLsbD_extractLsb', hr, hsub, decide_true, Bool.true_and]
    congr 1; omega

theorem lane64_simdExt16b_8_0 (u : BitVec 128) :
    lane64 (simdExt16b u u 8) 0 = lane64 u 1 := by
  have hext : simdExt16b u u 8 =
      lane8 u 7 ++ lane8 u 6 ++ lane8 u 5 ++ lane8 u 4 ++
      lane8 u 3 ++ lane8 u 2 ++ lane8 u 1 ++ lane8 u 0 ++
      lane8 u 15 ++ lane8 u 14 ++ lane8 u 13 ++ lane8 u 12 ++
      lane8 u 11 ++ lane8 u 10 ++ lane8 u 9 ++ lane8 u 8 := rfl
  rw [hext]
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  unfold lane64
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  simp only [hr, decide_true, Bool.true_and, Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.zero_add,
    Nat.mul_one]
  repeat rw [BitVec.getLsbD_append]
  by_cases h1 : r < 8
  · simp [h1, lane8]
  · by_cases h2 : r < 16
    · simp only [h1, show r - 8 < 8 by omega, ↓reduceIte, lane8, BitVec.getLsbD_extractLsb',
        decide_true, Bool.true_and]; congr 1; omega
    · by_cases h3 : r < 24
      · simp only [h1, show ¬(r - 8 < 8) by omega, show r - 8 - 8 < 8 by omega, ↓reduceIte, lane8,
          BitVec.getLsbD_extractLsb', decide_true, Bool.true_and]; congr 1; omega
      · by_cases h4 : r < 32
        · simp only [h1, show ¬(r - 8 < 8) by omega, show ¬(r - 8 - 8 < 8) by omega,
            show r - 8 - 8 - 8 < 8 by omega, ↓reduceIte, lane8, BitVec.getLsbD_extractLsb',
            decide_true, Bool.true_and]; congr 1; omega
        · by_cases h5 : r < 40
          · simp only [h1, show ¬(r - 8 < 8) by omega, show ¬(r - 8 - 8 < 8) by omega,
              show ¬(r - 8 - 8 - 8 < 8) by omega, show r - 8 - 8 - 8 - 8 < 8 by omega, ↓reduceIte,
              lane8, BitVec.getLsbD_extractLsb', decide_true, Bool.true_and]; congr 1; omega
          · by_cases h6 : r < 48
            · simp only [h1, show ¬(r - 8 < 8) by omega, show ¬(r - 8 - 8 < 8) by omega,
                show ¬(r - 8 - 8 - 8 < 8) by omega, show ¬(r - 8 - 8 - 8 - 8 < 8) by omega,
                show r - 8 - 8 - 8 - 8 - 8 < 8 by omega, ↓reduceIte, lane8,
                BitVec.getLsbD_extractLsb', decide_true, Bool.true_and]; congr 1; omega
            · by_cases h7 : r < 56
              · simp only [h1, show ¬(r - 8 < 8) by omega, show ¬(r - 8 - 8 < 8) by omega,
                  show ¬(r - 8 - 8 - 8 < 8) by omega, show ¬(r - 8 - 8 - 8 - 8 < 8) by omega,
                  show ¬(r - 8 - 8 - 8 - 8 - 8 < 8) by omega,
                  show r - 8 - 8 - 8 - 8 - 8 - 8 < 8 by omega, ↓reduceIte, lane8,
                  BitVec.getLsbD_extractLsb', decide_true, Bool.true_and]; congr 1; omega
              · simp only [h1, show ¬(r - 8 < 8) by omega, show ¬(r - 8 - 8 < 8) by omega,
                  show ¬(r - 8 - 8 - 8 < 8) by omega, show ¬(r - 8 - 8 - 8 - 8 < 8) by omega,
                  show ¬(r - 8 - 8 - 8 - 8 - 8 < 8) by omega,
                  show ¬(r - 8 - 8 - 8 - 8 - 8 - 8 < 8) by omega,
                  show r - 8 - 8 - 8 - 8 - 8 - 8 - 8 < 8 by omega, ↓reduceIte, lane8,
                  BitVec.getLsbD_extractLsb', decide_true, Bool.true_and]; congr 1; omega

theorem lane8_simdExt16b_8_4 (u : BitVec 128) :
    lane8 (simdExt16b u u 8) 4 = lane8 u 12 := by
  have h := congrArg (fun w : BitVec 64 => w.extractLsb' 32 8) (lane64_simdExt16b_8_0 u)
  have hlhs : (lane64 (simdExt16b u u 8) 0).extractLsb' 32 8 = lane8 (simdExt16b u u 8) 4 := by
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [lane64, lane8, hb, show 32 + b < 64 by omega]
  have hrhs : (lane64 u 1).extractLsb' 32 8 = lane8 u 12 := by
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp only [lane64, lane8, BitVec.getLsbD_extractLsb', hb, show 32 + b < 64 by omega,
      decide_true, Bool.true_and, Fin.val_one, Nat.mul_one]
    congr 1; omega
  rwa [hlhs, hrhs] at h

theorem lane16_simdExt16b_8_2 (u : BitVec 128) :
    lane16 (simdExt16b u u 8) 2 = lane16 u 6 := by
  have h := congrArg (fun w : BitVec 64 => w.extractLsb' 32 16) (lane64_simdExt16b_8_0 u)
  have hlhs : (lane64 (simdExt16b u u 8) 0).extractLsb' 32 16 = lane16 (simdExt16b u u 8) 2 := by
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [lane64, lane16, hb, show 32 + b < 64 by omega]
  have hrhs : (lane64 u 1).extractLsb' 32 16 = lane16 u 6 := by
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp only [lane64, lane16, BitVec.getLsbD_extractLsb', hb, show 32 + b < 64 by omega,
      decide_true, Bool.true_and, Fin.val_one, Nat.mul_one]
    congr 1; omega
  rwa [hlhs, hrhs] at h

/-! ## 2. Shared 2-Stage `trn1`/`trn2` + `sli.4s` + `sli.2d` Bit Characterization -/

private theorem getLsbD_sli_pack64 (d : Nat) (mask16 : BitVec 16) (v : BitVec 128)
    (hd : 0 < d ∧ d ≤ 12)
    (hm16 : ∀ r, mask16.getLsbD r = decide (r < d))
    (hm32 : ∀ r, ((1#32 <<< d) - 1#32).getLsbD r = decide (r < d))
    (hm64 : ∀ r, ((1#64 <<< (2 * d)) - 1#64).getLsbD r = decide (r < 2 * d))
    (q : Fin 2) (r : Nat) (hrd4 : r / d < 4) (hr : r < 4 * d) :
    (lane64 (simdSli2d
      (simdTrn1_4s (simdSli4s (simdTrn1_8h (v &&& dup8x16 mask16) (v &&& dup8x16 mask16))
                              (simdTrn2_8h (v &&& dup8x16 mask16) (v &&& dup8x16 mask16)) d)
                   (simdSli4s (simdTrn1_8h (v &&& dup8x16 mask16) (v &&& dup8x16 mask16))
                              (simdTrn2_8h (v &&& dup8x16 mask16) (v &&& dup8x16 mask16)) d))
      (simdTrn2_4s (simdSli4s (simdTrn1_8h (v &&& dup8x16 mask16) (v &&& dup8x16 mask16))
                              (simdTrn2_8h (v &&& dup8x16 mask16) (v &&& dup8x16 mask16)) d)
                   (simdSli4s (simdTrn1_8h (v &&& dup8x16 mask16) (v &&& dup8x16 mask16))
                              (simdTrn2_8h (v &&& dup8x16 mask16) (v &&& dup8x16 mask16)) d))
      (2 * d)) q).getLsbD r =
      (lane16 v ⟨4 * q.val + r / d, by omega⟩).getLsbD (r % d) := by
  set v' := v &&& dup8x16 mask16
  set mixt := simdSli4s (simdTrn1_8h v' v') (simdTrn2_8h v' v') d
  have hmixt : ∀ (p : Fin 4) (s : Nat) (hsd2 : s / d < 2) (hs : s < 2 * d),
      (lane32 mixt p).getLsbD s =
        (lane16 v ⟨2 * p.val + s / d, by omega⟩).getLsbD (s % d) := by
    intro p s hsd2 hs
    dsimp only [mixt]
    rw [lane32_simdSli4s, BitVec.getLsbD_or, BitVec.getLsbD_and, hm32 s, BitVec.getLsbD_shiftLeft]
    by_cases hsd : s < d
    · rw [getLsbD_lane32_eq_lane16 _ p s (by omega)]
      simp only [hsd, show s < 16 by omega, ↓reduceIte, decide_true, Bool.and_true, Bool.not_true,
        Bool.and_false, Bool.false_and, Bool.or_false, lane16_simdTrn1_8h, Nat.mul_mod_right,
        beq_self_eq_true, Nat.mul_div_cancel_left _ (by omega : 0 < 2), Nat.div_eq_of_lt hsd,
        Nat.add_zero, Nat.mod_eq_of_lt hsd]
      have hp : (⟨p.val * 2, by omega⟩ : Fin 8) = ⟨2 * p.val, by omega⟩ := by ext; dsimp only; omega
      rw [hp]; dsimp only [v']
      rw [lane16_and, lane16_dup8x16, BitVec.getLsbD_and, hm16 s]
      simp [hsd]
    · have hsub16 : s - d < 16 := by omega
      have hsubd : s - d < d := by omega
      rw [getLsbD_lane32_eq_lane16 _ p (s - d) (by omega)]
      have hdiv : s / d = 1 := by
        have h1 : s = d * 1 + (s - d) := by omega
        rw [h1, Nat.mul_add_div hd.1, Nat.div_eq_of_lt hsubd]
      have hmod : s % d = s - d := by
        have h1 : s = d * 1 + (s - d) := by omega
        conv_lhs => rw [h1]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hsubd]
      simp only [hsd, hsub16, ↓reduceIte, decide_false, Bool.and_false, Bool.not_false,
        show s < 32 by omega, decide_true, Bool.true_and, Bool.false_or, lane16_simdTrn2_8h,
        Nat.mul_mod_right, beq_self_eq_true, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
        hdiv, hmod]
      have hp : (⟨p.val * 2 + 1, by omega⟩ : Fin 8) = ⟨2 * p.val + 1, by omega⟩ := by
        ext; dsimp only; omega
      rw [hp]; dsimp only [v']
      rw [lane16_and, lane16_dup8x16, BitVec.getLsbD_and, hm16 (s - d)]
      simp [hsubd]
  rw [lane64_simdSli2d, BitVec.getLsbD_or, BitVec.getLsbD_and, hm64 r, BitVec.getLsbD_shiftLeft]
  by_cases hr2d : r < 2 * d
  · rw [getLsbD_lane64_eq_lane32 _ q r (by omega)]
    simp only [hr2d, show r < 32 by omega, ↓reduceIte, decide_true, Bool.and_true, Bool.not_true,
      Bool.and_false, Bool.false_and, Bool.or_false, lane32_simdTrn1_4s, Nat.mul_mod_right,
      beq_self_eq_true, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    have hq : (⟨q.val * 2, by omega⟩ : Fin 4) = ⟨2 * q.val, by omega⟩ := by ext; dsimp only; omega
    have hrd2 : r / d < 2 := (Nat.div_lt_iff_lt_mul hd.1).mpr hr2d
    rw [hq, hmixt ⟨2 * q.val, by omega⟩ r hrd2 hr2d]
    congr 2; apply Fin.ext; dsimp only; omega
  · have hsub2d : r - 2 * d < 2 * d := by omega
    rw [getLsbD_lane64_eq_lane32 _ q (r - 2 * d) (by omega)]
    simp only [hr2d, show r - 2 * d < 32 by omega, ↓reduceIte, decide_false, Bool.and_false,
      Bool.not_false, show r < 64 by omega, decide_true, Bool.true_and, Bool.false_or,
      lane32_simdTrn2_4s, Nat.mul_mod_right, beq_self_eq_true,
      Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    have hq : (⟨q.val * 2 + 1, by omega⟩ : Fin 4) = ⟨2 * q.val + 1, by omega⟩ := by
      ext; dsimp only; omega
    have hsubd2 : (r - 2 * d) / d < 2 := (Nat.div_lt_iff_lt_mul hd.1).mpr hsub2d
    rw [hq, hmixt ⟨2 * q.val + 1, by omega⟩ (r - 2 * d) hsubd2 hsub2d]
    have h1 : r = d * 2 + (r - 2 * d) := by omega
    have hdiv : r / d = 2 + (r - 2 * d) / d := by
      conv_lhs => rw [h1]
      rw [Nat.mul_add_div hd.1]
    have hmod : r % d = (r - 2 * d) % d := by
      conv_lhs => rw [h1]
      rw [Nat.mul_add_mod]
    rw [hmod]; congr 2; apply Fin.ext; dsimp only; omega

/-! ## 3. `serialize_10` (`10` Bytes per Vector / `20` Bytes per Pair, `B03 +0x6c28..+0x6c90`) -/

@[expose] def neonSerialize10Mix (v : BitVec 128) : BitVec 128 :=
  let v' := v &&& dup8x16 0x03ff#16
  let mixt := simdSli4s (simdTrn1_8h v' v') (simdTrn2_8h v' v') 10
  simdSli2d (simdTrn1_4s mixt mixt) (simdTrn2_4s mixt mixt) 20

@[expose] def neonSerialize10Half (v : BitVec 128) : List (BitVec 8) :=
  let m := neonSerialize10Mix v
  let mHi := simdExt16b m m 8
  unpack32 ((lane64 m 0).truncate 32) ++ [lane8 m 4] ++
  unpack32 ((lane64 mHi 0).truncate 32) ++ [lane8 m 12]

@[expose] def neonSerialize10Bytes (v0 v1 : BitVec 128) : List (BitVec 8) :=
  neonSerialize10Half v0 ++ neonSerialize10Half v1

private theorem mask_pow2_lsb {w : Nat} (len : Nat) (hlen : len < w) (r : Nat) :
    (BitVec.ofNat w (2 ^ len - 1)).getLsbD r = decide (r < len) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases hr : r < w
  · simp [hr]
  · simp [hr, show ¬(r < len) by omega]

theorem neonSerialize10Half_eq (v : BitVec 128) :
    neonSerialize10Half v = byteEncodeHalf 10 (lane16 v) := by
  have hm16 : ∀ r, (0x03ff#16).getLsbD r = decide (r < 10) := mask_pow2_lsb 10 (by decide)
  have hm32 : ∀ r, ((1#32 <<< 10) - 1#32).getLsbD r = decide (r < 10) := by
    intro r; rw [show (1#32 <<< 10) - 1#32 = BitVec.ofNat 32 (2 ^ 10 - 1) from rfl]
    exact mask_pow2_lsb 10 (by decide) r
  have hm64 : ∀ r, ((1#64 <<< 20) - 1#64).getLsbD r = decide (r < 20) := by
    intro r; rw [show (1#64 <<< 20) - 1#64 = BitVec.ofNat 64 (2 ^ 20 - 1) from rfl]
    exact mask_pow2_lsb 20 (by decide) r
  refine eq_byteEncodeHalf_of_bits ?_ ?_
  · simp [neonSerialize10Half]
  · intro k b hk hb
    have hbyte : ((neonSerialize10Half v).getD k 0#8)[b] =
        (lane64 (neonSerialize10Mix v) ⟨k / 5, by omega⟩).getLsbD (8 * (k % 5) + b) := by
      unfold neonSerialize10Half
      dsimp only
      rw [lane64_simdExt16b_8_0]
      rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
      all_goals {
        simp only [unpack32, List.cons_append, List.nil_append, List.getD_cons_zero,
          List.getD_cons_succ, BitVec.getElem_extractLsb', BitVec.truncate_eq_setWidth,
          BitVec.getLsbD_setWidth, lane8, lane64, BitVec.getLsbD_extractLsb']
        simp [show 8 + b < 32 by omega, show 16 + b < 32 by omega, show 24 + b < 32 by omega,
          show b < 32 by omega, show b < 64 by omega, show 8 + b < 64 by omega,
          show 16 + b < 64 by omega, show 24 + b < 64 by omega, show 32 + b < 64 by omega]
        try (congr 1; omega)
      }
    have hsli := getLsbD_sli_pack64 10 0x03ff#16 v ⟨by decide, by decide⟩ hm16 hm32 hm64
      ⟨k / 5, by omega⟩ (8 * (k % 5) + b) (by omega) (by omega)
    refine hbyte.trans (hsli.trans ?_)
    have hidx : 8 * k + b = 10 * (4 * (k / 5)) + (8 * (k % 5) + b) := by omega
    have hdiv : (8 * k + b) / 10 = 4 * (k / 5) + (8 * (k % 5) + b) / 10 := by
      rw [hidx, Nat.mul_add_div (by decide : 0 < 10)]
    have hmod : (8 * k + b) % 10 = (8 * (k % 5) + b) % 10 := by rw [hidx, Nat.mul_add_mod]
    rw [hmod]; congr 2; apply Fin.ext; dsimp only; exact hdiv.symm

theorem neonSerialize10Bytes_eq (v0 v1 : BitVec 128) :
    neonSerialize10Bytes v0 v1 = byteEncodeChunkVec 10 v0 v1 := by
  rw [neonSerialize10Bytes, neonSerialize10Half_eq, neonSerialize10Half_eq,
    byteEncodeChunkVec_eq_append_half]

/-! ## 4. `serialize_12` (`12` Bytes per Vector / `24` Bytes per Pair, `B21`, `B05`) -/

@[expose] def neonSerialize12Mix (v : BitVec 128) : BitVec 128 :=
  let v' := v &&& dup8x16 0x0fff#16
  let mixt := simdSli4s (simdTrn1_8h v' v') (simdTrn2_8h v' v') 12
  simdSli2d (simdTrn1_4s mixt mixt) (simdTrn2_4s mixt mixt) 24

/-- Unmasked `serialize_12` (`B21`, `B05`) equals `neonSerialize12Mix` when every lane is `< 4096`. -/
theorem neonSerialize12Mix_unmasked (v : BitVec 128)
    (h : ∀ j : Fin 8, (lane16 v j).toNat < 4096) :
    let mixt := simdSli4s (simdTrn1_8h v v) (simdTrn2_8h v v) 12
    simdSli2d (simdTrn1_4s mixt mixt) (simdTrn2_4s mixt mixt) 24 = neonSerialize12Mix v := by
  have hv : v &&& dup8x16 0x0fff#16 = v := by
    apply ext_lane16; intro j
    rw [lane16_and, lane16_dup8x16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x0fff#16).toNat = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (h j)
  dsimp only [neonSerialize12Mix]; rw [hv]

@[expose] def neonSerialize12Half (v : BitVec 128) : List (BitVec 8) :=
  let m := neonSerialize12Mix v
  let mHi := simdExt16b m m 8
  unpack32 ((lane64 m 0).truncate 32) ++ unpack16 (lane16 m 2) ++
  unpack32 ((lane64 mHi 0).truncate 32) ++ unpack16 (lane16 mHi 2)

@[expose] def neonSerialize12Bytes (v0 v1 : BitVec 128) : List (BitVec 8) :=
  neonSerialize12Half v0 ++ neonSerialize12Half v1

theorem neonSerialize12Half_eq (v : BitVec 128) :
    neonSerialize12Half v = byteEncodeHalf 12 (lane16 v) := by
  have hm16 : ∀ r, (0x0fff#16).getLsbD r = decide (r < 12) := mask_pow2_lsb 12 (by decide)
  have hm32 : ∀ r, ((1#32 <<< 12) - 1#32).getLsbD r = decide (r < 12) := by
    intro r; rw [show (1#32 <<< 12) - 1#32 = BitVec.ofNat 32 (2 ^ 12 - 1) from rfl]
    exact mask_pow2_lsb 12 (by decide) r
  have hm64 : ∀ r, ((1#64 <<< 24) - 1#64).getLsbD r = decide (r < 24) := by
    intro r; rw [show (1#64 <<< 24) - 1#64 = BitVec.ofNat 64 (2 ^ 24 - 1) from rfl]
    exact mask_pow2_lsb 24 (by decide) r
  refine eq_byteEncodeHalf_of_bits ?_ ?_
  · simp [neonSerialize12Half]
  · intro k b hk hb
    have hbyte : ((neonSerialize12Half v).getD k 0#8)[b] =
        (lane64 (neonSerialize12Mix v) ⟨k / 6, by omega⟩).getLsbD (8 * (k % 6) + b) := by
      unfold neonSerialize12Half
      dsimp only
      rw [lane64_simdExt16b_8_0, lane16_simdExt16b_8_2]
      rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
      all_goals {
        simp only [unpack32, unpack16, List.cons_append, List.nil_append, List.getD_cons_zero,
          List.getD_cons_succ, BitVec.getElem_extractLsb', BitVec.truncate_eq_setWidth,
          BitVec.getLsbD_setWidth, lane16, lane64, BitVec.getLsbD_extractLsb']
        simp [show b < 16 by omega, show 8 + b < 16 by omega, show b < 32 by omega,
          show 8 + b < 32 by omega, show 16 + b < 32 by omega, show 24 + b < 32 by omega,
          show b < 64 by omega, show 8 + b < 64 by omega, show 16 + b < 64 by omega,
          show 24 + b < 64 by omega, show 32 + b < 64 by omega, show 40 + b < 64 by omega]
        try (congr 1; omega)
      }
    have hsli := getLsbD_sli_pack64 12 0x0fff#16 v ⟨by decide, by decide⟩ hm16 hm32 hm64
      ⟨k / 6, by omega⟩ (8 * (k % 6) + b) (by omega) (by omega)
    refine hbyte.trans (hsli.trans ?_)
    have hidx : 8 * k + b = 12 * (4 * (k / 6)) + (8 * (k % 6) + b) := by omega
    have hdiv : (8 * k + b) / 12 = 4 * (k / 6) + (8 * (k % 6) + b) / 12 := by
      rw [hidx, Nat.mul_add_div (by decide : 0 < 12)]
    have hmod : (8 * k + b) % 12 = (8 * (k % 6) + b) % 12 := by rw [hidx, Nat.mul_add_mod]
    rw [hmod]; congr 2; apply Fin.ext; dsimp only; exact hdiv.symm

theorem neonSerialize12Bytes_eq (v0 v1 : BitVec 128) :
    neonSerialize12Bytes v0 v1 = byteEncodeChunkVec 12 v0 v1 := by
  rw [neonSerialize12Bytes, neonSerialize12Half_eq, neonSerialize12Half_eq,
    byteEncodeChunkVec_eq_append_half]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh

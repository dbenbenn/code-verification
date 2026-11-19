/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import Mathlib.Data.ZMod.Basic -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import

/-!
# 128-bit NEON `8 × i16` lane and 32-vector polynomial representation

1. `lane16` (`Fin 8 → BitVec 16`), `lane8`, `lane32`, `lane64`, `pack8x16`, `pack4x32`,
   `pack2x64`, `pack16x8`, `dup8x16`, `dup4hLow`, `ZMod 3329` / `Int` lane views, and 64-bit
   `hi ++ lo` load/store decomposition.
2. `@[simp]` lane-extraction bridges for `Arm64` `getSimdLane`, `setSimdLane`, `simdLaneUInt`,
   `simdLaneSInt`, `intToSimdLane`, `mapLanes`/`mapSimdLanes`, and `zipLanes`/`zipSimdLanes`.
3. 32-vector polynomial representation (`PolyVec128`, `vec128ToPoly16`), `getLsbD_readLE`,
   and `bytesToPoly16` bridge.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 mlkemQ bytesToPoly16
)

/-! ## 1. Lane Extraction, Packing, and `ZMod 3329` / `Int` Views -/

@[expose] def lane16 (v : BitVec 128) (i : Fin 8) : BitVec 16 := v.extractLsb' (16 * i.val) 16
@[expose] def lane8 (v : BitVec 128) (i : Fin 16) : BitVec 8 := v.extractLsb' (8 * i.val) 8
@[expose] def lane32 (v : BitVec 128) (i : Fin 4) : BitVec 32 := v.extractLsb' (32 * i.val) 32
@[expose] def lane64 (v : BitVec 128) (i : Fin 2) : BitVec 64 := v.extractLsb' (64 * i.val) 64
@[expose] def lane16Int (v : BitVec 128) (i : Fin 8) : Int := (lane16 v i).toInt
@[expose] def lane16ZMod (v : BitVec 128) (i : Fin 8) : ZMod mlkemQ := ((lane16 v i).toInt : ZMod mlkemQ)

@[expose] def pack8x16 (f : Fin 8 → BitVec 16) : BitVec 128 :=
  f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0
@[expose] def pack4x32 (f : Fin 4 → BitVec 32) : BitVec 128 := f 3 ++ f 2 ++ f 1 ++ f 0
@[expose] def pack2x64 (f : Fin 2 → BitVec 64) : BitVec 128 := f 1 ++ f 0
@[expose] def pack16x8 (f : Fin 16 → BitVec 8) : BitVec 128 :=
  f 15 ++ f 14 ++ f 13 ++ f 12 ++ f 11 ++ f 10 ++ f 9 ++ f 8 ++
  f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

@[expose] def dup8x16 (x : BitVec 16) : BitVec 128 := pack8x16 (fun _ => x)
@[expose] def dup4hLow (x : BitVec 16) : BitVec 128 := (x ++ x ++ x ++ x).zeroExtend 128

theorem fin8_cases {P : Fin 8 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (i : Fin 8) : P i := by
  rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · omega

theorem fin4_cases {P : Fin 4 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (i : Fin 4) : P i := by
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · omega

@[simp] theorem lane16_pack8x16 (f : Fin 8 → BitVec 16) (i : Fin 8) :
    lane16 (pack8x16 f) i = f i := by
  induction i using fin8_cases
  · change (pack8x16 f).extractLsb' 0 16 = f 0
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp only [pack8x16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.zero_add, hb,
      decide_true, Bool.true_and, ↓reduceIte]
  · change (pack8x16 f).extractLsb' 16 16 = f 1
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h1 : ¬ (16 + b < 16) := by omega
    have h2 : 16 + b - 16 < 16 := by omega
    simp only [pack8x16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true,
      Bool.true_and, h1, h2, ↓reduceIte]; congr 1; omega
  · change (pack8x16 f).extractLsb' 32 16 = f 2
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h1 : ¬ (32 + b < 16) := by omega
    have h2 : ¬ (32 + b - 16 < 16) := by omega
    have h3 : 32 + b - 16 - 16 < 16 := by omega
    simp only [pack8x16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true,
      Bool.true_and, h1, h2, h3, ↓reduceIte]; congr 1; omega
  · change (pack8x16 f).extractLsb' 48 16 = f 3
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h1 : ¬ (48 + b < 16) := by omega
    have h2 : ¬ (48 + b - 16 < 16) := by omega
    have h3 : ¬ (48 + b - 16 - 16 < 16) := by omega
    have h4 : 48 + b - 16 - 16 - 16 < 16 := by omega
    simp only [pack8x16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true,
      Bool.true_and, h1, h2, h3, h4, ↓reduceIte]; congr 1; omega
  · change (pack8x16 f).extractLsb' 64 16 = f 4
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h1 : ¬ (64 + b < 16) := by omega
    have h2 : ¬ (64 + b - 16 < 16) := by omega
    have h3 : ¬ (64 + b - 16 - 16 < 16) := by omega
    have h4 : ¬ (64 + b - 16 - 16 - 16 < 16) := by omega
    have h5 : 64 + b - 16 - 16 - 16 - 16 < 16 := by omega
    simp only [pack8x16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true,
      Bool.true_and, h1, h2, h3, h4, h5, ↓reduceIte]; congr 1; omega
  · change (pack8x16 f).extractLsb' 80 16 = f 5
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h1 : ¬ (80 + b < 16) := by omega
    have h2 : ¬ (80 + b - 16 < 16) := by omega
    have h3 : ¬ (80 + b - 16 - 16 < 16) := by omega
    have h4 : ¬ (80 + b - 16 - 16 - 16 < 16) := by omega
    have h5 : ¬ (80 + b - 16 - 16 - 16 - 16 < 16) := by omega
    have h6 : 80 + b - 16 - 16 - 16 - 16 - 16 < 16 := by omega
    simp only [pack8x16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true,
      Bool.true_and, h1, h2, h3, h4, h5, h6, ↓reduceIte]; congr 1; omega
  · change (pack8x16 f).extractLsb' 96 16 = f 6
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h1 : ¬ (96 + b < 16) := by omega
    have h2 : ¬ (96 + b - 16 < 16) := by omega
    have h3 : ¬ (96 + b - 16 - 16 < 16) := by omega
    have h4 : ¬ (96 + b - 16 - 16 - 16 < 16) := by omega
    have h5 : ¬ (96 + b - 16 - 16 - 16 - 16 < 16) := by omega
    have h6 : ¬ (96 + b - 16 - 16 - 16 - 16 - 16 < 16) := by omega
    have h7 : 96 + b - 16 - 16 - 16 - 16 - 16 - 16 < 16 := by omega
    simp only [pack8x16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true,
      Bool.true_and, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]; congr 1; omega
  · change (pack8x16 f).extractLsb' 112 16 = f 7
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h1 : ¬ (112 + b < 16) := by omega
    have h2 : ¬ (112 + b - 16 < 16) := by omega
    have h3 : ¬ (112 + b - 16 - 16 < 16) := by omega
    have h4 : ¬ (112 + b - 16 - 16 - 16 < 16) := by omega
    have h5 : ¬ (112 + b - 16 - 16 - 16 - 16 < 16) := by omega
    have h6 : ¬ (112 + b - 16 - 16 - 16 - 16 - 16 < 16) := by omega
    have h7 : ¬ (112 + b - 16 - 16 - 16 - 16 - 16 - 16 < 16) := by omega
    simp only [pack8x16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true,
      Bool.true_and, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]; congr 1; omega

@[simp] theorem pack8x16_lane16 (v : BitVec 128) : pack8x16 (lane16 v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  dsimp only [pack8x16, lane16]
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h1 : b < 16
  · simp [h1]
  · by_cases h2 : b < 32
    · have ha : b - 16 < 16 := by omega
      simp [h1, ha]; congr 1; omega
    · by_cases h3 : b < 48
      · have ha : ¬ (b - 16 < 16) := by omega
        have hb2 : b - 16 - 16 < 16 := by omega
        simp [h1, ha, hb2]; congr 1; omega
      · by_cases h4 : b < 64
        · have ha : ¬ (b - 16 < 16) := by omega
          have hb2 : ¬ (b - 16 - 16 < 16) := by omega
          have hc : b - 16 - 16 - 16 < 16 := by omega
          simp [h1, ha, hb2, hc]; congr 1; omega
        · by_cases h5 : b < 80
          · have ha : ¬ (b - 16 < 16) := by omega
            have hb2 : ¬ (b - 16 - 16 < 16) := by omega
            have hc : ¬ (b - 16 - 16 - 16 < 16) := by omega
            have hd : b - 16 - 16 - 16 - 16 < 16 := by omega
            simp [h1, ha, hb2, hc, hd]; congr 1; omega
          · by_cases h6 : b < 96
            · have ha : ¬ (b - 16 < 16) := by omega
              have hb2 : ¬ (b - 16 - 16 < 16) := by omega
              have hc : ¬ (b - 16 - 16 - 16 < 16) := by omega
              have hd : ¬ (b - 16 - 16 - 16 - 16 < 16) := by omega
              have he : b - 16 - 16 - 16 - 16 - 16 < 16 := by omega
              simp [h1, ha, hb2, hc, hd, he]; congr 1; omega
            · by_cases h7 : b < 112
              · have ha : ¬ (b - 16 < 16) := by omega
                have hb2 : ¬ (b - 16 - 16 < 16) := by omega
                have hc : ¬ (b - 16 - 16 - 16 < 16) := by omega
                have hd : ¬ (b - 16 - 16 - 16 - 16 < 16) := by omega
                have he : ¬ (b - 16 - 16 - 16 - 16 - 16 < 16) := by omega
                have hf : b - 16 - 16 - 16 - 16 - 16 - 16 < 16 := by omega
                simp [h1, ha, hb2, hc, hd, he, hf]; congr 1; omega
              · have ha : ¬ (b - 16 < 16) := by omega
                have hb2 : ¬ (b - 16 - 16 < 16) := by omega
                have hc : ¬ (b - 16 - 16 - 16 < 16) := by omega
                have hd : ¬ (b - 16 - 16 - 16 - 16 < 16) := by omega
                have he : ¬ (b - 16 - 16 - 16 - 16 - 16 < 16) := by omega
                have hf : ¬ (b - 16 - 16 - 16 - 16 - 16 - 16 < 16) := by omega
                have hg : b - 16 - 16 - 16 - 16 - 16 - 16 - 16 < 16 := by omega
                simp [h1, ha, hb2, hc, hd, he, hf, hg]; congr 1; omega

theorem ext_lane16 {u v : BitVec 128} (h : ∀ i : Fin 8, lane16 u i = lane16 v i) : u = v := by
  rw [← pack8x16_lane16 u, ← pack8x16_lane16 v]; congr 1; funext i; exact h i

@[simp] theorem lane32_pack4x32 (f : Fin 4 → BitVec 32) (i : Fin 4) :
    lane32 (pack4x32 f) i = f i := by
  induction i using fin4_cases
  · change (pack4x32 f).extractLsb' 0 32 = f 0
    dsimp only [pack4x32]; bv_bits
  · change (pack4x32 f).extractLsb' 32 32 = f 1
    dsimp only [pack4x32]; bv_bits
  · change (pack4x32 f).extractLsb' 64 32 = f 2
    dsimp only [pack4x32]; bv_bits
  · change (pack4x32 f).extractLsb' 96 32 = f 3
    dsimp only [pack4x32]; bv_bits

@[simp] theorem pack4x32_lane32 (v : BitVec 128) : pack4x32 (lane32 v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  dsimp only [pack4x32, lane32]
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h1 : b < 32
  · simp [h1]
  · by_cases h2 : b < 64
    · have ha : b - 32 < 32 := by omega
      simp [h1, ha]; congr 1; omega
    · by_cases h3 : b < 96
      · have ha : ¬ (b - 32 < 32) := by omega
        have hb2 : b - 32 - 32 < 32 := by omega
        simp [h1, ha, hb2]; congr 1; omega
      · have ha : ¬ (b - 32 < 32) := by omega
        have hb2 : ¬ (b - 32 - 32 < 32) := by omega
        have hc : b - 32 - 32 - 32 < 32 := by omega
        simp [h1, ha, hb2, hc]; congr 1; omega

theorem ext_lane32 {u v : BitVec 128} (h : ∀ i : Fin 4, lane32 u i = lane32 v i) : u = v := by
  rw [← pack4x32_lane32 u, ← pack4x32_lane32 v]; congr 1; funext i; exact h i

@[simp] theorem lane64_pack2x64 (f : Fin 2 → BitVec 64) (i : Fin 2) :
    lane64 (pack2x64 f) i = f i := by
  rcases i with ⟨_ | _ | n, hi⟩
  · change (pack2x64 f).extractLsb' 0 64 = f 0
    dsimp only [pack2x64]; bv_bits
  · change (pack2x64 f).extractLsb' 64 64 = f 1
    dsimp only [pack2x64]; bv_bits
  · omega

@[simp] theorem lane16_dup8x16 (x : BitVec 16) (i : Fin 8) : lane16 (dup8x16 x) i = x := by
  simp [dup8x16]

theorem lane16_dup4hLow_lt4 (x : BitVec 16) (i : Fin 8) (hi : i.val < 4) :
    lane16 (dup4hLow x) i = x := by
  rcases i with ⟨_ | _ | _ | _ | n, hlt⟩
  · change ((x ++ x ++ x ++ x).zeroExtend 128).extractLsb' 0 16 = x
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h128 : b < 128 := by omega
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
      Nat.zero_add, hb, h128, decide_true, Bool.true_and, ↓reduceIte]
  · change ((x ++ x ++ x ++ x).zeroExtend 128).extractLsb' 16 16 = x
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h128 : 16 + b < 128 := by omega
    have h16 : ¬ (16 + b < 16) := by omega
    have h32 : 16 + b - 16 < 16 := by omega
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
      hb, h128, h16, h32, decide_true, Bool.true_and, ↓reduceIte]
    congr 1; omega
  · change ((x ++ x ++ x ++ x).zeroExtend 128).extractLsb' 32 16 = x
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h128 : 32 + b < 128 := by omega
    have h1 : ¬ (32 + b < 16) := by omega
    have h2 : ¬ (32 + b - 16 < 16) := by omega
    have h3 : 32 + b - 16 - 16 < 16 := by omega
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
      hb, h128, h1, h2, h3, decide_true, Bool.true_and, ↓reduceIte]
    congr 1; omega
  · change ((x ++ x ++ x ++ x).zeroExtend 128).extractLsb' 48 16 = x
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have h128 : 48 + b < 128 := by omega
    have h1 : ¬ (48 + b < 16) := by omega
    have h2 : ¬ (48 + b - 16 < 16) := by omega
    have h3 : ¬ (48 + b - 16 - 16 < 16) := by omega
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
      hb, h128, h1, h2, h3, decide_true, Bool.true_and, ↓reduceIte]
    congr 1; omega
  · dsimp at hi; omega

theorem lane16_dup4hLow_ge4 (x : BitVec 16) (i : Fin 8) (hi : 4 ≤ i.val) :
    lane16 (dup4hLow x) i = 0#16 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have h128 : 16 * i.val + b < 128 := by omega
  have hge64 : 64 ≤ 16 * i.val + b := by omega
  simp [lane16, dup4hLow, hb, h128, BitVec.getLsbD_of_ge _ _ hge64]

theorem lane16_append64_lo (hi lo : BitVec 64) (i : Fin 8) (h : i.val < 4) :
    lane16 (hi ++ lo) i = lo.extractLsb' (16 * i.val) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hlt : 16 * i.val + b < 64 := by omega
  simp only [lane16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, hlt,
    decide_true, Bool.true_and, ↓reduceIte]

theorem lane16_append64_hi (hi lo : BitVec 64) (i : Fin 8) (h : 4 ≤ i.val) :
    lane16 (hi ++ lo) i = hi.extractLsb' (16 * (i.val - 4)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hge : ¬ (16 * i.val + b < 64) := by omega
  have hsub : 16 * i.val + b - 64 = 16 * (i.val - 4) + b := by omega
  simp only [lane16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, hge, hsub,
    decide_true, Bool.true_and, ↓reduceIte]

theorem extractLsb64_lo_pack8x16 (f : Fin 8 → BitVec 16) :
    (pack8x16 f).extractLsb' 0 64 = f 3 ++ f 2 ++ f 1 ++ f 0 := by
  dsimp only [pack8x16]; bv_bits

theorem extractLsb64_hi_pack8x16 (f : Fin 8 → BitVec 16) :
    (pack8x16 f).extractLsb' 64 64 = f 7 ++ f 6 ++ f 5 ++ f 4 := by
  dsimp only [pack8x16]; bv_bits

theorem truncate16_eq_lane16_zero (v : BitVec 128) : v.truncate 16 = lane16 v 0 := by
  change v.truncate 16 = v.extractLsb' 0 16; bv_bits

theorem truncate8_eq_lane8_zero (v : BitVec 128) : v.truncate 8 = lane8 v 0 := by
  change v.truncate 8 = v.extractLsb' 0 8; bv_bits

/-! ## 2. `Arm64` `getSimdLane` / `setSimdLane` / `mapSimdLanes` / `zipSimdLanes` Bridges -/

private theorem mask_getLsbD (w : Nat) (hw : w ≤ 64) (b : Nat) :
    (1#128 <<< w - 1#128).getLsbD b = decide (b < w) := by
  have hp : 2 ^ w < 2 ^ 128 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hp1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  have hval : (1#128 <<< w - 1#128).toNat = 2 ^ w - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
    simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  change (1#128 <<< w - 1#128).toNat.testBit b = decide (b < w)
  rw [hval, Nat.testBit_two_pow_sub_one]

private theorem getLsbD_65535_128 (b : Nat) : (65535#128).getLsbD b = decide (b < 16) :=
  mask_getLsbD 16 (by omega) b

private theorem getLsbD_4294967295_128 (b : Nat) :
    (4294967295#128).getLsbD b = decide (b < 32) :=
  mask_getLsbD 32 (by omega) b

private theorem getLsbD_255_128 (b : Nat) : (255#128).getLsbD b = decide (b < 8) :=
  mask_getLsbD 8 (by omega) b

@[simp] theorem getSimdLane_16_eq (v : BitVec 128) (i : Fin 8) :
    getSimdLane v 16 i.val = (lane16 v i).zeroExtend 128 := by
  have hm : (1#128 <<< 16 - 1#128) = 65535#128 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [getSimdLane, hm]
  simp only [lane16, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, getLsbD_65535_128,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and, BitVec.getLsbD_extractLsb']
  by_cases h16 : b < 16
  · simp [h16, Nat.mul_comm i.val 16]
  · simp [h16]

@[simp] theorem getSimdLane_32_eq (v : BitVec 128) (i : Fin 4) :
    getSimdLane v 32 i.val = (lane32 v i).zeroExtend 128 := by
  have hm : (1#128 <<< 32 - 1#128) = 4294967295#128 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [getSimdLane, hm]
  simp only [lane32, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, getLsbD_4294967295_128,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and, BitVec.getLsbD_extractLsb']
  by_cases h32 : b < 32
  · simp [h32, Nat.mul_comm i.val 32]
  · simp [h32]

@[simp] theorem getSimdLane_8_eq (v : BitVec 128) (i : Fin 16) :
    getSimdLane v 8 i.val = (lane8 v i).zeroExtend 128 := by
  have hm : (1#128 <<< 8 - 1#128) = 255#128 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [getSimdLane, hm]
  simp only [lane8, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, getLsbD_255_128,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and, BitVec.getLsbD_extractLsb']
  by_cases h8 : b < 8
  · simp [h8, Nat.mul_comm i.val 8]
  · simp [h8]

@[simp] theorem lane16_setSimdLane_16 (v elem : BitVec 128) (idx i : Fin 8) :
    lane16 (setSimdLane v 16 idx.val elem) i =
      if i = idx then elem.truncate 16 else lane16 v i := by
  have hm : (1#128 <<< 16 - 1#128) = 65535#128 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hpos : 16 * i.val + b < 128 := by omega
  rw [setSimdLane, hm]
  by_cases heq : i = idx
  · subst heq
    have hge : ¬ (16 * i.val + b < i.val * 16) := by omega
    have hsub : 16 * i.val + b - i.val * 16 = b := by omega
    simp only [↓reduceIte, lane16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hb,
      decide_true, Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hpos,
      BitVec.getLsbD_shiftLeft, hge, hsub, getLsbD_65535_128]
    simp
  · have hne_val : i.val ≠ idx.val := fun h => heq (Fin.ext h)
    by_cases hlt : 16 * i.val + b < idx.val * 16
    · simp only [heq, ↓reduceIte, lane16, BitVec.getLsbD_extractLsb', hb, decide_true,
        Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hpos,
        BitVec.getLsbD_shiftLeft, hlt]
      simp
    · have hsub16 : ¬ (16 * i.val + b - idx.val * 16 < 16) := by omega
      simp only [heq, ↓reduceIte, lane16, BitVec.getLsbD_extractLsb', hb, decide_true,
        Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hpos,
        BitVec.getLsbD_shiftLeft, hlt, getLsbD_65535_128, hsub16, decide_false]
      simp

@[simp] theorem lane32_setSimdLane_32 (v elem : BitVec 128) (idx i : Fin 4) :
    lane32 (setSimdLane v 32 idx.val elem) i =
      if i = idx then elem.truncate 32 else lane32 v i := by
  have hm : (1#128 <<< 32 - 1#128) = 4294967295#128 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hpos : 32 * i.val + b < 128 := by omega
  rw [setSimdLane, hm]
  by_cases heq : i = idx
  · subst heq
    have hge : ¬ (32 * i.val + b < i.val * 32) := by omega
    have hsub : 32 * i.val + b - i.val * 32 = b := by omega
    simp only [↓reduceIte, lane32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hb,
      decide_true, Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hpos,
      BitVec.getLsbD_shiftLeft, hge, hsub, getLsbD_4294967295_128]
    simp
  · have hne_val : i.val ≠ idx.val := fun h => heq (Fin.ext h)
    by_cases hlt : 32 * i.val + b < idx.val * 32
    · simp only [heq, ↓reduceIte, lane32, BitVec.getLsbD_extractLsb', hb, decide_true,
        Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hpos,
        BitVec.getLsbD_shiftLeft, hlt]
      simp
    · have hsub32 : ¬ (32 * i.val + b - idx.val * 32 < 32) := by omega
      simp only [heq, ↓reduceIte, lane32, BitVec.getLsbD_extractLsb', hb, decide_true,
        Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hpos,
        BitVec.getLsbD_shiftLeft, hlt, getLsbD_4294967295_128, hsub32, decide_false]
      simp

@[simp] theorem simdLaneUInt_16_zeroExtend (x : BitVec 16) :
    simdLaneUInt 16 (x.zeroExtend 128) = (x.toNat : Int) := by
  have hx := x.isLt
  simp only [simdLaneUInt]
  have h : (x.zeroExtend 128 &&& (1#128 <<< 16 - 1#128)) = x.zeroExtend 128 := by bv_bits
  rw [h, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; rfl

@[simp] theorem simdLaneSInt_16_zeroExtend (x : BitVec 16) :
    simdLaneSInt 16 (x.zeroExtend 128) = x.toInt := by
  simp only [simdLaneSInt, simdLaneUInt_16_zeroExtend]
  have hbit : (x.zeroExtend 128).getLsbD 15 = x.msb := by
    rw [BitVec.msb_eq_getLsbD_last]; simp
  rw [hbit, BitVec.toInt_eq_msb_cond]
  cases x.msb <;> rfl

@[simp] theorem simdLaneUInt_32_zeroExtend (x : BitVec 32) :
    simdLaneUInt 32 (x.zeroExtend 128) = (x.toNat : Int) := by
  have hx := x.isLt
  simp only [simdLaneUInt]
  have h : (x.zeroExtend 128 &&& (1#128 <<< 32 - 1#128)) = x.zeroExtend 128 := by bv_bits
  rw [h, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; rfl

@[simp] theorem simdLaneSInt_32_zeroExtend (x : BitVec 32) :
    simdLaneSInt 32 (x.zeroExtend 128) = x.toInt := by
  simp only [simdLaneSInt, simdLaneUInt_32_zeroExtend]
  have hbit : (x.zeroExtend 128).getLsbD 31 = x.msb := by
    rw [BitVec.msb_eq_getLsbD_last]; simp
  rw [hbit, BitVec.toInt_eq_msb_cond]
  cases x.msb <;> rfl

@[simp] theorem truncate16_intToSimdLane_16 (z : Int) :
    (intToSimdLane 16 z).truncate 16 = BitVec.ofInt 16 z := by
  simp only [intToSimdLane]
  have hmask : ((BitVec.ofInt 128 z &&& (1#128 <<< 16 - 1#128)).truncate 16) =
      (BitVec.ofInt 128 z).truncate 16 := by bv_bits
  rw [hmask]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.reducePow]
  omega

@[simp] theorem truncate32_intToSimdLane_32 (z : Int) :
    (intToSimdLane 32 z).truncate 32 = BitVec.ofInt 32 z := by
  simp only [intToSimdLane]
  have hmask : ((BitVec.ofInt 128 z &&& (1#128 <<< 32 - 1#128)).truncate 32) =
      (BitVec.ofInt 128 z).truncate 32 := by bv_bits
  rw [hmask]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.reducePow]
  omega

private theorem mapLanes_16_getLsbD (v : BitVec 128) (f : BitVec 128 → BitVec 128) :
    ∀ (n b : Nat), b < 128 →
      (mapLanes 16 v f n).getLsbD b =
        if b < 16 * n then
          (f ((v.extractLsb' (16 * (b / 16)) 16).zeroExtend 128)).getLsbD (b % 16)
        else false
  | 0, b, _ => by simp [mapLanes]
  | n + 1, b, hb => by
    have ih := mapLanes_16_getLsbD v f n b hb
    have hm16 : laneMask 16 = 65535#128 := rfl
    simp only [mapLanes, BitVec.getLsbD_or, ih, BitVec.getLsbD_shiftLeft, hb, decide_true,
      Bool.true_and, BitVec.getLsbD_and, hm16]
    by_cases hbn : b < 16 * n
    · have hlt : b < n * 16 := by omega
      have hbn1 : b < 16 * (n + 1) := by omega
      simp [hbn, hlt, hbn1]
    · by_cases hbn1 : b < 16 * (n + 1)
      · have hnlt : ¬ (b < n * 16) := by omega
        have hdiv : b / 16 = n := by omega
        have hsub : b - n * 16 = b % 16 := by omega
        have hmod_lt : b % 16 < 16 := by omega
        have hin : (v >>> (n * 16) &&& 65535#128) =
            (v.extractLsb' (16 * n) 16).zeroExtend 128 := by
          simpa [getSimdLane, lane16] using getSimdLane_16_eq v ⟨n, by omega⟩
        simp [hbn, hbn1, hnlt, hdiv, hsub, getLsbD_65535_128, hmod_lt, hin]
      · have hnlt : ¬ (b < n * 16) := by omega
        have hsub_ge : ¬ (b - n * 16 < 16) := by omega
        simp [hbn, hbn1, hnlt, getLsbD_65535_128, hsub_ge]

@[simp] theorem lane16_mapLanes_8 (v : BitVec 128) (f : BitVec 128 → BitVec 128) (i : Fin 8) :
    lane16 (mapLanes 16 v f 8) i = (f ((lane16 v i).zeroExtend 128)).truncate 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hpos : 16 * i.val + b < 128 := by omega
  have hdiv : (16 * i.val + b) / 16 = i.val := by omega
  have hmod : (16 * i.val + b) % 16 = b := by omega
  simp only [lane16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hb, decide_true,
    Bool.true_and, mapLanes_16_getLsbD v f 8 _ hpos, hpos, hdiv, hmod, ↓reduceIte]

@[simp] theorem lane16_mapSimdLanes_true_16 (v : BitVec 128) (f : BitVec 128 → BitVec 128)
    (i : Fin 8) :
    lane16 (mapSimdLanes true 16 v f) i = (f ((lane16 v i).zeroExtend 128)).truncate 16 := by
  rw [mapSimdLanes_true_16, lane16_mapLanes_8]

private theorem zipLanes_16_getLsbD (vn vm : BitVec 128)
    (f : BitVec 128 → BitVec 128 → BitVec 128) :
    ∀ (n b : Nat), b < 128 →
      (zipLanes 16 vn vm f n).getLsbD b =
        if b < 16 * n then
          (f ((vn.extractLsb' (16 * (b / 16)) 16).zeroExtend 128)
             ((vm.extractLsb' (16 * (b / 16)) 16).zeroExtend 128)).getLsbD (b % 16)
        else false
  | 0, b, _ => by simp [zipLanes]
  | n + 1, b, hb => by
    have ih := zipLanes_16_getLsbD vn vm f n b hb
    have hm16 : laneMask 16 = 65535#128 := rfl
    simp only [zipLanes, BitVec.getLsbD_or, ih, BitVec.getLsbD_shiftLeft, hb, decide_true,
      Bool.true_and, BitVec.getLsbD_and, hm16]
    by_cases hbn : b < 16 * n
    · have hlt : b < n * 16 := by omega
      have hbn1 : b < 16 * (n + 1) := by omega
      simp [hbn, hlt, hbn1]
    · by_cases hbn1 : b < 16 * (n + 1)
      · have hnlt : ¬ (b < n * 16) := by omega
        have hdiv : b / 16 = n := by omega
        have hsub : b - n * 16 = b % 16 := by omega
        have hmod_lt : b % 16 < 16 := by omega
        have hin1 : (vn >>> (n * 16) &&& 65535#128) =
            (vn.extractLsb' (16 * n) 16).zeroExtend 128 := by
          simpa [getSimdLane, lane16] using getSimdLane_16_eq vn ⟨n, by omega⟩
        have hin2 : (vm >>> (n * 16) &&& 65535#128) =
            (vm.extractLsb' (16 * n) 16).zeroExtend 128 := by
          simpa [getSimdLane, lane16] using getSimdLane_16_eq vm ⟨n, by omega⟩
        simp [hbn, hbn1, hnlt, hdiv, hsub, getLsbD_65535_128, hmod_lt, hin1, hin2]
      · have hnlt : ¬ (b < n * 16) := by omega
        have hsub_ge : ¬ (b - n * 16 < 16) := by omega
        simp [hbn, hbn1, hnlt, getLsbD_65535_128, hsub_ge]

@[simp] theorem lane16_zipLanes_8 (vn vm : BitVec 128)
    (f : BitVec 128 → BitVec 128 → BitVec 128) (i : Fin 8) :
    lane16 (zipLanes 16 vn vm f 8) i =
      (f ((lane16 vn i).zeroExtend 128) ((lane16 vm i).zeroExtend 128)).truncate 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hpos : 16 * i.val + b < 128 := by omega
  have hdiv : (16 * i.val + b) / 16 = i.val := by omega
  have hmod : (16 * i.val + b) % 16 = b := by omega
  simp only [lane16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hb, decide_true,
    Bool.true_and, zipLanes_16_getLsbD vn vm f 8 _ hpos, hpos, hdiv, hmod, ↓reduceIte]

@[simp] theorem lane16_zipSimdLanes_true_16 (vn vm : BitVec 128)
    (f : BitVec 128 → BitVec 128 → BitVec 128) (i : Fin 8) :
    lane16 (zipSimdLanes true 16 vn vm f) i =
      (f ((lane16 vn i).zeroExtend 128) ((lane16 vm i).zeroExtend 128)).truncate 16 := by
  rw [zipSimdLanes_true_16, lane16_zipLanes_8]

/-! ## 3. 32-Vector Polynomial Representation (`PolyVec128`, `vec128ToPoly16`) -/

@[expose] def PolyVec128 (p : Poly16) (vIdx : Fin 32) : BitVec 128 :=
  pack8x16 fun lane => p.getD (8 * vIdx.val + lane.val) 0#16
@[expose] def vec128ToPoly16 (vecs : Fin 32 → BitVec 128) : Poly16 :=
  Array.ofFn (n := 256) fun ⟨idx, _⟩ => lane16 (vecs ⟨idx / 8, by omega⟩) ⟨idx % 8, by omega⟩

@[simp] theorem vec128ToPoly16_size (vecs : Fin 32 → BitVec 128) :
    (vec128ToPoly16 vecs).size = 256 := by simp [vec128ToPoly16]
@[simp] theorem lane16_polyVec128 (p : Poly16) (vIdx : Fin 32) (lane : Fin 8) :
    lane16 (PolyVec128 p vIdx) lane = p.getD (8 * vIdx.val + lane.val) 0#16 := by simp [PolyVec128]

theorem getD_vec128ToPoly16 (vecs : Fin 32 → BitVec 128) (idx : Nat) (h : idx < 256) :
    (vec128ToPoly16 vecs).getD idx 0#16 =
      lane16 (vecs ⟨idx / 8, by omega⟩) ⟨idx % 8, by omega⟩ := by
  simp [vec128ToPoly16, Array.getD, h]

@[simp] theorem polyVec128_vec128ToPoly16 (vecs : Fin 32 → BitVec 128) :
    PolyVec128 (vec128ToPoly16 vecs) = vecs := by
  funext vIdx; apply ext_lane16; intro lane
  rw [lane16_polyVec128, getD_vec128ToPoly16 _ _ (by omega)]
  have hv : (⟨(8 * vIdx.val + lane.val) / 8, by omega⟩ : Fin 32) = vIdx := by
    apply Fin.ext; dsimp; omega
  have hl : (⟨(8 * vIdx.val + lane.val) % 8, by omega⟩ : Fin 8) = lane := by
    apply Fin.ext; dsimp; omega
  rw [hv, hl]

theorem vec128ToPoly16_polyVec128 {p : Poly16} (hp : p.size = 256) :
    vec128ToPoly16 (PolyVec128 p) = p := by
  apply Array.ext
  · rw [vec128ToPoly16_size, hp]
  · intro idx h1 h2
    simp only [vec128ToPoly16, Array.getElem_ofFn, lane16_polyVec128]
    have hidx : 8 * (idx / 8) + idx % 8 = idx := by omega
    simp [hidx, Array.getD, h2]

theorem getLsbD_readLE (bs : List (BitVec 8)) (off : Nat) :
    ∀ (n k : Nat), k < 64 →
      (ByteSlice.readLE bs off n).getLsbD k =
        if k < 8 * n then (bs.getD (off + k / 8) 0#8).getLsbD (k % 8) else false
  | 0, k, _ => by simp
  | n + 1, k, hk => by
    rw [ByteSlice.readLE_succ, BitVec.getLsbD_or, getLsbD_readLE bs off n k hk,
      BitVec.getLsbD_shiftLeft]
    by_cases hkn : k < 8 * n
    · have hkn1 : k < 8 * (n + 1) := by omega
      simp [hkn, hkn1]
    · by_cases hkn1 : k < 8 * (n + 1)
      · have hdiv : k / 8 = n := by omega
        have hsub : k - 8 * n = k % 8 := by omega
        have hmod64 : k % 8 < 64 := by omega
        simp [hkn, hkn1, hk, hdiv, hsub, hmod64]
      · have hge8 : 8 ≤ k - 8 * n := by omega
        simp [hkn, hkn1, hk, BitVec.getLsbD_of_ge _ _ hge8]

theorem extractLsb16_readLE_8 (bs : List (BitVec 8)) (off j : Nat) (hj : j < 4) :
    (ByteSlice.readLE bs off 8).extractLsb' (16 * j) 16 =
      (bs.getD (off + 2 * j) 0#8).zeroExtend 16 |||
      ((bs.getD (off + 2 * j + 1) 0#8).zeroExtend 16 <<< 8) := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hk : 16 * j + b < 64 := by omega
  rw [BitVec.getLsbD_extractLsb', getLsbD_readLE bs off 8 (16 * j + b) hk]
  by_cases hb8 : b < 8
  · have hdiv : (16 * j + b) / 8 = 2 * j := by omega
    have hmod : (16 * j + b) % 8 = b := by omega
    simp [hb, hk, hb8, hdiv, hmod]
  · have hdiv : (16 * j + b) / 8 = 2 * j + 1 := by omega
    have hmod : (16 * j + b) % 8 = b - 8 := by omega
    have hge8 : 8 ≤ b := by omega
    have hidx : off + (2 * j + 1) = off + 2 * j + 1 := by omega
    simp [hb, hk, hb8, hdiv, hmod, hidx, BitVec.getLsbD_of_ge _ b hge8]

private theorem array_toArray_getD (bs : List (BitVec 8)) (k : Nat) (d : BitVec 8) :
    bs.toArray.getD k d = bs.getD k d := by
  by_cases hk : k < bs.length <;> simp [Array.getD, List.getD_eq_getElem?_getD, hk]

private theorem getD_ofFn_256 {α : Type} (f : Fin 256 → α) (idx : Nat) (d : α) (h : idx < 256) :
    (Array.ofFn f).getD idx d = f ⟨idx, h⟩ := by
  simp [Array.getD, h]

theorem polyVec128_bytesToPoly16 (bs : List (BitVec 8)) (vIdx : Fin 32) :
    PolyVec128 (bytesToPoly16 bs) vIdx =
      ByteSlice.readLE bs (16 * vIdx.val + 8) 8 ++ ByteSlice.readLE bs (16 * vIdx.val) 8 := by
  apply ext_lane16; intro lane
  rw [lane16_polyVec128]
  have hlt : 8 * vIdx.val + lane.val < 256 := by omega
  have hget : (bytesToPoly16 bs).getD (8 * vIdx.val + lane.val) 0#16 =
      (bs.getD (2 * (8 * vIdx.val + lane.val)) 0#8).zeroExtend 16 |||
      ((bs.getD (2 * (8 * vIdx.val + lane.val) + 1) 0#8).zeroExtend 16 <<< 8) := by
    unfold bytesToPoly16
    rw [getD_ofFn_256 _ _ _ hlt]
    dsimp only
    rw [array_toArray_getD, array_toArray_getD]
  rw [hget]
  by_cases h4 : lane.val < 4
  · rw [lane16_append64_lo _ _ _ h4, extractLsb16_readLE_8 _ _ _ h4]
    have h0 : 2 * (8 * vIdx.val + lane.val) = 16 * vIdx.val + 2 * lane.val := by omega
    have h1 : 2 * (8 * vIdx.val + lane.val) + 1 = 16 * vIdx.val + 2 * lane.val + 1 := by omega
    rw [h1, h0]
  · have hge : 4 ≤ lane.val := by omega
    have hlt4 : lane.val - 4 < 4 := by omega
    rw [lane16_append64_hi _ _ _ hge, extractLsb16_readLE_8 _ _ _ hlt4]
    have h0 : 2 * (8 * vIdx.val + lane.val) = (16 * vIdx.val + 8) + 2 * (lane.val - 4) := by omega
    have h1 : 2 * (8 * vIdx.val + lane.val) + 1 =
        (16 * vIdx.val + 8) + 2 * (lane.val - 4) + 1 := by omega
    rw [h1, h0]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16

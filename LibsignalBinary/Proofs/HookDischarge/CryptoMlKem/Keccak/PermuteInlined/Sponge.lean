/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round

/-!
# Sponge absorb, multi-rate padding, and squeeze bridges

Byte/lane, padding, and sponge-folding lemmas shared by the Keccak proofs:
- Byte/lane bridges: `readLE_8_eq_packLane64`, `readLE_8_eq_packLane64_slice`,
  `unpack64_eq_unpackLane64`, `pointsTo64_eq_unpackLane64`, 32/64/128-byte cell-to-slice mergers
  (`pointsTo64_4_eq_bytes`, `pointsTo64_8_eq_bytes`, `pointsTo64_16_eq_bytes`), and
  `memRegion32_cells`, `memRegion64_cells`, `memRegion128_cells`.
- Hardware `UMULH` division by `136` (`umulh_div136_nat`, `umulh_div136_bv` for `n < 2 ^ 32`).
- Stack pad-buffer construction equivalence (`keccakPadBuf_eq_lastBlock`) and multi-block absorb
  folding (`keccakAbsorbPrefix17`, `keccakAbsorb_17_eq`, `keccakAbsorb_9_lt72`).
- Squeeze output characterizations for `sha3_256List`, `sha3_512List`, and `shake256List`
  (`outLen = 32` and `outLen = 128`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakAbsorb
  keccakAbsorbBlock
  keccakExtractRate
  keccakF1600
  keccakPadBlocks
  keccakSponge
  keccakSqueezeBlocks
  keccakZeroState
  packLane64
  sha3_256List
  sha3_512List
  shake256List
  unpackLane64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  keccakXorRate17
  keccakXorRate9
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakF1600_size
)

/-! ## Little-endian `ByteSlice.readLE` ↔ `packLane64` and `unpack64` ↔ `unpackLane64` -/

theorem readLE_8_eq_packLane64 (bs : List (BitVec 8)) (off : Nat) :
    ByteSlice.readLE bs off 8 = packLane64 bs off := by
  simp only [ByteSlice.readLE, packLane64, Nat.mul_zero, Nat.add_zero,
    BitVec.shiftLeft_zero, BitVec.zero_or]

private theorem getD_drop_take_byte (bs : List (BitVec 8)) (baseOff rateBytes off : Nat)
    (hoff : off < rateBytes) :
    ((bs.drop baseOff).take rateBytes).getD off 0#8 = bs.getD (baseOff + off) 0#8 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hoff]

theorem readLE_8_eq_packLane64_slice (bs : List (BitVec 8)) (baseOff rateBytes k : Nat)
    (hk : 8 * k + 8 ≤ rateBytes := by omega) :
    ByteSlice.readLE bs (baseOff + 8 * k) 8 =
      packLane64 ((bs.drop baseOff).take rateBytes) (8 * k) := by
  rw [readLE_8_eq_packLane64]
  unfold packLane64
  have g (j : Nat) (hj : j < 8) :
      bs.getD (baseOff + 8 * k + j) 0#8 =
        ((bs.drop baseOff).take rateBytes).getD (8 * k + j) 0#8 := by
    rw [getD_drop_take_byte bs baseOff rateBytes (8 * k + j) (by omega)]
    congr 1
    omega
  rw [show bs.getD (baseOff + 8 * k) 0#8 = bs.getD (baseOff + 8 * k + 0) 0#8 by simp,
      g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide),
      g 4 (by decide), g 5 (by decide), g 6 (by decide), g 7 (by decide),
      Nat.add_zero]

theorem unpack64_eq_unpackLane64 (w : BitVec 64) :
    unpack64 w = unpackLane64 w := by
  unfold unpack64 unpackLane64
  have h (k : Nat) : w.extractLsb' k 8 = (w >>> k).truncate 8 := by
    ext i hi
    simp [BitVec.getElem_extractLsb', BitVec.getLsbD_ushiftRight]
  simp only [h]

theorem pointsTo64_eq_unpackLane64 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) = (a ↦ₛ unpackLane64 w) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_eq_unpackLane64]

@[simp] theorem unpackLane64_length (w : BitVec 64) :
    (unpackLane64 w).length = 8 := rfl

/-! ## 32 / 64 / 128-byte `pointsTo64` ↔ `pointsToBytes` and `memRegion` splitters -/

theorem pointsTo64_4_eq_bytes (a w0 w1 w2 w3 : BitVec 64) :
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
     (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) =
      (a ↦ₛ (unpackLane64 w0 ++ unpackLane64 w1 ++ unpackLane64 w2 ++ unpackLane64 w3)) := by
  simp only [pointsTo64_eq_unpackLane64, pointsToBytes_append, List.length_append,
    unpackLane64_length]
  sep_eq

theorem pointsTo64_8_eq_bytes (a w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    ((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
      (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ∗
     ((((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗
      (((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)))) =
      (a ↦ₛ (unpackLane64 w0 ++ unpackLane64 w1 ++ unpackLane64 w2 ++ unpackLane64 w3 ++
             unpackLane64 w4 ++ unpackLane64 w5 ++ unpackLane64 w6 ++ unpackLane64 w7)) := by
  have h2 :
      ((((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗
       (((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7))) =
        ((a + 32#64) ↦ₛ (unpackLane64 w4 ++ unpackLane64 w5 ++ unpackLane64 w6 ++ unpackLane64 w7)) := by
    rw [show a + 40#64 = (a + 32#64) + 8#64 by bv_omega,
        show a + 48#64 = (a + 32#64) + 16#64 by bv_omega,
        show a + 56#64 = (a + 32#64) + 24#64 by bv_omega]
    exact pointsTo64_4_eq_bytes (a + 32#64) w4 w5 w6 w7
  rw [pointsTo64_4_eq_bytes a w0 w1 w2 w3, h2]
  have happ :
      unpackLane64 w0 ++ unpackLane64 w1 ++ unpackLane64 w2 ++ unpackLane64 w3 ++
        unpackLane64 w4 ++ unpackLane64 w5 ++ unpackLane64 w6 ++ unpackLane64 w7 =
      (unpackLane64 w0 ++ unpackLane64 w1 ++ unpackLane64 w2 ++ unpackLane64 w3) ++
        (unpackLane64 w4 ++ unpackLane64 w5 ++ unpackLane64 w6 ++ unpackLane64 w7) := by
    simp only [List.append_assoc]
  symm
  rw [happ, pointsToBytes_append]
  simp only [List.length_append, unpackLane64_length]

theorem pointsTo64_16_eq_bytes
    (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    (((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
       (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ∗
      ((((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗
       (((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)))) ∗
     (((((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9)) ∗
       (((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11))) ∗
      ((((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13)) ∗
       (((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15))))) =
      (a ↦ₛ (unpackLane64 w0 ++ unpackLane64 w1 ++ unpackLane64 w2 ++ unpackLane64 w3 ++
             unpackLane64 w4 ++ unpackLane64 w5 ++ unpackLane64 w6 ++ unpackLane64 w7 ++
             unpackLane64 w8 ++ unpackLane64 w9 ++ unpackLane64 w10 ++ unpackLane64 w11 ++
             unpackLane64 w12 ++ unpackLane64 w13 ++ unpackLane64 w14 ++ unpackLane64 w15)) := by
  have h2 :
      (((((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9)) ∗
        (((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11))) ∗
       ((((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13)) ∗
        (((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15)))) =
        ((a + 64#64) ↦ₛ (unpackLane64 w8 ++ unpackLane64 w9 ++ unpackLane64 w10 ++ unpackLane64 w11 ++
                         unpackLane64 w12 ++ unpackLane64 w13 ++ unpackLane64 w14 ++ unpackLane64 w15)) := by
    rw [show a + 72#64 = (a + 64#64) + 8#64 by bv_omega,
        show a + 80#64 = (a + 64#64) + 16#64 by bv_omega,
        show a + 88#64 = (a + 64#64) + 24#64 by bv_omega,
        show a + 96#64 = (a + 64#64) + 32#64 by bv_omega,
        show a + 104#64 = (a + 64#64) + 40#64 by bv_omega,
        show a + 112#64 = (a + 64#64) + 48#64 by bv_omega,
        show a + 120#64 = (a + 64#64) + 56#64 by bv_omega]
    exact pointsTo64_8_eq_bytes (a + 64#64) w8 w9 w10 w11 w12 w13 w14 w15
  rw [pointsTo64_8_eq_bytes a w0 w1 w2 w3 w4 w5 w6 w7, h2]
  have happ :
      unpackLane64 w0 ++ unpackLane64 w1 ++ unpackLane64 w2 ++ unpackLane64 w3 ++
        unpackLane64 w4 ++ unpackLane64 w5 ++ unpackLane64 w6 ++ unpackLane64 w7 ++
        unpackLane64 w8 ++ unpackLane64 w9 ++ unpackLane64 w10 ++ unpackLane64 w11 ++
        unpackLane64 w12 ++ unpackLane64 w13 ++ unpackLane64 w14 ++ unpackLane64 w15 =
      (unpackLane64 w0 ++ unpackLane64 w1 ++ unpackLane64 w2 ++ unpackLane64 w3 ++
       unpackLane64 w4 ++ unpackLane64 w5 ++ unpackLane64 w6 ++ unpackLane64 w7) ++
      (unpackLane64 w8 ++ unpackLane64 w9 ++ unpackLane64 w10 ++ unpackLane64 w11 ++
       unpackLane64 w12 ++ unpackLane64 w13 ++ unpackLane64 w14 ++ unpackLane64 w15) := by
    simp only [List.append_assoc]
  symm
  rw [happ, pointsToBytes_append]
  simp only [List.length_append, unpackLane64_length]

/-- View `memRegion a 32` in a `SepWP` precondition as four 64-bit cells (`a`, `a+8`, `a+16`, `a+24`). -/
theorem memRegion32_cells {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64)
    (hf : P = memRegion a 32 ∗ F := by sep_focus)
    (h : ∀ w0 w1 w2 w3 : BitVec 64,
      SepWP prog target_pc s
        ((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
          (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hf,
      show memRegion a 32 = memRegion a 16 ∗ memRegion (a + 16#64) 16 from
        memRegion_split a 16 16 (by decide),
      show memRegion a 16 = memRegion a 8 ∗ memRegion (a + 8#64) 8 from
        memRegion_split a 8 8 (by decide),
      show memRegion (a + 16#64) 16 = memRegion (a + 16#64) 8 ∗ memRegion ((a + 16#64) + 8#64) 8 from
        memRegion_split (a + 16#64) 8 8 (by decide),
      show (a + 16#64) + 8#64 = a + 24#64 by bv_omega]
  refine SepWP.memRegion8_cell a fun w0 => ?_
  refine SepWP.memRegion8_cell (a + 8#64) fun w1 => ?_
  refine SepWP.memRegion8_cell (a + 16#64) fun w2 => ?_
  refine SepWP.memRegion8_cell (a + 24#64) fun w3 => ?_
  exact SepWP.congr_pre (by sep_eq) (h w0 w1 w2 w3)

/-- View `memRegion a 64` in a `SepWP` precondition as eight 64-bit cells (`a .. a+56`). -/
theorem memRegion64_cells {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64)
    (hf : P = memRegion a 64 ∗ F := by sep_focus)
    (h : ∀ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64,
      SepWP prog target_pc s
        (((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
           (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ∗
          ((((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗
           (((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)))) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hf, show memRegion a 64 = memRegion a 32 ∗ memRegion (a + 32#64) 32 from
    memRegion_split a 32 32 (by decide)]
  refine memRegion32_cells a (by sep_focus) fun w0 w1 w2 w3 => ?_
  refine memRegion32_cells (a + 32#64) (by sep_focus) fun w4 w5 w6 w7 => ?_
  rw [show (a + 32#64) + 8#64 = a + 40#64 by bv_omega,
      show (a + 32#64) + 16#64 = a + 48#64 by bv_omega,
      show (a + 32#64) + 24#64 = a + 56#64 by bv_omega]
  exact SepWP.congr_pre (by sep_eq) (h w0 w1 w2 w3 w4 w5 w6 w7)

/-- View `memRegion a 128` in a `SepWP` precondition as sixteen 64-bit cells (`a .. a+120`). -/
theorem memRegion128_cells {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64)
    (hf : P = memRegion a 128 ∗ F := by sep_focus)
    (h : ∀ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64,
      SepWP prog target_pc s
        ((((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
            (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ∗
           ((((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗
            (((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)))) ∗
          (((((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9)) ∗
            (((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11))) ∗
           ((((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13)) ∗
            (((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15))))) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hf, show memRegion a 128 = memRegion a 64 ∗ memRegion (a + 64#64) 64 from
    memRegion_split a 64 64 (by decide)]
  refine memRegion64_cells a (by sep_focus) fun w0 w1 w2 w3 w4 w5 w6 w7 => ?_
  refine memRegion64_cells (a + 64#64) (by sep_focus)
    fun w8 w9 w10 w11 w12 w13 w14 w15 => ?_
  rw [show (a + 64#64) + 8#64 = a + 72#64 by bv_omega,
      show (a + 64#64) + 16#64 = a + 80#64 by bv_omega,
      show (a + 64#64) + 24#64 = a + 88#64 by bv_omega,
      show (a + 64#64) + 32#64 = a + 96#64 by bv_omega,
      show (a + 64#64) + 40#64 = a + 104#64 by bv_omega,
      show (a + 64#64) + 48#64 = a + 112#64 by bv_omega,
      show (a + 64#64) + 56#64 = a + 120#64 by bv_omega]
  exact SepWP.congr_pre (by sep_eq)
    (h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)

/-! ## Hardware `UMULH` division by `136` (`B01`, `B02`) -/

/-- `(n * 0xf0f0f0f0f0f0f0f1) >>> 71 = n / 136` for all `n < 2 ^ 32`. -/
theorem umulh_div136_nat {n : Nat} (hn : n < 2 ^ 32) :
    (n * 0xf0f0f0f0f0f0f0f1 / 2 ^ 64) / 2 ^ 7 = n / 136 := by
  have hdiv : (n * 0xf0f0f0f0f0f0f0f1 / 2 ^ 64) / 2 ^ 7 = n * 0xf0f0f0f0f0f0f0f1 / 2 ^ 71 :=
    Nat.div_div_eq_div_mul _ _ _
  rw [hdiv]
  omega

/-- BitVec form matching `umulh x8, x22, 0xf0f0f0f0f0f0f0f1; lsr x23, x8, #7`. -/
theorem umulh_div136_bv {n : Nat} (hn : n < 2 ^ 32) :
    BitVec.ofNat 64 ((n * (0xf0f0f0f0f0f0f0f1#64).toNat) / 2 ^ 64) >>> 7 =
      BitVec.ofNat 64 (n / 136) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : n * (0xf0f0f0f0f0f0f0f1#64).toNat / 2 ^ 64 < 2 ^ 64 := by
    have : (0xf0f0f0f0f0f0f0f1#64).toNat = 0xf0f0f0f0f0f0f0f1 := rfl
    rw [this]; omega
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.shiftRight_eq_div_pow, show (0xf0f0f0f0f0f0f0f1#64).toNat = 0xf0f0f0f0f0f0f0f1 from rfl,
      umulh_div136_nat hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## Multi-rate padding and sponge absorb fold (`rate = 136` and `rate = 72`) -/

/-- Final `rateBytes`-byte padded block of `keccakPadBlocks rateBytes dsByte msg`. -/
@[expose] def keccakLastBlock (rateBytes : Nat) (dsByte : BitVec 8) (msg : List (BitVec 8)) :
    List (BitVec 8) :=
  let fullCount := msg.length / rateBytes
  let remLen := msg.length % rateBytes
  let tailBytes := msg.drop (fullCount * rateBytes)
  (List.range rateBytes).map fun j =>
    let base : BitVec 8 :=
      if j < remLen then tailBytes.getD j 0#8
      else if j == remLen then dsByte
      else 0#8
    if j == rateBytes - 1 then base ^^^ 0x80#8 else base

theorem keccakLastBlock_length (rateBytes : Nat) (dsByte : BitVec 8) (msg : List (BitVec 8)) :
    (keccakLastBlock rateBytes dsByte msg).length = rateBytes := by
  simp [keccakLastBlock]

/-- Stack pad-buffer sequence (`tail ++ replicate (rateBytes - remLen) 0`, write `dsByte` at
    `remLen`, then `|||` `0x80` into byte `rateBytes - 1`) equals `keccakLastBlock`. -/
theorem keccakPadBuf_eq_lastBlock {rateBytes : Nat} (dsByte : BitVec 8) (msg : List (BitVec 8))
    (hrate : 0 < rateBytes) (hds : dsByte &&& 0x80#8 = 0#8) :
    let fullCount := msg.length / rateBytes
    let remLen := msg.length % rateBytes
    let tail := msg.drop (fullCount * rateBytes)
    let buf0 := tail ++ List.replicate (rateBytes - remLen) 0#8
    let buf1 := ByteSlice.write8 buf0 remLen dsByte
    ByteSlice.write8 buf1 (rateBytes - 1) (buf1.getD (rateBytes - 1) 0#8 ||| 0x80#8) =
      keccakLastBlock rateBytes dsByte msg := by
  have hrem_lt : msg.length % rateBytes < rateBytes := Nat.mod_lt _ hrate
  have htail_len : (msg.drop (msg.length / rateBytes * rateBytes)).length =
      msg.length % rateBytes := by
    rw [List.length_drop, Nat.mul_comm]
    have hdiv := Nat.div_add_mod msg.length rateBytes
    omega
  set fullCount := msg.length / rateBytes
  set remLen := msg.length % rateBytes
  set tail := msg.drop (fullCount * rateBytes)
  set buf0 := tail ++ List.replicate (rateBytes - remLen) 0#8
  have hlen0 : buf0.length = rateBytes := by
    simp only [buf0, List.length_append, List.length_replicate, htail_len]
    omega
  set buf1 := ByteSlice.write8 buf0 remLen dsByte
  have hlen1 : buf1.length = rateBytes := by
    unfold buf1 ByteSlice.write8
    rw [ByteSlice.write_length buf0 [dsByte] remLen (by simp [hlen0]; omega), hlen0]
  set buf2 := ByteSlice.write8 buf1 (rateBytes - 1) (buf1.getD (rateBytes - 1) 0#8 ||| 0x80#8)
  have hlen2 : buf2.length = rateBytes := by
    unfold buf2 ByteSlice.write8
    rw [ByteSlice.write_length buf1 [_] (rateBytes - 1) (by simp [hlen1]; omega), hlen1]
  have hor_xor (b : BitVec 8) (hb : b &&& 0x80#8 = 0#8) : b ||| 0x80#8 = b ^^^ 0x80#8 := by
    ext i hi
    have hbi := congrArg (fun x => x[i]) hb
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hbi
    simp only [BitVec.getElem_or, BitVec.getElem_xor]
    cases h1 : b[i] <;> cases h2 : (0x80#8)[i] <;> simp_all
  apply ByteSlice.ext_getD (hlen2.trans (keccakLastBlock_length rateBytes dsByte msg).symm)
  intro j hj
  rw [hlen2] at hj
  have hbuf1_at (k : Nat) (hk : k < rateBytes) :
      buf1.getD k 0#8 =
        if k < remLen then tail.getD k 0#8
        else if k == remLen then dsByte
        else 0#8 := by
    rw [ByteSlice.getD_write8 buf0 remLen dsByte k 0#8 (by omega)]
    by_cases hk1 : k < remLen
    · have hne : k ≠ remLen := by omega
      simp only [hne, ↓reduceIte, hk1, buf0, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega : k < tail.length)]
    · by_cases hk2 : k = remLen
      · subst hk2; simp
      · have hbeq : (k == remLen) = false := beq_false_of_ne hk2
        simp only [hk2, ↓reduceIte, hk1, hbeq, Bool.false_eq_true, buf0,
          List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega : tail.length ≤ k),
          List.getElem?_replicate, show k - tail.length < rateBytes - remLen by omega,
          Option.getD_some]
  have hrhs : (keccakLastBlock rateBytes dsByte msg).getD j 0#8 =
      (let base := if j < remLen then tail.getD j 0#8 else if j == remLen then dsByte else 0#8
       if j == rateBytes - 1 then base ^^^ 0x80#8 else base) := by
    simp [keccakLastBlock, List.getD_eq_getElem?_getD, hj, fullCount, remLen, tail]
  rw [hrhs]
  dsimp only [buf2]
  rw [ByteSlice.getD_write8 buf1 (rateBytes - 1) _ j 0#8 (by omega)]
  by_cases hjlast : j = rateBytes - 1
  · subst hjlast
    simp only [↓reduceIte, beq_self_eq_true, hbuf1_at (rateBytes - 1) (by omega)]
    apply hor_xor
    by_cases hlt : rateBytes - 1 < remLen
    · omega
    · simp only [hlt, ↓reduceIte]
      by_cases heq : (rateBytes - 1 == remLen) = true
      · simp [heq, hds]
      · simp [heq]
  · have hbeq : (j == rateBytes - 1) = false := beq_false_of_ne hjlast
    simp only [hjlast, ↓reduceIte, hbeq, Bool.false_eq_true, hbuf1_at j hj]

theorem keccakAbsorbBlock_17 (s : KeccakState) (blk : List (BitVec 8)) :
    keccakAbsorbBlock 17 s blk = keccakF1600 (keccakXorRate17 s blk) := rfl

theorem keccakAbsorbBlock_9 (s : KeccakState) (blk : List (BitVec 8)) :
    keccakAbsorbBlock 9 s blk = keccakF1600 (keccakXorRate9 s blk) := rfl

/-- State after absorbing the first `k` full 136-byte blocks of `msg`. -/
@[expose] def keccakAbsorbPrefix17 (msg : List (BitVec 8)) : Nat → KeccakState
  | 0 => keccakZeroState
  | k + 1 =>
    keccakF1600 (keccakXorRate17 (keccakAbsorbPrefix17 msg k) ((msg.drop (k * 136)).take 136))

theorem keccakAbsorbPrefix17_size (msg : List (BitVec 8)) :
    ∀ k, (keccakAbsorbPrefix17 msg k).size = 25
  | 0 => rfl
  | _ + 1 => keccakF1600_size _

private theorem foldl_range_absorb17 (msg : List (BitVec 8)) :
    ∀ k, ((List.range k).map fun i => (msg.drop (i * 136)).take 136).foldl
        (keccakAbsorbBlock 17) keccakZeroState =
      keccakAbsorbPrefix17 msg k
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append,
        List.foldl_cons, List.foldl_nil, foldl_range_absorb17 msg k, keccakAbsorbBlock_17]
    rfl

theorem keccakAbsorb_17_eq (dsByte : BitVec 8) (msg : List (BitVec 8)) :
    keccakAbsorb 17 dsByte msg =
      keccakF1600 (keccakXorRate17 (keccakAbsorbPrefix17 msg (msg.length / 136))
        (keccakLastBlock 136 dsByte msg)) := by
  unfold keccakAbsorb keccakPadBlocks
  change (((List.range (msg.length / 136)).map fun i => (msg.drop (i * 136)).take 136) ++
      [keccakLastBlock 136 dsByte msg]).foldl (keccakAbsorbBlock 17) keccakZeroState = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_range_absorb17 msg (msg.length / 136), keccakAbsorbBlock_17]

theorem keccakAbsorb_9_lt72 (dsByte : BitVec 8) (msg : List (BitVec 8)) (h : msg.length < 72) :
    keccakAbsorb 9 dsByte msg =
      keccakF1600 (keccakXorRate9 keccakZeroState (keccakLastBlock 72 dsByte msg)) := by
  unfold keccakAbsorb keccakPadBlocks
  have hdiv : msg.length / (8 * 9) = 0 := Nat.div_eq_of_lt h
  change (((List.range (msg.length / 72)).map fun i => (msg.drop (i * 72)).take 72) ++
      [keccakLastBlock 72 dsByte msg]).foldl (keccakAbsorbBlock 9) keccakZeroState = _
  rw [show msg.length / 72 = 0 from hdiv, List.range_zero, List.map_nil, List.nil_append,
      List.foldl_cons, List.foldl_nil, keccakAbsorbBlock_9]

/-! ## Squeeze output characterizations (`SHA3-256`, `SHA3-512`, `SHAKE-256`) -/

private theorem map_getD_eq_take (xs : List (BitVec 8)) (n : Nat) (hn : n ≤ xs.length) :
    ((List.range n).map fun i => xs.getD i 0#8) = xs.take n := by
  apply ByteSlice.ext_getD
  · simp [Nat.min_eq_left hn]
  · intro i hi
    simp only [List.length_map, List.length_range] at hi
    simp [List.getD_eq_getElem?_getD, hi, Nat.lt_of_lt_of_le hi hn]

theorem keccakExtractRate_length (rateLanes : Nat) (s : KeccakState) :
    (keccakExtractRate rateLanes s).length = 8 * rateLanes := by
  unfold keccakExtractRate
  induction rateLanes with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.flatten_append,
        List.flatten_singleton, List.length_append, ih, unpackLane64_length]
    omega

theorem keccakSponge_singleBlock {rateLanes outLen : Nat} (dsByte : BitVec 8)
    (msg : List (BitVec 8)) (ho_pos : 0 < outLen) (ho_le : outLen ≤ 8 * rateLanes) :
    keccakSponge rateLanes dsByte outLen msg =
      (keccakExtractRate rateLanes (keccakAbsorb rateLanes dsByte msg)).take outLen := by
  dsimp only [keccakSponge]
  have hn : (outLen + 8 * rateLanes - 1) / (8 * rateLanes) = 1 := by
    have hr : 0 < 8 * rateLanes := by omega
    rw [show outLen + 8 * rateLanes - 1 = (outLen - 1) + 8 * rateLanes by omega,
        Nat.add_div_right _ hr, Nat.div_eq_of_lt (by omega : outLen - 1 < 8 * rateLanes)]
  rw [hn]
  dsimp only [keccakSqueezeBlocks]
  exact map_getD_eq_take _ outLen (by rw [keccakExtractRate_length]; exact ho_le)

theorem keccakExtractRate_17_take_32 (s : KeccakState) :
    (keccakExtractRate 17 s).take 32 =
      unpackLane64 (s.getD 0 0#64) ++ unpackLane64 (s.getD 1 0#64) ++
        unpackLane64 (s.getD 2 0#64) ++ unpackLane64 (s.getD 3 0#64) := by
  have h17 : List.range 17 = [0, 1, 2, 3] ++ (List.range 13).map (· + 4) := by decide
  unfold keccakExtractRate
  rw [h17, List.map_append, List.flatten_append]
  set pfx := ([0, 1, 2, 3].map fun idx => unpackLane64 (s.getD idx 0#64)).flatten
  have hpfx_eq : pfx =
      unpackLane64 (s.getD 0 0#64) ++ unpackLane64 (s.getD 1 0#64) ++
        unpackLane64 (s.getD 2 0#64) ++ unpackLane64 (s.getD 3 0#64) := by
    simp [pfx, List.append_assoc]
  have hpfx_len : pfx.length = 32 := by simp [hpfx_eq]
  have htake : ∀ rest : List (BitVec 8), (pfx ++ rest).take 32 = pfx := fun rest => by
    rw [← hpfx_len, List.take_left]
  rw [htake, hpfx_eq]

theorem keccakExtractRate_17_take_128 (s : KeccakState) :
    (keccakExtractRate 17 s).take 128 =
      unpackLane64 (s.getD 0 0#64) ++ unpackLane64 (s.getD 1 0#64) ++
        unpackLane64 (s.getD 2 0#64) ++ unpackLane64 (s.getD 3 0#64) ++
        unpackLane64 (s.getD 4 0#64) ++ unpackLane64 (s.getD 5 0#64) ++
        unpackLane64 (s.getD 6 0#64) ++ unpackLane64 (s.getD 7 0#64) ++
        unpackLane64 (s.getD 8 0#64) ++ unpackLane64 (s.getD 9 0#64) ++
        unpackLane64 (s.getD 10 0#64) ++ unpackLane64 (s.getD 11 0#64) ++
        unpackLane64 (s.getD 12 0#64) ++ unpackLane64 (s.getD 13 0#64) ++
        unpackLane64 (s.getD 14 0#64) ++ unpackLane64 (s.getD 15 0#64) := by
  have h17 : List.range 17 = List.range 16 ++ [16] := rfl
  unfold keccakExtractRate
  rw [h17, List.map_append, List.flatten_append]
  set pfx := ((List.range 16).map fun idx => unpackLane64 (s.getD idx 0#64)).flatten
  have hlen : pfx.length = 128 := keccakExtractRate_length 16 s
  have htake : ∀ rest : List (BitVec 8), (pfx ++ rest).take 128 = pfx := fun rest => by
    rw [← hlen, List.take_left]
  rw [htake]
  have hr16 : List.range 16 =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := rfl
  simp only [pfx, hr16, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem keccakExtractRate_9_take_64 (s : KeccakState) :
    (keccakExtractRate 9 s).take 64 =
      unpackLane64 (s.getD 0 0#64) ++ unpackLane64 (s.getD 1 0#64) ++
        unpackLane64 (s.getD 2 0#64) ++ unpackLane64 (s.getD 3 0#64) ++
        unpackLane64 (s.getD 4 0#64) ++ unpackLane64 (s.getD 5 0#64) ++
        unpackLane64 (s.getD 6 0#64) ++ unpackLane64 (s.getD 7 0#64) := by
  have h9 : List.range 9 = List.range 8 ++ [8] := rfl
  unfold keccakExtractRate
  rw [h9, List.map_append, List.flatten_append]
  set pfx := ((List.range 8).map fun idx => unpackLane64 (s.getD idx 0#64)).flatten
  have hlen : pfx.length = 64 := keccakExtractRate_length 8 s
  have htake : ∀ rest : List (BitVec 8), (pfx ++ rest).take 64 = pfx := fun rest => by
    rw [← hlen, List.take_left]
  rw [htake]
  have hr8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [pfx, hr8, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem sha3_256List_eq_lanes (msg : List (BitVec 8)) :
    sha3_256List msg =
      let s := keccakAbsorb 17 0x06#8 msg
      unpackLane64 (s.getD 0 0#64) ++ unpackLane64 (s.getD 1 0#64) ++
        unpackLane64 (s.getD 2 0#64) ++ unpackLane64 (s.getD 3 0#64) := by
  unfold sha3_256List
  rw [keccakSponge_singleBlock 0x06#8 msg (by decide) (by decide), keccakExtractRate_17_take_32]

theorem sha3_512List_eq_lanes (msg : List (BitVec 8)) :
    sha3_512List msg =
      let s := keccakAbsorb 9 0x06#8 msg
      unpackLane64 (s.getD 0 0#64) ++ unpackLane64 (s.getD 1 0#64) ++
        unpackLane64 (s.getD 2 0#64) ++ unpackLane64 (s.getD 3 0#64) ++
        unpackLane64 (s.getD 4 0#64) ++ unpackLane64 (s.getD 5 0#64) ++
        unpackLane64 (s.getD 6 0#64) ++ unpackLane64 (s.getD 7 0#64) := by
  unfold sha3_512List
  rw [keccakSponge_singleBlock 0x06#8 msg (by decide) (by decide), keccakExtractRate_9_take_64]

theorem shake256List_eq_take_extract {outLen : Nat} (msg : List (BitVec 8))
    (hout : outLen = 32 ∨ outLen = 128) :
    shake256List outLen msg =
      (keccakExtractRate 17 (keccakAbsorb 17 0x1f#8 msg)).take outLen := by
  unfold shake256List
  rcases hout with rfl | rfl
  · exact keccakSponge_singleBlock 0x1f#8 msg (by decide) (by decide)
  · exact keccakSponge_singleBlock 0x1f#8 msg (by decide) (by decide)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge

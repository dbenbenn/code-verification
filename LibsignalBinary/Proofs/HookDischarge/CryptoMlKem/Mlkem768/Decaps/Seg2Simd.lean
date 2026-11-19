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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode10 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 2 AdvSIMD Bridges & Pure Decompress Lemmas (`Seg2Simd`)

Shared `{svc}`-polymorphic narrowing/widening AdvSIMD execution bridges (`movi.4s #512`/`#8`,
`xtn.4h`, `shrn.4h #16`, `umlal.4s`, `ushr.4s #10`/`#4`) and pure 16-chunk vector equivalences
for `deserialize_10 + decompress_10` (`Seg2a`) and `B25 deserialize_4 + decompress_4` (`Seg2c`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2Simd

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 decodeAndDecompress decompressCoeff)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup4hLow dup8x16 ext_lane16 ext_lane32 fin4_cases fin8_cases
  getSimdLane_16_eq getSimdLane_32_eq lane16 lane16_dup4hLow_lt4 lane16_dup8x16 lane16_pack8x16
  lane16_setSimdLane_16 lane32 lane32_pack4x32 pack4x32 pack8x16 simdLaneUInt_16_zeroExtend
  simdLaneUInt_32_zeroExtend truncate16_intToSimdLane_16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (lane16_simdTrn1_8h simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonPolyNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (
  decodeAndDecompress_poly16_spec neonDecompressLane16 neonDecompressLane16_spec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (byteDecodeRaw_lt_two_pow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode10 (
  deserialize10_scalar_lanes_eq lane16_neonDecompress10_eq_decodeAndDecompress neonDecompress10_8h
  neonDeserialize10Half simdShrn16_4h simdUmlal4sLow simdUshr4s simdXtn4h simdXtn4h_eq_of_even_lanes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  decodeAndDecompress_chunk_eq deserializeChunkBytes deserializeChunkCoeff
  q0_lane_deserializeChunkBytes q1_lane_deserializeChunkBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (polyVecNat)

/-! ## 1. Pure Decompressed `Poly16` Definitions & Specs -/

@[expose] def decompPoly16 (d : Nat) (bs : List (BitVec 8)) : Poly16 :=
  (decodeAndDecompress d bs).map fun c => BitVec.ofNat 16 c
@[simp] theorem decompPoly16_size (d : Nat) (bs : List (BitVec 8)) :
    (decompPoly16 d bs).size = 256 := by simp [decompPoly16, decodeAndDecompress, Spec.byteDecodeRaw]

theorem decompPoly16_spec {d : Nat} (bs : List (BitVec 8))
    (hd : d = 1 ∨ d = 4 ∨ d = 5 ∨ d = 10 ∨ d = 11) :
    PolyBounded16 3328 (decompPoly16 d bs) ∧ PolyRepresents (decompPoly16 d bs) (decodeAndDecompress d bs) := by
  have hd_lt : d < 16 := by rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide
  exact decodeAndDecompress_poly16_spec bs hd (fun i hi => byteDecodeRaw_lt_two_pow d hd_lt bs i hi)

@[expose] def uPoly16 (ct1 : List (BitVec 8)) (idx : Nat) : Poly16 :=
  decompPoly16 10 ((ct1.drop (320 * idx)).take 320)
@[expose] def uHatPoly16 (ct1 : List (BitVec 8)) (idx : Nat) : Poly16 := neonPolyNtt16 (uPoly16 ct1 idx)
@[expose] def vPoly16 (ct2 : List (BitVec 8)) : Poly16 := decompPoly16 4 ct2

/-! ## 2. `{svc}`-Polymorphic Narrowing & Widening AdvSIMD Bridges -/

private theorem writeV_adv_congr {s : State} {rd : BitVec 5} {a b : BitVec 128} (h : a = b) :
    (s.writeVReg128 rd a).advancePC = (s.writeVReg128 rd b).advancePC := h ▸ rfl

private theorem getLsbD_65535_64 (b : Nat) : (65535#64).getLsbD b = decide (b < 16) := by
  by_cases hb : b < 64
  · exact (by decide +kernel : ∀ k : Fin 64, (65535#64).getLsbD k.val = decide (k.val < 16)) ⟨b, hb⟩
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [show ¬(b < 16) by omega]

private theorem getLsbD_4294967295_128 (b : Nat) : (4294967295#128).getLsbD b = decide (b < 32) := by
  by_cases hb : b < 128
  · exact (by decide +kernel : ∀ k : Fin 128, (4294967295#128).getLsbD k.val = decide (k.val < 32)) ⟨b, hb⟩
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [show ¬(b < 32) by omega]

private theorem narrow4h_fold_getLsbD (n0 n1 n2 n3 : BitVec 64) (p : Nat) (hp : p < 64) :
    ((((0#64 ||| ((n0 &&& 65535#64) <<< 0)) ||| ((n1 &&& 65535#64) <<< 16)) |||
      ((n2 &&& 65535#64) <<< 32)) ||| ((n3 &&& 65535#64) <<< 48)).getLsbD p =
      if p < 16 then n0.getLsbD p
      else if p < 32 then n1.getLsbD (p - 16)
      else if p < 48 then n2.getLsbD (p - 32)
      else n3.getLsbD (p - 48) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
    BitVec.getLsbD_zero, Bool.false_or, hp, decide_true, Bool.true_and, Nat.sub_zero,
    getLsbD_65535_64]
  by_cases h1 : p < 16
  · simp [h1, show p < 32 by omega, show p < 48 by omega]
  · by_cases h2 : p < 32
    · simp [h1, h2, show p - 16 < 16 by omega, show p < 48 by omega]
    · by_cases h3 : p < 48
      · simp [h1, h2, h3, show ¬(p - 16 < 16) by omega, show p - 32 < 16 by omega]
      · simp [h1, h2, h3, show ¬(p - 16 < 16) by omega, show ¬(p - 32 < 16) by omega,
          show p - 48 < 16 by omega]

private theorem lane16_narrowSimdLanes_false_16 (vd vn : BitVec 128)
    (f : BitVec 128 → BitVec 128) (i : Fin 8) :
    lane16 (narrowSimdLanes false 16 vd vn f) i =
      if h : i.val < 4 then (f ((lane32 vn ⟨i.val, h⟩).zeroExtend 128)).truncate 16 else 0#16 := by
  have hg0 := getSimdLane_32_eq vn ⟨0, by decide⟩
  have hg1 := getSimdLane_32_eq vn ⟨1, by decide⟩
  have hg2 := getSimdLane_32_eq vn ⟨2, by decide⟩
  have hg3 := getSimdLane_32_eq vn ⟨3, by decide⟩
  dsimp only at hg0 hg1 hg2 hg3
  simp only [narrowSimdLanes, Bool.false_eq_true, ↓reduceIte,
    show 2 * 16 = 32 from rfl, show 64 / 16 = 4 from rfl,
    show (1#64 <<< 16 - 1#64 : BitVec 64) = 65535#64 from rfl,
    List.range, List.range.loop, List.foldl, Nat.zero_mul, Nat.one_mul,
    show 3 * 16 = 48 from rfl, hg0, hg1, hg2, hg3]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  by_cases hi4 : i.val < 4
  · have hpos : 16 * i.val + b < 64 := by omega
    simp only [hi4, ↓reduceDIte, lane16, BitVec.getLsbD_extractLsb', BitVec.truncate_eq_setWidth,
      BitVec.zeroExtend, BitVec.getLsbD_setWidth, hb, show 16 * i.val + b < 128 by omega,
      decide_true, Bool.true_and, narrow4h_fold_getLsbD _ _ _ _ _ hpos]
    rcases i with ⟨_ | _ | _ | _ | k, hk⟩
    · simp [show b < 16 by omega, show b < 64 by omega]
    · simp [show ¬(16 + b < 16) by omega, show 16 + b < 32 by omega,
        show 16 + b - 16 = b by omega, show b < 64 by omega]
    · simp [show ¬(16 * 2 + b < 16) by omega, show ¬(16 * 2 + b < 32) by omega,
        show 16 * 2 + b < 48 by omega, show 16 * 2 + b - 32 = b by omega, show b < 64 by omega]
    · simp [show ¬(16 * 3 + b < 16) by omega, show ¬(16 * 3 + b < 32) by omega,
        show ¬(16 * 3 + b < 48) by omega, show 16 * 3 + b - 48 = b by omega, show b < 64 by omega]
    · dsimp only at hi4; omega
  · have hge64 : 64 ≤ 16 * i.val + b := by omega
    simp only [hi4, ↓reduceDIte, lane16, BitVec.getLsbD_extractLsb', BitVec.zeroExtend,
      BitVec.getLsbD_setWidth, hb, show 16 * i.val + b < 128 by omega,
      decide_true, Bool.true_and, BitVec.getLsbD_zero]
    exact BitVec.getLsbD_of_ge _ _ hge64

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_4s_512 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b00100#5 2#5 rd) s =
      (s.writeVReg128 rd (pack4x32 fun _ => 512#32)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_false, Bool.true_and, decide_true, ↓reduceIte]
  exact writeV_adv_congr (by decide)

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_4s_8 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b00000#5 8#5 rd) s =
      (s.writeVReg128 rd (pack4x32 fun _ => 8#32)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_false, Bool.true_and, decide_true, ↓reduceIte]
  exact writeV_adv_congr (by decide)

@[simp, arm64_norm, wp_norm]
theorem exec_simdXtn_4h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdTwoRegMisc false false 0b01#2 0b10010#5 rn rd) s =
      (s.writeVReg128 rd (simdXtn4h (s.readVReg128 rn))).advancePC := by
  simp only [execInstWithSvc, BEq.beq, bne, Bool.not_false, Bool.true_and,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine writeV_adv_congr ?_
  change narrowSimdLanes false 16 (s.readVReg128 rd) (s.readVReg128 rn) (fun wide => wide) =
    simdXtn4h (s.readVReg128 rn)
  apply ext_lane16; intro i
  rw [lane16_narrowSimdLanes_false_16, simdXtn4h, lane16_pack8x16]
  split_ifs with h
  · apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [lane16, lane32, BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hb,
      show b < 32 by omega, show 32 * i.val + b = 16 * (2 * i.val) + b by omega]
  · rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdShrn16_4h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift false false 0b0010#4 0#3 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdShrn16_4h (s.readVReg128 rn))).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_false, Bool.true_and,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine writeV_adv_congr ?_
  change narrowSimdLanes false 16 (s.readVReg128 rd) (s.readVReg128 rn)
    (fun wide => intToSimdLane 16 (aslRShr (simdLaneUInt 32 wide) 16 false)) =
    simdShrn16_4h (s.readVReg128 rn)
  apply ext_lane16; intro i
  rw [lane16_narrowSimdLanes_false_16, simdShrn16_4h, lane16_pack8x16]
  split_ifs with h
  · set w := lane32 (s.readVReg128 rn) ⟨i.val, h⟩
    rw [simdLaneUInt_32_zeroExtend, truncate16_intToSimdLane_16]
    simp only [aslRShr, show (16 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      show Int.ofNat (1 <<< 16) = (65536 : Int) from rfl]
    have hofInt : BitVec.ofInt 16 ((w.toNat : Int) / 65536) = BitVec.ofNat 16 (w.toNat / 65536) := by
      have : ((w.toNat : Int) / 65536) = ((w.toNat / 65536 : Nat) : Int) := by omega
      rw [this]; rfl
    rw [hofInt]
    have hsh : BitVec.ofNat 16 (w.toNat / 65536) = (w >>> 16).truncate 16 := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ushiftRight, BitVec.truncate_eq_setWidth]
    rw [hsh]
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [w, lane16, lane32, BitVec.truncate_eq_setWidth, hb, show 16 + b < 32 by omega,
      show 32 * i.val + (16 + b) = 16 * (2 * i.val + 1) + b by omega]
  · rfl

private theorem wide4s_fold_getLsbD (w0 w1 w2 w3 : BitVec 32) (p : Nat) (hp : p < 128) :
    ((((0#128 ||| (w0.zeroExtend 128 <<< 0)) ||| (w1.zeroExtend 128 <<< 32)) |||
      (w2.zeroExtend 128 <<< 64)) ||| (w3.zeroExtend 128 <<< 96)).getLsbD p =
      if p < 32 then w0.getLsbD p
      else if p < 64 then w1.getLsbD (p - 32)
      else if p < 96 then w2.getLsbD (p - 64)
      else w3.getLsbD (p - 96) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.zeroExtend,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_zero, Bool.false_or, hp, decide_true,
    Bool.true_and, Nat.sub_zero]
  by_cases h1 : p < 32
  · simp [h1, show p < 64 by omega, show p < 96 by omega]
  · by_cases h2 : p < 64
    · simp [h1, h2, BitVec.getLsbD_of_ge w0 p (by omega), show p - 32 < 128 by omega,
        show p < 96 by omega]
    · by_cases h3 : p < 96
      · simp [h1, h2, h3, BitVec.getLsbD_of_ge w0 p (by omega),
          BitVec.getLsbD_of_ge w1 (p - 32) (by omega), show p - 32 < 128 by omega,
          show p - 64 < 128 by omega]
      · simp [h1, h2, h3, BitVec.getLsbD_of_ge w0 p (by omega),
          BitVec.getLsbD_of_ge w1 (p - 32) (by omega),
          BitVec.getLsbD_of_ge w2 (p - 64) (by omega),
          show p - 32 < 128 by omega, show p - 64 < 128 by omega, show p - 96 < 128 by omega]

@[simp, arm64_norm, wp_norm]
theorem exec_simdUmlal_4s_low {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeDiff false true 0b01#2 rm 0b1000#4 rn rd) s =
      (s.writeVReg128 rd
        (simdUmlal4sLow (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp only [execInstWithSvc, Bool.false_eq_true, ↓reduceIte]
  refine writeV_adv_congr ?_
  have hwide : ∀ (d : BitVec 32) (x y : BitVec 16),
      intToSimdLane 32
        (simdLaneUInt 32 (d.zeroExtend 128) +
          simdLaneUInt 16 (x.zeroExtend 128) * simdLaneUInt 16 (y.zeroExtend 128)) =
      (d + x.zeroExtend 32 * y.zeroExtend 32).zeroExtend 128 := by
    intro d x y
    rw [simdLaneUInt_32_zeroExtend, simdLaneUInt_16_zeroExtend, simdLaneUInt_16_zeroExtend]
    have hisInt : ((d.toNat : Int) + (x.toNat : Int) * (y.toNat : Int)) =
        ((d.toNat + x.toNat * y.toNat : Nat) : Int) := by push_cast; ring
    rw [hisInt]
    set sNat : Nat := d.toNat + x.toNat * y.toNat
    have hm32 : (1#128 <<< 32 - 1#128 : BitVec 128) = 4294967295#128 := rfl
    have hbv32 : (d + x.zeroExtend 32 * y.zeroExtend 32) = BitVec.ofNat 32 sNat := by
      apply BitVec.eq_of_toNat_eq
      simp only [sNat, BitVec.toNat_add, BitVec.toNat_mul, BitVec.zeroExtend,
        BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have hx32 : x.toNat % 4294967296 = x.toNat := Nat.mod_eq_of_lt (by omega)
      have hy32 : y.toNat % 4294967296 = y.toNat := Nat.mod_eq_of_lt (by omega)
      rw [hx32, hy32]; omega
    rw [hbv32]
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    rw [intToSimdLane, hm32]
    have hofInt : BitVec.ofInt 128 (sNat : Int) = BitVec.ofNat 128 sNat := rfl
    rw [hofInt, BitVec.getLsbD_and, getLsbD_4294967295_128]
    simp only [BitVec.zeroExtend, BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
      BitVec.getLsbD_ofNat]
    by_cases hb32 : b < 32
    · simp [hb32]
    · simp [hb32]
  have hg32_0 := getSimdLane_32_eq (s.readVReg128 rd) ⟨0, by decide⟩
  have hg32_1 := getSimdLane_32_eq (s.readVReg128 rd) ⟨1, by decide⟩
  have hg32_2 := getSimdLane_32_eq (s.readVReg128 rd) ⟨2, by decide⟩
  have hg32_3 := getSimdLane_32_eq (s.readVReg128 rd) ⟨3, by decide⟩
  have hg16_n := fun k hk => getSimdLane_16_eq (s.readVReg128 rn) ⟨k, hk⟩
  have hg16_m := fun k hk => getSimdLane_16_eq (s.readVReg128 rm) ⟨k, hk⟩
  dsimp only at hg32_0 hg32_1 hg32_2 hg32_3
  simp only [evalSimdThreeDiff, show (0b1000#4 == 4#4 || 0b1000#4 == 6#4) = false from rfl,
    Bool.false_eq_true, ↓reduceIte,
    show 8 <<< (0b01#2).toNat = 16 from rfl, show 2 * 16 = 32 from rfl, show 64 / 16 = 4 from rfl,
    List.range, List.range.loop, List.foldl, Nat.zero_mul,
    show 2 * 32 = 64 from rfl, show 3 * 32 = 96 from rfl, hg32_0, hg32_1, hg32_2, hg32_3,
    hg16_n 0 (by decide), hg16_n 1 (by decide), hg16_n 2 (by decide), hg16_n 3 (by decide),
    hg16_m 0 (by decide), hg16_m 1 (by decide), hg16_m 2 (by decide), hg16_m 3 (by decide), hwide]
  apply ext_lane32; intro i
  rw [simdUmlal4sLow, lane32_pack4x32]
  induction i using fin4_cases <;> {
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp only [lane32, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
    rw [wide4s_fold_getLsbD _ _ _ _ _ (by omega)]
    simp [hb, show ¬(32 * 1 + b < 32) by omega, show 32 * 1 + b < 64 by omega,
      show 32 * 1 + b - 32 = b by omega,
      show ¬(32 * 2 + b < 32) by omega, show ¬(32 * 2 + b < 64) by omega,
      show 32 * 2 + b < 96 by omega, show 32 * 2 + b - 64 = b by omega,
      show ¬(32 * 3 + b < 32) by omega, show ¬(32 * 3 + b < 64) by omega,
      show ¬(32 * 3 + b < 96) by omega, show 32 * 3 + b - 96 = b by omega]
  }

private theorem mapLanes_32_getLsbD (v : BitVec 128) (f : BitVec 128 → BitVec 128) :
    ∀ (n b : Nat), b < 128 →
      (mapLanes 32 v f n).getLsbD b =
        if b < 32 * n then
          (f ((v.extractLsb' (32 * (b / 32)) 32).zeroExtend 128)).getLsbD (b % 32)
        else false
  | 0, b, _ => by simp [mapLanes]
  | n + 1, b, hb => by
    have ih := mapLanes_32_getLsbD v f n b hb
    have hm32 : laneMask 32 = 4294967295#128 := rfl
    simp only [mapLanes, BitVec.getLsbD_or, ih, BitVec.getLsbD_shiftLeft, hb, decide_true,
      Bool.true_and, BitVec.getLsbD_and, hm32, getLsbD_4294967295_128]
    by_cases hbn : b < 32 * n
    · simp [hbn, show b < n * 32 by omega, show b < 32 * (n + 1) by omega]
    · by_cases hbn1 : b < 32 * (n + 1)
      · have hin : (v >>> (n * 32) &&& 4294967295#128) =
            (v.extractLsb' (32 * n) 32).zeroExtend 128 := by
          simpa [getSimdLane, lane32] using getSimdLane_32_eq v ⟨n, by omega⟩
        simp [hbn, hbn1, show ¬(b < n * 32) by omega, show b / 32 = n by omega,
          show b - n * 32 = b % 32 by omega, show b % 32 < 32 by omega, hin]
      · simp [hbn, hbn1, show ¬(b < n * 32) by omega, show ¬(b - n * 32 < 32) by omega]

private theorem lane32_mapSimdLanes_32 (v : BitVec 128) (f : BitVec 128 → BitVec 128) (i : Fin 4) :
    lane32 (mapSimdLanes true 32 v f) i = (f ((lane32 v i).zeroExtend 128)).truncate 32 := by
  rw [mapSimdLanes_true_32]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hpos : 32 * i.val + b < 128 := by omega
  simp only [lane32, BitVec.getLsbD_extractLsb', BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
    mapLanes_32_getLsbD v f 4 _ hpos, hpos,
    show (32 * i.val + b) / 32 = i.val by omega,
    show (32 * i.val + b) % 32 = b by omega, ↓reduceIte]

@[simp, arm64_norm, wp_norm]
theorem exec_simdUshr_4s_10 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0110#4 0b110#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdUshr4s (s.readVReg128 rn) 10)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane >>> 10) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, simdUshr4s, lane32_pack4x32]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hb, show 10 + b < 128 by omega]

@[simp, arm64_norm, wp_norm]
theorem exec_simdUshr_4s_4_op {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0111#4 0b100#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdUshr4s (s.readVReg128 rn) 4)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane >>> 4) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, simdUshr4s, lane32_pack4x32]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hb, show 4 + b < 128 by omega]

/-! ## 3. Pure `deserialize_10` + `decompress_10` & `deserialize_4` + `decompress_4` Bridges -/

@[expose] def rawGroup10Lanes (b0 b1 b2 b3 b4 : BitVec 8) :
    BitVec 32 × BitVec 16 × BitVec 16 × BitVec 16 :=
  let w0 := (evalBitfield .W32 .BFM (b0.zeroExtend 64) (b1.zeroExtend 64) 24 1).truncate 32
  let w1 := (evalBitfield .W32 .BFM
    (evalBitfield .W32 .UBFM (b1.zeroExtend 64) (b1.zeroExtend 64) 2 31)
    (b2.zeroExtend 64) 26 3).truncate 16
  let w2 := (evalBitfield .W32 .BFM
    (evalBitfield .W32 .UBFM (b2.zeroExtend 64) (b2.zeroExtend 64) 4 31)
    (b3.zeroExtend 64) 28 5).truncate 16
  let u3 := (evalBitfield .W32 .UBFM (b3.zeroExtend 64) (b3.zeroExtend 64) 6 31).truncate 32
  let w3 := (u3 ||| ((b4.zeroExtend 32) <<< 2)).truncate 16
  (w0, w1, w2, w3)

@[expose] def rawDeser10Pre7 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) : BitVec 128 :=
  let (g0_0, g0_1, g0_2, g0_3) := rawGroup10Lanes b0 b1 b2 b3 b4
  let (g1_0, g1_1, g1_2, _) := rawGroup10Lanes b5 b6 b7 b8 0#8
  setSimdLane
    (setSimdLane
      (setSimdLane
        (setSimdLane
          (setSimdLane
            (setSimdLane (g0_0.zeroExtend 128) 16 1 (g0_1.zeroExtend 128))
            16 2 (g0_2.zeroExtend 128))
          16 3 (g0_3.zeroExtend 128))
        16 4 ((g1_0.truncate 16).zeroExtend 128))
      16 5 (g1_1.zeroExtend 128))
    16 6 (g1_2.zeroExtend 128)

@[expose] def rawDeser10Full (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) : BitVec 128 :=
  let (_, _, _, g1_3) := rawGroup10Lanes b5 b6 b7 b8 b9
  setSimdLane (rawDeser10Pre7 b0 b1 b2 b3 b4 b5 b6 b7 b8) 16 7 (g1_3.zeroExtend 128)

private theorem rawDeser10Full_eq_half (chunk : List (BitVec 8)) (off : Nat) :
    rawDeser10Full
      (chunk.getD (off + 0) 0#8) (chunk.getD (off + 1) 0#8)
      (chunk.getD (off + 2) 0#8) (chunk.getD (off + 3) 0#8)
      (chunk.getD (off + 4) 0#8) (chunk.getD (off + 5) 0#8)
      (chunk.getD (off + 6) 0#8) (chunk.getD (off + 7) 0#8)
      (chunk.getD (off + 8) 0#8) (chunk.getD (off + 9) 0#8) =
    neonDeserialize10Half chunk off := by
  obtain ⟨hl0, hl1, hl2, hl3⟩ := deserialize10_scalar_lanes_eq
    (chunk.getD (off + 0) 0#8) (chunk.getD (off + 1) 0#8)
    (chunk.getD (off + 2) 0#8) (chunk.getD (off + 3) 0#8) (chunk.getD (off + 4) 0#8)
  obtain ⟨hr0, hr1, hr2, hr3⟩ := deserialize10_scalar_lanes_eq
    (chunk.getD (off + 5) 0#8) (chunk.getD (off + 6) 0#8)
    (chunk.getD (off + 7) 0#8) (chunk.getD (off + 8) 0#8) (chunk.getD (off + 9) 0#8)
  have htrunc16_16 : ∀ x : BitVec 64, (x.truncate 32).truncate 16 = x.truncate 16 := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [BitVec.truncate_eq_setWidth, hb]
  have horr_16 : ∀ (x : BitVec 64) (y : BitVec 8),
      ((x.truncate 32) ||| ((y.zeroExtend 32) <<< 2)).truncate 16 =
        (x ||| ((y.zeroExtend 64) <<< 2)).truncate 16 := by
    intro x y; apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hb, show b < 64 by omega]
  have hz128_16 : ∀ w : BitVec 16, (w.zeroExtend 128).truncate 16 = w := by
    intro w; apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hb]
  have hlane0_32 : ∀ x : BitVec 64, lane16 ((x.truncate 32).zeroExtend 128) 0 = x.truncate 16 := by
    intro x; apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [lane16, BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hb,
      show b < 32 by omega, show b < 64 by omega, show b < 128 by omega]
  have hpos : ∀ {α : Type} {c : Prop} [Decidable c], c → ∀ (t e : α), (if c then t else e) = t := by
    intro α c inst hc t e; cases inst with | isTrue _ => rfl | isFalse h => exact absurd hc h
  have hneg : ∀ {α : Type} {c : Prop} [Decidable c], ¬c → ∀ (t e : α), (if c then t else e) = e := by
    intro α c inst hc t e; cases inst with | isTrue h => exact absurd h hc | isFalse _ => rfl
  have hset1 := fun v elem i => lane16_setSimdLane_16 v elem ⟨1, by decide⟩ i
  have hset2 := fun v elem i => lane16_setSimdLane_16 v elem ⟨2, by decide⟩ i
  have hset3 := fun v elem i => lane16_setSimdLane_16 v elem ⟨3, by decide⟩ i
  have hset4 := fun v elem i => lane16_setSimdLane_16 v elem ⟨4, by decide⟩ i
  have hset5 := fun v elem i => lane16_setSimdLane_16 v elem ⟨5, by decide⟩ i
  have hset6 := fun v elem i => lane16_setSimdLane_16 v elem ⟨6, by decide⟩ i
  have hset7 := fun v elem i => lane16_setSimdLane_16 v elem ⟨7, by decide⟩ i
  dsimp only at hset1 hset2 hset3 hset4 hset5 hset6 hset7
  apply ext_lane16; intro j
  unfold rawDeser10Full rawDeser10Pre7 rawGroup10Lanes neonDeserialize10Half; dsimp only
  rw [lane16_pack8x16]
  induction j using fin8_cases
  · rw [hset7, hneg (by decide), hset6, hneg (by decide), hset5, hneg (by decide),
      hset4, hneg (by decide), hset3, hneg (by decide), hset2, hneg (by decide),
      hset1, hneg (by decide), hlane0_32]; exact hl0
  · rw [hset7, hneg (by decide), hset6, hneg (by decide), hset5, hneg (by decide),
      hset4, hneg (by decide), hset3, hneg (by decide), hset2, hneg (by decide),
      hset1, hpos (by decide), hz128_16]; exact hl1
  · rw [hset7, hneg (by decide), hset6, hneg (by decide), hset5, hneg (by decide),
      hset4, hneg (by decide), hset3, hneg (by decide), hset2, hpos (by decide), hz128_16]; exact hl2
  · rw [hset7, hneg (by decide), hset6, hneg (by decide), hset5, hneg (by decide),
      hset4, hneg (by decide), hset3, hpos (by decide), hz128_16, horr_16]; exact hl3
  · rw [hset7, hneg (by decide), hset6, hneg (by decide), hset5, hneg (by decide),
      hset4, hpos (by decide), hz128_16, htrunc16_16]; exact hr0
  · rw [hset7, hneg (by decide), hset6, hneg (by decide), hset5, hpos (by decide), hz128_16]; exact hr1
  · rw [hset7, hneg (by decide), hset6, hpos (by decide), hz128_16]; exact hr2
  · rw [hset7, hpos (by decide), hz128_16, horr_16]; exact hr3

private theorem simdXtn4h_rawPre7_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) :
    simdXtn4h (rawDeser10Pre7 b0 b1 b2 b3 b4 b5 b6 b7 b8) =
    simdXtn4h (rawDeser10Full b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) := by
  apply simdXtn4h_eq_of_even_lanes; intro r
  unfold rawDeser10Full; dsimp only
  rw [show (7 : Nat) = (7 : Fin 8).val from rfl, lane16_setSimdLane_16]
  have hne : (⟨2 * r.val, by omega⟩ : Fin 8) ≠ 7 := by
    intro h; have := congrArg Fin.val h; dsimp only at this; omega
  simp [hne]

theorem simdUmlal4sLow_v8_eq (bias vn v8 : BitVec 128)
    (hv8 : v8.truncate 64 = (dup4hLow 3329#16).truncate 64) :
    simdUmlal4sLow bias vn v8 = simdUmlal4sLow bias vn (dup8x16 3329#16) := by
  unfold simdUmlal4sLow; congr 1; funext i
  have hlane : lane16 v8 ⟨i.val, by omega⟩ = 3329#16 := by
    have h64 : (v8.truncate 64).extractLsb' (16 * i.val) 16 =
        ((dup4hLow 3329#16).truncate 64).extractLsb' (16 * i.val) 16 := by rw [hv8]
    have htr : ∀ u : BitVec 128,
        (u.truncate 64).extractLsb' (16 * i.val) 16 = lane16 u ⟨i.val, by omega⟩ := by
      intro u; apply BitVec.eq_of_getLsbD_eq; intro b hb
      simp [lane16, BitVec.truncate_eq_setWidth, hb, show 16 * i.val + b < 64 by omega]
    rw [htr, htr] at h64
    rw [h64, lane16_dup4hLow_lt4 3329#16 ⟨i.val, by omega⟩ i.isLt]
  rw [hlane, lane16_dup8x16]

theorem deser10Decomp_chunk_eq (bs : List (BitVec 8)) (c : Nat) (hc : c < 16)
    (hbs : bs.length = 320) (v8 : BitVec 128)
    (hv8 : v8.truncate 64 = (dup4hLow 3329#16).truncate 64) :
    let bias := pack4x32 fun _ => 512#32
    let pre0 := rawDeser10Pre7 (bs.getD (20 * c + 0) 0#8) (bs.getD (20 * c + 1) 0#8)
      (bs.getD (20 * c + 2) 0#8) (bs.getD (20 * c + 3) 0#8) (bs.getD (20 * c + 4) 0#8)
      (bs.getD (20 * c + 5) 0#8) (bs.getD (20 * c + 6) 0#8) (bs.getD (20 * c + 7) 0#8)
      (bs.getD (20 * c + 8) 0#8)
    let full0 := rawDeser10Full (bs.getD (20 * c + 0) 0#8) (bs.getD (20 * c + 1) 0#8)
      (bs.getD (20 * c + 2) 0#8) (bs.getD (20 * c + 3) 0#8) (bs.getD (20 * c + 4) 0#8)
      (bs.getD (20 * c + 5) 0#8) (bs.getD (20 * c + 6) 0#8) (bs.getD (20 * c + 7) 0#8)
      (bs.getD (20 * c + 8) 0#8) (bs.getD (20 * c + 9) 0#8)
    let pre1 := rawDeser10Pre7 (bs.getD (20 * c + 10) 0#8) (bs.getD (20 * c + 11) 0#8)
      (bs.getD (20 * c + 12) 0#8) (bs.getD (20 * c + 13) 0#8) (bs.getD (20 * c + 14) 0#8)
      (bs.getD (20 * c + 15) 0#8) (bs.getD (20 * c + 16) 0#8) (bs.getD (20 * c + 17) 0#8)
      (bs.getD (20 * c + 18) 0#8)
    let full1 := rawDeser10Full (bs.getD (20 * c + 10) 0#8) (bs.getD (20 * c + 11) 0#8)
      (bs.getD (20 * c + 12) 0#8) (bs.getD (20 * c + 13) 0#8) (bs.getD (20 * c + 14) 0#8)
      (bs.getD (20 * c + 15) 0#8) (bs.getD (20 * c + 16) 0#8) (bs.getD (20 * c + 17) 0#8)
      (bs.getD (20 * c + 18) 0#8) (bs.getD (20 * c + 19) 0#8)
    simdTrn1_8h (simdUshr4s (simdUmlal4sLow bias (simdXtn4h pre0) v8) 10)
        (simdUshr4s (simdUmlal4sLow bias (simdShrn16_4h full0) v8) 10) =
      polyVecNat (decompPoly16 10 bs) (2 * c) ∧
    simdTrn1_8h (simdUshr4s (simdUmlal4sLow bias (simdXtn4h pre1) v8) 10)
        (simdUshr4s (simdUmlal4sLow bias (simdShrn16_4h full1) v8) 10) =
      polyVecNat (decompPoly16 10 bs) (2 * c + 1) := by
  dsimp only
  set chunk := (bs.drop (20 * c)).take 20
  have hget : ∀ r : Nat, r < 20 → bs.getD (20 * c + r) 0#8 = chunk.getD r 0#8 := by
    intro r hr; dsimp only [chunk]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt hr, List.getElem?_drop]
  rw [simdXtn4h_rawPre7_eq _ _ _ _ _ _ _ _ _ (bs.getD (20 * c + 9) 0#8),
    simdXtn4h_rawPre7_eq _ _ _ _ _ _ _ _ _ (bs.getD (20 * c + 19) 0#8)]
  have hf0 : rawDeser10Full (bs.getD (20 * c + 0) 0#8) (bs.getD (20 * c + 1) 0#8)
      (bs.getD (20 * c + 2) 0#8) (bs.getD (20 * c + 3) 0#8) (bs.getD (20 * c + 4) 0#8)
      (bs.getD (20 * c + 5) 0#8) (bs.getD (20 * c + 6) 0#8) (bs.getD (20 * c + 7) 0#8)
      (bs.getD (20 * c + 8) 0#8) (bs.getD (20 * c + 9) 0#8) = neonDeserialize10Half chunk 0 := by
    simp only [hget 0 (by omega), hget 1 (by omega), hget 2 (by omega), hget 3 (by omega),
      hget 4 (by omega), hget 5 (by omega), hget 6 (by omega), hget 7 (by omega),
      hget 8 (by omega), hget 9 (by omega)]
    simpa [Nat.zero_add] using rawDeser10Full_eq_half chunk 0
  have hf1 : rawDeser10Full (bs.getD (20 * c + 10) 0#8) (bs.getD (20 * c + 11) 0#8)
      (bs.getD (20 * c + 12) 0#8) (bs.getD (20 * c + 13) 0#8) (bs.getD (20 * c + 14) 0#8)
      (bs.getD (20 * c + 15) 0#8) (bs.getD (20 * c + 16) 0#8) (bs.getD (20 * c + 17) 0#8)
      (bs.getD (20 * c + 18) 0#8) (bs.getD (20 * c + 19) 0#8) = neonDeserialize10Half chunk 10 := by
    simp only [hget 10 (by omega), hget 11 (by omega), hget 12 (by omega), hget 13 (by omega),
      hget 14 (by omega), hget 15 (by omega), hget 16 (by omega), hget 17 (by omega),
      hget 18 (by omega), hget 19 (by omega)]
    exact rawDeser10Full_eq_half chunk 10
  rw [hf0, hf1, simdUmlal4sLow_v8_eq _ _ v8 hv8, simdUmlal4sLow_v8_eq _ _ v8 hv8,
    simdUmlal4sLow_v8_eq _ _ v8 hv8, simdUmlal4sLow_v8_eq _ _ v8 hv8]
  change neonDecompress10_8h (neonDeserialize10Half chunk 0) = _ ∧
    neonDecompress10_8h (neonDeserialize10Half chunk 10) = _
  have hdec_sz : (decodeAndDecompress 10 bs).size = 256 := by
    simp [decodeAndDecompress, Spec.byteDecodeRaw]
  constructor
  · apply ext_lane16; intro j
    rw [(lane16_neonDecompress10_eq_decodeAndDecompress bs c hc (by omega) j).1,
      polyVecNat, lane16_pack8x16]
    simp [decompPoly16, Array.getD, hdec_sz, show 8 * (2 * c) + j.val = 16 * c + j.val by omega,
      show 16 * c + j.val < 256 by omega]
  · apply ext_lane16; intro j
    rw [(lane16_neonDecompress10_eq_decodeAndDecompress bs c hc (by omega) j).2,
      polyVecNat, lane16_pack8x16]
    simp [decompPoly16, Array.getD, hdec_sz, show 8 * (2 * c + 1) + j.val = 16 * c + (8 + j.val) by omega,
      show 16 * c + (8 + j.val) < 256 by omega]

private theorem lane16_even_pack4x32 (f : Fin 4 → BitVec 32) (r : Fin 4) :
    lane16 (pack4x32 f) ⟨2 * r.val, by omega⟩ = (f r).truncate 16 := by
  have h32 := lane32_pack4x32 f r
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hb32 := congrArg (fun w : BitVec 32 => w.getLsbD b) h32
  simp only [lane32, BitVec.getLsbD_extractLsb', show b < 32 by omega, decide_true,
    Bool.true_and] at hb32
  simp only [lane16, BitVec.getLsbD_extractLsb', BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and]
  rwa [show 16 * (2 * r.val) + b = 32 * r.val + b by omega]

private theorem neonDecompress4_8h_lane (v : BitVec 128)
    (hv : ∀ j : Fin 8, (lane16 v j).toNat < 16) (j : Fin 8) :
    let bias := pack4x32 fun _ => 8#32
    let qVec := dup4hLow 3329#16
    lane16 (simdTrn1_8h
      (simdUshr4s (simdUmlal4sLow bias (simdXtn4h v) qVec) 4)
      (simdUshr4s (simdUmlal4sLow bias (simdShrn16_4h v) qVec) 4)) j =
      BitVec.ofNat 16 (decompressCoeff 4 (lane16 v j).toNat) := by
  dsimp only
  rw [simdUmlal4sLow_v8_eq _ _ (dup4hLow 3329#16) rfl,
    simdUmlal4sLow_v8_eq _ _ (dup4hLow 3329#16) rfl, lane16_simdTrn1_8h]
  have h4 : ∀ x : BitVec 16, x.toNat < 16 →
      (((8#32 + x.zeroExtend 32 * 3329#32) >>> 4).truncate 16) =
        BitVec.ofNat 16 (decompressCoeff 4 x.toNat) := by
    intro x hx
    rw [BitVec.add_comm 8#32]
    exact (neonDecompressLane16_spec (d := 4) (Or.inl rfl) hx).1
  by_cases hev : j.val % 2 == 0
  · have hmod0 : j.val % 2 = 0 := beq_iff_eq.mp hev
    simp only [hev, ↓reduceIte, simdUshr4s, simdUmlal4sLow]
    have hfin : (⟨j.val / 2 * 2, by omega⟩ : Fin 8) = ⟨2 * (j.val / 2), by omega⟩ := by
      apply Fin.ext; dsimp only; omega
    rw [hfin, lane16_even_pack4x32 _ ⟨j.val / 2, by omega⟩]
    simp only [lane32_pack4x32, simdXtn4h, lane16_pack8x16, show j.val / 2 < 4 by omega,
      ↓reduceDIte, lane16_dup8x16]
    have hj : (⟨2 * (j.val / 2), by omega⟩ : Fin 8) = j := by apply Fin.ext; dsimp only; omega
    rw [hj]; exact h4 (lane16 v j) (hv j)
  · have hmod1 : j.val % 2 = 1 := by
      have := beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hev); omega
    simp only [hev, Bool.false_eq_true, ↓reduceIte, simdUshr4s, simdUmlal4sLow]
    have hfin : (⟨j.val / 2 * 2, by omega⟩ : Fin 8) = ⟨2 * (j.val / 2), by omega⟩ := by
      apply Fin.ext; dsimp only; omega
    rw [hfin, lane16_even_pack4x32 _ ⟨j.val / 2, by omega⟩]
    simp only [lane32_pack4x32, simdShrn16_4h, lane16_pack8x16, show j.val / 2 < 4 by omega,
      ↓reduceDIte, lane16_dup8x16]
    have hj : (⟨2 * (j.val / 2) + 1, by omega⟩ : Fin 8) = j := by apply Fin.ext; dsimp only; omega
    rw [hj]; exact h4 (lane16 v j) (hv j)

theorem deser4Decomp_chunk_eq (ct2 : List (BitVec 8)) (c : Nat) (hc : c < 16)
    (hct2 : ct2.length = 128) :
    let sub := (ct2.drop (8 * c)).take 8
    let outBs := deserializeChunkBytes 4 sub
    let q0 := ByteSlice.readLE outBs 8 8 ++ ByteSlice.readLE outBs 0 8
    let q1 := ByteSlice.readLE outBs 24 8 ++ ByteSlice.readLE outBs 16 8
    let bias := pack4x32 fun _ => 8#32
    let qVec := dup4hLow 3329#16
    simdTrn1_8h (simdUshr4s (simdUmlal4sLow bias (simdXtn4h q0) qVec) 4)
        (simdUshr4s (simdUmlal4sLow bias (simdShrn16_4h q0) qVec) 4) =
      polyVecNat (decompPoly16 4 ct2) (2 * c) ∧
    simdTrn1_8h (simdUshr4s (simdUmlal4sLow bias (simdXtn4h q1) qVec) 4)
        (simdUshr4s (simdUmlal4sLow bias (simdShrn16_4h q1) qVec) 4) =
      polyVecNat (decompPoly16 4 ct2) (2 * c + 1) := by
  dsimp only
  set sub := (ct2.drop (8 * c)).take 8
  set outBs := deserializeChunkBytes 4 sub
  set q0 := ByteSlice.readLE outBs 8 8 ++ ByteSlice.readLE outBs 0 8
  set q1 := ByteSlice.readLE outBs 24 8 ++ ByteSlice.readLE outBs 16 8
  have hq0_eq : ∀ j : Fin 8, lane16 q0 j = deserializeChunkCoeff 4 sub j.val :=
    fun j => q0_lane_deserializeChunkBytes 4 sub j.val j.isLt
  have hq1_eq : ∀ j : Fin 8, lane16 q1 j = deserializeChunkCoeff 4 sub (8 + j.val) :=
    fun j => q1_lane_deserializeChunkBytes 4 sub j.val j.isLt
  have hq0_lt : ∀ j : Fin 8, (lane16 q0 j).toNat < 16 := fun j => by
    rw [hq0_eq j]; unfold deserializeChunkCoeff
    have hlt := byteDecodeRaw_lt_two_pow 4 (by decide) sub j.val (by omega)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hlt
  have hq1_lt : ∀ j : Fin 8, (lane16 q1 j).toNat < 16 := fun j => by
    rw [hq1_eq j]; unfold deserializeChunkCoeff
    have hlt := byteDecodeRaw_lt_two_pow 4 (by decide) sub (8 + j.val) (by omega)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hlt
  have hcell (idx : Nat) (hidx : idx < 16) :
      decompressCoeff 4 (deserializeChunkCoeff 4 sub idx).toNat =
        (decodeAndDecompress 4 ct2).getD (16 * c + idx) 0 := by
    have hlt := byteDecodeRaw_lt_two_pow 4 (by decide) sub idx (by omega)
    unfold deserializeChunkCoeff
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show sub = (ct2.drop (2 * 4 * c)).take (2 * 4) by simp [sub]]
    exact decodeAndDecompress_chunk_eq 4 ct2 c idx hc hidx (by omega)
  have hdec_sz : (decodeAndDecompress 4 ct2).size = 256 := by
    simp [decodeAndDecompress, Spec.byteDecodeRaw]
  constructor
  · apply ext_lane16; intro j
    rw [neonDecompress4_8h_lane q0 hq0_lt j, hq0_eq j, hcell j.val (by omega), polyVecNat, lane16_pack8x16]
    simp [decompPoly16, Array.getD, hdec_sz, show 8 * (2 * c) + j.val = 16 * c + j.val by omega,
      show 16 * c + j.val < 256 by omega]
  · apply ext_lane16; intro j
    rw [neonDecompress4_8h_lane q1 hq1_lt j, hq1_eq j, hcell (8 + j.val) (by omega), polyVecNat, lane16_pack8x16]
    simp [decompPoly16, Array.getD, hdec_sz, show 8 * (2 * c + 1) + j.val = 16 * c + (8 + j.val) by omega,
      show 16 * c + (8 + j.val) < 256 by omega]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2Simd

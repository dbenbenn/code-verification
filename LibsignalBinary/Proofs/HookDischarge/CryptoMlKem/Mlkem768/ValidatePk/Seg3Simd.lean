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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common

/-! # `validate_pk_bytes` (`B21`) — Segment 3 AdvSIMD Bridges & `serialize_12` Equivalences (`Role::Proof`). -/

set_option autoImplicit false
public section
namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  ext_lane16 ext_lane32 getSimdLane_16_eq getSimdLane_32_eq lane16 lane16_mapSimdLanes_true_16
  lane16_pack8x16 lane32 lane32_pack4x32 lane64 pack2x64 pack4x32 pack8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdCmltZero8h simdExt16b lane16_simdAdd8h lane16_simdCmltZero8h
  simdSli2d simdSli4s simdTrn1_4s simdTrn1_8h simdTrn2_4s simdTrn2_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (eq_byteEncodeHalf_of_bits)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh (
  lane16_simdExt16b_8_2 lane64_simdExt16b_8_0 neonSerialize12Bytes neonSerialize12Half neonSerialize12Half_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base (
  packTriple12 rawCoeff0 rawCoeff0_lt_4096 rawCoeff1 rawCoeff1_lt_4096 reduce12 reencodePoly384 reencodeTriple)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (deserVec8h lane16_deserVec8h)

/-! ## 1. `{svc}`-Polymorphic AdvSIMD Execution Bridges -/

private theorem writeV_adv_congr {s : State} {rd : BitVec 5} {a b : BitVec 128} (h : a = b) :
    (s.writeVReg128 rd a).advancePC = (s.writeVReg128 rd b).advancePC := h ▸ rfl

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdAnd_16b {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b00#2 rm 0b00011#5 rn rd) s =
      (s.writeVReg128 rd (s.readVReg128 rn &&& s.readVReg128 rm)).advancePC := rfl

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdCmltZero_8h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdTwoRegMisc true false 0b01#2 0b01010#5 rn rd) s =
      (s.writeVReg128 rd (simdCmltZero8h (s.readVReg128 rn))).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_false, Bool.true_and,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq,
    show (8 <<< (0b01#2).toNat) = 16 from rfl,
    show (1#128 <<< 16 - 1#128 : BitVec 128) = 65535#128 from rfl]
  refine writeV_adv_congr ?_
  apply ext_lane16; intro i
  rw [lane16_mapSimdLanes_true_16, lane16_simdCmltZero8h]
  set x := lane16 (s.readVReg128 rn) i
  have hbit : (x.zeroExtend 128).getLsbD (16 - 1) = x.msb := by
    rw [BitVec.msb_eq_getLsbD_last]; simp
  have hneg : x.toInt < 0 ↔ x.msb = true := by
    have := x.isLt; rw [BitVec.toInt_eq_msb_cond]
    cases x.msb <;> (simp; try omega)
  rw [hbit]
  cases hm : x.msb
  · simp [show ¬(x.toInt < 0) from fun h => by rw [hneg.mp h] at hm; cases hm]
  · simp [hneg.mpr hm]

private theorem getSimdLane_64_eq (v : BitVec 128) (i : Fin 2) :
    getSimdLane v 64 i.val = (lane64 v i).zeroExtend 128 := by
  have hm : ∀ b : Nat, (1#128 <<< 64 - 1#128).getLsbD b = decide (b < 64) := fun b => by
    change (18446744073709551615#128).toNat.testBit b = decide (b < 64)
    rw [show (18446744073709551615#128).toNat = 2 ^ 64 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [getSimdLane]
  simp only [lane64, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, hm,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and, BitVec.getLsbD_extractLsb']
  by_cases h64 : b < 64
  · simp [h64, Nat.mul_comm i.val 64]
  · simp [h64]

private theorem getLsbD_zext128_shl {w : Nat} (x : BitVec w) (s b : Nat) (hb : b < 128) :
    (x.zeroExtend 128 <<< s).getLsbD b = (decide (s ≤ b ∧ b < s + w) && x.getLsbD (b - s)) := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and]
  by_cases hs : b < s
  · simp [hs, show ¬(s ≤ b ∧ b < s + w) by omega]
  · by_cases hw : b < s + w
    · simp [hs, show s ≤ b ∧ b < s + w from ⟨by omega, hw⟩, show b - s < 128 by omega]
    · simp [hs, show ¬(s ≤ b ∧ b < s + w) by omega, BitVec.getLsbD_of_ge x (b - s) (by omega)]

private theorem getLsbD_zext128_band {w : Nat} (x : BitVec w) (b : Nat) (hb : b < 128) :
    (x.zeroExtend 128).getLsbD b = (decide (b < w) && x.getLsbD b) := by
  simpa using getLsbD_zext128_shl x 0 b hb

private theorem dec_32_k (k s j b : Nat) (hs : s = 32 * k) (hb : b < 32) :
    decide (s ≤ 32 * j + b ∧ 32 * j + b < s + 32) = (j == k) := by
  subst hs; by_cases h : j = k
  · subst h; simp [hb]
  · have hn : ¬(32 * k ≤ 32 * j + b ∧ 32 * j + b < 32 * k + 32) := by omega
    simp [hn, h]

private theorem dec_32_0 (j b : Nat) (hb : b < 32) : decide (32 * j + b < 32) = (j == 0) := by
  simpa using dec_32_k 0 0 j b rfl hb

private theorem dec_16_k (k s j b : Nat) (hs : s = 16 * k) (hb : b < 16) :
    decide (s ≤ 16 * j + b ∧ 16 * j + b < s + 16) = (j == k) := by
  subst hs; by_cases h : j = k
  · subst h; simp [hb]
  · have hn : ¬(16 * k ≤ 16 * j + b ∧ 16 * j + b < 16 * k + 16) := by omega
    simp [hn, h]

private theorem dec_16_0 (j b : Nat) (hb : b < 16) : decide (16 * j + b < 16) = (j == 0) := by
  simpa using dec_16_k 0 0 j b rfl hb

private theorem or_shift_eq_pack2x64 (a0 a1 : BitVec 64) :
    (a0.zeroExtend 128 ||| a1.zeroExtend 128 <<< 64) =
      pack2x64 (fun i => if i.val = 0 then a0 else a1) := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  dsimp only [pack2x64]
  rw [BitVec.getLsbD_or, BitVec.getLsbD_append,
    getLsbD_zext128_band a0 b hb, getLsbD_zext128_shl a1 64 b hb]
  by_cases h0 : b < 64
  · simp [h0, show ¬(64 ≤ b ∧ b < 64 + 64) by omega]
  · simp [h0, show 64 ≤ b ∧ b < 64 + 64 by omega]

private theorem or_shift_eq_pack4x32 (a0 a1 a2 a3 : BitVec 32) :
    (a0.zeroExtend 128 ||| a1.zeroExtend 128 <<< 32 |||
      a2.zeroExtend 128 <<< 64 ||| a3.zeroExtend 128 <<< 96) =
      pack4x32 (fun i => match i.val with | 0 => a0 | 1 => a1 | 2 => a2 | _ => a3) := by
  apply ext_lane32; intro i; rw [lane32_pack4x32]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hp : 32 * i.val + b < 128 := by omega
  simp only [lane32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, hb, decide_true, Bool.true_and]
  rw [getLsbD_zext128_band a0 _ hp, getLsbD_zext128_shl a1 32 _ hp,
      getLsbD_zext128_shl a2 64 _ hp, getLsbD_zext128_shl a3 96 _ hp,
      dec_32_0 i.val b hb, dec_32_k 1 32 i.val b rfl hb,
      dec_32_k 2 64 i.val b rfl hb, dec_32_k 3 96 i.val b rfl hb]
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals simp

private theorem or_shift_eq_pack8x16 (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 16) :
    (a0.zeroExtend 128 ||| a1.zeroExtend 128 <<< 16 |||
      a2.zeroExtend 128 <<< 32 ||| a3.zeroExtend 128 <<< 48 |||
      a4.zeroExtend 128 <<< 64 ||| a5.zeroExtend 128 <<< 80 |||
      a6.zeroExtend 128 <<< 96 ||| a7.zeroExtend 128 <<< 112) =
      pack8x16 (fun i => match i.val with
        | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4 | 5 => a5 | 6 => a6 | _ => a7) := by
  apply ext_lane16; intro i; rw [lane16_pack8x16]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hp : 16 * i.val + b < 128 := by omega
  simp only [lane16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, hb, decide_true, Bool.true_and]
  rw [getLsbD_zext128_band a0 _ hp, getLsbD_zext128_shl a1 16 _ hp,
      getLsbD_zext128_shl a2 32 _ hp, getLsbD_zext128_shl a3 48 _ hp,
      getLsbD_zext128_shl a4 64 _ hp, getLsbD_zext128_shl a5 80 _ hp,
      getLsbD_zext128_shl a6 96 _ hp, getLsbD_zext128_shl a7 112 _ hp,
      dec_16_0 i.val b hb, dec_16_k 1 16 i.val b rfl hb,
      dec_16_k 2 32 i.val b rfl hb, dec_16_k 3 48 i.val b rfl hb,
      dec_16_k 4 64 i.val b rfl hb, dec_16_k 5 80 i.val b rfl hb,
      dec_16_k 6 96 i.val b rfl hb, dec_16_k 7 112 i.val b rfl hb]
  rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals simp

private theorem sli32_lane_eq (x d : BitVec 32) :
    (((d.zeroExtend 128 &&& ~~~((4294967295#128 <<< 12) &&& 4294967295#128)) |||
      (((x.zeroExtend 128 <<< 12) &&& 4294967295#128) &&&
        ((4294967295#128 <<< 12) &&& 4294967295#128))) &&& 4294967295#128) =
      ((d &&& 4095#32) ||| (x <<< 12)).zeroExtend 128 := by
  bv_bits

private theorem sli64_lane_eq (x d : BitVec 64) :
    (((d.zeroExtend 128 &&& ~~~((18446744073709551615#128 <<< 24) &&& 18446744073709551615#128)) |||
      (((x.zeroExtend 128 <<< 24) &&& 18446744073709551615#128) &&&
        ((18446744073709551615#128 <<< 24) &&& 18446744073709551615#128))) &&&
      18446744073709551615#128) =
      ((d &&& 16777215#64) ||| (x <<< 24)).zeroExtend 128 := by
  bv_bits

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdSli_4s_12 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0101#4 0b100#3 0b01010#5 rn rd) s =
      (s.writeVReg128 rd (simdSli4s (s.readVReg128 rd) (s.readVReg128 rn) 12)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  set vd := s.readVReg128 rd
  dsimp only [zipLanes, laneMask]
  simp only [Nat.zero_mul, Nat.one_mul, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero,
    BitVec.zero_or, show 2 * 32 = 64 from rfl, show 3 * 32 = 96 from rfl,
    show (1#128 <<< 32 - 1#128 : BitVec 128) = 4294967295#128 from rfl]
  have h32_0 : ∀ v : BitVec 128, v &&& 4294967295#128 = (lane32 v 0).zeroExtend 128 :=
    fun v => by simpa [getSimdLane] using getSimdLane_32_eq v ⟨0, by decide⟩
  have h32_1 : ∀ v : BitVec 128, v >>> 32 &&& 4294967295#128 = (lane32 v 1).zeroExtend 128 :=
    fun v => getSimdLane_32_eq v ⟨1, by decide⟩
  have h32_2 : ∀ v : BitVec 128, v >>> 64 &&& 4294967295#128 = (lane32 v 2).zeroExtend 128 :=
    fun v => getSimdLane_32_eq v ⟨2, by decide⟩
  have h32_3 : ∀ v : BitVec 128, v >>> 96 &&& 4294967295#128 = (lane32 v 3).zeroExtend 128 :=
    fun v => getSimdLane_32_eq v ⟨3, by decide⟩
  have hsli := sli32_lane_eq
  conv at hsli => ext x d; lhs; simp
  rw [h32_0 vn, h32_0 vd, h32_1 vn, h32_1 vd, h32_2 vn, h32_2 vd, h32_3 vn, h32_3 vd,
      hsli, hsli, hsli, hsli]
  exact or_shift_eq_pack4x32 _ _ _ _

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdSli_2d_24 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b1011#4 0b000#3 0b01010#5 rn rd) s =
      (s.writeVReg128 rd (simdSli2d (s.readVReg128 rd) (s.readVReg128 rn) 24)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  set vd := s.readVReg128 rd
  dsimp only [zipLanes, laneMask]
  simp only [Nat.zero_mul, Nat.one_mul, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero,
    BitVec.zero_or,
    show (1#128 <<< 64 - 1#128 : BitVec 128) = 18446744073709551615#128 from rfl]
  have h64_0 : ∀ v : BitVec 128, v &&& 18446744073709551615#128 = (lane64 v 0).zeroExtend 128 :=
    fun v => by simpa [getSimdLane] using getSimdLane_64_eq v ⟨0, by decide⟩
  have h64_1 : ∀ v : BitVec 128, v >>> 64 &&& 18446744073709551615#128 = (lane64 v 1).zeroExtend 128 :=
    fun v => getSimdLane_64_eq v ⟨1, by decide⟩
  have hsli := sli64_lane_eq
  conv at hsli => ext x d; lhs; simp
  rw [h64_0 vn, h64_0 vd, h64_1 vn, h64_1 vd, hsli, hsli]
  exact or_shift_eq_pack2x64 _ _

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdDupScalar_h2 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdDupScalar 0b01010#5 rn rd) s =
      (s.writeVReg128 rd ((lane16 (s.readVReg128 rn) 2).zeroExtend 128)).advancePC := by
  simp [execInstWithSvc, evalSimdDupScalar]
  refine writeV_adv_congr ?_
  simpa using getSimdLane_16_eq (s.readVReg128 rn) 2

@[simp, arm64_norm, wp_norm ↓]
theorem svc_simdTrn1_8h {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdPermute true 0b01#2 rm 0b010#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn1_8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, List.range']; refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn; set vm := s.readVReg128 rm
  rw [getSimdLane_16_eq vn ⟨0, by decide⟩, getSimdLane_16_eq vm ⟨0, by decide⟩,
      getSimdLane_16_eq vn ⟨2, by decide⟩, getSimdLane_16_eq vm ⟨2, by decide⟩,
      getSimdLane_16_eq vn ⟨4, by decide⟩, getSimdLane_16_eq vm ⟨4, by decide⟩,
      getSimdLane_16_eq vn ⟨6, by decide⟩, getSimdLane_16_eq vm ⟨6, by decide⟩]
  exact or_shift_eq_pack8x16 _ _ _ _ _ _ _ _

@[simp, arm64_norm, wp_norm ↓]
theorem svc_simdTrn2_8h {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdPermute true 0b01#2 rm 0b110#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn2_8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, List.range']; refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn; set vm := s.readVReg128 rm
  rw [getSimdLane_16_eq vn ⟨1, by decide⟩, getSimdLane_16_eq vm ⟨1, by decide⟩,
      getSimdLane_16_eq vn ⟨3, by decide⟩, getSimdLane_16_eq vm ⟨3, by decide⟩,
      getSimdLane_16_eq vn ⟨5, by decide⟩, getSimdLane_16_eq vm ⟨5, by decide⟩,
      getSimdLane_16_eq vn ⟨7, by decide⟩, getSimdLane_16_eq vm ⟨7, by decide⟩]
  exact or_shift_eq_pack8x16 _ _ _ _ _ _ _ _

@[simp, arm64_norm, wp_norm ↓]
theorem svc_simdTrn1_4s {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdPermute true 0b10#2 rm 0b010#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn1_4s (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, List.range']; refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn; set vm := s.readVReg128 rm
  rw [getSimdLane_32_eq vn ⟨0, by decide⟩, getSimdLane_32_eq vm ⟨0, by decide⟩,
      getSimdLane_32_eq vn ⟨2, by decide⟩, getSimdLane_32_eq vm ⟨2, by decide⟩]
  exact or_shift_eq_pack4x32 _ _ _ _

@[simp, arm64_norm, wp_norm ↓]
theorem svc_simdTrn2_4s {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdPermute true 0b10#2 rm 0b110#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn2_4s (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, List.range']; refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn; set vm := s.readVReg128 rm
  rw [getSimdLane_32_eq vn ⟨1, by decide⟩, getSimdLane_32_eq vm ⟨1, by decide⟩,
      getSimdLane_32_eq vn ⟨3, by decide⟩, getSimdLane_32_eq vm ⟨3, by decide⟩]
  exact or_shift_eq_pack4x32 _ _ _ _

private theorem getLsbD_append64 (hi lo : BitVec 64) (b : Nat) :
    ((hi ++ lo : BitVec 128)).getLsbD b = if b < 64 then lo.getLsbD b else hi.getLsbD (b - 64) :=
  BitVec.getLsbD_append

private theorem getLsbD_append128 (hi lo : BitVec 128) (b : Nat) :
    ((hi ++ lo : BitVec 256)).getLsbD b = if b < 128 then lo.getLsbD b else hi.getLsbD (b - 128) :=
  BitVec.getLsbD_append

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdExt_16b_8 {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdExt true rm 8#4 rn rd) s =
      (s.writeVReg128 rd
        ((s.readVReg128 rm).truncate 64 ++ (s.readVReg128 rn).extractLsb' 64 64)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [getLsbD_append128, getLsbD_append64, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and]
  by_cases hb64 : b < 64
  · simp only [hb64, show 64 + b < 128 by omega, ↓reduceIte, decide_true, Bool.true_and]
  · simp only [hb64, show ¬ (64 + b < 128) by omega,
      show b - 64 < 64 by omega, show 64 + b - 128 = b - 64 by omega,
      ↓reduceIte, decide_true, Bool.true_and]

theorem low32_eq_lane64_0 (u : BitVec 128) :
    u.extractLsb' 0 32 = (lane64 u 0).truncate 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp [lane64, hb]

theorem ext8_self_low32 (u : BitVec 128) :
    (u.truncate 64 ++ u.extractLsb' 64 64).extractLsb' 0 32 =
      (lane64 (simdExt16b u u 8) 0).truncate 32 := by
  rw [lane64_simdExt16b_8_0]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp [getLsbD_append64, lane64, hb, show b < 64 by omega]

theorem ext8_self_lane16_2 (u : BitVec 128) :
    lane16 (u.truncate 64 ++ u.extractLsb' 64 64) 2 = lane16 (simdExt16b u u 8) 2 := by
  rw [lane16_simdExt16b_8_2]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [lane16, BitVec.getLsbD_extractLsb', getLsbD_append64, hb, decide_true, Bool.true_and,
    Fin.isValue, show 16 * (2 : Fin 8).val + b = 32 + b from rfl,
    show 16 * (6 : Fin 8).val + b = 96 + b from rfl, show 32 + b < 64 by omega, ↓reduceIte]
  congr 1; omega

/-! ## 2. Pure `deserVec8h` Bounds & `neonSerialize12Bytes` = `reencodePoly384` Slice -/

private theorem reduce12_lt_3329 {d : Nat} (hd : d < 4096) : (reduce12 d).toNat < 3329 := by
  unfold reduce12; split_ifs <;> (rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

theorem deserVec8h_lane_lt_3329 (bs : List (BitVec 8)) (off : Nat) (i : Fin 8) :
    (lane16 (deserVec8h bs off) i).toNat < 3329 := by
  rw [lane16_deserVec8h]; dsimp only
  split_ifs
  · exact reduce12_lt_3329 (rawCoeff0_lt_4096 _ _)
  · exact reduce12_lt_3329 (rawCoeff1_lt_4096 _ _)

theorem deserVec8h_lane_lt_4096 (bs : List (BitVec 8)) (off : Nat) (i : Fin 8) :
    (lane16 (deserVec8h bs off) i).toNat < 4096 :=
  Nat.lt_trans (deserVec8h_lane_lt_3329 bs off i) (by decide)

theorem cmltZero_deserVec8h (bs : List (BitVec 8)) (off : Nat) :
    simdCmltZero8h (deserVec8h bs off) = 0#128 := by
  apply ext_lane16; intro i
  rw [lane16_simdCmltZero8h]
  have hlt := deserVec8h_lane_lt_3329 bs off i
  have hmsb : (lane16 (deserVec8h bs off) i).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega
  have hnonneg : ¬ ((lane16 (deserVec8h bs off) i).toInt < 0) := by
    rw [BitVec.toInt_eq_msb_cond, hmsb]; simp
  simp only [hnonneg, ↓reduceIte]; simp [lane16]

theorem cmltAdd_deserVec8h (bs : List (BitVec 8)) (off : Nat) (qVec : BitVec 128) :
    simdAdd8h (simdCmltZero8h (deserVec8h bs off) &&& qVec) (deserVec8h bs off) =
      deserVec8h bs off := by
  rw [cmltZero_deserVec8h, BitVec.zero_and]
  apply ext_lane16; intro i
  have hz : lane16 0#128 i = 0#16 := by simp [lane16]
  rw [lane16_simdAdd8h, hz, BitVec.zero_add]

private theorem packTriple12_getD (c0 c1 : BitVec 16) (j b : Nat) (hj : j < 3) (hb : b < 8) :
    ((packTriple12 c0 c1).getD j 0#8)[b] =
      if 8 * j + b < 12 then c0.getLsbD (8 * j + b) else c1.getLsbD (8 * j + b - 12) := by
  have hmask : ∀ r : Nat, (0xfff#24).getLsbD r = decide (r < 12) := fun r => by
    change (0xfff#24).toNat.testBit r = decide (r < 12)
    rw [show (0xfff#24).toNat = 2 ^ 12 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  unfold packTriple12; dsimp only
  rcases j with _ | _ | _ | j <;> try omega
  · simp only [List.getD_cons_zero, ← BitVec.getLsbD_eq_getElem hb, BitVec.truncate_eq_setWidth,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
      hmask, hb, decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add]
    simp [show b < 12 by omega, show b < 16 by omega, show b < 24 by omega]
  · simp only [List.getD_cons_zero, List.getD_cons_succ, ← BitVec.getLsbD_eq_getElem hb,
      BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, hmask, hb, decide_true,
      Bool.true_and, show 8 * 1 = 8 from rfl]
    by_cases h4 : b < 4
    · simp [show 8 + b < 12 by omega, show 8 + b < 16 by omega, show 8 + b < 24 by omega]
    · simp [show ¬(8 + b < 12) by omega, show 8 + b < 24 by omega,
        show 8 + b - 12 < 12 by omega, show 8 + b - 12 < 16 by omega, show 8 + b - 12 < 24 by omega]
  · simp only [List.getD_cons_zero, List.getD_cons_succ, ← BitVec.getLsbD_eq_getElem hb,
      BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, hmask, hb, decide_true,
      Bool.true_and, show 8 * (1 + 1) = 16 from rfl]
    simp [show ¬(16 + b < 12) by omega, show 16 + b < 24 by omega,
      show 16 + b - 12 < 12 by omega, show 16 + b - 12 < 16 by omega, show 16 + b - 12 < 24 by omega]

theorem neonSerialize12Half_eq_packTriples (v : BitVec 128) :
    neonSerialize12Half v =
      packTriple12 (lane16 v 0) (lane16 v 1) ++ packTriple12 (lane16 v 2) (lane16 v 3) ++
      packTriple12 (lane16 v 4) (lane16 v 5) ++ packTriple12 (lane16 v 6) (lane16 v 7) := by
  rw [neonSerialize12Half_eq]; symm
  refine eq_byteEncodeHalf_of_bits (by simp [packTriple12]) fun k b hk hb => ?_
  have hget : (packTriple12 (lane16 v 0) (lane16 v 1) ++ packTriple12 (lane16 v 2) (lane16 v 3) ++
        packTriple12 (lane16 v 4) (lane16 v 5) ++ packTriple12 (lane16 v 6) (lane16 v 7)).getD k 0#8 =
      (packTriple12 (lane16 v ⟨2 * (k / 3), by omega⟩)
        (lane16 v ⟨2 * (k / 3) + 1, by omega⟩)).getD (k % 3) 0#8 := by
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
    all_goals rfl
  rw [hget, packTriple12_getD _ _ (k % 3) b (by omega) hb]
  by_cases h12 : 8 * (k % 3) + b < 12
  · simp only [h12, ↓reduceIte, show (8 * k + b) % 12 = 8 * (k % 3) + b by omega]
    congr 2; apply Fin.ext; dsimp only; omega
  · simp only [h12, ↓reduceIte, show (8 * k + b) % 12 = 8 * (k % 3) + b - 12 by omega]
    congr 2; apply Fin.ext; dsimp only; omega

/-- 24-byte `serialize_12` chunk produced by iteration `k`. -/
@[expose] def reencodeChunk24 (bs : List (BitVec 8)) (k : Nat) : List (BitVec 8) :=
  neonSerialize12Bytes (deserVec8h bs (24 * k)) (deserVec8h bs (24 * k + 12))

@[simp] theorem reencodeChunk24_length (bs : List (BitVec 8)) (k : Nat) :
    (reencodeChunk24 bs k).length = 24 := by
  simp [reencodeChunk24, neonSerialize12Bytes, neonSerialize12Half]

/-- Prefix of `k` 24-byte `serialize_12` chunks (`24 * k` bytes). -/
@[expose] def reencodePolyPrefix (bs : List (BitVec 8)) (k : Nat) : List (BitVec 8) :=
  ((List.range k).map (reencodeChunk24 bs)).flatten

@[simp] theorem reencodePolyPrefix_zero (bs : List (BitVec 8)) : reencodePolyPrefix bs 0 = [] := rfl

theorem reencodePolyPrefix_succ (bs : List (BitVec 8)) (k : Nat) :
    reencodePolyPrefix bs (k + 1) = reencodePolyPrefix bs k ++ reencodeChunk24 bs k := by
  simp [reencodePolyPrefix, List.range_succ]

@[simp] theorem reencodePolyPrefix_length (bs : List (BitVec 8)) :
    ∀ k : Nat, (reencodePolyPrefix bs k).length = 24 * k
  | 0 => rfl
  | k + 1 => by
    rw [reencodePolyPrefix_succ, List.length_append, reencodePolyPrefix_length bs k,
      reencodeChunk24_length]; omega

private theorem neonSerialize12Half_deserVec8h (bs : List (BitVec 8)) (t0 : Nat) :
    neonSerialize12Half (deserVec8h bs (3 * t0)) =
      reencodeTriple (bs.getD (3 * t0) 0#8) (bs.getD (3 * t0 + 1) 0#8) (bs.getD (3 * t0 + 2) 0#8) ++
      reencodeTriple (bs.getD (3 * (t0 + 1)) 0#8) (bs.getD (3 * (t0 + 1) + 1) 0#8) (bs.getD (3 * (t0 + 1) + 2) 0#8) ++
      reencodeTriple (bs.getD (3 * (t0 + 2)) 0#8) (bs.getD (3 * (t0 + 2) + 1) 0#8) (bs.getD (3 * (t0 + 2) + 2) 0#8) ++
      reencodeTriple (bs.getD (3 * (t0 + 3)) 0#8) (bs.getD (3 * (t0 + 3) + 1) 0#8) (bs.getD (3 * (t0 + 3) + 2) 0#8) := by
  rw [neonSerialize12Half_eq_packTriples]
  rw [lane16_deserVec8h, lane16_deserVec8h, lane16_deserVec8h, lane16_deserVec8h,
      lane16_deserVec8h, lane16_deserVec8h, lane16_deserVec8h, lane16_deserVec8h]
  change packTriple12 (reduce12 (rawCoeff0 (bs.getD (3 * t0 + 0) 0#8) (bs.getD (3 * t0 + 0 + 1) 0#8)))
      (reduce12 (rawCoeff1 (bs.getD (3 * t0 + 0 + 1) 0#8) (bs.getD (3 * t0 + 0 + 2) 0#8))) ++
    packTriple12 (reduce12 (rawCoeff0 (bs.getD (3 * t0 + 3) 0#8) (bs.getD (3 * t0 + 3 + 1) 0#8)))
      (reduce12 (rawCoeff1 (bs.getD (3 * t0 + 3 + 1) 0#8) (bs.getD (3 * t0 + 3 + 2) 0#8))) ++
    packTriple12 (reduce12 (rawCoeff0 (bs.getD (3 * t0 + 6) 0#8) (bs.getD (3 * t0 + 6 + 1) 0#8)))
      (reduce12 (rawCoeff1 (bs.getD (3 * t0 + 6 + 1) 0#8) (bs.getD (3 * t0 + 6 + 2) 0#8))) ++
    packTriple12 (reduce12 (rawCoeff0 (bs.getD (3 * t0 + 9) 0#8) (bs.getD (3 * t0 + 9 + 1) 0#8)))
      (reduce12 (rawCoeff1 (bs.getD (3 * t0 + 9 + 1) 0#8) (bs.getD (3 * t0 + 9 + 2) 0#8))) = _
  dsimp only [reencodeTriple, Nat.add_zero]
  rw [show 3 * t0 + 3 = 3 * (t0 + 1) by omega, show 3 * (t0 + 1) + 1 + 1 = 3 * (t0 + 1) + 2 by omega,
      show 3 * t0 + 6 = 3 * (t0 + 2) by omega, show 3 * (t0 + 2) + 1 + 1 = 3 * (t0 + 2) + 2 by omega,
      show 3 * t0 + 9 = 3 * (t0 + 3) by omega, show 3 * (t0 + 3) + 1 + 1 = 3 * (t0 + 3) + 2 by omega]

theorem reencodeChunk24_eq_triples (bs : List (BitVec 8)) (k : Nat) :
    reencodeChunk24 bs k = ((List.range 8).map fun j => reencodeTriple
      (bs.getD (3 * (8 * k + j)) 0#8) (bs.getD (3 * (8 * k + j) + 1) 0#8)
      (bs.getD (3 * (8 * k + j) + 2) 0#8)).flatten := by
  unfold reencodeChunk24 neonSerialize12Bytes
  rw [show 24 * k = 3 * (8 * k) by omega, show 3 * (8 * k) + 12 = 3 * (8 * k + 4) by omega,
    neonSerialize12Half_deserVec8h bs (8 * k), neonSerialize12Half_deserVec8h bs (8 * k + 4),
    show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp [List.map, List.flatten, Nat.add_assoc]

theorem reencodePolyPrefix_16 (bs : List (BitVec 8)) :
    reencodePolyPrefix bs 16 = reencodePoly384 bs := by
  have h128 : ((List.range 16).map fun k => (List.range 8).map fun j => 8 * k + j).flatten =
      List.range 128 := by decide
  unfold reencodePolyPrefix reencodePoly384
  rw [← h128, List.map_flatten, List.map_map, List.flatten_flatten, List.map_map]
  congr 1; apply List.map_congr_left; intro k _
  simp only [Function.comp_apply, reencodeChunk24_eq_triples, List.map_map]; rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd

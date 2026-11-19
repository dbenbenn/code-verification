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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd -- proof-setup: allow-public-import

/-!
# `encapsulate2` (`B20`) — Segment 3 AdvSIMD Permute & Widening Bridges (`Seg3SimdPerm`)

Provides `@[simp, arm64_norm, wp_norm]` symbolic-execution bridges for AdvSIMD vector permutes
(`TRN1`, `TRN2`, `UZP1`, `ZIP1`, `ZIP2`, `REV64`, `EXT`) and signed widening multiply-accumulate
(`SMULL`, `SMULL2`, `SMLAL`, `SMLAL2`) in `B20` `[0x0bdc .. 0x10a0]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdPerm

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  ext_lane16
  ext_lane32
  getSimdLane_16_eq
  getSimdLane_32_eq
  lane16
  lane16_pack8x16
  lane32
  lane32_pack4x32
  lane64
  pack2x64
  pack4x32
  pack8x16
  simdLaneSInt_16_zeroExtend
  simdLaneSInt_32_zeroExtend
  truncate32_intToSimdLane_32
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdSmlal4s
  simdSmull4s
  simdTrn1_4s
  simdTrn1_8h
  simdTrn2_4s
  simdTrn2_8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  simdRev64_4s
  simdUzp1_4s
)

/-! ## 1. Lane-Packing & Bit-Mask Helpers -/

private theorem writeV_adv_congr {s : State} {rd : BitVec 5} {a b : BitVec 128} (h : a = b) :
    (s.writeVReg128 rd a).advancePC = (s.writeVReg128 rd b).advancePC :=
  h ▸ rfl

private theorem getLsbD_65535_128 (b : Nat) : (65535#128).getLsbD b = decide (b < 16) := by
  change (65535#128).toNat.testBit b = decide (b < 16)
  have hval : (65535#128).toNat = 2 ^ 16 - 1 := rfl
  rw [hval, Nat.testBit_two_pow_sub_one]

private theorem getLsbD_mask32_64 (b : Nat) : (4294967295#64).getLsbD b = decide (b < 32) := by
  change (4294967295#64).toNat.testBit b = decide (b < 32)
  have hval : (4294967295#64).toNat = 2 ^ 32 - 1 := rfl
  rw [hval, Nat.testBit_two_pow_sub_one]

private theorem getLsbD_mask32_128 (b : Nat) : (4294967295#128).getLsbD b = decide (b < 32) := by
  change (4294967295#128).toNat.testBit b = decide (b < 32)
  have hval : (4294967295#128).toNat = 2 ^ 32 - 1 := rfl
  rw [hval, Nat.testBit_two_pow_sub_one]

private theorem getLsbD_mask64_128 (b : Nat) :
    (18446744073709551615#128).getLsbD b = decide (b < 64) := by
  change (18446744073709551615#128).toNat.testBit b = decide (b < 64)
  have hval : (18446744073709551615#128).toNat = 2 ^ 64 - 1 := rfl
  rw [hval, Nat.testBit_two_pow_sub_one]

private theorem getSimdLane_64_eq (v : BitVec 128) (i : Fin 2) :
    getSimdLane v 64 i.val = (lane64 v i).zeroExtend 128 := by
  have hm : (1#128 <<< 64 - 1#128) = 18446744073709551615#128 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [getSimdLane, hm]
  simp only [lane64, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, getLsbD_mask64_128,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and, BitVec.getLsbD_extractLsb']
  by_cases h64 : b < 64
  · simp [h64, Nat.mul_comm i.val 64]
  · simp [h64]

private theorem getLsbD_zext128_shl_band {w : Nat} (x : BitVec w) (s b : Nat) (hb : b < 128) :
    (x.zeroExtend 128 <<< s).getLsbD b =
      (decide (s ≤ b ∧ b < s + w) && x.getLsbD (b - s)) := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and]
  by_cases hs : b < s
  · have h : ¬ (s ≤ b ∧ b < s + w) := by omega
    simp [hs, h]
  · by_cases hw : b < s + w
    · have h : s ≤ b ∧ b < s + w := ⟨by omega, hw⟩
      have hsub : b - s < 128 := by omega
      simp [hs, h, hsub]
    · have h : ¬ (s ≤ b ∧ b < s + w) := by omega
      have hge : w ≤ b - s := by omega
      simp [hs, h, BitVec.getLsbD_of_ge x (b - s) hge]

private theorem getLsbD_zext128_band {w : Nat} (x : BitVec w) (b : Nat) (hb : b < 128) :
    (x.zeroExtend 128).getLsbD b = (decide (b < w) && x.getLsbD b) := by
  simpa using getLsbD_zext128_shl_band x 0 b hb

private theorem getLsbD_append64 (hi lo : BitVec 64) (b : Nat) :
    ((hi ++ lo : BitVec 128)).getLsbD b = if b < 64 then lo.getLsbD b else hi.getLsbD (b - 64) :=
  BitVec.getLsbD_append

private theorem getLsbD_append128 (hi lo : BitVec 128) (b : Nat) :
    ((hi ++ lo : BitVec 256)).getLsbD b = if b < 128 then lo.getLsbD b else hi.getLsbD (b - 128) :=
  BitVec.getLsbD_append

private theorem dec_32_0 (j b : Nat) (hb : b < 32) :
    decide (32 * j + b < 32) = (j == 0) := by
  by_cases h : j = 0
  · subst h; simp [hb]
  · have hn : ¬ (32 * j + b < 32) := by omega
    simp [hn, h]

private theorem dec_32_k (k s j b : Nat) (hs : s = 32 * k) (hb : b < 32) :
    decide (s ≤ 32 * j + b ∧ 32 * j + b < s + 32) = (j == k) := by
  subst hs
  by_cases h : j = k
  · subst h; simp [hb]
  · have hn : ¬ (32 * k ≤ 32 * j + b ∧ 32 * j + b < 32 * k + 32) := by omega
    simp [hn, h]

private theorem dec_16_0 (j b : Nat) (hb : b < 16) :
    decide (16 * j + b < 16) = (j == 0) := by
  by_cases h : j = 0
  · subst h; simp [hb]
  · have hn : ¬ (16 * j + b < 16) := by omega
    simp [hn, h]

private theorem dec_16_k (k s j b : Nat) (hs : s = 16 * k) (hb : b < 16) :
    decide (s ≤ 16 * j + b ∧ 16 * j + b < s + 16) = (j == k) := by
  subst hs
  by_cases h : j = k
  · subst h; simp [hb]
  · have hn : ¬ (16 * k ≤ 16 * j + b ∧ 16 * j + b < 16 * k + 16) := by omega
    simp [hn, h]

private theorem or_shift_eq_pack4x32 (a0 a1 a2 a3 : BitVec 32) :
    (a0.zeroExtend 128 ||| a1.zeroExtend 128 <<< 32 |||
      a2.zeroExtend 128 <<< 64 ||| a3.zeroExtend 128 <<< 96) =
    pack4x32 (fun i => match i.val with | 0 => a0 | 1 => a1 | 2 => a2 | _ => a3) := by
  apply ext_lane32; intro i
  rw [lane32_pack4x32]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hp : 32 * i.val + b < 128 := by omega
  simp only [lane32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, hb, decide_true, Bool.true_and]
  rw [getLsbD_zext128_band a0 _ hp,
      getLsbD_zext128_shl_band a1 32 _ hp,
      getLsbD_zext128_shl_band a2 64 _ hp,
      getLsbD_zext128_shl_band a3 96 _ hp,
      dec_32_0 i.val b hb,
      dec_32_k 1 32 i.val b rfl hb,
      dec_32_k 2 64 i.val b rfl hb,
      dec_32_k 3 96 i.val b rfl hb]
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals simp

private theorem or_shift_eq_pack4x32_uzp (a0 a1 a2 a3 : BitVec 32) :
    (a0.zeroExtend 128 ||| a2.zeroExtend 128 <<< 64 |||
      a1.zeroExtend 128 <<< 32 ||| a3.zeroExtend 128 <<< 96) =
    pack4x32 (fun i => match i.val with | 0 => a0 | 1 => a1 | 2 => a2 | _ => a3) := by
  rw [show (a0.zeroExtend 128 ||| a2.zeroExtend 128 <<< 64 ||| a1.zeroExtend 128 <<< 32) =
      (a0.zeroExtend 128 ||| a1.zeroExtend 128 <<< 32 ||| a2.zeroExtend 128 <<< 64) by
    rw [BitVec.or_assoc, BitVec.or_comm (a2.zeroExtend 128 <<< 64), ← BitVec.or_assoc]]
  exact or_shift_eq_pack4x32 a0 a1 a2 a3

private theorem or_shift_eq_pack8x16 (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 16) :
    (a0.zeroExtend 128 ||| a1.zeroExtend 128 <<< 16 |||
      a2.zeroExtend 128 <<< 32 ||| a3.zeroExtend 128 <<< 48 |||
      a4.zeroExtend 128 <<< 64 ||| a5.zeroExtend 128 <<< 80 |||
      a6.zeroExtend 128 <<< 96 ||| a7.zeroExtend 128 <<< 112) =
    pack8x16 (fun i =>
      match i.val with
      | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
      | 4 => a4 | 5 => a5 | 6 => a6 | _ => a7) := by
  apply ext_lane16; intro i
  rw [lane16_pack8x16]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hp : 16 * i.val + b < 128 := by omega
  simp only [lane16, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, hb, decide_true, Bool.true_and]
  rw [getLsbD_zext128_band a0 _ hp,
      getLsbD_zext128_shl_band a1 16 _ hp,
      getLsbD_zext128_shl_band a2 32 _ hp,
      getLsbD_zext128_shl_band a3 48 _ hp,
      getLsbD_zext128_shl_band a4 64 _ hp,
      getLsbD_zext128_shl_band a5 80 _ hp,
      getLsbD_zext128_shl_band a6 96 _ hp,
      getLsbD_zext128_shl_band a7 112 _ hp,
      dec_16_0 i.val b hb,
      dec_16_k 1 16 i.val b rfl hb,
      dec_16_k 2 32 i.val b rfl hb,
      dec_16_k 3 48 i.val b rfl hb,
      dec_16_k 4 64 i.val b rfl hb,
      dec_16_k 5 80 i.val b rfl hb,
      dec_16_k 6 96 i.val b rfl hb,
      dec_16_k 7 112 i.val b rfl hb]
  rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals simp

/-! ## 2. Vector Permute, `REV64`, and `EXT` Bridges -/

@[simp, arm64_norm, wp_norm]
theorem exec_simdTrn1_8h (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdPermute true 0b01#2 rm 0b010#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn1_8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, List.range']
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  rw [getSimdLane_16_eq vn ⟨0, by decide⟩, getSimdLane_16_eq vm ⟨0, by decide⟩,
      getSimdLane_16_eq vn ⟨2, by decide⟩, getSimdLane_16_eq vm ⟨2, by decide⟩,
      getSimdLane_16_eq vn ⟨4, by decide⟩, getSimdLane_16_eq vm ⟨4, by decide⟩,
      getSimdLane_16_eq vn ⟨6, by decide⟩, getSimdLane_16_eq vm ⟨6, by decide⟩]
  exact or_shift_eq_pack8x16 _ _ _ _ _ _ _ _

@[simp, arm64_norm, wp_norm]
theorem exec_simdTrn2_8h (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdPermute true 0b01#2 rm 0b110#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn2_8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, List.range']
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  rw [getSimdLane_16_eq vn ⟨1, by decide⟩, getSimdLane_16_eq vm ⟨1, by decide⟩,
      getSimdLane_16_eq vn ⟨3, by decide⟩, getSimdLane_16_eq vm ⟨3, by decide⟩,
      getSimdLane_16_eq vn ⟨5, by decide⟩, getSimdLane_16_eq vm ⟨5, by decide⟩,
      getSimdLane_16_eq vn ⟨7, by decide⟩, getSimdLane_16_eq vm ⟨7, by decide⟩]
  exact or_shift_eq_pack8x16 _ _ _ _ _ _ _ _

@[simp, arm64_norm, wp_norm]
theorem exec_simdTrn1_4s (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdPermute true 0b10#2 rm 0b010#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn1_4s (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, List.range']
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  rw [getSimdLane_32_eq vn ⟨0, by decide⟩, getSimdLane_32_eq vm ⟨0, by decide⟩,
      getSimdLane_32_eq vn ⟨2, by decide⟩, getSimdLane_32_eq vm ⟨2, by decide⟩]
  exact or_shift_eq_pack4x32 _ _ _ _

@[simp, arm64_norm, wp_norm]
theorem exec_simdTrn2_4s (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdPermute true 0b10#2 rm 0b110#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn2_4s (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, List.range']
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  rw [getSimdLane_32_eq vn ⟨1, by decide⟩, getSimdLane_32_eq vm ⟨1, by decide⟩,
      getSimdLane_32_eq vn ⟨3, by decide⟩, getSimdLane_32_eq vm ⟨3, by decide⟩]
  exact or_shift_eq_pack4x32 _ _ _ _

@[simp, arm64_norm, wp_norm]
theorem exec_simdUzp1_4s (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdPermute true 0b10#2 rm 0b001#3 rn rd) s =
      (s.writeVReg128 rd (simdUzp1_4s (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, List.range']
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  rw [getSimdLane_32_eq vn ⟨0, by decide⟩, getSimdLane_32_eq vm ⟨0, by decide⟩,
      getSimdLane_32_eq vn ⟨2, by decide⟩, getSimdLane_32_eq vm ⟨2, by decide⟩]
  exact or_shift_eq_pack4x32_uzp _ _ _ _

@[simp, arm64_norm, wp_norm]
theorem exec_simdZip1_2d (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdPermute true 0b11#2 rm 0b011#3 rn rd) s =
      (s.writeVReg128 rd
        (pack2x64 fun c =>
          if c.val = 0 then lane64 (s.readVReg128 rn) 0
          else lane64 (s.readVReg128 rm) 0)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  rw [getSimdLane_64_eq vn ⟨0, by decide⟩, getSimdLane_64_eq vm ⟨0, by decide⟩]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  change ((lane64 vn ⟨0, by decide⟩).zeroExtend 128 |||
      (lane64 vm ⟨0, by decide⟩).zeroExtend 128 <<< 64).getLsbD b =
    (lane64 vm 0 ++ lane64 vn 0).getLsbD b
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  by_cases hb64 : b < 64
  · simp [hb64]
  · have hsub : b - 64 < 128 := by omega
    simp [hb64, hsub, BitVec.getLsbD_of_ge _ _ (show 64 ≤ b by omega)]

@[simp, arm64_norm, wp_norm]
theorem exec_simdZip2_2d (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdPermute true 0b11#2 rm 0b111#3 rn rd) s =
      (s.writeVReg128 rd
        (pack2x64 fun c =>
          if c.val = 0 then lane64 (s.readVReg128 rn) 1
          else lane64 (s.readVReg128 rm) 1)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  rw [getSimdLane_64_eq vn ⟨1, by decide⟩, getSimdLane_64_eq vm ⟨1, by decide⟩]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  change ((lane64 vn ⟨1, by decide⟩).zeroExtend 128 |||
      (lane64 vm ⟨1, by decide⟩).zeroExtend 128 <<< 64).getLsbD b =
    (lane64 vm 1 ++ lane64 vn 1).getLsbD b
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  by_cases hb64 : b < 64
  · simp [hb64]
  · have hsub : b - 64 < 128 := by omega
    simp [hb64, hsub, BitVec.getLsbD_of_ge _ _ (show 64 ≤ b by omega)]

@[simp, arm64_norm, wp_norm]
theorem exec_simdRev64_4s (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdTwoRegMisc true false 0b10#2 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdRev64_4s (s.readVReg128 rn))).advancePC := by
  simp [execInstWithSvc, List.range']
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [simdRev64_4s, pack4x32, lane32,
    getLsbD_append64, BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth, getLsbD_mask32_64]
  by_cases hb32 : b < 32
  · simp only [hb32, show b < 64 by omega, show 32 + b < 64 by omega,
      ↓reduceIte, decide_true, Bool.not_true, Bool.false_and, Bool.true_and,
      Bool.and_true, Bool.false_or]
    rfl
  · by_cases hb64 : b < 64
    · simp only [hb32, hb64, show b - 32 < 32 by omega, show b - 32 < 64 by omega,
        ↓reduceIte, decide_true, decide_false, Bool.not_false,
        Bool.and_false, Bool.true_and, Bool.and_true, Bool.or_false]
      exact (congrArg vn.getLsbD (Nat.zero_add (b - 32))).symm
    · by_cases hb96 : b < 96
      · have hsub : b - 64 < 32 := by omega
        have heq1 : b - 32 - 32 = b - 64 := by omega
        have heq2 : 64 + (32 + (b - 64)) = 96 + (b - 64) := by omega
        simp only [hb32, hb64, show ¬ (b - 32 < 32) by omega, heq1, hsub,
          show b - 64 < 64 by omega, show 32 + (b - 64) < 64 by omega, heq2,
          ↓reduceIte, decide_true, Bool.not_true, Bool.and_false, Bool.false_and,
          Bool.true_and, Bool.and_true, Bool.false_or]
        rfl
      · have heq1 : b - 32 - 32 = b - 64 := by omega
        have heq2 : b - 64 - 32 = b - 96 := by omega
        simp only [hb32, hb64, show ¬ (b - 32 < 32) by omega, heq1,
          show b - 64 < 64 by omega, show ¬ (b - 64 < 32) by omega, heq2,
          show b - 96 < 32 by omega, show b - 96 < 64 by omega,
          ↓reduceIte, decide_true, decide_false, Bool.not_false,
          Bool.and_false, Bool.true_and, Bool.and_true, Bool.or_false]
        rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdExt_16b_8 (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdExt true rm 8#4 rn rd) s =
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

/-! ## 3. Widening Signed Multiply & Multiply-Accumulate Bridges -/

private theorem ushr64_getSimdLane_16 (v : BitVec 128) (e : Fin 4) :
    getSimdLane (v >>> 64) 16 e.val = (lane16 v ⟨4 + e.val, by omega⟩).zeroExtend 128 := by
  have hm : (1#128 <<< 16 - 1#128) = 65535#128 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [getSimdLane, hm]
  simp only [lane16, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, getLsbD_65535_128,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and, BitVec.getLsbD_extractLsb']
  by_cases h16 : b < 16
  · simp [h16, show 64 + (e.val * 16 + b) = 16 * (4 + e.val) + b by omega]
  · simp [h16]

private theorem intToSimdLane_32_eq (z : Int) :
    intToSimdLane 32 z = (BitVec.ofInt 32 z).zeroExtend 128 := by
  have hm : (1#128 <<< 32 - 1#128) = 4294967295#128 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  by_cases hb32 : b < 32
  · rw [← truncate32_intToSimdLane_32 z]
    simp only [BitVec.getLsbD_setWidth, hb, hb32, decide_true, Bool.true_and]
  · rw [intToSimdLane, hm]
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, getLsbD_mask32_128,
      hb, hb32, decide_true, decide_false, Bool.and_false,
      BitVec.getLsbD_of_ge _ b (show 32 ≤ b by omega)]

private theorem ofInt32_mul_sext16 (x y : BitVec 16) :
    BitVec.ofInt 32 (x.toInt * y.toInt) = x.signExtend 32 * y.signExtend 32 := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by decide),
    BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt]

private theorem ofInt32_add_mul_sext16 (d : BitVec 32) (x y : BitVec 16) :
    BitVec.ofInt 32 (d.toInt + x.toInt * y.toInt) =
      d + x.signExtend 32 * y.signExtend 32 := by
  rw [← ofInt32_mul_sext16]
  conv_rhs => rw [← BitVec.ofInt_toInt (x := d)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofInt, Nat.reducePow]
  omega

@[simp, arm64_norm, wp_norm]
theorem exec_simdSmull_4s (q : Bool) (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdThreeDiff q false 0b01#2 rm 0b1100#4 rn rd) s =
      (s.writeVReg128 rd (simdSmull4s q (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, evalSimdThreeDiff, validSimdThreeDiff, List.range_succ, List.range_zero]
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  cases q
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [getSimdLane_16_eq vn ⟨0, by decide⟩, getSimdLane_16_eq vm ⟨0, by decide⟩,
        getSimdLane_16_eq vn ⟨1, by decide⟩, getSimdLane_16_eq vm ⟨1, by decide⟩,
        getSimdLane_16_eq vn ⟨2, by decide⟩, getSimdLane_16_eq vm ⟨2, by decide⟩,
        getSimdLane_16_eq vn ⟨3, by decide⟩, getSimdLane_16_eq vm ⟨3, by decide⟩]
    simp only [simdLaneSInt_16_zeroExtend, intToSimdLane_32_eq, ofInt32_mul_sext16]
    exact or_shift_eq_pack4x32 _ _ _ _
  · simp only [↓reduceIte]
    rw [ushr64_getSimdLane_16 vn ⟨0, by decide⟩, ushr64_getSimdLane_16 vm ⟨0, by decide⟩,
        ushr64_getSimdLane_16 vn ⟨1, by decide⟩, ushr64_getSimdLane_16 vm ⟨1, by decide⟩,
        ushr64_getSimdLane_16 vn ⟨2, by decide⟩, ushr64_getSimdLane_16 vm ⟨2, by decide⟩,
        ushr64_getSimdLane_16 vn ⟨3, by decide⟩, ushr64_getSimdLane_16 vm ⟨3, by decide⟩]
    simp only [simdLaneSInt_16_zeroExtend, intToSimdLane_32_eq, ofInt32_mul_sext16]
    exact or_shift_eq_pack4x32 _ _ _ _

@[simp, arm64_norm, wp_norm]
theorem exec_simdSmlal_4s (q : Bool) (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdThreeDiff q false 0b01#2 rm 0b1000#4 rn rd) s =
      (s.writeVReg128 rd
        (simdSmlal4s q (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, evalSimdThreeDiff, validSimdThreeDiff, List.range_succ, List.range_zero]
  refine writeV_adv_congr ?_
  set vd := s.readVReg128 rd
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  rw [getSimdLane_32_eq vd ⟨0, by decide⟩, getSimdLane_32_eq vd ⟨1, by decide⟩,
      getSimdLane_32_eq vd ⟨2, by decide⟩, getSimdLane_32_eq vd ⟨3, by decide⟩]
  simp only [simdLaneSInt_32_zeroExtend]
  cases q
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [getSimdLane_16_eq vn ⟨0, by decide⟩, getSimdLane_16_eq vm ⟨0, by decide⟩,
        getSimdLane_16_eq vn ⟨1, by decide⟩, getSimdLane_16_eq vm ⟨1, by decide⟩,
        getSimdLane_16_eq vn ⟨2, by decide⟩, getSimdLane_16_eq vm ⟨2, by decide⟩,
        getSimdLane_16_eq vn ⟨3, by decide⟩, getSimdLane_16_eq vm ⟨3, by decide⟩]
    simp only [simdLaneSInt_16_zeroExtend, intToSimdLane_32_eq, ofInt32_add_mul_sext16]
    exact or_shift_eq_pack4x32 _ _ _ _
  · simp only [↓reduceIte]
    rw [ushr64_getSimdLane_16 vn ⟨0, by decide⟩, ushr64_getSimdLane_16 vm ⟨0, by decide⟩,
        ushr64_getSimdLane_16 vn ⟨1, by decide⟩, ushr64_getSimdLane_16 vm ⟨1, by decide⟩,
        ushr64_getSimdLane_16 vn ⟨2, by decide⟩, ushr64_getSimdLane_16 vm ⟨2, by decide⟩,
        ushr64_getSimdLane_16 vn ⟨3, by decide⟩, ushr64_getSimdLane_16 vm ⟨3, by decide⟩]
    simp only [simdLaneSInt_16_zeroExtend, intToSimdLane_32_eq, ofInt32_add_mul_sext16]
    exact or_shift_eq_pack4x32 _ _ _ _

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdPerm

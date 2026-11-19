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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a

/-!
# `encapsulate1_serialized` (`B03`) — Segment 6 `compress_10` / `serialize_10` SIMD Bridges

`{svc}`-polymorphic AdvSIMD execution bridges and vector identities for 10-bit `ct1`
compression and serialization (`encaps1OutCt1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 bitsToBytes compressAndEncode compressCoeff polyAdd polyInvNtt polyNtt
  sampleMatrixWith sampleNtt sampleVecCbd2 sha3_512List vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 ext_lane16 ext_lane32 fin4_cases getSimdLane_32_eq lane16 lane16_dup8x16
  lane16_pack8x16 lane32 lane32_pack4x32 lane64 lane8 pack2x64 pack4x32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_and lane16_simdAdd8h simdAdd8h simdCmltZero8h simdExt16b simdSli2d simdSli4s
  simdSqdmulh4s simdTrn1_4s simdTrn1_8h simdTrn2_4s simdTrn2_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (
  lane16_neonCompress8h neonCompress8h neonCompressLane16_of_mod)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (
  byteEncodeChunk byteEncodeChunkVec compressAndEncode_eq_flatten_chunks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh (
  neonSerialize10Bytes neonSerialize10Bytes_eq neonSerialize10Half neonSerialize10Mix)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (encaps1OutCt1)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (sha3_512List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5 (
  uVecPoly16 uVecPoly16_spec)

private theorem writeV_adv_congr {s : State} {rd : BitVec 5} {a b : BitVec 128} (h : a = b) :
    (s.writeVReg128 rd a).advancePC = (s.writeVReg128 rd b).advancePC :=
  h ▸ rfl
/-! ## 1. `{svc}`-Polymorphic AdvSIMD Execution Bridges for `compress_10` & `serialize_10` -/

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdBic_4s_fc24 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0b111#3 0b01110#5 0b11100#5 rd) s =
      (s.writeVReg128 rd (s.readVReg128 rd &&& 0x03ffffff03ffffff03ffffff03ffffff#128)).advancePC := rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdBic_8h_fc8 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0b111#3 0b10110#5 0b11100#5 rd) s =
      (s.writeVReg128 rd (s.readVReg128 rd &&& dup8x16 0x03ff#16)).advancePC := rfl

private theorem getLsbD_mask32_128 :
    ∀ k : Fin 128, (4294967295#128).getLsbD k.val = decide (k.val < 32) := by
  decide +kernel

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
    have hm_b := fun (r : Nat) (hr : r < 128) => getLsbD_mask32_128 ⟨r, hr⟩
    simp only [mapLanes, BitVec.getLsbD_or, ih, BitVec.getLsbD_shiftLeft, hb, decide_true,
      Bool.true_and, BitVec.getLsbD_and, hm32]
    by_cases hbn : b < 32 * n
    · simp [hbn, show b < n * 32 by omega, show b < 32 * (n + 1) by omega]
    · by_cases hbn1 : b < 32 * (n + 1)
      · have hin : (v >>> (n * 32) &&& 4294967295#128) =
            (v.extractLsb' (32 * n) 32).zeroExtend 128 := by
          simpa [getSimdLane, lane32] using getSimdLane_32_eq v ⟨n, by omega⟩
        have hm' : (4294967295#128).getLsbD (b % 32) = true := by
          rw [hm_b (b % 32) (by omega)]; simp [show b % 32 < 32 by omega]
        simp [hbn, hbn1, show ¬ (b < n * 32) by omega, show b / 32 = n by omega,
          show b - n * 32 = b % 32 by omega, hm', hin]
      · have hm' := hm_b (b - n * 32) (by omega); dsimp only at hm'
        simp [hbn, hbn1, show ¬ (b < n * 32) by omega, hm', show ¬ (b - n * 32 < 32) by omega]

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
theorem exec_simdShl_4s_10 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0101#4 0b010#3 0b01010#5 rn rd) s =
      (s.writeVReg128 rd (pack4x32 fun k => lane32 (s.readVReg128 rn) k <<< 10)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_false, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane <<< 10) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, lane32_pack4x32]; bv_bits

@[simp, arm64_norm, wp_norm]
theorem exec_simdUshr_4s_6 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0111#4 0b010#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (pack4x32 fun k => lane32 (s.readVReg128 rn) k >>> 6)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane >>> 6) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, lane32_pack4x32]; bv_bits

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

private theorem dec_32_k (k s j b : Nat) (hs : s = 32 * k) (hb : b < 32) :
    decide (s ≤ 32 * j + b ∧ 32 * j + b < s + 32) = (j == k) := by
  subst hs; by_cases h : j = k
  · subst h; simp [hb]
  · have hn : ¬(32 * k ≤ 32 * j + b ∧ 32 * j + b < 32 * k + 32) := by omega
    simp [hn, h]

private theorem or_shift_eq_pack2x64 (a0 a1 : BitVec 64) :
    (a0.zeroExtend 128 ||| a1.zeroExtend 128 <<< 64) =
      pack2x64 (fun i => if i.val = 0 then a0 else a1) := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  dsimp only [pack2x64]
  have hz := getLsbD_zext128_shl a0 0 b hb
  simp only [BitVec.shiftLeft_zero, Nat.zero_le, Nat.zero_add, Nat.sub_zero, true_and] at hz
  rw [BitVec.getLsbD_or, BitVec.getLsbD_append, hz, getLsbD_zext128_shl a1 64 b hb]
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
  have hz := getLsbD_zext128_shl a0 0 _ hp
  simp only [BitVec.shiftLeft_zero, Nat.sub_zero] at hz
  simp only [lane32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, hb, decide_true, Bool.true_and]
  rw [hz, getLsbD_zext128_shl a1 32 _ hp, getLsbD_zext128_shl a2 64 _ hp,
      getLsbD_zext128_shl a3 96 _ hp, dec_32_k 0 0 i.val b rfl hb,
      dec_32_k 1 32 i.val b rfl hb, dec_32_k 2 64 i.val b rfl hb, dec_32_k 3 96 i.val b rfl hb]
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals simp

private theorem sli32_10_lane_eq (x d : BitVec 32) :
    (((d.zeroExtend 128 &&& ~~~((4294967295#128 <<< 10) &&& 4294967295#128)) |||
      (((x.zeroExtend 128 <<< 10) &&& 4294967295#128) &&&
        ((4294967295#128 <<< 10) &&& 4294967295#128))) &&& 4294967295#128) =
      ((d &&& 1023#32) ||| (x <<< 10)).zeroExtend 128 := by bv_bits

private theorem sli64_20_lane_eq (x d : BitVec 64) :
    (((d.zeroExtend 128 &&& ~~~((18446744073709551615#128 <<< 20) &&& 18446744073709551615#128)) |||
      (((x.zeroExtend 128 <<< 20) &&& 18446744073709551615#128) &&&
        ((18446744073709551615#128 <<< 20) &&& 18446744073709551615#128))) &&&
      18446744073709551615#128) =
      ((d &&& 1048575#64) ||| (x <<< 20)).zeroExtend 128 := by bv_bits

@[simp, arm64_norm, wp_norm]
theorem exec_simdSli_4s_10 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0101#4 0b010#3 0b01010#5 rn rd) s =
      (s.writeVReg128 rd (simdSli4s (s.readVReg128 rd) (s.readVReg128 rn) 10)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn; set vd := s.readVReg128 rd
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
  have hsli := sli32_10_lane_eq
  conv at hsli => ext x d; lhs; simp
  rw [h32_0 vn, h32_0 vd, h32_1 vn, h32_1 vd, h32_2 vn, h32_2 vd, h32_3 vn, h32_3 vd,
      hsli, hsli, hsli, hsli]
  exact or_shift_eq_pack4x32 _ _ _ _
@[simp, arm64_norm, wp_norm]
theorem exec_simdSli_2d_20 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b1010#4 0b100#3 0b01010#5 rn rd) s =
      (s.writeVReg128 rd (simdSli2d (s.readVReg128 rd) (s.readVReg128 rn) 20)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn; set vd := s.readVReg128 rd
  dsimp only [zipLanes, laneMask]
  simp only [Nat.zero_mul, Nat.one_mul, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero,
    BitVec.zero_or, show (1#128 <<< 64 - 1#128 : BitVec 128) = 18446744073709551615#128 from rfl]
  have h64_0 : ∀ v : BitVec 128, v &&& 18446744073709551615#128 = (lane64 v 0).zeroExtend 128 :=
    fun v => by simpa [getSimdLane] using getSimdLane_64_eq v ⟨0, by decide⟩
  have h64_1 : ∀ v : BitVec 128, v >>> 64 &&& 18446744073709551615#128 = (lane64 v 1).zeroExtend 128 :=
    fun v => getSimdLane_64_eq v ⟨1, by decide⟩
  have hsli := sli64_20_lane_eq
  conv at hsli => ext x d; lhs; simp
  rw [h64_0 vn, h64_0 vd, h64_1 vn, h64_1 vd, hsli, hsli]
  exact or_shift_eq_pack2x64 _ _

private theorem getSimdLane_8_eq (v : BitVec 128) (i : Fin 16) :
    getSimdLane v 8 i.val = (lane8 v i).zeroExtend 128 := by
  have hm : ∀ b : Nat, (1#128 <<< 8 - 1#128).getLsbD b = decide (b < 8) := fun b => by
    change (255#128).toNat.testBit b = decide (b < 8)
    rw [show (255#128).toNat = 2 ^ 8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [getSimdLane]
  simp only [lane8, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, hm,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and, BitVec.getLsbD_extractLsb']
  by_cases h8 : b < 8
  · simp [h8, Nat.mul_comm i.val 8]
  · simp [h8]

@[simp, arm64_norm, wp_norm]
theorem exec_simdDupScalar_b4 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdDupScalar 0b01001#5 rn rd) s =
      (s.writeVReg128 rd ((lane8 (s.readVReg128 rn) 4).zeroExtend 128)).advancePC := by
  simp [execInstWithSvc, evalSimdDupScalar]
  exact writeV_adv_congr (by simpa using getSimdLane_8_eq (s.readVReg128 rn) 4)

@[simp, arm64_norm, wp_norm]
theorem exec_simdDupScalar_b12 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdDupScalar 0b11001#5 rn rd) s =
      (s.writeVReg128 rd ((lane8 (s.readVReg128 rn) 12).zeroExtend 128)).advancePC := by
  simp [execInstWithSvc, evalSimdDupScalar]
  exact writeV_adv_congr (by simpa using getSimdLane_8_eq (s.readVReg128 rn) 12)
/-! ## 2. Vector `compress_10` / `serialize_10` & `encaps1OutCt1` Identities -/

theorem seg6_compress10_eq (vn : BitVec 128) :
    let u := simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn
    let evenIn := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j <<< 10) &&& 0x03ffffff03ffffff03ffffff03ffffff#128) k +
        lane32 (pack4x32 fun _ => 1664#32) k
    let oddIn := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j >>> 6) &&& (pack4x32 fun _ => 67107840#32)) k +
        lane32 (pack4x32 fun _ => 1664#32) k
    let cMul := pack4x32 fun _ => 10321340#32
    let evenOut := pack4x32 fun k => lane32 (simdSqdmulh4s evenIn cMul) k >>> 4
    let oddOut := pack4x32 fun k => lane32 (simdSqdmulh4s oddIn cMul) k >>> 4
    (simdTrn1_8h evenOut oddOut &&& dup8x16 0x03ff#16) = neonCompress8h 10 vn := by
  dsimp only; unfold neonCompress8h
  have hu : simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn =
      simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16) := by
    apply ext_lane16; intro i; rw [lane16_simdAdd8h, lane16_simdAdd8h, BitVec.add_comm]
  rw [hu]; set u := simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16)
  have l32_and (a b : BitVec 128) (k : Fin 4) : lane32 (a &&& b) k = lane32 a k &&& lane32 b k := by
    apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [lane32, hr]
  have hm_ev (w : BitVec 32) : (w <<< 10) &&& 0x03ffffff#32 = (w <<< 10) &&& (0x0000ffff#32 <<< 10) := by
    bv_bits
  have hev : (pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j <<< 10) &&& 0x03ffffff03ffffff03ffffff03ffffff#128) k +
        lane32 (pack4x32 fun _ => 1664#32) k) =
      (pack4x32 fun k => ((lane32 u k <<< 10) &&& (0x0000ffff#32 <<< 10)) + 1664#32) := by
    apply ext_lane32; intro k
    rw [lane32_pack4x32, lane32_pack4x32, l32_and, lane32_pack4x32, lane32_pack4x32]
    have hc : lane32 0x03ffffff03ffffff03ffffff03ffffff#128 k = 0x03ffffff#32 := by
      induction k using fin4_cases <;> rfl
    rw [hc, hm_ev]
  have hod : (pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j >>> 6) &&& (pack4x32 fun _ => 67107840#32)) k +
        lane32 (pack4x32 fun _ => 1664#32) k) =
      (pack4x32 fun k => ((lane32 u k >>> (16 - 10)) &&& (0x0000ffff#32 <<< 10)) + 1664#32) := by
    apply ext_lane32; intro k
    rw [lane32_pack4x32, lane32_pack4x32, l32_and, lane32_pack4x32, lane32_pack4x32, lane32_pack4x32]
    rfl
  rw [hev, hod]; rfl

theorem seg6_serialize10_mix_eq (vn : BitVec 128) :
    let c := neonCompress8h 10 vn
    let mixt := simdSli4s (simdTrn1_8h c c) (simdTrn2_8h c c) 10
    simdSli2d (simdTrn1_4s mixt mixt) (simdTrn2_4s mixt mixt) 20 = neonSerialize10Mix c := by
  dsimp only [neonSerialize10Mix]
  have hc : neonCompress8h 10 vn &&& dup8x16 0x03ff#16 = neonCompress8h 10 vn := by
    unfold neonCompress8h; dsimp only
    rw [show BitVec.ofNat 16 ((1 <<< 10) - 1) = 0x03ff#16 from rfl, BitVec.and_assoc, BitVec.and_self]
  rw [hc]
theorem cells10_eq_neonSerialize10Half (a : BitVec 64) (v : BitVec 128) :
    let m := neonSerialize10Mix v
    let mHi := simdExt16b m m 8
    (a ↦₃₂ (lane64 m 0).truncate 32) ∗ ((a + 4#64) ↦₈ lane8 m 4) ∗
    ((a + 5#64) ↦₃₂ (lane64 mHi 0).truncate 32) ∗ ((a + 9#64) ↦₈ lane8 m 12) =
    (a ↦ₛ neonSerialize10Half v) := by
  dsimp only [neonSerialize10Half]
  simp only [List.append_assoc, pointsToBytes_append, unpack32_length, List.length_singleton,
    pointsToBytes_singleton, ← pointsTo32_eq_pointsToBytes,
    show a + 4#64 + BitVec.ofNat 64 1 = a + 5#64 by bv_omega,
    show a + 5#64 + BitVec.ofNat 64 4 = a + 9#64 by bv_omega]

theorem cells20_eq_neonSerialize10Bytes (a : BitVec 64) (v0 v1 : BitVec 128) :
    let m0 := neonSerialize10Mix v0
    let m1 := neonSerialize10Mix v1
    (a ↦₃₂ (lane64 m0 0).truncate 32) ∗ ((a + 4#64) ↦₈ lane8 m0 4) ∗
    ((a + 5#64) ↦₃₂ (lane64 (simdExt16b m0 m0 8) 0).truncate 32) ∗ ((a + 9#64) ↦₈ lane8 m0 12) ∗
    ((a + 10#64) ↦₃₂ (lane64 m1 0).truncate 32) ∗ ((a + 14#64) ↦₈ lane8 m1 4) ∗
    ((a + 15#64) ↦₃₂ (lane64 (simdExt16b m1 m1 8) 0).truncate 32) ∗ ((a + 19#64) ↦₈ lane8 m1 12) =
    (a ↦ₛ neonSerialize10Bytes v0 v1) := by
  dsimp only
  have hc0 := cells10_eq_neonSerialize10Half a v0
  have hc1 := cells10_eq_neonSerialize10Half (a + 10#64) v1
  dsimp only at hc0 hc1
  rw [neonSerialize10Bytes, pointsToBytes_append,
    show (neonSerialize10Half v0).length = 10 by simp [neonSerialize10Half], ← hc0, ← hc1]
  simp only [sepConj_assoc, show a + 10#64 + 4#64 = a + 14#64 by bv_omega,
    show a + 10#64 + 5#64 = a + 15#64 by bv_omega, show a + 10#64 + 9#64 = a + 19#64 by bv_omega]

@[expose] def neonCompressSerialize10Poly (re : Poly16) : List (BitVec 8) :=
  ((List.range 16).map fun c =>
    neonSerialize10Bytes (neonCompress8h 10 (polyVecNat re (2 * c)))
      (neonCompress8h 10 (polyVecNat re (2 * c + 1)))).flatten

@[simp] theorem neonCompressSerialize10Poly_length (re : Poly16) :
    (neonCompressSerialize10Poly re).length = 320 := by
  have hr : List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
  unfold neonCompressSerialize10Poly; rw [hr]; simp [neonSerialize10Bytes, neonSerialize10Half]

theorem neonCompressSerialize10Poly_eq {re : Poly16} {f : Poly}
    (hb : PolyBounded16 1664 re) (hr : PolyRepresents re f) :
    neonCompressSerialize10Poly re = compressAndEncode 10 f := by
  unfold neonCompressSerialize10Poly
  rw [compressAndEncode_eq_flatten_chunks 10 (by decide) f]
  apply congrArg List.flatten; apply List.map_congr_left; intro c hc
  have hc16 : c < 16 := List.mem_range.mp hc
  rw [neonSerialize10Bytes_eq]
  unfold byteEncodeChunkVec byteEncodeChunk
  apply congrArg bitsToBytes; apply Array.ext
  · simp
  · intro idx hi1 hi2
    have hidx : idx < 160 := by simpa using hi1
    have hj : idx / 10 < 16 := by omega
    have hpos : 16 * c + idx / 10 < 256 := by omega
    have hb_i := hb.2 (16 * c + idx / 10) hpos
    have heq := neonCompressLane16_of_mod (d := 10) (Or.inr (Or.inr (Or.inl rfl)))
      (by omega) (by omega) (hr.2 (16 * c + idx / 10) hpos)
    have hlt_c : compressCoeff 10 (f.getD (16 * c + idx / 10) 0) < 2 ^ 16 := by
      unfold compressCoeff; exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    have hmap : (f.map (compressCoeff 10)).getD (16 * c + idx / 10) 0 =
        compressCoeff 10 (f.getD (16 * c + idx / 10) 0) := by
      by_cases hf : 16 * c + idx / 10 < f.size
      · simp [Array.getD, hf]
      · simp [Array.getD, hf]; unfold compressCoeff; decide
    simp only [Array.getElem_ofFn, hmap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_c]
    rw [← heq]
    by_cases hj8 : idx / 10 < 8
    · simp only [hj8, ↓reduceDIte, lane16_neonCompress8h (by decide : 1 ≤ 10) (by decide : 10 ≤ 16),
        polyVecNat, lane16_pack8x16, show 8 * (2 * c) + idx / 10 = 16 * c + idx / 10 by omega]
    · have hj8' : idx / 10 - 8 < 8 := by omega
      simp only [hj8, hj8', ↓reduceDIte, lane16_neonCompress8h (by decide : 1 ≤ 10) (by decide : 10 ≤ 16),
        polyVecNat, lane16_pack8x16, show 8 * (2 * c + 1) + (idx / 10 - 8) = 16 * c + idx / 10 by omega]
section PureCt1
attribute [local irreducible] sha3_512List sampleNtt polyNtt polyInvNtt sampleVecCbd2

theorem encaps1OutCt1_eq {hdr rand : List (BitVec 8)}
    (hhdr : hdr.length = 64) (hrand : rand.length = 32) :
    let rho := hdr.take 32
    let pkHash := (hdr.drop 32).take 32
    let hashed := sha3_512List (rand ++ pkHash)
    let coins := (hashed.drop 32).take 32
    neonCompressSerialize10Poly (uVecPoly16 rho coins 0) ++
      neonCompressSerialize10Poly (uVecPoly16 rho coins 1) ++
      neonCompressSerialize10Poly (uVecPoly16 rho coins 2) =
      encaps1OutCt1 hdr rand := by
  dsimp only
  unfold encaps1OutCt1
  have htr : rand.take 32 = rand := List.take_of_length_le (Nat.le_of_eq hrand)
  have hrho : (hdr.take 32).length = 32 := by simp [List.length_take, hhdr]
  have hhashed : (sha3_512List (rand ++ (hdr.drop 32).take 32)).length = 64 :=
    sha3_512List_length _
  have hcoins : (((sha3_512List (rand ++ (hdr.drop 32).take 32)).drop 32).take 32).length = 32 := by
    simp [List.length_take, List.length_drop, hhashed]
  obtain ⟨hb0, hr0⟩ := uVecPoly16_spec hrho hcoins (by decide : 0 < 3)
  obtain ⟨hb1, hr1⟩ := uVecPoly16_spec hrho hcoins (by decide : 1 < 3)
  obtain ⟨hb2, hr2⟩ := uVecPoly16_spec hrho hcoins (by decide : 2 < 3)
  have hrng : List.range 3 = [0, 1, 2] := by decide
  simp only [htr, hrng, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]
  have hg (row : Nat) (h : row < 3) (f : Fin 3 → Poly) :
      (Array.ofFn f).getD row zeroPoly = f ⟨row, h⟩ := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]; simp [h]
  rw [hg 0 (by decide), hg 1 (by decide), hg 2 (by decide),
    neonCompressSerialize10Poly_eq hb0 hr0,
    neonCompressSerialize10Poly_eq hb1 hr1,
    neonCompressSerialize10Poly_eq hb2 hr2]

end PureCt1

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd

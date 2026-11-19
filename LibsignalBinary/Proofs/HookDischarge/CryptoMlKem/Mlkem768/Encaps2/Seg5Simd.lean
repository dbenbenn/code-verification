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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh

/-!
# `encapsulate2` (`B20`) — Segment 5 AdvSIMD Bridges & Loop Step Identities (`Seg5Simd`)

`{svc}`-polymorphic execution bridges for Segment 5's `4S`/`8H`/`4H` compression and
serialization instructions, plus exact vector/word identities for Loop 1 and Loop 2.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 neonBarrettReduce16 neonCompressSerialize4 neonMontgomeryMul16 neonMontgomeryReduce16
  sqdmulh16 sqdmulh32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 ext_lane16 ext_lane32 fin4_cases getSimdLane_16_eq getSimdLane_32_eq lane16
  lane16_dup8x16 lane16_mapSimdLanes_true_16 lane16_pack8x16 lane32 lane32_pack4x32 lane64
  pack4x32 pack8x16 simdLaneSInt_32_zeroExtend truncate32_intToSimdLane_32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_simdAdd8h lane16_simdCmltZero8h lane16_simdMla8h lane16_simdMul8h lane16_simdSqdmulh8h
  lane16_simdSshr8h lane16_simdSub8h lane32_simdSqdmulh4s simdAdd8h simdCmltZero8h simdExt16b
  simdMla8h simdMul8h simdSqdmulh4s simdSqdmulh8h simdSshr8h simdSub8h simdTrn1_8h simdUshl8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  barrett_mla_0xf2ff montgomery_precomp_mul)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (
  lane16_neonCompress8h neonCompress8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (simdAddv4h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh (
  lane64_simdExt16b_8_0)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow (
  evalBitfield_bfxil_0_16 neonCompressSerialize4_eq_flatten neonSerialize4Bytes
  neonSerialize4HalfWord32 neonSerialize4Lowt neonSerialize4Word64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (polyVecNat)

/-! ## 1. `4S` Map/Zip & `SQDMULH.4S` Helpers -/

private theorem writeV_adv_congr {s : State} {rd : BitVec 5} {a b : BitVec 128} (h : a = b) :
    (s.writeVReg128 rd a).advancePC = (s.writeVReg128 rd b).advancePC :=
  h ▸ rfl

private theorem writeV_fpsr_adv_congr {s : State} {rd : BitVec 5} {f : BitVec 32}
    {a b : BitVec 128} (h : a = b) :
    ((s.writeVReg128 rd a).orFpsr f).advancePC = ((s.writeVReg128 rd b).orFpsr f).advancePC :=
  h ▸ rfl

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

private theorem zipLanes_32_getLsbD (vn vm : BitVec 128)
    (f : BitVec 128 → BitVec 128 → BitVec 128) :
    ∀ (n b : Nat), b < 128 →
      (zipLanes 32 vn vm f n).getLsbD b =
        if b < 32 * n then
          (f ((vn.extractLsb' (32 * (b / 32)) 32).zeroExtend 128)
             ((vm.extractLsb' (32 * (b / 32)) 32).zeroExtend 128)).getLsbD (b % 32)
        else false
  | 0, b, _ => by simp [zipLanes]
  | n + 1, b, hb => by
    have ih := zipLanes_32_getLsbD vn vm f n b hb
    have hm32 : laneMask 32 = 4294967295#128 := rfl
    have hm_b := fun (r : Nat) (hr : r < 128) => getLsbD_mask32_128 ⟨r, hr⟩
    simp only [zipLanes, BitVec.getLsbD_or, ih, BitVec.getLsbD_shiftLeft, hb, decide_true,
      Bool.true_and, BitVec.getLsbD_and, hm32]
    by_cases hbn : b < 32 * n
    · simp [hbn, show b < n * 32 by omega, show b < 32 * (n + 1) by omega]
    · by_cases hbn1 : b < 32 * (n + 1)
      · have hin1 : (vn >>> (n * 32) &&& 4294967295#128) =
            (vn.extractLsb' (32 * n) 32).zeroExtend 128 := by
          simpa [getSimdLane, lane32] using getSimdLane_32_eq vn ⟨n, by omega⟩
        have hin2 : (vm >>> (n * 32) &&& 4294967295#128) =
            (vm.extractLsb' (32 * n) 32).zeroExtend 128 := by
          simpa [getSimdLane, lane32] using getSimdLane_32_eq vm ⟨n, by omega⟩
        have hm' : (4294967295#128).getLsbD (b % 32) = true := by
          rw [hm_b (b % 32) (by omega)]; simp [show b % 32 < 32 by omega]
        simp [hbn, hbn1, show ¬ (b < n * 32) by omega, show b / 32 = n by omega,
          show b - n * 32 = b % 32 by omega, hm', hin1, hin2]
      · have hm' := hm_b (b - n * 32) (by omega); dsimp only at hm'
        simp [hbn, hbn1, show ¬ (b < n * 32) by omega, hm', show ¬ (b - n * 32 < 32) by omega]

private theorem lane32_zipSimdLanes_32 (vn vm : BitVec 128)
    (f : BitVec 128 → BitVec 128 → BitVec 128) (i : Fin 4) :
    lane32 (zipSimdLanes true 32 vn vm f) i =
      (f ((lane32 vn i).zeroExtend 128) ((lane32 vm i).zeroExtend 128)).truncate 32 := by
  rw [zipSimdLanes_true_32]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hpos : 32 * i.val + b < 128 := by omega
  simp only [lane32, BitVec.getLsbD_extractLsb', BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
    zipLanes_32_getLsbD vn vm f 4 _ hpos, hpos,
    show (32 * i.val + b) / 32 = i.val by omega,
    show (32 * i.val + b) % 32 = b by omega, ↓reduceIte]

private theorem sshift32_trunc32_toInt (x : BitVec 64) :
    ((x.sshiftRight 32).truncate 32).toInt = x.toInt / 4294967296 := by
  have htr : (x.sshiftRight 32).truncate 32 = (x >>> 32).truncate 32 := by
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    rw [BitVec.truncate_eq_setWidth, BitVec.truncate_eq_setWidth,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight]
    have h1 : ¬ (64 ≤ b) := by omega
    have h2 : 32 + b < 64 := by omega
    simp only [hb, h1, h2, decide_true, decide_false, Bool.not_false, Bool.true_and, ↓reduceIte]
  rw [htr]
  set hi : BitVec 32 := (x >>> 32).truncate 32
  have hx_lt := x.isLt
  have hhi_nat : hi.toNat = x.toNat / 4294967296 := by
    simp only [hi, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.reducePow]
    exact Nat.mod_eq_of_lt (by omega)
  have hmsb : hi.msb = x.msb := by
    simp [hi, BitVec.msb_eq_getLsbD_last]
  rw [BitVec.toInt_eq_msb_cond hi, BitVec.toInt_eq_msb_cond x, hmsb, hhi_nat]
  cases x.msb <;> simp only [↓reduceIte, Bool.false_eq_true, Nat.reducePow] <;> omega

private theorem sqdmulh32_prod_bound {a b : BitVec 32}
    (hne : ¬ (a = 0x80000000#32 ∧ b = 0x80000000#32)) :
    -4611686016279904256 ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt ≤ 4611686016279904256 := by
  have ha_lo := BitVec.le_toInt a; have ha_hi := @BitVec.toInt_lt 32 a
  have hb_lo := BitVec.le_toInt b; have hb_hi := @BitVec.toInt_lt 32 b
  have hmin32 : (0x80000000#32 : BitVec 32).toInt = -2147483648 := rfl
  have hnot_both : ¬ (a.toInt = -2147483648 ∧ b.toInt = -2147483648) := fun ⟨ha, hb⟩ =>
    hne ⟨BitVec.eq_of_toInt_eq (ha.trans hmin32.symm), BitVec.eq_of_toInt_eq (hb.trans hmin32.symm)⟩
  by_cases ha_min : a.toInt = -2147483648
  · rw [ha_min]; constructor <;> omega
  · have ha_gt : -2147483647 ≤ a.toInt := by omega
    constructor <;> by_cases hb0 : 0 ≤ b.toInt
    · have := Int.mul_le_mul_of_nonneg_right ha_gt hb0; omega
    · have := Int.mul_le_mul_of_nonpos_right (by omega : a.toInt ≤ 2147483647) (by omega : b.toInt ≤ 0); omega
    · have := Int.mul_le_mul_of_nonneg_right (by omega : a.toInt ≤ 2147483647) hb0; omega
    · have := Int.mul_le_mul_of_nonpos_right ha_gt (by omega : b.toInt ≤ 0); omega

private theorem sqdmulh32_toInt {a b : BitVec 32}
    (hne : ¬ (a = 0x80000000#32 ∧ b = 0x80000000#32)) :
    (sqdmulh32 a b).toInt = (a.toInt * b.toInt) / 2147483648 := by
  have ha_lo := BitVec.le_toInt a; have ha_hi := @BitVec.toInt_lt 32 a
  have hb_lo := BitVec.le_toInt b; have hb_hi := @BitVec.toInt_lt 32 b
  have hprod_bound := sqdmulh32_prod_bound hne
  have hcond : (a == 0x80000000#32 && b == 0x80000000#32) = false := by
    cases ha8 : (a == 0x80000000#32) <;> cases hb8 : (b == 0x80000000#32) <;> simp_all
  unfold sqdmulh32; rw [hcond]; simp only [Bool.false_eq_true, ↓reduceIte]
  have hmul64 : (a.signExtend 64 * b.signExtend 64).toInt = a.toInt * b.toInt := by
    rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by omega),
      BitVec.toInt_signExtend_of_le (by omega), Int.bmod_eq_of_le] <;> omega
  have hshl1 : ((a.signExtend 64 * b.signExtend 64) <<< 1).toInt = 2 * (a.toInt * b.toInt) := by
    have : ((a.signExtend 64 * b.signExtend 64) <<< 1) =
        (a.signExtend 64 * b.signExtend 64) * 2#64 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq]
    rw [this, BitVec.toInt_mul, hmul64]
    change ((a.toInt * b.toInt) * 2).bmod 18446744073709551616 = 2 * (a.toInt * b.toInt)
    rw [Int.bmod_eq_of_le] <;> omega
  rw [sshift32_trunc32_toInt, hshl1]; omega

/-! ## 2. `{svc}`-Polymorphic AdvSIMD & GPR↔Vec Execution Bridges -/

/-- Saturation-flag payload emitted by `SQDMULH Vd.4S, Vn.4S, Vm.4S` (kept opaque to `simp`). -/
def sqdmulh4sFlags (vn vm : BitVec 128) : BitVec 32 :=
  (evalSimdThreeSameExtSatFlags true false 0b10#2 0b10110#5 vn vm).getD 0#32

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_8h_15 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b10000#5 15#5 rd) s =
      (s.writeVReg128 rd (dup8x16 0x000f#16)).advancePC := rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdBic_4s_15 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b00010#5 15#5 rd) s =
      (s.writeVReg128 rd (s.readVReg128 rd &&& 0xfffffff0fffffff0fffffff0fffffff0#128)).advancePC :=
  rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdAnd_16b {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b00#2 rm 0b00011#5 rn rd) s =
      (s.writeVReg128 rd (s.readVReg128 rn &&& s.readVReg128 rm)).advancePC := rfl

@[simp, arm64_norm, wp_norm]
theorem exec_fmov_w_s {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.fmovGprVec false 0b00#2 0b00#2 0b110#3 rn rd) s =
      (s.writeReg32 (Reg.fromZRBits rd) ((s.readVReg128 rn).truncate 32)).advancePC := rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdDup_4s {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 0b00100#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd
        (pack4x32 fun _ => (s.readReg64 (Reg.fromZRBits rn)).truncate 32)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_false, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 0#128
    (fun _ => (s.readReg64 (Reg.fromZRBits rn)).zeroExtend 128 &&& (1#128 <<< 32 - 1#128)) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, lane32_pack4x32]
  bv_bits

@[simp, arm64_norm, wp_norm]
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
    cases x.msb
    · simp
    · simp; omega
  rw [hbit]
  cases hm : x.msb
  · have hf : ¬ (x.toInt < 0) := fun h => by rw [hneg.mp h] at hm; cases hm
    simp [hf]
  · simp [hneg.mpr hm]

@[simp, arm64_norm, wp_norm]
theorem exec_simdShl_4s_4 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0100#4 0b100#3 0b01010#5 rn rd) s =
      (s.writeVReg128 rd (pack4x32 fun k => lane32 (s.readVReg128 rn) k <<< 4)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_false, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane <<< 4) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, lane32_pack4x32]; bv_bits

@[simp, arm64_norm, wp_norm]
theorem exec_simdUshr_4s_12 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0110#4 0b100#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (pack4x32 fun k => lane32 (s.readVReg128 rn) k >>> 12)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane >>> 12) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, lane32_pack4x32]; bv_bits

@[simp, arm64_norm, wp_norm]
theorem exec_simdUshr_4s_4 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0111#4 0b100#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (pack4x32 fun k => lane32 (s.readVReg128 rn) k >>> 4)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane >>> 4) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, lane32_pack4x32]; bv_bits

@[simp, arm64_norm, wp_norm]
theorem exec_simdAdd_4s {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b10#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd
        (pack4x32 fun k => lane32 (s.readVReg128 rn) k + lane32 (s.readVReg128 rm) k)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq,
    show (8 <<< (0b10#2).toNat) = 32 from rfl]
  refine writeV_adv_congr ?_
  apply ext_lane32; intro i
  rw [lane32_zipSimdLanes_32, lane32_pack4x32]
  set x := lane32 (s.readVReg128 rn) i
  set y := lane32 (s.readVReg128 rm) i
  change (x.zeroExtend 128 + y.zeroExtend 128).setWidth 32 = x + y
  rw [BitVec.setWidth_add _ _ (by decide)]
  congr 1 <;> bv_bits

@[simp, arm64_norm, wp_norm]
theorem exec_simdSqdmulh_4s {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b10#2 rm 0b10110#5 rn rd) s =
      ((s.writeVReg128 rd (simdSqdmulh4s (s.readVReg128 rn) (s.readVReg128 rm))).orFpsr
        (sqdmulh4sFlags (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  have hflags : evalSimdThreeSameExtSatFlags true false 0b10#2 0b10110#5
      (s.readVReg128 rn) (s.readVReg128 rm) =
      some (sqdmulh4sFlags (s.readVReg128 rn) (s.readVReg128 rm)) := rfl
  simp only [execInstWithSvc, BEq.beq, Bool.false_eq_true,
    decide_false, ↓reduceIte, BitVec.reduceEq, hflags, evalSimdThreeSameExt, applySimdSatResult,
    show (8 <<< (0b10#2).toNat) = 32 from rfl]
  refine writeV_fpsr_adv_congr ?_
  apply ext_lane32; intro i
  rw [lane32_zipSimdLanes_32, lane32_simdSqdmulh4s,
    simdLaneSInt_32_zeroExtend, simdLaneSInt_32_zeroExtend]
  set x := lane32 (s.readVReg128 rn) i
  set y := lane32 (s.readVReg128 rm) i
  by_cases hmin : x = 0x80000000#32 ∧ y = 0x80000000#32
  · rcases hmin with ⟨hx, hy⟩; rw [hx, hy]; decide
  · have hsq := sqdmulh32_toInt hmin
    have hprod_bound := sqdmulh32_prod_bound hmin
    have hdiv_eq : aslRShr (2 * x.toInt * y.toInt) 32 false = (x.toInt * y.toInt) / 2147483648 := by
      change (2 * x.toInt * y.toInt) / 4294967296 = (x.toInt * y.toInt) / 2147483648
      rw [Int.mul_assoc 2 x.toInt y.toInt]; omega
    have hgt : ¬ ((x.toInt * y.toInt) / 2147483648 > 2147483648 - 1) := by omega
    have hlt : ¬ ((x.toInt * y.toInt) / 2147483648 < -2147483648) := by omega
    rw [hdiv_eq]; unfold aslSignedSat
    simp only [show Int.ofNat (1 <<< (32 - 1)) = 2147483648 from rfl, hgt, hlt, ↓reduceIte]
    rw [truncate32_intToSimdLane_32, ← hsq, BitVec.ofInt_toInt]

@[simp, arm64_norm, wp_norm]
theorem exec_simdAddv_4h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdAcrossLanes false false 0b01#2 0b11011#5 rn rd) s =
      (s.writeVReg128 rd ((simdAddv4h (s.readVReg128 rn)).zeroExtend 128)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.false_and, Bool.not_false, Bool.true_and,
    Bool.false_or, Bool.or_true, Bool.false_eq_true, decide_false, decide_true, ↓reduceIte,
    BitVec.reduceEq, Std.Legacy.Range.forIn_eq_forIn_range',
    show (8 <<< (0b01#2).toNat) = 16 from rfl,
    show (1#128 <<< 16 - 1#128 : BitVec 128) = 65535#128 from rfl]
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  change ((((0#128 + ((vn >>> 0) &&& 65535#128)) + ((vn >>> 16) &&& 65535#128)) +
      ((vn >>> 32) &&& 65535#128)) + ((vn >>> 48) &&& 65535#128)) &&& 65535#128 =
    ((lane16 vn 0 + lane16 vn 1) + (lane16 vn 2 + lane16 vn 3)).zeroExtend 128
  have hl0 : (vn >>> 0) &&& 65535#128 = (lane16 vn 0).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 0
  have hl1 : (vn >>> 16) &&& 65535#128 = (lane16 vn 1).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 1
  have hl2 : (vn >>> 32) &&& 65535#128 = (lane16 vn 2).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 2
  have hl3 : (vn >>> 48) &&& 65535#128 = (lane16 vn 3).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 3
  rw [hl0, hl1, hl2, hl3]
  set a0 := lane16 vn 0; set a1 := lane16 vn 1; set a2 := lane16 vn 2; set a3 := lane16 vn 3
  have hand (w : BitVec 128) : w &&& 65535#128 = (w.setWidth 16).zeroExtend 128 := by bv_bits
  rw [hand, BitVec.zero_add]
  congr 1
  rw [BitVec.setWidth_add _ _ (by decide), BitVec.setWidth_add _ _ (by decide),
    BitVec.setWidth_add _ _ (by decide)]
  have hsw (x : BitVec 16) : (x.zeroExtend 128).setWidth 16 = x := by bv_bits
  rw [hsw, hsw, hsw, hsw, BitVec.add_assoc]

/-! ## 3. Loop 1 (`seg5FinalPoly`) & Loop 2 (`neonCompressSerialize4`) Step Identities -/

/-- Final `v` polynomial computed in `B20` Loop 1 (matching `v` in `Spec.mlkem768Encaps2List`). -/
@[expose] def seg5FinalPoly (inv err2 msgPoly : Poly16) : Poly16 :=
  Array.ofFn (n := 256) fun ⟨i, _⟩ =>
    let normal := neonMontgomeryMul16 (inv.getD i 0#16) 1441#16
    let sum1 := err2.getD i 0#16 + msgPoly.getD i 0#16
    neonBarrettReduce16 (normal + sum1)

@[simp] theorem seg5FinalPoly_size (inv err2 msgPoly : Poly16) :
    (seg5FinalPoly inv err2 msgPoly).size = 256 := by simp [seg5FinalPoly]

theorem seg5Loop1_vec_eq (inv err2 msgPoly : Poly16) (idx : Nat) (hidx : idx < 32)
    (commSum : Bool) :
    let qx := polyVecNat inv idx
    let qe := polyVecNat err2 idx
    let qm := polyVecNat msgPoly idx
    let normal := simdSub8h
      (simdSshr8h (simdSqdmulh8h qx (dup8x16 1441#16)) 1)
      (simdSshr8h (simdSqdmulh8h (simdMul8h qx (dup8x16 55457#16)) (dup8x16 3329#16)) 1)
    let sum1 := simdAdd8h qe qm
    let tot := if commSum then simdAdd8h sum1 normal else simdAdd8h normal sum1
    let quot := simdSshr8h (simdAdd8h (simdSqdmulh8h tot (dup8x16 20159#16)) (dup8x16 1024#16)) 11
    simdMla8h tot quot (dup8x16 0xf2ff#16) =
      polyVecNat (seg5FinalPoly inv err2 msgPoly) idx := by
  dsimp only
  apply ext_lane16; intro i
  have hi256 : 8 * idx + i.val < 256 := by omega
  have hmont (x : BitVec 16) :
      (sqdmulh16 x 1441#16).sshiftRight 1 -
        (sqdmulh16 (x * 55457#16) 3329#16).sshiftRight 1 =
      neonMontgomeryMul16 x 1441#16 := by
    unfold neonMontgomeryMul16 neonMontgomeryReduce16; dsimp only
    rw [montgomery_precomp_mul x 1441#16]; rfl
  have hget : (seg5FinalPoly inv err2 msgPoly).getD (8 * idx + i.val) 0#16 =
      neonBarrettReduce16
        (neonMontgomeryMul16 (inv.getD (8 * idx + i.val) 0#16) 1441#16 +
          (err2.getD (8 * idx + i.val) 0#16 + msgPoly.getD (8 * idx + i.val) 0#16)) := by
    simp [seg5FinalPoly, Array.getD, hi256]
  set vInv := inv.getD (8 * idx + i.val) 0#16
  set vErr := err2.getD (8 * idx + i.val) 0#16
  set vMsg := msgPoly.getD (8 * idx + i.val) 0#16
  cases commSum
  · simp only [Bool.false_eq_true, ↓reduceIte, polyVecNat, lane16_pack8x16, lane16_simdMla8h,
      lane16_simdSshr8h, lane16_simdAdd8h, lane16_simdSqdmulh8h, lane16_simdSub8h,
      lane16_simdMul8h, lane16_dup8x16, hmont, hget]
    rw [barrett_mla_0xf2ff]; rfl
  · simp only [↓reduceIte, polyVecNat, lane16_pack8x16, lane16_simdMla8h,
      lane16_simdSshr8h, lane16_simdAdd8h, lane16_simdSqdmulh8h, lane16_simdSub8h,
      lane16_simdMul8h, lane16_dup8x16, hmont, hget]
    rw [barrett_mla_0xf2ff, BitVec.add_comm (vErr + vMsg) _]; rfl

/-- Raw Loop 2 compression expression (with `bic #15` mask `0xfffffff0#32` and `add v16, vn` order)
    equals `neonCompress8h 4 vn`. -/
theorem seg5Loop2_compress_eq (vn : BitVec 128) :
    let u := simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn
    let evenIn := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j <<< 4) &&& (pack4x32 fun _ => 1048560#32)) k +
        lane32 (pack4x32 fun _ => 1664#32) k
    let oddIn := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j >>> 12) &&& 0xfffffff0fffffff0fffffff0fffffff0#128) k +
        lane32 (pack4x32 fun _ => 1664#32) k
    let cMul := pack4x32 fun _ => 10321340#32
    let evenOut := pack4x32 fun k => lane32 (simdSqdmulh4s evenIn cMul) k >>> 4
    let oddOut := pack4x32 fun k => lane32 (simdSqdmulh4s oddIn cMul) k >>> 4
    (simdTrn1_8h evenOut oddOut &&& dup8x16 0x000f#16) = neonCompress8h 4 vn := by
  dsimp only
  unfold neonCompress8h
  have hu : simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn =
      simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16) := by
    apply ext_lane16; intro i; simp [BitVec.add_comm]
  rw [hu]
  set u := simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16)
  have lane32_and (a b : BitVec 128) (k : Fin 4) :
      lane32 (a &&& b) k = lane32 a k &&& lane32 b k := by
    apply BitVec.eq_of_getLsbD_eq; intro r hr
    simp [lane32, hr]
  have hev : (pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j <<< 4) &&& (pack4x32 fun _ => 1048560#32)) k +
        lane32 (pack4x32 fun _ => 1664#32) k) =
      (pack4x32 fun k => ((lane32 u k <<< 4) &&& (0x0000ffff#32 <<< 4)) + 1664#32) := by
    apply ext_lane32; intro k
    rw [lane32_pack4x32, lane32_pack4x32, lane32_and, lane32_pack4x32, lane32_pack4x32,
      lane32_pack4x32]
    rfl
  have hm_odd : ∀ b : Fin 32,
      ((0xfffffff0#32).getLsbD b.val = decide (4 ≤ b.val)) ∧
      ((0x0000ffff#32 <<< 4).getLsbD b.val = decide (4 ≤ b.val ∧ b.val < 20)) := by
    decide +kernel
  have hod : (pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j >>> 12) &&& 0xfffffff0fffffff0fffffff0fffffff0#128) k +
        lane32 (pack4x32 fun _ => 1664#32) k) =
      (pack4x32 fun k => ((lane32 u k >>> (16 - 4)) &&& (0x0000ffff#32 <<< 4)) + 1664#32) := by
    apply ext_lane32; intro k
    rw [lane32_pack4x32, lane32_pack4x32, lane32_and, lane32_pack4x32, lane32_pack4x32]
    have hc : lane32 0xfffffff0fffffff0fffffff0fffffff0#128 k = 0xfffffff0#32 := by
      induction k using fin4_cases <;> rfl
    rw [hc]; congr 1
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    have ⟨hm1, hm2⟩ := hm_odd ⟨b, hb⟩; dsimp only at hm1 hm2
    simp only [Nat.reduceSub, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, hm1, hm2]
    by_cases hb20 : b < 20
    · simp [hb20]
    · simp [hb20, BitVec.getLsbD_of_ge (lane32 u k) (12 + b) (by omega)]
  rw [hev, hod]; rfl

theorem seg5Loop2_lowt_eq (vn : BitVec 128) :
    simdUshl8h (neonCompress8h 4 vn) 0x000c000800040000000c000800040000#128 =
      neonSerialize4Lowt (neonCompress8h 4 vn) := by
  unfold neonSerialize4Lowt neonCompress8h
  dsimp only
  have hm : BitVec.ofNat 16 ((1 <<< 4) - 1) = 0x000f#16 := rfl
  rw [hm, BitVec.and_assoc, BitVec.and_self]

theorem seg5Loop2_addv4h_ext8_eq (u : BitVec 128) :
    simdAddv4h (u.truncate 64 ++ u.extractLsb' 64 64) = simdAddv4h (simdExt16b u u 8) := by
  have hlo (w : BitVec 128) (r : Nat) (hr : r < 4) :
      lane16 w ⟨r, by omega⟩ = (lane64 w 0).extractLsb' (16 * r) 16 := by
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [lane16, lane64, hb, show 16 * r + b < 64 by omega]
  have h64 : lane64 (u.truncate 64 ++ u.extractLsb' 64 64) 0 = lane64 (simdExt16b u u 8) 0 := by
    rw [lane64_simdExt16b_8_0]
    apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [lane64, hb]
  change (lane16 _ ⟨0, by decide⟩ + lane16 _ ⟨1, by decide⟩) +
      (lane16 _ ⟨2, by decide⟩ + lane16 _ ⟨3, by decide⟩) =
    (lane16 _ ⟨0, by decide⟩ + lane16 _ ⟨1, by decide⟩) +
      (lane16 _ ⟨2, by decide⟩ + lane16 _ ⟨3, by decide⟩)
  rw [hlo _ 0 (by decide), hlo _ 1 (by decide), hlo _ 2 (by decide), hlo _ 3 (by decide),
    hlo _ 0 (by decide), hlo _ 1 (by decide), hlo _ 2 (by decide), hlo _ 3 (by decide), h64]

theorem seg5Loop2_word64_assemble (s1_6 s0_6 s1_7 s0_7 : BitVec 16) :
    let w11_0 := ((s1_6.zeroExtend 128).truncate 32).zeroExtend 64
    let w12_0 := ((s0_6.zeroExtend 128).truncate 32).zeroExtend 64
    let w12_1 := ((s0_7.zeroExtend 128).truncate 32).zeroExtend 64
    let w12_2 := ((s1_7.zeroExtend 128).truncate 32).zeroExtend 64
    let w11_shl := ((evalBitfield .W32 .UBFM w11_0 w11_0 16 15).truncate 32).zeroExtend 64
    ((evalBitfield .W64 .BFM w11_shl w12_0 0 15) ||| (w12_1 <<< 32)) ||| (w12_2 <<< 48) =
      (s1_7 ++ s0_7) ++ (s1_6 ++ s0_6) := by
  dsimp only
  have hz32 (x : BitVec 16) : ((x.zeroExtend 128).truncate 32).zeroExtend 64 = x.zeroExtend 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hk]
  have hshl (x : BitVec 16) :
      ((evalBitfield .W32 .UBFM (x.zeroExtend 64) (x.zeroExtend 64) 16 15).truncate 32).zeroExtend 64 =
        (x.zeroExtend 64) <<< 16 := by
    have hbeq : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := rfl
    unfold evalBitfield; dsimp only [Nat.reduceMod, Nat.reduceSub]
    simp only [hbeq, Bool.true_and, decide_true,
      show 16 > 15 by decide, show 15 + 1 = 16 by decide]
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, hk, decide_true, Bool.true_and]
    by_cases hk16 : k < 16
    · simp [hk16]
    · by_cases hk32 : k < 32
      · simp [hk16, hk32, hk, show k - 16 < 64 by omega]
      · simp [hk16, hk32, BitVec.getLsbD_of_ge x (k - 16) (by omega)]
  rw [hz32, hz32, hz32, hz32, hshl, evalBitfield_bfxil_0_16]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
    BitVec.zeroExtend, BitVec.getLsbD_setWidth, hk, decide_true, Bool.true_and]
  by_cases hk32 : k < 32
  · simp [hk32, show k < 48 by omega]
  · by_cases hk48 : k < 48
    · simp [hk32, hk48, show ¬ (k < 16) by omega, BitVec.getLsbD_of_ge s1_6 (k - 16) (by omega),
        show k - 32 < 64 by omega, show k - 32 < 16 by omega]
    · simp [hk32, hk48, show ¬ (k < 16) by omega, BitVec.getLsbD_of_ge s1_6 (k - 16) (by omega),
        BitVec.getLsbD_of_ge s0_7 (k - 32) (by omega), show ¬ (k - 32 < 16) by omega,
        show k - 48 < 64 by omega, show k - 32 - 16 = k - 48 by omega]

theorem seg5_compressSerialize4_eq (re : Poly16) :
    ((List.range 16).map fun c =>
      neonSerialize4Bytes
        (neonCompress8h 4 (polyVecNat re (2 * c)))
        (neonCompress8h 4 (polyVecNat re (2 * c + 1)))).flatten =
      neonCompressSerialize4 re := by
  refine neonCompressSerialize4_eq_flatten re _ _ ?_ ?_
  · intro c _ j
    rw [lane16_neonCompress8h (by decide) (by decide), polyVecNat, lane16_pack8x16]
    have hidx : 8 * (2 * c) + j.val = 16 * c + j.val := by omega
    rw [hidx]; rfl
  · intro c _ j
    rw [lane16_neonCompress8h (by decide) (by decide), polyVecNat, lane16_pack8x16]
    have hidx : 8 * (2 * c + 1) + j.val = 16 * c + 8 + j.val := by omega
    rw [hidx]; rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd

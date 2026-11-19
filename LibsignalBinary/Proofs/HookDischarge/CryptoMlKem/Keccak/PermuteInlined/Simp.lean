/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib

/-!
# 2-Way NEON `keccak_f1600` Scoped Simplification Rules (`Keccak.PermuteInlined.Simp`)

Scoped `@[scoped simp, scoped arm64_norm, scoped wp_norm]` rewrite rules that normalize
2-way 128-bit NEON (`uint64x2_t`, represented as `hi64 ++ lo64`) operations into per-lane
64-bit `BitVec 64` operations matching `Spec.Keccak`:
1. `BitVec 128` (`a1 ++ a0`) lane extraction and bitwise operations (`EOR`, `AND`, `ORR`, `BIC`).
2. `ZIP1 .2D`, `ZIP2 .2D`, `ADD .2D`, `SHL .2D`, `DUP .2D`, `MOV` lane, and `LD1 {Vt.D}[1]`.
3. `SampleNTT` `SHAKE-128` domain-pad `BSL` and `FNEG .2D` rules (`B03`–`B07`).
4. `USRA .2D` evaluation and all 24 FIPS 202 `ρ`-rotation (`SHL + USRA` / `ADD + USRA` →
   `BitVec.rotateLeft`) collapses.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

open Arm64 (VReg State execInst execInstWithSvc getSimdLane
  evalSimdTwoRegMiscExt evalSimdTwoRegMiscExtSatFlags
  evalSimdImmShiftNonZeroExt evalSimdImmShiftNonZeroExtSatFlags
  setSimdLane simdLdSt1SingleLaneIdx mapSimdLanes zipSimdLanes
  simdLaneUInt aslRShr intToSimdLane)
open ProofLib (mapLanes zipLanes mapSimdLanes_true_64 zipSimdLanes_true_64 laneMask_64)

/-! ## 1. 2-Lane `BitVec 128` (`hi64 ++ lo64`) Extraction & Bitwise Rules -/

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem extractLsb_lo_append (a1 a0 : BitVec 64) :
    (a1 ++ a0).extractLsb' 0 64 = a0 := by
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem extractLsb_hi_append (a1 a0 : BitVec 64) :
    (a1 ++ a0).extractLsb' 64 64 = a1 := by
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem extractLsb_lo_zext128 (a0 : BitVec 64) :
    (a0.zeroExtend 128 : BitVec 128).extractLsb' 0 64 = a0 := by
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem extractLsb_hi_zext128 (a0 : BitVec 64) :
    (a0.zeroExtend 128 : BitVec 128).extractLsb' 64 64 = 0#64 := by
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem extractLsb_lo_zero128 :
    (0#128 : BitVec 128).extractLsb' 0 64 = 0#64 := by
  decide

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem extractLsb_hi_zero128 :
    (0#128 : BitVec 128).extractLsb' 64 64 = 0#64 := by
  decide

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem eor_append (a1 a0 b1 b0 : BitVec 64) :
    (a1 ++ a0) ^^^ (b1 ++ b0) = (a1 ^^^ b1) ++ (a0 ^^^ b0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append]
  split <;> rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem eor_zero_left_128 (v : BitVec 128) : (0#128 ^^^ v) = v :=
  BitVec.zero_xor

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem eor_zero_right_128 (v : BitVec 128) : (v ^^^ 0#128) = v :=
  BitVec.xor_zero

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem eor_zero_left_64 (v : BitVec 64) : (0#64 ^^^ v) = v :=
  BitVec.zero_xor

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem eor_zero_right_64 (v : BitVec 64) : (v ^^^ 0#64) = v :=
  BitVec.xor_zero

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem and_append (a1 a0 b1 b0 : BitVec 64) :
    (a1 ++ a0) &&& (b1 ++ b0) = (a1 &&& b1) ++ (a0 &&& b0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_append]
  split <;> rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem or_append (a1 a0 b1 b0 : BitVec 64) :
    (a1 ++ a0) ||| (b1 ++ b0) = (a1 ||| b1) ++ (a0 ||| b0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_append]
  split <;> rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem orr_self_128 (v : BitVec 128) : (v ||| v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_or, Bool.or_self]

/-- `BIC Vd.16B, Vn.16B, Vm.16B` (`vn &&& ~~~vm`) normalized directly to `(~~~b &&& a)` per lane
    to match `Spec.Keccak.keccakF1600Round`'s `(~~~b1) &&& b2`. -/
@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem bic_append (a1 a0 b1 b0 : BitVec 64) :
    (a1 ++ a0) &&& ~~~(b1 ++ b0) = (~~~b1 &&& a1) ++ (~~~b0 &&& a0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_append]
  by_cases h64 : i < 64
  · simp only [h64, ↓reduceIte, decide_eq_true hi, decide_true, Bool.true_and,
      Bool.and_comm]
  · have hi64 : i - 64 < 64 := by omega
    simp only [h64, ↓reduceIte, decide_eq_true hi, decide_eq_true hi64, Bool.true_and,
      Bool.and_comm]

/-! ## 2. `ZIP1 .2D`, `ZIP2 .2D`, `ADD .2D`, `SHL .2D`, `DUP .2D`, `MOV` Lane, `LD1` Single-Lane -/

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem zip1_2d_bind_forIn (x y : BitVec 128) :
    (Id.run (Bind.bind
      (forIn [:1] 0#128 fun i __s =>
        Pure.pure
          (ForInStep.yield
            (__s |||
              (x >>> (i * 64) &&& 18446744073709551615#128) <<< (2 * i * 64) |||
              (y >>> (i * 64) &&& 18446744073709551615#128) <<< ((2 * i + 1) * 64))))
      fun __s => Pure.pure __s)) = y.extractLsb' 0 64 ++ x.extractLsb' 0 64 := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : List.range' ([:1] : Std.Legacy.Range).start ([:1] : Std.Legacy.Range).size
      ([:1] : Std.Legacy.Range).step = [0] := rfl
  rw [hr]
  simp only [List.forIn_cons, List.forIn_nil, bind, pure, Id.run]
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem zip2_2d_bind_forIn (x y : BitVec 128) :
    (Id.run (Bind.bind
      (forIn [:1] 0#128 fun i __s =>
        Pure.pure
          (ForInStep.yield
            (__s |||
              (x >>> ((1 + i) * 64) &&& 18446744073709551615#128) <<< (2 * i * 64) |||
              (y >>> ((1 + i) * 64) &&& 18446744073709551615#128) <<< ((2 * i + 1) * 64))))
      fun __s => Pure.pure __s)) = y.extractLsb' 64 64 ++ x.extractLsb' 64 64 := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : List.range' ([:1] : Std.Legacy.Range).start ([:1] : Std.Legacy.Range).size
      ([:1] : Std.Legacy.Range).step = [0] := rfl
  rw [hr]
  simp only [List.forIn_cons, List.forIn_nil, bind, pure, Id.run]
  bv_bits

private theorem zip1_mask_eq (x y : BitVec 128) :
    (x &&& 18446744073709551615#128 ||| (y &&& 18446744073709551615#128) <<< 64) =
      BitVec.setWidth 64 y ++ BitVec.setWidth 64 x := by
  bv_bits

private theorem zip2_mask_eq (x y : BitVec 128) :
    (x >>> 64 &&& 18446744073709551615#128 |||
      (y >>> 64 &&& 18446744073709551615#128) <<< 64) =
      y.extractLsb' 64 64 ++ x.extractLsb' 64 64 := by
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem execInst_zip1_2d (rm rn rd : VReg) (s : State) :
    execInst (.simdPermute true 0b11#2 rm 0b011#3 rn rd) s =
      (s.writeVReg128 rd
        ((s.readVReg128 rm).extractLsb' 0 64 ++ (s.readVReg128 rn).extractLsb' 0 64)).advancePC := by
  simp [execInst, execInstWithSvc, getSimdLane, Std.Legacy.Range.forIn_eq_forIn_range', zip1_mask_eq]

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem execInst_zip2_2d (rm rn rd : VReg) (s : State) :
    execInst (.simdPermute true 0b11#2 rm 0b111#3 rn rd) s =
      (s.writeVReg128 rd
        ((s.readVReg128 rm).extractLsb' 64 64 ++ (s.readVReg128 rn).extractLsb' 64 64)).advancePC := by
  simp [execInst, execInstWithSvc, getSimdLane, Std.Legacy.Range.forIn_eq_forIn_range', zip2_mask_eq]

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem zip1_2d_forIn (x y : BitVec 128) :
    (Id.run do
      let __s ←
        forIn [:1] 0#128 fun i __s =>
          Pure.pure
            (ForInStep.yield
              (__s |||
                (x >>> (i * 64) &&& 18446744073709551615#128) <<< (2 * i * 64) |||
                (y >>> (i * 64) &&& 18446744073709551615#128) <<< ((2 * i + 1) * 64)))
      Pure.pure __s) = y.extractLsb' 0 64 ++ x.extractLsb' 0 64 := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : List.range' ([:1] : Std.Legacy.Range).start ([:1] : Std.Legacy.Range).size
      ([:1] : Std.Legacy.Range).step = [0] := rfl
  rw [hr]
  simp only [List.forIn_cons, List.forIn_nil, bind, pure, Id.run]
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem zip2_2d_forIn (x y : BitVec 128) :
    (Id.run do
      let __s ←
        forIn [:1] 0#128 fun i __s =>
          Pure.pure
            (ForInStep.yield
              (__s |||
                (x >>> ((1 + i) * 64) &&& 18446744073709551615#128) <<< (2 * i * 64) |||
                (y >>> ((1 + i) * 64) &&& 18446744073709551615#128) <<< ((2 * i + 1) * 64)))
      Pure.pure __s) = y.extractLsb' 64 64 ++ x.extractLsb' 64 64 := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : List.range' ([:1] : Std.Legacy.Range).start ([:1] : Std.Legacy.Range).size
      ([:1] : Std.Legacy.Range).step = [0] := rfl
  rw [hr]
  simp only [List.forIn_cons, List.forIn_nil, bind, pure, Id.run]
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem add_2d_lanes (x y : BitVec 128) :
    (0#128 |||
      ((x >>> 0 &&& 18446744073709551615#128) + (y >>> 0 &&& 18446744073709551615#128) &&&
        18446744073709551615#128) <<< 0 |||
      ((x >>> 64 &&& 18446744073709551615#128) + (y >>> 64 &&& 18446744073709551615#128) &&&
        18446744073709551615#128) <<< 64) =
      (x.extractLsb' 64 64 + y.extractLsb' 64 64) ++
        (x.extractLsb' 0 64 + y.extractLsb' 0 64) := by
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem shl_2d_lanes (x : BitVec 128) (k : Nat) :
    (0#128 |||
      ((x >>> 0 &&& 18446744073709551615#128) <<< k &&& 18446744073709551615#128) <<< 0 |||
      ((x >>> 64 &&& 18446744073709551615#128) <<< k &&& 18446744073709551615#128) <<< 64) =
      (x.extractLsb' 64 64 <<< k) ++ (x.extractLsb' 0 64 <<< k) := by
  have hm : (18446744073709551615#128 : BitVec 128) = (0#64 : BitVec 64) ++ ~~~0#64 := by decide
  rw [hm]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_zero, Nat.zero_add, Nat.sub_zero, Nat.not_lt_zero, decide_false, Bool.not_false,
    Bool.false_or]
  by_cases h64 : i < 64
  · have hsub : i - k < 64 := Nat.lt_of_le_of_lt (Nat.sub_le i k) h64
    have hsub128 : i - k < 128 := by omega
    simp only [h64, ↓reduceIte, decide_eq_true hi,
      decide_true, hsub, Bool.not_true, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.true_and, Bool.and_true]
  · have hi64 : i - 64 < 64 := by omega
    have hi128 : i - 64 < 128 := by omega
    have hsub : i - 64 - k < 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ k) hi64
    have hsub128 : i - 64 - k < 128 := by omega
    simp only [h64, ↓reduceIte, decide_eq_true hi,
      decide_eq_true hi128, decide_true, decide_false,
      hi64, hsub, Bool.not_false, Bool.and_false, Bool.false_or, Bool.true_and, Bool.and_true]

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem dup_2d_lane0 (x : BitVec 128) :
    (0#128 |||
      (x >>> 0 &&& 18446744073709551615#128 &&& 18446744073709551615#128) <<< 0 |||
      (x >>> 0 &&& 18446744073709551615#128 &&& 18446744073709551615#128) <<< 64) =
      x.extractLsb' 0 64 ++ x.extractLsb' 0 64 := by
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem dup_2d_lane1 (x : BitVec 128) :
    (0#128 |||
      (x >>> 64 &&& 18446744073709551615#128 &&& 18446744073709551615#128) <<< 0 |||
      (x >>> 64 &&& 18446744073709551615#128 &&& 18446744073709551615#128) <<< 64) =
      x.extractLsb' 64 64 ++ x.extractLsb' 64 64 := by
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem mov_d1_d0 (vd vn : BitVec 128) :
    ((vd &&& 18446744073709551615#128) |||
      ((vn >>> 0 &&& 18446744073709551615#128) <<< 64)) =
      vn.extractLsb' 0 64 ++ vd.extractLsb' 0 64 := by
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem mov_b0_zero (r : BitVec 64) :
    ((0#128 &&& 340282366920938463463374607431768211200#128) |||
      ((BitVec.zeroExtend 128 r &&& 255#128) <<< 0)) =
      (0#64 : BitVec 64) ++ (r.truncate 8).zeroExtend 64 := by
  bv_bits

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem ld1_single64_lane1 (vd : BitVec 128) (v : BitVec 64) :
    setSimdLane vd 64 (simdLdSt1SingleLaneIdx true 0x4#3 false 0x1#2) (v.zeroExtend 128) =
      v ++ vd.extractLsb' 0 64 := by
  have hidx : simdLdSt1SingleLaneIdx true 0x4#3 false 0x1#2 = 1 := by decide
  rw [hidx]
  unfold setSimdLane
  have hm : (((1#128 <<< 64) - 1#128) <<< (1 * 64) : BitVec 128) =
      (~~~0#64 : BitVec 64) ++ 0#64 := by decide
  rw [hm]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_zero,
    Nat.one_mul, Nat.zero_add]
  by_cases h64 : i < 64
  · simp only [h64, ↓reduceIte, decide_eq_true hi, decide_true, Bool.not_false,
      Bool.not_true, Bool.true_and, Bool.and_true, Bool.and_false, Bool.false_and, Bool.or_false]
  · have hi64 : i - 64 < 64 := by omega
    have hi128 : i - 64 < 128 := by omega
    simp only [h64, ↓reduceIte, decide_eq_true hi, decide_eq_true hi64,
      decide_eq_true hi128, decide_false, Bool.not_false, Bool.not_true,
      Bool.true_and, Bool.and_true, Bool.and_false, Bool.false_or]

/-! ## 3. `SampleNTT` `SHAKE-128` Domain-Pad `BSL` & `FNEG` Rules (`B03`–`B07`) -/

private theorem evalSimdTwoRegMiscExt_fneg2d (vd vn : BitVec 128) :
    evalSimdTwoRegMiscExt true true 3#2 15#5 vd vn =
      Except.ok (mapSimdLanes true 64 vn (fun a => a ^^^ (1#128 <<< 63))) := rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem fneg_2d_eval (vd vn : BitVec 128) :
    evalSimdTwoRegMiscExt true true 3#2 15#5 vd vn =
      Except.ok ((vn.extractLsb' 64 64 ^^^ 0x8000000000000000#64) ++
        (vn.extractLsb' 0 64 ^^^ 0x8000000000000000#64)) := by
  rw [evalSimdTwoRegMiscExt_fneg2d, mapSimdLanes_true_64]
  apply congrArg Except.ok
  simp only [mapLanes, laneMask_64]
  have hb : (1#128 <<< 63 : BitVec 128) = (0#64 : BitVec 64) ++ 0x8000000000000000#64 := by decide
  have hm : (0xffffffffffffffff#128 : BitVec 128) = (0#64 : BitVec 64) ++ ~~~0#64 := by decide
  rw [hb, hm]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_append, BitVec.getLsbD_zero, Nat.zero_mul, Nat.one_mul, Nat.zero_add,
    Nat.sub_zero, Nat.not_lt_zero, decide_false, Bool.not_false, Bool.false_or]
  by_cases h64 : i < 64
  · simp only [h64, ↓reduceIte, decide_eq_true hi, decide_true, Bool.not_true,
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.true_and, Bool.and_true]
  · have hi64 : i - 64 < 64 := by omega
    have hi128 : i - 64 < 128 := by omega
    simp only [h64, ↓reduceIte, decide_eq_true hi,
      decide_true, decide_false, hi64, Bool.not_false, Bool.and_false,
      Bool.false_or, Bool.true_and, Bool.and_true]

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem fneg_2d_satFlags (vd vn : BitVec 128) :
    evalSimdTwoRegMiscExtSatFlags true true 3#2 15#5 vd vn = none := by
  rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem movi_8h_31_eq :
    (160963658725094870944756432904323103#128 : BitVec 128) =
      0x001f001f001f001f#64 ++ 0x001f001f001f001f#64 := by
  decide

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem bsl_shake128_idx0 (b : BitVec 8) :
    ((b.zeroExtend 64 ^^^ 0x001f001f001f001f#64) &&& 0xffffffffff0000ff#64) ^^^
        0x001f001f001f001f#64 =
      0x00000000001f0000#64 ||| b.zeroExtend 64 := by
  revert b; decide

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem bsl_shake128_idx1 (b : BitVec 8) :
    ((b.zeroExtend 64 ^^^ 0x00000000001f0100#64) &&& 0xffffffffff0000ff#64) ^^^
        0x00000000001f0100#64 =
      0x00000000001f0100#64 ||| b.zeroExtend 64 := by
  revert b; decide

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem bsl_shake128_idx2 (b : BitVec 8) :
    ((b.zeroExtend 64 ^^^ 0x00000000001f0200#64) &&& 0xffffffffff0000ff#64) ^^^
        0x00000000001f0200#64 =
      0x00000000001f0200#64 ||| b.zeroExtend 64 := by
  revert b; decide

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem bsl_shake128_idx3 (b : BitVec 8) :
    ((b.zeroExtend 64 ^^^ 0x00000000001f0300#64) &&& 0xffffffffff0000ff#64) ^^^
        0x00000000001f0300#64 =
      0x00000000001f0300#64 ||| b.zeroExtend 64 := by
  revert b; decide

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem bsl_shake128_hi_mask :
    ((0#64 ^^^ 0x001f001f001f001f#64) &&& 0xffffffffffffffff#64) ^^^ 0x001f001f001f001f#64 =
      0#64 := by
  decide

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem bsl_shake128_hi_zero :
    (0#64 &&& 0xffffffffffffffff#64 : BitVec 64) = 0#64 := by
  decide

/-! ## 4. `USRA .2D` Evaluation & All 24 FIPS 202 `ρ`-Rotation Collapses -/

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_satFlags (immh : BitVec 4) (immb : BitVec 3) (vn : BitVec 128) :
    evalSimdImmShiftNonZeroExtSatFlags true true immh immb 2#5 vn = none := by
  unfold evalSimdImmShiftNonZeroExtSatFlags
  simp

private theorem and_mask64_eq_zext (w : BitVec 128) :
    w &&& 0xffffffffffffffff#128 = (w.extractLsb' 0 64).zeroExtend 128 := by
  bv_bits

private theorem extractLsb0_lane0 (w : BitVec 128) :
    (w >>> 0 &&& 0xffffffffffffffff#128).extractLsb' 0 64 = w.extractLsb' 0 64 := by
  bv_bits

private theorem extractLsb0_lane1 (w : BitVec 128) :
    (w >>> 64 &&& 0xffffffffffffffff#128).extractLsb' 0 64 = w.extractLsb' 64 64 := by
  bv_bits

private theorem usra64_lane_rhs (lane : BitVec 128) (r : Nat) (hr : (r == 0) = false) :
    intToSimdLane 64 (aslRShr (simdLaneUInt 64 lane) r false) =
      ((lane.extractLsb' 0 64) >>> r).zeroExtend 128 := by
  unfold simdLaneUInt aslRShr intToSimdLane
  rw [hr]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hm : ((1#128 <<< 64) - 1#128 : BitVec 128) = 0xffffffffffffffff#128 := by decide
  have h1 : (1 <<< r : Nat) = 2 ^ r := Nat.one_shiftLeft r
  have hdiv (m n : Nat) : (Int.ofNat m : Int) / Int.ofNat n = Int.ofNat (m / n) := rfl
  have hinner : (lane &&& 0xffffffffffffffff#128).toNat = (lane.extractLsb' 0 64).toNat := by
    rw [and_mask64_eq_zext, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (lane.extractLsb' 0 64).isLt (by decide))
  rw [hm, h1, hdiv, hinner, ← Nat.shiftRight_eq_div_pow, ← BitVec.toNat_ushiftRight]
  change (BitVec.ofNat 128 ((lane.extractLsb' 0 64 >>> r).toNat)) &&& 0xffffffffffffffff#128 = _
  rw [and_mask64_eq_zext]
  congr 1
  generalize lane.extractLsb' 0 64 >>> r = u
  have h0u : BitVec.ofNat 128 u.toNat = 0#64 ++ u := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_append, show (0#64).toNat = 0 from rfl,
      Nat.zero_shiftLeft, Nat.zero_or, Nat.mod_eq_of_lt (Nat.lt_trans u.isLt (by decide))]
  change (BitVec.ofNat 128 u.toNat).extractLsb' 0 64 = u
  rw [h0u, extractLsb_lo_append]

private theorem usra64_zip_eval (vd vn : BitVec 128) (r : Nat) (hr : (r == 0) = false) :
    zipSimdLanes true 64 vn vd
        (fun lane acc => acc + intToSimdLane 64 (aslRShr (simdLaneUInt 64 lane) r false)) =
      (vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> r)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> r)) := by
  rw [zipSimdLanes_true_64]
  simp only [zipLanes, laneMask_64, usra64_lane_rhs _ r hr, Nat.zero_mul, Nat.one_mul,
    extractLsb0_lane0, extractLsb0_lane1]
  generalize vn.extractLsb' 0 64 >>> r = u0
  generalize vn.extractLsb' 64 64 >>> r = u1
  bv_bits

private theorem shl_add_ushr_eq_rotateLeft (a : BitVec 64) (k r : Nat)
    (hk64 : k < 64) (hkr : r + k = 64) :
    (a <<< k) + (a >>> r) = a.rotateLeft k := by
  have hand : (a <<< k) &&& (a >>> r) = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_zero, decide_eq_true hi, Bool.true_and]
    by_cases hik : i < k
    · simp only [decide_eq_true hik, Bool.not_true, Bool.false_and]
    · have hge : 64 ≤ r + i := by omega
      simp only [BitVec.getLsbD_of_ge a (r + i) hge, Bool.and_false]
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hand]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_rotateLeft_of_le hk64]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, decide_eq_true hi,
    Bool.true_and]
  by_cases hik : i < k
  · simp only [hik, ↓reduceIte, decide_true, Bool.not_true, Bool.false_and,
      Bool.false_or]
    congr 1; omega
  · have hge : 64 ≤ r + i := by omega
    simp only [hik, ↓reduceIte, decide_false, Bool.not_false, Bool.true_and,
      BitVec.getLsbD_of_ge a (r + i) hge, Bool.or_false]

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r63 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 8#4 1#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 63)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 63))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 63 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_1_of_add_usra (a : BitVec 64) :
    a + a + (a >>> 63) = a.rotateLeft 1 := by
  have h2 : a + a = a <<< 1 := by bv_bits
  rw [h2]
  exact shl_add_ushr_eq_rotateLeft a 1 63 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r62 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 8#4 2#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 62)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 62))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 62 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_2 (a : BitVec 64) : (a <<< 2) + (a >>> 62) = a.rotateLeft 2 :=
  shl_add_ushr_eq_rotateLeft a 2 62 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r61 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 8#4 3#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 61)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 61))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 61 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_3 (a : BitVec 64) : (a <<< 3) + (a >>> 61) = a.rotateLeft 3 :=
  shl_add_ushr_eq_rotateLeft a 3 61 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r58 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 8#4 6#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 58)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 58))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 58 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_6 (a : BitVec 64) : (a <<< 6) + (a >>> 58) = a.rotateLeft 6 :=
  shl_add_ushr_eq_rotateLeft a 6 58 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r56 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 9#4 0#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 56)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 56))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 56 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_8 (a : BitVec 64) : (a <<< 8) + (a >>> 56) = a.rotateLeft 8 :=
  shl_add_ushr_eq_rotateLeft a 8 56 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r54 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 9#4 2#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 54)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 54))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 54 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_10 (a : BitVec 64) : (a <<< 10) + (a >>> 54) = a.rotateLeft 10 :=
  shl_add_ushr_eq_rotateLeft a 10 54 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r50 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 9#4 6#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 50)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 50))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 50 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_14 (a : BitVec 64) : (a <<< 14) + (a >>> 50) = a.rotateLeft 14 :=
  shl_add_ushr_eq_rotateLeft a 14 50 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r49 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 9#4 7#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 49)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 49))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 49 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_15 (a : BitVec 64) : (a <<< 15) + (a >>> 49) = a.rotateLeft 15 :=
  shl_add_ushr_eq_rotateLeft a 15 49 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r46 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 10#4 2#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 46)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 46))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 46 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_18 (a : BitVec 64) : (a <<< 18) + (a >>> 46) = a.rotateLeft 18 :=
  shl_add_ushr_eq_rotateLeft a 18 46 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r44 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 10#4 4#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 44)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 44))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 44 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_20 (a : BitVec 64) : (a <<< 20) + (a >>> 44) = a.rotateLeft 20 :=
  shl_add_ushr_eq_rotateLeft a 20 44 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r43 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 10#4 5#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 43)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 43))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 43 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_21 (a : BitVec 64) : (a <<< 21) + (a >>> 43) = a.rotateLeft 21 :=
  shl_add_ushr_eq_rotateLeft a 21 43 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r39 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 11#4 1#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 39)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 39))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 39 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_25 (a : BitVec 64) : (a <<< 25) + (a >>> 39) = a.rotateLeft 25 :=
  shl_add_ushr_eq_rotateLeft a 25 39 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r37 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 11#4 3#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 37)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 37))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 37 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_27 (a : BitVec 64) : (a <<< 27) + (a >>> 37) = a.rotateLeft 27 :=
  shl_add_ushr_eq_rotateLeft a 27 37 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r36 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 11#4 4#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 36)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 36))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 36 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_28 (a : BitVec 64) : (a <<< 28) + (a >>> 36) = a.rotateLeft 28 :=
  shl_add_ushr_eq_rotateLeft a 28 36 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r28 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 12#4 4#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 28)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 28))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 28 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_36 (a : BitVec 64) : (a <<< 36) + (a >>> 28) = a.rotateLeft 36 :=
  shl_add_ushr_eq_rotateLeft a 36 28 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r25 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 12#4 7#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 25)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 25))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 25 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_39 (a : BitVec 64) : (a <<< 39) + (a >>> 25) = a.rotateLeft 39 :=
  shl_add_ushr_eq_rotateLeft a 39 25 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r23 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 13#4 1#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 23)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 23))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 23 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_41 (a : BitVec 64) : (a <<< 41) + (a >>> 23) = a.rotateLeft 41 :=
  shl_add_ushr_eq_rotateLeft a 41 23 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r21 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 13#4 3#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 21)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 21))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 21 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_43 (a : BitVec 64) : (a <<< 43) + (a >>> 21) = a.rotateLeft 43 :=
  shl_add_ushr_eq_rotateLeft a 43 21 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r20 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 13#4 4#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 20)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 20))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 20 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_44 (a : BitVec 64) : (a <<< 44) + (a >>> 20) = a.rotateLeft 44 :=
  shl_add_ushr_eq_rotateLeft a 44 20 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r19 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 13#4 5#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 19)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 19))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 19 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_45 (a : BitVec 64) : (a <<< 45) + (a >>> 19) = a.rotateLeft 45 :=
  shl_add_ushr_eq_rotateLeft a 45 19 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r9 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 14#4 7#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 9)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 9))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 9 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_55 (a : BitVec 64) : (a <<< 55) + (a >>> 9) = a.rotateLeft 55 :=
  shl_add_ushr_eq_rotateLeft a 55 9 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r8 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 15#4 0#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 8)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 8))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 8 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_56 (a : BitVec 64) : (a <<< 56) + (a >>> 8) = a.rotateLeft 56 :=
  shl_add_ushr_eq_rotateLeft a 56 8 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r3 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 15#4 5#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 3)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 3))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 3 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_61 (a : BitVec 64) : (a <<< 61) + (a >>> 3) = a.rotateLeft 61 :=
  shl_add_ushr_eq_rotateLeft a 61 3 (by omega) rfl

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem usra_2d_r2 (vd vn : BitVec 128) :
    evalSimdImmShiftNonZeroExt true true 15#4 6#3 2#5 vd vn =
      Except.ok ((vd.extractLsb' 64 64 + (vn.extractLsb' 64 64 >>> 2)) ++
        (vd.extractLsb' 0 64 + (vn.extractLsb' 0 64 >>> 2))) :=
  congrArg Except.ok (usra64_zip_eval vd vn 2 rfl)

@[scoped simp, scoped arm64_norm, scoped wp_norm]
theorem rotl_62 (a : BitVec 64) : (a <<< 62) + (a >>> 2) = a.rotateLeft 62 :=
  shl_add_ushr_eq_rotateLeft a 62 2 (by omega) rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

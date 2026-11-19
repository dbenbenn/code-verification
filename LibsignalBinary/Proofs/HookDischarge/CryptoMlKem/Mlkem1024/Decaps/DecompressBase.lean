/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1

/-!
# `kyber_decapsulate` (`B06`) — Portable Deserialize + NEON Decompress Base (`DecompressBase`)

Shared AdvSIMD execution bridges and `Poly16` equivalence lemmas for
`PortableVector::deserialize_{5, 11}` followed by 16-lane NEON `decompress_{5, 11}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.DecompressBase

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement mlkemCall_of_blockOk mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 byteDecodeRaw decodeAndDecompress)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  ext_lane16 ext_lane32 getSimdLane_16_eq getSimdLane_32_eq
  lane16 lane16_pack8x16 lane32 lane32_pack4x32
  pack4x32 pack8x16 simdLaneUInt_16_zeroExtend simdLaneUInt_32_zeroExtend
  truncate32_intToSimdLane_32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_simdTrn1_8h simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (
  decodeAndDecompress_poly16_spec neonDecompressLane16 neonDecompressLane16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (
  byteDecodeRaw_lt_two_pow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  deserializeChunkBytes decodeAndDecompress_chunk_eq mlkemDeserialize11RWSpec
  mlkemDeserialize5RWSpec q0_lane_deserializeChunkBytes q1_lane_deserializeChunkBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize (
  blk26_deserialize5_RW_ok blk27_deserialize11_RW_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepLoad128 polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (blkPC06)

theorem blk26_deserialize5_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 26)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemDeserialize5RWSpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk26_deserialize5_RW_ok

theorem blk27_deserialize11_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 27)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemDeserialize11RWSpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk27_deserialize11_RW_ok

/-! ## 1. Pure `decompressPoly16` & 128-Bit `readLE` Load Helper -/

/-- `Poly16` encoding of `Spec.decodeAndDecompress d bs`. -/
@[expose] def decompressPoly16 (d : Nat) (bs : List (BitVec 8)) : Poly16 :=
  (decodeAndDecompress d bs).map fun c => BitVec.ofNat 16 c

@[simp] theorem decompressPoly16_size (d : Nat) (bs : List (BitVec 8)) :
    (decompressPoly16 d bs).size = 256 := by
  simp [decompressPoly16, decodeAndDecompress, byteDecodeRaw]

theorem decompressPoly16_spec {d : Nat} (bs : List (BitVec 8)) (hd : d = 5 ∨ d = 11) :
    PolyBounded16 3328 (decompressPoly16 d bs) ∧
    PolyRepresents (decompressPoly16 d bs) (decodeAndDecompress d bs) :=
  decodeAndDecompress_poly16_spec bs
    (by rcases hd with rfl | rfl <;> simp)
    (fun i hi => byteDecodeRaw_lt_two_pow d (by omega) bs i hi)

theorem SepLoad128.of_pointsToBytes_readLE {ea ptr : BitVec 64} {bs : List (BitVec 8)}
    {off : Nat} {P F : SepProp}
    (h : P = (ptr ↦ₛ bs) ∗ F) (hoff : off + 16 ≤ bs.length)
    (ha : ptr + BitVec.ofNat 64 off = ea) :
    SepLoad128 ea P (ByteSlice.readLE bs (off + 8) 8 ++ ByteSlice.readLE bs off 8) := by
  have hlo : (ByteSlice.readLE bs (off + 8) 8 ++ ByteSlice.readLE bs off 8).extractLsb' 0 64 =
      ByteSlice.readLE bs off 8 := by bv_bits
  have hhi : (ByteSlice.readLE bs (off + 8) 8 ++ ByteSlice.readLE bs off 8).extractLsb' 64 64 =
      ByteSlice.readLE bs (off + 8) 8 := by bv_bits
  refine ⟨?_, ?_⟩
  · rw [hlo]
    exact SepLoad64.of_pointsToBytes_readLE h (by omega) ha
  · rw [hhi]
    exact SepLoad64.of_pointsToBytes_readLE h (by omega)
      (by rw [← ha]; clear * -; bv_omega)

/-! ## 2. NEON `decompress_{5, 11}` Vector Operations & `{svc}` Execution Bridges -/

@[expose] def simdXtn4h (vn : BitVec 128) : BitVec 128 :=
  (lane16 vn ⟨6, by decide⟩ ++ lane16 vn ⟨4, by decide⟩ ++
    lane16 vn ⟨2, by decide⟩ ++ lane16 vn ⟨0, by decide⟩).zeroExtend 128

@[expose] def simdShrn16_4h (vn : BitVec 128) : BitVec 128 :=
  (lane16 vn ⟨7, by decide⟩ ++ lane16 vn ⟨5, by decide⟩ ++
    lane16 vn ⟨3, by decide⟩ ++ lane16 vn ⟨1, by decide⟩).zeroExtend 128

@[expose] def simdUmlal4sLow (acc vn vm : BitVec 128) : BitVec 128 :=
  pack4x32 fun i =>
    lane32 acc i +
      (lane16 vn ⟨i.val, by omega⟩).zeroExtend 32 * (lane16 vm ⟨i.val, by omega⟩).zeroExtend 32

@[expose] def simdUshr4s (vn : BitVec 128) (sh : Nat) : BitVec 128 :=
  pack4x32 fun i => lane32 vn i >>> sh

private theorem writeV_adv_congr {s : State} {rd : BitVec 5} {a b : BitVec 128} (h : a = b) :
    (s.writeVReg128 rd a).advancePC = (s.writeVReg128 rd b).advancePC :=
  h ▸ rfl

theorem exec_simdMovi_4s_1024 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b00100#5 4#5 rd) s =
      (s.writeVReg128 rd (pack4x32 fun _ => 1024#32)).advancePC := rfl

theorem exec_simdMovi_4s_16 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0#5 16#5 rd) s =
      (s.writeVReg128 rd (pack4x32 fun _ => 16#32)).advancePC := rfl

private theorem getLsbD_mask16_64 (b : Nat) : (0xffff#64).getLsbD b = decide (b < 16) := by
  change (0xffff#64).toNat.testBit b = decide (b < 16)
  rw [show (0xffff#64).toNat = 2 ^ 16 - 1 from rfl, Nat.testBit_two_pow_sub_one]

private theorem getLsbD_mask16_128 (b : Nat) : (0xffff#128).getLsbD b = decide (b < 16) := by
  change (0xffff#128).toNat.testBit b = decide (b < 16)
  rw [show (0xffff#128).toNat = 2 ^ 16 - 1 from rfl, Nat.testBit_two_pow_sub_one]

private theorem getLsbD_mask32_128_nat (b : Nat) : (0xffffffff#128).getLsbD b = decide (b < 32) := by
  change (0xffffffff#128).toNat.testBit b = decide (b < 32)
  rw [show (0xffffffff#128).toNat = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]

private theorem append4x16_getLsbD (a3 a2 a1 a0 : BitVec 16) (b : Nat) :
    (a3 ++ a2 ++ a1 ++ a0).getLsbD b =
      if b < 16 then a0.getLsbD b
      else if b < 32 then a1.getLsbD (b - 16)
      else if b < 48 then a2.getLsbD (b - 32)
      else a3.getLsbD (b - 48) := by
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases h16 : b < 16
  · simp [h16]
  · by_cases h32 : b < 32
    · simp [h16, h32, show b - 16 < 16 by omega]
    · by_cases h48 : b < 48
      · simp [h16, h32, h48, show ¬ (b - 16 < 16) by omega,
          show b - 16 - 16 = b - 32 by omega, show b - 32 < 16 by omega]
      · simp [h16, h32, h48, show ¬ (b - 16 < 16) by omega,
          show ¬ (b - 16 - 16 < 16) by omega,
          show b - 16 - 16 - 16 = b - 48 by omega]

private theorem append4x32_getLsbD (r3 r2 r1 r0 : BitVec 32) (b : Nat) :
    (r3 ++ r2 ++ r1 ++ r0).getLsbD b =
      if b < 32 then r0.getLsbD b
      else if b < 64 then r1.getLsbD (b - 32)
      else if b < 96 then r2.getLsbD (b - 64)
      else r3.getLsbD (b - 96) := by
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases h32 : b < 32
  · simp [h32]
  · by_cases h64 : b < 64
    · simp [h32, h64, show b - 32 < 32 by omega]
    · by_cases h96 : b < 96
      · simp [h32, h64, h96, show ¬ (b - 32 < 32) by omega,
          show b - 32 - 32 = b - 64 by omega, show b - 64 < 32 by omega]
      · simp [h32, h64, h96, show ¬ (b - 32 < 32) by omega,
          show ¬ (b - 32 - 32 < 32) by omega,
          show b - 32 - 32 - 32 = b - 96 by omega]

private theorem or_shift4x16_eq (a0 a1 a2 a3 : BitVec 16) :
    ((0#64 ||| a0.zeroExtend 64 <<< 0 ||| a1.zeroExtend 64 <<< 16 |||
      a2.zeroExtend 64 <<< 32 ||| a3.zeroExtend 64 <<< 48)).zeroExtend 128 =
      (a3 ++ a2 ++ a1 ++ a0).zeroExtend 128 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_zero, Bool.false_or, BitVec.getLsbD_shiftLeft]
  by_cases h64 : b < 64
  · simp only [h64, decide_true, Bool.true_and, append4x16_getLsbD]
    by_cases h16 : b < 16
    · simp [h64, h16, show b < 32 by omega, show b < 48 by omega]
    · by_cases h32 : b < 32
      · simp [h16, h32, show b < 48 by omega, show b - 16 < 64 by omega,
          BitVec.getLsbD_of_ge a0 b (by omega)]
      · by_cases h48 : b < 48
        · simp [h16, h32, h48, show b - 32 < 64 by omega,
            BitVec.getLsbD_of_ge a0 b (by omega), BitVec.getLsbD_of_ge a1 (b - 16) (by omega)]
        · simp [h16, h32, h48, show b - 48 < 64 by omega,
            BitVec.getLsbD_of_ge a0 b (by omega), BitVec.getLsbD_of_ge a1 (b - 16) (by omega),
            BitVec.getLsbD_of_ge a2 (b - 32) (by omega)]
  · simp only [h64, decide_false, Bool.false_and]
    exact (BitVec.getLsbD_of_ge (a3 ++ a2 ++ a1 ++ a0) b (by omega)).symm

private theorem xtn_narrow_lane (w : BitVec 32) :
    ((w.zeroExtend 128).truncate 64 &&& (1#64 <<< 16 - 1#64)) =
      (w.extractLsb' 0 16).zeroExtend 64 := by
  rw [show (1#64 <<< 16 - 1#64) = 0xffff#64 from rfl]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [BitVec.getLsbD_and, getLsbD_mask16_64]
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    hb, show b < 128 by omega, decide_true, Bool.true_and, BitVec.getLsbD_extractLsb']
  by_cases h16 : b < 16 <;> simp [h16]

private theorem extractLsb_32_lo16 (v : BitVec 128) (k : Nat) :
    (v.extractLsb' (32 * k) 32).extractLsb' 0 16 = v.extractLsb' (16 * (2 * k)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, show b < 32 by omega, decide_true, Bool.true_and,
    Nat.zero_add, show 32 * k = 16 * (2 * k) by omega]

private theorem extractLsb_32_hi16 (v : BitVec 128) (k : Nat) :
    (v.extractLsb' (32 * k) 32).extractLsb' 16 16 = v.extractLsb' (16 * (2 * k + 1)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, show 16 + b < 32 by omega, decide_true, Bool.true_and]
  congr 1; omega

theorem exec_simdXtn_4h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdTwoRegMisc false false 0b01#2 0b10010#5 rn rd) s =
      (s.writeVReg128 rd (simdXtn4h (s.readVReg128 rn))).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  have hr4 : List.range 4 = [0, 1, 2, 3] := rfl
  change (List.foldl (fun acc e =>
      acc ||| (((getSimdLane vn 32 e).truncate 64 &&& (1#64 <<< 16 - 1#64)) <<< (e * 16)))
    0#64 (List.range 4)).zeroExtend 128 = simdXtn4h vn
  rw [hr4]; dsimp only [List.foldl]
  rw [getSimdLane_32_eq vn ⟨0, by decide⟩, getSimdLane_32_eq vn ⟨1, by decide⟩,
      getSimdLane_32_eq vn ⟨2, by decide⟩, getSimdLane_32_eq vn ⟨3, by decide⟩,
      xtn_narrow_lane, xtn_narrow_lane, xtn_narrow_lane, xtn_narrow_lane]
  dsimp only [simdXtn4h, lane16, lane32]
  rw [extractLsb_32_lo16 vn 0, extractLsb_32_lo16 vn 1,
      extractLsb_32_lo16 vn 2, extractLsb_32_lo16 vn 3]
  simpa using or_shift4x16_eq
    (vn.extractLsb' 0 16) (vn.extractLsb' 32 16) (vn.extractLsb' 64 16) (vn.extractLsb' 96 16)

private theorem shrn16_narrow_lane (w : BitVec 32) :
    ((intToSimdLane 16 (aslRShr (simdLaneUInt 32 (w.zeroExtend 128)) 16 false)).truncate 64) &&&
      (1#64 <<< 16 - 1#64) = (w.extractLsb' 16 16).zeroExtend 64 := by
  rw [simdLaneUInt_32_zeroExtend]
  have hasl : aslRShr (w.toNat : Int) 16 false = Int.ofNat (w.toNat / 65536) :=
    (Int.natCast_ediv w.toNat 65536).symm
  have hint : intToSimdLane 16 (Int.ofNat (w.toNat / 65536)) =
      BitVec.ofNat 128 (w.toNat / 65536) &&& 0xffff#128 := rfl
  have hex : w.extractLsb' 16 16 = BitVec.ofNat 16 (w.toNat / 65536) := by
    have hsh : w.extractLsb' 16 16 = (w >>> 16).truncate 16 := by
      apply BitVec.eq_of_getLsbD_eq; intro b hb
      simp [BitVec.truncate_eq_setWidth, BitVec.getLsbD_ushiftRight, hb]
    rw [hsh]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow w.toNat 16]
  rw [hasl, hint, hex, show (1#64 <<< 16 - 1#64) = 0xffff#64 from rfl]
  generalize w.toNat / 65536 = q
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [BitVec.getLsbD_and, getLsbD_mask16_64]
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_and, getLsbD_mask16_128]
  by_cases h16 : b < 16
  · simp only [h16, decide_true, Bool.and_true]
    change (BitVec.ofNat 128 q).toNat.testBit b = (BitVec.ofNat 16 q).toNat.testBit b
    simp only [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, h16, show b < 128 by omega,
      decide_true, Bool.true_and]
  · simp [h16, BitVec.getLsbD_of_ge (BitVec.ofNat 16 q) b (by omega)]

theorem exec_simdShrn16_4h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift false false 0b0010#4 0#3 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdShrn16_4h (s.readVReg128 rn))).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  set vn := s.readVReg128 rn
  have hr4 : List.range 4 = [0, 1, 2, 3] := rfl
  change (List.foldl (fun acc e =>
      acc ||| ((((intToSimdLane 16 (aslRShr (simdLaneUInt 32 (getSimdLane vn 32 e)) 16 false)).truncate 64) &&&
        (1#64 <<< 16 - 1#64)) <<< (e * 16)))
    0#64 (List.range 4)).zeroExtend 128 = simdShrn16_4h vn
  rw [hr4]; dsimp only [List.foldl]
  rw [getSimdLane_32_eq vn ⟨0, by decide⟩, getSimdLane_32_eq vn ⟨1, by decide⟩,
      getSimdLane_32_eq vn ⟨2, by decide⟩, getSimdLane_32_eq vn ⟨3, by decide⟩,
      shrn16_narrow_lane, shrn16_narrow_lane, shrn16_narrow_lane, shrn16_narrow_lane]
  dsimp only [simdShrn16_4h, lane16, lane32]
  rw [extractLsb_32_hi16 vn 0, extractLsb_32_hi16 vn 1,
      extractLsb_32_hi16 vn 2, extractLsb_32_hi16 vn 3]
  simpa using or_shift4x16_eq
    (vn.extractLsb' 16 16) (vn.extractLsb' 48 16) (vn.extractLsb' 80 16) (vn.extractLsb' 112 16)

private theorem or_shift4x32_eq (r0 r1 r2 r3 : BitVec 32) :
    (0#128 ||| r0.zeroExtend 128 <<< 0 ||| r1.zeroExtend 128 <<< 32 |||
      r2.zeroExtend 128 <<< 64 ||| r3.zeroExtend 128 <<< 96) =
      r3 ++ r2 ++ r1 ++ r0 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero, Bool.false_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
    append4x32_getLsbD]
  by_cases h32 : b < 32
  · simp [hb, h32, show b < 64 by omega, show b < 96 by omega]
  · by_cases h64 : b < 64
    · simp [h32, h64, show b < 96 by omega, show b - 32 < 128 by omega,
        BitVec.getLsbD_of_ge r0 b (by omega)]
    · by_cases h96 : b < 96
      · simp [h32, h64, h96, show b - 64 < 128 by omega,
          BitVec.getLsbD_of_ge r0 b (by omega), BitVec.getLsbD_of_ge r1 (b - 32) (by omega)]
      · simp [h32, h64, h96, show b - 96 < 128 by omega,
          BitVec.getLsbD_of_ge r0 b (by omega), BitVec.getLsbD_of_ge r1 (b - 32) (by omega),
          BitVec.getLsbD_of_ge r2 (b - 64) (by omega)]

theorem exec_simdUmlal_4s_low {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeDiff false true 0b01#2 rm 0b1000#4 rn rd) s =
      (s.writeVReg128 rd
        (simdUmlal4sLow (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  set vd := s.readVReg128 rd
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  have hr4 : List.range 4 = [0, 1, 2, 3] := rfl
  change List.foldl (fun acc e =>
      acc ||| ((intToSimdLane 32
        (simdLaneUInt 32 (getSimdLane vd 32 e) +
          simdLaneUInt 16 (getSimdLane vn 16 e) * simdLaneUInt 16 (getSimdLane vm 16 e))) <<< (e * 32)))
    0#128 (List.range 4) = simdUmlal4sLow vd vn vm
  rw [hr4]; dsimp only [List.foldl]
  rw [getSimdLane_16_eq vn ⟨0, by decide⟩, getSimdLane_16_eq vm ⟨0, by decide⟩,
      getSimdLane_32_eq vd ⟨0, by decide⟩,
      getSimdLane_16_eq vn ⟨1, by decide⟩, getSimdLane_16_eq vm ⟨1, by decide⟩,
      getSimdLane_32_eq vd ⟨1, by decide⟩,
      getSimdLane_16_eq vn ⟨2, by decide⟩, getSimdLane_16_eq vm ⟨2, by decide⟩,
      getSimdLane_32_eq vd ⟨2, by decide⟩,
      getSimdLane_16_eq vn ⟨3, by decide⟩, getSimdLane_16_eq vm ⟨3, by decide⟩,
      getSimdLane_32_eq vd ⟨3, by decide⟩]
  simp only [simdLaneUInt_16_zeroExtend, simdLaneUInt_32_zeroExtend]
  have hzext32 (z : Int) : intToSimdLane 32 z = (BitVec.ofInt 32 z).zeroExtend 128 := by
    have hmask : ∀ x : BitVec 128,
        x &&& 0xffffffff#128 = ((x &&& 0xffffffff#128).truncate 32).zeroExtend 128 := by
      intro x; apply BitVec.eq_of_getLsbD_eq; intro b hb
      rw [BitVec.getLsbD_and, getLsbD_mask32_128_nat]
      simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and]
      rw [BitVec.getLsbD_and, getLsbD_mask32_128_nat]
      by_cases h32 : b < 32 <;> simp [h32]
    exact (hmask (BitVec.ofInt 128 z)).trans
      (congrArg (fun t => t.zeroExtend 128) (truncate32_intToSimdLane_32 z))
  have hstep (d32 : BitVec 32) (a16 b16 : BitVec 16) :
      intToSimdLane 32 ((d32.toNat : Int) + (a16.toNat : Int) * (b16.toNat : Int)) =
        (d32 + a16.zeroExtend 32 * b16.zeroExtend 32).zeroExtend 128 := by
    rw [hzext32]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have hd := d32.isLt; have ha := a16.isLt; have hb := b16.isLt
    have hsum_nonneg : 0 ≤ (d32.toNat : Int) + (a16.toNat : Int) * (b16.toNat : Int) := by positivity
    rw [BitVec.toNat_ofInt]
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (show a16.toNat < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show b16.toNat < 2 ^ 32 by omega)]
    omega
  rw [hstep, hstep, hstep, hstep]
  dsimp only [simdUmlal4sLow, pack4x32]
  simpa using or_shift4x32_eq
    (lane32 vd ⟨0, by decide⟩ +
      (lane16 vn ⟨0, by decide⟩).zeroExtend 32 * (lane16 vm ⟨0, by decide⟩).zeroExtend 32)
    (lane32 vd ⟨1, by decide⟩ +
      (lane16 vn ⟨1, by decide⟩).zeroExtend 32 * (lane16 vm ⟨1, by decide⟩).zeroExtend 32)
    (lane32 vd ⟨2, by decide⟩ +
      (lane16 vn ⟨2, by decide⟩).zeroExtend 32 * (lane16 vm ⟨2, by decide⟩).zeroExtend 32)
    (lane32 vd ⟨3, by decide⟩ +
      (lane16 vn ⟨3, by decide⟩).zeroExtend 32 * (lane16 vm ⟨3, by decide⟩).zeroExtend 32)

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

private theorem lane32_mapLanes_32_4 (v : BitVec 128) (f : BitVec 128 → BitVec 128) (i : Fin 4) :
    lane32 (mapLanes 32 v f 4) i = (f ((lane32 v i).zeroExtend 128)).truncate 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hpos : 32 * i.val + b < 128 := by omega
  simp only [lane32, BitVec.getLsbD_extractLsb', BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
    mapLanes_32_getLsbD v f 4 _ hpos, hpos,
    show (32 * i.val + b) / 32 = i.val by omega,
    show (32 * i.val + b) % 32 = b by omega, ↓reduceIte]

private theorem ushr_zext128_trunc32 (w : BitVec 32) (sh : Nat) :
    (w.zeroExtend 128 >>> sh).truncate 32 = w >>> sh := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]
  by_cases h128 : sh + b < 128
  · simp [h128]
  · simp [h128, BitVec.getLsbD_of_ge w (sh + b) (by omega)]

theorem exec_simdUshr_4s_11 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0110#4 0b101#3 0#5 rn rd) s =
      (s.writeVReg128 rd (simdUshr4s (s.readVReg128 rn) 11)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  apply ext_lane32; intro i
  rw [lane32_mapLanes_32_4, simdUshr4s, lane32_pack4x32]
  exact ushr_zext128_trunc32 (lane32 (s.readVReg128 rn) i) 11

theorem exec_simdUshr_4s_5 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0111#4 0b011#3 0#5 rn rd) s =
      (s.writeVReg128 rd (simdUshr4s (s.readVReg128 rn) 5)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  apply ext_lane32; intro i
  rw [lane32_mapLanes_32_4, simdUshr4s, lane32_pack4x32]
  exact ushr_zext128_trunc32 (lane32 (s.readVReg128 rn) i) 5

/-! ## 3. Exact 8-Lane Equivalence for `decompress_5` & `decompress_11` -/

@[expose] def neonDecompressRaw8h (d : Nat) (bias : BitVec 32) (q q3329 : BitVec 128) : BitVec 128 :=
  simdTrn1_8h
    (simdUshr4s (simdUmlal4sLow (pack4x32 fun _ => bias) (simdXtn4h q) q3329) d)
    (simdUshr4s (simdUmlal4sLow (pack4x32 fun _ => bias) (simdShrn16_4h q) q3329) d)

private theorem lane16_q3329_of_low64 {q3329 : BitVec 128}
    (hq : q3329.truncate 64 = 0x0d010d010d010d01#64) (j : Fin 4) :
    lane16 q3329 ⟨j.val, by omega⟩ = 3329#16 := by
  have hsub : lane16 q3329 ⟨j.val, by omega⟩ = (q3329.truncate 64).extractLsb' (16 * j.val) 16 := by
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp only [lane16, BitVec.getLsbD_extractLsb', BitVec.truncate_eq_setWidth,
      BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
      show 16 * j.val + b < 64 by omega]
  rw [hsub, hq]
  match j with
  | ⟨0, _⟩ => dsimp only; decide
  | ⟨1, _⟩ => dsimp only; decide
  | ⟨2, _⟩ => dsimp only; decide
  | ⟨3, _⟩ => dsimp only; decide
  | ⟨_ + 4, hj⟩ => omega

private theorem extractLsb_append4x16_zext (a3 a2 a1 a0 : BitVec 16) :
    let v := (a3 ++ a2 ++ a1 ++ a0).zeroExtend 128
    v.extractLsb' 0 16 = a0 ∧ v.extractLsb' 16 16 = a1 ∧
    v.extractLsb' 32 16 = a2 ∧ v.extractLsb' 48 16 = a3 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [append4x16_getLsbD, hb, show b < 128 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [append4x16_getLsbD,
      hb, show ¬ (16 + b < 16) by omega, show 16 + b < 32 by omega, show 16 + b < 128 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [append4x16_getLsbD,
      hb, show ¬ (32 + b < 16) by omega, show ¬ (32 + b < 32) by omega,
      show 32 + b < 48 by omega, show 32 + b < 128 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp [append4x16_getLsbD,
      hb, show ¬ (48 + b < 16) by omega, show ¬ (48 + b < 32) by omega,
      show ¬ (48 + b < 48) by omega, show 48 + b < 128 by omega]

private theorem lane16_simdXtn4h_low (q : BitVec 128) (j : Fin 4) :
    lane16 (simdXtn4h q) ⟨j.val, by omega⟩ = lane16 q ⟨2 * j.val, by omega⟩ := by
  have ⟨h0, h1, h2, h3⟩ := extractLsb_append4x16_zext
    (lane16 q ⟨6, by decide⟩) (lane16 q ⟨4, by decide⟩)
    (lane16 q ⟨2, by decide⟩) (lane16 q ⟨0, by decide⟩)
  match j with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact h3
  | ⟨_ + 4, hj⟩ => omega

private theorem lane16_simdShrn16_4h_low (q : BitVec 128) (j : Fin 4) :
    lane16 (simdShrn16_4h q) ⟨j.val, by omega⟩ = lane16 q ⟨2 * j.val + 1, by omega⟩ := by
  have ⟨h0, h1, h2, h3⟩ := extractLsb_append4x16_zext
    (lane16 q ⟨7, by decide⟩) (lane16 q ⟨5, by decide⟩)
    (lane16 q ⟨3, by decide⟩) (lane16 q ⟨1, by decide⟩)
  match j with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact h3
  | ⟨_ + 4, hj⟩ => omega

private theorem lane16_even_eq_lane32_trunc (v : BitVec 128) (j : Fin 4) :
    lane16 v ⟨2 * j.val, by omega⟩ = (lane32 v j).truncate 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [lane16, lane32, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', hb, show b < 32 by omega, decide_true, Bool.true_and,
    show 16 * (2 * j.val) = 32 * j.val by omega]

private theorem neonDecompressRaw8h_eq (d : Nat) (q q3329 : BitVec 128)
    (hq3329 : q3329.truncate 64 = 0x0d010d010d010d01#64) :
    neonDecompressRaw8h d (BitVec.ofNat 32 (1 <<< (d - 1))) q q3329 =
      pack8x16 fun i => neonDecompressLane16 d (lane16 q i) := by
  set bias := BitVec.ofNat 32 (1 <<< (d - 1))
  set vev := simdUshr4s (simdUmlal4sLow (pack4x32 fun _ => bias) (simdXtn4h q) q3329) d
  set vod := simdUshr4s (simdUmlal4sLow (pack4x32 fun _ => bias) (simdShrn16_4h q) q3329) d
  have hev (j : Fin 4) :
      lane16 vev ⟨2 * j.val, by omega⟩ = neonDecompressLane16 d (lane16 q ⟨2 * j.val, by omega⟩) := by
    rw [lane16_even_eq_lane32_trunc vev j]
    simp only [vev, simdUshr4s, simdUmlal4sLow, lane32_pack4x32,
      lane16_simdXtn4h_low q j, lane16_q3329_of_low64 hq3329 j, neonDecompressLane16]
    rw [BitVec.add_comm]; rfl
  have hod (j : Fin 4) :
      lane16 vod ⟨2 * j.val, by omega⟩ =
        neonDecompressLane16 d (lane16 q ⟨2 * j.val + 1, by omega⟩) := by
    rw [lane16_even_eq_lane32_trunc vod j]
    simp only [vod, simdUshr4s, simdUmlal4sLow, lane32_pack4x32,
      lane16_simdShrn16_4h_low q j, lane16_q3329_of_low64 hq3329 j, neonDecompressLane16]
    rw [BitVec.add_comm]; rfl
  apply ext_lane16; intro i
  rw [neonDecompressRaw8h, lane16_simdTrn1_8h, lane16_pack8x16]
  match i with
  | ⟨0, _⟩ => simpa using hev ⟨0, by decide⟩
  | ⟨1, _⟩ => simpa using hod ⟨0, by decide⟩
  | ⟨2, _⟩ => simpa using hev ⟨1, by decide⟩
  | ⟨3, _⟩ => simpa using hod ⟨1, by decide⟩
  | ⟨4, _⟩ => simpa using hev ⟨2, by decide⟩
  | ⟨5, _⟩ => simpa using hod ⟨2, by decide⟩
  | ⟨6, _⟩ => simpa using hev ⟨3, by decide⟩
  | ⟨7, _⟩ => simpa using hod ⟨3, by decide⟩
  | ⟨_ + 8, hi⟩ => omega

theorem neonDecompress_q0_eq {d : Nat} {fullBs : List (BitVec 8)} {k : Nat} {q3329 : BitVec 128}
    (hd : d = 5 ∨ d = 11) (hk : k < 16) (hlen : 2 * d * (k + 1) ≤ fullBs.length)
    (hq3329 : q3329.truncate 64 = 0x0d010d010d010d01#64) :
    let chunk := (fullBs.drop (2 * d * k)).take (2 * d)
    let buf := deserializeChunkBytes d chunk
    neonDecompressRaw8h d (BitVec.ofNat 32 (1 <<< (d - 1)))
      (ByteSlice.readLE buf 8 8 ++ ByteSlice.readLE buf 0 8) q3329 =
      polyVecNat (decompressPoly16 d fullBs) (2 * k) := by
  intro chunk buf
  rw [neonDecompressRaw8h_eq d _ q3329 hq3329]
  apply ext_lane16; intro i
  have hi : i.val < 8 := i.isLt
  have hlane : lane16 (ByteSlice.readLE buf 8 8 ++ ByteSlice.readLE buf 0 8) i =
      BitVec.ofNat 16 ((byteDecodeRaw d chunk).getD i.val 0) :=
    q0_lane_deserializeChunkBytes d chunk i.val hi
  have hraw_lt : (byteDecodeRaw d chunk).getD i.val 0 < 2 ^ d :=
    byteDecodeRaw_lt_two_pow d (by omega) chunk i.val (by omega)
  have hpow16 : 2 ^ d ≤ 65536 := by rcases hd with rfl | rfl <;> decide
  have htonat : (BitVec.ofNat 16 ((byteDecodeRaw d chunk).getD i.val 0)).toNat =
      (byteDecodeRaw d chunk).getD i.val 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hd4 : d = 4 ∨ d = 5 ∨ d = 10 ∨ d = 11 := by rcases hd with rfl | rfl <;> simp
  have hspec := (neonDecompressLane16_spec (d := d)
    (y := BitVec.ofNat 16 ((byteDecodeRaw d chunk).getD i.val 0))
    hd4 (by rw [htonat]; exact hraw_lt)).1
  rw [htonat, decodeAndDecompress_chunk_eq d fullBs k i.val hk (by omega) hlen] at hspec
  have hidx : 16 * k + i.val < (decodeAndDecompress d fullBs).size := by
    simp only [decodeAndDecompress, byteDecodeRaw, Array.size_map, Array.size_ofFn]; omega
  rw [lane16_pack8x16, hlane, hspec, polyVecNat, lane16_pack8x16]
  simp only [decompressPoly16]
  have hmul : 8 * (2 * k) + i.val = 16 * k + i.val := by omega
  rw [hmul, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_map, Array.getElem?_eq_getElem hidx]
  rfl

theorem neonDecompress_q1_eq {d : Nat} {fullBs : List (BitVec 8)} {k : Nat} {q3329 : BitVec 128}
    (hd : d = 5 ∨ d = 11) (hk : k < 16) (hlen : 2 * d * (k + 1) ≤ fullBs.length)
    (hq3329 : q3329.truncate 64 = 0x0d010d010d010d01#64) :
    let chunk := (fullBs.drop (2 * d * k)).take (2 * d)
    let buf := deserializeChunkBytes d chunk
    neonDecompressRaw8h d (BitVec.ofNat 32 (1 <<< (d - 1)))
      (ByteSlice.readLE buf 24 8 ++ ByteSlice.readLE buf 16 8) q3329 =
      polyVecNat (decompressPoly16 d fullBs) (2 * k + 1) := by
  intro chunk buf
  rw [neonDecompressRaw8h_eq d _ q3329 hq3329]
  apply ext_lane16; intro i
  have hi : i.val < 8 := i.isLt
  have hlane : lane16 (ByteSlice.readLE buf 24 8 ++ ByteSlice.readLE buf 16 8) i =
      BitVec.ofNat 16 ((byteDecodeRaw d chunk).getD (8 + i.val) 0) :=
    q1_lane_deserializeChunkBytes d chunk i.val hi
  have hraw_lt : (byteDecodeRaw d chunk).getD (8 + i.val) 0 < 2 ^ d :=
    byteDecodeRaw_lt_two_pow d (by omega) chunk (8 + i.val) (by omega)
  have hpow16 : 2 ^ d ≤ 65536 := by rcases hd with rfl | rfl <;> decide
  have htonat : (BitVec.ofNat 16 ((byteDecodeRaw d chunk).getD (8 + i.val) 0)).toNat =
      (byteDecodeRaw d chunk).getD (8 + i.val) 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hd4 : d = 4 ∨ d = 5 ∨ d = 10 ∨ d = 11 := by rcases hd with rfl | rfl <;> simp
  have hspec := (neonDecompressLane16_spec (d := d)
    (y := BitVec.ofNat 16 ((byteDecodeRaw d chunk).getD (8 + i.val) 0))
    hd4 (by rw [htonat]; exact hraw_lt)).1
  rw [htonat, decodeAndDecompress_chunk_eq d fullBs k (8 + i.val) hk (by omega) hlen] at hspec
  have hidx : 16 * k + (8 + i.val) < (decodeAndDecompress d fullBs).size := by
    simp only [decodeAndDecompress, byteDecodeRaw, Array.size_map, Array.size_ofFn]; omega
  rw [lane16_pack8x16, hlane, hspec, polyVecNat, lane16_pack8x16]
  simp only [decompressPoly16]
  have hmul : 8 * (2 * k + 1) + i.val = 16 * k + (8 + i.val) := by omega
  rw [hmul, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_map, Array.getElem?_eq_getElem hidx]
  rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.DecompressBase

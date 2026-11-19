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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common

/-!
# `kyber_encapsulate` (`B07`) — Segment 4 `compress_11` / `serialize_11` Bridges

NEON instruction step lemmas (`movi`, `bic`, `shl`, `ushr`, `umov`) and bit-packing identities
relating `compress_11` and `serialize_11` to `compressAndEncode 11`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Simd

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 bitsToBytes compressAndEncode compressCoeff)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 ext_lane16 ext_lane32 fin4_cases getSimdLane_16_eq getSimdLane_32_eq
  lane16 lane16_dup8x16 lane16_pack8x16 lane32 lane32_pack4x32 pack4x32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_and lane16_simdAdd8h simdAdd8h simdCmltZero8h simdSqdmulh4s simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (
  even_shl_extract32 lane16_neonCompress8h neonCompress11_orr_eq_add
  neonCompress8h neonCompressLane16_of_mod odd_ushr_extract32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (
  byteEncodeChunk byteEncodeChunkVec compressAndEncode_eq_flatten_chunks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid (
  neonSerialize11Bytes neonSerialize11Bytes_eq neonSerialize11Half)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (polyVecNat)

private theorem writeV_adv_congr {s : State} {rd : BitVec 5} {a b : BitVec 128} (h : a = b) :
    (s.writeVReg128 rd a).advancePC = (s.writeVReg128 rd b).advancePC :=
  h ▸ rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC :=
  rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdBic_4s_f8_24 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0b111#3 0b01110#5 0b11000#5 rd) s =
      (s.writeVReg128 rd (s.readVReg128 rd &&& 0x07ffffff07ffffff07ffffff07ffffff#128)).advancePC :=
  rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdBic_8h_f8_8 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0b111#3 0b10110#5 0b11000#5 rd) s =
      (s.writeVReg128 rd (s.readVReg128 rd &&& dup8x16 0x07ff#16)).advancePC :=
  rfl

private theorem getLsbD_mask32_128 (k : Nat) :
    (4294967295#128).getLsbD k = decide (k < 32) := by
  change (4294967295#128).toNat.testBit k = decide (k < 32)
  rw [show (4294967295#128).toNat = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]

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
      Bool.true_and, BitVec.getLsbD_and, hm32]
    by_cases hbn : b < 32 * n
    · simp [hbn, show b < n * 32 by omega, show b < 32 * (n + 1) by omega]
    · by_cases hbn1 : b < 32 * (n + 1)
      · have hin : (v >>> (n * 32) &&& 4294967295#128) =
            (v.extractLsb' (32 * n) 32).zeroExtend 128 := by
          simpa [getSimdLane, lane32] using getSimdLane_32_eq v ⟨n, by omega⟩
        have hm' : (4294967295#128).getLsbD (b % 32) = true := by
          rw [getLsbD_mask32_128]; simp [show b % 32 < 32 by omega]
        simp [hbn, hbn1, show ¬ (b < n * 32) by omega, show b / 32 = n by omega,
          show b - n * 32 = b % 32 by omega, hm', hin]
      · simp [hbn, hbn1, show ¬ (b < n * 32) by omega, getLsbD_mask32_128,
          show ¬ (b - n * 32 < 32) by omega]

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
theorem exec_simdShl_4s_11 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0101#4 0b011#3 0b01010#5 rn rd) s =
      (s.writeVReg128 rd (pack4x32 fun k => lane32 (s.readVReg128 rn) k <<< 11)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_false, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane <<< 11) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, lane32_pack4x32]; bv_bits

@[simp, arm64_norm, wp_norm]
theorem exec_simdUshr_4s_5 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0111#4 0b011#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (pack4x32 fun k => lane32 (s.readVReg128 rn) k >>> 5)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane >>> 5) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, lane32_pack4x32]; bv_bits

private theorem writeR64_adv_congr {s : State} {r : Reg} {a b : BitVec 64} (h : a = b) :
    (s.writeReg64 r a).advancePC = (s.writeReg64 r b).advancePC :=
  h ▸ rfl

private theorem umov8_lane1_eq (v : BitVec 128) :
    (((getSimdLane v 8 1).truncate 64).truncate 32).zeroExtend 64 =
      ((lane16 v 0 >>> 8).truncate 8).zeroExtend 64 := by
  dsimp only [getSimdLane, lane16, Fin.val_zero]; bv_bits

private theorem umov16_lane_eq (v : BitVec 128) (k : Fin 8) :
    (((getSimdLane v 16 k.val).truncate 64).truncate 32).zeroExtend 64 =
      (lane16 v k).zeroExtend 64 := by
  rw [getSimdLane_16_eq v k]; bv_bits

@[simp, arm64_norm, wp_norm]
theorem exec_umov_b1 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 3#5 0b0111#4 rn rd) s =
      (s.writeReg64 (Reg.fromZRBits rd)
        (((lane16 (s.readVReg128 rn) 0 >>> 8).truncate 8).zeroExtend 64)).advancePC := by
  simp only [execInstWithSvc, State.writeReg]
  exact writeR64_adv_congr (umov8_lane1_eq (s.readVReg128 rn))

@[simp, arm64_norm, wp_norm]
theorem exec_umov_h0 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 2#5 0b0111#4 rn rd) s =
      (s.writeReg64 (Reg.fromZRBits rd) ((lane16 (s.readVReg128 rn) 0).zeroExtend 64)).advancePC := by
  simp only [execInstWithSvc, State.writeReg]
  exact writeR64_adv_congr (umov16_lane_eq (s.readVReg128 rn) 0)

@[simp, arm64_norm, wp_norm]
theorem exec_umov_h1 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 6#5 0b0111#4 rn rd) s =
      (s.writeReg64 (Reg.fromZRBits rd) ((lane16 (s.readVReg128 rn) 1).zeroExtend 64)).advancePC := by
  simp only [execInstWithSvc, State.writeReg]
  exact writeR64_adv_congr (umov16_lane_eq (s.readVReg128 rn) 1)

@[simp, arm64_norm, wp_norm]
theorem exec_umov_h2 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 10#5 0b0111#4 rn rd) s =
      (s.writeReg64 (Reg.fromZRBits rd) ((lane16 (s.readVReg128 rn) 2).zeroExtend 64)).advancePC := by
  simp only [execInstWithSvc, State.writeReg]
  exact writeR64_adv_congr (umov16_lane_eq (s.readVReg128 rn) 2)

@[simp, arm64_norm, wp_norm]
theorem exec_umov_h3 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 14#5 0b0111#4 rn rd) s =
      (s.writeReg64 (Reg.fromZRBits rd) ((lane16 (s.readVReg128 rn) 3).zeroExtend 64)).advancePC := by
  simp only [execInstWithSvc, State.writeReg]
  exact writeR64_adv_congr (umov16_lane_eq (s.readVReg128 rn) 3)

@[simp, arm64_norm, wp_norm]
theorem exec_umov_h4 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 18#5 0b0111#4 rn rd) s =
      (s.writeReg64 (Reg.fromZRBits rd) ((lane16 (s.readVReg128 rn) 4).zeroExtend 64)).advancePC := by
  simp only [execInstWithSvc, State.writeReg]
  exact writeR64_adv_congr (umov16_lane_eq (s.readVReg128 rn) 4)

@[simp, arm64_norm, wp_norm]
theorem exec_umov_h5 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 22#5 0b0111#4 rn rd) s =
      (s.writeReg64 (Reg.fromZRBits rd) ((lane16 (s.readVReg128 rn) 5).zeroExtend 64)).advancePC := by
  simp only [execInstWithSvc, State.writeReg]
  exact writeR64_adv_congr (umov16_lane_eq (s.readVReg128 rn) 5)

@[simp, arm64_norm, wp_norm]
theorem exec_umov_h6 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 26#5 0b0111#4 rn rd) s =
      (s.writeReg64 (Reg.fromZRBits rd) ((lane16 (s.readVReg128 rn) 6).zeroExtend 64)).advancePC := by
  simp only [execInstWithSvc, State.writeReg]
  exact writeR64_adv_congr (umov16_lane_eq (s.readVReg128 rn) 6)

@[simp, arm64_norm, wp_norm]
theorem exec_umov_h7 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 30#5 0b0111#4 rn rd) s =
      (s.writeReg64 (Reg.fromZRBits rd) ((lane16 (s.readVReg128 rn) 7).zeroExtend 64)).advancePC := by
  simp only [execInstWithSvc, State.writeReg]
  exact writeR64_adv_congr (umov16_lane_eq (s.readVReg128 rn) 7)

theorem seg4_compress11_eq (vn : BitVec 128) :
    let u := simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn
    let evenIn := ((pack4x32 fun j => lane32 u j <<< 11) &&&
      0x07ffffff07ffffff07ffffff07ffffff#128) ||| (pack4x32 fun _ => 1664#32)
    let oddIn := ((pack4x32 fun j => lane32 u j >>> 5) &&&
      (pack4x32 fun _ => 134215680#32)) ||| (pack4x32 fun _ => 1664#32)
    let cMul := pack4x32 fun _ => 10321340#32
    let evenOut := pack4x32 fun k => lane32 (simdSqdmulh4s evenIn cMul) k >>> 4
    let oddOut := pack4x32 fun k => lane32 (simdSqdmulh4s oddIn cMul) k >>> 4
    (simdTrn1_8h evenOut oddOut &&& dup8x16 0x07ff#16) = neonCompress8h 11 vn := by
  dsimp only; unfold neonCompress8h
  have hu : simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn =
      simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16) := by
    apply ext_lane16; intro i; rw [lane16_simdAdd8h, lane16_simdAdd8h, BitVec.add_comm]
  rw [hu]; set u := simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16)
  have l32_and (a b : BitVec 128) (k : Fin 4) : lane32 (a &&& b) k = lane32 a k &&& lane32 b k := by
    apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [lane32, hr]
  have l32_or (a b : BitVec 128) (k : Fin 4) : lane32 (a ||| b) k = lane32 a k ||| lane32 b k := by
    apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [lane32, hr]
  have hm_ev (w : BitVec 32) : (w <<< 11) &&& 0x07ffffff#32 = (w <<< 11) &&& (0x0000ffff#32 <<< 11) := by
    bv_bits
  have hev : (((pack4x32 fun j => lane32 u j <<< 11) &&&
      0x07ffffff07ffffff07ffffff07ffffff#128) ||| (pack4x32 fun _ => 1664#32)) =
      (pack4x32 fun k => ((lane32 u k <<< 11) &&& (0x0000ffff#32 <<< 11)) + 1664#32) := by
    apply ext_lane32; intro k
    rw [l32_or, l32_and, lane32_pack4x32, lane32_pack4x32, lane32_pack4x32]
    have hc : lane32 0x07ffffff07ffffff07ffffff07ffffff#128 k = 0x07ffffff#32 := by
      induction k using fin4_cases <;> rfl
    rw [hc, hm_ev, even_shl_extract32 (lane32 u k) 11 (by decide), neonCompress11_orr_eq_add]
  have hod : (((pack4x32 fun j => lane32 u j >>> 5) &&&
      (pack4x32 fun _ => 134215680#32)) ||| (pack4x32 fun _ => 1664#32)) =
      (pack4x32 fun k => ((lane32 u k >>> (16 - 11)) &&& (0x0000ffff#32 <<< 11)) + 1664#32) := by
    apply ext_lane32; intro k
    rw [l32_or, l32_and, lane32_pack4x32, lane32_pack4x32, lane32_pack4x32, lane32_pack4x32]
    change (((lane32 u k >>> (16 - 11)) &&& (0x0000ffff#32 <<< 11)) ||| 1664#32) = _
    rw [odd_ushr_extract32 (lane32 u k) 11 (by decide) (by decide), neonCompress11_orr_eq_add]
  rw [hev, hod]; rfl

theorem lane16_neonCompress8h_11_mask (vn : BitVec 128) (j : Fin 8) :
    lane16 (neonCompress8h 11 vn) j &&& 0x07ff#16 = lane16 (neonCompress8h 11 vn) j := by
  unfold neonCompress8h; dsimp only
  rw [lane16_and, lane16_dup8x16,
    show BitVec.ofNat 16 ((1 <<< 11) - 1) = 0x07ff#16 from rfl,
    BitVec.and_assoc, BitVec.and_self]

theorem ser11_b0 (v : BitVec 128) (h0 : lane16 v 0 &&& 0x07ff#16 = lane16 v 0) :
    v.truncate 8 = (lane16 v 0 &&& 0x07ff#16).truncate 8 := by
  rw [h0]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [lane16, BitVec.truncate_eq_setWidth, hi, show i < 16 by omega]

theorem ser11_b1 (c0 c1 : BitVec 16) (h0 : c0 &&& 0x07ff#16 = c0) (h1 : c1 &&& 0x07ff#16 = c1) :
    ((((c0 >>> 8).truncate 8).zeroExtend 32 ||| (c1.zeroExtend 32 <<< 3))).truncate 8 =
      (((c0 &&& 0x07ff#16) >>> 8) ||| ((c1 &&& 0x07ff#16) <<< 3)).truncate 8 := by
  rw [h0, h1]; bv_bits

theorem ser11_shl_lsr (ca cb : BitVec 16) (shL shR : Nat)
    (ha : ca &&& 0x07ff#16 = ca) (hb : cb &&& 0x07ff#16 = cb)
    (hs : shL + shR = 11) (hL : 1 ≤ shL) (hL7 : shL ≤ 7) :
    (((cb.zeroExtend 32 <<< shL) ||| (ca.zeroExtend 32 >>> shR))).truncate 8 =
      (((ca &&& 0x07ff#16) >>> shR) ||| ((cb &&& 0x07ff#16) <<< shL)).truncate 8 := by
  rw [ha, hb]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    hi, show i < 32 by omega, show i < 16 by omega, decide_true, Bool.true_and]
  by_cases hli : i < shL
  · simp [hli, show shR + i < 16 by omega, show shR + i < 32 by omega]
  · by_cases h16 : shR + i < 16
    · simp [hli, h16, show shR + i < 32 by omega, show i - shL < 16 by omega,
        show i - shL < 32 by omega, Bool.or_comm]
    · simp [hli, show shR + i < 32 by omega, show i - shL < 16 by omega,
        show i - shL < 32 by omega, BitVec.getLsbD_of_ge ca (shR + i) (by omega)]

theorem ser11_lsr (ca : BitVec 16) (shR : Nat) (ha : ca &&& 0x07ff#16 = ca)
    (hR : shR = 1 ∨ shR = 2 ∨ shR = 3) :
    (ca.zeroExtend 32 >>> shR).truncate 8 = ((ca &&& 0x07ff#16) >>> shR).truncate 8 := by
  rw [ha]; rcases hR with rfl | rfl | rfl <;> bv_bits

theorem cells11_eq_neonSerialize11Half (a : BitVec 64) (v : BitVec 128) :
    let c : Fin 8 → BitVec 16 := fun j => lane16 v j &&& 0x07ff#16
    (a ↦₈ (c 0).truncate 8) ∗ ((a + 1#64) ↦₈ ((c 0 >>> 8) ||| (c 1 <<< 3)).truncate 8) ∗
    ((a + 2#64) ↦₈ ((c 1 >>> 5) ||| (c 2 <<< 6)).truncate 8) ∗ ((a + 3#64) ↦₈ (c 2 >>> 2).truncate 8) ∗
    ((a + 4#64) ↦₈ ((c 2 >>> 10) ||| (c 3 <<< 1)).truncate 8) ∗
    ((a + 5#64) ↦₈ ((c 3 >>> 7) ||| (c 4 <<< 4)).truncate 8) ∗
    ((a + 6#64) ↦₈ ((c 4 >>> 4) ||| (c 5 <<< 7)).truncate 8) ∗ ((a + 7#64) ↦₈ (c 5 >>> 1).truncate 8) ∗
    ((a + 8#64) ↦₈ ((c 5 >>> 9) ||| (c 6 <<< 2)).truncate 8) ∗
    ((a + 9#64) ↦₈ ((c 6 >>> 6) ||| (c 7 <<< 5)).truncate 8) ∗ ((a + 10#64) ↦₈ (c 7 >>> 3).truncate 8) =
    (a ↦ₛ neonSerialize11Half v) := by
  dsimp only [neonSerialize11Half]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem cells22_eq_neonSerialize11Bytes (a : BitVec 64) (v0 v1 : BitVec 128) :
    (a ↦ₛ neonSerialize11Half v0) ∗ ((a + 11#64) ↦ₛ neonSerialize11Half v1) =
    (a ↦ₛ neonSerialize11Bytes v0 v1) := by
  rw [neonSerialize11Bytes, pointsToBytes_append,
    show (neonSerialize11Half v0).length = 11 by rfl]

@[expose] def neonCompressSerialize11Poly (re : Poly16) : List (BitVec 8) :=
  ((List.range 16).map fun c =>
    neonSerialize11Bytes (neonCompress8h 11 (polyVecNat re (2 * c)))
      (neonCompress8h 11 (polyVecNat re (2 * c + 1)))).flatten

private theorem neonSerialize11Bytes_length (v0 v1 : BitVec 128) :
    (neonSerialize11Bytes v0 v1).length = 22 := rfl

@[simp] theorem neonCompressSerialize11Poly_length (re : Poly16) :
    (neonCompressSerialize11Poly re).length = 352 := by
  have hr : List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
  unfold neonCompressSerialize11Poly; rw [hr]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.length_append, List.length_nil, neonSerialize11Bytes_length]

theorem neonCompressSerialize11Poly_eq {re : Poly16} {f : Poly}
    (hb : PolyBounded16 1664 re) (hr : PolyRepresents re f) :
    neonCompressSerialize11Poly re = compressAndEncode 11 f := by
  unfold neonCompressSerialize11Poly
  rw [compressAndEncode_eq_flatten_chunks 11 (by decide) f]
  apply congrArg List.flatten; apply List.map_congr_left; intro c hc
  have hc16 : c < 16 := List.mem_range.mp hc
  rw [neonSerialize11Bytes_eq]
  unfold byteEncodeChunkVec byteEncodeChunk
  apply congrArg bitsToBytes; apply Array.ext
  · simp
  · intro idx hi1 hi2
    have hidx : idx < 176 := by simpa using hi1
    have hj : idx / 11 < 16 := by omega
    have hpos : 16 * c + idx / 11 < 256 := by omega
    have hb_i := hb.2 (16 * c + idx / 11) hpos
    have heq := neonCompressLane16_of_mod (d := 11) (Or.inr (Or.inr (Or.inr rfl)))
      (by omega) (by omega) (hr.2 (16 * c + idx / 11) hpos)
    have hlt_c : compressCoeff 11 (f.getD (16 * c + idx / 11) 0) < 2 ^ 16 := by
      unfold compressCoeff; exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    have hmap : (f.map (compressCoeff 11)).getD (16 * c + idx / 11) 0 =
        compressCoeff 11 (f.getD (16 * c + idx / 11) 0) := by
      by_cases hf : 16 * c + idx / 11 < f.size
      · simp [Array.getD, hf]
      · simp [Array.getD, hf]; unfold compressCoeff; decide
    simp only [Array.getElem_ofFn, hmap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_c]
    rw [← heq]
    by_cases hj8 : idx / 11 < 8
    · simp only [hj8, ↓reduceDIte, lane16_neonCompress8h (by decide : 1 ≤ 11) (by decide : 11 ≤ 16),
        polyVecNat, lane16_pack8x16, show 8 * (2 * c) + idx / 11 = 16 * c + idx / 11 by omega]
    · have hj8' : idx / 11 - 8 < 8 := by omega
      simp only [hj8, hj8', ↓reduceDIte, lane16_neonCompress8h (by decide : 1 ≤ 11) (by decide : 11 ≤ 16),
        polyVecNat, lane16_pack8x16, show 8 * (2 * c + 1) + (idx / 11 - 8) = 16 * c + idx / 11 by omega]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Simd

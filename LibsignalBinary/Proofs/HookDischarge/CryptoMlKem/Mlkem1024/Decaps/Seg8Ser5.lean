/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvAdd -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7SerSimd

/-!
# `kyber_decapsulate` (`B06`) — Segment 8 `compress_5` + `serialize_5` + `memcpy` (`+0xd6e0 .. +0xd89c`)

Proves the 16-iteration `compress_and_serialize_5` loop (`+0xd6e0 .. +0xd880`) writing `c₂'` (`160` B)
at `[sp + 26112, sp + 26272)` immediately after `c₁'` (`[sp + 24704, sp + 26112)`), followed by
`B28` `memcpy` (`+0xd880 .. +0xd89c`) copying `1,568` bytes `c₁' ++ c₂'` to `[sp + 30448, sp + 32016)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Ser5

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 bitsToBytes compressAndEncode compressCoeff)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 ext_lane16 ext_lane32 fin4_cases getSimdLane_16_eq getSimdLane_32_eq
  lane16 lane16_dup8x16 lane16_pack8x16 lane32 lane32_pack4x32 pack4x32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_and lane16_simdAdd8h lane16_simdTrn1_8h simdAdd8h simdCmltZero8h simdSqdmulh4s simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (
  even_shl_extract32 lane16_neonCompress8h neonCompress8h neonCompressLane16_of_mod odd_ushr_extract32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (
  byteEncodeChunk byteEncodeChunkVec compressAndEncode_eq_flatten_chunks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid (
  neonSerialize5Bytes neonSerialize5Bytes_eq neonSerialize5Half
  serialize5_byte1_llvm serialize5_byte4_unmasked)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 polyVecNat step_ldpQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (
  exec_simdAdd_4s exec_simdAnd_16b exec_simdCmltZero_8h exec_simdDup_4s
  exec_simdSqdmulh_4s exec_simdUshr_4s_4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (blk28_memcpy_06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7SerSimd (
  exec_umov_h1 exec_umov_h2 exec_umov_h3 exec_umov_h4 exec_umov_h5 exec_umov_h6)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvAdd (offD6e0)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0xd6e0 → 0xd898]
end

namespace Simp
@[scoped simp, arm64_norm, wp_norm] abbrev offD720      : BitVec 64 := BitVec.ofNat 64 55072
@[scoped simp, arm64_norm, wp_norm] abbrev offD7bc      : BitVec 64 := BitVec.ofNat 64 55228
@[scoped simp, arm64_norm, wp_norm] abbrev offD804      : BitVec 64 := BitVec.ofNat 64 55300
@[scoped simp, arm64_norm, wp_norm] abbrev offD87c      : BitVec 64 := BitVec.ofNat 64 55420
@[scoped simp, arm64_norm, wp_norm] abbrev offD880      : BitVec 64 := BitVec.ofNat 64 55424
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg9Start : BitVec 64 := BitVec.ofNat 64 55452
end Simp
export Simp (offD720 offD7bc offD804 offD87c offD880 offSeg9Start)
open scoped Simp

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC06

private theorem writeV_adv_congr {s : State} {rd : BitVec 5} {a b : BitVec 128} (h : a = b) :
    (s.writeVReg128 rd a).advancePC = (s.writeVReg128 rd b).advancePC :=
  h ▸ rfl

private theorem writeR64_adv_congr {s : State} {r : Reg} {a b : BitVec 64} (h : a = b) :
    (s.writeReg64 r a).advancePC = (s.writeReg64 r b).advancePC :=
  h ▸ rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_8h_31 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b10000#5 31#5 rd) s =
      (s.writeVReg128 rd (dup8x16 0x001f#16)).advancePC := rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdBic_4s_31 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b00010#5 31#5 rd) s =
      (s.writeVReg128 rd (s.readVReg128 rd &&& 0xffffffe0ffffffe0ffffffe0ffffffe0#128)).advancePC := rfl

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
theorem exec_simdShl_4s_5 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0100#4 0b101#3 0b01010#5 rn rd) s =
      (s.writeVReg128 rd (pack4x32 fun k => lane32 (s.readVReg128 rn) k <<< 5)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_false, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane <<< 5) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, lane32_pack4x32]; bv_bits

@[simp, arm64_norm, wp_norm]
theorem exec_simdUshr_4s_11 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0110#4 0b101#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (pack4x32 fun k => lane32 (s.readVReg128 rn) k >>> 11)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.true_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_
  change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane >>> 11) = _
  apply ext_lane32; intro i
  rw [lane32_mapSimdLanes_32, lane32_pack4x32]; bv_bits

private theorem umov16_lane0_eq (v : BitVec 128) :
    (((getSimdLane v 16 (0 : Fin 8).val).truncate 64).truncate 32).zeroExtend 64 =
      (lane16 v 0).zeroExtend 64 := by
  rw [getSimdLane_16_eq v 0]; bv_bits

@[simp, arm64_norm, wp_norm]
theorem exec_umov_h0 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 2#5 0b0111#4 rn rd) s =
      (s.writeReg64 (Reg.fromZRBits rd) ((lane16 (s.readVReg128 rn) 0).zeroExtend 64)).advancePC := by
  simp only [execInstWithSvc, State.writeReg]
  exact writeR64_adv_congr (umov16_lane0_eq (s.readVReg128 rn))

attribute [local wp_norm ↓ high]
  exec_simdMovi_8h_31 exec_simdBic_4s_31 exec_simdShl_4s_5 exec_simdUshr_4s_11
  exec_umov_h0 exec_umov_h1 exec_umov_h2 exec_umov_h3 exec_umov_h4 exec_umov_h5 exec_umov_h6
  exec_simdAdd_4s exec_simdAnd_16b exec_simdDup_4s exec_simdCmltZero_8h
  exec_simdUshr_4s_4 exec_simdSqdmulh_4s
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdTrn1_8h

theorem seg8_compress5_eq (vn : BitVec 128) :
    let u := simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn
    let evenIn := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j <<< 5) &&&
        (pack4x32 fun _ => 2097120#32)) k + 1664#32
    let oddIn := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j >>> 11) &&&
        0xffffffe0ffffffe0ffffffe0ffffffe0#128) k + 1664#32
    let cMul := pack4x32 fun _ => 10321340#32
    let evenOut := pack4x32 fun k => lane32 (simdSqdmulh4s evenIn cMul) k >>> 4
    let oddOut := pack4x32 fun k => lane32 (simdSqdmulh4s oddIn cMul) k >>> 4
    (simdTrn1_8h evenOut oddOut &&& dup8x16 0x001f#16) = neonCompress8h 5 vn := by
  dsimp only; unfold neonCompress8h
  have hu : simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn =
      simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16) := by
    apply ext_lane16; intro i; rw [lane16_simdAdd8h, lane16_simdAdd8h, BitVec.add_comm]
  rw [hu]; set u := simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16)
  have l32_and (a b : BitVec 128) (k : Fin 4) : lane32 (a &&& b) k = lane32 a k &&& lane32 b k := by
    apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [lane32, hr]
  have hm_ev (w : BitVec 32) : (w <<< 5) &&& 2097120#32 = (w <<< 5) &&& (0x0000ffff#32 <<< 5) := by
    bv_bits
  have hm_od (w : BitVec 32) : (w >>> 11) &&& 0xffffffe0#32 = (w >>> (16 - 5)) &&& (0x0000ffff#32 <<< 5) := by
    change (w >>> 11) &&& 0xffffffe0#32 = (w >>> 11) &&& (0x0000ffff#32 <<< 5); bv_bits
  have hev : (pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j <<< 5) &&&
        (pack4x32 fun _ => 2097120#32)) k + 1664#32) =
      (pack4x32 fun k => ((lane32 u k <<< 5) &&& (0x0000ffff#32 <<< 5)) + 1664#32) := by
    apply ext_lane32; intro k
    rw [lane32_pack4x32, lane32_pack4x32, l32_and, lane32_pack4x32, lane32_pack4x32, hm_ev,
      even_shl_extract32 (lane32 u k) 5 (by decide)]
  have hod : (pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u j >>> 11) &&&
        0xffffffe0ffffffe0ffffffe0ffffffe0#128) k + 1664#32) =
      (pack4x32 fun k => ((lane32 u k >>> (16 - 5)) &&& (0x0000ffff#32 <<< 5)) + 1664#32) := by
    apply ext_lane32; intro k
    rw [lane32_pack4x32, lane32_pack4x32, l32_and, lane32_pack4x32]
    have hc : lane32 0xffffffe0ffffffe0ffffffe0ffffffe0#128 k = 0xffffffe0#32 := by
      induction k using fin4_cases <;> rfl
    rw [hc, hm_od, odd_ushr_extract32 (lane32 u k) 5 (by decide) (by decide)]
  rw [hev, hod]; rfl

theorem lane16_neonCompress8h_5_mask (vn : BitVec 128) (j : Fin 8) :
    lane16 (neonCompress8h 5 vn) j &&& 0x001f#16 = lane16 (neonCompress8h 5 vn) j := by
  unfold neonCompress8h; dsimp only
  rw [lane16_and, lane16_dup8x16,
    show BitVec.ofNat 16 ((1 <<< 5) - 1) = 0x001f#16 from rfl,
    BitVec.and_assoc, BitVec.and_self]

theorem ser5_b0 (c0 c1 : BitVec 16) (h0 : c0 &&& 0x001f#16 = c0) (h1 : c1 &&& 0x001f#16 = c1) :
    ((c1.zeroExtend 32 <<< 5) ||| c0.zeroExtend 32).truncate 8 =
      ((c0 &&& 0x001f#16) ||| ((c1 &&& 0x001f#16) <<< 5)).truncate 8 := by
  rw [h0, h1]; bv_bits

theorem ser5_b1 (c1 c2 c3 : BitVec 16)
    (h1 : c1 &&& 0x001f#16 = c1) (h2 : c2 &&& 0x001f#16 = c2) :
    ((((c2.zeroExtend 32 <<< 10) ||| (c3.zeroExtend 32 <<< 15)) ||| (c1.zeroExtend 32 <<< 5)) >>> 8).truncate 8 =
      (((c1 &&& 0x001f#16) >>> 3) ||| ((c2 &&& 0x001f#16) <<< 2) ||| ((c3 &&& 0x001f#16) <<< 7)).truncate 8 := by
  have h := serialize5_byte1_llvm c1 c2 c3 h1 h2
  rw [h, h1, h2]

theorem ser5_b2 (c3 c4 : BitVec 16) (h3 : c3 &&& 0x001f#16 = c3) (h4 : c4 &&& 0x001f#16 = c4) :
    ((c4.zeroExtend 32 <<< 4) ||| (c3.zeroExtend 32 >>> 1)).truncate 8 =
      (((c3 &&& 0x001f#16) >>> 1) ||| ((c4 &&& 0x001f#16) <<< 4)).truncate 8 := by
  rw [h3, h4]; bv_bits

theorem ser5_b3 (c4 c5 c6 : BitVec 16)
    (h4 : c4 &&& 0x001f#16 = c4) (h5 : c5 &&& 0x001f#16 = c5) (h6 : c6 &&& 0x001f#16 = c6) :
    (((c6.zeroExtend 32 <<< 6) ||| (c4.zeroExtend 32 >>> 4)) ||| (c5.zeroExtend 32 <<< 1)).truncate 8 =
      (((c4 &&& 0x001f#16) >>> 4) ||| ((c5 &&& 0x001f#16) <<< 1) ||| ((c6 &&& 0x001f#16) <<< 6)).truncate 8 := by
  conv_lhs => rw [← h4, ← h5, ← h6]
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rcases b with _ | _ | _ | _ | _ | _ | _ | _ | b <;> try omega
  all_goals simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend]

theorem ser5_b4 (evenOut oddOut vMask : BitVec 128)
    (hv : vMask = simdTrn1_8h evenOut oddOut &&& dup8x16 0x001f#16) :
    (((lane16 oddOut 6).zeroExtend 32 <<< 3) ||| ((lane16 vMask 6).zeroExtend 32 >>> 2)).truncate 8 =
      (((lane16 vMask 6 &&& 0x001f#16) >>> 2) ||| ((lane16 vMask 7 &&& 0x001f#16) <<< 3)).truncate 8 := by
  have hc7 : lane16 vMask 7 &&& 0x001f#16 = lane16 oddOut 6 &&& 0x001f#16 := by
    rw [hv, lane16_and, lane16_dup8x16, BitVec.and_assoc, BitVec.and_self,
      lane16_simdTrn1_8h]
    rfl
  rw [hc7, ← serialize5_byte4_unmasked (lane16 vMask 6) (lane16 oddOut 6)]
  have hc6 : lane16 vMask 6 &&& 0x001f#16 = lane16 vMask 6 := by
    rw [hv, lane16_and, lane16_dup8x16, BitVec.and_assoc, BitVec.and_self]
  rw [hc6]; bv_bits

@[expose] def neonCompressSerialize5Poly (re : Poly16) : List (BitVec 8) :=
  ((List.range 16).map fun c =>
    neonSerialize5Bytes (neonCompress8h 5 (polyVecNat re (2 * c)))
      (neonCompress8h 5 (polyVecNat re (2 * c + 1)))).flatten

private theorem neonSerialize5Bytes_length (v0 v1 : BitVec 128) :
    (neonSerialize5Bytes v0 v1).length = 10 := rfl

@[simp] theorem neonCompressSerialize5Poly_length (re : Poly16) :
    (neonCompressSerialize5Poly re).length = 160 := by
  have hr : List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
  unfold neonCompressSerialize5Poly; rw [hr]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.length_append, List.length_nil, neonSerialize5Bytes_length]

theorem neonCompressSerialize5Poly_eq {re : Poly16} {f : Poly}
    (hb : PolyBounded16 1664 re) (hr : PolyRepresents re f) :
    neonCompressSerialize5Poly re = compressAndEncode 5 f := by
  unfold neonCompressSerialize5Poly
  rw [compressAndEncode_eq_flatten_chunks 5 (by decide) f]
  apply congrArg List.flatten; apply List.map_congr_left; intro c hc
  have hc16 : c < 16 := List.mem_range.mp hc
  rw [neonSerialize5Bytes_eq]
  unfold byteEncodeChunkVec byteEncodeChunk
  apply congrArg bitsToBytes; apply Array.ext
  · simp
  · intro idx hi1 hi2
    have hidx : idx < 80 := by simpa using hi1
    have hpos : 16 * c + idx / 5 < 256 := by omega
    have hb_i := hb.2 (16 * c + idx / 5) hpos
    have heq := neonCompressLane16_of_mod (d := 5) (Or.inr (Or.inl rfl))
      (by omega) (by omega) (hr.2 (16 * c + idx / 5) hpos)
    have hlt_c : compressCoeff 5 (f.getD (16 * c + idx / 5) 0) < 2 ^ 16 := by
      unfold compressCoeff; exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    have hmap : (f.map (compressCoeff 5)).getD (16 * c + idx / 5) 0 =
        compressCoeff 5 (f.getD (16 * c + idx / 5) 0) := by
      by_cases hf : 16 * c + idx / 5 < f.size
      · simp [Array.getD, hf]
      · simp [Array.getD, hf]; unfold compressCoeff; decide
    simp only [Array.getElem_ofFn, hmap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_c]
    rw [← heq]
    by_cases hj8 : idx / 5 < 8
    · simp only [hj8, ↓reduceDIte, lane16_neonCompress8h (by decide : 1 ≤ 5) (by decide : 5 ≤ 16),
        polyVecNat, lane16_pack8x16, show 8 * (2 * c) + idx / 5 = 16 * c + idx / 5 by omega]
    · have hj8' : idx / 5 - 8 < 8 := by omega
      simp only [hj8, hj8', ↓reduceDIte, lane16_neonCompress8h (by decide : 1 ≤ 5) (by decide : 5 ≤ 16),
        polyVecNat, lane16_pack8x16, show 8 * (2 * c + 1) + (idx / 5 - 8) = 16 * c + idx / 5 by omega]

/-! ## 1. `ByteRangeMem` & `serialize_5` Cell Helpers -/

private def ByteRangeMem : Nat → BitVec 64 → (Nat → BitVec 8) → SepProp
  | 0, _, _ => emp
  | n + 1, ptr, f => (ptr ↦₈ f 0) ∗ ByteRangeMem n (ptr + 1#64) (fun i => f (i + 1))

private theorem byteRangeMem_congr {n : Nat} {ptr : BitVec 64} {f g : Nat → BitVec 8}
    (h : ∀ i, i < n → f i = g i) : ByteRangeMem n ptr f = ByteRangeMem n ptr g := by
  induction n generalizing ptr f g with
  | zero => rfl
  | succ n ih =>
    simp only [ByteRangeMem, h 0 (Nat.zero_lt_succ n),
      ih (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))]

private theorem SepStore8.byteRange {n k : Nat} {ea ptr : BitVec 64} {val : BitVec 8}
    {f : Nat → BitVec 8} (hk : k < n) (ha : ptr + BitVec.ofNat 64 k = ea) :
    SepStore8 ea val (ByteRangeMem n ptr f) (ByteRangeMem n ptr (Function.update f k val)) := by
  induction n generalizing k ptr ea f with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      have h0 : ptr = ea := by simpa using ha
      have hu : ByteRangeMem n (ptr + 1#64) (fun i => Function.update f 0 val (i + 1)) =
          ByteRangeMem n (ptr + 1#64) (fun i => f (i + 1)) :=
        byteRangeMem_congr (fun i _ => by simp [Function.update])
      simp only [ByteRangeMem, Function.update_self, hu]
      exact SepStore8.left (SepStore8.here h0)
    | succ j =>
      have ha' : (ptr + 1#64) + BitVec.ofNat 64 j = ea := by rw [← ha]; bv_omega
      have hu : ByteRangeMem n (ptr + 1#64) (fun i => Function.update f (j + 1) val (i + 1)) =
          ByteRangeMem n (ptr + 1#64) (Function.update (fun i => f (i + 1)) j val) :=
        byteRangeMem_congr (fun i _ => by simp [Function.update])
      simp only [ByteRangeMem, show Function.update f (j + 1) val 0 = f 0 by simp [Function.update], hu]
      exact SepStore8.right (ih (Nat.lt_of_succ_lt_succ hk) ha')

private theorem sepWP_elim_cell1 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 8, SepWP prog target s ((a ↦₈ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 1 ∗ R0) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [memRegion_one, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  exact h v R (by simpa only [sepConj_assoc] using hv)

private theorem sepWP_elim_byteRange :
    ∀ (n : Nat), n ≤ 16 → ∀ {prog : Program} {target : BitVec 64} {s : State}
      {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop},
      (∀ f : Nat → BitVec 8, SepWP prog target s (ByteRangeMem n a f ∗ R0) post) →
      SepWP prog target s (memRegion a n ∗ R0) post
  | 0, _, _, _, _, a, _, _, h => by
    simpa [ByteRangeMem, memRegion_zero] using h (fun _ => 0#8)
  | n + 1, hn, _, _, _, a, R0, _, h => by
    rw [show n + 1 = 1 + n by omega,
      memRegion_split' (b := a) (b' := a + 1#64) (n := 1) (k := (n : Nat)) rfl (by bv_omega)
        (by change 1 + n ≤ 0x10000000000000000; omega),
      sepConj_assoc]
    apply sepWP_elim_cell1; intro v0
    refine SepWP.weaken_pre
      (show (a ↦₈ v0) ∗ (memRegion (a + 1#64) n ∗ R0) ⊢
        memRegion (a + 1#64) n ∗ ((a ↦₈ v0) ∗ R0) by sep_frame) ?_
    apply sepWP_elim_byteRange n (by omega); intro f'
    let f : Nat → BitVec 8 := fun i => match i with | 0 => v0 | j + 1 => f' j
    have hf : ByteRangeMem (n + 1) a f = (a ↦₈ v0) ∗ ByteRangeMem n (a + 1#64) f' := rfl
    refine SepWP.weaken_pre ?_ (h f)
    rw [hf]; sep_frame

private theorem byteRangeMem_split5 (a : BitVec 64) (f : Nat → BitVec 8) :
    ByteRangeMem 10 a f =
      ByteRangeMem 5 a f ∗ ByteRangeMem 5 (a + 5#64) (fun i => f (i + 5)) := by
  dsimp only [ByteRangeMem]
  simp only [sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd, Nat.add_assoc]

private theorem byteRangeMem5_eq_cells (a : BitVec 64) (f : Nat → BitVec 8) :
    ByteRangeMem 5 a f =
      (a ↦₈ f 0) ∗ ((a + 1#64) ↦₈ f 1) ∗ ((a + 2#64) ↦₈ f 2) ∗
      ((a + 3#64) ↦₈ f 3) ∗ ((a + 4#64) ↦₈ f 4) := by
  dsimp only [ByteRangeMem]
  simp only [sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

private theorem cells5_eq_neonSerialize5Half (a : BitVec 64) (v : BitVec 128) :
    let c : Fin 8 → BitVec 16 := fun j => lane16 v j &&& 0x001f#16
    (a ↦₈ (c 0 ||| (c 1 <<< 5)).truncate 8) ∗
    ((a + 1#64) ↦₈ ((c 1 >>> 3) ||| (c 2 <<< 2) ||| (c 3 <<< 7)).truncate 8) ∗
    ((a + 2#64) ↦₈ ((c 3 >>> 1) ||| (c 4 <<< 4)).truncate 8) ∗
    ((a + 3#64) ↦₈ ((c 4 >>> 4) ||| (c 5 <<< 1) ||| (c 6 <<< 6)).truncate 8) ∗
    ((a + 4#64) ↦₈ ((c 6 >>> 2) ||| (c 7 <<< 3)).truncate 8) =
    (a ↦ₛ neonSerialize5Half v) := by
  dsimp only [neonSerialize5Half]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

private theorem cells10_eq_neonSerialize5Bytes (a : BitVec 64) (v0 v1 : BitVec 128) :
    (a ↦ₛ neonSerialize5Half v0) ∗ ((a + 5#64) ↦ₛ neonSerialize5Half v1) =
    (a ↦ₛ neonSerialize5Bytes v0 v1) := by
  rw [neonSerialize5Bytes, pointsToBytes_append,
    show (neonSerialize5Half v0).length = 5 by rfl]

@[simp] private theorem sp_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).sp = s.sp := rfl
@[simp] private theorem spA_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).spAligned = s.spAligned := rfl
@[simp] private theorem pstate_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).pstate = s.pstate := rfl
@[simp] private theorem readReg64_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) (r : Reg) :
    (s.writeVReg128 v w).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem sp_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).sp = s.sp := rfl
@[simp] private theorem spA_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).spAligned = s.spAligned := rfl
@[simp] private theorem pstate_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).pstate = s.pstate := rfl
@[simp] private theorem status_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).status = s.status := rfl
@[simp] private theorem mem_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).mem = s.mem := rfl
@[simp] private theorem readReg64_orFpsr' (s : State) (f : BitVec 32) (r : Reg) :
    (s.orFpsr f).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readVReg128_orFpsr' (s : State) (f : BitVec 32) (v : BitVec 5) :
    (s.orFpsr f).readVReg128 v = s.readVReg128 v := rfl
@[simp] private theorem spA_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).spAligned = s.spAligned := rfl
@[simp] private theorem spA_setMem' (s : State) (m : Memory) : (s.setMem m).spAligned = s.spAligned := rfl
@[simp] private theorem readReg64_setPC' (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readReg64_setMem' (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readVReg128_setMem' (s : State) (m : Memory) (v : BitVec 5) :
    (s.setMem m).readVReg128 v = s.readVReg128 v := rfl
@[simp] private theorem readReg32_setMem' (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[simp] private theorem readReg32_setPC' (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[simp] private theorem pstate_setMem' (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := rfl
@[simp] private theorem sp_setMem' (s : State) (m : Memory) : (s.setMem m).sp = s.sp := rfl

private theorem step_str8_byteRange {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (b ea : BitVec 64) (pcOff nextOff k : Nat) (rt : Reg) (val : BitVec 8)
    (f : Nat → BitVec 8)
    (hk : k < 10) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.str .B8 rt (.Offset .x11 (BitVec.ofNat 64 k))))
    (hea : s.readReg64 .x11 = ea) (hval : (s.readReg32 rt).truncate 8 = val)
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
      (ByteRangeMem 10 ea (Function.update f k val) ∗ Rest) post) :
    SepWP prog target_pc s (ByteRangeMem 10 ea f ∗ Rest) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact SepWP.step_str8 (wb := none) hpc hrun hfetch rfl
    (by simp [evalAddrMode, hea]) hval
    (SepStore8.left (SepStore8.byteRange hk rfl))
    (by simp [applyWriteback, hpc']) hnext

private def ser5Chunk (v : Poly16) (c : Nat) : List (BitVec 8) :=
  neonSerialize5Bytes (neonCompress8h 5 (polyVecNat v (2 * c)))
    (neonCompress8h 5 (polyVecNat v (2 * c + 1)))

private def ser5Prefix (v : Poly16) (c : Nat) : List (BitVec 8) :=
  ((List.range c).map (ser5Chunk v)).flatten

private theorem ser5Chunk_length (v : Poly16) (c : Nat) : (ser5Chunk v c).length = 10 := rfl

private theorem ser5Prefix_length (v : Poly16) (c : Nat) : (ser5Prefix v c).length = 10 * c := by
  induction c with
  | zero => simp [ser5Prefix]
  | succ n ih =>
    rw [ser5Prefix, List.range_succ, List.map_append, List.flatten_append, List.length_append,
      ← ser5Prefix, ih]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, ser5Chunk_length]
    omega

private theorem ser5Prefix_succ (v : Poly16) (c : Nat) :
    ser5Prefix v (c + 1) = ser5Prefix v c ++ ser5Chunk v c := by
  simp [ser5Prefix, List.range_succ, List.flatten_append]

private theorem ser5Prefix_sixteen (v : Poly16) :
    ser5Prefix v 16 = neonCompressSerialize5Poly v := rfl

private theorem ser5_prefix_append_chunk (dst : BitVec 64) (v : Poly16) (c : Nat) :
    (dst ↦ₛ ser5Prefix v c) ∗ ((dst + BitVec.ofNat 64 (10 * c)) ↦ₛ ser5Chunk v c) =
      (dst ↦ₛ ser5Prefix v (c + 1)) := by
  rw [ser5Prefix_succ, pointsToBytes_append, ser5Prefix_length]

private def c31Vec       : BitVec 128 := dup8x16 0x001f#16
private def c3329Vec     : BitVec 128 := dup8x16 3329#16
private def c2097120Vec  : BitVec 128 := pack4x32 fun _ => 2097120#32
private def c1664Vec     : BitVec 128 := pack4x32 fun _ => 1664#32
private def c10321340Vec : BitVec 128 := pack4x32 fun _ => 10321340#32

private theorem sepWP_seq_cl {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post1 post2 : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mpl sm.mem ∧ post1 sm Pm)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mpl m)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl h1
      (fun _ _ _ _ hc hp1 => ⟨hc, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hp1⟩ => h2 sm Pm hpc hrun hc hp1)

private structure Seg8SimdPres (s0 sm : State) (sp : BitVec 64) : Prop where
  fp  : sm.readReg64 .fp  = s0.readReg64 .fp
  x22 : sm.readReg64 .x22 = s0.readReg64 .x22
  x10 : sm.readReg64 .x10 = sp + 24704#64
  v0  : sm.readVReg128 0#5 = c31Vec
  v1  : sm.readVReg128 1#5 = c3329Vec
  v2  : sm.readVReg128 2#5 = c2097120Vec
  v3  : sm.readVReg128 3#5 = c1664Vec
  v4  : sm.readVReg128 4#5 = c10321340Vec

@[simp] private theorem spA_writeReg64_gpr (s : State) (i : BitVec 5) (w : BitVec 64) :
    (s.writeReg64 (.gpr i) w).spAligned = s.spAligned := rfl
@[simp] private theorem spA_writeReg32_gpr (s : State) (i : BitVec 5) (w : BitVec 32) :
    (s.writeReg32 (.gpr i) w).spAligned = s.spAligned := rfl
@[simp] private theorem spA_setPState (s : State) (p : PState) :
    (s.setPState p).spAligned = s.spAligned := rfl
@[simp] private theorem readReg64_setPState' (s : State) (p : PState) (r : Reg) :
    (s.setPState p).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readVReg128_setPState' (s : State) (p : PState) (v : BitVec 5) :
    (s.setPState p).readVReg128 v = s.readVReg128 v := rfl
@[simp] private theorem readVReg128_setPC' (s : State) (pc : BitVec 64) (v : BitVec 5) :
    (s.setPC pc).readVReg128 v = s.readVReg128 v := rfl
@[simp] private theorem readVReg128_writeReg64' (s : State) (r : Reg) (w : BitVec 64) (v : BitVec 5) :
    (s.writeReg64 r w).readVReg128 v = s.readVReg128 v := by cases r <;> rfl
@[simp] private theorem readVReg128_writeReg32' (s : State) (r : Reg) (w : BitVec 32) (v : BitVec 5) :
    (s.writeReg32 r w).readVReg128 v = s.readVReg128 v := by cases r <;> rfl

private theorem seg8_ser5_header [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (P : SepProp)
    (hpc : s.pc = b + offD6e0) (hrun : s.status = .Running) (hsp : s.sp = sp) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offD720) s P
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = s.spAligned ∧
        sm.readReg64 .x8 = sp + 32512#64 ∧ sm.readReg64 .x9 = 1408#64 ∧
        Seg8SimdPres s sm sp ∧ Pm = P) := by
  subst hbase
  wp_steps 16
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp,
      by simp, by simp,
      ⟨by simp, by simp, by simp,
        by simp [c31Vec], by simp [c3329Vec], by simp [c2097120Vec],
        by simp [c1664Vec], by simp [c10321340Vec]⟩, rfl⟩

private theorem trunc32_zext64_shl (x : BitVec 16) (n : Nat) :
    ((x.zeroExtend 64) <<< n).truncate 32 = (x.zeroExtend 32) <<< n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, hi, show i < 64 by omega, decide_true, Bool.true_and]
  by_cases hn : i < n
  · simp [hn]
  · simp [hn, show i - n < 32 by omega, show i - n < 64 by omega]

section InnerSimd
attribute [local irreducible] dup8x16 pack4x32 lane32 polyVecNat
  simdAdd8h simdCmltZero8h simdSqdmulh4s simdTrn1_8h neonCompress8h

set_option maxRecDepth 24000 in
private theorem seg8_inner_simd_m1 [MlKemPlacement]
    (s : State) (sp : BitVec 64) (P : SepProp) (u0 u1 : BitVec 128)
    (hpc : s.pc = blkPl06.base + BitVec.ofNat 64 55116) (hrun : s.status = .Running)
    (hpres : Seg8SimdPres s s sp)
    (hv5 : s.readVReg128 5#5 = u0) (hv6 : s.readVReg128 6#5 = u1) :
    let ev0 := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u0 j <<< 5) &&& c2097120Vec) k + lane32 c1664Vec k
    let od0 := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u0 j >>> 11) &&& 0xffffffe0ffffffe0ffffffe0ffffffe0#128) k + lane32 c1664Vec k
    let ev1 := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u1 j <<< 5) &&& c2097120Vec) k + lane32 c1664Vec k
    let od1 := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u1 j >>> 11) &&& 0xffffffe0ffffffe0ffffffe0ffffffe0#128) k + lane32 c1664Vec k
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + BitVec.ofNat 64 55164) s P
      (fun s1 P1 =>
        s1.sp = s.sp ∧ s1.spAligned = s.spAligned ∧ s1.pstate = s.pstate ∧
        (∀ r : Reg, s1.readReg64 r = s.readReg64 r) ∧
        Seg8SimdPres s s1 sp ∧
        s1.readVReg128 7#5 = ev0 ∧ s1.readVReg128 5#5 = od0 ∧
        s1.readVReg128 16#5 = ev1 ∧ s1.readVReg128 6#5 = od1 ∧ P1 = P) := by
  dsimp only
  rcases hpres with ⟨_, _, hx10, hv0, hv1, hv2, hv3, hv4⟩
  wp_steps 12
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp, by simp, fun r => by simp,
      ⟨by simp, by simp, by simp [hx10], by simp [hv0], by simp [hv1],
        by simp [hv2], by simp [hv3], by simp [hv4]⟩,
      by simp, by simp, by simp, by simp, rfl⟩

set_option maxRecDepth 24000 in
private theorem seg8_inner_simd_m2 [MlKemPlacement]
    (s0 s : State) (sp : BitVec 64) (P : SepProp) (ev0 od0 ev1 od1 : BitVec 128)
    (hpc : s.pc = blkPl06.base + BitVec.ofNat 64 55164) (hrun : s.status = .Running)
    (hpres : Seg8SimdPres s0 s sp)
    (hv7 : s.readVReg128 7#5 = ev0) (hv5 : s.readVReg128 5#5 = od0)
    (hv16 : s.readVReg128 16#5 = ev1) (hv6 : s.readVReg128 6#5 = od1) :
    let evenOut0 := pack4x32 fun k => lane32 (simdSqdmulh4s ev0 c10321340Vec) k >>> 4
    let oddOut0  := pack4x32 fun k => lane32 (simdSqdmulh4s od0 c10321340Vec) k >>> 4
    let evenOut1 := pack4x32 fun k => lane32 (simdSqdmulh4s ev1 c10321340Vec) k >>> 4
    let oddOut1  := pack4x32 fun k => lane32 (simdSqdmulh4s od1 c10321340Vec) k >>> 4
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + offD7bc) s P
      (fun s2 P2 =>
        s2.sp = s.sp ∧ s2.spAligned = s.spAligned ∧ s2.pstate = s.pstate ∧
        s2.readReg64 .x8 = s.readReg64 .x8 ∧ s2.readReg64 .x9 = s.readReg64 .x9 ∧
        s2.readReg64 .x11 = s.readReg64 .x11 ∧ Seg8SimdPres s0 s2 sp ∧
        s2.readVReg128 5#5 = (simdTrn1_8h evenOut0 oddOut0 &&& dup8x16 0x001f#16) ∧
        s2.readVReg128 6#5 = (simdTrn1_8h evenOut1 oddOut1 &&& dup8x16 0x001f#16) ∧
        s2.readReg32 .x12 = (lane16 oddOut0 6).zeroExtend 32 <<< 3 ∧
        s2.readReg32 .x13 = (lane16 oddOut1 6).zeroExtend 32 <<< 3 ∧ P2 = P) := by
  dsimp only
  rcases hpres with ⟨hfp, hx22, hx10, hv0, hv1, hv2, hv3, hv4⟩
  wp_steps 16
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp, by simp, by simp, by simp, by simp,
      ⟨by simp [hfp], by simp [hx22], by simp [hx10], by simp [hv0], by simp [hv1],
        by simp [hv2], by simp [hv3], by simp [hv4]⟩,
      by simp [c31Vec],
      by simp [c31Vec],
      by simp [State.readReg32, BitVec.truncate_eq_setWidth, BitVec.zeroExtend],
      by simp [State.readReg32, BitVec.truncate_eq_setWidth, BitVec.zeroExtend], rfl⟩

private theorem seg8_inner_simd [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (re : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offD720) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = sp + BitVec.ofNat 64 (32512 + 32 * c))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (1408 + 10 * c))
    (hpres : Seg8SimdPres s0 s sp) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offD7bc) s
      (PolyMem (sp + 32496#64) (polyVecNat re) ∗ Rest)
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = s.spAligned ∧
        s2.pstate = subsPState64 (BitVec.ofNat 64 (1408 + 10 * (c + 1))) 1568#64 ∧
        s2.readReg64 .x8 = sp + BitVec.ofNat 64 (32512 + 32 * (c + 1)) ∧
        s2.readReg64 .x9 = BitVec.ofNat 64 (1408 + 10 * (c + 1)) ∧
        s2.readReg64 .x11 = sp + BitVec.ofNat 64 (26112 + 10 * c) ∧
        Seg8SimdPres s0 s2 sp ∧
        s2.readVReg128 5#5 = neonCompress8h 5 (polyVecNat re (2 * c)) ∧
        s2.readVReg128 6#5 = neonCompress8h 5 (polyVecNat re (2 * c + 1)) ∧
        (∃ evenOut0 oddOut0,
          neonCompress8h 5 (polyVecNat re (2 * c)) =
            simdTrn1_8h evenOut0 oddOut0 &&& dup8x16 0x001f#16 ∧
          s2.readReg32 .x12 = (lane16 oddOut0 6).zeroExtend 32 <<< 3) ∧
        (∃ evenOut1 oddOut1,
          neonCompress8h 5 (polyVecNat re (2 * c + 1)) =
            simdTrn1_8h evenOut1 oddOut1 &&& dup8x16 0x001f#16 ∧
          s2.readReg32 .x13 = (lane16 oddOut1 6).zeroExtend 32 <<< 3) ∧
        P2 = (PolyMem (sp + 32496#64) (polyVecNat re) ∗ Rest)) := by
  subst hbase
  have ha_ldp : (sp + 32496#64) + BitVec.ofNat 64 (16 * (2 * c)) =
      (sp + BitVec.ofNat 64 (32512 + 32 * c)) + 0xfffffffffffffff0#64 := by
    clear * - hc; bv_omega
  refine step_ldpQ128
    (s' := ((s.writeVReg128 5#5 (polyVecNat re (2 * c))).writeVReg128 6#5
      (polyVecNat re (2 * c + 1))).setPC (blkPl06.base + BitVec.ofNat 64 55076))
    (vt1 := 5#5) (vt2 := 6#5) (addr := .Offset .x8 0xfffffffffffffff0#64) (wb := none)
    hpc hrun (by simp only [arm64_norm]; rfl) rfl (by simp [evalAddrMode, hx8]) rfl
    (SepLoad128.left (SepLoad128.vecRange (by omega : 2 * c < 32) ha_ldp))
    (SepLoad128.left (SepLoad128.vecRange (by omega : 2 * c + 1 < 32)
      (by rw [← ha_ldp]; clear * -; bv_omega)))
    (by simp [applyWriteback, offD720]) ?_
  wp_steps 10
  refine SepWP.seq (seg8_inner_simd_m1 _ sp _
    (simdAdd8h (simdCmltZero8h (polyVecNat re (2 * c)) &&& c3329Vec) (polyVecNat re (2 * c)))
    (simdAdd8h (simdCmltZero8h (polyVecNat re (2 * c + 1)) &&& c3329Vec) (polyVecNat re (2 * c + 1)))
    (by wp_norm_lhs) (by simp [hrun])
    ⟨rfl, rfl, by simp [hpres.x10], by simp [hpres.v0], by simp [hpres.v1],
      by simp [hpres.v2], by simp [hpres.v3], by simp [hpres.v4]⟩
    (by simp [hpres.v1]) (by simp [hpres.v1])) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hpst1, hregs1, hpres1, hv7_1, hv5_1, hv16_1, hv6_1, rfl⟩
  have hpres01 : Seg8SimdPres s0 s1 sp :=
    ⟨hpres1.fp.trans (by simp [hpres.fp]), hpres1.x22.trans (by simp [hpres.x22]),
      hpres1.x10, hpres1.v0, hpres1.v1, hpres1.v2, hpres1.v3, hpres1.v4⟩
  refine SepWP.mono (seg8_inner_simd_m2 s0 s1 sp _ _ _ _ _ hpc1 hrun1 hpres01 hv7_1 hv5_1 hv16_1 hv6_1) ?_
  rintro s2 P2 _ _ ⟨hsp2, hspA2, hpst2, hx8_2, hx9_2, hx11_2, hpres2, hv5_2, hv6_2, hx12_2, hx13_2, rfl⟩
  have h9 : BitVec.ofNat 64 (1408 + 10 * c) + 10#64 = BitVec.ofNat 64 (1408 + 10 * (c + 1)) := by
    clear * - hc; bv_omega
  have h8 : sp + BitVec.ofNat 64 (32512 + 32 * c) + 32#64 = sp + BitVec.ofNat 64 (32512 + 32 * (c + 1)) := by
    clear * - hc; bv_omega
  have h11 : (sp + 24704#64) + BitVec.ofNat 64 (1408 + 10 * c) = sp + BitVec.ofNat 64 (26112 + 10 * c) := by
    clear * - hc; bv_omega
  simp only [c3329Vec, c2097120Vec, c1664Vec, c10321340Vec, lane32_pack4x32] at hv5_2 hv6_2 hx12_2 hx13_2
  have hc0 := seg8_compress5_eq (polyVecNat re (2 * c))
  dsimp only at hc0
  have hc1 := seg8_compress5_eq (polyVecNat re (2 * c + 1))
  dsimp only at hc1
  exact ⟨by simpa [hsp] using hsp2.trans hsp1,
    by simpa using hspA2.trans hspA1,
    by rw [hpst2, hpst1]; simp [h9],
    by rw [hx8_2, hregs1]; simp [h8],
    by rw [hx9_2, hregs1]; simp [h9],
    by rw [hx11_2, hregs1]; simp [hpres.x10, h11],
    hpres2,
    hv5_2.trans hc0,
    hv6_2.trans hc1,
    ⟨_, _, hc0.symm, hx12_2⟩,
    ⟨_, _, hc1.symm, hx13_2⟩, rfl⟩

end InnerSimd

local macro "s8_strb " ea:term:arg hx11:term:arg hrun:term:arg
    pcOff:num nextOff:num k:num rt:term:arg : tactic => `(tactic|
  (refine step_str8_byteRange blkPl06.base $ea $pcOff $nextOff $k $rt _ _
      (by decide) (by wp_norm_lhs) (by simp [$hrun:term]) (by simp only [arm64_norm])
      (by simp [$hx11:term]) rfl rfl ?_;
   intro _))

private theorem zext8_or_zext64 (a : BitVec 32) (b : BitVec 16) :
    zeroExtend 8 (zeroExtend 64 a ||| zeroExtend 64 b) = (a ||| zeroExtend 32 b).truncate 8 := by
  bv_bits

set_option maxRecDepth 8000 in
private theorem seg8_inner_store [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 s : State) (sp ea : BitVec 64) (vFirst vSecond : BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offD7bc) (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = ea) (hpres : Seg8SimdPres s0 s sp)
    (hv5 : s.readVReg128 5#5 = vFirst) (hv6 : s.readVReg128 6#5 = vSecond)
    (hm5 : ∀ j : Fin 8, lane16 vFirst j &&& 0x001f#16 = lane16 vFirst j)
    (hm6 : ∀ j : Fin 8, lane16 vSecond j &&& 0x001f#16 = lane16 vSecond j)
    (ho0 : ∃ evenOut0 oddOut0, vFirst = simdTrn1_8h evenOut0 oddOut0 &&& dup8x16 0x001f#16 ∧
      s.readReg32 .x12 = (lane16 oddOut0 6).zeroExtend 32 <<< 3)
    (ho1 : ∃ evenOut1 oddOut1, vSecond = simdTrn1_8h evenOut1 oddOut1 &&& dup8x16 0x001f#16 ∧
      s.readReg32 .x13 = (lane16 oddOut1 6).zeroExtend 32 <<< 3) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offD87c) s
      (memRegion ea 10 ∗ Rest)
      (fun s3 P3 =>
        s3.sp = s.sp ∧ s3.spAligned = s.spAligned ∧ s3.pstate = s.pstate ∧
        s3.readReg64 .x8 = s.readReg64 .x8 ∧ s3.readReg64 .x9 = s.readReg64 .x9 ∧
        Seg8SimdPres s0 s3 sp ∧
        (P3 ⊢ (ea ↦ₛ neonSerialize5Bytes vFirst vSecond) ∗ Rest)) := by
  subst hbase
  apply sepWP_elim_byteRange 10 (by decide); intro f0
  wp_steps 18; s8_strb ea hx11 hrun 55300 55304 4 .x12
  wp_steps 11; s8_strb ea hx11 hrun 55348 55352 0 .x15
  wp_steps 2;  s8_strb ea hx11 hrun 55360 55364 7 .x12
  wp_steps 7
  s8_strb ea hx11 hrun 55392 55396 2 .x19
  s8_strb ea hx11 hrun 55396 55400 5 .x2
  s8_strb ea hx11 hrun 55400 55404 3 .x16
  s8_strb ea hx11 hrun 55404 55408 8 .x15
  s8_strb ea hx11 hrun 55408 55412 1 .x14
  s8_strb ea hx11 hrun 55412 55416 6 .x12
  s8_strb ea hx11 hrun 55416 55420 9 .x13
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp, by simp, by simp, by simp,
      ⟨by simp [hpres.fp], by simp [hpres.x22], by simp [hpres.x10],
        by simp [hpres.v0], by simp [hpres.v1], by simp [hpres.v2],
        by simp [hpres.v3], by simp [hpres.v4]⟩, ?_⟩
  rcases ho0 with ⟨evenOut0, oddOut0, hvf0, hx12⟩
  rcases ho1 with ⟨evenOut1, oddOut1, hvf1, hx13⟩
  change (s.readReg64 (.gpr 12#5)).truncate 32 = _ at hx12
  change (s.readReg64 (.gpr 13#5)).truncate 32 = _ at hx13
  have hc0 := cells5_eq_neonSerialize5Half ea vFirst; dsimp only at hc0
  have hc1 := cells5_eq_neonSerialize5Half (ea + 5#64) vSecond
  dsimp only at hc1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hc1
  conv_lhs =>
    arg 1
    rw [byteRangeMem_split5]
    arg 1
    rw [byteRangeMem5_eq_cells]
    simp only [arm64_norm, Function.update, Nat.reduceEqDiff,
      trunc32_zext64_shl, zext8_or_zext64]
    rw [hx12, ser5_b0 _ _ (hm5 0) (hm5 1), ser5_b1 _ _ _ (hm5 1) (hm5 2),
      ser5_b2 _ _ (hm5 3) (hm5 4), ser5_b3 _ _ _ (hm5 4) (hm5 5) (hm5 6),
      ser5_b4 evenOut0 oddOut0 vFirst hvf0, hc0]
  conv_lhs =>
    arg 1
    arg 2
    rw [byteRangeMem5_eq_cells]
    simp only [arm64_norm, Function.update, Nat.reduceEqDiff,
      trunc32_zext64_shl, zext8_or_zext64]
    rw [hx13, ser5_b0 _ _ (hm6 0) (hm6 1), ser5_b1 _ _ _ (hm6 1) (hm6 2),
      ser5_b2 _ _ (hm6 3) (hm6 4), ser5_b3 _ _ _ (hm6 4) (hm6 5) (hm6 6),
      ser5_b4 evenOut1 oddOut1 vSecond hvf1, hc1]
  conv_lhs => arg 1; rw [cells10_eq_neonSerialize5Bytes]
  sep_frame

private theorem seg8_inner_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (re : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offD720) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hpres : Seg8SimdPres s0 s sp)
    (hx8 : s.readReg64 .x8 = sp + BitVec.ofNat 64 (32512 + 32 * c))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (1408 + 10 * c)) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if c + 1 < 16 then b + offD720 else b + offD880) s
      (PolyMem (sp + 32496#64) (polyVecNat re) ∗
        memRegion (sp + BitVec.ofNat 64 (26112 + 10 * c)) 10 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = sp + BitVec.ofNat 64 (32512 + 32 * (c + 1)) ∧
        sf.readReg64 .x9 = BitVec.ofNat 64 (1408 + 10 * (c + 1)) ∧
        Seg8SimdPres s0 sf sp ∧
        (Pf ⊢ PolyMem (sp + 32496#64) (polyVecNat re) ∗
          ((sp + BitVec.ofNat 64 (26112 + 10 * c)) ↦ₛ ser5Chunk re c) ∗ Rest)) := by
  refine SepWP.seq
    (seg8_inner_simd hb hbase s0 s sp hc re _ hpc hrun hsp hx8 hx9 hpres) ?_
  rintro s2 P2 hpc2 hrun2
    ⟨hsp2, hspA2, hpst2, hx8_2, hx9_2, hx11_2, hpres2, hv5_2, hv6_2, ho0, ho1, rfl⟩
  refine SepWP.seq
    (SepWP.weaken_pre
      (show PolyMem (sp + 32496#64) (polyVecNat re) ∗ (memRegion _ 10 ∗ Rest) ⊢
        memRegion _ 10 ∗ (PolyMem (sp + 32496#64) (polyVecNat re) ∗ Rest) by sep_frame)
      (seg8_inner_store hb hbase s0 s2 sp _ _ _ _ hpc2 hrun2 hx11_2 hpres2 hv5_2 hv6_2
        (fun j => lane16_neonCompress8h_5_mask _ j)
        (fun j => lane16_neonCompress8h_5_mask _ j) ho0 ho1)) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hsp3, hspA3, hpst3, hx8_3, hx9_3, hpres3, hP3⟩
  subst hbase
  have hspA3' : s3.spAligned = true := hspA3.trans (hspA2.trans hspA)
  have hpost : P3 ⊢ PolyMem (sp + 32496#64) (polyVecNat re) ∗
      ((sp + BitVec.ofNat 64 (26112 + 10 * c)) ↦ₛ ser5Chunk re c) ∗ Rest :=
    Entails.trans hP3 (by dsimp only [ser5Chunk]; sep_frame)
  by_cases hlt : c + 1 < 16
  · simp only [hlt, ↓reduceIte]
    refine step_bCond_taken (dst := blkPl06.base + offD720)
      hpc3 hrun3 (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpst3, hpst2]
          clear * - hlt
          rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;>
            first | decide | omega)
      (by clear * -; dsimp [offD87c, offD720]; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun3])
      ⟨by simp [hsp3, hsp2], spAligned_of_sp_eq hspA3' (hsp3.trans hsp2) (by simp [hsp3, hsp2]),
        by simp [hx8_3, hx8_2], by simp [hx9_3, hx9_2],
        ⟨by simp [hpres3.fp], by simp [hpres3.x22], by simp [hpres3.x10],
          by simp [hpres3.v0], by simp [hpres3.v1], by simp [hpres3.v2],
          by simp [hpres3.v3], by simp [hpres3.v4]⟩, hpost⟩
  · simp only [hlt, ↓reduceIte]
    have hc15 : c = 15 := by omega
    subst hc15
    refine step_bCond_not_taken (dst := blkPl06.base + offD880)
      hpc3 hrun3 (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpst3, hpst2])
      (by clear * -; dsimp [offD87c, offD880]; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun3])
      ⟨by simp [hsp3, hsp2], spAligned_of_sp_eq hspA3' (hsp3.trans hsp2) (by simp [hsp3, hsp2]),
        by simp [hx8_3, hx8_2], by simp [hx9_3, hx9_2],
        ⟨by simp [hpres3.fp], by simp [hpres3.x22], by simp [hpres3.x10],
          by simp [hpres3.v0], by simp [hpres3.v1], by simp [hpres3.v2],
          by simp [hpres3.v3], by simp [hpres3.v4]⟩, hpost⟩

private theorem seg8_inner_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 : State) (sp : BitVec 64) (re : Poly16) :
    ∀ (rem c : Nat), c + rem = 15 → ∀ (s : State) (Rest : SepProp),
      s.pc = b + offD720 → s.status = .Running → s.sp = sp → s.spAligned = true →
      Seg8SimdPres s0 s sp →
      s.readReg64 .x8 = sp + BitVec.ofNat 64 (32512 + 32 * c) →
      s.readReg64 .x9 = BitVec.ofNat 64 (1408 + 10 * c) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + offD880) s
        (PolyMem (sp + 32496#64) (polyVecNat re) ∗ ((sp + 26112#64) ↦ₛ ser5Prefix re c) ∗
          memRegion (sp + BitVec.ofNat 64 (26112 + 10 * c)) (10 * (16 - c)) ∗ Rest)
        (fun sf Pf =>
          sf.sp = sp ∧ sf.spAligned = true ∧
          sf.readReg64 .fp = s0.readReg64 .fp ∧ sf.readReg64 .x22 = s0.readReg64 .x22 ∧
          (Pf ⊢ PolyMem (sp + 32496#64) (polyVecNat re) ∗
            ((sp + 26112#64) ↦ₛ neonCompressSerialize5Poly re) ∗ Rest)) := by
  intro rem c hrem s Rest hpc hrun hsp hspA hpres hx8 hx9
  induction rem generalizing c s with
  | zero =>
    have hc15 : c = 15 := by omega
    subst hc15
    have hstep := seg8_inner_iter hb hbase s0 s sp (by decide : 15 < 16) re
      (((sp + 26112#64) ↦ₛ ser5Prefix re 15) ∗ Rest) hpc hrun hsp hspA hpres hx8 hx9
    simp only [show ¬ (15 + 1 < 16) by decide, ↓reduceIte, show 10 * (16 - 15) = 10 by decide] at hstep ⊢
    refine SepWP.weaken_pre (by sep_frame) (SepWP.mono hstep ?_)
    rintro sf Pf _ _ ⟨hsp', hspA', _, _, hpres', hPf⟩
    refine ⟨hsp', hspA', hpres'.fp, hpres'.x22, Entails.trans hPf ?_⟩
    have ha : (sp + 26112#64) + BitVec.ofNat 64 (10 * 15) = sp + BitVec.ofNat 64 (26112 + 10 * 15) := by
      clear * -; bv_omega
    rw [← ser5Prefix_sixteen re, ← ser5_prefix_append_chunk (sp + 26112#64) re 15, ha]; sep_frame
  | succ rem ih =>
    have hc15 : c + 1 < 16 := by omega
    have hsplit : memRegion (sp + BitVec.ofNat 64 (26112 + 10 * c)) (10 * (16 - c)) =
        memRegion (sp + BitVec.ofNat 64 (26112 + 10 * c)) 10 ∗
          memRegion (sp + BitVec.ofNat 64 (26112 + 10 * (c + 1))) (10 * (16 - (c + 1))) :=
      memRegion_split' (b := sp + BitVec.ofNat 64 (26112 + 10 * c))
        (b' := sp + BitVec.ofNat 64 (26112 + 10 * (c + 1))) (n := 10)
        (k := (10 * (16 - (c + 1)) : Nat)) (by omega) (by clear * - hc15; bv_omega) (by omega)
    rw [hsplit]
    have hstep := seg8_inner_iter hb hbase s0 s sp (by omega : c < 16) re
      (((sp + 26112#64) ↦ₛ ser5Prefix re c) ∗
        memRegion (sp + BitVec.ofNat 64 (26112 + 10 * (c + 1))) (10 * (16 - (c + 1))) ∗ Rest)
      hpc hrun hsp hspA hpres hx8 hx9
    simp only [hc15, ↓reduceIte] at hstep
    refine SepWP.seq (SepWP.weaken_pre (by sep_frame) hstep) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hx8_1, hx9_1, hpres1, hP1⟩
    have ha : (sp + 26112#64) + BitVec.ofNat 64 (10 * c) = sp + BitVec.ofNat 64 (26112 + 10 * c) := by
      clear * - hc15; bv_omega
    exact SepWP.weaken_pre
      (Entails.trans hP1 (by rw [← ser5_prefix_append_chunk (sp + 26112#64) re c, ha]; sep_frame))
      (ih (c + 1) (by omega) s1 hpc1 hrun1 hsp1 hspA1 hpres1 hx8_1 hx9_1)

theorem seg8_ser5_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {c1 : List (BitVec 8)} (hc1 : c1.length = 1408)
    (re : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offD6e0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let ct' := c1 ++ neonCompressSerialize5Poly re
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg9Start) s
      (((sp + 24704#64) ↦ₛ c1) ∗ memRegion (sp + 26112#64) 160 ∗
        memRegion (sp + 30448#64) 1568 ∗ PolyMem (sp + 32496#64) (polyVecNat re) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 1568#64 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ ((sp + 24704#64) ↦ₛ ct') ∗ ((sp + 30448#64) ↦ₛ ct') ∗
          PolyMem (sp + 32496#64) (polyVecNat re) ∗ Rest)) := by
  intro ct'
  refine sepWP_seq_cl hcl (seg8_ser5_header hb hbase s sp _ hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hsp1, hspA1, hx8_1, hx9_1, hpres1, rfl⟩
  have hloop := seg8_inner_loop hb hbase s sp re 15 0 rfl s1
    (((sp + 24704#64) ↦ₛ c1) ∗ memRegion (sp + 30448#64) 1568 ∗ Rest)
    hpc1 hrun1 hsp1 (hspA1.trans hspA) hpres1
    (by simpa using hx8_1) (by simpa using hx9_1)
  simp only [show ser5Prefix re 0 = [] from rfl, pointsToBytes_nil, emp_sepConj,
    show 10 * (16 - 0) = 160 by decide,
    show sp + BitVec.ofNat 64 (26112 + 10 * 0) = sp + 26112#64 by clear * -; bv_omega] at hloop
  refine sepWP_seq_cl hcl1 (SepWP.weaken_pre (by sep_frame) hloop) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hsp2, hspA2, hfp2, hx22_2, hP2⟩
  subst hbase
  have hjoin : ((sp + 24704#64) ↦ₛ c1) ∗ ((sp + 26112#64) ↦ₛ neonCompressSerialize5Poly re) =
      ((sp + 24704#64) ↦ₛ ct') := by
    have ha : (sp + 24704#64) + BitVec.ofNat 64 c1.length = sp + 26112#64 := by
      rw [hc1]; clear * -; bv_omega
    rw [pointsToBytes_append, ha]
  have hlen : ct'.length = 1568 := by
    simp [ct', List.length_append, hc1, neonCompressSerialize5Poly_length]
  refine SepWP.weaken_pre
    (Entails.trans hP2 (show PolyMem (sp + 32496#64) (polyVecNat re) ∗
      ((sp + 26112#64) ↦ₛ neonCompressSerialize5Poly re) ∗
      (((sp + 24704#64) ↦ₛ c1) ∗ memRegion (sp + 30448#64) 1568 ∗ Rest) ⊢
      ((sp + 24704#64) ↦ₛ ct') ∗ memRegion (sp + 30448#64) 1568 ∗
        (PolyMem (sp + 32496#64) (polyVecNat re) ∗ Rest) by rw [← hjoin]; sep_frame)) ?_
  wp_steps 6; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl2)
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 30448#64, sp + 24704#64, ct')
  apply SepWP.done (by assumption) (by assumption); intro _hcl3
  have hsp3 : sf.sp = sp := hsp_sf.trans hsp2
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun_sf])
    ⟨hsp3, spAligned_of_sp_eq hspA2 hsp2 hsp3,
      by simp [*], by simp [*, Reg.x22], by simp [*, Reg.fp], by sep_frame⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Ser5

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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Add -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Simd

/-!
# `kyber_encapsulate` (`B07`) — Segment 5 `compress_5` SIMD Half (`+0x9d34 .. +0x9e10`)

Pure `compress_5` / `serialize_5` byte identities, `neonCompressSerialize5Poly`,
header (`+0x9d34 .. +0x9d74`), and SIMD `compress_5` body (`+0x9d74 .. +0x9e10`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5CompressSimd

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemBase MlKemPlacement mlkemBlockPlacement_ρ mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly Poly16 bitsToBytes compressAndEncode compressCoeff)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 ext_lane16 ext_lane32 fin4_cases getSimdLane_32_eq lane16 lane16_dup8x16 lane16_pack8x16 lane32 lane32_pack4x32 pack4x32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (lane16_and lane16_simdAdd8h lane16_simdTrn1_8h simdAdd8h simdCmltZero8h simdSqdmulh4s simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (even_shl_extract32 lane16_neonCompress8h neonCompress8h neonCompressLane16_of_mod odd_ushr_extract32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (byteEncodeChunk byteEncodeChunkVec compressAndEncode_eq_flatten_chunks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid (neonSerialize5Bytes neonSerialize5Bytes_eq serialize5_byte1_llvm serialize5_byte4_unmasked)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (PolyMem SepLoad128 polyVecNat step_ldpQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (exec_simdAdd_4s exec_simdAnd_16b exec_simdCmltZero_8h exec_simdDup_4s exec_simdSqdmulh_4s exec_simdUshr_4s_4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (blk07_code_eq blk07_tree_size blkLib07 blkPC07 blkPl07 blkPlaceable07 blkTree07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Add (offSeg5Compress)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Simd (exec_umov_h6)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x9d34 → 0x9e0c]
end

namespace Simp
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg5SerLoop  : BitVec 64 := BitVec.ofNat 64 40308
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg5SerStore : BitVec 64 := BitVec.ofNat 64 40464
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg5Tail     : BitVec 64 := BitVec.ofNat 64 40660

@[scoped simp, arm64_norm, wp_norm]
theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 7 sym

@[scoped simp, arm64_norm, wp_norm]
theorem exec_simdMovi_8h_31 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b10000#5 31#5 rd) s =
      (s.writeVReg128 rd (dup8x16 0x001f#16)).advancePC := rfl

@[scoped simp, arm64_norm, wp_norm]
theorem exec_simdBic_4s_31 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b00010#5 31#5 rd) s =
      (s.writeVReg128 rd (s.readVReg128 rd &&& 0xffffffe0ffffffe0ffffffe0ffffffe0#128)).advancePC := rfl
end Simp
export Simp (offSeg5SerLoop offSeg5SerStore offSeg5Tail exec_simdMovi_8h_31 exec_simdBic_4s_31)
open scoped Simp

private theorem writeV_adv_congr {s : State} {rd : BitVec 5} {a b : BitVec 128} (h : a = b) :
    (s.writeVReg128 rd a).advancePC = (s.writeVReg128 rd b).advancePC :=
  h ▸ rfl

private theorem getLsbD_mask32_128 (k : Nat) : (4294967295#128).getLsbD k = decide (k < 32) := by
  change (4294967295#128).toNat.testBit k = decide (k < 32)
  rw [show (4294967295#128).toNat = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]

private theorem mapLanes_32_getLsbD (v : BitVec 128) (f : BitVec 128 → BitVec 128) :
    ∀ (n b : Nat), b < 128 → (mapLanes 32 v f n).getLsbD b =
      if b < 32 * n then (f ((v.extractLsb' (32 * (b / 32)) 32).zeroExtend 128)).getLsbD (b % 32) else false
  | 0, b, _ => by simp [mapLanes]
  | n + 1, b, hb => by
    have ih := mapLanes_32_getLsbD v f n b hb
    simp only [mapLanes, BitVec.getLsbD_or, ih, BitVec.getLsbD_shiftLeft, hb, decide_true,
      Bool.true_and, BitVec.getLsbD_and, show laneMask 32 = 4294967295#128 from rfl]
    by_cases hbn : b < 32 * n
    · simp [hbn, show b < n * 32 by omega, show b < 32 * (n + 1) by omega]
    · by_cases hbn1 : b < 32 * (n + 1)
      · have hin : (v >>> (n * 32) &&& 4294967295#128) = (v.extractLsb' (32 * n) 32).zeroExtend 128 := by
          simpa [getSimdLane, lane32] using getSimdLane_32_eq v ⟨n, by omega⟩
        have hm' : (4294967295#128).getLsbD (b % 32) = true := by rw [getLsbD_mask32_128]; simp [show b % 32 < 32 by omega]
        simp [hbn, hbn1, show ¬ (b < n * 32) by omega, show b / 32 = n by omega, show b - n * 32 = b % 32 by omega, hm', hin]
      · simp [hbn, hbn1, show ¬ (b < n * 32) by omega, getLsbD_mask32_128, show ¬ (b - n * 32 < 32) by omega]

private theorem lane32_mapSimdLanes_32 (v : BitVec 128) (f : BitVec 128 → BitVec 128) (i : Fin 4) :
    lane32 (mapSimdLanes true 32 v f) i = (f ((lane32 v i).zeroExtend 128)).truncate 32 := by
  rw [mapSimdLanes_true_32]; apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hpos : 32 * i.val + b < 128 := by omega
  simp only [lane32, BitVec.getLsbD_extractLsb', BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hb,
    decide_true, Bool.true_and, mapLanes_32_getLsbD v f 4 _ hpos, hpos,
    show (32 * i.val + b) / 32 = i.val by omega, show (32 * i.val + b) % 32 = b by omega, ↓reduceIte]

namespace Simp
@[scoped simp, arm64_norm, wp_norm]
theorem exec_simdShl_4s_5 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0100#4 0b101#3 0b01010#5 rn rd) s =
      (s.writeVReg128 rd (pack4x32 fun k => lane32 (s.readVReg128 rn) k <<< 5)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_false, Bool.true_and, Bool.false_eq_true, decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_; change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane <<< 5) = _
  apply ext_lane32; intro i; rw [lane32_mapSimdLanes_32, lane32_pack4x32]; bv_bits

@[scoped simp, arm64_norm, wp_norm]
theorem exec_simdUshr_4s_11 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0110#4 0b101#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (pack4x32 fun k => lane32 (s.readVReg128 rn) k >>> 11)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.true_and, Bool.false_eq_true, decide_false, decide_true, ↓reduceIte, BitVec.reduceEq]
  refine writeV_adv_congr ?_; change mapSimdLanes true 32 (s.readVReg128 rn) (fun lane => lane >>> 11) = _
  apply ext_lane32; intro i; rw [lane32_mapSimdLanes_32, lane32_pack4x32]; bv_bits
end Simp
export Simp (exec_simdShl_4s_5 exec_simdUshr_4s_11)
open scoped Simp

theorem seg5_compress5_eq (vn : BitVec 128) :
    let u := simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn
    let evenIn := pack4x32 fun k => lane32 ((pack4x32 fun j => lane32 u j <<< 5) &&& (pack4x32 fun _ => 2097120#32)) k + 1664#32
    let oddIn := pack4x32 fun k => lane32 ((pack4x32 fun j => lane32 u j >>> 11) &&& 0xffffffe0ffffffe0ffffffe0ffffffe0#128) k + 1664#32
    let cMul := pack4x32 fun _ => 10321340#32
    let evenOut := pack4x32 fun k => lane32 (simdSqdmulh4s evenIn cMul) k >>> 4
    let oddOut := pack4x32 fun k => lane32 (simdSqdmulh4s oddIn cMul) k >>> 4
    (simdTrn1_8h evenOut oddOut &&& dup8x16 0x001f#16) = neonCompress8h 5 vn := by
  dsimp only; unfold neonCompress8h
  have hu : simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn = simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16) := by
    apply ext_lane16; intro i; rw [lane16_simdAdd8h, lane16_simdAdd8h, BitVec.add_comm]
  rw [hu]; set u := simdAdd8h vn (simdCmltZero8h vn &&& dup8x16 3329#16)
  have l32_and (a b : BitVec 128) (k : Fin 4) : lane32 (a &&& b) k = lane32 a k &&& lane32 b k := by
    apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [lane32, hr]
  have hm_ev (w : BitVec 32) : (w <<< 5) &&& 2097120#32 = (w <<< 5) &&& (0x0000ffff#32 <<< 5) := by bv_bits
  have hm_od (w : BitVec 32) : (w >>> 11) &&& 0xffffffe0#32 = (w >>> (16 - 5)) &&& (0x0000ffff#32 <<< 5) := by
    change (w >>> 11) &&& 0xffffffe0#32 = (w >>> 11) &&& (0x0000ffff#32 <<< 5); bv_bits
  have hev : (pack4x32 fun k => lane32 ((pack4x32 fun j => lane32 u j <<< 5) &&& (pack4x32 fun _ => 2097120#32)) k + 1664#32) =
      (pack4x32 fun k => ((lane32 u k <<< 5) &&& (0x0000ffff#32 <<< 5)) + 1664#32) := by
    apply ext_lane32; intro k; rw [lane32_pack4x32, lane32_pack4x32, l32_and, lane32_pack4x32, lane32_pack4x32, hm_ev, even_shl_extract32 (lane32 u k) 5 (by decide)]
  have hod : (pack4x32 fun k => lane32 ((pack4x32 fun j => lane32 u j >>> 11) &&& 0xffffffe0ffffffe0ffffffe0ffffffe0#128) k + 1664#32) =
      (pack4x32 fun k => ((lane32 u k >>> (16 - 5)) &&& (0x0000ffff#32 <<< 5)) + 1664#32) := by
    apply ext_lane32; intro k; rw [lane32_pack4x32, lane32_pack4x32, l32_and, lane32_pack4x32]
    have hc : lane32 0xffffffe0ffffffe0ffffffe0ffffffe0#128 k = 0xffffffe0#32 := by induction k using fin4_cases <;> rfl
    rw [hc, hm_od, odd_ushr_extract32 (lane32 u k) 5 (by decide) (by decide)]
  rw [hev, hod]; rfl

theorem lane16_neonCompress8h_5_mask (vn : BitVec 128) (j : Fin 8) :
    lane16 (neonCompress8h 5 vn) j &&& 0x001f#16 = lane16 (neonCompress8h 5 vn) j := by
  unfold neonCompress8h; dsimp only
  rw [lane16_and, lane16_dup8x16,
    show BitVec.ofNat 16 ((1 <<< 5) - 1) = 0x001f#16 from rfl,
    BitVec.and_assoc, BitVec.and_self]

theorem ser5_b0 (c0 c1 : BitVec 16) (h0 : c0 &&& 0x001f#16 = c0) (h1 : c1 &&& 0x001f#16 = c1) :
    ((c1.zeroExtend 32 <<< 5).zeroExtend 64 ||| c0.zeroExtend 64).zeroExtend 8 =
      ((c0 &&& 0x001f#16) ||| ((c1 &&& 0x001f#16) <<< 5)).truncate 8 := by rw [h0, h1]; bv_bits

theorem ser5_b1 (c1 c2 c3 : BitVec 16) (h1 : c1 &&& 0x001f#16 = c1) (h2 : c2 &&& 0x001f#16 = c2) :
    ((((c2.zeroExtend 32 <<< 10) ||| (c3.zeroExtend 32 <<< 15)) ||| (c1.zeroExtend 32 <<< 5)) >>> 8).truncate 8 =
      (((c1 &&& 0x001f#16) >>> 3) ||| ((c2 &&& 0x001f#16) <<< 2) ||| ((c3 &&& 0x001f#16) <<< 7)).truncate 8 := by
  rw [serialize5_byte1_llvm c1 c2 c3 h1 h2, h1, h2]

theorem ser5_b2 (c3 c4 : BitVec 16) (h3 : c3 &&& 0x001f#16 = c3) (h4 : c4 &&& 0x001f#16 = c4) :
    ((c4.zeroExtend 32 <<< 4) ||| (c3.zeroExtend 32 >>> 1)).truncate 8 =
      (((c3 &&& 0x001f#16) >>> 1) ||| ((c4 &&& 0x001f#16) <<< 4)).truncate 8 := by rw [h3, h4]; bv_bits

theorem ser5_b3 (c4 c5 c6 : BitVec 16)
    (h4 : c4 &&& 0x001f#16 = c4) (h5 : c5 &&& 0x001f#16 = c5) (h6 : c6 &&& 0x001f#16 = c6) :
    (((c6.zeroExtend 32 <<< 6) ||| (c4.zeroExtend 32 >>> 4)) ||| (c5.zeroExtend 32 <<< 1)).truncate 8 =
      (((c4 &&& 0x001f#16) >>> 4) ||| ((c5 &&& 0x001f#16) <<< 1) ||| ((c6 &&& 0x001f#16) <<< 6)).truncate 8 := by
  rw [h4, h5, h6]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi32 : 4 + i < 32 := by omega
  simp [hi, hi32, Bool.or_comm, Bool.or_left_comm]

theorem ser5_b4 (evenOut oddOut vMask : BitVec 128)
    (hv : vMask = simdTrn1_8h evenOut oddOut &&& dup8x16 0x001f#16) :
    (((lane16 oddOut 6).zeroExtend 32 <<< 3) ||| ((lane16 vMask 6).zeroExtend 32 >>> 2)).truncate 8 =
      (((lane16 vMask 6 &&& 0x001f#16) >>> 2) ||| ((lane16 vMask 7 &&& 0x001f#16) <<< 3)).truncate 8 := by
  have hc7 : lane16 vMask 7 &&& 0x001f#16 = lane16 oddOut 6 &&& 0x001f#16 := by
    rw [hv, lane16_and, lane16_dup8x16, BitVec.and_assoc, BitVec.and_self, lane16_simdTrn1_8h]
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

namespace Simp
@[scoped simp] theorem neonCompressSerialize5Poly_length (re : Poly16) :
    (neonCompressSerialize5Poly re).length = 160 := by
  have hr : List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
  unfold neonCompressSerialize5Poly; rw [hr]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.length_append, List.length_nil, neonSerialize5Bytes_length]
end Simp
export Simp (neonCompressSerialize5Poly_length)
open scoped Simp

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

attribute [local irreducible]
  blkPC07 polyVecNat dup8x16 lane16 lane32 pack4x32
  simdAdd8h simdCmltZero8h simdSqdmulh4s simdTrn1_8h neonCompress8h

namespace Simp
@[scoped simp, arm64_norm, wp_norm] theorem readReg64_orFpsr' (s : State) (fl : BitVec 32) (r : Reg) : (s.orFpsr fl).readReg64 r = s.readReg64 r := State.readReg64_orFpsr s fl r
@[scoped simp, arm64_norm, wp_norm] theorem readVReg128_orFpsr' (s : State) (fl : BitVec 32) (r : BitVec 5) : (s.orFpsr fl).readVReg128 r = s.readVReg128 r := State.readVReg128_orFpsr s fl r
@[scoped simp, arm64_norm, wp_norm] theorem status_orFpsr' (s : State) (fl : BitVec 32) : (s.orFpsr fl).status = s.status := by cases s; rfl
@[scoped simp, arm64_norm, wp_norm] theorem pc_orFpsr' (s : State) (fl : BitVec 32) : (s.orFpsr fl).pc = s.pc := by cases s; rfl
@[scoped simp, arm64_norm, wp_norm] theorem sp_orFpsr' (s : State) (fl : BitVec 32) : (s.orFpsr fl).sp = s.sp := by cases s; rfl
@[scoped simp, arm64_norm, wp_norm] theorem spAligned_orFpsr' (s : State) (fl : BitVec 32) : (s.orFpsr fl).spAligned = s.spAligned := by cases s; rfl
@[scoped simp, arm64_norm, wp_norm] theorem pstate_orFpsr' (s : State) (fl : BitVec 32) : (s.orFpsr fl).pstate = s.pstate := by cases s; rfl
@[scoped simp, arm64_norm, wp_norm] theorem mem_orFpsr' (s : State) (fl : BitVec 32) : (s.orFpsr fl).mem = s.mem := by cases s; rfl
@[scoped simp, arm64_norm, wp_norm] theorem sp_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) : (s.writeVReg128 v w).sp = s.sp := rfl
@[scoped simp, arm64_norm, wp_norm] theorem spAligned_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) : (s.writeVReg128 v w).spAligned = s.spAligned := rfl
@[scoped simp, arm64_norm, wp_norm] theorem pstate_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) : (s.writeVReg128 v w).pstate = s.pstate := rfl
@[scoped simp, arm64_norm, wp_norm] theorem readReg64_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) (r : Reg) : (s.writeVReg128 v w).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[scoped simp, arm64_norm, wp_norm] theorem spAligned_writeReg64_gpr' (s : State) (i : BitVec 5) (w : BitVec 64) : (s.writeReg64 (.gpr i) w).spAligned = s.spAligned := by cases s; rfl
@[scoped simp, arm64_norm, wp_norm] theorem spAligned_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).spAligned = s.spAligned := by cases s; rfl
@[scoped simp, arm64_norm, wp_norm] theorem spAligned_setPState' (s : State) (ps : PState) : (s.setPState ps).spAligned = s.spAligned := by cases s; rfl
@[scoped simp, arm64_norm, wp_norm] theorem spAligned_setMem' (s : State) (m : Memory) : (s.setMem m).spAligned = s.spAligned := by cases s; rfl
@[scoped simp, arm64_norm, wp_norm] theorem readReg64_setPC' (s : State) (pc : BitVec 64) (r : Reg) : (s.setPC pc).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[scoped simp, arm64_norm, wp_norm] theorem readReg64_setMem' (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[scoped simp, arm64_norm, wp_norm] theorem readVReg128_setMem' (s : State) (m : Memory) (v : BitVec 5) : (s.setMem m).readVReg128 v = s.readVReg128 v := rfl
end Simp
export Simp (readReg64_orFpsr' readVReg128_orFpsr' status_orFpsr' pc_orFpsr' sp_orFpsr'
  spAligned_orFpsr' pstate_orFpsr' mem_orFpsr' sp_writeVReg128' spAligned_writeVReg128'
  pstate_writeVReg128' readReg64_writeVReg128' spAligned_writeReg64_gpr' spAligned_setPC'
  spAligned_setPState' spAligned_setMem' readReg64_setPC' readReg64_setMem' readVReg128_setMem')
open scoped Simp

attribute [local wp_norm ↓ high]
  exec_simdMovi_8h_31 exec_simdBic_4s_31 exec_simdShl_4s_5 exec_simdUshr_4s_11
  exec_umov_h6
  exec_simdAdd_4s exec_simdAnd_16b exec_simdDup_4s exec_simdCmltZero_8h
  exec_simdUshr_4s_4 exec_simdSqdmulh_4s
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdTrn1_8h

@[expose] def c31Vec       : BitVec 128 := dup8x16 0x001f#16
@[expose] def c3329Vec     : BitVec 128 := dup8x16 3329#16
@[expose] def c2097120Vec  : BitVec 128 := pack4x32 fun _ => 2097120#32
@[expose] def c1664Vec     : BitVec 128 := pack4x32 fun _ => 1664#32
@[expose] def c10321340Vec : BitVec 128 := pack4x32 fun _ => 10321340#32

theorem seg5_ser_header [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (P : SepProp)
    (hpc : s.pc = b + offSeg5Compress) (hrun : s.status = .Running) (hsp : s.sp = sp) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5SerLoop) s P
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = s.spAligned ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 .x8 = sp + 30912#64 ∧ sm.readReg64 .x9 = 1408#64 ∧
        sm.readReg64 .x10 = sp + 23104#64 ∧
        sm.readVReg128 0#5 = c31Vec ∧ sm.readVReg128 1#5 = c3329Vec ∧
        sm.readVReg128 2#5 = c2097120Vec ∧ sm.readVReg128 3#5 = c1664Vec ∧
        sm.readVReg128 4#5 = c10321340Vec ∧ Pm = P) := by
  subst hbase
  have hpc' : s.pc = blkPl07.base + BitVec.ofNat 64 40244 := hpc
  wp_steps 16
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp, by simp,
      by simp, by simp, by simp,
      by simp [c31Vec], by simp [c3329Vec], by simp [c2097120Vec],
      by simp [c1664Vec], by simp [c10321340Vec], rfl⟩

private theorem sepWP_cut {prog : Program} {t : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (Q : State → Prop) (hQ : Q s)
    (hk : ∀ s1, Q s1 → SepWP prog t s1 P post) : SepWP prog t s P post := hk s hQ

set_option maxRecDepth 8000 in
private theorem seg5_inner_simd_ushr [MlKemPlacement] (sn : State) (P : SepProp)
    (q0 q1 q2 q3 : BitVec 128)
    (hpc : sn.pc = blkPl07.base + BitVec.ofNat 64 40416) (hrun : sn.status = .Running)
    (hv7 : sn.readVReg128 7#5 = q0) (hv5 : sn.readVReg128 5#5 = q1)
    (hv16 : sn.readVReg128 16#5 = q2) (hv6 : sn.readVReg128 6#5 = q3)
    (hv0 : sn.readVReg128 0#5 = c31Vec) (hv1 : sn.readVReg128 1#5 = c3329Vec)
    (hv2 : sn.readVReg128 2#5 = c2097120Vec) (hv3 : sn.readVReg128 3#5 = c1664Vec)
    (hv4 : sn.readVReg128 4#5 = c10321340Vec) :
    SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + offSeg5SerStore) sn P
      (fun s1 P1 =>
        let evOut0 := pack4x32 fun k => lane32 q0 k >>> 4
        let odOut0 := pack4x32 fun k => lane32 q1 k >>> 4
        let evOut1 := pack4x32 fun k => lane32 q2 k >>> 4
        let odOut1 := pack4x32 fun k => lane32 q3 k >>> 4
        s1.sp = sn.sp ∧ s1.spAligned = sn.spAligned ∧ s1.pstate = sn.pstate ∧
        (∀ r : Reg, r ≠ .x12 → r ≠ .x13 → s1.readReg64 r = sn.readReg64 r) ∧
        s1.readReg64 .x12 = (((lane16 odOut0 6).zeroExtend 32) <<< 3).zeroExtend 64 ∧
        s1.readReg64 .x13 = (((lane16 odOut1 6).zeroExtend 32) <<< 3).zeroExtend 64 ∧
        s1.readVReg128 5#5 = (simdTrn1_8h evOut0 odOut0 &&& dup8x16 0x001f#16) ∧
        s1.readVReg128 6#5 = (simdTrn1_8h evOut1 odOut1 &&& dup8x16 0x001f#16) ∧
        s1.readVReg128 0#5 = c31Vec ∧ s1.readVReg128 1#5 = c3329Vec ∧
        s1.readVReg128 2#5 = c2097120Vec ∧ s1.readVReg128 3#5 = c1664Vec ∧
        s1.readVReg128 4#5 = c10321340Vec ∧ P1 = P) := by
  wp_steps 12
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp, by simp, fun r h12 h13 => ?_,
      by simp, by simp, by simp [c31Vec], by simp [c31Vec],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], rfl⟩
  have hne12 : r ≠ .gpr 12#5 := h12; have hne13 : r ≠ .gpr 13#5 := h13
  simp only [arm64_norm, hne12, hne13, ite_self]

@[expose] def compress5EvOut (vn : BitVec 128) : BitVec 128 :=
  let u := simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn
  let evenIn := pack4x32 fun k => lane32 ((pack4x32 fun j => lane32 u j <<< 5) &&& (pack4x32 fun _ => 2097120#32)) k + 1664#32
  pack4x32 fun k => lane32 (simdSqdmulh4s evenIn (pack4x32 fun _ => 10321340#32)) k >>> 4

@[expose] def compress5OdOut (vn : BitVec 128) : BitVec 128 :=
  let u := simdAdd8h (simdCmltZero8h vn &&& dup8x16 3329#16) vn
  let oddIn := pack4x32 fun k => lane32 ((pack4x32 fun j => lane32 u j >>> 11) &&& 0xffffffe0ffffffe0ffffffe0ffffffe0#128) k + 1664#32
  pack4x32 fun k => lane32 (simdSqdmulh4s oddIn (pack4x32 fun _ => 10321340#32)) k >>> 4

theorem compress5_trn1_eq (vn : BitVec 128) :
    (simdTrn1_8h (compress5EvOut vn) (compress5OdOut vn) &&& dup8x16 0x001f#16) = neonCompress8h 5 vn :=
  seg5_compress5_eq vn

set_option maxRecDepth 8000 in
private theorem seg5_inner_simd_mul [MlKemPlacement] (sm : State) (P : SepProp)
    (ev0 od0 ev1 od1 : BitVec 128)
    (hpc : sm.pc = blkPl07.base + BitVec.ofNat 64 40400) (hrun : sm.status = .Running)
    (hv7 : sm.readVReg128 7#5 = ev0) (hv5 : sm.readVReg128 5#5 = od0)
    (hv16 : sm.readVReg128 16#5 = ev1) (hv6 : sm.readVReg128 6#5 = od1)
    (hv0 : sm.readVReg128 0#5 = c31Vec) (hv1 : sm.readVReg128 1#5 = c3329Vec)
    (hv2 : sm.readVReg128 2#5 = c2097120Vec) (hv3 : sm.readVReg128 3#5 = c1664Vec)
    (hv4 : sm.readVReg128 4#5 = c10321340Vec) :
    SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + offSeg5SerStore) sm P
      (fun s1 P1 =>
        let evOut0 := pack4x32 fun k => lane32 (simdSqdmulh4s ev0 c10321340Vec) k >>> 4
        let odOut0 := pack4x32 fun k => lane32 (simdSqdmulh4s od0 c10321340Vec) k >>> 4
        let evOut1 := pack4x32 fun k => lane32 (simdSqdmulh4s ev1 c10321340Vec) k >>> 4
        let odOut1 := pack4x32 fun k => lane32 (simdSqdmulh4s od1 c10321340Vec) k >>> 4
        s1.sp = sm.sp ∧ s1.spAligned = sm.spAligned ∧ s1.pstate = sm.pstate ∧
        (∀ r : Reg, r ≠ .x12 → r ≠ .x13 → s1.readReg64 r = sm.readReg64 r) ∧
        s1.readReg64 .x12 = (((lane16 odOut0 6).zeroExtend 32) <<< 3).zeroExtend 64 ∧
        s1.readReg64 .x13 = (((lane16 odOut1 6).zeroExtend 32) <<< 3).zeroExtend 64 ∧
        s1.readVReg128 5#5 = (simdTrn1_8h evOut0 odOut0 &&& dup8x16 0x001f#16) ∧
        s1.readVReg128 6#5 = (simdTrn1_8h evOut1 odOut1 &&& dup8x16 0x001f#16) ∧
        s1.readVReg128 0#5 = c31Vec ∧ s1.readVReg128 1#5 = c3329Vec ∧
        s1.readVReg128 2#5 = c2097120Vec ∧ s1.readVReg128 3#5 = c1664Vec ∧
        s1.readVReg128 4#5 = c10321340Vec ∧ P1 = P) := by
  wp_steps 4
  refine SepWP.mono (seg5_inner_simd_ushr _ P
    (simdSqdmulh4s ev0 c10321340Vec) (simdSqdmulh4s od0 c10321340Vec)
    (simdSqdmulh4s ev1 c10321340Vec) (simdSqdmulh4s od1 c10321340Vec)
    (by wp_norm_lhs) (by simp [hrun]) (by simp) (by simp) (by simp) (by simp)
    (by simp [hv0]) (by simp [hv1]) (by simp [hv2]) (by simp [hv3]) (by simp [hv4])) ?_
  rintro s1 P1 _ _ ⟨hsp1, hspA1, hpst1, hregs1, hx12_1, hx13_1, hv5_1, hv6_1,
    hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, hP1⟩
  exact ⟨hsp1.trans (by simp), hspA1.trans (by simp), hpst1.trans (by simp),
    fun r h12 h13 => (hregs1 r h12 h13).trans (by simp),
    hx12_1, hx13_1, hv5_1, hv6_1, hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, hP1⟩

private theorem lane32_c1664Vec_add (x : BitVec 128) :
    (pack4x32 fun k => lane32 x k + lane32 c1664Vec k) =
      (pack4x32 fun k => lane32 x k + 1664#32) := by
  dsimp only [c1664Vec]
  simp only [lane32_pack4x32]

set_option maxRecDepth 8000 in
private theorem seg5_inner_simd_mid [MlKemPlacement] (sb : State) (P : SepProp)
    (a0 a1 : BitVec 128)
    (hpc : sb.pc = blkPl07.base + BitVec.ofNat 64 40352) (hrun : sb.status = .Running)
    (hv5 : sb.readVReg128 5#5 = a0) (hv6 : sb.readVReg128 6#5 = a1)
    (hv0 : sb.readVReg128 0#5 = c31Vec) (hv1 : sb.readVReg128 1#5 = c3329Vec)
    (hv2 : sb.readVReg128 2#5 = c2097120Vec) (hv3 : sb.readVReg128 3#5 = c1664Vec)
    (hv4 : sb.readVReg128 4#5 = c10321340Vec) :
    SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + offSeg5SerStore) sb P
      (fun s1 P1 =>
        let evIn0 := pack4x32 fun k =>
          lane32 ((pack4x32 fun j => lane32 a0 j <<< 5) &&& c2097120Vec) k + 1664#32
        let odIn0 := pack4x32 fun k =>
          lane32 ((pack4x32 fun j => lane32 a0 j >>> 11) &&&
            0xffffffe0ffffffe0ffffffe0ffffffe0#128) k + 1664#32
        let evIn1 := pack4x32 fun k =>
          lane32 ((pack4x32 fun j => lane32 a1 j <<< 5) &&& c2097120Vec) k + 1664#32
        let odIn1 := pack4x32 fun k =>
          lane32 ((pack4x32 fun j => lane32 a1 j >>> 11) &&&
            0xffffffe0ffffffe0ffffffe0ffffffe0#128) k + 1664#32
        let evOut0 := pack4x32 fun k => lane32 (simdSqdmulh4s evIn0 c10321340Vec) k >>> 4
        let odOut0 := pack4x32 fun k => lane32 (simdSqdmulh4s odIn0 c10321340Vec) k >>> 4
        let evOut1 := pack4x32 fun k => lane32 (simdSqdmulh4s evIn1 c10321340Vec) k >>> 4
        let odOut1 := pack4x32 fun k => lane32 (simdSqdmulh4s odIn1 c10321340Vec) k >>> 4
        s1.sp = sb.sp ∧ s1.spAligned = sb.spAligned ∧ s1.pstate = sb.pstate ∧
        (∀ r : Reg, r ≠ .x12 → r ≠ .x13 → s1.readReg64 r = sb.readReg64 r) ∧
        s1.readReg64 .x12 = (((lane16 odOut0 6).zeroExtend 32) <<< 3).zeroExtend 64 ∧
        s1.readReg64 .x13 = (((lane16 odOut1 6).zeroExtend 32) <<< 3).zeroExtend 64 ∧
        s1.readVReg128 5#5 = (simdTrn1_8h evOut0 odOut0 &&& dup8x16 0x001f#16) ∧
        s1.readVReg128 6#5 = (simdTrn1_8h evOut1 odOut1 &&& dup8x16 0x001f#16) ∧
        s1.readVReg128 0#5 = c31Vec ∧ s1.readVReg128 1#5 = c3329Vec ∧
        s1.readVReg128 2#5 = c2097120Vec ∧ s1.readVReg128 3#5 = c1664Vec ∧
        s1.readVReg128 4#5 = c10321340Vec ∧ P1 = P) := by
  wp_steps 4
  refine sepWP_cut (fun sc => sc.pc = blkPl07.base + BitVec.ofNat 64 40368 ∧ sc.status = .Running ∧
    sc.sp = sb.sp ∧ sc.spAligned = sb.spAligned ∧ sc.pstate = sb.pstate ∧
    (∀ r : Reg, sc.readReg64 r = sb.readReg64 r) ∧
    sc.readVReg128 7#5 = (pack4x32 fun j => lane32 a0 j <<< 5) ∧
    sc.readVReg128 5#5 = (pack4x32 fun j => lane32 a0 j >>> 11) ∧
    sc.readVReg128 16#5 = (pack4x32 fun j => lane32 a1 j <<< 5) ∧
    sc.readVReg128 6#5 = (pack4x32 fun j => lane32 a1 j >>> 11) ∧
    sc.readVReg128 0#5 = c31Vec ∧ sc.readVReg128 1#5 = c3329Vec ∧
    sc.readVReg128 2#5 = c2097120Vec ∧ sc.readVReg128 3#5 = c1664Vec ∧
    sc.readVReg128 4#5 = c10321340Vec)
    ⟨by wp_norm_lhs, by simp [hrun], by simp, by simp, by simp, fun _ => by simp,
      by simp, by simp, by simp, by simp,
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4]⟩ ?_
  rintro sc ⟨hpc_c, hrun_c, hsp_c, hspA_c, hpst_c, hregs_c,
    hv7_c, hv5_c, hv16_c, hv6_c, hv0_c, hv1_c, hv2_c, hv3_c, hv4_c⟩
  wp_steps 8
  let evIn0 := pack4x32 fun k => lane32 ((pack4x32 fun j => lane32 a0 j <<< 5) &&& c2097120Vec) k + 1664#32
  let odIn0 := pack4x32 fun k => lane32 ((pack4x32 fun j => lane32 a0 j >>> 11) &&& 0xffffffe0ffffffe0ffffffe0ffffffe0#128) k + 1664#32
  let evIn1 := pack4x32 fun k => lane32 ((pack4x32 fun j => lane32 a1 j <<< 5) &&& c2097120Vec) k + 1664#32
  let odIn1 := pack4x32 fun k => lane32 ((pack4x32 fun j => lane32 a1 j >>> 11) &&& 0xffffffe0ffffffe0ffffffe0ffffffe0#128) k + 1664#32
  refine SepWP.mono (seg5_inner_simd_mul _ P evIn0 odIn0 evIn1 odIn1
    (by wp_norm_lhs) (by simp [hrun_c])
    (by dsimp only [evIn0]; simp only [wp_norm, arm64_norm]; exact lane32_c1664Vec_add _)
    (by dsimp only [odIn0]; simp only [wp_norm, arm64_norm]; exact lane32_c1664Vec_add _)
    (by dsimp only [evIn1]; simp only [wp_norm, arm64_norm]; exact lane32_c1664Vec_add _)
    (by dsimp only [odIn1]; simp only [wp_norm, arm64_norm]; exact lane32_c1664Vec_add _)
    (by simp [hv0_c]) (by simp [hv1_c]) (by simp [hv2_c]) (by simp [hv3_c]) (by simp [hv4_c])) ?_
  rintro s1 P1 _ _ ⟨hsp1, hspA1, hpst1, hregs1, hx12_1, hx13_1, hv5_1, hv6_1,
    hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, hP1⟩
  exact ⟨hsp1.trans (by simp [hsp_c]), hspA1.trans (by simp [hspA_c]),
    hpst1.trans (by simp [hpst_c]),
    fun r h12 h13 => (hregs1 r h12 h13).trans (by simp [hregs_c r]),
    hx12_1, hx13_1, hv5_1, hv6_1, hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, hP1⟩

private theorem seg5_inner_simd_prep [MlKemPlacement] (sa : State) (P : SepProp)
    (v0_in v1_in : BitVec 128)
    (hpc : sa.pc = blkPl07.base + BitVec.ofNat 64 40328) (hrun : sa.status = .Running)
    (hv5 : sa.readVReg128 5#5 = v0_in) (hv6 : sa.readVReg128 6#5 = v1_in)
    (hv0 : sa.readVReg128 0#5 = c31Vec) (hv1 : sa.readVReg128 1#5 = c3329Vec)
    (hv2 : sa.readVReg128 2#5 = c2097120Vec) (hv3 : sa.readVReg128 3#5 = c1664Vec)
    (hv4 : sa.readVReg128 4#5 = c10321340Vec) :
    SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + offSeg5SerStore) sa P
      (fun s1 P1 =>
        s1.sp = sa.sp ∧ s1.spAligned = sa.spAligned ∧ s1.pstate = sa.pstate ∧
        (∀ r : Reg, r ≠ .x12 → r ≠ .x13 → s1.readReg64 r = sa.readReg64 r) ∧
        s1.readReg64 .x12 = (((lane16 (compress5OdOut v0_in) 6).zeroExtend 32) <<< 3).zeroExtend 64 ∧
        s1.readReg64 .x13 = (((lane16 (compress5OdOut v1_in) 6).zeroExtend 32) <<< 3).zeroExtend 64 ∧
        s1.readVReg128 5#5 = neonCompress8h 5 v0_in ∧
        s1.readVReg128 6#5 = neonCompress8h 5 v1_in ∧
        s1.readVReg128 0#5 = c31Vec ∧ s1.readVReg128 1#5 = c3329Vec ∧
        s1.readVReg128 2#5 = c2097120Vec ∧ s1.readVReg128 3#5 = c1664Vec ∧
        s1.readVReg128 4#5 = c10321340Vec ∧ P1 = P) := by
  wp_steps 6
  refine SepWP.mono (seg5_inner_simd_mid _ P
    (simdAdd8h (simdCmltZero8h v0_in &&& c3329Vec) v0_in)
    (simdAdd8h (simdCmltZero8h v1_in &&& c3329Vec) v1_in)
    (by wp_norm_lhs) (by simp [hrun]) (by simp) (by simp)
    (by simp [hv0]) (by simp [hv1]) (by simp [hv2]) (by simp [hv3]) (by simp [hv4])) ?_
  rintro s1 P1 _ _ ⟨hsp1, hspA1, hpst1, hregs1, hx12_1, hx13_1, hv5_1, hv6_1,
    hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, hP1⟩
  exact ⟨hsp1.trans (by simp), hspA1.trans (by simp), hpst1.trans (by simp),
    fun r h12 h13 => (hregs1 r h12 h13).trans (by simp),
    hx12_1, hx13_1,
    hv5_1.trans (compress5_trn1_eq v0_in), hv6_1.trans (compress5_trn1_eq v1_in),
    hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, hP1⟩

theorem seg5_inner_simd [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (v : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5SerLoop) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = sp + BitVec.ofNat 64 (30912 + 32 * c))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (1408 + 10 * c))
    (hx10 : s.readReg64 .x10 = sp + 23104#64)
    (hv0 : s.readVReg128 0#5 = c31Vec) (hv1 : s.readVReg128 1#5 = c3329Vec)
    (hv2 : s.readVReg128 2#5 = c2097120Vec) (hv3 : s.readVReg128 3#5 = c1664Vec)
    (hv4 : s.readVReg128 4#5 = c10321340Vec) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5SerStore) s
      (PolyMem (sp + 30896#64) (polyVecNat v) ∗ Rest)
      (fun s1 P1 =>
        let vn0 := polyVecNat v (2 * c)
        let vn1 := polyVecNat v (2 * c + 1)
        s1.sp = sp ∧ s1.spAligned = s.spAligned ∧
        s1.pstate = subsPState64 (BitVec.ofNat 64 (1408 + 10 * (c + 1))) 1568#64 ∧
        s1.readReg64 .x8 = sp + BitVec.ofNat 64 (30912 + 32 * (c + 1)) ∧
        s1.readReg64 .x9 = BitVec.ofNat 64 (1408 + 10 * (c + 1)) ∧
        s1.readReg64 .x10 = sp + 23104#64 ∧
        s1.readReg64 .x11 = sp + BitVec.ofNat 64 (24512 + 10 * c) ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readReg64 .x12 = (((lane16 (compress5OdOut vn0) 6).zeroExtend 32) <<< 3).zeroExtend 64 ∧
        s1.readReg64 .x13 = (((lane16 (compress5OdOut vn1) 6).zeroExtend 32) <<< 3).zeroExtend 64 ∧
        s1.readVReg128 5#5 = neonCompress8h 5 vn0 ∧
        s1.readVReg128 6#5 = neonCompress8h 5 vn1 ∧
        s1.readVReg128 0#5 = c31Vec ∧ s1.readVReg128 1#5 = c3329Vec ∧
        s1.readVReg128 2#5 = c2097120Vec ∧ s1.readVReg128 3#5 = c1664Vec ∧
        s1.readVReg128 4#5 = c10321340Vec ∧
        P1 = (PolyMem (sp + 30896#64) (polyVecNat v) ∗ Rest)) := by
  subst hbase
  have ha_ldp : (sp + 30896#64) + BitVec.ofNat 64 (16 * (2 * c)) =
      (sp + BitVec.ofNat 64 (30912 + 32 * c)) + 0xfffffffffffffff0#64 := by
    clear * - hc; bv_omega
  refine step_ldpQ128
    (s' := ((s.writeVReg128 5#5 (polyVecNat v (2 * c))).writeVReg128 6#5
      (polyVecNat v (2 * c + 1))).setPC (blkPl07.base + BitVec.ofNat 64 40312))
    (vt1 := 5#5) (vt2 := 6#5) (addr := .Offset .x8 0xfffffffffffffff0#64) (wb := none)
    hpc hrun (by simp only [arm64_norm]; rfl) rfl (by simp [evalAddrMode, hx8]) rfl
    (SepLoad128.left (SepLoad128.vecRange (by omega : 2 * c < 32) ha_ldp))
    (SepLoad128.left (SepLoad128.vecRange (by omega : 2 * c + 1 < 32)
      (by rw [← ha_ldp]; clear * -; bv_omega)))
    (by simp [applyWriteback, offSeg5SerLoop]) ?_
  wp_steps 4
  refine SepWP.mono
    (seg5_inner_simd_prep _ _ (polyVecNat v (2 * c)) (polyVecNat v (2 * c + 1))
      (by wp_norm_lhs) (by simp [hrun]) (by simp) (by simp)
      (by simp [hv0]) (by simp [hv1]) (by simp [hv2]) (by simp [hv3]) (by simp [hv4])) ?_
  rintro s1 P1 _ _ ⟨hsp1, hspA1, hpst1, hregs1, hx12_1, hx13_1, hv5_1, hv6_1,
    hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, hP1⟩
  have h10c : BitVec.ofNat 64 (1408 + 10 * c) + 10#64 = BitVec.ofNat 64 (1408 + 10 * (c + 1)) := by
    clear * - hc; bv_omega
  have h32c : sp + BitVec.ofNat 64 (30912 + 32 * c) + 32#64 =
      sp + BitVec.ofNat 64 (30912 + 32 * (c + 1)) := by
    clear * - hc; bv_omega
  have h11c : sp + 23104#64 + BitVec.ofNat 64 (1408 + 10 * c) =
      sp + BitVec.ofNat 64 (24512 + 10 * c) := by
    clear * - hc; bv_omega
  refine ⟨by simpa [hsp] using hsp1, by simpa using hspA1,
    by rw [hpst1]; simp only [arm64_norm]; exact congrArg (subsPState64 · 1568#64) h10c,
    by rw [hregs1 .x8 (by decide) (by decide)]; simp only [arm64_norm]; exact h32c,
    by rw [hregs1 .x9 (by decide) (by decide)]; simp only [arm64_norm]; exact h10c,
    by rw [hregs1 .x10 (by decide) (by decide)]; simp [hx10],
    by rw [hregs1 .x11 (by decide) (by decide)]; simp only [arm64_norm]; exact h11c,
    by rw [hregs1 .fp (by decide) (by decide)]; simp,
    hx12_1, hx13_1, hv5_1, hv6_1, hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, hP1⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5CompressSimd

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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure

/-!
# `kyber_decapsulate` (`B06`): `Seg3` Tail (`+0x3830 .. +0x39c4`)

Steps `B28 memcpy` (`+0x3830`), the 16-iteration `vPoly - inv1` Montgomery-normal and Barrett
subtraction loop (`+0x3834..+0x38d8`), the two `B28 memcpy` calls (`+0x38d8..+0x3918`), and the
16-iteration `compress_1 + serialize_1` loop (`+0x3918..+0x39c4`), producing `m'` (`32` B) at
`sp + 28368`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3Tail

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement fetch_rebase_ldst128Lo12_site mlkemCall_of_blockOk mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk cst16_4_vec cst16_5_vec mlkemData06Bytes_length mlkemData07Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 ext_lane16 getSimdLane_16_eq lane16 lane16_dup8x16 lane16_pack8x16 pack8x16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_and lane16_eor lane16_simdAdd8h lane16_simdMul8h lane16_simdMla8h
  lane16_simdSqdmulh8h lane16_simdSshr8h lane16_simdSub8h
  simdAdd8h simdCmltZero8h simdMla8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h simdUshl8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  barrett_mla_0xf2ff montgomery_precomp_mul neonBarrettReduce16_spec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (
  neonCompress1Lane16 neonCompress1Lane16_of_mod neonCompress1PreShift16 neonCompress1PreShift8h
  lane16_neonCompress1PreShift8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (
  byteEncodeChunk compressAndEncode_eq_flatten_chunks simdAddv8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow (
  neonSerialize1MsbHalf neonSerialize1Msb_bfi_eq
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse step_ldrQ128_ro step_strQ128_region
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 polyVecNat step_ldrQ128 step_ldpQ128 step_stpQ128 step_strQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_entails_memRegion
  vecRangeMem_eq_pointsToBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  Spill21 Spill21Mem SepLoad128.spill21
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops (Inv13Preserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  applySimdResult_ok exec_simdUshl_8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (
  exec_fmov_w_s exec_simdAnd_16b exec_simdCmltZero_8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  evalSimdModImmExt_bic_8h_13_lsl8
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem (
  Poly Poly16 compressAndEncode compressCoeff mlkemQ neonBarrettReduce16
  neonMontgomeryMul16 neonMontgomeryReduce16 polySub sqdmulh16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdMla_8h svc_simdMovi_8h_1024
  svc_simdMul_8h svc_simdMvni_8h_f2ff svc_simdSqdmulh_8h svc_simdSshr_8h_1
  svc_simdSshr_8h_11 svc_simdSub_8h
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x3918 → 0x39c4]
gen_placed_odd_sites blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x3924 → 0x3928]

@[simp, arm64_norm]
private theorem blkPC06_rebase_ldst128_cst16_4 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC06.rebase b X).fetch (b + BitVec.ofNat 64 14644) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 2)
        (.Offset (.gpr (BitVec.ofNat 5 11))
          (lo12Of (blkPl06.ρ "libcrux_ml_kem:.rodata.cst16.4")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib06) (prog := blkPC06) (pl := blkPl06)
    (b := b) (X := X) (off := 14644)
    (r := { off := 14644, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.4" })
    rfl blkPlaceable06 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 14644)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 3661) blk06_code_eq blk06_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC06_rebase_ldst128_cst16_5 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC06.rebase b X).fetch (b + BitVec.ofNat 64 14648) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 3)
        (.Offset (.gpr (BitVec.ofNat 5 12))
          (lo12Of (blkPl06.ρ "libcrux_ml_kem:.rodata.cst16.5")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib06) (prog := blkPC06) (pl := blkPl06)
    (b := b) (X := X) (off := 14648)
    (r := { off := 14648, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.5" })
    rfl blkPlaceable06 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 14648)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 3662) blk06_code_eq blk06_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

theorem blk28_memcpy_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk28_memcpy_ok

attribute [local irreducible] blkPC06

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem svc_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm]
private theorem exec_simdEor_16b {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b00#2 rm 0b00011#5 rn rd) s =
      (s.writeVReg128 rd (s.readVReg128 rn ^^^ s.readVReg128 rm)).advancePC := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdBic_8h_13_lsl8 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b10110#5 13#5 rd) s =
      (s.writeVReg128 rd (s.readVReg128 rd &&& dup8x16 0xf2ff#16)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.true_and, decide_true, ↓reduceIte,
    evalSimdModImmExt_bic_8h_13_lsl8, applySimdResult_ok]
  rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdUshl_8h_svc {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b01#2 rm 0b01000#5 rn rd) s =
      (s.writeVReg128 rd (simdUshl8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdUshl_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
private theorem exec_simdAddv_8h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdAcrossLanes true false 0b01#2 0b11011#5 rn rd) s =
      (s.writeVReg128 rd ((simdAddv8h (s.readVReg128 rn)).zeroExtend 128)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.false_and, Bool.not_false, Bool.true_and,
    Bool.false_or, Bool.or_true, Bool.false_eq_true, decide_false, decide_true, ↓reduceIte,
    BitVec.reduceEq, Std.Legacy.Range.forIn_eq_forIn_range',
    show (8 <<< (0b01#2).toNat) = 16 from rfl,
    show (1#128 <<< 16 - 1#128 : BitVec 128) = 65535#128 from rfl]
  congr 1; congr 1
  set vn := s.readVReg128 rn
  have h0 : (vn >>> 0) &&& 65535#128 = (lane16 vn 0).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 0
  have h1 : (vn >>> 16) &&& 65535#128 = (lane16 vn 1).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 1
  have h2 : (vn >>> 32) &&& 65535#128 = (lane16 vn 2).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 2
  have h3 : (vn >>> 48) &&& 65535#128 = (lane16 vn 3).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 3
  have h4 : (vn >>> 64) &&& 65535#128 = (lane16 vn 4).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 4
  have h5 : (vn >>> 80) &&& 65535#128 = (lane16 vn 5).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 5
  have h6 : (vn >>> 96) &&& 65535#128 = (lane16 vn 6).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 6
  have h7 : (vn >>> 112) &&& 65535#128 = (lane16 vn 7).zeroExtend 128 := by
    simpa [getSimdLane] using getSimdLane_16_eq vn 7
  change ((((((((0#128 + ((vn >>> 0) &&& 65535#128)) + ((vn >>> 16) &&& 65535#128)) +
      ((vn >>> 32) &&& 65535#128)) + ((vn >>> 48) &&& 65535#128)) +
      ((vn >>> 64) &&& 65535#128)) + ((vn >>> 80) &&& 65535#128)) +
      ((vn >>> 96) &&& 65535#128)) + ((vn >>> 112) &&& 65535#128)) &&& 65535#128 =
    (((lane16 vn 0 + lane16 vn 1) + (lane16 vn 2 + lane16 vn 3)) +
      ((lane16 vn 4 + lane16 vn 5) + (lane16 vn 6 + lane16 vn 7))).zeroExtend 128
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  set a0 := lane16 vn 0; set a1 := lane16 vn 1; set a2 := lane16 vn 2; set a3 := lane16 vn 3
  set a4 := lane16 vn 4; set a5 := lane16 vn 5; set a6 := lane16 vn 6; set a7 := lane16 vn 7
  bv_bits

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdMla_8h
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSshr_8h_11
  svc_simdMovi_8h_1024 svc_simdMvni_8h_f2ff svc_simdDup_8h_gpr
  exec_simdEor_16b exec_simdBic_8h_13_lsl8 exec_simdUshl_8h_svc exec_simdAddv_8h
  exec_simdCmltZero_8h exec_simdAnd_16b exec_fmov_w_s svc_simdMovi_2d_0

/-! ## 1. Pure `seg3SubPoly` (`vPoly - inv1` + Barrett) & `compress_1 + serialize_1` Identities -/

/-- Exact `w` polynomial computed in `B06 +0x3858..+0x38d8` (`vPoly - neonMontgomeryMul16 inv 1441`
    followed by `neonBarrettReduce16`). -/
@[expose] def seg3SubPoly (inv vPoly16 : Poly16) : Poly16 :=
  Array.ofFn (n := 256) fun ⟨i, _⟩ =>
    let normal := neonMontgomeryMul16 (inv.getD i 0#16) 1441#16
    neonBarrettReduce16 (vPoly16.getD i 0#16 - normal)

@[simp] theorem seg3SubPoly_size (inv vPoly16 : Poly16) :
    (seg3SubPoly inv vPoly16).size = 256 := by simp [seg3SubPoly]

theorem seg3SubLoop_vec_eq (inv vPoly16 : Poly16) (idx : Nat) (hidx : idx < 32)
    (commSum : Bool) :
    let qx := polyVecNat inv idx
    let qv := polyVecNat vPoly16 idx
    let negNormal := simdSub8h
      (simdSshr8h (simdSqdmulh8h (simdMul8h qx (dup8x16 55457#16)) (dup8x16 3329#16)) 1)
      (simdSshr8h (simdSqdmulh8h qx (dup8x16 1441#16)) 1)
    let diff := if commSum then simdAdd8h qv negNormal else simdAdd8h negNormal qv
    let quot := simdSshr8h (simdAdd8h (simdSqdmulh8h diff (dup8x16 20159#16)) (dup8x16 1024#16)) 11
    simdMla8h diff quot (dup8x16 0xf2ff#16) =
      polyVecNat (seg3SubPoly inv vPoly16) idx := by
  dsimp only
  apply ext_lane16; intro i
  have hi256 : 8 * idx + i.val < 256 := by omega
  have hmont (x : BitVec 16) :
      (sqdmulh16 (x * 55457#16) 3329#16).sshiftRight 1 -
        (sqdmulh16 x 1441#16).sshiftRight 1 =
      -(neonMontgomeryMul16 x 1441#16) := by
    unfold neonMontgomeryMul16 neonMontgomeryReduce16; dsimp only
    rw [montgomery_precomp_mul x 1441#16, show (1441#16 * 62209#16) = 55457#16 from rfl]
    bv_omega
  have hget : (seg3SubPoly inv vPoly16).getD (8 * idx + i.val) 0#16 =
      neonBarrettReduce16
        (vPoly16.getD (8 * idx + i.val) 0#16 -
          neonMontgomeryMul16 (inv.getD (8 * idx + i.val) 0#16) 1441#16) := by
    simp [seg3SubPoly, Array.getD, hi256]
  have hd0 (a b : BitVec 16) : -b + a = a - b := by bv_omega
  have hd1 (a b : BitVec 16) : a + -b = a - b := by bv_omega
  cases commSum
  · simp only [Bool.false_eq_true, ↓reduceIte, polyVecNat, lane16_pack8x16, lane16_simdMla8h,
      lane16_simdSshr8h, lane16_simdAdd8h, lane16_simdSqdmulh8h, lane16_simdSub8h,
      lane16_simdMul8h, lane16_dup8x16, hmont, hd0, hget]
    rw [barrett_mla_0xf2ff]; rfl
  · simp only [↓reduceIte, polyVecNat, lane16_pack8x16, lane16_simdMla8h,
      lane16_simdSshr8h, lane16_simdAdd8h, lane16_simdSqdmulh8h, lane16_simdSub8h,
      lane16_simdMul8h, lane16_dup8x16, hmont, hd1, hget]
    rw [barrett_mla_0xf2ff]; rfl

private theorem seg3SubPoly_compress1_eq {inv vPoly16 : Poly16} {vSpec invSpec : Poly}
    (hv_sz : vSpec.size = 256) (hinv_sz : invSpec.size = 256)
    (hv_bnd : ∀ i, i < 256 → -3329 ≤ (vPoly16.getD i 0#16).toInt ∧ (vPoly16.getD i 0#16).toInt < 3329)
    (hv_rep : ∀ i, i < 256 → (vPoly16.getD i 0#16).toInt % 3329 = (vSpec.getD i 0 : Int) % 3329)
    (hn_bnd : ∀ i, i < 256 →
      -2496 ≤ (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ∧
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ≤ 2496)
    (hn_rep : ∀ i, i < 256 →
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt % 3329 = (invSpec.getD i 0 : Int) % 3329)
    (i : Nat) (hi : i < 256) :
    neonCompress1Lane16 ((seg3SubPoly inv vPoly16).getD i 0#16) =
      BitVec.ofNat 16 ((polySub vSpec invSpec).getD i 0 |> compressCoeff 1) := by
  have hget : (seg3SubPoly inv vPoly16).getD i 0#16 =
      neonBarrettReduce16 (vPoly16.getD i 0#16 - neonMontgomeryMul16 (inv.getD i 0#16) 1441#16) := by
    simp [seg3SubPoly, Array.getD, hi]
  rw [hget]
  let x := vPoly16.getD i 0#16
  let y := neonMontgomeryMul16 (inv.getD i 0#16) 1441#16
  have hx := hv_bnd i hi
  have hy := hn_bnd i hi
  have hsub_int : (x - y).toInt = x.toInt - y.toInt :=
    LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith.toInt_sub_of_bounds
      (by dsimp only [x, y]; omega) (by dsimp only [x, y]; omega)
  obtain ⟨hb_lo, hb_hi, hb_mod⟩ := neonBarrettReduce16_spec (x - y)
  have hsub_spec : (polySub vSpec invSpec).getD i 0 =
      (vSpec.getD i 0 + mlkemQ - invSpec.getD i 0 % mlkemQ) % mlkemQ := by
    simp [polySub, Array.getD, hv_sz, hinv_sz, hi]
  have hmod : (neonBarrettReduce16 (x - y)).toInt % 3329 =
      ((polySub vSpec invSpec).getD i 0 : Int) % 3329 := by
    rw [hb_mod, hsub_int, hsub_spec]
    have hxr := hv_rep i hi
    have hyr := hn_rep i hi
    dsimp only [x, y, mlkemQ]
    have hvi : (invSpec.getD i 0 % 3329 : Nat) < 3329 := Nat.mod_lt _ (by decide)
    omega
  have hc := neonCompress1Lane16_of_mod (c := (polySub vSpec invSpec).getD i 0)
    (by omega) (by omega) hmod
  have hlt2 : compressCoeff 1 ((polySub vSpec invSpec).getD i 0) < 2 := by
    unfold compressCoeff; exact Nat.mod_lt _ (by decide)
  exact BitVec.eq_of_toNat_eq (by
    rw [hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])

private def serHalf1 (w : Poly16) (c : Nat) : BitVec 16 :=
  (evalBitfield .W32 .BFM
    ((neonSerialize1MsbHalf (neonCompress1PreShift8h (polyVecNat w (2 * c)))).zeroExtend 64)
    ((neonSerialize1MsbHalf (neonCompress1PreShift8h (polyVecNat w (2 * c + 1)))).zeroExtend 64)
    24 23).truncate 16

private def HalfRangeMem : Nat → BitVec 64 → (Nat → BitVec 16) → SepProp
  | 0, _, _ => emp
  | n + 1, ptr, h => (ptr ↦₁₆ h 0) ∗ HalfRangeMem n (ptr + 2#64) (fun i => h (i + 1))

private theorem halfRangeMem_congr {n : Nat} {ptr : BitVec 64} {f g : Nat → BitVec 16}
    (h : ∀ i, i < n → f i = g i) : HalfRangeMem n ptr f = HalfRangeMem n ptr g := by
  induction n generalizing ptr f g with
  | zero => rfl
  | succ n ih =>
    simp only [HalfRangeMem, h 0 (Nat.zero_lt_succ n),
      ih (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))]

private theorem SepStore16.halfRange {n c : Nat} {ea ptr : BitVec 64} {val : BitVec 16}
    {w : Nat → BitVec 16} (hc : c < n) (ha : ptr + BitVec.ofNat 64 (2 * c) = ea) :
    SepStore16 ea val (HalfRangeMem n ptr w) (HalfRangeMem n ptr (Function.update w c val)) := by
  induction n generalizing c ptr w with
  | zero => omega
  | succ n ih =>
    rcases c with _ | c
    · simp only [Nat.mul_zero, BitVec.add_zero] at ha
      have htail : HalfRangeMem n (ptr + 2#64) (fun i => Function.update w 0 val (i + 1)) =
          HalfRangeMem n (ptr + 2#64) (fun i => w (i + 1)) :=
        halfRangeMem_congr fun i _ => Function.update_of_ne (Nat.succ_ne_zero i) val w
      simp only [HalfRangeMem, Function.update_self, htail]; exact (SepStore16.here ha).left
    · have ha' : (ptr + 2#64) + BitVec.ofNat 64 (2 * c) = ea := by
        rw [← ha, BitVec.add_assoc]; congr 1
        rw [show 2 * (c + 1) = 2 + 2 * c by omega, BitVec.ofNat_add]
      have hhead : Function.update w (c + 1) val 0 = w 0 :=
        Function.update_of_ne (Nat.succ_ne_zero c).symm val w
      have htail : (fun i => Function.update w (c + 1) val (i + 1)) =
          Function.update (fun i => w (i + 1)) c val := by
        funext i; by_cases h : i = c
        · subst h; simp
        · simp [Function.update_of_ne h, Function.update_of_ne (show i + 1 ≠ c + 1 by omega)]
      simp only [HalfRangeMem, hhead, htail]; exact (ih (by omega) ha').right

private theorem halfRangeMem_eq_pointsToBytes (n : Nat) (ptr : BitVec 64) (w : Nat → BitVec 16) :
    HalfRangeMem n ptr w = (ptr ↦ₛ ((List.range n).map fun i => unpack16 (w i)).flatten) := by
  induction n generalizing ptr w with
  | zero => simp [HalfRangeMem, pointsToBytes_nil]
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [HalfRangeMem, List.map_cons, List.map_map, Function.comp_def, List.flatten_cons,
      ih (ptr + 2#64) (fun i => w (i + 1)), pointsTo16_eq_pointsToBytes]
    rw [pointsToBytes_append]
    simp [unpack16_length]

private theorem vec128Zero2_eq_halfRangeMem (ptr : BitVec 64) :
    LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.Vec128At ptr 0#128 ∗
      LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.Vec128At (ptr + 16#64) 0#128 =
      HalfRangeMem 16 ptr (fun _ => 0#16) := by
  have hrep : ((List.range 16).map fun (_ : Nat) => unpack16 0#16).flatten =
      (unpack64 0#64 ++ unpack64 0#64) ++ (unpack64 0#64 ++ unpack64 0#64) := by decide
  rw [halfRangeMem_eq_pointsToBytes, hrep, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.Vec128At,
    pointsTo64_eq_pointsToBytes]
  rw [show (0#128 : BitVec 128).extractLsb' 0 64 = 0#64 by decide,
    show (0#128 : BitVec 128).extractLsb' 64 64 = 0#64 by decide]
  simp [unpack64_length, show (ptr + 16#64) + 8#64 = ptr + 24#64 by bv_omega, sepConj_assoc]

private theorem halfRangeMem_serHalf1_eq {inv vPoly16 : Poly16} {vSpec invSpec : Poly}
    (hv_sz : vSpec.size = 256) (hinv_sz : invSpec.size = 256)
    (hv_bnd : ∀ i, i < 256 → -3329 ≤ (vPoly16.getD i 0#16).toInt ∧ (vPoly16.getD i 0#16).toInt < 3329)
    (hv_rep : ∀ i, i < 256 → (vPoly16.getD i 0#16).toInt % 3329 = (vSpec.getD i 0 : Int) % 3329)
    (hn_bnd : ∀ i, i < 256 →
      -2496 ≤ (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ∧
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ≤ 2496)
    (hn_rep : ∀ i, i < 256 →
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt % 3329 = (invSpec.getD i 0 : Int) % 3329)
    (ptr : BitVec 64) :
    HalfRangeMem 16 ptr (serHalf1 (seg3SubPoly inv vPoly16)) =
      (ptr ↦ₛ compressAndEncode 1 (polySub vSpec invSpec)) := by
  rw [halfRangeMem_eq_pointsToBytes,
    compressAndEncode_eq_flatten_chunks 1 (by decide) (polySub vSpec invSpec)]
  congr 1; congr 1
  apply List.map_congr_left; intro c hc
  have hc16 : c < 16 := List.mem_range.mp hc
  unfold serHalf1
  rw [neonSerialize1Msb_bfi_eq]
  unfold byteEncodeChunk
  congr 1
  refine Array.ext (by simp) fun j hj1 hj2 => ?_
  simp only [Array.size_ofFn] at hj1
  simp only [Array.getElem_ofFn, Nat.div_one, Nat.mod_one, Nat.shiftRight_zero]
  congr 2
  have hw_sz : (polySub vSpec invSpec).size = 256 := by simp [polySub, hv_sz, hinv_sz]
  have hmap_getD (k : Nat) (hk : k < 256) :
      ((polySub vSpec invSpec).map (compressCoeff 1)).getD k 0 =
        compressCoeff 1 ((polySub vSpec invSpec).getD k 0) := by
    simp [Array.getD, hw_sz, hk]
  by_cases hj8 : j < 8
  · simp only [hj8, lane16_neonCompress1PreShift8h]
    change neonCompress1Lane16 (lane16 (polyVecNat (seg3SubPoly inv vPoly16) (2 * c)) ⟨j, hj8⟩) = _
    rw [polyVecNat, lane16_pack8x16]
    dsimp only
    rw [show 8 * (2 * c) + j = 16 * c + j by omega,
      seg3SubPoly_compress1_eq hv_sz hinv_sz hv_bnd hv_rep hn_bnd hn_rep (16 * c + j) (by omega),
      hmap_getD (16 * c + j) (by omega)]
  · have hj16 : j - 8 < 8 := by omega
    simp only [hj8, hj16, lane16_neonCompress1PreShift8h]
    change neonCompress1Lane16 (lane16 (polyVecNat (seg3SubPoly inv vPoly16) (2 * c + 1)) ⟨j - 8, hj16⟩) = _
    rw [polyVecNat, lane16_pack8x16]
    dsimp only
    rw [show 8 * (2 * c + 1) + (j - 8) = 16 * c + j by omega,
      seg3SubPoly_compress1_eq hv_sz hinv_sz hv_bnd hv_rep hn_bnd hn_rep (16 * c + j) (by omega),
      hmap_getD (16 * c + j) (by omega)]

/-! ## 2. `compress_1 + serialize_1` Setup & Loop (`+0x3918 → +0x39c4`) -/

private theorem sepWP_cut {prog : Program} {t : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (Q : State → Prop) (hQ : Q s)
    (hk : ∀ s1, Q s1 → SepWP prog t s1 P post) : SepWP prog t s P post := hk s hQ

private theorem seg3_ser1_setup [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 s : State) (sp : BitVec 64) (v0 v1 : BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x3918#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = sp + 28368#64)
    (hx20 : s.readReg64 .x20 = sp + 14432#64)
    (hpres : Inv13Preserved s0 s) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x394c#64) s
      (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.Vec128At
          (sp + 28368#64) v0 ∗
        LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.Vec128At
          (sp + 28384#64) v1 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = sp + 14448#64 ∧
        sf.readReg64 .x19 = sp + 28368#64 ∧
        sf.readReg64 .x20 = sp + 14432#64 ∧
        sf.readVReg128 0#5 = dup8x16 1664#16 ∧
        sf.readVReg128 1#5 = dup8x16 0xfcc0#16 ∧
        sf.readVReg128 2#5 = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 ∧
        sf.readVReg128 3#5 = 0x00800040002000100008000400020001#128 ∧
        Inv13Preserved s0 sf ∧
        Pf = (HalfRangeMem 16 (sp + 28368#64) (fun _ => 0#16) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hpres with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  wp_steps
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro.cst16_4 mlkemData06Bytes_length cst16_4_vec (by wp_norm_lhs) ?_
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro.cst16_5 mlkemData07Bytes_length cst16_5_vec (by wp_norm_lhs) ?_
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 28384#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp] using hsp_chk)
    (by simp [evalAddrMode, hsp]) (by simp)
    (SepStore128.right (SepStore128.left (SepStore128.vec128At rfl)))
    (by wp_norm_lhs) ?_
  intro m1
  refine step_strQ128 (wb := none) (ea := sp + 28368#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp] using hsp_chk)
    (by simp [evalAddrMode, hsp]) (by simp)
    (SepStore128.left (SepStore128.vec128At rfl))
    (by wp_norm_lhs) ?_
  intro m2
  have hzero :
      LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.Vec128At
          (sp + 28368#64) 0#128 ∗
        LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.Vec128At
          (sp + 28384#64) 0#128 =
      HalfRangeMem 16 (sp + 28368#64) (fun _ => 0#16) := by
    simpa [show (sp + 28368#64) + 16#64 = sp + 28384#64 by bv_omega] using
      vec128Zero2_eq_halfRangeMem (sp + 28368#64)
  rw [← sepConj_assoc, hzero]
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp [hx19], by simp [hx20],
      by simp, by simp, by simp, by simp,
      ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
       by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩, rfl⟩

private theorem bfi_ser1_eq (lo hi : BitVec 16) :
    (lo &&& 255#16) ||| ((hi &&& 65535#16) <<< 8) =
    setWidth 16 (evalBitfield .W32 .BFM (setWidth 64 lo) (setWidth 64 hi) 24 23) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  unfold evalBitfield
  dsimp only [Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd]
  simp only [show (BitfieldOp.BFM == BitfieldOp.UBFM) = false from rfl,
    show (BitfieldOp.BFM == BitfieldOp.SBFM) = false from rfl,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, show ¬(23 ≥ 24) by decide,
    BitVec.truncate_eq_setWidth, BitVec.zeroExtend,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, hk, show k < 32 by omega, show k < 64 by omega, decide_true,
    Bool.true_and]
  have hm24 : ∀ i, i < 64 → (BitVec.ofNat 64 (Nat.shiftLeft 1 24 - 1)).getLsbD i = decide (i < 24) := by
    intro i hi64; revert i hi64; decide
  have hm8 : ∀ i, i < 16 → (255#16 : BitVec 16).getLsbD i = decide (i < 8) := by
    intro i hi16; revert i hi16; decide
  have hm16 : ∀ i, i < 16 → (65535#16 : BitVec 16).getLsbD i = decide (i < 16) := by
    intro i hi16; revert i hi16; decide
  by_cases hk8 : k < 8
  · rw [hm8 k hk]; simp [hk8]
  · rw [hm8 k hk, hm24 (k - 8) (by omega), hm16 (k - 8) (by omega)]
    simp [hk8, show k - 8 < 16 by omega, show k - 8 < 24 by omega,
      show k - 8 < 32 by omega, show k - 8 < 64 by omega]

private theorem step_bCond_taken {P : Program} {target_pc pc off dst : BitVec 64}
    {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.bCond c off))
    (hcond : ConditionHolds c s.pstate = true) (hdst : pc + off = dst)
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]
        simp [wp_norm, arm64_norm, hcond, hdst])
    rfl hnext

private theorem step_bCond_not_taken {P : Program} {target_pc pc off dst : BitVec 64}
    {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.bCond c off))
    (hcond : ConditionHolds c s.pstate = false) (hdst : pc + 4#64 = dst)
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]
        cases s; subst hpc; subst hdst
        simp [wp_norm, arm64_norm, hcond, State.advancePC, State.setPC])
    rfl hnext

attribute [local irreducible]
  polyVecNat dup8x16 simdAdd8h simdSub8h simdCmltZero8h simdUshl8h simdAddv8h

private theorem seg3_ser1_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp : BitVec 64) (w : Poly16) {r : Nat} (hr : r < 16)
    (h : Nat → BitVec 16) (Rest : SepProp)
    (hpc : s.pc = b + 0x394c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 r)
    (hx9 : s.readReg64 .x9 = sp + 14448#64 + BitVec.ofNat 64 (32 * r))
    (hx19 : s.readReg64 .x19 = sp + 28368#64)
    (hx20 : s.readReg64 .x20 = sp + 14432#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 1664#16)
    (hv1 : s.readVReg128 1#5 = dup8x16 0xfcc0#16)
    (hv2 : s.readVReg128 2#5 = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128)
    (hv3 : s.readVReg128 3#5 = 0x00800040002000100008000400020001#128)
    (hpres : Inv13Preserved s0 s) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + 0x394c#64 else b + 0x39c4#64) s
      (HalfRangeMem 16 (sp + 28368#64) h ∗ PolyMem (sp + 14432#64) (polyVecNat w) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (r + 1) ∧
        s'.readReg64 .x9 = sp + 14448#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x19 = sp + 28368#64 ∧
        s'.readReg64 .x20 = sp + 14432#64 ∧
        s'.readVReg128 0#5 = dup8x16 1664#16 ∧
        s'.readVReg128 1#5 = dup8x16 0xfcc0#16 ∧
        s'.readVReg128 2#5 = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 ∧
        s'.readVReg128 3#5 = 0x00800040002000100008000400020001#128 ∧
        Inv13Preserved s0 s' ∧
        P' = (HalfRangeMem 16 (sp + 28368#64) (Function.update h r (serHalf1 w r)) ∗
          PolyMem (sp + 14432#64) (polyVecNat w) ∗ Rest)) := by
  rcases hpres with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 14432#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 14432#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat w (2 * r)) (v2 := polyVecNat w (2 * r + 1))
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx9]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 27
  refine sepWP_cut (fun s1 =>
    s1.pc = b + 0x39bc#64 ∧ s1.status = .Running ∧
    s1.sp = sp ∧ s1.spAligned = true ∧
    s1.pstate = subsPState64 (BitVec.ofNat 64 r + 1#64) 16#64 ∧
    s1.readReg64 .x8 = BitVec.ofNat 64 r + 1#64 ∧
    s1.readReg64 .x9 = sp + 14448#64 + BitVec.ofNat 64 (32 * r) + 32#64 ∧
    s1.readReg64 .x10 = BitVec.ofNat 64 r ∧
    s1.readReg64 .x19 = sp + 28368#64 ∧
    s1.readReg64 .x20 = sp + 14432#64 ∧
    s1.readVReg128 0#5 = dup8x16 1664#16 ∧
    s1.readVReg128 1#5 = dup8x16 0xfcc0#16 ∧
    s1.readVReg128 2#5 = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 ∧
    s1.readVReg128 3#5 = 0x00800040002000100008000400020001#128 ∧
    Inv13Preserved s0 s1 ∧
    (s1.readReg32 .x11).truncate 16 = serHalf1 w r)
    ⟨by wp_norm_lhs, by simp [hrun], by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp, by simp, by simp, by simp,
      by simp [hx19], by simp [hx20],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3],
      ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
       by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩,
      by
        simp [State.readReg32,
          serHalf1, neonCompress1PreShift8h, neonSerialize1MsbHalf]
        exact bfi_ser1_eq _ _⟩ ?_
  clear hpc hrun hsp hspA hx8 hx9 hx19 hx20 hv0 hv1 hv2 hv3 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 pfp
  rintro s1 ⟨hpc, hrun, hsp, hspA, hpst, hx8, hx9, hx10, hx19, hx20, hv0, hv1, hv2, hv3, hpres1, hx11⟩
  rcases hpres1 with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  refine SepWP.step_str16 (s' := s1.setPC (b + 0x39c0#64))
    (wb := none) (ea := (sp + 28368#64) + BitVec.ofNat 64 (2 * r))
    (val := serHalf1 w r)
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx19, hx10]; clear * - hr; bv_omega)
    hx11
    (SepStore16.left (SepStore16.halfRange (n := 16) (c := r) hr rfl))
    (by simp [applyWriteback]) ?_
  intro m'
  by_cases hr15 : r < 15
  · simp only [hr15, ↓reduceIte]
    have hcond : ConditionHolds .NE ((s1.setPC (b + 0x39c0#64)).setMem m').pstate = true := by
      simp only [State.setMem, State.setPC, hpst]
      clear * - hr15
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r
      all_goals first | omega | simp [wp_norm, arm64_norm]
    refine step_bCond_taken (pc := b + 0x39c0#64) (dst := b + 0x394c#64)
      rfl (by simp [hrun]) (by wp_norm_lhs) hcond (by bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx8]; clear * - hr15; bv_omega,
        by simp [hx9]; clear * - hr15; bv_omega,
        by simp [hx19], by simp [hx20],
        by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3],
        ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
         by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩, rfl⟩
  · have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    have hcond : ConditionHolds .NE ((s1.setPC (b + 0x39c0#64)).setMem m').pstate = false := by
      simp [hpst, hr_eq, wp_norm, arm64_norm]
    refine step_bCond_not_taken (pc := b + 0x39c0#64) (dst := b + 0x39c4#64)
      rfl (by simp [hrun]) (by wp_norm_lhs) hcond (by bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx8, hr_eq], by simp [hx9, hr_eq],
        by simp [hx19], by simp [hx20],
        by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3],
        ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
         by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩, rfl⟩

private theorem seg3_ser1_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (s0 : State) (sp : BitVec 64) (w : Poly16) (Rest : SepProp) :
    ∀ (rem r : Nat), rem + r = 15 →
    ∀ (s : State) (h : Nat → BitVec 16),
      s.pc = b + 0x394c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = BitVec.ofNat 64 r →
      s.readReg64 .x9 = sp + 14448#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x19 = sp + 28368#64 → s.readReg64 .x20 = sp + 14432#64 →
      s.readVReg128 0#5 = dup8x16 1664#16 → s.readVReg128 1#5 = dup8x16 0xfcc0#16 →
      s.readVReg128 2#5 = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 →
      s.readVReg128 3#5 = 0x00800040002000100008000400020001#128 →
      Inv13Preserved s0 s →
      (∀ j, j < r → h j = serHalf1 w j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x39c4#64) s
        (HalfRangeMem 16 (sp + 28368#64) h ∗ PolyMem (sp + 14432#64) (polyVecNat w) ∗ Rest)
        (fun sf Pf =>
          sf.sp = sp ∧ sf.spAligned = true ∧ Inv13Preserved s0 sf ∧
          Pf = (HalfRangeMem 16 (sp + 28368#64) (serHalf1 w) ∗
            PolyMem (sp + 14432#64) (polyVecNat w) ∗ Rest))
  | 0, r, hrem, s, h, hpc, hrun, hsp, hspA, _hcl, _hro,
      hx8, hx9, hx19, hx20, hv0, hv1, hv2, hv3, hpres, hlo => by
    have hr15 : r = 15 := by omega
    subst hr15
    have hit := seg3_ser1_iter hb s0 s sp w (r := 15) (by decide) h Rest
      hpc hrun hsp hspA hx8 hx9 hx19 hx20 hv0 hv1 hv2 hv3 hpres
    simp only [Nat.lt_irrefl, ↓reduceIte] at hit
    refine SepWP.mono hit ?_
    rintro sf Pf _ _ ⟨hsp', hspA', _, _, _, _, _, _, _, _, hpres', rfl⟩
    refine ⟨hsp', hspA', hpres', ?_⟩
    rw [halfRangeMem_congr (f := Function.update h 15 (serHalf1 w 15)) (g := serHalf1 w)
      (fun j hj => by
        by_cases heq : j = 15
        · subst heq; simp
        · rw [Function.update_of_ne heq]; exact hlo j (by omega))]
  | rem + 1, r, hrem, s, h, hpc, hrun, hsp, hspA, hcl, hro,
      hx8, hx9, hx19, hx20, hv0, hv1, hv2, hv3, hpres, hlo => by
    have hr15 : r < 15 := by omega
    have hit := seg3_ser1_iter hb s0 s sp w (r := r) (by omega) h Rest
      hpc hrun hsp hspA hx8 hx9 hx19 hx20 hv0 hv1 hv2 hv3 hpres
    simp only [hr15, ↓reduceIte] at hit
    refine sepWP_seq_env hcl hro hit ?_
    rintro s1 P1 hpc1 hrun1 hcl1 hro1
      ⟨hsp1, hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hv0_1, hv1_1, hv2_1, hv3_1, hpres1, rfl⟩
    exact seg3_ser1_loop hb s0 sp w Rest rem (r + 1) (by omega) s1
      (Function.update h r (serHalf1 w r)) hpc1 hrun1 hsp1 hspA1 hcl1 hro1
      hx8_1 hx9_1 hx19_1 hx20_1 hv0_1 hv1_1 hv2_1 hv3_1 hpres1
      (fun j hj => by
        by_cases heq : j = r
        · subst heq; simp
        · rw [Function.update_of_ne heq]; exact hlo j (by omega))

theorem seg3_ser1_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 s : State) (sp : BitVec 64) {inv vPoly16 : Poly16} {vSpec invSpec : Poly}
    (hv_sz : vSpec.size = 256) (hinv_sz : invSpec.size = 256)
    (hv_bnd : ∀ i, i < 256 → -3329 ≤ (vPoly16.getD i 0#16).toInt ∧ (vPoly16.getD i 0#16).toInt < 3329)
    (hv_rep : ∀ i, i < 256 → (vPoly16.getD i 0#16).toInt % 3329 = (vSpec.getD i 0 : Int) % 3329)
    (hn_bnd : ∀ i, i < 256 →
      -2496 ≤ (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ∧
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ≤ 2496)
    (hn_rep : ∀ i, i < 256 →
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt % 3329 = (invSpec.getD i 0 : Int) % 3329)
    (Rest : SepProp)
    (hpc : s.pc = b + 0x3918#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = sp + 28368#64)
    (hx20 : s.readReg64 .x20 = sp + 14432#64)
    (hpres : Inv13Preserved s0 s) :
    let w := seg3SubPoly inv vPoly16
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x39c4#64) s
      (PolyMem (sp + 28368#64) (polyVecNat w) ∗ PolyMem (sp + 14432#64) (polyVecNat w) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ Inv13Preserved s0 sf ∧
        (Pf ⊢ ((sp + 28368#64) ↦ₛ compressAndEncode 1 (polySub vSpec invSpec)) ∗
          memRegion (sp + 28400#64) 480 ∗ PolyMem (sp + 14432#64) (polyVecNat w) ∗ Rest)) := by
  intro w
  have hsplit : PolyMem (sp + 28368#64) (polyVecNat w) =
      (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.Vec128At
          (sp + 28368#64) (polyVecNat w 0) ∗
        LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.Vec128At
          (sp + 28384#64) (polyVecNat w 1) ∗
        LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.VecRangeMem 30
          (sp + 28400#64) (fun i => polyVecNat w (i + 2))) := by
    change LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.VecRangeMem 32
        (sp + 28368#64) (polyVecNat w) = _
    simp only [LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.VecRangeMem,
      show (sp + 28368#64) + 16#64 = sp + 28384#64 by bv_omega,
      show (sp + 28384#64) + 16#64 = sp + 28400#64 by bv_omega]
  rw [hsplit, sepConj_assoc, sepConj_assoc]
  refine sepWP_seq_env hcl hro
    (seg3_ser1_setup hb hbase s0 s sp (polyVecNat w 0) (polyVecNat w 1) _
      hpc hrun hsp hspA hcl hro hx19 hx20 hpres) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hv0_1, hv1_1, hv2_1, hv3_1, hpres1, rfl⟩
  rw [show (HalfRangeMem 16 (sp + 28368#64) (fun _ => 0#16) ∗
        (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.VecRangeMem 30
          (sp + 28400#64) (fun i => polyVecNat w (i + 2)) ∗
          (PolyMem (sp + 14432#64) (polyVecNat w) ∗ Rest))) =
      (HalfRangeMem 16 (sp + 28368#64) (fun _ => 0#16) ∗
        PolyMem (sp + 14432#64) (polyVecNat w) ∗
        (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.VecRangeMem 30
          (sp + 28400#64) (fun i => polyVecNat w (i + 2)) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine SepWP.mono
    (seg3_ser1_loop hb s0 sp w _ 15 0 rfl s1 (fun _ => 0#16)
      hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 (by simpa using hx9_1) hx19_1 hx20_1
      hv0_1 hv1_1 hv2_1 hv3_1 hpres1 (fun _ hj => by omega)) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hpres_f, rfl⟩
  refine ⟨hsp_f, hspA_f, hpres_f, ?_⟩
  rw [halfRangeMem_serHalf1_eq hv_sz hinv_sz hv_bnd hv_rep hn_bnd hn_rep (sp + 28368#64)]
  have h480 := vecRangeMem_entails_memRegion 30 (sp + 28400#64) (fun i => polyVecNat w (i + 2))
  exact Entails.trans
    (by sep_frame : _ ⊢
      LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.VecRangeMem 30
        (sp + 28400#64) (fun i => polyVecNat w (i + 2)) ∗
      (((sp + 28368#64) ↦ₛ compressAndEncode 1 (polySub vSpec invSpec)) ∗
        PolyMem (sp + 14432#64) (polyVecNat w) ∗ Rest))
    (Entails.trans (sepConj_mono_left h480) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3Tail

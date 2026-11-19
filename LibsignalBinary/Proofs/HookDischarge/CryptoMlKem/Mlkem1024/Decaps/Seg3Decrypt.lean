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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatIter -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.DecompressBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3DecompressFp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Accum
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Inv1LowLoops
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3InvSym1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3InvSym1c
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3Tail

/-!
# `kyber_decapsulate` (`B06`) — Segment 3 (`IND-CPA.Decrypt`, `+0x1858 .. +0x39c4`)

Composes `decompress_5` (`+0x1858..+0x1970`), 4-way `sHat · uHat` (`+0x1970..+0x1e84`),
7-stage `InvNTT` (`+0x1e84..+0x3830`), `vPoly - to_std(inv)` + Barrett (`+0x3830..+0x3918`),
and `compress_1 + serialize_1` (`+0x3918..+0x39c4`) into `indCpaDecrypt 4 11 5 (sk.take 1536) ct`
at `[sp + 28368, sp + 28400)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3Decrypt

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 byteDecodeMod byteDecodeRaw compressAndEncode decodeAndDecompress
  indCpaDecrypt mlkemQ neonInvNttMontgomery16 neonMontgomeryMul16
  polyInvNtt polyNtt polySub vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents neonVecDotNtt4_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt (
  neonPolyInvNttFromMontInv16 neonPolyInvNttFromMontInv16_spec vecDotNtt_canonical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (byteDecodeRaw_lt_two_pow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 Vec32 VecRangeMem
  poly32Mem_ofFn polyVecNat step_ldpQ128 step_ldrQ128 step_stpQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr
  vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (
  sepWP_elim_poly32 tHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16 lowerInvNtt16_size upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdMla_8h svc_simdMovi_8h_1024
  svc_simdMul_8h svc_simdMvni_8h_f2ff svc_simdSqdmulh_8h svc_simdSshr_8h_1
  svc_simdSshr_8h_11 svc_simdSub_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  Spill21 Spill21Mem spill21Mem_entails_memRegion spill21Mem_ofFn)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1 (AccSpill21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops (Inv13Preserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  Spill40 SpillSliceMem SymEnv SymGprs evalSExpr evalSymGpr symInitState)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SymSpatial SymStateMatches blk06NoRelocInRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym (
  sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  poly_eq_upperInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (blk28_memcpy_06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.DecompressBase (
  decompressPoly16 decompressPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatIter (
  uHatPoly16 uHatPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3DecompressFp (
  seg3_decompress5_fp_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul (
  neonDot4 neonDot4_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Accum (dot1_full_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Inv1LowLoops (inv1_low_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3InvSym1a (cfgSeg3Inv)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3InvSym1c (
  run_seg3_inv1 seg3_inv1_ast_eq seg3_inv1_noSpillVreg symSeg3InvEnd)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3Tail (
  seg3SubLoop_vec_eq seg3SubPoly seg3_ser1_ok)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x3830 → 0x3914]
end

attribute [local irreducible] blkPC06 polyVecNat

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp] private theorem readReg64_orFpsr' (s : State) (f : BitVec 32) (r : Reg) :
    (s.orFpsr f).readReg64 r = s.readReg64 r := rfl
@[simp] private theorem readVReg128_orFpsr' (s : State) (f : BitVec 32) (v : BitVec 5) :
    (s.orFpsr f).readVReg128 v = s.readVReg128 v := rfl
@[simp] private theorem status_orFpsr' (s : State) (f : BitVec 32) :
    (s.orFpsr f).status = s.status := rfl
@[simp] private theorem pc_orFpsr' (s : State) (f : BitVec 32) :
    (s.orFpsr f).pc = s.pc := rfl
@[simp] private theorem sp_orFpsr' (s : State) (f : BitVec 32) :
    (s.orFpsr f).sp = s.sp := rfl
@[simp] private theorem spAligned_orFpsr' (s : State) (f : BitVec 32) :
    (s.orFpsr f).spAligned = s.spAligned := rfl
@[simp] private theorem pstate_orFpsr' (s : State) (f : BitVec 32) :
    (s.orFpsr f).pstate = s.pstate := rfl
@[simp] private theorem mem_orFpsr' (s : State) (f : BitVec 32) :
    (s.orFpsr f).mem = s.mem := rfl

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdMla_8h
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSshr_8h_11
  svc_simdMovi_8h_1024 svc_simdMvni_8h_f2ff svc_simdDup_8h_gpr

abbrev off1858 : BitVec 64 := 6232#64
private abbrev off1970 : BitVec 64 := 6512#64
private abbrev off1e84 : BitVec 64 := 7812#64
private abbrev off1fd0 : BitVec 64 := 8144#64
private abbrev off3830 : BitVec 64 := 14384#64
private abbrev off3834 : BitVec 64 := 14388#64
private abbrev off3858 : BitVec 64 := 14424#64
private abbrev off38d4 : BitVec 64 := 14548#64
private abbrev off38d8 : BitVec 64 := 14552#64
private abbrev off3900 : BitVec 64 := 14592#64
private abbrev off3918 : BitVec 64 := 14616#64
abbrev off39c4 : BitVec 64 := 14788#64

/-! ## 1. Pure `IND-CPA.Decrypt` (`K = 4, d_u = 11, d_v = 5`) Soundness -/

theorem tHatPoly16_spec (bs : List (BitVec 8)) :
    PolyBounded16 4095 (tHatPoly16 bs) ∧ PolyRepresents (tHatPoly16 bs) (byteDecodeMod 12 bs) := by
  unfold tHatPoly16
  have hsz_raw : (byteDecodeRaw 12 bs).size = 256 := by simp [byteDecodeRaw]
  have hsz : ((byteDecodeRaw 12 bs).map fun c => BitVec.ofNat 16 c).size = 256 := by simp [hsz_raw]
  refine ⟨⟨hsz, fun i hi => ?_⟩, ⟨hsz, fun i hi => ?_⟩⟩
  · have hlt := byteDecodeRaw_lt_two_pow 12 (by omega) bs i hi
    have hmap : ((byteDecodeRaw 12 bs).map fun c => BitVec.ofNat 16 c).getD i 0#16 =
        BitVec.ofNat 16 ((byteDecodeRaw 12 bs).getD i 0) := by simp [Array.getD, hsz_raw, hi]
    rw [hmap, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · have hlt := byteDecodeRaw_lt_two_pow 12 (by omega) bs i hi
    have hmap16 : ((byteDecodeRaw 12 bs).map fun c => BitVec.ofNat 16 c).getD i 0#16 =
        BitVec.ofNat 16 ((byteDecodeRaw 12 bs).getD i 0) := by simp [Array.getD, hsz_raw, hi]
    have hmapMod : (byteDecodeMod 12 bs).getD i 0 = (byteDecodeRaw 12 bs).getD i 0 % mlkemQ := by
      simp [byteDecodeMod, Array.getD, hsz_raw, hi]
    rw [hmap16, hmapMod, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    dsimp only [mlkemQ]; omega

private theorem uHatPoly16_spec_4095 (ctSlice : List (BitVec 8)) :
    PolyBounded16 4095 (uHatPoly16 ctSlice) ∧
    PolyRepresents (uHatPoly16 ctSlice) (polyNtt (decodeAndDecompress 11 ctSlice)) := by
  obtain ⟨_, ⟨hsz, hb⟩, hr⟩ := uHatPoly16_spec ctSlice
  exact ⟨⟨hsz, fun i hi => ⟨by have := (hb i hi).1; omega, by have := (hb i hi).2; omega⟩⟩, hr⟩

private theorem take1536_slice (sk : List (BitVec 8)) (i : Nat) (hi : i < 4) :
    ((sk.take 1536).drop (384 * i)).take 384 = (sk.drop (384 * i)).take 384 := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

private theorem seg3_decrypt_pure {sk ct : List (BitVec 8)} (hct : ct.length = 1568) :
    let sHat : Array Poly := Array.ofFn (n := 4) fun ⟨i, _⟩ =>
      byteDecodeMod 12 ((sk.take 1536).drop (384 * i) |>.take 384)
    let uHat : Array Poly := Array.ofFn (n := 4) fun ⟨i, _⟩ =>
      polyNtt (decodeAndDecompress 11 ((ct.drop (i * 352)).take 352))
    let vSpec := decodeAndDecompress 5 (ct.drop 1408)
    let invSpec := polyInvNtt (vecDotNtt 4 sHat uHat)
    let dot := neonDot4
      (tHatPoly16 (sk.take 384)) (tHatPoly16 ((sk.drop 384).take 384))
      (tHatPoly16 ((sk.drop 768).take 384)) (tHatPoly16 ((sk.drop 1152).take 384))
      (uHatPoly16 (ct.take 352)) (uHatPoly16 ((ct.drop 352).take 352))
      (uHatPoly16 ((ct.drop 704).take 352)) (uHatPoly16 ((ct.drop 1056).take 352))
    let inv := neonInvNttMontgomery16 dot
    let vPoly16 := decompressPoly16 5 (ct.drop 1408)
    vSpec.size = 256 ∧ invSpec.size = 256 ∧
    (∀ i, i < 256 → -3329 ≤ (vPoly16.getD i 0#16).toInt ∧ (vPoly16.getD i 0#16).toInt < 3329) ∧
    (∀ i, i < 256 → (vPoly16.getD i 0#16).toInt % 3329 = (vSpec.getD i 0 : Int) % 3329) ∧
    (∀ i, i < 256 → -2496 ≤ (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ∧
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ≤ 2496) ∧
    (∀ i, i < 256 → (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt % 3329 =
      (invSpec.getD i 0 : Int) % 3329) ∧
    compressAndEncode 1 (polySub vSpec invSpec) = indCpaDecrypt 4 11 5 (sk.take 1536) ct := by
  intro sHat uHat vSpec invSpec dot inv vPoly16
  obtain ⟨hv_b, hv_r⟩ := decompressPoly16_spec (ct.drop 1408) (Or.inl rfl)
  obtain ⟨hs0_b, hs0_r⟩ := tHatPoly16_spec (sk.take 384)
  obtain ⟨hs1_b, hs1_r⟩ := tHatPoly16_spec ((sk.drop 384).take 384)
  obtain ⟨hs2_b, hs2_r⟩ := tHatPoly16_spec ((sk.drop 768).take 384)
  obtain ⟨hs3_b, hs3_r⟩ := tHatPoly16_spec ((sk.drop 1152).take 384)
  obtain ⟨hu0_b, hu0_r⟩ := uHatPoly16_spec_4095 (ct.take 352)
  obtain ⟨hu1_b, hu1_r⟩ := uHatPoly16_spec_4095 ((ct.drop 352).take 352)
  obtain ⟨hu2_b, hu2_r⟩ := uHatPoly16_spec_4095 ((ct.drop 704).take 352)
  obtain ⟨hu3_b, hu3_r⟩ := uHatPoly16_spec_4095 ((ct.drop 1056).take 352)
  have hs0 : sHat.getD 0 zeroPoly = byteDecodeMod 12 (sk.take 384) := by
    simp [sHat, Array.getD, List.take_take]
  have hs1 : sHat.getD 1 zeroPoly = byteDecodeMod 12 ((sk.drop 384).take 384) := by
    simp [sHat, Array.getD, take1536_slice sk 1 (by decide)]
  have hs2 : sHat.getD 2 zeroPoly = byteDecodeMod 12 ((sk.drop 768).take 384) := by
    simp [sHat, Array.getD, take1536_slice sk 2 (by decide)]
  have hs3 : sHat.getD 3 zeroPoly = byteDecodeMod 12 ((sk.drop 1152).take 384) := by
    simp [sHat, Array.getD, take1536_slice sk 3 (by decide)]
  have hu0 : uHat.getD 0 zeroPoly = polyNtt (decodeAndDecompress 11 (ct.take 352)) := by
    simp [uHat, Array.getD]
  have hu1 : uHat.getD 1 zeroPoly = polyNtt (decodeAndDecompress 11 ((ct.drop 352).take 352)) := by
    simp [uHat, Array.getD]
  have hu2 : uHat.getD 2 zeroPoly = polyNtt (decodeAndDecompress 11 ((ct.drop 704).take 352)) := by
    simp [uHat, Array.getD]
  have hu3 : uHat.getD 3 zeroPoly = polyNtt (decodeAndDecompress 11 ((ct.drop 1056).take 352)) := by
    simp [uHat, Array.getD]
  obtain ⟨hdot_b, hdot_r⟩ := neonVecDotNtt4_spec hs0_b hs1_b hs2_b hs3_b hu0_b hu1_b hu2_b hu3_b
    (hs0 ▸ hs0_r) (hs1 ▸ hs1_r) (hs2 ▸ hs2_r) (hs3 ▸ hs3_r)
    (hu0 ▸ hu0_r) (hu1 ▸ hu1_r) (hu2 ▸ hu2_r) (hu3 ▸ hu3_r)
  obtain ⟨⟨hinv_sz, _⟩, ⟨hm_sz, hm_b⟩, ⟨_, hm_r⟩⟩ :=
    neonPolyInvNttFromMontInv16_spec (dot := dot) hdot_b hdot_r (vecDotNtt_canonical 4 sHat uHat)
  have hct_drop : (ct.drop 1408).take 160 = ct.drop 1408 :=
    List.take_of_length_le (by simp [hct])
  refine ⟨by simp [vSpec, decodeAndDecompress, byteDecodeRaw], hinv_sz, ?_, hv_r.2, ?_, ?_, ?_⟩
  · intro i hi; dsimp only [vPoly16]; have h := hv_b.2 i hi; exact ⟨by omega, by omega⟩
  · intro i hi
    have hget : (neonPolyInvNttFromMontInv16 dot).getD i 0#16 =
        neonMontgomeryMul16 (inv.getD i 0#16) 1441#16 := by
      have hisz : inv.size = 256 := by simpa [neonPolyInvNttFromMontInv16, inv] using hm_sz
      simp [neonPolyInvNttFromMontInv16, inv, Array.getD, hisz, hi]
    rw [← hget]; exact hm_b i hi
  · intro i hi
    have hget : (neonPolyInvNttFromMontInv16 dot).getD i 0#16 =
        neonMontgomeryMul16 (inv.getD i 0#16) 1441#16 := by
      have hisz : inv.size = 256 := by simpa [neonPolyInvNttFromMontInv16, inv] using hm_sz
      simp [neonPolyInvNttFromMontInv16, inv, Array.getD, hisz, hi]
    rw [← hget]; exact hm_r i hi
  · simp [indCpaDecrypt, sHat, uHat, vSpec, invSpec, hct_drop]

/-! ## 2. Symbolic Upper `InvNTT1` (`+0x1fd0 → +0x3830`) -/

private theorem noReloc_inv1 : blk06NoRelocInRange 2036 3596 = true := by decide +kernel

private def mkInvEnv (s : State) (sp21 : Spill21) (p : Poly16) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := Spill40.ofFn fun i => if i < 21 then sp21.get i else 0#128
  poly0   := Vec32.ofFn (polyVecNat p)
  src0    := Vec32.zero
  gpr0    := fun r => s.readReg64 (.gpr r)
  pstate0 := s.pstate

private theorem matches_invInit {sp : BitVec 64} {s : State} (sp21 : Spill21) (p : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SymStateMatches sp (mkInvEnv s sp21 p) symInitState s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symInitState, SymGprs.ofFn, SymGprs.get, evalSymGpr, mkInvEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem spill21Mem_eq_initSlice (ptr : BitVec 64) (s : State) (sp21 : Spill21) (p : Poly16) :
    Spill21Mem ptr sp21 = SpillSliceMem 21 ptr (symInitState.spill.eval (mkInvEnv s sp21 p)) :=
  vecRangeMem_congr fun i hi => by
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10
    | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 => rfl
    | _ + 21 => omega

private theorem polyMem_eq_initPoly32 (ptr : BitVec 64) (s : State) (sp21 : Spill21) (p : Poly16) :
    PolyMem ptr (polyVecNat p) = Poly32Mem ptr (symInitState.poly.eval (mkInvEnv s sp21 p)) := by
  change PolyMem ptr (polyVecNat p) = Poly32Mem ptr (Vec32.ofFn (polyVecNat p))
  rw [poly32Mem_ofFn]

private theorem seg3_inv_upper_ok [MlKemPlacement] {b : BitVec 64}
    (s : State) (sp : BitVec 64) {dot : Poly16} (hdot : dot.size = 256)
    (sp21 : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + off1fd0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3830) s
      (Spill21Mem (sp + 2096#64) sp21 ∗
        PolyMem (sp + 28368#64) (polyVecNat (lowerInvNtt16 dot)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = sp + 14432#64 ∧ sf.readReg64 .x1 = sp + 28368#64 ∧
        sf.readReg64 .x2 = 512#64 ∧ sf.readReg64 .x19 = sp + 14432#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        ∃ sp40 : Spill40,
          sp40.get 14 = dup8x16 20159#16 ∧ sp40.get 19 = dup8x16 3329#16 ∧
          (Pf ⊢ SpillSliceMem 21 (sp + 2096#64) sp40 ∗
            PolyMem (sp + 28368#64) (polyVecNat (neonInvNttMontgomery16 dot)) ∗ Rest)) := by
  let env := mkInvEnv s sp21 (lowerInvNtt16 dot)
  have hpre : Spill21Mem (sp + 2096#64) sp21 ∗
      PolyMem (sp + 28368#64) (polyVecNat (lowerInvNtt16 dot)) ∗ Rest ⊢
      SymSpatial cfgSeg3Inv sp env symInitState Rest := by
    simp only [SymSpatial, PolySymBridge.polyPtr, PolySymBridge.SrcOptMem, cfgSeg3Inv,
      Bool.false_eq_true, ↓reduceIte]
    rw [spill21Mem_eq_initSlice (sp + 2096#64) s sp21 (lowerInvNtt16 dot),
      polyMem_eq_initPoly32 (sp + 28368#64) s sp21 (lowerInvNtt16 dot)]
    sep_frame
  refine SepWP.weaken_pre hpre
    (sepWP_of_runSymRange (wLo := 2036) (wHi := 3596) 1560 2036
      noReloc_inv1 (by decide) (by omega) (by omega) run_seg3_inv1
      (matches_invInit sp21 (lowerInvNtt16 dot) hsp hspA) hpc hrun ?_)
  intro sf _ _ hmf
  have hgpr := hmf.hgprs
  have hg0 := hgpr 0#5 (by decide)
  have hg1 := hgpr 1#5 (by decide)
  have hg2 := hgpr 2#5 (by decide)
  have hg19 := hgpr 19#5 (by decide)
  have hg23 := hgpr 23#5 (by decide)
  have hg25 := hgpr 25#5 (by decide)
  have hg26 := hgpr 26#5 (by decide)
  have hg29 := hgpr 29#5 (by decide)
  change sf.readReg64 .x0 = sp + 14432#64 at hg0
  change sf.readReg64 .x1 = sp + 28368#64 at hg1
  change sf.readReg64 .x2 = 512#64 at hg2
  change sf.readReg64 .x19 = sp + 14432#64 at hg19
  change sf.readReg64 .x23 = s.readReg64 .x23 + 0#64 at hg23
  change sf.readReg64 .x25 = s.readReg64 .x25 + 0#64 at hg25
  change sf.readReg64 .x26 = s.readReg64 .x26 + 0#64 at hg26
  change sf.readReg64 .fp = s.readReg64 .fp + 0#64 at hg29
  refine ⟨hmf.hsp, hmf.hsp_al, hg0, hg1, hg2, hg19,
    by rw [hg23, BitVec.add_zero], by rw [hg25, BitVec.add_zero],
    by rw [hg26, BitVec.add_zero], by rw [hg29, BitVec.add_zero],
    symSeg3InvEnd.spill.eval env, rfl, rfl, ?_⟩
  simp only [SymSpatial, PolySymBridge.polyPtr, PolySymBridge.SrcOptMem, cfgSeg3Inv,
    Bool.false_eq_true, ↓reduceIte]
  have hpoly_eq := poly_eq_upperInvNtt16 (sp + 28368#64) (lowerInvNtt16_size hdot) env rfl
    symSeg3InvEnd.poly seg3_inv1_noSpillVreg seg3_inv1_ast_eq
  rw [hpoly_eq, upperInvNtt16_lowerInvNtt16]
  sep_frame

/-! ## 3. `memcpy` In, Subtraction + Barrett Loop, & Dual `memcpy` Out (`+0x3830 → +0x3918`) -/

private theorem seg3_sub_memcpy_in [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (inv : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off3830) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 14432#64) (hx1 : s.readReg64 .x1 = sp + 28368#64)
    (hx2 : s.readReg64 .x2 = 512#64) (hx19 : s.readReg64 .x19 = sp + 14432#64)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3834) s
      (memRegion (sp + 14432#64) 512 ∗ PolyMem (sp + 28368#64) (polyVecNat inv) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x19 = sp + 14432#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        Pf = (PolyMem (sp + 14432#64) (polyVecNat inv) ∗
          PolyMem (sp + 28368#64) (polyVecNat inv) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs_def : vecRangeBytes 32 (polyVecNat inv) = bsInv
  have hbs : bsInv.length = 512 := by rw [← hbs_def, vecRangeBytes_length]
  have hp28368 : PolyMem (sp + 28368#64) (polyVecNat inv) = ((sp + 28368#64) ↦ₛ bsInv) := by
    rw [← hbs_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp14432 : ((sp + 14432#64) ↦ₛ bsInv) = PolyMem (sp + 14432#64) (polyVecNat inv) := by
    rw [← hbs_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  rw [hp28368]
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 14432#64, sp + 28368#64, bsInv)
  rw [← hp28368, hp14432]
  have hsp_sf : sf.sp = sp := by simp [*]
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], sepProp_ext (by sep_frame) (by sep_frame)⟩

private theorem seg3_sub_setup [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp : BitVec 64) (sp40 : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + off3834) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = sp + 14432#64)
    (hs14 : sp40.get 14 = dup8x16 20159#16) (hs19 : sp40.get 19 = dup8x16 3329#16) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3858) s
      (SpillSliceMem 21 (sp + 2096#64) sp40 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x8 = 0#64 ∧ s1.readReg64 .x9 = 1441#64 ∧
        s1.readReg64 .x10 = 55457#64 ∧ s1.readReg64 .x11 = sp + 26320#64 ∧
        s1.readReg64 .x19 = sp + 14432#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readVReg128 5#5 = dup8x16 3329#16 ∧ s1.readVReg128 6#5 = dup8x16 20159#16 ∧
        s1.readVReg128 7#5 = dup8x16 1024#16 ∧ s1.readVReg128 16#5 = dup8x16 62207#16 ∧
        P1 = (SpillSliceMem 21 (sp + 2096#64) sp40 ∗ Rest)) := by
  have _ : b = blkPl06.base := _hb
  wp_steps 2
  refine step_ldrQ128 (wb := none) (ea := (sp + 2096#64) + BitVec.ofNat 64 (16 * 14))
    (v := dup8x16 20159#16)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (hs14 ▸ SepLoad128.left (SepLoad128.vecRange (n := 21) (k := 14) (by decide) rfl))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := (sp + 2096#64) + BitVec.ofNat 64 (16 * 19))
    (v := dup8x16 3329#16)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (hs19 ▸ SepLoad128.left (SepLoad128.vecRange (n := 21) (k := 19) (by decide) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 5
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp, by simp, by simp, by simp, by simp [hx19],
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, rfl⟩

private theorem update2_split {f g0 g1 : Nat → BitVec 128} {r : Nat}
    (hlo : ∀ j, j < 2 * r → f j = g1 j)
    (hhi : ∀ j, 2 * r ≤ j → j < 32 → f j = g0 j) :
    let f' := Function.update (Function.update f (2 * r) (g1 (2 * r)))
      (2 * r + 1) (g1 (2 * r + 1))
    (∀ j, j < 2 * (r + 1) → f' j = g1 j) ∧
    (∀ j, 2 * (r + 1) ≤ j → j < 32 → f' j = g0 j) := by
  refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
  · by_cases h1 : j = 2 * r + 1
    · subst h1; simp
    · rw [Function.update_of_ne h1]
      by_cases h0 : j = 2 * r
      · subst h0; simp
      · rw [Function.update_of_ne h0]; exact hlo j (by omega)
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hhi j (by omega) hj2

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

private theorem seg3_sub_branch [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    {r : Nat} (hr : r < 16) (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = b + off38d4) (hrun : s.status = .Running)
    (hpst : s.pstate = subsPState64 (BitVec.ofNat 64 (32 * r) + 32#64) 512#64)
    (hpost : ∀ s', s'.sp = s.sp → s'.spAligned = s.spAligned →
      (∀ g : BitVec 5, s'.readReg64 (.gpr g) = s.readReg64 (.gpr g)) →
      (∀ v, s'.readVReg128 v = s.readVReg128 v) → post s' P) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + off3858 else b + off38d8) s P post := by
  have _ : b = blkPl06.base := _hb
  by_cases hr15 : r < 15
  · simp only [hr15, ↓reduceIte]
    have hcond : ConditionHolds .NE s.pstate = true := by
      rw [hpst]; clear * - hr15
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r
      all_goals first | omega | simp [wp_norm, arm64_norm]
    refine step_bCond_taken (pc := b + off38d4) (dst := b + off3858)
      hpc hrun (by wp_norm_lhs) hcond (by simp only [BitVec.add_assoc]; rfl) ?_
    exact SepWP.done (by simp [State.setPC]) (by simp [State.setPC, hrun])
      (hpost (s.setPC (b + off3858)) (by simp [State.setPC]) (by simp [State.spAligned, State.setPC])
        (fun _ => by simp [State.readReg64, State.setPC])
        (fun _ => by simp [State.readVReg128, State.setPC]))
  · have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    have hcond : ConditionHolds .NE s.pstate = false := by
      simp [hpst, hr_eq, wp_norm, arm64_norm]
    refine step_bCond_not_taken (pc := b + off38d4) (dst := b + off38d8)
      hpc hrun (by wp_norm_lhs) hcond (by simp only [BitVec.add_assoc]; rfl) ?_
    exact SepWP.done (by simp [State.setPC]) (by simp [State.setPC, hrun])
      (hpost (s.setPC (b + off38d8)) (by simp [State.setPC]) (by simp [State.spAligned, State.setPC])
        (fun _ => by simp [State.readReg64, State.setPC])
        (fun _ => by simp [State.readVReg128, State.setPC]))

private theorem seg3_sub_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp : BitVec 64) (inv vPoly : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off3858) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (32 * r))
    (hx9 : s.readReg64 .x9 = 1441#64) (hx10 : s.readReg64 .x10 = 55457#64)
    (hx11 : s.readReg64 .x11 = sp + 26320#64) (hx19 : s.readReg64 .x19 = sp + 14432#64)
    (hv5 : s.readVReg128 5#5 = dup8x16 3329#16) (hv6 : s.readVReg128 6#5 = dup8x16 20159#16)
    (hv7 : s.readVReg128 7#5 = dup8x16 1024#16) (hv16 : s.readVReg128 16#5 = dup8x16 62207#16)
    (hhi0 : f (2 * r) = polyVecNat inv (2 * r))
    (hhi1 : f (2 * r + 1) = polyVecNat inv (2 * r + 1)) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + off3858 else b + off38d8) s
      (PolyMem (sp + 14432#64) f ∗ PolyMem (sp + 26320#64) (polyVecNat vPoly) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x9 = 1441#64 ∧ s'.readReg64 .x10 = 55457#64 ∧
        s'.readReg64 .x11 = sp + 26320#64 ∧ s'.readReg64 .x19 = sp + 14432#64 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 5#5 = dup8x16 3329#16 ∧ s'.readVReg128 6#5 = dup8x16 20159#16 ∧
        s'.readVReg128 7#5 = dup8x16 1024#16 ∧ s'.readVReg128 16#5 = dup8x16 62207#16 ∧
        P' = (PolyMem (sp + 14432#64)
          (Function.update
            (Function.update f (2 * r) (polyVecNat (seg3SubPoly inv vPoly) (2 * r)))
            (2 * r + 1) (polyVecNat (seg3SubPoly inv vPoly) (2 * r + 1))) ∗
          PolyMem (sp + 26320#64) (polyVecNat vPoly) ∗ Rest)) := by
  have _ : b = blkPl06.base := _hb
  wp_steps 3
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 14432#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 14432#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat inv (2 * r)) (v2 := polyVecNat inv (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 15
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 26320#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 26320#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat vPoly (2 * r)) (v2 := polyVecNat vPoly (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 10
  have hv1_eq := seg3SubLoop_vec_eq inv vPoly (2 * r) (by omega) true
  have hv0_eq := seg3SubLoop_vec_eq inv vPoly (2 * r + 1) (by omega) false
  simp only [Bool.false_eq_true, ↓reduceIte] at hv1_eq hv0_eq
  refine step_stpQ128 (wb := none)
    (ea := (sp + 14432#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 14432#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat (seg3SubPoly inv vPoly) (2 * r))
    (v2 := polyVecNat (seg3SubPoly inv vPoly) (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by simp [← hv1_eq])
    (by simp [← hv0_eq])
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'
  refine seg3_sub_branch _hb hr _ _ _ (by wp_norm_lhs) (by simp [hrun])
    (by simp) ?_
  intro s' hsp' hspA' hr' hv'
  refine ⟨by rw [hsp']; simp [hsp], by rw [hspA']; simpa [State.spAligned, hsp] using hspA,
    by rw [hr' 8#5]; simp; clear * - hr; bv_omega,
    by rw [hr' 9#5]; simp [hx9], by rw [hr' 10#5]; simp [hx10],
    by rw [hr' 11#5]; simp [hx11], by rw [hr' 19#5]; simp [hx19],
    by rw [hr' 23#5]; simp, by rw [hr' 25#5]; simp, by rw [hr' 26#5]; simp, by rw [hr' 29#5]; simp,
    by rw [hv']; simp [hv5], by rw [hv']; simp [hv6],
    by rw [hv']; simp [hv7], by rw [hv']; simp [hv16], rfl⟩

private theorem seg3_sub_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (sp x23v x25v x26v fpv : BitVec 64) (inv vPoly : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 →
    ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + off3858 → s.status = .Running →
      s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x9 = 1441#64 → s.readReg64 .x10 = 55457#64 →
      s.readReg64 .x11 = sp + 26320#64 → s.readReg64 .x19 = sp + 14432#64 →
      s.readReg64 .x23 = x23v → s.readReg64 .x25 = x25v →
      s.readReg64 .x26 = x26v → s.readReg64 .fp = fpv →
      s.readVReg128 5#5 = dup8x16 3329#16 → s.readVReg128 6#5 = dup8x16 20159#16 →
      s.readVReg128 7#5 = dup8x16 1024#16 → s.readVReg128 16#5 = dup8x16 62207#16 →
      (∀ j, j < 2 * r → f j = polyVecNat (seg3SubPoly inv vPoly) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat inv j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + off38d8) s
        (PolyMem (sp + 14432#64) f ∗ PolyMem (sp + 26320#64) (polyVecNat vPoly) ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .x23 = x23v ∧ s'.readReg64 .x25 = x25v ∧
          s'.readReg64 .x26 = x26v ∧ s'.readReg64 .fp = fpv ∧
          P' = (PolyMem (sp + 14432#64) (polyVecNat (seg3SubPoly inv vPoly)) ∗
            PolyMem (sp + 26320#64) (polyVecNat vPoly) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl _hro hx8 hx9 hx10 hx11 hx19
      hx23 hx25 hx26 hfp hv5 hv6 hv7 hv16 hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hstep := seg3_sub_iter hb s sp inv vPoly (r := 15) (by decide) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx19 hv5 hv6 hv7 hv16
      (hhi 30 (by decide) (by decide)) (hhi 31 (by decide) (by decide))
    simp only [show ¬ (15 < 15) by decide, ↓reduceIte] at hstep
    refine SepWP.mono hstep ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, hx23', hx25', hx26', hfp', _, _, _, _, hP'⟩
    refine ⟨hsp', hspA', hx23'.trans hx23, hx25'.trans hx25, hx26'.trans hx26, hfp'.trans hfp, ?_⟩
    rw [hP']; dsimp only [PolyMem]
    rw [vecRangeMem_congr (update2_split (r := 15) hlo hhi).1]
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx19
      hx23 hx25 hx26 hfp hv5 hv6 hv7 hv16 hlo hhi
    have hr_lt : r < 15 := by omega
    have hstep := seg3_sub_iter hb s sp inv vPoly (r := r) (by omega) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx19 hv5 hv6 hv7 hv16
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr_lt, ↓reduceIte] at hstep
    refine sepWP_seq_env hcl hro hstep ?_
    rintro sm _ hpc' hrun' hcl' hro'
      ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx19', hx23', hx25', hx26', hfp',
        hv5', hv6', hv7', hv16', rfl⟩
    have ⟨hlo', hhi'⟩ := update2_split (r := r) hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc' hrun' hsp' hspA' hcl' hro'
      hx8' hx9' hx10' hx11' hx19' (hx23'.trans hx23) (hx25'.trans hx25)
      (hx26'.trans hx26) (hfp'.trans hfp) hv5' hv6' hv7' hv16' hlo' hhi'

private theorem seg3_sub_memcpy_out [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (w : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off38d8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3918) s
      (PolyMem (sp + 14432#64) (polyVecNat w) ∗ memRegion (sp + 28368#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 28368#64 ∧ sf.readReg64 .x20 = sp + 14432#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ PolyMem (sp + 28368#64) (polyVecNat w) ∗
          PolyMem (sp + 14432#64) (polyVecNat w) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs_def : vecRangeBytes 32 (polyVecNat w) = bsW
  have hbs : bsW.length = 512 := by rw [← hbs_def, vecRangeBytes_length]
  have hp14432 : PolyMem (sp + 14432#64) (polyVecNat w) = ((sp + 14432#64) ↦ₛ bsW) := by
    rw [← hbs_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp28368 : ((sp + 28368#64) ↦ₛ bsW) = PolyMem (sp + 28368#64) (polyVecNat w) := by
    rw [← hbs_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hstep1 : SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off3900) s
      (PolyMem (sp + 14432#64) (polyVecNat w) ∗ memRegion (sp + 28368#64) 512 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x19 = sp + 28368#64 ∧ s1.readReg64 .x20 = sp + 14432#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        P1 = (((sp + 28368#64) ↦ₛ bsW) ∗ ((sp + 14432#64) ↦ₛ bsW) ∗ Rest)) := by
    rw [hp14432]
    wp_steps 9
    wp_call (blk28_memcpy_06 blkPl06.base) (sp + 28368#64, sp + 14432#64, bsW)
    have hsp_s1 : sf.sp = sp := by simp [*]
    exact SepWP.done (by wp_norm_lhs) (by simp [*])
      ⟨hsp_s1, spAligned_of_chk hsp_s1 hsp_chk,
        by simp [*], by simp [*],
        by simp [*], by simp [*], by simp [*], by simp [*],
        sepProp_ext (by sep_frame) (by sep_frame)⟩
  refine sepWP_seq_env hcl hro hstep1 ?_
  rintro s1 _ hpc1 hrun1 hcl1 _ ⟨hsp1, hspA1, hx19_1, hx20_1, hx23_1, hx25_1, hx26_1, hfp_1, rfl⟩
  have hm14 : ((sp + 28368#64) ↦ₛ bsW) ∗ ((sp + 14432#64) ↦ₛ bsW) ∗ Rest ⊢
      memRegion (sp + 14432#64) 512 ∗ ((sp + 28368#64) ↦ₛ bsW) ∗ Rest := by
    have hm : ((sp + 14432#64) ↦ₛ bsW) ⊢ memRegion (sp + 14432#64) 512 := by
      rw [← hbs]; exact pointsToBytes_entails_memRegion _ _
    exact entails_sub hm (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hm14 ?_
  wp_steps 5
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 14432#64, sp + 28368#64, bsW)
  rw [← hp14432, hp28368]
  have hsp_sf : sf.sp = sp := by simp [*]
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*],
      by sep_frame⟩

private theorem seg3_sub_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (sp40 : Spill40) (inv vPoly : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off3830) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 14432#64) (hx1 : s.readReg64 .x1 = sp + 28368#64)
    (hx2 : s.readReg64 .x2 = 512#64) (hx19 : s.readReg64 .x19 = sp + 14432#64)
    (hs14 : sp40.get 14 = dup8x16 20159#16) (hs19 : sp40.get 19 = dup8x16 3329#16)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let w := seg3SubPoly inv vPoly
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3918) s
      (SpillSliceMem 21 (sp + 2096#64) sp40 ∗ memRegion (sp + 14432#64) 512 ∗
        PolyMem (sp + 26320#64) (polyVecNat vPoly) ∗
        PolyMem (sp + 28368#64) (polyVecNat inv) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 28368#64 ∧ sf.readReg64 .x20 = sp + 14432#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ memRegion (sp + 2096#64) 336 ∗ memRegion (sp + 26320#64) 512 ∗
          PolyMem (sp + 28368#64) (polyVecNat w) ∗
          PolyMem (sp + 14432#64) (polyVecNat w) ∗ Rest)) := by
  intro w
  set R1 := SpillSliceMem 21 (sp + 2096#64) sp40 ∗ PolyMem (sp + 26320#64) (polyVecNat vPoly) ∗ Rest
  have hpre1 : SpillSliceMem 21 (sp + 2096#64) sp40 ∗ memRegion (sp + 14432#64) 512 ∗
      PolyMem (sp + 26320#64) (polyVecNat vPoly) ∗ PolyMem (sp + 28368#64) (polyVecNat inv) ∗ Rest ⊢
      memRegion (sp + 14432#64) 512 ∗ PolyMem (sp + 28368#64) (polyVecNat inv) ∗ R1 := by
    dsimp only [R1]; sep_frame
  refine SepWP.weaken_pre hpre1 (sepWP_seq_env hcl hro
    (seg3_sub_memcpy_in hb hbase s sp inv R1 hpc hrun hsp hspA hx0 hx1 hx2 hx19 hcl) ?_)
  rintro s1 _ hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx23_1, hx25_1, hx26_1, hfp_1, rfl⟩
  set R2 := PolyMem (sp + 14432#64) (polyVecNat inv) ∗ PolyMem (sp + 28368#64) (polyVecNat inv) ∗
    PolyMem (sp + 26320#64) (polyVecNat vPoly) ∗ Rest
  have hpre2 : PolyMem (sp + 14432#64) (polyVecNat inv) ∗
      PolyMem (sp + 28368#64) (polyVecNat inv) ∗ R1 ⊢
      SpillSliceMem 21 (sp + 2096#64) sp40 ∗ R2 := by dsimp only [R1, R2]; sep_frame
  refine SepWP.weaken_pre hpre2 (sepWP_seq_env hcl1 hro1
    (seg3_sub_setup hb s1 sp sp40 R2 hpc1 hrun1 hsp1 hspA1 hx19_1 hs14 hs19) ?_)
  rintro s2 _ hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx19_2, hx23_2, hx25_2, hx26_2, hfp_2,
      hv5_2, hv6_2, hv7_2, hv16_2, rfl⟩
  set R3 := SpillSliceMem 21 (sp + 2096#64) sp40 ∗ PolyMem (sp + 28368#64) (polyVecNat inv) ∗ Rest
  have hpre3 : SpillSliceMem 21 (sp + 2096#64) sp40 ∗ R2 ⊢
      PolyMem (sp + 14432#64) (polyVecNat inv) ∗ PolyMem (sp + 26320#64) (polyVecNat vPoly) ∗ R3 := by
    dsimp only [R2, R3]; sep_frame
  refine SepWP.weaken_pre hpre3 (sepWP_seq_env hcl2 hro2
    (seg3_sub_loop hb sp (s.readReg64 .x23) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .fp)
      inv vPoly R3 15 0 rfl
      s2 (polyVecNat inv) hpc2 hrun2 hsp2 hspA2 hcl2 hro2
      (by simpa using hx8_2) hx9_2 hx10_2 hx11_2 hx19_2
      (hx23_2.trans hx23_1) (hx25_2.trans hx25_1) (hx26_2.trans hx26_1) (hfp_2.trans hfp_1)
      hv5_2 hv6_2 hv7_2 hv16_2 (fun _ hj => by omega) (fun _ _ _ => rfl)) ?_)
  rintro s3 _ hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hx23_3, hx25_3, hx26_3, hfp_3, rfl⟩
  set R4 := memRegion (sp + 2096#64) 336 ∗ memRegion (sp + 26320#64) 512 ∗ Rest
  have hpre4 : PolyMem (sp + 14432#64) (polyVecNat w) ∗
      PolyMem (sp + 26320#64) (polyVecNat vPoly) ∗ R3 ⊢
      PolyMem (sp + 14432#64) (polyVecNat w) ∗ memRegion (sp + 28368#64) 512 ∗ R4 := by
    dsimp only [R3, R4, PolyMem, SpillSliceMem]
    have hm20 : VecRangeMem 21 (sp + 2096#64) sp40.get ⊢ memRegion (sp + 2096#64) 336 :=
      vecRangeMem_entails_memRegion 21 (sp + 2096#64) sp40.get
    have hm26 : VecRangeMem 32 (sp + 26320#64) (polyVecNat vPoly) ⊢ memRegion (sp + 26320#64) 512 :=
      vecRangeMem_entails_memRegion 32 (sp + 26320#64) (polyVecNat vPoly)
    have hm28 : VecRangeMem 32 (sp + 28368#64) (polyVecNat inv) ⊢ memRegion (sp + 28368#64) 512 :=
      vecRangeMem_entails_memRegion 32 (sp + 28368#64) (polyVecNat inv)
    exact entails_sub hm20 (by sep_frame)
      (entails_sub hm26 (by sep_frame) (entails_sub hm28 (by sep_frame) (by sep_frame)))
  refine SepWP.weaken_pre hpre4
    (SepWP.mono (seg3_sub_memcpy_out hb hbase s3 sp w R4 hpc3 hrun3 hsp3 hspA3 hcl3 hro3) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx19_f, hx20_f, hx23_f, hx25_f, hx26_f, hfp_f, hPf⟩
  refine ⟨hsp_f, hspA_f, hx19_f, hx20_f,
    hx23_f.trans hx23_3, hx25_f.trans hx25_3, hx26_f.trans hx26_3, hfp_f.trans hfp_3,
    Entails.trans hPf ?_⟩
  dsimp only [R4]; sep_frame

/-! ## 4. Composed `Seg3` `IND-CPA.Decrypt` (`+0x1858 → +0x39c4`) -/

private theorem inv13_refl (s : State) : Inv13Preserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem ct_split_1408 (ctA : BitVec 64) {ct : List (BitVec 8)} (hct : ct.length = 1568) :
    (ctA ↦ₛ ct) = (ctA ↦ₛ ct.take 1408) ∗ ((ctA + 1408#64) ↦ₛ ct.drop 1408) := by
  conv_lhs => rw [← List.take_append_drop 1408 ct]
  rw [pointsToBytes_append, show (ct.take 1408).length = 1408 by simp [hct]]

private theorem four_poly_entails_2048 (base : BitVec 64) (p0 p1 p2 p3 : Poly16) :
    PolyMem base (polyVecNat p0) ∗ PolyMem (base + 512#64) (polyVecNat p1) ∗
      PolyMem (base + 1024#64) (polyVecNat p2) ∗ PolyMem (base + 1536#64) (polyVecNat p3) ⊢
      memRegion base 2048 := by
  dsimp only [PolyMem]
  have hm0 := vecRangeMem_entails_memRegion 32 base (polyVecNat p0)
  have hm1 := vecRangeMem_entails_memRegion 32 (base + 512#64) (polyVecNat p1)
  have hm2 := vecRangeMem_entails_memRegion 32 (base + 1024#64) (polyVecNat p2)
  have hm3 := vecRangeMem_entails_memRegion 32 (base + 1536#64) (polyVecNat p3)
  rw [memRegion_split' (b := base) (b' := base + 512#64) (n := 512) (k := (1536 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := base + 512#64) (b' := base + 1024#64) (n := 512) (k := (1024 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := base + 1024#64) (b' := base + 1536#64) (n := 512) (k := (512 : Nat)) rfl (by bv_omega) (by decide)]
  exact entails_sub hm0 (by sep_frame)
    (entails_sub hm1 (by sep_frame) (entails_sub hm2 (by sep_frame) (entails_sub hm3 (by sep_frame) (by sep_frame))))

/-- Segment 3 (`+0x1858 → +0x39c4`): computes `m' = indCpaDecrypt 4 11 5 (sk.take 1536) ct`
    into `[sp + 28368, sp + 28400)` while reclaiming `uHat[0..3]` and `sHat[0..3]` stack buffers. -/
theorem seg3_decrypt_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) {sk ct : List (BitVec 8)} (hct : ct.length = 1568)
    (Rest : SepProp)
    (hpc : s.pc = b + off1858) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let s0p := tHatPoly16 (sk.take 384)
    let s1p := tHatPoly16 ((sk.drop 384).take 384)
    let s2p := tHatPoly16 ((sk.drop 768).take 384)
    let s3p := tHatPoly16 ((sk.drop 1152).take 384)
    let u0 := uHatPoly16 (ct.take 352)
    let u1 := uHatPoly16 ((ct.drop 352).take 352)
    let u2 := uHatPoly16 ((ct.drop 704).take 352)
    let u3 := uHatPoly16 ((ct.drop 1056).take 352)
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off39c4) s
      (stackAt sp 1136 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        memRegion (sp + 2096#64) 336 ∗
        PolyMem (sp + 4160#64) (polyVecNat u0) ∗ PolyMem (sp + 4672#64) (polyVecNat u1) ∗
        PolyMem (sp + 5184#64) (polyVecNat u2) ∗ PolyMem (sp + 5696#64) (polyVecNat u3) ∗
        memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 26320#64) 512 ∗
        memRegion (sp + 28368#64) 512 ∗
        PolyMem (sp + 30448#64) (polyVecNat s0p) ∗ PolyMem (sp + 30960#64) (polyVecNat s1p) ∗
        PolyMem (sp + 31472#64) (polyVecNat s2p) ∗ PolyMem (sp + 31984#64) (polyVecNat s3p) ∗
        (ctA ↦ₛ ct) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x23 = ctA ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ stackAt sp 1136 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
          memRegion (sp + 2096#64) 336 ∗ memRegion (sp + 4160#64) 2048 ∗
          memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 26320#64) 512 ∗
          ((sp + 28368#64) ↦ₛ indCpaDecrypt 4 11 5 (sk.take 1536) ct) ∗
          memRegion (sp + 28400#64) 480 ∗ memRegion (sp + 30448#64) 2048 ∗
          (ctA ↦ₛ ct) ∗ Rest)) := by
  intro s0p s1p s2p s3p u0 u1 u2 u3
  have hct2 : (ct.drop 1408).length = 160 := by simp [hct]
  have h14_split : memRegion (sp + 14432#64) 512 =
      memRegion (sp + 14432#64) 32 ∗ memRegion (sp + 14464#64) 480 :=
    memRegion_split' (b := sp + 14432#64) (b' := sp + 14464#64) (n := 32) (k := (480 : Nat))
      rfl (by bv_omega) (by decide)
  set R_dec := memRegion (sp + 2096#64) 336 ∗
    PolyMem (sp + 4160#64) (polyVecNat u0) ∗ PolyMem (sp + 4672#64) (polyVecNat u1) ∗
    PolyMem (sp + 5184#64) (polyVecNat u2) ∗ PolyMem (sp + 5696#64) (polyVecNat u3) ∗
    memRegion (sp + 14464#64) 480 ∗ memRegion (sp + 28368#64) 512 ∗
    PolyMem (sp + 30448#64) (polyVecNat s0p) ∗ PolyMem (sp + 30960#64) (polyVecNat s1p) ∗
    PolyMem (sp + 31472#64) (polyVecNat s2p) ∗ PolyMem (sp + 31984#64) (polyVecNat s3p) ∗
    (ctA ↦ₛ ct.take 1408) ∗ Rest
  have hP0 : stackAt sp 1136 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
      memRegion (sp + 2096#64) 336 ∗
      PolyMem (sp + 4160#64) (polyVecNat u0) ∗ PolyMem (sp + 4672#64) (polyVecNat u1) ∗
      PolyMem (sp + 5184#64) (polyVecNat u2) ∗ PolyMem (sp + 5696#64) (polyVecNat u3) ∗
      memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 26320#64) 512 ∗
      memRegion (sp + 28368#64) 512 ∗
      PolyMem (sp + 30448#64) (polyVecNat s0p) ∗ PolyMem (sp + 30960#64) (polyVecNat s1p) ∗
      PolyMem (sp + 31472#64) (polyVecNat s2p) ∗ PolyMem (sp + 31984#64) (polyVecNat s3p) ∗
      (ctA ↦ₛ ct) ∗ Rest ⊢
      stackAt sp 1136 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
      memRegion (sp + 14432#64) 32 ∗ memRegion (sp + 26320#64) 512 ∗
      ((ctA + 1408#64) ↦ₛ ct.drop 1408) ∗ R_dec := by
    dsimp only [R_dec]; rw [h14_split, ct_split_1408 ctA hct]; sep_frame
  refine SepWP.weaken_pre hP0
    (sepWP_seq_env hcl hro
      (seg3_decompress5_fp_ok hb hbase s sp ctA (ct.drop 1408) R_dec hpc hrun hsp hspA hcl hct2) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx23_1, hx25_1, hx26_1, hfp_1, hP1⟩
  set vPoly16 := decompressPoly16 5 (ct.drop 1408)
  set R_dot := stackAt sp 1136 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
    PolyMem (sp + 26320#64) (polyVecNat vPoly16) ∗ (ctA ↦ₛ ct) ∗ Rest
  have hP1' : P1 ⊢ memRegion (sp + 2096#64) 336 ∗ memRegion (sp + 28368#64) 512 ∗
      memRegion (sp + 14432#64) 512 ∗
      (PolyMem (sp + 30448#64) (polyVecNat s0p) ∗ PolyMem (sp + 30960#64) (polyVecNat s1p) ∗
        PolyMem (sp + 31472#64) (polyVecNat s2p) ∗ PolyMem (sp + 31984#64) (polyVecNat s3p) ∗
        PolyMem (sp + 4160#64) (polyVecNat u0) ∗ PolyMem (sp + 4672#64) (polyVecNat u1) ∗
        PolyMem (sp + 5184#64) (polyVecNat u2) ∗ PolyMem (sp + 5696#64) (polyVecNat u3) ∗ R_dot) := by
    refine Entails.trans hP1 ?_
    dsimp only [R_dec, R_dot, vPoly16]; rw [h14_split, ct_split_1408 ctA hct]; sep_frame
  refine SepWP.weaken_pre hP1' ?_
  apply LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.SepWP.of_memRegion_vecRangeMem
    21 (sp + 2096#64); intro f21
  rw [← spill21Mem_ofFn (sp + 2096#64) f21]
  sep_frame_apply (sepWP_elim_poly32 (ptr := sp + 28368#64)); intro v28
  sep_frame_apply (sepWP_elim_poly32 (ptr := sp + 14432#64)); intro v14
  have hreord_dot : Poly32Mem (sp + 14432#64) v14 ∗
      (Poly32Mem (sp + 28368#64) v28 ∗
        (Spill21Mem (sp + 2096#64) (Spill21.ofFn f21) ∗
          (PolyMem (sp + 30448#64) (polyVecNat s0p) ∗ PolyMem (sp + 30960#64) (polyVecNat s1p) ∗
            PolyMem (sp + 31472#64) (polyVecNat s2p) ∗ PolyMem (sp + 31984#64) (polyVecNat s3p) ∗
            PolyMem (sp + 4160#64) (polyVecNat u0) ∗ PolyMem (sp + 4672#64) (polyVecNat u1) ∗
            PolyMem (sp + 5184#64) (polyVecNat u2) ∗ PolyMem (sp + 5696#64) (polyVecNat u3) ∗ R_dot))) ⊢
      Spill21Mem (sp + 2096#64) (Spill21.ofFn f21) ∗
        PolyMem (sp + 30448#64) (polyVecNat s0p) ∗ PolyMem (sp + 30960#64) (polyVecNat s1p) ∗
        PolyMem (sp + 31472#64) (polyVecNat s2p) ∗ PolyMem (sp + 31984#64) (polyVecNat s3p) ∗
        PolyMem (sp + 4160#64) (polyVecNat u0) ∗ PolyMem (sp + 4672#64) (polyVecNat u1) ∗
        PolyMem (sp + 5184#64) (polyVecNat u2) ∗ PolyMem (sp + 5696#64) (polyVecNat u3) ∗
        Poly32Mem (sp + 28368#64) v28 ∗ Poly32Mem (sp + 14432#64) v14 ∗ R_dot := by sep_frame
  refine SepWP.weaken_pre hreord_dot
    (sepWP_seq_env hcl1 hro1
      (dot1_full_ok hb s1 s1 sp (Spill21.ofFn f21) s0p s1p s2p s3p u0 u1 u2 u3 v28 v14 R_dot
        hpc1 hrun1 hsp1 hspA1 hcl1 hro1 (inv13_refl s1)) ?_)
  rintro s2 _ hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hpres2, rfl⟩
  set dot := neonDot4 s0p s1p s2p s3p u0 u1 u2 u3
  have hdot_sz : dot.size = 256 := neonDot4_size s0p s1p s2p s3p u0 u1 u2 u3
  set R_inv := memRegion (sp + 4160#64) 2048 ∗ memRegion (sp + 30448#64) 2048 ∗
    memRegion (sp + 14432#64) 512 ∗ R_dot
  have hP2 : Spill21Mem (sp + 2096#64) (AccSpill21 (Spill21.ofFn f21) dot) ∗
      PolyMem (sp + 30448#64) (polyVecNat s0p) ∗ PolyMem (sp + 30960#64) (polyVecNat s1p) ∗
      PolyMem (sp + 31472#64) (polyVecNat s2p) ∗ PolyMem (sp + 31984#64) (polyVecNat s3p) ∗
      PolyMem (sp + 4160#64) (polyVecNat u0) ∗ PolyMem (sp + 4672#64) (polyVecNat u1) ∗
      PolyMem (sp + 5184#64) (polyVecNat u2) ∗ PolyMem (sp + 5696#64) (polyVecNat u3) ∗
      PolyMem (sp + 28368#64) (polyVecNat dot) ∗
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (Spec.neonPolyNttMul16 s3p u3))) ∗ R_dot ⊢
      PolyMem (sp + 28368#64) (polyVecNat dot) ∗
      (Spill21Mem (sp + 2096#64) (AccSpill21 (Spill21.ofFn f21) dot) ∗ R_inv) := by
    dsimp only [R_inv]
    have hu_reg : PolyMem (sp + 4160#64) (polyVecNat u0) ∗ PolyMem (sp + 4672#64) (polyVecNat u1) ∗
        PolyMem (sp + 5184#64) (polyVecNat u2) ∗ PolyMem (sp + 5696#64) (polyVecNat u3) ⊢
        memRegion (sp + 4160#64) 2048 := by
      simpa [show sp + 4160#64 + 512#64 = sp + 4672#64 by bv_omega,
        show sp + 4160#64 + 1024#64 = sp + 5184#64 by bv_omega,
        show sp + 4160#64 + 1536#64 = sp + 5696#64 by bv_omega] using
        four_poly_entails_2048 (sp + 4160#64) u0 u1 u2 u3
    have hs_reg : PolyMem (sp + 30448#64) (polyVecNat s0p) ∗ PolyMem (sp + 30960#64) (polyVecNat s1p) ∗
        PolyMem (sp + 31472#64) (polyVecNat s2p) ∗ PolyMem (sp + 31984#64) (polyVecNat s3p) ⊢
        memRegion (sp + 30448#64) 2048 := by
      simpa [show sp + 30448#64 + 512#64 = sp + 30960#64 by bv_omega,
        show sp + 30448#64 + 1024#64 = sp + 31472#64 by bv_omega,
        show sp + 30448#64 + 1536#64 = sp + 31984#64 by bv_omega] using
        four_poly_entails_2048 (sp + 30448#64) s0p s1p s2p s3p
    have h14_reg : Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (Spec.neonPolyNttMul16 s3p u3))) ⊢
        memRegion (sp + 14432#64) 512 := by
      rw [poly32Mem_ofFn]
      exact vecRangeMem_entails_memRegion 32 (sp + 14432#64) _
    exact entails_sub hu_reg (by sep_frame)
      (entails_sub hs_reg (by sep_frame) (entails_sub h14_reg (by sep_frame) (by sep_frame)))
  refine SepWP.weaken_pre hP2
    (sepWP_seq_env hcl2 hro2
      (inv1_low_ok hb s2 sp hdot_sz _ hpc2 hrun2 hsp2 hspA2 hcl2 hro2) ?_)
  rintro s3 _ hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hpres3, rfl⟩
  have hP3 : PolyMem (sp + 28368#64) (polyVecNat (lowerInvNtt16 dot)) ∗
      (Spill21Mem (sp + 2096#64) (AccSpill21 (Spill21.ofFn f21) dot) ∗ R_inv) ⊢
      Spill21Mem (sp + 2096#64) (AccSpill21 (Spill21.ofFn f21) dot) ∗
      PolyMem (sp + 28368#64) (polyVecNat (lowerInvNtt16 dot)) ∗ R_inv := by sep_frame
  refine SepWP.weaken_pre hP3
    (sepWP_seq_env hcl3 hro3
      (seg3_inv_upper_ok s3 sp hdot_sz _ R_inv hpc3 hrun3 hsp3 hspA3) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspA4, hx0_4, hx1_4, hx2_4, hx19_4, hx23_4, hx25_4, hx26_4, hfp_4, sp40, hs14, hs19, hP4⟩
  set inv := neonInvNttMontgomery16 dot
  set R_sub := memRegion (sp + 4160#64) 2048 ∗ memRegion (sp + 30448#64) 2048 ∗
    stackAt sp 1136 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗ (ctA ↦ₛ ct) ∗ Rest
  have hP4' : P4 ⊢ SpillSliceMem 21 (sp + 2096#64) sp40 ∗ memRegion (sp + 14432#64) 512 ∗
      PolyMem (sp + 26320#64) (polyVecNat vPoly16) ∗
      PolyMem (sp + 28368#64) (polyVecNat inv) ∗ R_sub := by
    refine Entails.trans hP4 ?_; dsimp only [R_inv, R_dot, R_sub, inv]; sep_frame
  refine SepWP.weaken_pre hP4'
    (sepWP_seq_env hcl4 hro4
      (seg3_sub_ok hb hbase s4 sp sp40 inv vPoly16 R_sub
        hpc4 hrun4 hsp4 hspA4 hx0_4 hx1_4 hx2_4 hx19_4 hs14 hs19 hcl4 hro4) ?_)
  rintro s5 P5 hpc5 hrun5 hcl5 hro5
    ⟨hsp5, hspA5, hx19_5, hx20_5, hx23_5, hx25_5, hx26_5, hfp_5, hP5⟩
  obtain ⟨hv_sz, hinv_sz, hv_bnd, hv_rep, hn_bnd, hn_rep, hdec_eq⟩ := seg3_decrypt_pure (sk := sk) hct
  set w := seg3SubPoly inv vPoly16
  set R_ser := memRegion (sp + 2096#64) 336 ∗ memRegion (sp + 26320#64) 512 ∗ R_sub
  have hP5' : P5 ⊢ PolyMem (sp + 28368#64) (polyVecNat w) ∗
      PolyMem (sp + 14432#64) (polyVecNat w) ∗ R_ser := by
    refine Entails.trans hP5 ?_; dsimp only [R_ser, w]; sep_frame
  refine SepWP.weaken_pre hP5'
    (SepWP.mono
      (seg3_ser1_ok hb hbase s5 s5 sp hv_sz hinv_sz hv_bnd hv_rep hn_bnd hn_rep R_ser
        hpc5 hrun5 hsp5 hspA5 hcl5 hro5 hx19_5 hx20_5 (inv13_refl s5)) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hpres_f, hPf⟩
  refine ⟨hsp_f, hspA_f,
    hpres_f.x23.trans (hx23_5.trans (hx23_4.trans (hpres3.x23.trans (hpres2.x23.trans hx23_1)))),
    hpres_f.x25.trans (hx25_5.trans (hx25_4.trans (hpres3.x25.trans (hpres2.x25.trans hx25_1)))),
    hpres_f.x26.trans (hx26_5.trans (hx26_4.trans (hpres3.x26.trans (hpres2.x26.trans hx26_1)))),
    hpres_f.fp.trans (hfp_5.trans (hfp_4.trans (hpres3.fp.trans (hpres2.fp.trans hfp_1)))),
    Entails.trans hPf ?_⟩
  rw [hdec_eq]
  dsimp only [R_ser, R_sub, PolyMem]
  have h14w := vecRangeMem_entails_memRegion 32 (sp + 14432#64) (polyVecNat w)
  exact entails_sub h14w (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3Decrypt

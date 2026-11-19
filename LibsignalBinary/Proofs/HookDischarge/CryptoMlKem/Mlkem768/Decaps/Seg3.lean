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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3c -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2c
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3b

/-!
# `decapsulate_compressed_key` (`B04`) — Composed Segments 1–3 (`+0x0000 → +0x39f4`)

Composes `seg2_ok`, `seg3a_ok`, `seg3b_ok`, and `seg3_ser1_ok`, proving that `sp + 20704` holds
`m' = Spec.indCpaDecrypt 3 10 4 (dk.take 1152) (ct1 ++ ct2)` (`32` B).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 byteDecodeMod byteDecodeRaw compressAndEncode decodeAndDecompress indCpaDecrypt
  mlkemQ neonInvNttMontgomery16 neonMontgomeryMul16 polyInvNtt polyNtt polySub vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonPolyNtt16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents neonVecDotNtt3_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt (
  byteDecodeMod_canonical neonPolyInvNttFromMontInv16 neonPolyInvNttFromMontInv16_spec
  polyInvNtt_canonical vecDotNtt_canonical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (byteDecodeRaw_lt_two_pow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (tHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (neonDot3)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem Vec128At polyVecNat vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  SavedFrame04 blkPC04 blkPl04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  Spill21Mem spill21Mem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b (cst16_3_val)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1c (uHatZetaSpill21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2Simd (
  decompPoly16_spec uHatPoly16 uPoly16 vPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2c (Seg2Spatial seg2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3a (seg3a_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3b (seg3SubPoly seg3b_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3c (
  offSeg3cEnd seg3_ser1_ok)


/-! ## 1. Pure Soundness Bridges to `Spec.indCpaDecrypt 3 10 4` -/

private theorem toInt_ofNat16_of_lt {c : Nat} (hc : c < 4096) :
    (BitVec.ofNat 16 c).toInt = (c : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem tHatPoly16_spec (bs : List (BitVec 8)) :
    PolyBounded16 4095 (tHatPoly16 bs) ∧ PolyRepresents (tHatPoly16 bs) (byteDecodeMod 12 bs) := by
  have hraw_sz : (byteDecodeRaw 12 bs).size = 256 := by simp [byteDecodeRaw]
  have ht_sz : (tHatPoly16 bs).size = 256 := by simp [tHatPoly16, hraw_sz]
  refine ⟨⟨ht_sz, fun i hi => ?_⟩, ⟨ht_sz, fun i hi => ?_⟩⟩
  · have hlt := byteDecodeRaw_lt_two_pow 12 (by decide) bs i hi
    have hget : (tHatPoly16 bs).getD i 0#16 = BitVec.ofNat 16 ((byteDecodeRaw 12 bs).getD i 0) := by
      simp [tHatPoly16, Array.getD, hraw_sz, hi]
    rw [hget, toInt_ofNat16_of_lt hlt]
    omega
  · have hlt := byteDecodeRaw_lt_two_pow 12 (by decide) bs i hi
    have hget1 : (tHatPoly16 bs).getD i 0#16 = BitVec.ofNat 16 ((byteDecodeRaw 12 bs).getD i 0) := by
      simp [tHatPoly16, Array.getD, hraw_sz, hi]
    have hget2 : (byteDecodeMod 12 bs).getD i 0 = (byteDecodeRaw 12 bs).getD i 0 % mlkemQ := by
      simp [byteDecodeMod, Array.getD, hraw_sz, hi]
    rw [hget1, hget2, toInt_ofNat16_of_lt hlt]
    dsimp only [mlkemQ]
    omega

private theorem uHatPoly16_spec (ct1 : List (BitVec 8)) (idx : Nat) :
    let uSpec := polyNtt (decodeAndDecompress 10 ((ct1.drop (320 * idx)).take 320))
    uSpec.size = 256 ∧
    PolyBounded16 4095 (uHatPoly16 ct1 idx) ∧
    PolyRepresents (uHatPoly16 ct1 idx) uSpec := by
  dsimp only [uHatPoly16, uPoly16]
  set bs := (ct1.drop (320 * idx)).take 320
  obtain ⟨hb, hr⟩ := decompPoly16_spec (d := 10) bs (by decide)
  have hdec_sz : (decodeAndDecompress 10 bs).size = 256 := by
    simp [decodeAndDecompress, byteDecodeRaw]
  obtain ⟨hntt_sz, hb_ntt, hr_ntt⟩ := neonPolyNtt16_spec hb hr hdec_sz
  exact ⟨hntt_sz, ⟨hb_ntt.1, fun i hi => by have := hb_ntt.2 i hi; omega⟩, hr_ntt⟩

private theorem dk_slice_eq {dk : List (BitVec 8)} (i : Nat) (hi : i < 3) :
    ((dk.take 1152).drop (384 * i)).take 384 = (dk.drop (384 * i)).take 384 := by
  rw [List.drop_take, List.take_take]
  congr 1
  omega

private theorem ct1_slice_eq {ct1 ct2 : List (BitVec 8)} (hct1 : ct1.length = 960)
    (i : Nat) (hi : i < 3) :
    (((ct1 ++ ct2).drop (i * 320)).take 320) = (ct1.drop (320 * i)).take 320 := by
  rw [Nat.mul_comm i 320, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp [hct1]; omega)]

private theorem ct2_slice_eq {ct1 ct2 : List (BitVec 8)}
    (hct1 : ct1.length = 960) (hct2 : ct2.length = 128) :
    ((ct1 ++ ct2).drop 960).take 128 = ct2 := by
  rw [← hct1, List.drop_left, ← hct2, List.take_length]

/-! ## 2. Stack Decompositions & Composed `seg3_ok` (`+0x0000 → +0x39f4`) -/

@[expose] def Seg3Spatial (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 25824#64
  let m' := indCpaDecrypt 3 10 4 (dk.take 1152) (ct1 ++ ct2)
  stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗ memRegion sp 136 ∗ ((sp + 136#64) ↦₆₄ ret) ∗
  memRegion (sp + 144#64) 56 ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗ memRegion (sp + 208#64) 1632 ∗
  ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗ memRegion (sp + 1848#64) 8 ∗
  ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗ memRegion (sp + 1864#64) 8 ∗ ((sp + 1872#64) ↦₆₄ dkA) ∗
  memRegion (sp + 1880#64) 8 ∗ ((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗ memRegion (sp + 1896#64) 8 ∗
  Vec128At (sp + 1904#64) cst16_3_val ∗ memRegion (sp + 1920#64) 336 ∗
  ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗ ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
  memRegion (sp + 4432#64) 16272 ∗ ((sp + 20704#64) ↦ₛ m') ∗ memRegion (sp + 20736#64) 4928 ∗
  (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F

private theorem memRegion_11952_seg3_split (sp : BitVec 64) :
    memRegion (sp + 7216#64) 11952 =
      memRegion (sp + 7216#64) 4640 ∗ memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 12368#64) 6800 := by
  rw [memRegion_split' (b := sp + 7216#64) (b' := sp + 11856#64) (n := 4640) (k := (7312 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 11856#64) (b' := sp + 12368#64) (n := 512) (k := (6800 : Nat)) rfl (by bv_omega) (by decide)]

private theorem memRegion_2720_seg3_split (sp : BitVec 64) :
    memRegion (sp + 19680#64) 2720 =
      memRegion (sp + 19680#64) 1024 ∗ memRegion (sp + 20704#64) 512 ∗ memRegion (sp + 21216#64) 1184 := by
  rw [memRegion_split' (b := sp + 19680#64) (b' := sp + 20704#64) (n := 1024) (k := (1696 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 20704#64) (b' := sp + 21216#64) (n := 512) (k := (1184 : Nat)) rfl (by bv_omega) (by decide)]

private theorem memRegion_16272_seg3_join (sp : BitVec 64) :
    memRegion (sp + 4432#64) 1248 ∗ memRegion (sp + 5680#64) 512 ∗
      memRegion (sp + 6192#64) 512 ∗ memRegion (sp + 6704#64) 512 ∗
      memRegion (sp + 7216#64) 4640 ∗ memRegion (sp + 11856#64) 512 ∗
      memRegion (sp + 12368#64) 6800 ∗ memRegion (sp + 19168#64) 512 ∗
      memRegion (sp + 19680#64) 1024 =
      memRegion (sp + 4432#64) 16272 := by
  rw [memRegion_split' (b := sp + 4432#64) (b' := sp + 5680#64) (n := 1248) (k := (15024 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 5680#64) (b' := sp + 6192#64) (n := 512) (k := (14512 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 6192#64) (b' := sp + 6704#64) (n := 512) (k := (14000 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 6704#64) (b' := sp + 7216#64) (n := 512) (k := (13488 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 7216#64) (b' := sp + 11856#64) (n := 4640) (k := (8848 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 11856#64) (b' := sp + 12368#64) (n := 512) (k := (8336 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 12368#64) (b' := sp + 19168#64) (n := 6800) (k := (1536 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 19168#64) (b' := sp + 19680#64) (n := 512) (k := (1024 : Nat)) rfl (by bv_omega) (by decide)]

private theorem memRegion_4928_seg3_join (sp : BitVec 64) :
    memRegion (sp + 20736#64) 480 ∗ memRegion (sp + 21216#64) 1184 ∗
      memRegion (sp + 22400#64) 512 ∗ memRegion (sp + 22912#64) 512 ∗
      memRegion (sp + 23424#64) 512 ∗ memRegion (sp + 23936#64) 1728 =
      memRegion (sp + 20736#64) 4928 := by
  rw [memRegion_split' (b := sp + 20736#64) (b' := sp + 21216#64) (n := 480) (k := (4448 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 21216#64) (b' := sp + 22400#64) (n := 1184) (k := (3264 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22400#64) (b' := sp + 22912#64) (n := 512) (k := (2752 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22912#64) (b' := sp + 23424#64) (n := 512) (k := (2240 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 23424#64) (b' := sp + 23936#64) (n := 512) (k := (1728 : Nat)) rfl (by bv_omega) (by decide)]

private theorem decrypt_spec_eq (dk ct1 ct2 : List (BitVec 8))
    (hct1 : ct1.length = 960) (hct2 : ct2.length = 128) :
    let sHat0 := tHatPoly16 (dk.take 384)
    let sHat1 := tHatPoly16 ((dk.drop 384).take 384)
    let sHat2 := tHatPoly16 ((dk.drop 768).take 384)
    let uHat0 := uHatPoly16 ct1 0
    let uHat1 := uHatPoly16 ct1 1
    let uHat2 := uHatPoly16 ct1 2
    let dot := neonDot3 sHat0 sHat1 sHat2 uHat0 uHat1 uHat2
    let inv := neonInvNttMontgomery16 dot
    let vP := vPoly16 ct2
    ∃ (vSpec invSpec : Poly),
      vSpec.size = 256 ∧ invSpec.size = 256 ∧
      (∀ i, i < 256 → -3329 ≤ (vP.getD i 0#16).toInt ∧ (vP.getD i 0#16).toInt < 3329) ∧
      (∀ i, i < 256 → (vP.getD i 0#16).toInt % 3329 = (vSpec.getD i 0 : Int) % 3329) ∧
      (∀ i, i < 256 →
        -2496 ≤ (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ∧
        (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ≤ 2496) ∧
      (∀ i, i < 256 →
        (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt % 3329 = (invSpec.getD i 0 : Int) % 3329) ∧
      compressAndEncode 1 (polySub vSpec invSpec) =
        indCpaDecrypt 3 10 4 (dk.take 1152) (ct1 ++ ct2) := by
  dsimp only
  set skPke := dk.take 1152
  set ct := ct1 ++ ct2
  set sArr : Array Poly := Array.ofFn (n := 3) fun ⟨i, _⟩ => byteDecodeMod 12 ((skPke.drop (384 * i)).take 384)
  set uArr : Array Poly := Array.ofFn (n := 3) fun ⟨i, _⟩ => polyNtt (decodeAndDecompress 10 ((ct.drop (i * 320)).take 320))
  set vSpec : Poly := decodeAndDecompress 4 ((ct.drop 960).take 128)
  set invSpec : Poly := polyInvNtt (vecDotNtt 3 sArr uArr)
  obtain ⟨hs0_b, hs0_r⟩ := tHatPoly16_spec (dk.take 384)
  obtain ⟨hs1_b, hs1_r⟩ := tHatPoly16_spec ((dk.drop 384).take 384)
  obtain ⟨hs2_b, hs2_r⟩ := tHatPoly16_spec ((dk.drop 768).take 384)
  obtain ⟨_, hu0_b, hu0_r⟩ := uHatPoly16_spec ct1 0
  obtain ⟨_, hu1_b, hu1_r⟩ := uHatPoly16_spec ct1 1
  obtain ⟨_, hu2_b, hu2_r⟩ := uHatPoly16_spec ct1 2
  have hs0_eq : sArr.getD 0 zeroPoly = byteDecodeMod 12 (dk.take 384) := by
    simpa [sArr, skPke, Array.getD] using congrArg (byteDecodeMod 12) (dk_slice_eq (dk := dk) 0 (by decide))
  have hs1_eq : sArr.getD 1 zeroPoly = byteDecodeMod 12 ((dk.drop 384).take 384) := by
    simp [sArr, skPke, Array.getD, dk_slice_eq 1 (by decide)]
  have hs2_eq : sArr.getD 2 zeroPoly = byteDecodeMod 12 ((dk.drop 768).take 384) := by
    simp [sArr, skPke, Array.getD, dk_slice_eq 2 (by decide)]
  have hu0_eq : uArr.getD 0 zeroPoly = polyNtt (decodeAndDecompress 10 ((ct1.drop 0).take 320)) := by
    simpa [uArr, ct, Array.getD] using
      congrArg (fun bs => polyNtt (decodeAndDecompress 10 bs)) (ct1_slice_eq (ct2 := ct2) hct1 0 (by decide))
  have hu1_eq : uArr.getD 1 zeroPoly = polyNtt (decodeAndDecompress 10 ((ct1.drop 320).take 320)) := by
    simp [uArr, ct, Array.getD, ct1_slice_eq hct1 1 (by decide)]
  have hu2_eq : uArr.getD 2 zeroPoly = polyNtt (decodeAndDecompress 10 ((ct1.drop 640).take 320)) := by
    simp [uArr, ct, Array.getD, ct1_slice_eq hct1 2 (by decide)]
  obtain ⟨hdot_b, hdot_r⟩ := neonVecDotNtt3_spec hs0_b hs1_b hs2_b hu0_b hu1_b hu2_b
    (hs0_eq ▸ hs0_r) (hs1_eq ▸ hs1_r) (hs2_eq ▸ hs2_r)
    (hu0_eq ▸ hu0_r) (hu1_eq ▸ hu1_r) (hu2_eq ▸ hu2_r)
  have hdot_b8704 : PolyBounded16 8704 (neonDot3 (tHatPoly16 (dk.take 384))
      (tHatPoly16 ((dk.drop 384).take 384)) (tHatPoly16 ((dk.drop 768).take 384))
      (uHatPoly16 ct1 0) (uHatPoly16 ct1 1) (uHatPoly16 ct1 2)) := by
    dsimp only [neonDot3]
    exact ⟨hdot_b.1, fun j hj => by have := hdot_b.2 j hj; omega⟩
  obtain ⟨hinv_can, hinv_b, hinv_r⟩ :=
    neonPolyInvNttFromMontInv16_spec hdot_b8704 hdot_r (vecDotNtt_canonical 3 sArr uArr)
  have hsz : (neonInvNttMontgomery16 (neonDot3 (tHatPoly16 (dk.take 384))
      (tHatPoly16 ((dk.drop 384).take 384)) (tHatPoly16 ((dk.drop 768).take 384))
      (uHatPoly16 ct1 0) (uHatPoly16 ct1 1) (uHatPoly16 ct1 2))).size = 256 := by
    simpa [neonPolyInvNttFromMontInv16] using hinv_b.1
  obtain ⟨hb4, hr4⟩ := decompPoly16_spec (d := 4) ct2 (by decide)
  have hct2' : ((ct.drop 960).take 128) = ct2 := ct2_slice_eq hct1 hct2
  refine ⟨vSpec, invSpec, by simp [vSpec, decodeAndDecompress, byteDecodeRaw], hinv_can.1,
    fun i hi => by have h := hb4.2 i hi; dsimp only [vPoly16]; omega,
    fun i hi => by simpa [vPoly16, vSpec, hct2'] using hr4.2 i hi,
    fun i hi => by simpa [neonPolyInvNttFromMontInv16, Array.getD, hsz, hi] using hinv_b.2 i hi,
    fun i hi => by simpa [neonPolyInvNttFromMontInv16, invSpec, Array.getD, hsz, hi] using hinv_r.2 i hi,
    rfl⟩

/-- Composed Segments 1–3 contract (`+0x0000 → +0x39f4`). -/
theorem seg3_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro : MlKemRoOk mlkemMpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = dkA)
    (hx2 : s0.readReg64 .x2 = ct1A) (hx3 : s0.readReg64 .x3 = ct2A)
    (hdk : dk.length = 2400) (hct1 : ct1.length = 960) (hct2 : ct2.length = 128) :
    let sp := s0.sp - 25824#64
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg3cEnd) s0
      (stackAt s0.sp 26960 ∗ (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readReg64 .x23 = dkA + 384#64 ∧
        sf.readReg64 .x26 = sp + 20704#64 ∧
        sf.readReg64 .x28 = sp + 20968#64 ∧
        (Pf ⊢ Seg3Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)) := by
  intro sp
  refine sepWP_seq_env hcl hro
    (seg2_ok hb hbase s0 ret dkA ct1A ct2A dk ct1 ct2 F hpc hrun hsp0 hcl hro hx0 hx1 hx2 hx3 hdk hct1 hct2) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx26_2, hx28_2, hP2⟩
  set sHat0 := tHatPoly16 (dk.take 384)
  set sHat1 := tHatPoly16 ((dk.drop 384).take 384)
  set sHat2 := tHatPoly16 ((dk.drop 768).take 384)
  set uHat0 := uHatPoly16 ct1 0
  set uHat1 := uHatPoly16 ct1 1
  set uHat2 := uHatPoly16 ct1 2
  set vP := vPoly16 ct2
  set R3a := stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗ memRegion sp 136 ∗ ((sp + 136#64) ↦₆₄ ret) ∗
    memRegion (sp + 144#64) 56 ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗ memRegion (sp + 208#64) 1632 ∗
    ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗ memRegion (sp + 1848#64) 8 ∗
    ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗ memRegion (sp + 1864#64) 8 ∗ ((sp + 1872#64) ↦₆₄ dkA) ∗
    memRegion (sp + 1880#64) 8 ∗ memRegion (sp + 1896#64) 8 ∗
    Vec128At (sp + 1904#64) cst16_3_val ∗
    ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗ ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
    memRegion (sp + 4432#64) 1248 ∗ memRegion (sp + 7216#64) 4640 ∗ memRegion (sp + 12368#64) 6800 ∗
    PolyMem (sp + 19168#64) (polyVecNat vP) ∗ memRegion (sp + 19680#64) 1024 ∗
    memRegion (sp + 21216#64) 1184 ∗ memRegion (sp + 23936#64) 1728 ∗
    (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F
  have hP2' : P2 ⊢ ((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗ Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
      PolyMem (sp + 5680#64) (polyVecNat uHat0) ∗ PolyMem (sp + 6192#64) (polyVecNat uHat1) ∗
      PolyMem (sp + 6704#64) (polyVecNat uHat2) ∗ memRegion (sp + 11856#64) 512 ∗
      memRegion (sp + 20704#64) 512 ∗ PolyMem (sp + 22400#64) (polyVecNat sHat0) ∗
      PolyMem (sp + 22912#64) (polyVecNat sHat1) ∗ PolyMem (sp + 23424#64) (polyVecNat sHat2) ∗ R3a := by
    refine Entails.trans hP2 ?_
    dsimp only [Seg2Spatial, R3a, sp, sHat0, sHat1, sHat2, uHat0, uHat1, uHat2, vP]
    rw [memRegion_11952_seg3_split (s0.sp - 25824#64), memRegion_2720_seg3_split (s0.sp - 25824#64)]
    sep_frame
  refine SepWP.weaken_pre hP2' (sepWP_seq_env hcl2 hro2
    (seg3a_ok hb hbase s2 sp (dkA + 384#64) uHatZetaSpill21 sHat0 sHat1 sHat2 uHat0 uHat1 uHat2 R3a
      hpc2 hrun2 hsp2 hspA2 hcl2 hro2) ?_)
  rintro s3a P3a hpc3a hrun3a hcl3a hro3a
    ⟨hsp3a, hspA3a, hx0_3a, hx1_3a, hx2_3a, hx20_3a, hx23_3a, hx26_3a, hx28_3a, hfp3a,
      tOut, ht14, ht19, hP3a⟩
  set dot := neonDot3 sHat0 sHat1 sHat2 uHat0 uHat1 uHat2
  set inv := neonInvNttMontgomery16 dot
  set R3b := ((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗
    PolyMem (sp + 5680#64) (polyVecNat uHat0) ∗ PolyMem (sp + 6192#64) (polyVecNat uHat1) ∗
    PolyMem (sp + 6704#64) (polyVecNat uHat2) ∗
    PolyMem (sp + 22400#64) (polyVecNat sHat0) ∗ PolyMem (sp + 22912#64) (polyVecNat sHat1) ∗
    PolyMem (sp + 23424#64) (polyVecNat sHat2) ∗
    (stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗ memRegion sp 136 ∗ ((sp + 136#64) ↦₆₄ ret) ∗
    memRegion (sp + 144#64) 56 ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗ memRegion (sp + 208#64) 1632 ∗
    ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗ memRegion (sp + 1848#64) 8 ∗
    ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗ memRegion (sp + 1864#64) 8 ∗ ((sp + 1872#64) ↦₆₄ dkA) ∗
    memRegion (sp + 1880#64) 8 ∗ memRegion (sp + 1896#64) 8 ∗
    Vec128At (sp + 1904#64) cst16_3_val ∗
    ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗ ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
    memRegion (sp + 4432#64) 1248 ∗ memRegion (sp + 7216#64) 4640 ∗ memRegion (sp + 12368#64) 6800 ∗
    memRegion (sp + 19680#64) 1024 ∗ memRegion (sp + 21216#64) 1184 ∗ memRegion (sp + 23936#64) 1728 ∗
    (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F)
  have hP3a' : P3a ⊢ Spill21Mem (sp + 1920#64) tOut ∗ memRegion (sp + 11856#64) 512 ∗
      PolyMem (sp + 19168#64) (polyVecNat vP) ∗ PolyMem (sp + 20704#64) (polyVecNat inv) ∗ R3b := by
    refine Entails.trans hP3a ?_
    dsimp only [R3a, R3b, inv, dot]; sep_frame
  refine SepWP.weaken_pre hP3a' (sepWP_seq_env hcl3a hro3a
    (seg3b_ok hb hbase s3a sp tOut inv vP R3b
      hpc3a hrun3a hsp3a hspA3a hx0_3a hx1_3a hx2_3a hx20_3a ht14 ht19 hcl3a hro3a) ?_)
  rintro s3b P3b hpc3b hrun3b hcl3b hro3b
    ⟨hsp3b, hspA3b, hx20_3b, hx21_3b, hx23_3b, hx26_3b, hx28_3b, hfp3b, hP3b⟩
  obtain ⟨vSpec, invSpec, hv_sz, hinv_sz, hv_bnd, hv_rep, hn_bnd, hn_rep, hm'_eq⟩ :=
    decrypt_spec_eq dk ct1 ct2 hct1 hct2
  set w := seg3SubPoly inv vP
  set R3c := Spill21Mem (sp + 1920#64) tOut ∗ PolyMem (sp + 19168#64) (polyVecNat vP) ∗ R3b
  have hP3b' : P3b ⊢ PolyMem (sp + 20704#64) (polyVecNat w) ∗
      PolyMem (sp + 11856#64) (polyVecNat w) ∗ R3c := by
    refine Entails.trans hP3b ?_
    dsimp only [R3c, w]; sep_frame
  refine SepWP.weaken_pre hP3b'
    (SepWP.mono (seg3_ser1_ok hb hbase s3b sp hv_sz hinv_sz hv_bnd hv_rep hn_bnd hn_rep R3c
      hpc3b hrun3b hsp3b hspA3b hcl3b hro3b hx20_3b hx21_3b) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx23_f, hx26_f, hx28_f, hfp_f, hPf⟩
  refine ⟨hsp_f, hspA_f,
    hfp_f.trans (hfp3b.trans (hfp3a.trans hfp2)),
    hx23_f.trans (hx23_3b.trans hx23_3a),
    hx26_f.trans (hx26_3b.trans (hx26_3a.trans hx26_2)),
    hx28_f.trans (hx28_3b.trans (hx28_3a.trans hx28_2)), ?_⟩
  refine Entails.trans hPf ?_
  rw [hm'_eq]
  dsimp only [R3c, R3b, Seg3Spatial, sp]
  have ht_m := spill21Mem_entails_memRegion (s0.sp - 25824#64 + 1920#64) tOut
  have hu0_m : PolyMem (s0.sp - 25824#64 + 5680#64) (polyVecNat uHat0) ⊢
      memRegion (s0.sp - 25824#64 + 5680#64) 512 :=
    vecRangeMem_entails_memRegion 32 (s0.sp - 25824#64 + 5680#64) (polyVecNat uHat0)
  have hu1_m : PolyMem (s0.sp - 25824#64 + 6192#64) (polyVecNat uHat1) ⊢
      memRegion (s0.sp - 25824#64 + 6192#64) 512 :=
    vecRangeMem_entails_memRegion 32 (s0.sp - 25824#64 + 6192#64) (polyVecNat uHat1)
  have hu2_m : PolyMem (s0.sp - 25824#64 + 6704#64) (polyVecNat uHat2) ⊢
      memRegion (s0.sp - 25824#64 + 6704#64) 512 :=
    vecRangeMem_entails_memRegion 32 (s0.sp - 25824#64 + 6704#64) (polyVecNat uHat2)
  have hw_m : PolyMem (s0.sp - 25824#64 + 11856#64) (polyVecNat w) ⊢
      memRegion (s0.sp - 25824#64 + 11856#64) 512 :=
    vecRangeMem_entails_memRegion 32 (s0.sp - 25824#64 + 11856#64) (polyVecNat w)
  have hv_m : PolyMem (s0.sp - 25824#64 + 19168#64) (polyVecNat vP) ⊢
      memRegion (s0.sp - 25824#64 + 19168#64) 512 :=
    vecRangeMem_entails_memRegion 32 (s0.sp - 25824#64 + 19168#64) (polyVecNat vP)
  have hs0_m : PolyMem (s0.sp - 25824#64 + 22400#64) (polyVecNat sHat0) ⊢
      memRegion (s0.sp - 25824#64 + 22400#64) 512 :=
    vecRangeMem_entails_memRegion 32 (s0.sp - 25824#64 + 22400#64) (polyVecNat sHat0)
  have hs1_m : PolyMem (s0.sp - 25824#64 + 22912#64) (polyVecNat sHat1) ⊢
      memRegion (s0.sp - 25824#64 + 22912#64) 512 :=
    vecRangeMem_entails_memRegion 32 (s0.sp - 25824#64 + 22912#64) (polyVecNat sHat1)
  have hs2_m : PolyMem (s0.sp - 25824#64 + 23424#64) (polyVecNat sHat2) ⊢
      memRegion (s0.sp - 25824#64 + 23424#64) 512 :=
    vecRangeMem_entails_memRegion 32 (s0.sp - 25824#64 + 23424#64) (polyVecNat sHat2)
  rw [← memRegion_16272_seg3_join (s0.sp - 25824#64), ← memRegion_4928_seg3_join (s0.sp - 25824#64)]
  exact entails_sub ht_m (by sep_frame)
    (entails_sub hu0_m (by sep_frame)
      (entails_sub hu1_m (by sep_frame)
        (entails_sub hu2_m (by sep_frame)
          (entails_sub hw_m (by sep_frame)
            (entails_sub hv_m (by sep_frame)
              (entails_sub hs0_m (by sep_frame)
                (entails_sub hs1_m (by sep_frame)
                  (entails_sub hs2_m (by sep_frame) (by sep_frame)))))))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3

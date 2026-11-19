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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Rhat
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Add
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Rows
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Decomp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Dot
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5InvLow
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Add
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Tail

/-!
# `kyber::encapsulate` (`B07`) — Segments 4 & 5 Composition (`+0x59d0 → ret`)

Chains `Seg4Rows`, `Seg4Compress`, `Seg5Decomp`, `Seg5Dot`, `Seg5InvLow`, `Seg5Add`,
`Seg5Compress`, and `Seg5Tail` from `Seg3Post` (`+0x59d0`) to function return (`s0.readReg64 .lr`),
reconstituting `stackAt s0.sp 34240` and identifying `(ct, ss)` with `kyber1024Encaps pk rand`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 byteDecodeMod compressAndEncode decodeAndDecompress indCpaEncryptWith
  kyber1024Encaps kyber1024EncapsWith neonBarrettReduce16 neonInvNttMontgomery16
  neonMontgomeryMul16 neonPolyNttMul16 polyAdd polyInvNtt polyNtt sampleMatrixWith sampleNtt
  samplePolyCbd2 sampleVecCbd2 sha3_256List sha3_512List shake256List vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs (
  kyber1024Encaps_eq_with sha3_256List_length sha3_512List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonBarrettReducePoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt (
  byteDecodeMod_canonical neonPolyInvNttFromMontInv16 neonPolyInvNttFromMontInv16_spec
  vecDotNtt_canonical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents neonVecDotNtt4_spec polyAdd16 polyAdd16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16 neonCbd2Poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (decodeAndDecompress_poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (byteDecodeRaw_lt_two_pow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepWP.of_memRegion_vecRangeMem Spill13Mem Vec32 poly32Mem_entails_memRegion
  poly32Mem_ofFn polyVecNat spill13Mem_entails_memRegion vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (msgPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16 lowerInvNtt16_size neonDot3 polyAdd16_size polyZero16
  upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure (upperInvNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (AccRegs AccSpill)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (seg5FinalPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul (neonDot4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  SavedFrame07 blkPC07 blkPl07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (
  SpilledMsgWords shake256List_len spilledMsgWords_entails_memRegion128 stackAt_34240_split)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  pkEk0 pkEk1 pkEk2 pkEk3 pkRho pkRho_len tHatModPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3 (
  Seg3Post Seg3Spatial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Cbd (
  ATransAt PublicKeyStateAt pkStateBytes pkStateBytes_length publicKeyStateAt_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Rhat (
  rHatPoly16 rHatPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E2 (offSeg4Start)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Add (
  offSeg4Pre offSeg4RowsEnd)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Simd (
  neonCompressSerialize11Poly neonCompressSerialize11Poly_eq neonCompressSerialize11Poly_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Rows (
  seg4_rows_ok uVecPoly16 uVecPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Compress (
  seg4_compress_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Decomp (
  offSeg5Dot offSeg5Start seg5_decomp_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Dot (
  offSeg5DotStart offSeg5InvLow ro00Sym seg5_dot_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5InvLow (
  offSeg5InvLowStart seg5_inv_low_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Add (
  offSeg5Compress offSeg5InvUpper seg5_add_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Compress (
  neonCompressSerialize5Poly neonCompressSerialize5Poly_eq neonCompressSerialize5Poly_length
  offSeg5Tail seg5_compress_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Tail (seg5_tail_ok)

/-! ## 1. Pure Output Equivalence (`(ct, ss) = kyber1024Encaps pk rand`) -/

private theorem tHatModPoly16_spec (bs : List (BitVec 8)) :
    PolyBounded16 4095 (tHatModPoly16 bs) ∧
    PolyRepresents (tHatModPoly16 bs) (byteDecodeMod 12 bs) := by
  unfold tHatModPoly16
  obtain ⟨hsz, hlt⟩ := byteDecodeMod_canonical 12 bs
  set f := byteDecodeMod 12 bs
  have hmsz : (f.map (BitVec.ofNat 16)).size = 256 := by simp [hsz]
  have hint : ∀ i < 256, ((f.map (BitVec.ofNat 16)).getD i 0#16).toInt = (f.getD i 0 : Int) := by
    intro i hi
    have hq : f.getD i 0 < 3329 := hlt i hi
    have hget : (f.map (BitVec.ofNat 16)).getD i 0#16 = BitVec.ofNat 16 (f.getD i 0) := by
      simp [Array.getD, hsz, hi]
    set c := f.getD i 0
    have hc1 : c < 65536 := by omega
    have hc2 : 2 * c < 65536 := by omega
    rw [hget, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc1]
    simp only [hc2, ↓reduceIte]
  refine ⟨⟨hmsz, fun i hi => ?_⟩, ⟨hmsz, fun i hi => ?_⟩⟩
  · have hq : f.getD i 0 < 3329 := hlt i hi
    rw [hint i hi]; omega
  · rw [hint i hi]

private theorem msgPoly16_spec (m : List (BitVec 8)) :
    PolyBounded16 3328 (msgPoly16 m) ∧
    PolyRepresents (msgPoly16 m) (decodeAndDecompress 1 m) :=
  decodeAndDecompress_poly16_spec m (.inl rfl) (byteDecodeRaw_lt_two_pow 1 (by decide) m)

private theorem seg5FinalPoly_eq_barrett_aux {inv : Poly16} (hinv : inv.size = 256)
    (e2 msgPoly : Poly16) :
    seg5FinalPoly inv e2 msgPoly =
      (polyAdd16 (polyAdd16 (inv.map (fun c => neonMontgomeryMul16 c 1441#16)) e2) msgPoly).map
        neonBarrettReduce16 := by
  unfold seg5FinalPoly polyAdd16
  apply Array.ext
  · simp only [Array.size_ofFn, Array.size_map]
  · intro i hi1 _
    have hi : i < 256 := by simpa only [Array.size_ofFn] using hi1
    have hi' : i < inv.size := hinv ▸ hi
    have hofFn : ∀ (g : Fin 256 → BitVec 16), (Array.ofFn g).getD i 0#16 = g ⟨i, hi⟩ :=
      fun g => by
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some]
    have hmap : ∀ (f : BitVec 16 → BitVec 16), (inv.map f).getD i 0#16 = f (inv.getD i 0#16) :=
      fun f => by
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem, hi',
          Option.map_some, Option.getD_some]
    simp only [Array.getElem_ofFn, Array.getElem_map, hofFn, hmap, BitVec.add_assoc]

private theorem seg5FinalPoly_eq_barrett {dot : Poly16} (hdot : dot.size = 256)
    (e2 msgPoly : Poly16) :
    seg5FinalPoly (neonInvNttMontgomery16 dot) e2 msgPoly =
      (polyAdd16 (polyAdd16 (neonPolyInvNttFromMontInv16 dot) e2) msgPoly).map neonBarrettReduce16 := by
  have hinv : (neonInvNttMontgomery16 dot).size = 256 := by
    rw [← upperInvNtt16_lowerInvNtt16 dot, upperInvNtt16_size]
    exact lowerInvNtt16_size hdot
  exact seg5FinalPoly_eq_barrett_aux hinv e2 msgPoly

private theorem polyBounded16_mono {b1 b2 : Int} {p : Poly16}
    (hle : b1 ≤ b2) (h : PolyBounded16 b1 p) : PolyBounded16 b2 p :=
  ⟨h.1, fun i hi => ⟨by have := (h.2 i hi).1; omega, by have := (h.2 i hi).2; omega⟩⟩

private def seg5VPoly16 (pk m coins : List (BitVec 8)) : Poly16 :=
  let dot := neonDot4
    (tHatModPoly16 (pkEk0 pk)) (tHatModPoly16 (pkEk1 pk))
    (tHatModPoly16 (pkEk2 pk)) (tHatModPoly16 (pkEk3 pk))
    (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [3#8])))
  let e2 := neonCbd2Poly16 (shake256List 128 (coins ++ [8#8]))
  seg5FinalPoly (neonInvNttMontgomery16 dot) e2 (msgPoly16 m)

section PureVPoly
attribute [local irreducible]
  shake256List byteDecodeMod decodeAndDecompress polyNtt polyInvNtt samplePolyCbd2
  tHatModPoly16 msgPoly16 neonCbd2Poly16 neonInvNttMontgomery16 neonPolyInvNttFromMontInv16
  polyAdd16 neonBarrettReduce16 polyAdd vecDotNtt

set_option maxRecDepth 4000 in
private theorem seg5VPoly16_spec {pk m coins : List (BitVec 8)}
    (hm : m.length = 32) (hcoins : coins.length = 32) :
    let tHat : Array Poly := Array.ofFn (n := 4) fun ⟨i, _⟩ =>
      byteDecodeMod 12 ((pk.drop (384 * i)).take 384)
    let rHat := (sampleVecCbd2 4 coins 0).map polyNtt
    let e2 := samplePolyCbd2 (shake256List 128 (coins.take 32 ++ [BitVec.ofNat 8 (2 * 4)]))
    let mPoly := decodeAndDecompress 1 (m.take 32)
    let vPoly := polyAdd (polyAdd (polyInvNtt (vecDotNtt 4 tHat rHat)) e2) mPoly
    PolyBounded16 1664 (seg5VPoly16 pk m coins) ∧
    PolyRepresents (seg5VPoly16 pk m coins) vPoly := by
  dsimp only; unfold seg5VPoly16
  have hd_sz : (neonDot4
      (tHatModPoly16 (pkEk0 pk)) (tHatModPoly16 (pkEk1 pk))
      (tHatModPoly16 (pkEk2 pk)) (tHatModPoly16 (pkEk3 pk))
      (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [3#8])))).size = 256 := polyAdd16_size _ _
  dsimp only [neonDot4, neonDot3] at hd_sz ⊢
  have htm : m.take 32 = m := List.take_of_length_le (Nat.le_of_eq hm)
  have htc : coins.take 32 = coins := List.take_of_length_le (Nat.le_of_eq hcoins)
  have hsh (d : BitVec 8) : (shake256List 128 (coins ++ [d])).length = 128 :=
    shake256List_len _ _
  obtain ⟨ht0_b, ht0_r⟩ := tHatModPoly16_spec (pkEk0 pk)
  obtain ⟨ht1_b, ht1_r⟩ := tHatModPoly16_spec (pkEk1 pk)
  obtain ⟨ht2_b, ht2_r⟩ := tHatModPoly16_spec (pkEk2 pk)
  obtain ⟨ht3_b, ht3_r⟩ := tHatModPoly16_spec (pkEk3 pk)
  have htg (j : Nat) (hj : j < 4) :
      (Array.ofFn (n := 4) fun ⟨i, _⟩ =>
        byteDecodeMod 12 ((pk.drop (384 * i)).take 384)).getD j zeroPoly =
        byteDecodeMod 12 ((pk.drop (384 * j)).take 384) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hj, ↓reduceDIte, Option.getD_some]
  change PolyRepresents _ (byteDecodeMod 12 ((pk.drop (384 * 0)).take 384)) at ht0_r
  change PolyRepresents _ (byteDecodeMod 12 ((pk.drop (384 * 1)).take 384)) at ht1_r
  change PolyRepresents _ (byteDecodeMod 12 ((pk.drop (384 * 2)).take 384)) at ht2_r
  change PolyRepresents _ (byteDecodeMod 12 ((pk.drop (384 * 3)).take 384)) at ht3_r
  rw [← htg 0 (by decide)] at ht0_r; rw [← htg 1 (by decide)] at ht1_r
  rw [← htg 2 (by decide)] at ht2_r; rw [← htg 3 (by decide)] at ht3_r
  obtain ⟨_, hr0_b, hr0_r⟩ := rHatPoly16_spec (hsh 0#8)
  obtain ⟨_, hr1_b, hr1_r⟩ := rHatPoly16_spec (hsh 1#8)
  obtain ⟨_, hr2_b, hr2_r⟩ := rHatPoly16_spec (hsh 2#8)
  obtain ⟨_, hr3_b, hr3_r⟩ := rHatPoly16_spec (hsh 3#8)
  have hrg (j : Nat) (hj : j < 4) :
      ((sampleVecCbd2 4 coins 0).map polyNtt).getD j zeroPoly =
        polyNtt (samplePolyCbd2 (shake256List 128 (coins ++ [BitVec.ofNat 8 j]))) := by
    unfold sampleVecCbd2
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_ofFn]
    simp only [htc, hj, Nat.zero_add, ↓reduceDIte, Option.map_some, Option.getD_some]
  rw [show (0#8 : BitVec 8) = BitVec.ofNat 8 0 from rfl, ← hrg 0 (by decide)] at hr0_r
  rw [show (1#8 : BitVec 8) = BitVec.ofNat 8 1 from rfl, ← hrg 1 (by decide)] at hr1_r
  rw [show (2#8 : BitVec 8) = BitVec.ofNat 8 2 from rfl, ← hrg 2 (by decide)] at hr2_r
  rw [show (3#8 : BitVec 8) = BitVec.ofNat 8 3 from rfl, ← hrg 3 (by decide)] at hr3_r
  obtain ⟨hdot_b, hdot_r⟩ := neonVecDotNtt4_spec ht0_b ht1_b ht2_b ht3_b
    (polyBounded16_mono (by decide) hr0_b) (polyBounded16_mono (by decide) hr1_b)
    (polyBounded16_mono (by decide) hr2_b) (polyBounded16_mono (by decide) hr3_b)
    ht0_r ht1_r ht2_r ht3_r hr0_r hr1_r hr2_r hr3_r
  obtain ⟨_, hinv_b, hinv_r⟩ := neonPolyInvNttFromMontInv16_spec
    (polyBounded16_mono (by decide) hdot_b) hdot_r (vecDotNtt_canonical 4 _ _)
  obtain ⟨he2_b, he2_r⟩ := neonCbd2Poly16_spec (hsh 8#8)
  obtain ⟨hm_b, hm_r⟩ := msgPoly16_spec m
  rw [htc, htm, show BitVec.ofNat 8 (2 * 4) = 8#8 from rfl]
  obtain ⟨ha1_b, ha1_r⟩ := polyAdd16_spec hinv_b he2_b (by decide) hinv_r he2_r
  obtain ⟨_, ha2_r⟩ := polyAdd16_spec ha1_b hm_b (by decide) ha1_r hm_r
  rw [seg5FinalPoly_eq_barrett hd_sz]
  exact neonBarrettReducePoly16_spec ha2_r

private theorem seg45_output_eq {pk rand : List (BitVec 8)}
    (hpk : pk.length = 1568) (hrnd : rand.length = 32) :
    let m := sha3_256List rand
    let hashed := sha3_512List (m ++ sha3_256List pk)
    let coins := hashed.drop 32
    let rho := pkRho pk
    let c1 :=
      neonCompressSerialize11Poly (uVecPoly16 rho coins 0) ++
      neonCompressSerialize11Poly (uVecPoly16 rho coins 1) ++
      neonCompressSerialize11Poly (uVecPoly16 rho coins 2) ++
      neonCompressSerialize11Poly (uVecPoly16 rho coins 3)
    let c2 := neonCompressSerialize5Poly (seg5VPoly16 pk m coins)
    let ct := c1 ++ c2
    let ss := shake256List 32 (hashed.take 32 ++ sha3_256List ct)
    ct = (kyber1024Encaps pk rand).1 ∧ ss = (kyber1024Encaps pk rand).2 ∧
    c1.length = 1408 ∧ c2.length = 160 ∧ ct.length = 1568 := by
  intro m hashed coins rho c1 c2 ct ss
  have hpk_take : pk.take 1568 = pk := List.take_of_length_le (Nat.le_of_eq hpk)
  have hrnd_take : rand.take 32 = rand := List.take_of_length_le (Nat.le_of_eq hrnd)
  have hm : m.length = 32 := sha3_256List_length rand
  have hhashed : hashed.length = 64 := sha3_512List_length _
  have hcoins : coins.length = 32 := by simp [coins, hhashed]
  have hcoins_take : coins.take 32 = coins := List.take_of_length_le (Nat.le_of_eq hcoins)
  have hrho : rho.length = 32 := pkRho_len hpk
  obtain ⟨hbu0, hru0⟩ := uVecPoly16_spec hrho hcoins (row := 0) (by decide)
  obtain ⟨hbu1, hru1⟩ := uVecPoly16_spec hrho hcoins (row := 1) (by decide)
  obtain ⟨hbu2, hru2⟩ := uVecPoly16_spec hrho hcoins (row := 2) (by decide)
  obtain ⟨hbu3, hru3⟩ := uVecPoly16_spec hrho hcoins (row := 3) (by decide)
  obtain ⟨hbv, hrv⟩ := seg5VPoly16_spec (pk := pk) hm hcoins
  have hc1_eq : c1 = (indCpaEncryptWith sampleNtt 4 11 5 pk m coins).1 := by
    dsimp only [c1, indCpaEncryptWith]
    have hr4 : List.range 4 = [0, 1, 2, 3] := by decide
    rw [hr4, neonCompressSerialize11Poly_eq hbu0 hru0, neonCompressSerialize11Poly_eq hbu1 hru1,
      neonCompressSerialize11Poly_eq hbu2 hru2, neonCompressSerialize11Poly_eq hbu3 hru3]
    simp [rho, pkRho, Array.getD, List.append_assoc]
  have hc2_eq : c2 = (indCpaEncryptWith sampleNtt 4 11 5 pk m coins).2.1 := by
    dsimp only [c2, indCpaEncryptWith]
    refine (neonCompressSerialize5Poly_eq hbv hrv).trans ?_
    apply congrArg (compressAndEncode 5)
    refine congrArg₂ polyAdd ?_ rfl
    refine congrArg₂ polyAdd ?_ rfl
    apply congrArg polyInvNtt
    refine congrArg₂ (vecDotNtt 4) ?_ rfl
    apply Array.ext
    · simp
    · intro i hi1 hi2
      simp
  have hct_eq : ct = (kyber1024Encaps pk rand).1 := by
    rw [kyber1024Encaps_eq_with]
    dsimp only [kyber1024EncapsWith, ct]
    rw [hpk_take, hrnd_take]
    change c1 ++ c2 =
      (indCpaEncryptWith sampleNtt 4 11 5 pk m (coins.take 32)).1 ++
      (indCpaEncryptWith sampleNtt 4 11 5 pk m (coins.take 32)).2.1
    rw [hcoins_take, hc1_eq, hc2_eq]
  have hss_eq : ss = (kyber1024Encaps pk rand).2 := by
    rw [kyber1024Encaps_eq_with]
    dsimp only [kyber1024EncapsWith, ss]
    rw [hpk_take, hrnd_take]
    change shake256List 32 (hashed.take 32 ++ sha3_256List ct) =
      shake256List 32 (hashed.take 32 ++ sha3_256List
        ((indCpaEncryptWith sampleNtt 4 11 5 pk m (coins.take 32)).1 ++
         (indCpaEncryptWith sampleNtt 4 11 5 pk m (coins.take 32)).2.1))
    rw [hcoins_take, ← hc1_eq, ← hc2_eq]
  have hc1_len : c1.length = 1408 := by simp [c1, neonCompressSerialize11Poly_length]
  have hc2_len : c2.length = 160 := by simp [c2, neonCompressSerialize5Poly_length]
  exact ⟨hct_eq, hss_eq, hc1_len, hc2_len, by simp [ct, hc1_len, hc2_len]⟩
end PureVPoly

/-! ## 2. Spatial Collapse & Stack-Frame Reconstitution Helpers -/

private theorem polyMem_entails_memRegion512 (ptr : BitVec 64) (f : Nat → BitVec 128) :
    PolyMem ptr f ⊢ memRegion ptr 512 :=
  vecRangeMem_entails_memRegion 32 ptr f

private theorem polyMem4_entails_memRegion2048 (ptr : BitVec 64)
    (f0 f1 f2 f3 : Nat → BitVec 128) :
    PolyMem ptr f0 ∗ PolyMem (ptr + 512#64) f1 ∗
      PolyMem (ptr + 1024#64) f2 ∗ PolyMem (ptr + 1536#64) f3 ⊢
      memRegion ptr 2048 := by
  rw [memRegion_split' (b := ptr) (b' := ptr + 512#64) (n := 512) (k := (1536 : Nat))
        rfl rfl (by decide),
      memRegion_split' (b := ptr + 512#64) (b' := ptr + 1024#64) (n := 512) (k := (1024 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := ptr + 1024#64) (b' := ptr + 1536#64) (n := 512) (k := 512)
        rfl (by bv_omega) (by decide)]
  exact entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
    (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
      (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
        (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame) (by sep_frame))))

private theorem publicKeyStateAt_2560_eq (sp : BitVec 64) (pk : List (BitVec 8)) :
    PublicKeyStateAt (sp + 2560#64) pk =
      ATransAt (sp + 2560#64) (pkRho pk) ∗
      PolyMem (sp + 10752#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
      PolyMem (sp + 11264#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
      PolyMem (sp + 11776#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
      PolyMem (sp + 12288#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
      ((sp + 12800#64) ↦ₛ List.replicate 32 0#8) := by
  dsimp only [PublicKeyStateAt]
  have h0 : sp + 2560#64 + 8192#64 = sp + 10752#64 := by bv_omega
  have h1 : sp + 2560#64 + 8704#64 = sp + 11264#64 := by bv_omega
  have h2 : sp + 2560#64 + 9216#64 = sp + 11776#64 := by bv_omega
  have h3 : sp + 2560#64 + 9728#64 = sp + 12288#64 := by bv_omega
  have h4 : sp + 2560#64 + BitVec.ofNat 64 10240 = sp + 12800#64 := by bv_omega
  rw [h0, h1, h2, h3, h4]

private theorem publicKeyStateAt_entails_memRegion (sp : BitVec 64) (pk : List (BitVec 8)) :
    PublicKeyStateAt (sp + 2560#64) pk ⊢ memRegion (sp + 2560#64) 10272 := by
  rw [publicKeyStateAt_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion (sp + 2560#64) (pkStateBytes pk)
  rwa [pkStateBytes_length] at h

private theorem stackAt_34240_join (sp0 : BitVec 64) :
    let sp := sp0 - 33104#64
    stackAt sp 1136 ∗ memRegion sp 32944 ∗ memRegion (sp0 - 160#64) 160 =
      stackAt sp0 34240 := by
  intro sp
  rw [stackAt_34240_split sp0,
      memRegion_split' (b := sp) (b' := sp0 - 32928#64) (n := 176) (k := (32768 : Nat))
        rfl (by dsimp only [sp]; bv_omega) (by decide)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private def Seg45Frame (sp0 : BitVec 64) (s0 : State)
    (sp ret pkA rA : BitVec 64) (pk rand hashed : List (BitVec 8)) (Rest : SepProp) : SepProp :=
  (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ stackAt sp 1136 ∗ memRegion sp 8 ∗ ((sp + 8#64) ↦₆₄ ret) ∗
  memRegion (sp + 144#64) 1344 ∗ memRegion (sp + 2432#64) 64 ∗ ((sp + 2496#64) ↦ₛ hashed) ∗
  ((sp + 12800#64) ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp + 14904#64) 8200 ∗
  memRegion (sp + 24672#64) 48 ∗ memRegion (sp + 28816#64) 32 ∗
  memRegion (sp + 32640#64) 304 ∗ SavedFrame07 sp0 s0 ∗ memRegion ret 1600 ∗ Rest

private theorem seg45Frame_eq (sp0 : BitVec 64) (s0 : State)
    (sp ret pkA rA : BitVec 64) (pk rand hashed : List (BitVec 8)) (Rest : SepProp) :
    Seg45Frame sp0 s0 sp ret pkA rA pk rand hashed Rest =
      (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ stackAt sp 1136 ∗ memRegion sp 8 ∗ ((sp + 8#64) ↦₆₄ ret) ∗
      memRegion (sp + 144#64) 1344 ∗ memRegion (sp + 2432#64) 64 ∗ ((sp + 2496#64) ↦ₛ hashed) ∗
      ((sp + 12800#64) ↦ₛ List.replicate 32 0#8) ∗ memRegion (sp + 14904#64) 8200 ∗
      memRegion (sp + 24672#64) 48 ∗ memRegion (sp + 28816#64) 32 ∗
      memRegion (sp + 32640#64) 304 ∗ SavedFrame07 sp0 s0 ∗ memRegion ret 1600 ∗ Rest :=
  rfl

attribute [local irreducible] Seg45Frame

private theorem polyMem3_entails_memRegion1536 (ptr : BitVec 64)
    (f0 f1 f2 : Nat → BitVec 128) :
    PolyMem ptr f0 ∗ PolyMem (ptr + 512#64) f1 ∗ PolyMem (ptr + 1024#64) f2 ⊢
      memRegion ptr 1536 := by
  rw [memRegion_split' (b := ptr) (b' := ptr + 512#64) (n := 512) (k := (1024 : Nat))
        rfl rfl (by decide),
      memRegion_split' (b := ptr + 512#64) (b' := ptr + 1024#64) (n := 512) (k := 512)
        rfl (by bv_omega) (by decide)]
  exact entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
    (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
      (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame) (by sep_frame)))

private theorem seg4_entry_regions (sp : BitVec 64) :
    (memRegion (sp + 2000#64) 496 =
      memRegion (sp + 2000#64) 432 ∗ memRegion (sp + 2432#64) 64) ∧
    (memRegion (sp + 12832#64) 11888 =
      memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 13344#64) 1560 ∗
      memRegion (sp + 14904#64) 8200 ∗ memRegion (sp + 23104#64) 1408 ∗
      memRegion (sp + 24512#64) 160 ∗ memRegion (sp + 24672#64) 48) ∧
    (memRegion (sp + 30896#64) 2048 =
      memRegion (sp + 30896#64) 512 ∗ memRegion (sp + 31408#64) 1232 ∗
      memRegion (sp + 32640#64) 304) := by
  refine ⟨memRegion_split' (b := sp + 2000#64) (b' := sp + 2432#64) (n := 432) (k := 64)
      rfl (by bv_omega) (by decide), ?_, ?_⟩
  · rw [memRegion_split' (b := sp + 12832#64) (b' := sp + 13344#64) (n := 512) (k := (11376 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 13344#64) (b' := sp + 14904#64) (n := (1560 : Nat)) (k := (9816 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 14904#64) (b' := sp + 23104#64) (n := (8200 : Nat)) (k := (1616 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 23104#64) (b' := sp + 24512#64) (n := (1408 : Nat)) (k := 208)
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 24512#64) (b' := sp + 24672#64) (n := 160) (k := 48)
          rfl (by bv_omega) (by decide)]
  · rw [memRegion_split' (b := sp + 30896#64) (b' := sp + 31408#64) (n := 512) (k := (1536 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 31408#64) (b' := sp + 32640#64) (n := (1232 : Nat)) (k := 304)
          rfl (by bv_omega) (by decide)]

private theorem seg45_mid_regions (sp : BitVec 64) :
    (memRegion (sp + 2000#64) 432 =
      memRegion (sp + 2000#64) 368 ∗ memRegion (sp + 2368#64) 64) ∧
    (memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 13344#64) 1560 =
      memRegion (sp + 12832#64) 2072) ∧
    (memRegion (sp + 2000#64) 432 =
      memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 2224#64) 208) ∧
    (memRegion (sp + 24720#64) 2048 =
      memRegion (sp + 24720#64) 512 ∗ memRegion (sp + 25232#64) 1536) ∧
    (memRegion (sp + 28848#64) 2048 =
      memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 29360#64) 1536) ∧
    (memRegion (sp + 31408#64) 1232 =
      memRegion (sp + 31408#64) 512 ∗ memRegion (sp + 31920#64) 720) ∧
    (memRegion (sp + 2224#64) 208 =
      memRegion (sp + 2224#64) 96 ∗ memRegion (sp + 2320#64) 112) := by
  refine ⟨memRegion_split' (b := sp + 2000#64) (b' := sp + 2368#64) (n := 368) (k := 64)
      rfl (by bv_omega) (by decide),
    (memRegion_split' (b := sp + 12832#64) (b' := sp + 13344#64) (n := 512) (k := (1560 : Nat))
      rfl (by bv_omega) (by decide)).symm,
    memRegion_split' (b := sp + 2000#64) (b' := sp + 2224#64) (n := 224) (k := 208)
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 24720#64) (b' := sp + 25232#64) (n := 512) (k := (1536 : Nat))
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28848#64) (b' := sp + 29360#64) (n := 512) (k := (1536 : Nat))
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 31408#64) (b' := sp + 31920#64) (n := 512) (k := 720)
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2224#64) (b' := sp + 2320#64) (n := 96) (k := 112)
      rfl (by bv_omega) (by decide)⟩

private theorem seg5_tail_pre_splits (sp : BitVec 64) :
    (memRegion (sp + 2560#64) 10272 =
      memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 2592#64) 10240) ∧
    (memRegion (sp + 12832#64) 2048 =
      memRegion (sp + 12832#64) 64 ∗ memRegion (sp + 12896#64) 1984) ∧
    (memRegion (sp + 26768#64) 512 =
      memRegion (sp + 26768#64) 32 ∗ memRegion (sp + 26800#64) 480) ∧
    (memRegion (sp + 28848#64) 2048 =
      memRegion (sp + 28848#64) 1568 ∗ memRegion (sp + 30416#64) 480) ∧
    (memRegion (sp + 32640#64) 304 =
      memRegion (sp + 32640#64) 64 ∗ memRegion (sp + 32704#64) 32 ∗
      memRegion (sp + 32736#64) 128 ∗ memRegion (sp + 32864#64) 32 ∗
      memRegion (sp + 32896#64) 48) := by
  refine ⟨memRegion_split' (b := sp + 2560#64) (b' := sp + 2592#64) (n := 32) (k := (10240 : Nat))
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 12832#64) (b' := sp + 12896#64) (n := 64) (k := (1984 : Nat))
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 26768#64) (b' := sp + 26800#64) (n := 32) (k := 480)
      rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28848#64) (b' := sp + 30416#64) (n := (1568 : Nat)) (k := 480)
      rfl (by bv_omega) (by decide), ?_⟩
  rw [memRegion_split' (b := sp + 32640#64) (b' := sp + 32704#64) (n := 64) (k := 240)
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 32704#64) (b' := sp + 32736#64) (n := 32) (k := 208)
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 32736#64) (b' := sp + 32864#64) (n := 128) (k := 80)
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 32864#64) (b' := sp + 32896#64) (n := 32) (k := 48)
        rfl (by bv_omega) (by decide)]

private theorem memRegion_0_23104_eq (sp : BitVec 64) :
    memRegion sp 23104 =
      memRegion sp 8 ∗ memRegion (sp + 8#64) 8 ∗ memRegion (sp + 16#64) 128 ∗
      memRegion (sp + 144#64) 1344 ∗ memRegion (sp + 1488#64) 512 ∗
      memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 2224#64) 96 ∗
      memRegion (sp + 2320#64) 112 ∗ memRegion (sp + 2432#64) 64 ∗
      memRegion (sp + 2496#64) 64 ∗ memRegion (sp + 2560#64) 32 ∗
      memRegion (sp + 2592#64) 10240 ∗ memRegion (sp + 12832#64) 64 ∗
      memRegion (sp + 12896#64) 1984 ∗ memRegion (sp + 14880#64) 24 ∗
      memRegion (sp + 14904#64) 8200 := by
  rw [memRegion_split' (b' := sp + 8#64) (n := 8) (k := (23096 : Nat)) rfl rfl (by decide),
      memRegion_split' (b := sp + 8#64) (b' := sp + 16#64) (n := 8) (k := (23088 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 16#64) (b' := sp + 144#64) (n := 128) (k := (22960 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 144#64) (b' := sp + 1488#64) (n := (1344 : Nat)) (k := (21616 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 1488#64) (b' := sp + 2000#64) (n := 512) (k := (21104 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2000#64) (b' := sp + 2224#64) (n := 224) (k := (20880 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2224#64) (b' := sp + 2320#64) (n := 96) (k := (20784 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2320#64) (b' := sp + 2432#64) (n := 112) (k := (20672 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2432#64) (b' := sp + 2496#64) (n := 64) (k := (20608 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2496#64) (b' := sp + 2560#64) (n := 64) (k := (20544 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2560#64) (b' := sp + 2592#64) (n := 32) (k := (20512 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2592#64) (b' := sp + 12832#64) (n := (10240 : Nat)) (k := (10272 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 12832#64) (b' := sp + 12896#64) (n := 64) (k := (10208 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 12896#64) (b' := sp + 14880#64) (n := (1984 : Nat)) (k := (8224 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 14880#64) (b' := sp + 14904#64) (n := 24) (k := (8200 : Nat)) rfl (by bv_omega) (by decide)]

private theorem memRegion_23104_32944_eq (sp : BitVec 64) :
    memRegion (sp + 23104#64) 9840 =
      memRegion (sp + 23104#64) 1568 ∗ memRegion (sp + 24672#64) 48 ∗
      memRegion (sp + 24720#64) 512 ∗ memRegion (sp + 25232#64) 1536 ∗
      memRegion (sp + 26768#64) 32 ∗ memRegion (sp + 26800#64) 480 ∗
      memRegion (sp + 27280#64) 1536 ∗ memRegion (sp + 28816#64) 32 ∗
      memRegion (sp + 28848#64) 1568 ∗ memRegion (sp + 30416#64) 480 ∗
      memRegion (sp + 30896#64) 512 ∗ memRegion (sp + 31408#64) 512 ∗
      memRegion (sp + 31920#64) 720 ∗ memRegion (sp + 32640#64) 64 ∗
      memRegion (sp + 32704#64) 32 ∗ memRegion (sp + 32736#64) 128 ∗
      memRegion (sp + 32864#64) 32 ∗ memRegion (sp + 32896#64) 48 := by
  rw [memRegion_split' (b := sp + 23104#64) (b' := sp + 24672#64) (n := (1568 : Nat)) (k := (8272 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 24672#64) (b' := sp + 24720#64) (n := 48) (k := (8224 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 24720#64) (b' := sp + 25232#64) (n := 512) (k := (7712 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 25232#64) (b' := sp + 26768#64) (n := (1536 : Nat)) (k := (6176 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 26768#64) (b' := sp + 26800#64) (n := 32) (k := (6144 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 26800#64) (b' := sp + 27280#64) (n := 480) (k := (5664 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 27280#64) (b' := sp + 28816#64) (n := (1536 : Nat)) (k := (4128 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 28816#64) (b' := sp + 28848#64) (n := 32) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 28848#64) (b' := sp + 30416#64) (n := (1568 : Nat)) (k := (2528 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 30416#64) (b' := sp + 30896#64) (n := 480) (k := (2048 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 30896#64) (b' := sp + 31408#64) (n := 512) (k := (1536 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 31408#64) (b' := sp + 31920#64) (n := 512) (k := (1024 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 31920#64) (b' := sp + 32640#64) (n := 720) (k := 304) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 32640#64) (b' := sp + 32704#64) (n := 64) (k := 240) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 32704#64) (b' := sp + 32736#64) (n := 32) (k := 208) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 32736#64) (b' := sp + 32864#64) (n := 128) (k := 80) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 32864#64) (b' := sp + 32896#64) (n := 32) (k := 48) rfl (by bv_omega) (by decide)]

/-! ## 3. Segments 4 & 5 Composition (`+0x59d0 → ret`) -/

private theorem seg4_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s0 : State) (ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp)
    (s : State) (P : SepProp)
    (hpre : Seg3Post b s0.sp s0 ret pkA rA pk rand (memRegion ret 1600 ∗ Rest) s P) :
    let sp := s0.sp - 33104#64
    let m := sha3_256List rand
    let hashed := sha3_512List (m ++ sha3_256List pk)
    let coins := hashed.drop 32
    let rho := pkRho pk
    let e2 := neonCbd2Poly16 (shake256List 128 (coins ++ [8#8]))
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
    let c1 := neonCompressSerialize11Poly (uVecPoly16 rho coins 0) ++
      neonCompressSerialize11Poly (uVecPoly16 rho coins 1) ++
      neonCompressSerialize11Poly (uVecPoly16 rho coins 2) ++
      neonCompressSerialize11Poly (uVecPoly16 rho coins 3)
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Start) s P
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
        s2.readReg64 .x19 = sp + 10752#64 ∧ s2.readReg64 .x20 = sp + 12832#64 ∧
        s2.readReg64 .fp = sp + 33008#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl s2.mem ∧ MlKemRoOk mlkemMpl s2.mem ∧
        (P2 ⊢ SpilledMsgWords sp m ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          memRegion (sp + 2224#64) 208 ∗ memRegion (sp + 24720#64) 512 ∗
          memRegion (sp + 26768#64) 512 ∗ memRegion (sp + 31408#64) 512 ∗
          ATransAt (sp + 2560#64) rho ∗
          PolyMem (sp + 10752#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
          PolyMem (sp + 11264#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
          PolyMem (sp + 11776#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
          PolyMem (sp + 12288#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
          PolyMem (sp + 12832#64) (polyVecNat r0) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
          PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗
          memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 30896#64) 512 ∗
          memRegion (sp + 24512#64) 160 ∗ ((sp + 23104#64) ↦ₛ c1) ∗
          memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 14880#64) 24 ∗
          memRegion (sp + 25232#64) 1536 ∗ memRegion (sp + 27280#64) 1536 ∗
          memRegion (sp + 29360#64) 1536 ∗ memRegion (sp + 31920#64) 720 ∗
          Seg45Frame s0.sp s0 sp ret pkA rA pk rand hashed Rest)) := by
  intro sp m hashed coins rho e2 r0 r1 r2 r3 c1
  rcases hpre with ⟨hpc, hrun, hsp, hspA, hsp_chk, hcl, hro, hx20, hfp, hP⟩
  obtain ⟨hr2000, hr12832, hr30896⟩ := seg4_entry_regions sp
  have hP0 : P ⊢ ATransAt (sp + 2560#64) rho ∗
      PolyMem (sp + 28848#64) (fun _ => 0#128) ∗ PolyMem (sp + 29360#64) (fun _ => 0#128) ∗
      PolyMem (sp + 29872#64) (fun _ => 0#128) ∗ PolyMem (sp + 30384#64) (fun _ => 0#128) ∗
      PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
      PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
      PolyMem (sp + 26768#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [4#8])))) ∗
      PolyMem (sp + 27280#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [5#8])))) ∗
      PolyMem (sp + 27792#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [6#8])))) ∗
      PolyMem (sp + 28304#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [7#8])))) ∗
      memRegion (sp + 2000#64) 432 ∗ memRegion (sp + 12832#64) 512 ∗
      (SpilledMsgWords sp m ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        PolyMem (sp + 10752#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        PolyMem (sp + 11264#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        PolyMem (sp + 11776#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
        PolyMem (sp + 12288#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
        memRegion (sp + 13344#64) 1560 ∗ memRegion (sp + 23104#64) 1408 ∗
        memRegion (sp + 24512#64) 160 ∗ memRegion (sp + 30896#64) 512 ∗
        memRegion (sp + 31408#64) 1232 ∗ Seg45Frame s0.sp s0 sp ret pkA rA pk rand hashed Rest) := by
    refine Entails.trans hP ?_
    dsimp only [Seg3Spatial]
    rw [seg45Frame_eq, publicKeyStateAt_2560_eq sp pk, hr2000, hr12832, hr30896]
    sep_frame
  refine SepWP.weaken_pre hP0 (sepWP_seq_env hcl hro
    (seg4_rows_ok hb s sp rho coins _ hpc hrun hsp hspA hx20 hcl hro) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hfp1, _, _, hP1⟩
  obtain ⟨hr2000_64, hr12832_2072, hr2000_208, hr24720, hr28848, hr31408, _⟩ := seg45_mid_regions sp
  have he1_0 := polyMem_entails_memRegion512 (sp + 26768#64)
    (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [4#8]))))
  have he1_rest :
      PolyMem (sp + 27280#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [5#8])))) ∗
      PolyMem (sp + 27792#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [6#8])))) ∗
      PolyMem (sp + 28304#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [7#8])))) ⊢
      memRegion (sp + 27280#64) 1536 := by
    simpa [show sp + 27280#64 + 512#64 = sp + 27792#64 by bv_omega,
      show sp + 27280#64 + 1024#64 = sp + 28304#64 by bv_omega] using
      polyMem3_entails_memRegion1536 (sp + 27280#64) _ _ _
  have hP1' : P1 ⊢ memRegion (sp + 2368#64) 64 ∗
      memRegion (sp + 12832#64) 2072 ∗ memRegion (sp + 23104#64) 1408 ∗
      PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
      PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
      PolyMem (sp + 28848#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
      PolyMem (sp + 29360#64) (polyVecNat (uVecPoly16 rho coins 1)) ∗
      PolyMem (sp + 29872#64) (polyVecNat (uVecPoly16 rho coins 2)) ∗
      PolyMem (sp + 30384#64) (polyVecNat (uVecPoly16 rho coins 3)) ∗
      memRegion (sp + 31408#64) 1232 ∗
      (SpilledMsgWords sp m ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        memRegion (sp + 2000#64) 368 ∗ ATransAt (sp + 2560#64) rho ∗
        PolyMem (sp + 10752#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        PolyMem (sp + 11264#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        PolyMem (sp + 11776#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
        PolyMem (sp + 12288#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
        memRegion (sp + 24512#64) 160 ∗ memRegion (sp + 26768#64) 512 ∗
        memRegion (sp + 27280#64) 1536 ∗ memRegion (sp + 30896#64) 512 ∗
        Seg45Frame s0.sp s0 sp ret pkA rA pk rand hashed Rest) := by
    refine Entails.trans hP1 ?_
    rw [hr2000_64, ← hr12832_2072]
    exact entails_sub he1_0 (by sep_frame) (entails_sub he1_rest (by sep_frame) (by sep_frame))
  refine SepWP.weaken_pre hP1' (sepWP_seq_env hcl1 hro1
    (seg4_compress_ok hb hbase s1 sp (sp + 10752#64) (sp + 33008#64)
      (uVecPoly16 rho coins 0) (uVecPoly16 rho coins 1)
      (uVecPoly16 rho coins 2) (uVecPoly16 rho coins 3) r0 r1 r2 r3 _
      hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx19_1 (hfp1.trans hfp)) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx19_2, hx20_2, hfp2, hP2⟩
  refine SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, hsp_chk, hx19_2, hx20_2, hfp2, hcl2, hro2, ?_⟩
  refine Entails.trans hP2 ?_
  have hr2000_join : memRegion (sp + 2000#64) 368 ∗ memRegion (sp + 2368#64) 64 =
      memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 2224#64) 208 :=
    hr2000_64.symm.trans hr2000_208
  rw [hr24720, hr28848, hr31408]
  exact entails_sub (Entails.of_eq hr2000_join) (by sep_frame) (by sep_frame)

private theorem seg5_mid_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s0 s2 : State) (ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp)
    (P2 : SepProp) (hpc2 : s2.pc = b + offSeg5Start) (hrun2 : s2.status = .Running)
    (hpost4 :
      let sp := s0.sp - 33104#64
      let m := sha3_256List rand
      let hashed := sha3_512List (m ++ sha3_256List pk)
      let coins := hashed.drop 32
      let rho := pkRho pk
      let e2 := neonCbd2Poly16 (shake256List 128 (coins ++ [8#8]))
      let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
      let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
      let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
      let r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
      let c1 := neonCompressSerialize11Poly (uVecPoly16 rho coins 0) ++
        neonCompressSerialize11Poly (uVecPoly16 rho coins 1) ++
        neonCompressSerialize11Poly (uVecPoly16 rho coins 2) ++
        neonCompressSerialize11Poly (uVecPoly16 rho coins 3)
      s2.sp = sp ∧ s2.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
      s2.readReg64 .x19 = sp + 10752#64 ∧ s2.readReg64 .x20 = sp + 12832#64 ∧
      s2.readReg64 .fp = sp + 33008#64 ∧
      mlkemMultiLib.CodeLoaded mlkemMpl s2.mem ∧ MlKemRoOk mlkemMpl s2.mem ∧
      (P2 ⊢ SpilledMsgWords sp m ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        memRegion (sp + 2224#64) 208 ∗ memRegion (sp + 24720#64) 512 ∗
        memRegion (sp + 26768#64) 512 ∗ memRegion (sp + 31408#64) 512 ∗
        ATransAt (sp + 2560#64) rho ∗
        PolyMem (sp + 10752#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        PolyMem (sp + 11264#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        PolyMem (sp + 11776#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
        PolyMem (sp + 12288#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
        PolyMem (sp + 12832#64) (polyVecNat r0) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
        PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗
        memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 30896#64) 512 ∗
        memRegion (sp + 24512#64) 160 ∗ ((sp + 23104#64) ↦ₛ c1) ∗
        memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 14880#64) 24 ∗
        memRegion (sp + 25232#64) 1536 ∗ memRegion (sp + 27280#64) 1536 ∗
        memRegion (sp + 29360#64) 1536 ∗ memRegion (sp + 31920#64) 720 ∗
        Seg45Frame s0.sp s0 sp ret pkA rA pk rand hashed Rest)) :
    let sp := s0.sp - 33104#64
    let m := sha3_256List rand
    let hashed := sha3_512List (m ++ sha3_256List pk)
    let coins := hashed.drop 32
    let rho := pkRho pk
    let c1 := neonCompressSerialize11Poly (uVecPoly16 rho coins 0) ++
      neonCompressSerialize11Poly (uVecPoly16 rho coins 1) ++
      neonCompressSerialize11Poly (uVecPoly16 rho coins 2) ++
      neonCompressSerialize11Poly (uVecPoly16 rho coins 3)
    let c2 := neonCompressSerialize5Poly (seg5VPoly16 pk m coins)
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Tail) s2 P2
      (fun s7 P7 =>
        s7.sp = sp ∧ s7.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
        s7.readReg64 .fp = sp + 33008#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl s7.mem ∧ MlKemRoOk mlkemMpl s7.mem ∧
        (P7 ⊢ memRegion (sp + 16#64) 128 ∗ memRegion (sp + 1488#64) 512 ∗
          memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 2224#64) 96 ∗
          memRegion (sp + 2320#64) 112 ∗
          ATransAt (sp + 2560#64) rho ∗
          PolyMem (sp + 10752#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
          PolyMem (sp + 11264#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
          PolyMem (sp + 11776#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
          PolyMem (sp + 12288#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
          memRegion (sp + 12832#64) 2048 ∗ memRegion (sp + 14880#64) 24 ∗
          ((sp + 23104#64) ↦ₛ c1) ∗ ((sp + 24512#64) ↦ₛ c2) ∗
          memRegion (sp + 24720#64) 512 ∗ memRegion (sp + 25232#64) 1536 ∗
          memRegion (sp + 26768#64) 512 ∗ memRegion (sp + 27280#64) 1536 ∗
          memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 29360#64) 1536 ∗
          memRegion (sp + 30896#64) 512 ∗ memRegion (sp + 31408#64) 512 ∗
          memRegion (sp + 31920#64) 720 ∗
          Seg45Frame s0.sp s0 sp ret pkA rA pk rand hashed Rest)) := by
  intro sp m hashed coins rho c1 c2
  dsimp only at hpost4
  set e2 := neonCbd2Poly16 (shake256List 128 (coins ++ [8#8]))
  set r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
  set r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
  set r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
  set r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
  set t0 := tHatModPoly16 (pkEk0 pk)
  set t1 := tHatModPoly16 (pkEk1 pk)
  set t2 := tHatModPoly16 (pkEk2 pk)
  set t3 := tHatModPoly16 (pkEk3 pk)
  rcases hpost4 with ⟨hsp2, hspA2, hsp_chk, hx19_2, hx20_2, hfp2, hcl2, hro2, hP2⟩
  have hm : m.length = 32 := sha3_256List_length rand
  refine SepWP.weaken_pre hP2 (sepWP_seq_env hcl2 hro2
    (seg5_decomp_ok hb s2 sp (sp + 10752#64) (sp + 12832#64) (sp + 33008#64) hm e2 _
      hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx19_2 hx20_2 hfp2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx19_3, hx20_3, hfp3, hacc3, hP3⟩
  have hP3' : P3 ⊢ memRegion (sp + 28848#64) (16 * 32) ∗
      (Spill13Mem (sp + 2224#64) (AccSpill polyZero16) ∗
        PolyMem (sp + 10752#64) (polyVecNat t0) ∗ PolyMem (sp + 11264#64) (polyVecNat t1) ∗
        PolyMem (sp + 11776#64) (polyVecNat t2) ∗ PolyMem (sp + 12288#64) (polyVecNat t3) ∗
        PolyMem (sp + 12832#64) (polyVecNat r0) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
        PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗
        Poly32Mem (sp + 26768#64) (Vec32.ofFn (fun _ => 0#128)) ∗
        (memRegion (sp + 16#64) 128 ∗ memRegion (sp + 1488#64) 512 ∗
          ATransAt (sp + 2560#64) rho ∗ PolyMem (sp + 24720#64) (polyVecNat (msgPoly16 m)) ∗
          PolyMem (sp + 31408#64) (polyVecNat e2) ∗ memRegion (sp + 30896#64) 512 ∗
          memRegion (sp + 24512#64) 160 ∗ ((sp + 23104#64) ↦ₛ c1) ∗
          memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 14880#64) 24 ∗
          memRegion (sp + 25232#64) 1536 ∗ memRegion (sp + 27280#64) 1536 ∗
          memRegion (sp + 29360#64) 1536 ∗ memRegion (sp + 31920#64) 720 ∗
          Seg45Frame s0.sp s0 sp ret pkA rA pk rand hashed Rest)) := by
    refine Entails.trans hP3 ?_
    rw [poly32Mem_ofFn]
    change _ ⊢ memRegion (sp + 28848#64) 512 ∗ _
    exact entails_sub (spilledMsgWords_entails_memRegion128 sp m) (by sep_frame)
      (entails_sub (polyMem_entails_memRegion512 (sp + 1488#64) _) (by sep_frame) (by sep_frame))
  refine SepWP.weaken_pre hP3' ?_
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 28848#64) (by decide) rfl
  intro f28848
  change SepWP _ _ _ (PolyMem (sp + 28848#64) f28848 ∗ _) _
  rw [← poly32Mem_ofFn (sp + 28848#64) f28848]
  refine SepWP.weaken_pre (show _ ⊢ Spill13Mem (sp + 2224#64) (AccSpill polyZero16) ∗
      PolyMem (sp + 10752#64) (polyVecNat t0) ∗ PolyMem (sp + 11264#64) (polyVecNat t1) ∗
      PolyMem (sp + 11776#64) (polyVecNat t2) ∗ PolyMem (sp + 12288#64) (polyVecNat t3) ∗
      PolyMem (sp + 12832#64) (polyVecNat r0) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
      PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗
      Poly32Mem (sp + 26768#64) (Vec32.ofFn (fun _ => 0#128)) ∗
      Poly32Mem (sp + 28848#64) (Vec32.ofFn f28848) ∗ _ by sep_frame) ?_
  set dot := neonDot4 t0 t1 t2 t3 r0 r1 r2 r3
  refine sepWP_seq_env hcl3 hro3
    (seg5_dot_ok hb s3 sp (sp + 33008#64) t0 t1 t2 t3 r0 r1 r2 r3
      (Vec32.ofFn (fun _ => 0#128)) (Vec32.ofFn f28848) _
      hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx8_3 hx9_3 hx10_3 hx11_3 hx12_3 hx19_3 hx20_3 hfp3 hacc3) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hfp4, rfl⟩
  have hdot : dot.size = 256 := polyAdd16_size _ _
  have hr_col : PolyMem (sp + 12832#64) (polyVecNat r0) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
      PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ⊢
      memRegion (sp + 12832#64) 2048 := by
    simpa [show sp + 12832#64 + 512#64 = sp + 13344#64 by bv_omega,
      show sp + 12832#64 + 1024#64 = sp + 13856#64 by bv_omega,
      show sp + 12832#64 + 1536#64 = sp + 14368#64 by bv_omega] using
      polyMem4_entails_memRegion2048 (sp + 12832#64) _ _ _ _
  have hsp2224 : Spill13Mem (sp + 2224#64) (AccSpill dot) ⊢
      memRegion (sp + 2224#64) 96 ∗ memRegion (sp + 2320#64) 112 := by
    rw [← (seg45_mid_regions sp).2.2.2.2.2.2]
    exact spill13Mem_entails_memRegion (sp + 2224#64) (AccSpill dot)
  refine SepWP.weaken_pre (show _ ⊢ PolyMem (sp + 26768#64) (polyVecNat dot) ∗
      (memRegion (sp + 2224#64) 96 ∗ memRegion (sp + 2320#64) 112 ∗
        PolyMem (sp + 10752#64) (polyVecNat t0) ∗ PolyMem (sp + 11264#64) (polyVecNat t1) ∗
        PolyMem (sp + 11776#64) (polyVecNat t2) ∗ PolyMem (sp + 12288#64) (polyVecNat t3) ∗
        memRegion (sp + 12832#64) 2048 ∗ memRegion (sp + 28848#64) 512 ∗ _) from
      entails_sub hsp2224 (by sep_frame)
        (entails_sub hr_col (by sep_frame)
          (entails_sub (poly32Mem_entails_memRegion (sp + 28848#64) _) (by sep_frame) (by sep_frame)))) ?_
  refine sepWP_seq_env hcl4 hro4
    (seg5_inv_low_ok hb s4 sp (sp + 33008#64) hdot _ hpc4 hrun4 hsp4 hspA4 hcl4 hro4 hfp4) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hsp5, hspA5, hfp5, rfl⟩
  refine SepWP.weaken_pre (show _ ⊢ memRegion (sp + 2320#64) 112 ∗
      PolyMem (sp + 24720#64) (polyVecNat (msgPoly16 m)) ∗
      PolyMem (sp + 26768#64) (polyVecNat (lowerInvNtt16 dot)) ∗
      memRegion (sp + 30896#64) 512 ∗ PolyMem (sp + 31408#64) (polyVecNat e2) ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl5 hro5
    (seg5_add_ok hb hbase s5 sp hdot e2 (msgPoly16 m) _ hpc5 hrun5 hsp5 hspA5 hcl5 hro5) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 hro6 ⟨hsp6, hspA6, hfp6, hP6⟩
  have hfp6' : s6.readReg64 .fp = sp + 33008#64 := hfp6.trans hfp5
  have hv_eq : seg5FinalPoly (neonInvNttMontgomery16 dot) e2 (msgPoly16 m) = seg5VPoly16 pk m coins := rfl
  refine SepWP.weaken_pre hP6 ?_
  rw [hv_eq]
  refine SepWP.weaken_pre (show _ ⊢
      PolyMem (sp + 30896#64) (polyVecNat (seg5VPoly16 pk m coins)) ∗
        memRegion (sp + 24512#64) 160 ∗ _ by sep_frame)
    (sepWP_seq_env hcl6 hro6
      (seg5_compress_ok hb hbase s6 sp (sp + 33008#64) (seg5VPoly16 pk m coins) _
        hpc6 hrun6 hsp6 hspA6 hcl6 hro6 hfp6') ?_)
  rintro s7 P7 hpc7 hrun7 hcl7 hro7 ⟨hsp7, hspA7, hfp7, hP7⟩
  refine SepWP.done hpc7 hrun7 ⟨hsp7, hspA7, hsp_chk, hfp7, hcl7, hro7, ?_⟩
  refine Entails.trans hP7 ?_
  exact entails_sub (polyMem_entails_memRegion512 (sp + 30896#64) _) (by sep_frame) (by sep_frame)

/-- Full Segments 4 & 5 composition (`+0x59d0 → s0.readReg64 .lr`). -/
theorem seg5_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s0 : State) (ret pkA rA : BitVec 64) (pk rand : List (BitVec 8)) (Rest : SepProp)
    (hpk : pk.length = 1568) (hrnd : rand.length = 32) (hsp0 : s0.spAligned = true)
    (s : State) (P : SepProp)
    (hpre : Seg3Post b s0.sp s0 ret pkA rA pk rand (memRegion ret 1600 ∗ Rest) s P) :
    let (ct, ss) := kyber1024Encaps pk rand
    SepWP (blkPC07.rebase b (fun _ => none)) (s0.readReg64 .lr) s P
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ (ret ↦ₛ ct) ∗ ((ret + 1568#64) ↦ₛ ss) ∗
          stackAt s0.sp 34240 ∗ Rest)) := by
  dsimp only
  have hcl0 := hpre.2.2.2.2.2.1
  have hro0 := hpre.2.2.2.2.2.2.1
  refine sepWP_seq_env hcl0 hro0 (seg4_ok hb hbase s0 ret pkA rA pk rand Rest s P hpre) ?_
  rintro s2 P2 hpc2 hrun2 _ _ hpost4
  refine sepWP_seq_env hpost4.2.2.2.2.2.2.1 hpost4.2.2.2.2.2.2.2.1
    (seg5_mid_ok hb hbase s0 s2 ret pkA rA pk rand Rest P2 hpc2 hrun2 hpost4) ?_
  rintro s7 P7 hpc7 hrun7 hcl7 hro7 ⟨hsp7, _, hsp_chk, hfp7, _, _, hP7⟩
  set sp := s0.sp - 33104#64
  set m := sha3_256List rand
  set hashed := sha3_512List (m ++ sha3_256List pk)
  set coins := hashed.drop 32
  set rho := pkRho pk
  set c1 := neonCompressSerialize11Poly (uVecPoly16 rho coins 0) ++
    neonCompressSerialize11Poly (uVecPoly16 rho coins 1) ++
    neonCompressSerialize11Poly (uVecPoly16 rho coins 2) ++
    neonCompressSerialize11Poly (uVecPoly16 rho coins 3)
  set c2 := neonCompressSerialize5Poly (seg5VPoly16 pk m coins)
  set ct := c1 ++ c2
  obtain ⟨hct_eq, hss_eq, hc1_len, _, hct_len⟩ := seg45_output_eq hpk hrnd
  have hhashed : hashed.length = 64 := sha3_512List_length _
  obtain ⟨hs2560, hs12832, hs26768, hs28848, hs32640⟩ := seg5_tail_pre_splits sp
  have hct_pts : ((sp + 23104#64) ↦ₛ c1) ∗ ((sp + 24512#64) ↦ₛ c2) = ((sp + 23104#64) ↦ₛ ct) := by
    have h24512 : sp + 23104#64 + BitVec.ofNat 64 1408 = sp + 24512#64 := by clear * -; bv_omega
    dsimp only [ct]; rw [pointsToBytes_append (sp + 23104#64) c1 c2, hc1_len, h24512]
  have h28848_join : memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 29360#64) 1536 =
      memRegion (sp + 28848#64) 1568 ∗ memRegion (sp + 30416#64) 480 :=
    (seg45_mid_regions sp).2.2.2.2.1.symm.trans hs28848
  have hpk_reg : ATransAt (sp + 2560#64) rho ∗
      PolyMem (sp + 10752#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
      PolyMem (sp + 11264#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
      PolyMem (sp + 11776#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
      PolyMem (sp + 12288#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
      ((sp + 12800#64) ↦ₛ List.replicate 32 0#8) ⊢
      memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 2592#64) 10240 := by
    rw [← publicKeyStateAt_2560_eq sp pk, ← hs2560]
    exact publicKeyStateAt_entails_memRegion sp pk
  let tailRest : SepProp :=
    (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ memRegion sp 8 ∗ memRegion (sp + 16#64) 128 ∗
    memRegion (sp + 144#64) 1344 ∗ memRegion (sp + 1488#64) 512 ∗
    memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 2224#64) 96 ∗
    memRegion (sp + 2320#64) 112 ∗ memRegion (sp + 2432#64) 64 ∗
    memRegion (sp + 2592#64) 10240 ∗ memRegion (sp + 12896#64) 1984 ∗
    memRegion (sp + 14880#64) 24 ∗ memRegion (sp + 14904#64) 8200 ∗
    memRegion (sp + 24672#64) 48 ∗ memRegion (sp + 24720#64) 512 ∗
    memRegion (sp + 25232#64) 1536 ∗ memRegion (sp + 26800#64) 480 ∗
    memRegion (sp + 27280#64) 1536 ∗ memRegion (sp + 28816#64) 32 ∗
    memRegion (sp + 30416#64) 480 ∗ memRegion (sp + 30896#64) 512 ∗
    memRegion (sp + 31408#64) 512 ∗ memRegion (sp + 31920#64) 720 ∗
    memRegion (sp + 32640#64) 64 ∗ memRegion (sp + 32736#64) 128 ∗
    memRegion (sp + 32896#64) 48 ∗ Rest
  have hP7' : P7 ⊢ stackAt sp 1136 ∗ ((sp + 8#64) ↦₆₄ ret) ∗ ((sp + 2496#64) ↦ₛ hashed) ∗
      memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 12832#64) 64 ∗
      ((sp + 23104#64) ↦ₛ ct) ∗ memRegion (sp + 26768#64) 32 ∗
      memRegion (sp + 28848#64) 1568 ∗ memRegion (sp + 32704#64) 32 ∗
      memRegion (sp + 32864#64) 32 ∗ SavedFrame07 s0.sp s0 ∗ memRegion ret 1600 ∗ tailRest := by
    refine Entails.trans hP7 ?_
    dsimp only [tailRest]
    rw [seg45Frame_eq, hs12832, hs26768, hs32640]
    exact entails_sub hpk_reg (by sep_frame)
      (entails_sub (Entails.of_eq hct_pts) (by sep_frame)
        (entails_sub (Entails.of_eq h28848_join) (by sep_frame) (by sep_frame)))
  refine SepWP.weaken_pre hP7' (SepWP.mono
    (seg5_tail_ok hb hbase s0 s7 ret hashed ct tailRest hhashed hct_len hsp0 hpc7 hrun7 hsp7 hsp_chk
      hcl7 hro7 hfp7) ?_)
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  dsimp only [tailRest]
  rw [← hct_eq, ← hss_eq, ← stackAt_34240_join s0.sp]
  rw [memRegion_split' (b := sp) (b' := sp + 23104#64) (n := (23104 : Nat)) (k := (9840 : Nat))
        rfl rfl (by decide),
      memRegion_0_23104_eq sp, memRegion_23104_32944_eq sp]
  sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5

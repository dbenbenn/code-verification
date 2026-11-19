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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8c

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 8 Composition (`+0xabd8 → ret`)

Composes `Seg8a` (`decompress_1(m')` + `e₂` copy), `Seg8b` (`t̂ · r̂` + `InvNTT3` + `+ e₂ + msgPoly`),
and `Seg8c` (`compress_and_serialize_4` + `B28` `memcpy` + `B16` FO constant-time select + epilogue),
proves pure equivalence to `mlkem768DecapsWith sampleNtt`, and rejoins the `26,960`-byte tight stack
frame.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8
open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 byteDecodeMod compressAndEncode decodeAndDecompress indCpaDecrypt indCpaEncryptWith
  mlkem768DecapsWith neonBarrettReduce16 neonCompressSerialize4 neonInvNttMontgomery16
  neonMontgomeryMul16 polyAdd polyInvNtt polyNtt sampleNtt samplePolyCbd2 sampleVecCbd2
  sha3_512List shake256List vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonBarrettReducePoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt (
  neonPolyInvNttFromMontInv16 neonPolyInvNttFromMontInv16_spec vecDotNtt_canonical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents neonVecDotNtt3_spec polyAdd16 polyAdd16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  neonCbd2Poly16 neonCbd2Poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (
  decodeAndDecompress_poly16_spec neonCompressSerialize4_eq_compressAndEncode)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (byteEncode_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (
  byteDecodeRaw_lt_two_pow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem polyVecNat vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (msgPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16_size neonDot3 neonDot3_size upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure (upperInvNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (seg5FinalPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (sha3_512List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blkPC04 blkPl04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a (stackAt_26960_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  WordRangeMem modTHatPoly16 modTHatPoly16_spec msgWordFn wordRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5 (
  ATransMemAt ATransRowMemAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b (
  rHatPoly16 rHatPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b (offSeg8Start)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7 (Seg7Spatial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8a (seg8a_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8b (seg8b_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8c (seg8c_ok)

/-! ## 1. Pure Re-Encryption `c₂'` & Fujisaki–Okamoto Equivalence -/

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
      (polyAdd16 (polyAdd16 (neonPolyInvNttFromMontInv16 dot) e2) msgPoly).map
        neonBarrettReduce16 := by
  have hinv : (neonInvNttMontgomery16 dot).size = 256 := by
    rw [← upperInvNtt16_lowerInvNtt16 dot, upperInvNtt16_size]
    exact lowerInvNtt16_size hdot
  exact seg5FinalPoly_eq_barrett_aux hinv e2 msgPoly

private theorem polyBounded16_mono {b1 b2 : Int} {p : Poly16}
    (hle : b1 ≤ b2) (h : PolyBounded16 b1 p) : PolyBounded16 b2 p :=
  ⟨h.1, fun i hi => ⟨by have := (h.2 i hi).1; omega, by have := (h.2 i hi).2; omega⟩⟩

section PureCt2
attribute [local irreducible]
  sha3_512List shake256List byteDecodeMod decodeAndDecompress polyNtt polyInvNtt samplePolyCbd2
  modTHatPoly16 msgPoly16 neonCbd2Poly16 neonInvNttMontgomery16 neonPolyInvNttFromMontInv16
  polyAdd16 neonBarrettReduce16 polyAdd vecDotNtt

set_option maxRecDepth 4000 in
private theorem decapsCt2_eq {pk m coins : List (BitVec 8)}
    (hm : m.length = 32) (hcoins : coins.length = 32) :
    let pk0 := pk.take 384
    let pk1 := (pk.drop 384).take 384
    let pk2 := (pk.drop 768).take 384
    let dot := neonDot3
      (modTHatPoly16 pk0) (modTHatPoly16 pk1) (modTHatPoly16 pk2)
      (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
    let e2 := neonCbd2Poly16 (shake256List 128 (coins ++ [6#8]))
    neonCompressSerialize4
      (seg5FinalPoly (neonInvNttMontgomery16 dot) e2 (msgPoly16 m)) =
      (indCpaEncryptWith sampleNtt 3 10 4 pk m coins).2.1 := by
  dsimp only [indCpaEncryptWith]
  have hd_sz := neonDot3_size
    (modTHatPoly16 (pk.take 384))
    (modTHatPoly16 ((pk.drop 384).take 384))
    (modTHatPoly16 ((pk.drop 768).take 384))
    (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
  dsimp only [neonDot3] at hd_sz ⊢
  have htm : m.take 32 = m := List.take_of_length_le (Nat.le_of_eq hm)
  have htc : coins.take 32 = coins := List.take_of_length_le (Nat.le_of_eq hcoins)
  have hsh (d : BitVec 8) : (shake256List 128 (coins ++ [d])).length = 128 :=
    shake256List_length 128 (coins ++ [d])
  obtain ⟨ht0_b, ht0_r⟩ := modTHatPoly16_spec (pk.take 384)
  obtain ⟨ht1_b, ht1_r⟩ := modTHatPoly16_spec ((pk.drop 384).take 384)
  obtain ⟨ht2_b, ht2_r⟩ := modTHatPoly16_spec ((pk.drop 768).take 384)
  have htg (j : Nat) (hj : j < 3) :
      (Array.ofFn (n := 3) fun ⟨i, _⟩ =>
        byteDecodeMod 12 ((pk.drop (384 * i)).take 384)).getD j zeroPoly =
        byteDecodeMod 12 ((pk.drop (384 * j)).take 384) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hj, ↓reduceDIte, Option.getD_some]
  change PolyRepresents _ (byteDecodeMod 12 ((pk.drop (384 * 0)).take 384)) at ht0_r
  change PolyRepresents _ (byteDecodeMod 12 ((pk.drop (384 * 1)).take 384)) at ht1_r
  change PolyRepresents _ (byteDecodeMod 12 ((pk.drop (384 * 2)).take 384)) at ht2_r
  rw [← htg 0 (by decide)] at ht0_r
  rw [← htg 1 (by decide)] at ht1_r
  rw [← htg 2 (by decide)] at ht2_r
  obtain ⟨_, hr0_b, hr0_r⟩ := rHatPoly16_spec (hsh 0#8)
  obtain ⟨_, hr1_b, hr1_r⟩ := rHatPoly16_spec (hsh 1#8)
  obtain ⟨_, hr2_b, hr2_r⟩ := rHatPoly16_spec (hsh 2#8)
  have hrg (j : Nat) (hj : j < 3) :
      ((sampleVecCbd2 3 coins 0).map polyNtt).getD j zeroPoly =
        polyNtt (samplePolyCbd2 (shake256List 128 (coins ++ [BitVec.ofNat 8 j]))) := by
    unfold sampleVecCbd2
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_ofFn]
    simp only [htc, hj, Nat.zero_add, ↓reduceDIte, Option.map_some, Option.getD_some]
  rw [show (0#8 : BitVec 8) = BitVec.ofNat 8 0 from rfl, ← hrg 0 (by decide)] at hr0_r
  rw [show (1#8 : BitVec 8) = BitVec.ofNat 8 1 from rfl, ← hrg 1 (by decide)] at hr1_r
  rw [show (2#8 : BitVec 8) = BitVec.ofNat 8 2 from rfl, ← hrg 2 (by decide)] at hr2_r
  obtain ⟨hdot_b, hdot_r⟩ := neonVecDotNtt3_spec
    (polyBounded16_mono (by decide) ht0_b)
    (polyBounded16_mono (by decide) ht1_b)
    (polyBounded16_mono (by decide) ht2_b)
    (polyBounded16_mono (by decide) hr0_b)
    (polyBounded16_mono (by decide) hr1_b)
    (polyBounded16_mono (by decide) hr2_b)
    ht0_r ht1_r ht2_r hr0_r hr1_r hr2_r
  obtain ⟨hinv_sz, hinv_b, hinv_r⟩ := neonPolyInvNttFromMontInv16_spec
    (polyBounded16_mono (by decide) hdot_b) hdot_r (vecDotNtt_canonical 3 _ _)
  obtain ⟨he2_b, he2_r⟩ := neonCbd2Poly16_spec (hsh 6#8)
  obtain ⟨hm_b, hm_r⟩ := msgPoly16_spec m
  rw [htc, htm, show BitVec.ofNat 8 (2 * 3) = 6#8 from rfl]
  obtain ⟨ha1_b, ha1_r⟩ := polyAdd16_spec hinv_b he2_b (by decide) hinv_r he2_r
  obtain ⟨_, ha2_r⟩ := polyAdd16_spec ha1_b hm_b (by decide) ha1_r hm_r
  obtain ⟨hfin_b, hfin_r⟩ := neonBarrettReducePoly16_spec ha2_r
  rw [← seg5FinalPoly_eq_barrett hd_sz] at hfin_b hfin_r
  have hv_sz : (polyAdd (polyAdd (polyInvNtt (vecDotNtt 3
      (Array.ofFn (n := 3) fun ⟨i, _⟩ => byteDecodeMod 12 ((pk.drop (384 * i)).take 384))
      ((sampleVecCbd2 3 coins 0).map polyNtt)))
      (samplePolyCbd2 (shake256List 128 (coins ++ [6#8]))))
      (decodeAndDecompress 1 m)).size = 256 := by unfold polyAdd; simp
  refine (neonCompressSerialize4_eq_compressAndEncode
    (fun i hi => ⟨by have := (hfin_b.2 i hi).1; omega, by have := (hfin_b.2 i hi).2; omega⟩)
    hfin_r hv_sz).trans ?_
  apply congrArg (compressAndEncode 4)
  refine congrArg₂ polyAdd ?_ rfl
  refine congrArg₂ polyAdd ?_ rfl
  apply congrArg polyInvNtt
  refine congrArg₂ (vecDotNtt 3) ?_ rfl
  apply Array.ext
  · simp
  · intro i hi1 hi2
    simp

end PureCt2

private theorem indCpaDecrypt_len32 (sk ct : List (BitVec 8)) :
    (indCpaDecrypt 3 10 4 sk ct).length = 32 := by
  unfold indCpaDecrypt compressAndEncode; simp [byteEncode_length]

private theorem indCpaEncryptWith_ct1_len960 (pk m coins : List (BitVec 8)) :
    (indCpaEncryptWith sampleNtt 3 10 4 pk m coins).1.length = 960 := by
  dsimp only [indCpaEncryptWith]
  have hr : List.range 3 = [0, 1, 2] := rfl
  rw [hr]; simp [compressAndEncode, byteEncode_length]

private theorem decaps_output_eq {dk ct1 ct2 : List (BitVec 8)}
    (_hdk : dk.length = 2400) (hct1 : ct1.length = 960) (hct2 : ct2.length = 128) :
    let ct := ct1 ++ ct2
    let m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
    let pk := (dk.drop 1152).take 1184
    let hPk := (dk.drop 2336).take 32
    let z := (dk.drop 2368).take 32
    let kr := sha3_512List (m' ++ hPk)
    let coins := kr.drop 32
    let pk0 := (dk.drop 1152).take 384
    let pk1 := (dk.drop 1536).take 384
    let pk2 := (dk.drop 1920).take 384
    let dot := neonDot3
      (modTHatPoly16 pk0) (modTHatPoly16 pk1) (modTHatPoly16 pk2)
      (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
    let e2 := neonCbd2Poly16 (shake256List 128 (coins ++ [6#8]))
    let c1' := (indCpaEncryptWith sampleNtt 3 10 4 pk m' coins).1
    let c2' := neonCompressSerialize4
      (seg5FinalPoly (neonInvNttMontgomery16 dot) e2 (msgPoly16 m'))
    (if ct == c1' ++ c2' then kr.take 32 else shake256List 32 (z ++ ct)) =
      mlkem768DecapsWith sampleNtt dk ct1 ct2 := by
  dsimp only [mlkem768DecapsWith]
  have hct1_t : ct1.take 960 = ct1 := List.take_of_length_le (Nat.le_of_eq hct1)
  have hct2_t : ct2.take 128 = ct2 := List.take_of_length_le (Nat.le_of_eq hct2)
  rw [hct1_t, hct2_t]
  set ct := ct1 ++ ct2
  set m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
  set pk := (dk.drop 1152).take 1184
  set hPk := (dk.drop 2336).take 32
  set kr := sha3_512List (m' ++ hPk)
  have hcoins_len : (kr.drop 32).length = 32 := by
    simp [kr, List.length_drop, sha3_512List_length]
  have hcoins_t : (kr.drop 32).take 32 = kr.drop 32 :=
    List.take_of_length_le (Nat.le_of_eq hcoins_len)
  rw [hcoins_t]
  have hpk0 : (dk.drop 1152).take 384 = pk.take 384 := by
    simp [pk, List.take_take]
  have hpk1 : (dk.drop 1536).take 384 = (pk.drop 384).take 384 := by
    simp [pk, List.drop_take, List.drop_drop, List.take_take]
  have hpk2 : (dk.drop 1920).take 384 = (pk.drop 768).take 384 := by
    simp [pk, List.drop_take, List.drop_drop, List.take_take]
  rw [hpk0, hpk1, hpk2, decapsCt2_eq (indCpaDecrypt_len32 _ _) hcoins_len]

/-! ## 2. Stack Frame Split & Rejoin (`26,960 = 1,136 + 25,664 + 160`) -/

private theorem split_4912_seg8 (sp : BitVec 64) :
    memRegion (sp + 20704#64) 4912 =
      memRegion (sp + 20704#64) 512 ∗ memRegion (sp + 21216#64) 1184 ∗
      memRegion (sp + 22400#64) 512 ∗ memRegion (sp + 22912#64) 576 ∗
      memRegion (sp + 23488#64) 448 ∗ memRegion (sp + 23936#64) 512 ∗
      memRegion (sp + 24448#64) 512 ∗ memRegion (sp + 24960#64) 656 := by
  rw [memRegion_split' (b' := sp + 21216#64) (n := 512) (k := (4400 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 22400#64) (n := 1184) (k := (3216 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 22912#64) (n := 512) (k := (2704 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 23488#64) (n := 576) (k := (2128 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 23936#64) (n := 448) (k := (1680 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 24448#64) (n := 512) (k := (1168 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 24960#64) (n := 512) (k := (656 : Nat)) rfl (by bv_omega) (by decide)]

private theorem aTransRow_entails_1536 (sp : BitVec 64) (rho : List (BitVec 8)) (row : Nat)
    (_hrow : row < 3) :
    ATransRowMemAt sp 7216 rho row ⊢
      memRegion (sp + BitVec.ofNat 64 (7216 + 1536 * row)) 1536 := by
  unfold ATransRowMemAt
  rw [memRegion_split' (b' := sp + BitVec.ofNat 64 (7216 + 1536 * row + 512))
      (n := 512) (k := (1024 : Nat)) rfl (by clear * - _hrow; bv_omega) (by decide),
    memRegion_split' (b' := sp + BitVec.ofNat 64 (7216 + 1536 * row + 1024))
      (n := 512) (k := (512 : Nat)) rfl (by clear * - _hrow; bv_omega) (by decide)]
  exact sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
    (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _) (vecRangeMem_entails_memRegion 32 _ _))

private theorem aTransMemAt_entails_4608 (sp : BitVec 64) (rho : List (BitVec 8)) :
    ATransMemAt sp 7216 rho ⊢ memRegion (sp + 7216#64) 4608 := by
  unfold ATransMemAt
  rw [memRegion_split' (b' := sp + 8752#64) (n := 1536) (k := (3072 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 10288#64) (n := 1536) (k := (1536 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (aTransRow_entails_1536 sp rho 0 (by decide))
    (sepConj_mono (aTransRow_entails_1536 sp rho 1 (by decide))
      (aTransRow_entails_1536 sp rho 2 (by decide)))

private theorem poly3_entails_1536 (sp : BitVec 64) (off : Nat) (_hoff : off + 1536 ≤ 25664)
    (f0 f1 f2 : Nat → BitVec 128) :
    PolyMem (sp + BitVec.ofNat 64 off) f0 ∗
      PolyMem (sp + BitVec.ofNat 64 (off + 512)) f1 ∗
      PolyMem (sp + BitVec.ofNat 64 (off + 1024)) f2 ⊢
      memRegion (sp + BitVec.ofNat 64 off) 1536 := by
  rw [memRegion_split' (b' := sp + BitVec.ofNat 64 (off + 512))
      (n := 512) (k := (1024 : Nat)) rfl (by clear * - _hoff; bv_omega) (by decide),
    memRegion_split' (b' := sp + BitVec.ofNat 64 (off + 1024))
      (n := 512) (k := (512 : Nat)) rfl (by clear * - _hoff; bv_omega) (by decide)]
  exact sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
    (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _) (vecRangeMem_entails_memRegion 32 _ _))

private theorem memRegion_25664_seg8_eq (sp : BitVec 64) :
    memRegion sp 25664 =
      memRegion sp 8 ∗ memRegion (sp + 8#64) 128 ∗ memRegion (sp + 136#64) 8 ∗
      memRegion (sp + 144#64) 1168 ∗ memRegion (sp + 1312#64) 512 ∗
      memRegion (sp + 1824#64) 96 ∗ memRegion (sp + 1920#64) 336 ∗
      memRegion (sp + 2256#64) 1088 ∗ memRegion (sp + 3344#64) 1088 ∗
      memRegion (sp + 4432#64) 64 ∗ memRegion (sp + 4496#64) 32 ∗ memRegion (sp + 4528#64) 32 ∗
      memRegion (sp + 4560#64) 1120 ∗ memRegion (sp + 5680#64) 1536 ∗
      memRegion (sp + 7216#64) 4608 ∗ memRegion (sp + 11824#64) 32 ∗
      memRegion (sp + 11856#64) 1536 ∗ memRegion (sp + 13392#64) 4640 ∗
      memRegion (sp + 18032#64) 1088 ∗ memRegion (sp + 19120#64) 48 ∗
      memRegion (sp + 19168#64) 1536 ∗ memRegion (sp + 20704#64) 512 ∗
      memRegion (sp + 21216#64) 1184 ∗ memRegion (sp + 22400#64) 1088 ∗
      memRegion (sp + 23488#64) 448 ∗ memRegion (sp + 23936#64) 512 ∗
      memRegion (sp + 24448#64) 512 ∗ memRegion (sp + 24960#64) 656 ∗
      memRegion (sp + 25616#64) 32 ∗ memRegion (sp + 25648#64) 16 := by
  rw [memRegion_split' (b' := sp + 8#64) (n := 8) (k := (25656 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 136#64) (n := 128) (k := (25528 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 144#64) (n := 8) (k := (25520 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 1312#64) (n := 1168) (k := (24352 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 1824#64) (n := 512) (k := (23840 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 1920#64) (n := 96) (k := (23744 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2256#64) (n := 336) (k := (23408 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 3344#64) (n := 1088) (k := (22320 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 4432#64) (n := 1088) (k := (21232 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 4496#64) (n := 64) (k := (21168 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 4528#64) (n := 32) (k := (21136 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 4560#64) (n := 32) (k := (21104 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 5680#64) (n := 1120) (k := (19984 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 7216#64) (n := 1536) (k := (18448 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 11824#64) (n := 4608) (k := (13840 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 11856#64) (n := 32) (k := (13808 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 13392#64) (n := 1536) (k := (12272 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 18032#64) (n := 4640) (k := (7632 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 19120#64) (n := 1088) (k := (6544 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 19168#64) (n := 48) (k := (6496 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 20704#64) (n := 1536) (k := (4960 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 21216#64) (n := 512) (k := (4448 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 22400#64) (n := 1184) (k := (3264 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 23488#64) (n := 1088) (k := (2176 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 23936#64) (n := 448) (k := (1728 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 24448#64) (n := 512) (k := (1216 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 24960#64) (n := 512) (k := (704 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 25616#64) (n := 656) (k := (48 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 25616#64) (b' := sp + 25648#64)
      (n := 32) (k := (16 : Nat)) rfl (by bv_omega) (by decide)]

private theorem seg8_rest_entails (sp : BitVec 64) {ct coins : List (BitVec 8)}
    (hct : ct.length = 1088) (hcoins : coins.length = 32)
    (w : Nat → BitVec 32) (rho : List (BitVec 8))
    (fe2 ft0 ft1 ft2 fr0 fr1 fr2 fm : Nat → BitVec 128) :
    WordRangeMem 32 (sp + 8#64) w ∗ PolyMem (sp + 1312#64) fe2 ∗
      ((sp + 2256#64) ↦ₛ ct) ∗ ((sp + 4528#64) ↦ₛ coins) ∗
      (PolyMem (sp + 5680#64) ft0 ∗ PolyMem (sp + 6192#64) ft1 ∗ PolyMem (sp + 6704#64) ft2) ∗
      ATransMemAt sp 7216 rho ∗
      (PolyMem (sp + 11856#64) fr0 ∗ PolyMem (sp + 12368#64) fr1 ∗ PolyMem (sp + 12880#64) fr2) ∗
      (PolyMem (sp + 19168#64) fm ∗ PolyMem (sp + 19680#64) fr1 ∗ PolyMem (sp + 20192#64) fr2) ∗
      PolyMem (sp + 24448#64) fe2 ⊢
      memRegion (sp + 8#64) 128 ∗ memRegion (sp + 1312#64) 512 ∗
      memRegion (sp + 2256#64) 1088 ∗ memRegion (sp + 4528#64) 32 ∗
      memRegion (sp + 5680#64) 1536 ∗ memRegion (sp + 7216#64) 4608 ∗
      memRegion (sp + 11856#64) 1536 ∗ memRegion (sp + 19168#64) 1536 ∗
      memRegion (sp + 24448#64) 512 := by
  have hw : WordRangeMem 32 (sp + 8#64) w ⊢ memRegion (sp + 8#64) 128 :=
    wordRangeMem_entails_memRegion 32 (sp + 8#64) w (by decide)
  have h2256 : ((sp + 2256#64) ↦ₛ ct) ⊢ memRegion (sp + 2256#64) 1088 := by
    simpa only [hct] using pointsToBytes_entails_memRegion (sp + 2256#64) ct
  have h4528 : ((sp + 4528#64) ↦ₛ coins) ⊢ memRegion (sp + 4528#64) 32 := by
    simpa only [hcoins] using pointsToBytes_entails_memRegion (sp + 4528#64) coins
  exact sepConj_mono hw
    (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
      (sepConj_mono h2256
        (sepConj_mono h4528
          (sepConj_mono (poly3_entails_1536 sp 5680 (by decide) ft0 ft1 ft2)
            (sepConj_mono (aTransMemAt_entails_4608 sp rho)
              (sepConj_mono (poly3_entails_1536 sp 11856 (by decide) fr0 fr1 fr2)
                (sepConj_mono (poly3_entails_1536 sp 19168 (by decide) fm fr1 fr2)
                  (vecRangeMem_entails_memRegion 32 _ _))))))))

/-! ## 3. Segment 8 End-to-End Composition (`+0xabd8 → ret`) -/

attribute [local irreducible]
  blkPC04 sha3_512List shake256List indCpaDecrypt indCpaEncryptWith mlkem768DecapsWith
  neonCbd2Poly16 modTHatPoly16 rHatPoly16 msgPoly16 neonDot3 neonInvNttMontgomery16
  seg5FinalPoly neonCompressSerialize4 ATransMemAt

/-- Segment 8 (`+0xabd8 → ret`): completes `B04` from `Seg7Spatial`, writing
    `mlkem768DecapsWith sampleNtt dk ct1 ct2` to `ret` and restoring `stackAt s0.sp 26960`
    and all callee-saved registers. -/
theorem seg8_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 s : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (hdk : dk.length = 2400) (hct1 : ct1.length = 960) (hct2 : ct2.length = 128)
    (hsp0 : s0.spAligned = true)
    (hpc : s.pc = b + offSeg8Start) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hsp : s.sp = s0.sp - 25824#64) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = (s0.sp - 25824#64) + 11856#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (Seg7Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 (memRegion ret 32 ∗ F))
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((ret ↦ₛ mlkem768DecapsWith sampleNtt dk ct1 ct2) ∗
          (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗
          stackAt s0.sp 26960 ∗ F)) := by
  let sp := s0.sp - 25824#64
  let ct := ct1 ++ ct2
  let m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
  let pk := (dk.drop 1152).take 1184
  let rho := (dk.drop 2304).take 32
  let hPk := (dk.drop 2336).take 32
  let z := (dk.drop 2368).take 32
  let kr := sha3_512List (m' ++ hPk)
  let coins := kr.drop 32
  let pk0 := (dk.drop 1152).take 384
  let pk1 := (dk.drop 1536).take 384
  let pk2 := (dk.drop 1920).take 384
  let prf0 := shake256List 128 (coins ++ [0#8])
  let prf1 := shake256List 128 (coins ++ [1#8])
  let prf2 := shake256List 128 (coins ++ [2#8])
  let prf6 := shake256List 128 (coins ++ [6#8])
  let ct1' := (indCpaEncryptWith sampleNtt 3 10 4 pk m' coins).1
  have hct : ct.length = 1088 := by dsimp only [ct]; rw [List.length_append, hct1, hct2]
  have hm' : m'.length = 32 := indCpaDecrypt_len32 _ _
  have hkr : kr.length = 64 := sha3_512List_length _
  have hkGood : (kr.take 32).length = 32 := by simp [List.length_take, hkr]
  have hcoins : coins.length = 32 := by simp [coins, List.length_drop, hkr]
  have hkRej : (shake256List 32 (z ++ ct)).length = 32 := shake256List_length 32 _
  have hct1' : ct1'.length = 960 := indCpaEncryptWith_ct1_len960 pk m' coins
  have h432 : memRegion (sp + 1824#64) 432 =
      memRegion (sp + 1824#64) 96 ∗ memRegion (sp + 1920#64) 336 :=
    memRegion_split' (b' := sp + 1920#64) (n := 96) (k := (336 : Nat)) rfl (by bv_omega) (by decide)
  have h176 : memRegion (sp + 18992#64) 176 =
      memRegion (sp + 18992#64) 128 ∗ memRegion (sp + 19120#64) 48 :=
    memRegion_split' (b' := sp + 19120#64) (n := 128) (k := (48 : Nat)) rfl (by bv_omega) (by decide)
  have hkr_sp : ((sp + 4496#64) ↦ₛ kr) =
      ((sp + 4496#64) ↦ₛ kr.take 32) ∗ ((sp + 4528#64) ↦ₛ coins) := by
    conv_lhs => rw [← List.take_append_drop 32 kr]
    rw [pointsToBytes_append, hkGood, show (sp + 4496#64) + BitVec.ofNat 64 32 = sp + 4528#64 by bv_omega]
  dsimp only [Seg7Spatial]
  rw [h432, h176, hkr_sp, split_4912_seg8 sp]
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl hro
      (seg8a_ok hb s sp (sp + 11856#64) (s0.sp - 96#64) hm' (neonCbd2Poly16 prf6) (rHatPoly16 prf0) _
        hpc hrun hsp hspA hcl hro hx19 hfp) ?_)
  rintro s1 _ hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx19_1, hfp1, hacc1, t0, rfl⟩
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl1 hro1
      (seg8b_ok hb s1 sp (s0.sp - 96#64) t0
        (modTHatPoly16 pk0) (modTHatPoly16 pk1) (modTHatPoly16 pk2)
        (rHatPoly16 prf0) (rHatPoly16 prf1) (rHatPoly16 prf2)
        (neonCbd2Poly16 prf6) (msgPoly16 m') _
        hpc1 hrun1 hsp1 hspA1 hcl1 hro1
        hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1 hx19_1 hfp1 hacc1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hP2⟩
  have h1088 : memRegion (sp + 22400#64) 512 ∗ memRegion (sp + 22912#64) 576 =
      memRegion (sp + 22400#64) 1088 :=
    (memRegion_split' (b' := sp + 22912#64) (n := 512) (k := (576 : Nat)) rfl (by bv_omega) (by decide)).symm
  refine SepWP.weaken_pre (Entails.trans hP2 (by rw [← h1088]; sep_frame))
    (SepWP.mono
      (seg8c_ok hb s0 s2 ret _ ct ct1' (kr.take 32) (shake256List 32 (z ++ ct)) _
        hct hct1' hkGood hkRej hsp0 hpc2 hrun2 hsp2 hspA2 hfp2 hcl2 hro2) ?_)
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  rw [decaps_output_eq hdk hct1 hct2, stackAt_26960_eq s0.sp sp rfl, memRegion_25664_seg8_eq sp]
  have hsub := seg8_rest_entails sp hct hcoins (msgWordFn m') rho
    (polyVecNat (neonCbd2Poly16 prf6))
    (polyVecNat (modTHatPoly16 pk0)) (polyVecNat (modTHatPoly16 pk1)) (polyVecNat (modTHatPoly16 pk2))
    (polyVecNat (rHatPoly16 prf0)) (polyVecNat (rHatPoly16 prf1)) (polyVecNat (rHatPoly16 prf2))
    (polyVecNat (msgPoly16 m'))
  exact Entails.trans (by sep_frame) (Entails.trans (sepConj_mono_left hsub) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8

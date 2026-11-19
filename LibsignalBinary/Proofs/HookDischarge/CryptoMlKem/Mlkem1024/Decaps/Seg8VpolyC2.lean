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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7UvecC1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8MpolyInit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Ser5 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Dot3
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvAdd

/-!
# `kyber_decapsulate` (`B06`) — Segment 8 Full `vPoly` + `c₂'` + `ct'` (`+0xb308 .. +0xd89c`)

Composes `Seg8MpolyInit`, `Seg8Dot3`, `Seg8InvAdd`, and `Seg8Ser5` (`+0xb308 → +0xd89c`),
producing the full `1,568`-byte FO re-encryption ciphertext `ct' = c₁' ++ c₂'` matching
`(indCpaEncryptWith sampleNtt 4 11 5 pk m coins).1 ++ (indCpaEncryptWith sampleNtt 4 11 5 pk m coins).2.1`
at both `[sp + 24704, sp + 26272)` and `[sp + 30448, sp + 32016)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8VpolyC2

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 byteDecodeMod compressAndEncode decodeAndDecompress indCpaEncryptWith
  neonBarrettReduce16 neonInvNttMontgomery16 neonMontgomeryMul16 polyAdd polyInvNtt polyNtt
  sampleMatrixWith sampleNtt samplePolyCbd2 sampleVecCbd2 shake256List vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonBarrettReducePoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt (
  byteDecodeMod_canonical neonPolyInvNttFromMontInv16 neonPolyInvNttFromMontInv16_spec
  vecDotNtt_canonical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents neonVecDotNtt4_spec polyAdd16 polyAdd16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16 neonCbd2Poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (decodeAndDecompress_poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (byteDecodeRaw_lt_two_pow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (msgPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16_size neonDot3 polyAdd16_size upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure (upperInvNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (seg5FinalPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem Spill13Mem polyVecNat spill13Mem_entails_memRegion vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (shake256List_len)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  pkEk0 pkEk1 pkEk2 pkEk3 pkRho tHatModPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (blkPC06 blkPl06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul (neonDot4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1 (SpilledDecapsWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure (PublicKeyStateAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt (
  rHatPoly16 rHatPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7UvecC1 (
  c1Bytes06 c1Bytes06_length c1Bytes06_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8MpolyInit (
  offSeg8Start seg8_mpoly_init_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Dot3 (seg8_dot3_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvAdd (seg8_inv_add_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Ser5 (
  neonCompressSerialize5Poly neonCompressSerialize5Poly_eq offSeg9Start seg8_ser5_ok)

/-! ## 1. Pure `decapsVPoly16` & `ct'` Soundness Against `Spec.indCpaEncryptWith` -/

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

/-- `Poly16` result of Segment 8 (`v = InvNTT(t̂ᵀ ∘ r̂) + e₂ + Decompress₁(m)`). -/
def decapsVPoly16 (pk m coins : List (BitVec 8)) : Poly16 :=
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
theorem decapsVPoly16_spec {pk m coins : List (BitVec 8)}
    (hm : m.length = 32) (hcoins : coins.length = 32) :
    let tHat : Array Poly := Array.ofFn (n := 4) fun ⟨i, _⟩ =>
      byteDecodeMod 12 ((pk.drop (384 * i)).take 384)
    let rHat := (sampleVecCbd2 4 coins 0).map polyNtt
    let e2 := samplePolyCbd2 (shake256List 128 (coins.take 32 ++ [BitVec.ofNat 8 (2 * 4)]))
    let mPoly := decodeAndDecompress 1 (m.take 32)
    let vPoly := polyAdd (polyAdd (polyInvNtt (vecDotNtt 4 tHat rHat)) e2) mPoly
    PolyBounded16 1664 (decapsVPoly16 pk m coins) ∧
    PolyRepresents (decapsVPoly16 pk m coins) vPoly := by
  dsimp only; unfold decapsVPoly16
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

private theorem decaps_reencrypt_c1_eq (pk : List (BitVec 8)) {m coins : List (BitVec 8)}
    (hcoins : coins.length = 32) :
    c1Bytes06 (pkRho pk) coins =
      (indCpaEncryptWith sampleNtt 4 11 5 pk m coins).1 := by
  have hrho_eq : pkRho pk = (pk.drop (384 * 4)).take 32 := rfl
  have hc1 := c1Bytes06_spec ((pk.drop (384 * 4)).take 32) hcoins
  dsimp only [indCpaEncryptWith]
  have hr4 : List.range 4 = [0, 1, 2, 3] := by decide
  rw [hrho_eq, hc1, hr4]
  simp [Array.getD]

private theorem decaps_reencrypt_c2_eq (pk : List (BitVec 8)) {m coins : List (BitVec 8)}
    (hm : m.length = 32) (hcoins : coins.length = 32) :
    neonCompressSerialize5Poly (decapsVPoly16 pk m coins) =
      (indCpaEncryptWith sampleNtt 4 11 5 pk m coins).2.1 := by
  obtain ⟨hvb, hvr⟩ := decapsVPoly16_spec (pk := pk) hm hcoins
  dsimp only [indCpaEncryptWith]
  refine (neonCompressSerialize5Poly_eq hvb hvr).trans ?_
  apply congrArg (compressAndEncode 5)
  refine congrArg₂ polyAdd ?_ rfl
  refine congrArg₂ polyAdd ?_ rfl
  apply congrArg polyInvNtt
  refine congrArg₂ (vecDotNtt 4) ?_ rfl
  apply Array.ext
  · simp
  · intro i hi1 hi2
    simp

end PureVPoly

/-- Pure re-encryption equivalence: `c₁' ++ c₂'` computed by `Seg7UvecC1` + `Seg8VpolyC2` equals
    `(indCpaEncryptWith sampleNtt 4 11 5 pk m coins).1 ++ (indCpaEncryptWith sampleNtt 4 11 5 pk m coins).2.1`. -/
theorem decaps_reencrypt_eq (pk : List (BitVec 8)) {m coins : List (BitVec 8)}
    (hm : m.length = 32) (hcoins : coins.length = 32) :
    c1Bytes06 (pkRho pk) coins ++ neonCompressSerialize5Poly (decapsVPoly16 pk m coins) =
      (indCpaEncryptWith sampleNtt 4 11 5 pk m coins).1 ++
      (indCpaEncryptWith sampleNtt 4 11 5 pk m coins).2.1 :=
  congrArg₂ (· ++ ·) (decaps_reencrypt_c1_eq pk hcoins) (decaps_reencrypt_c2_eq pk hm hcoins)

/-! ## 2. Spatial Helpers & Composed Segment 8 (`+0xb308 → +0xd89c`) -/

private theorem publicKeyStateAt_4160_eq (sp : BitVec 64) (pk : List (BitVec 8)) :
    PublicKeyStateAt (sp + 4160#64) pk =
      (Seg6CbdPure.ATransAt (sp + 4160#64) (pkRho pk) ∗
        PolyMem (sp + 12352#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        PolyMem (sp + 12864#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        PolyMem (sp + 13376#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
        PolyMem (sp + 13888#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
        ((sp + 14400#64) ↦ₛ List.replicate 32 0#8)) := by
  dsimp only [PublicKeyStateAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem split_2224_96 (sp : BitVec 64) :
    memRegion (sp + 2224#64) 208 = memRegion (sp + 2224#64) 96 ∗ memRegion (sp + 2320#64) 112 := by
  simpa using memRegion_split' (b := sp + 2224#64) (b' := sp + 2320#64) (n := 96) (k := (112 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_30448_512 (sp : BitVec 64) :
    memRegion (sp + 30448#64) 1568 = memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 30960#64) 1056 := by
  simpa using memRegion_split' (b := sp + 30448#64) (b' := sp + 30960#64) (n := 512) (k := (1056 : Nat))
    rfl (by bv_omega) (by decide)


/-- Full Segment 8 (`+0xb308 → +0xd89c`): `vPoly` (`e₂` copy + `decompress_1(m)` + 4-way dot +
    `InvNTT` + Barrett) + `compress_and_serialize_5` (`c₂'`) + `memcpy` (`1,568`-byte `ct'`). -/
theorem seg8_vpoly_c2_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA fpVal : BitVec 64) (pk : List (BitVec 8))
    {m coins : List (BitVec 8)} (hm : m.length = 32) (hcoins : coins.length = 32)
    (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = sp + 12352#64) (hx20 : s.readReg64 .x20 = sp + 14432#64)
    (hfp : s.readReg64 .fp = fpVal)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
    let e2 := neonCbd2Poly16 (shake256List 128 (coins ++ [8#8]))
    let ct' := (indCpaEncryptWith sampleNtt 4 11 5 pk m coins).1 ++
      (indCpaEncryptWith sampleNtt 4 11 5 pk m coins).2.1
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg9Start) s
      (SpilledDecapsWords sp m ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗ memRegion (sp + 2224#64) 208 ∗
        PublicKeyStateAt (sp + 4160#64) pk ∗
        PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
        PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
        ((sp + 24704#64) ↦ₛ c1Bytes06 (pkRho pk) coins) ∗ memRegion (sp + 26112#64) 160 ∗
        memRegion (sp + 26320#64) 512 ∗ memRegion (sp + 28368#64) 512 ∗
        memRegion (sp + 30448#64) 1568 ∗ memRegion (sp + 32496#64) 512 ∗
        memRegion (sp + 33008#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 1568#64 ∧ sf.readReg64 .x22 = ctA ∧ sf.readReg64 .fp = fpVal ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ SpilledDecapsWords sp m ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
          PolyMem (sp + 1488#64) (polyVecNat e2) ∗ memRegion (sp + 2224#64) 208 ∗
          PublicKeyStateAt (sp + 4160#64) pk ∗
          PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
          PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
          ((sp + 24704#64) ↦ₛ ct') ∗ memRegion (sp + 26320#64) 512 ∗
          memRegion (sp + 28368#64) 512 ∗ ((sp + 30448#64) ↦ₛ ct') ∗
          memRegion (sp + 32496#64) 512 ∗ memRegion (sp + 33008#64) 512 ∗ Rest)) := by
  intro r0 r1 r2 r3 e2 ct'
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl hro
      (seg8_mpoly_init_ok hb s sp ctA (sp + 12352#64) (sp + 14432#64) fpVal hm e2 _
        hpc hrun hsp hspA hcl hro hx19 hx20 hfp) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx19_1, hx20_1, hx22_1, hfp1, hacc1, rfl⟩
  refine SepWP.weaken_pre (by rw [publicKeyStateAt_4160_eq sp pk, split_30448_512 sp]; sep_frame)
    (sepWP_seq_env hcl1 hro1
      (seg8_dot3_ok hb s1 sp ctA fpVal
        (tHatModPoly16 (pkEk0 pk)) (tHatModPoly16 (pkEk1 pk))
        (tHatModPoly16 (pkEk2 pk)) (tHatModPoly16 (pkEk3 pk))
        r0 r1 r2 r3 _ _
        hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx19_1 hx20_1 hx22_1 hfp1 hacc1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx22_2, hfp2, hP2⟩
  set dot := neonDot4
    (tHatModPoly16 (pkEk0 pk)) (tHatModPoly16 (pkEk1 pk))
    (tHatModPoly16 (pkEk2 pk)) (tHatModPoly16 (pkEk3 pk))
    r0 r1 r2 r3
  have hdot_sz : dot.size = 256 := polyAdd16_size _ _
  have hm2224 : Spill13Mem (sp + 2224#64) (Mlkem768.Encaps2.Seg3a.AccSpill dot) ⊢
      memRegion (sp + 2224#64) 96 ∗ memRegion (sp + 2320#64) 112 := by
    rw [← split_2224_96 sp]
    exact spill13Mem_entails_memRegion (sp + 2224#64) _
  have hP2' : P2 ⊢ memRegion (sp + 2320#64) 112 ∗
      PolyMem (sp + 26320#64) (polyVecNat (msgPoly16 m)) ∗
      PolyMem (sp + 28368#64) (polyVecNat dot) ∗
      memRegion (sp + 32496#64) 512 ∗
      PolyMem (sp + 33008#64) (polyVecNat e2) ∗
      (SpilledDecapsWords sp m ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗ memRegion (sp + 2224#64) 96 ∗
        PublicKeyStateAt (sp + 4160#64) pk ∗
        PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
        PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
        ((sp + 24704#64) ↦ₛ c1Bytes06 (pkRho pk) coins) ∗ memRegion (sp + 26112#64) 160 ∗
        memRegion (sp + 30448#64) 1568 ∗ Rest) := by
    refine Entails.trans hP2 ?_
    rw [publicKeyStateAt_4160_eq sp pk, split_30448_512 sp]
    refine entails_sub (Rest :=
        PolyMem (sp + 12352#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        PolyMem (sp + 12864#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        PolyMem (sp + 13376#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
        PolyMem (sp + 13888#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
        PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
        PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
        PolyMem (sp + 28368#64) (polyVecNat dot) ∗ memRegion (sp + 30448#64) 512 ∗
        PolyMem (sp + 26320#64) (polyVecNat (msgPoly16 m)) ∗
        memRegion (sp + 32496#64) 512 ∗ PolyMem (sp + 33008#64) (polyVecNat e2) ∗
        SpilledDecapsWords sp m ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗ Seg6CbdPure.ATransAt (sp + 4160#64) (pkRho pk) ∗
        ((sp + 14400#64) ↦ₛ List.replicate 32 0#8) ∗
        ((sp + 24704#64) ↦ₛ c1Bytes06 (pkRho pk) coins) ∗ memRegion (sp + 26112#64) 160 ∗
        memRegion (sp + 30960#64) 1056 ∗ Rest) hm2224 (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP2'
    (sepWP_seq_env hcl2 hro2
      (seg8_inv_add_ok hb hbase s2 sp hdot_sz e2 (msgPoly16 m) _
        hpc2 hrun2 hsp2 hspA2 hcl2 hro2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hx22_3, hfp3, hP3⟩
  have hv_eq : seg5FinalPoly (neonInvNttMontgomery16 dot) e2 (msgPoly16 m) =
      decapsVPoly16 pk m coins := rfl
  have hP3' : P3 ⊢ ((sp + 24704#64) ↦ₛ c1Bytes06 (pkRho pk) coins) ∗
      memRegion (sp + 26112#64) 160 ∗ memRegion (sp + 30448#64) 1568 ∗
      PolyMem (sp + 32496#64) (polyVecNat (decapsVPoly16 pk m coins)) ∗
      (SpilledDecapsWords sp m ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗ memRegion (sp + 2224#64) 208 ∗
        PublicKeyStateAt (sp + 4160#64) pk ∗
        PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
        PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
        memRegion (sp + 26320#64) 512 ∗ memRegion (sp + 28368#64) 512 ∗
        memRegion (sp + 33008#64) 512 ∗ Rest) := by
    refine Entails.trans hP3 ?_
    rw [hv_eq, split_2224_96 sp]; sep_frame
  refine SepWP.weaken_pre hP3'
    (sepWP_seq_env hcl3 hro3
      (seg8_ser5_ok hb hbase s3 sp (c1Bytes06_length (pkRho pk) coins) (decapsVPoly16 pk m coins) _
        hpc3 hrun3 hsp3 hspA3 hcl3) ?_)
  rintro sf Pf hpc_f hrun_f hcl_f hro_f ⟨hsp_f, hspA_f, hx19_f, hx22_f, hfp_f, hPf⟩
  refine SepWP.done hpc_f hrun_f
    ⟨hsp_f, hspA_f, hx19_f, hx22_f.trans (hx22_3.trans hx22_2), hfp_f.trans (hfp3.trans hfp2),
      hcl_f, hro_f, ?_⟩
  refine Entails.trans hPf ?_
  rw [decaps_reencrypt_eq pk hm hcoins]
  have hm32496 : PolyMem (sp + 32496#64) (polyVecNat (decapsVPoly16 pk m coins)) ⊢
      memRegion (sp + 32496#64) 512 :=
    vecRangeMem_entails_memRegion 32 (sp + 32496#64) (polyVecNat (decapsVPoly16 pk m coins))
  exact entails_sub (Rest := ((sp + 24704#64) ↦ₛ ct') ∗ ((sp + 30448#64) ↦ₛ ct') ∗
      SpilledDecapsWords sp m ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
      PolyMem (sp + 1488#64) (polyVecNat e2) ∗ memRegion (sp + 2224#64) 208 ∗
      PublicKeyStateAt (sp + 4160#64) pk ∗
      PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
      PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
      memRegion (sp + 26320#64) 512 ∗ memRegion (sp + 28368#64) 512 ∗
      memRegion (sp + 33008#64) 512 ∗ Rest)
    hm32496 (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8VpolyC2

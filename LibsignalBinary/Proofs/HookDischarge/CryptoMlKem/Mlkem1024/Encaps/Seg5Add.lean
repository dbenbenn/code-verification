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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Sym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Rhat
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5InvSym

/-!
# `kyber::encapsulate` (`B07`) — Segment 5 Upper `InvNTT` + `e₂` + `mPoly` (`+0x840c .. +0x9d34`)

Proves `seg5_add_ok` (`+0x840c → +0x9d34`): upper 5-stage `InvNTT` via `Seg5InvSym`,
`B28` `memcpy`, and 16-iteration normalizer + `e₂` + `msgPoly` + Barrett loop,
plus pure `vPoly16_spec` soundness against `Spec.indCpaEncryptWith`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Add

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 byteDecodeMod decodeAndDecompress neonBarrettReduce16 neonInvNttMontgomery16
  neonMontgomeryMul16 polyAdd polyInvNtt polyNtt samplePolyCbd2 sampleVecCbd2 shake256List
  vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (shake256List_len)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMla8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h)
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (msgPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec32 VecRangeMem
  poly32Mem_ofFn polyVecNat step_ldpQ128 step_ldrQ128 step_stpQ128 vecRangeBytes
  vecRangeBytes_length vecRangeMem_congr vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16 lowerInvNtt16_size polyAdd16_size upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure (upperInvNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdMla_8h svc_simdMovi_8h_1024 svc_simdMul_8h
  svc_simdMvni_8h_f2ff svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSshr_8h_11 svc_simdSub_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (seg5FinalPoly seg5Loop1_vec_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  Spill40 SpillSliceMem SymEnv SymGprs evalSymGpr symInitState)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SrcOptMem SymSpatial SymStateMatches polyPtr symSpill40_eval_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (poly_eq_upperInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul (neonDot4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07_code_eq blk07_tree_size blkLib07 blkPC07 blkPl07 blkPlaceable07 blkTree07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  pkEk0 pkEk1 pkEk2 pkEk3 tHatModPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (blk28_memcpy_07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Sym (
  Src12832OptMem SymSpatial07 sepWP_of_runSymRange07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Rhat (rHatPoly16 rHatPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5InvSym (
  cfgSeg5Inv noReloc_seg5_inv run_seg5_inv seg5_inv_ast_eq seg5_inv_noSpillVreg symSeg5InvEnd)

abbrev offSeg5InvUpper : BitVec 64 := BitVec.ofNat 64 0x840c
private abbrev offSeg5Memcpy : BitVec 64 := BitVec.ofNat 64 0x9c6c
private abbrev offSeg5Setup  : BitVec 64 := BitVec.ofNat 64 0x9c70
private abbrev offSeg5Loop   : BitVec 64 := BitVec.ofNat 64 0x9ca8
abbrev offSeg5Compress : BitVec 64 := BitVec.ofNat 64 0x9d34

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x9c6c → 0x9d30]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp] private theorem readReg64_orFpsr' (s : State) (f : BitVec 32) (r : Reg) :
    (s.orFpsr f).readReg64 r = s.readReg64 r := rfl
@[simp] private theorem readVReg128_orFpsr' (s : State) (f : BitVec 32) (v : BitVec 5) :
    (s.orFpsr f).readVReg128 v = s.readVReg128 v := rfl
@[simp] private theorem status_orFpsr' (s : State) (f : BitVec 32) :
    (s.orFpsr f).status = s.status := rfl

attribute [local irreducible]
  blkPC07 dup8x16 polyVecNat simdAdd8h simdSub8h simdMul8h simdMla8h simdSqdmulh8h simdSshr8h

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdMla_8h
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSshr_8h_11
  svc_simdMovi_8h_1024 svc_simdMvni_8h_f2ff svc_simdDup_8h_gpr

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

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g :=
  vecRangeMem_congr h

/-! ## 1. Pure `vPoly16` Soundness Against `Spec.indCpaEncryptWith` -/

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

/-- `Poly16` result of Segment 5 (`v = InvNTT(t̂ᵀ ∘ r̂) + e₂ + Decompress₁(m)`). -/
def vPoly16 (pk m coins : List (BitVec 8)) : Poly16 :=
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
theorem vPoly16_spec {pk m coins : List (BitVec 8)}
    (hm : m.length = 32) (hcoins : coins.length = 32) :
    let tHat : Array Poly := Array.ofFn (n := 4) fun ⟨i, _⟩ =>
      byteDecodeMod 12 ((pk.drop (384 * i)).take 384)
    let rHat := (sampleVecCbd2 4 coins 0).map polyNtt
    let e2 := samplePolyCbd2 (shake256List 128 (coins.take 32 ++ [BitVec.ofNat 8 (2 * 4)]))
    let mPoly := decodeAndDecompress 1 (m.take 32)
    let vPoly := polyAdd (polyAdd (polyInvNtt (vecDotNtt 4 tHat rHat)) e2) mPoly
    PolyBounded16 1664 (vPoly16 pk m coins) ∧
    PolyRepresents (vPoly16 pk m coins) vPoly := by
  dsimp only; unfold vPoly16
  have hd_sz : (neonDot4
      (tHatModPoly16 (pkEk0 pk)) (tHatModPoly16 (pkEk1 pk))
      (tHatModPoly16 (pkEk2 pk)) (tHatModPoly16 (pkEk3 pk))
      (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [3#8])))).size = 256 := polyAdd16_size _ _
  dsimp only [neonDot4, LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure.neonDot3] at hd_sz ⊢
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

end PureVPoly

/-! ## 2. Symbolic Upper `InvNTT` (`+0x840c → +0x9c6c`) -/

private def mkSeg5InvEnv (s : State) (f7 : Nat → BitVec 128) (p : Poly16) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := Spill40.ofFn fun i => if i < 7 then f7 i else 0#128
  poly0   := Vec32.ofFn (polyVecNat p)
  src0    := Vec32.zero
  gpr0    := fun r => s.readReg64 (.gpr r)
  pstate0 := s.pstate

private theorem matches_seg5InvInit {sp : BitVec 64} {s : State} (f7 : Nat → BitVec 128) (p : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SymStateMatches sp (mkSeg5InvEnv s f7 p) symInitState s := by
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
      simp [symInitState, SymGprs.ofFn, SymGprs.get, evalSymGpr, mkSeg5InvEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem spill7_eq_initSlice (ptr : BitVec 64) (s : State) (f7 : Nat → BitVec 128) (p : Poly16) :
    VecRangeMem 7 ptr f7 = SpillSliceMem 7 ptr (symInitState.spill.eval (mkSeg5InvEnv s f7 p)) :=
  vecRangeMem_congr fun i hi => by
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rfl
    | _ + 7 => omega

private theorem polyMem_eq_initPoly32 (ptr : BitVec 64) (s : State) (f7 : Nat → BitVec 128) (p : Poly16) :
    PolyMem ptr (polyVecNat p) = Poly32Mem ptr (symInitState.poly.eval (mkSeg5InvEnv s f7 p)) := by
  change PolyMem ptr (polyVecNat p) = Poly32Mem ptr (Vec32.ofFn (polyVecNat p))
  rw [poly32Mem_ofFn]

private theorem seg5_inv_upper_ok [MlKemPlacement] {b : BitVec 64}
    (s : State) (sp : BitVec 64) {dot : Poly16} (hdot : dot.size = 256)
    (f7 : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5InvUpper) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Memcpy) s
      (VecRangeMem 7 (sp + 2320#64) f7 ∗
        PolyMem (sp + 26768#64) (polyVecNat (lowerInvNtt16 dot)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = sp + 30896#64 ∧ sf.readReg64 .x1 = sp + 26768#64 ∧
        sf.readReg64 .x2 = 512#64 ∧ sf.readReg64 .x19 = sp + 30896#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        ∃ sp40 : Spill40,
          sp40.get 0 = dup8x16 20159#16 ∧ sp40.get 5 = dup8x16 3329#16 ∧
          (Pf ⊢ SpillSliceMem 7 (sp + 2320#64) sp40 ∗
            PolyMem (sp + 26768#64) (polyVecNat (neonInvNttMontgomery16 dot)) ∗ Rest)) := by
  let env := mkSeg5InvEnv s f7 (lowerInvNtt16 dot)
  have hpre : VecRangeMem 7 (sp + 2320#64) f7 ∗
      PolyMem (sp + 26768#64) (polyVecNat (lowerInvNtt16 dot)) ∗ Rest ⊢
      SymSpatial07 false cfgSeg5Inv sp env symInitState Rest := by
    simp only [SymSpatial07, SymSpatial, polyPtr, SrcOptMem, Src12832OptMem, cfgSeg5Inv,
      Bool.false_eq_true, ↓reduceIte]
    rw [spill7_eq_initSlice (sp + 2320#64) s f7 (lowerInvNtt16 dot),
      polyMem_eq_initPoly32 (sp + 26768#64) s f7 (lowerInvNtt16 dot)]
    sep_frame
  refine SepWP.weaken_pre hpre
    (sepWP_of_runSymRange07 (src12832 := false) (cfg := cfgSeg5Inv) (env := env) (F := Rest)
      1560 8451 noReloc_seg5_inv (by decide) (by decide) (by decide) run_seg5_inv
      (matches_seg5InvInit f7 (lowerInvNtt16 dot) hsp hspA) hpc hrun ?_)
  intro sf _ _ hmf
  rcases Seg5InvSym.symSeg5InvEnd_gprs with ⟨g0, g1, g2, g19, g29, _⟩
  rcases Seg5InvSym.symSeg5InvEnd_spills with ⟨sp0, sp5⟩
  have geq (r : Nat) (hr : BitVec.ofNat 5 r ≠ 31#5) (hlt : r < 32) :
      sf.readReg64 (.gpr (BitVec.ofNat 5 r)) = evalSymGpr sp env.gpr0 (symSeg5InvEnd.gprs.get r) :=
    by simpa [Nat.mod_eq_of_lt hlt] using hmf.hgprs (BitVec.ofNat 5 r) hr
  have hs0 : (symSeg5InvEnd.spill.eval env).get 0 = dup8x16 20159#16 := by
    rw [symSpill40_eval_get env symSeg5InvEnd.spill 0 (by decide), sp0]; rfl
  have hs5 : (symSeg5InvEnd.spill.eval env).get 5 = dup8x16 3329#16 := by
    rw [symSpill40_eval_get env symSeg5InvEnd.spill 5 (by decide), sp5]; rfl
  refine ⟨hmf.hsp, hmf.hsp_al,
    by have h := geq 0 (by decide) (by decide); rw [g0] at h; exact h,
    by have h := geq 1 (by decide) (by decide); rw [g1] at h; exact h,
    by have h := geq 2 (by decide) (by decide); rw [g2] at h; exact h,
    by have h := geq 19 (by decide) (by decide); rw [g19] at h; exact h,
    by have h := geq 29 (by decide) (by decide); rw [g29] at h; simpa [evalSymGpr, env, mkSeg5InvEnv] using h,
    symSeg5InvEnd.spill.eval env, hs0, hs5, ?_⟩
  simp only [SymSpatial07, SymSpatial, polyPtr, SrcOptMem, Src12832OptMem, cfgSeg5Inv,
    Bool.false_eq_true, ↓reduceIte]
  have hpoly_eq := poly_eq_upperInvNtt16 (sp + 26768#64) (lowerInvNtt16_size hdot) env rfl
    symSeg5InvEnd.poly seg5_inv_noSpillVreg seg5_inv_ast_eq
  rw [hpoly_eq, upperInvNtt16_lowerInvNtt16]
  sep_frame

/-! ## 3. `B28` `memcpy` + 16-Iter `seg5FinalPoly` Loop (`+0x9c6c → +0x9d34`) -/

private theorem seg5_add_memcpy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (inv : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Memcpy) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 30896#64) (hx1 : s.readReg64 .x1 = sp + 26768#64)
    (hx2 : s.readReg64 .x2 = 512#64) (hx19 : s.readReg64 .x19 = sp + 30896#64)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Setup) s
      (memRegion (sp + 30896#64) 512 ∗ PolyMem (sp + 26768#64) (polyVecNat inv) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x19 = sp + 30896#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        Pf = (PolyMem (sp + 30896#64) (polyVecNat inv) ∗
          PolyMem (sp + 26768#64) (polyVecNat inv) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs_def : vecRangeBytes 32 (polyVecNat inv) = bsInv
  have hbs : bsInv.length = 512 := by rw [← hbs_def, vecRangeBytes_length]
  have hp26768 : PolyMem (sp + 26768#64) (polyVecNat inv) = ((sp + 26768#64) ↦ₛ bsInv) := by
    rw [← hbs_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp30896 : ((sp + 30896#64) ↦ₛ bsInv) = PolyMem (sp + 30896#64) (polyVecNat inv) := by
    rw [← hbs_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  rw [hp26768]
  wp_call (blk28_memcpy_07 blkPl07.base) (sp + 30896#64, sp + 26768#64, bsInv)
  rw [← hp26768, hp30896]
  have hsp_sf : sf.sp = sp := by simp [*]
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*], by simp [*],
      sepProp_ext (by sep_frame) (by sep_frame)⟩

private theorem seg5_add_setup [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (s : State) (sp : BitVec 64) (sp40 : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Setup) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = sp + 30896#64)
    (hs0 : sp40.get 0 = dup8x16 20159#16) (hs5 : sp40.get 5 = dup8x16 3329#16) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Loop) s
      (SpillSliceMem 7 (sp + 2320#64) sp40 ∗ Rest)
      (fun s5 P5 =>
        s5.sp = sp ∧ s5.spAligned = true ∧
        s5.readReg64 .x8 = sp + 30912#64 ∧ s5.readReg64 .x9 = sp + 24736#64 ∧
        s5.readReg64 .x10 = sp + 31424#64 ∧ s5.readReg64 .x11 = 16#64 ∧
        s5.readReg64 .x12 = 1441#64 ∧ s5.readReg64 .x13 = 55457#64 ∧
        s5.readReg64 .fp = s.readReg64 .fp ∧
        s5.readVReg128 16#5 = dup8x16 3329#16 ∧ s5.readVReg128 17#5 = dup8x16 20159#16 ∧
        s5.readVReg128 18#5 = dup8x16 1024#16 ∧ s5.readVReg128 19#5 = dup8x16 0xf2ff#16 ∧
        P5 = (SpillSliceMem 7 (sp + 2320#64) sp40 ∗ Rest)) := by
  have _ : b = blkPl07.base := _hb
  wp_steps 4
  refine step_ldrQ128 (wb := none) (ea := (sp + 2320#64) + BitVec.ofNat 64 (16 * 0))
    (v := dup8x16 20159#16) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (hs0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 7) (k := 0) (by decide) rfl))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := (sp + 2320#64) + BitVec.ofNat 64 (16 * 5))
    (v := dup8x16 3329#16) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (hs5 ▸ SepLoad128.left (SepLoad128.vecRange (n := 7) (k := 5) (by decide) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 8
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, rfl⟩

private theorem seg5_add_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (s : State) (sp : BitVec 64) (inv err2 msgPoly : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Loop) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = sp + 30912#64 + BitVec.ofNat 64 (32 * r))
    (hx9 : s.readReg64 .x9 = sp + 24736#64 + BitVec.ofNat 64 (32 * r))
    (hx10 : s.readReg64 .x10 = sp + 31424#64 + BitVec.ofNat 64 (32 * r))
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (16 - r))
    (hx12 : s.readReg64 .x12 = 1441#64) (hx13 : s.readReg64 .x13 = 55457#64)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16) (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv18 : s.readVReg128 18#5 = dup8x16 1024#16) (hv19 : s.readVReg128 19#5 = dup8x16 0xf2ff#16)
    (hhi0 : f (2 * r) = polyVecNat inv (2 * r))
    (hhi1 : f (2 * r + 1) = polyVecNat inv (2 * r + 1)) :
    SepWP (blkPC07.rebase b (fun _ => none))
      (if r < 15 then b + offSeg5Loop else b + offSeg5Compress) s
      (PolyMem (sp + 30896#64) f ∗ PolyMem (sp + 31408#64) (polyVecNat err2) ∗
        PolyMem (sp + 24720#64) (polyVecNat msgPoly) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = sp + 30912#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x9 = sp + 24736#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x10 = sp + 31424#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x11 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x12 = 1441#64 ∧ s'.readReg64 .x13 = 55457#64 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
        s'.readVReg128 18#5 = dup8x16 1024#16 ∧ s'.readVReg128 19#5 = dup8x16 0xf2ff#16 ∧
        P' = (PolyMem (sp + 30896#64)
          (Function.update
            (Function.update f (2 * r) (polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r)))
            (2 * r + 1) (polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r + 1))) ∗
          PolyMem (sp + 31408#64) (polyVecNat err2) ∗
          PolyMem (sp + 24720#64) (polyVecNat msgPoly) ∗ Rest)) := by
  have _ : b = blkPl07.base := _hb
  wp_step
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 30896#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 30896#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat inv (2 * r)) (v2 := polyVecNat inv (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_step
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 31408#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 31408#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat err2 (2 * r)) (v2 := polyVecNat err2 (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx10]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 6
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 24720#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 24720#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat msgPoly (2 * r)) (v2 := polyVecNat msgPoly (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx9]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))))
    (SepLoad128.right (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))))
    (by wp_norm_lhs) ?_
  wp_steps 21
  have hv1_eq := seg5Loop1_vec_eq inv err2 msgPoly (2 * r) (by omega) true
  have hv0_eq := seg5Loop1_vec_eq inv err2 msgPoly (2 * r + 1) (by omega) false
  dsimp only [Bool.false_eq_true, ↓reduceIte] at hv1_eq hv0_eq
  refine step_stpQ128 (wb := none)
    (ea := (sp + 30896#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 30896#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r))
    (v2 := polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by simp [← hv1_eq]) (by simp [← hv0_eq])
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'
  wp_steps 2
  wp_if hne
  · have hr15 : r < 15 := by
      clear * - hr hne hx11
      by_contra hge; have hr_eq : r = 15 := by omega
      subst hr_eq; simp_all
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * - hr15; bv_omega, by simp; clear * - hr15; bv_omega,
        by simp; clear * - hr15; bv_omega, by simp; clear * - hr15; bv_omega,
        by simp [hx12], by simp [hx13], by simp,
        by simp [hv16], by simp [hv17], by simp [hv18], by simp [hv19], rfl⟩
  · have hr15 : ¬ r < 15 := by
      clear * - hne hx11
      intro hlt
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r
      all_goals try simp_all
      omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hr_eq], by simp [hr_eq], by simp [hr_eq], by simp [hr_eq],
        by simp [hx12], by simp [hx13], by simp,
        by simp [hv16], by simp [hv17], by simp [hv18], by simp [hv19], rfl⟩

private theorem seg5_add_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl07 b)
    (sp fpv : BitVec 64) (inv err2 msgPoly : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 →
    ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offSeg5Loop → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = sp + 30912#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x9 = sp + 24736#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x10 = sp + 31424#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x11 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x12 = 1441#64 → s.readReg64 .x13 = 55457#64 →
      s.readReg64 .fp = fpv →
      s.readVReg128 16#5 = dup8x16 3329#16 → s.readVReg128 17#5 = dup8x16 20159#16 →
      s.readVReg128 18#5 = dup8x16 1024#16 → s.readVReg128 19#5 = dup8x16 0xf2ff#16 →
      (∀ j, j < 2 * r → f j = polyVecNat (seg5FinalPoly inv err2 msgPoly) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat inv j) →
      SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Compress) s
        (PolyMem (sp + 30896#64) f ∗ PolyMem (sp + 31408#64) (polyVecNat err2) ∗
          PolyMem (sp + 24720#64) (polyVecNat msgPoly) ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .fp = fpv ∧
          P' = (PolyMem (sp + 30896#64) (polyVecNat (seg5FinalPoly inv err2 msgPoly)) ∗
            PolyMem (sp + 31408#64) (polyVecNat err2) ∗
            PolyMem (sp + 24720#64) (polyVecNat msgPoly) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl _hro hx8 hx9 hx10 hx11 hx12 hx13 hfp hv16 hv17 hv18 hv19 hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hstep := seg5_add_iter hb s sp inv err2 msgPoly (r := 15) (by decide) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx13 hv16 hv17 hv18 hv19
      (hhi 30 (by decide) (by decide)) (hhi 31 (by decide) (by decide))
    simp only [show ¬ (15 < 15) by decide, ↓reduceIte] at hstep
    refine SepWP.mono hstep ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, _, hfp', _, _, _, _, hP'⟩
    refine ⟨hsp', hspA', hfp'.trans hfp, ?_⟩
    rw [hP', polyMem_congr (update2_split (r := 15) hlo hhi).1]
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hfp hv16 hv17 hv18 hv19 hlo hhi
    have hr_lt : r < 15 := by omega
    have hstep := seg5_add_iter hb s sp inv err2 msgPoly (r := r) (by omega) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx13 hv16 hv17 hv18 hv19
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr_lt, ↓reduceIte] at hstep
    refine sepWP_seq_env hcl hro hstep ?_
    rintro sm _ hpc' hrun' hcl' hro'
      ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hfp', hv16', hv17', hv18', hv19', rfl⟩
    have ⟨hlo', hhi'⟩ := update2_split (r := r) hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc' hrun' hsp' hspA' hcl' hro'
      hx8' hx9' hx10' hx11' hx12' hx13' (hfp'.trans hfp) hv16' hv17' hv18' hv19' hlo' hhi'

/-- Segment 5 upper `InvNTT` + `e₂` + `msgPoly` (`+0x840c → +0x9d34`): computes
    `seg5FinalPoly (neonInvNttMontgomery16 dot) err2 msgPoly` at `[sp + 30896, sp + 31408)`. -/
theorem seg5_add_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) {dot : Poly16} (hdot : dot.size = 256)
    (err2 msgPoly : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5InvUpper) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let inv := neonInvNttMontgomery16 dot
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Compress) s
      (memRegion (sp + 2320#64) 112 ∗ PolyMem (sp + 24720#64) (polyVecNat msgPoly) ∗
        PolyMem (sp + 26768#64) (polyVecNat (lowerInvNtt16 dot)) ∗ memRegion (sp + 30896#64) 512 ∗
        PolyMem (sp + 31408#64) (polyVecNat err2) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ memRegion (sp + 2320#64) 112 ∗ memRegion (sp + 24720#64) 512 ∗
          memRegion (sp + 26768#64) 512 ∗
          PolyMem (sp + 30896#64) (polyVecNat (seg5FinalPoly inv err2 msgPoly)) ∗
          memRegion (sp + 31408#64) 512 ∗ Rest)) := by
  intro inv
  refine SepWP.of_memRegion_vecRangeMem 7 (sp + 2320#64) (by decide) (by sep_focus) fun f7 => ?_
  set R1 := PolyMem (sp + 24720#64) (polyVecNat msgPoly) ∗ memRegion (sp + 30896#64) 512 ∗
    PolyMem (sp + 31408#64) (polyVecNat err2) ∗ Rest
  have hpre1 : VecRangeMem 7 (sp + 2320#64) f7 ∗
      (PolyMem (sp + 24720#64) (polyVecNat msgPoly) ∗
        PolyMem (sp + 26768#64) (polyVecNat (lowerInvNtt16 dot)) ∗
        memRegion (sp + 30896#64) 512 ∗ PolyMem (sp + 31408#64) (polyVecNat err2) ∗ Rest) ⊢
      VecRangeMem 7 (sp + 2320#64) f7 ∗
        PolyMem (sp + 26768#64) (polyVecNat (lowerInvNtt16 dot)) ∗ R1 := by dsimp only [R1]; sep_frame
  refine SepWP.weaken_pre hpre1 (sepWP_seq_env hcl hro
    (seg5_inv_upper_ok s sp hdot f7 R1 hpc hrun hsp hspA) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx0_2, hx1_2, hx2_2, hx19_2, hfp_2, sp40, hs0, hs5, hP2⟩
  set R2 := SpillSliceMem 7 (sp + 2320#64) sp40 ∗ PolyMem (sp + 24720#64) (polyVecNat msgPoly) ∗
    PolyMem (sp + 31408#64) (polyVecNat err2) ∗ Rest
  have hpre2 : P2 ⊢ memRegion (sp + 30896#64) 512 ∗ PolyMem (sp + 26768#64) (polyVecNat inv) ∗ R2 :=
    Entails.trans hP2 (by dsimp only [R1, R2, inv]; sep_frame)
  refine SepWP.weaken_pre hpre2 (sepWP_seq_env hcl2 hro2
    (seg5_add_memcpy hb hbase s2 sp inv R2 hpc2 hrun2 hsp2 hspA2 hx0_2 hx1_2 hx2_2 hx19_2 hcl2) ?_)
  rintro s3 _ hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hx19_3, hfp_3, rfl⟩
  set R3 := PolyMem (sp + 30896#64) (polyVecNat inv) ∗ PolyMem (sp + 26768#64) (polyVecNat inv) ∗
    PolyMem (sp + 24720#64) (polyVecNat msgPoly) ∗ PolyMem (sp + 31408#64) (polyVecNat err2) ∗ Rest
  have hpre3 : PolyMem (sp + 30896#64) (polyVecNat inv) ∗ PolyMem (sp + 26768#64) (polyVecNat inv) ∗ R2 ⊢
      SpillSliceMem 7 (sp + 2320#64) sp40 ∗ R3 := by dsimp only [R2, R3]; sep_frame
  refine SepWP.weaken_pre hpre3 (sepWP_seq_env hcl3 hro3
    (seg5_add_setup hb s3 sp sp40 R3 hpc3 hrun3 hsp3 hspA3 hx19_3 hs0 hs5) ?_)
  rintro s4 _ hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspA4, hx8_4, hx9_4, hx10_4, hx11_4, hx12_4, hx13_4, hfp_4, hv16_4, hv17_4, hv18_4, hv19_4, rfl⟩
  set R4 := SpillSliceMem 7 (sp + 2320#64) sp40 ∗ PolyMem (sp + 26768#64) (polyVecNat inv) ∗ Rest
  have hpre4 : SpillSliceMem 7 (sp + 2320#64) sp40 ∗ R3 ⊢
      PolyMem (sp + 30896#64) (polyVecNat inv) ∗ PolyMem (sp + 31408#64) (polyVecNat err2) ∗
        PolyMem (sp + 24720#64) (polyVecNat msgPoly) ∗ R4 := by dsimp only [R3, R4]; sep_frame
  refine SepWP.weaken_pre hpre4 (SepWP.mono
    (seg5_add_loop hb sp (s.readReg64 .fp) inv err2 msgPoly R4 15 0 rfl
      s4 (polyVecNat inv) hpc4 hrun4 hsp4 hspA4 hcl4 hro4
      (by simpa using hx8_4) (by simpa using hx9_4) (by simpa using hx10_4) (by simpa using hx11_4)
      hx12_4 hx13_4 (hfp_4.trans (hfp_3.trans hfp_2))
      hv16_4 hv17_4 hv18_4 hv19_4 (fun _ hj => by omega) (fun _ _ _ => rfl)) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, rfl⟩
  refine ⟨hsp_f, hspA_f, hfp_f, ?_⟩
  dsimp only [R4, PolyMem, SpillSliceMem]
  have hm7 := vecRangeMem_entails_memRegion 7 (sp + 2320#64) sp40.get
  have hm24 := vecRangeMem_entails_memRegion 32 (sp + 24720#64) (polyVecNat msgPoly)
  have hm26 := vecRangeMem_entails_memRegion 32 (sp + 26768#64) (polyVecNat inv)
  have hm31 := vecRangeMem_entails_memRegion 32 (sp + 31408#64) (polyVecNat err2)
  exact entails_sub hm7 (by sep_frame)
    (entails_sub hm24 (by sep_frame) (entails_sub hm26 (by sep_frame) (entails_sub hm31 (by sep_frame) (by sep_frame))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Add

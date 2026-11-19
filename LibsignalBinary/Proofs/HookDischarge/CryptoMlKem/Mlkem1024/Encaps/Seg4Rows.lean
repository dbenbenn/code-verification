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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Rhat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Add -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Sym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Dot
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4InvLow
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4InvSym

/-!
# `kyber::encapsulate` (`B07`) — `Seg4` 4-Row `u = InvNTT(Âᵀ ∘ r̂) + e₁` (`+0x59d0 .. +0x760c`)

Composes `Seg4Add.seg4_init`, `Seg4Dot.seg4_dot_ok`, `Seg4InvLow.seg4_inv_low_ok`,
`Seg4InvSym` (`sepWP_of_runSymRange07`), `Seg4Add.seg4_add_ok`, and `Seg4Add.seg4_outer_tail`
across `row = 0, 1, 2, 3` to compute `uVec[0..3]` at `[sp + 28848, sp + 30896)`, preserving
`x19 = sp + 10752#64` and `fp`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Rows

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 Shake128SeedTerminates mlkemQ neonBarrettReduce16 neonInvNttMontgomery16
  neonMontgomeryMul16 neonPolyNttMul16 parseRej12Candidates polyAdd polyInvNtt polyNtt
  sampleMatrixWith sampleNtt samplePolyCbd2 sampleVecCbd2 shake128FirstBlocks shake256List
  vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs (shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonBarrettReducePoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt (
  PolyCanonical neonPolyInvNttFromMontInv16 neonPolyInvNttFromMontInv16_spec
  vecDotNtt_canonical zeroPoly_canonical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents neonVecDotNtt4_spec polyAdd16 polyAdd16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  neonCbd2Poly16 neonCbd2Poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepWP.of_memRegion_vecRangeMem Vec32 VecRangeMem
  poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat
  vecRangeMem_congr vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16 lowerInvNtt16_size neonDot3_size neonPolyNttMul16_size polyAdd16_size
  upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure (upperInvNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (seg5FinalPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr Spill40 SpillSliceMem SymEnv SymGprs SymSpill40 SymVRegs evalSExpr evalSymGpr
  spill40_ofFn_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SrcOptMem SymSpatial SymStateMatches polyPtr symSpill40_eval_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  poly_eq_upperInvNtt16 symUpperInvNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul (neonDot4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (blkPC07 blkPl07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2 (
  aTransPoly aTransPoly16 sampleMatrixWith_false_getD)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Sym (
  Src12832OptMem SymSpatial07 sepWP_of_runSymRange07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Cbd (
  ATransAt ATransRowAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Rhat (
  rHatPoly16 rHatPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Dot (
  Seg4DotPreserved offDotEnd offDotStart ro00Sym seg4_dot_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4InvLow (
  Seg4InvLowPreserved offInvLowEnd offInvLowStart seg4_inv_low_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4InvSym (
  cfgSeg4Inv noReloc_seg4_inv run_seg4_inv seg4_inv_ast_eq seg4_inv_noSpillVreg
  symSeg4InvEnd symSeg4InvEnd_gprs symSeg4InvEnd_vregs symSeg4InvInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Add (
  Seg4AddPreserved offAddStart offAddTail offSeg4Pre offSeg4RowsEnd seg4AddPoly
  seg4_add_ok seg4_init seg4_outer_tail)

/-! ## 1. Pure `uVecPoly16` Soundness Against `Spec.kyber1024Encaps` -/

/-- `Poly16` result of row `row` in `B07` Segment 4 (`InvNTT(Âᵀ[row] ∘ r̂) + e₁[row]`). -/
noncomputable def uVecPoly16 (rho coins : List (BitVec 8)) (row : Nat) : Poly16 :=
  let dot := neonDot4
    (aTransPoly16 rho row 0) (aTransPoly16 rho row 1)
    (aTransPoly16 rho row 2) (aTransPoly16 rho row 3)
    (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [3#8])))
  let e1 := neonCbd2Poly16 (shake256List 128 (coins ++ [BitVec.ofNat 8 (4 + row)]))
  seg4AddPoly (neonInvNttMontgomery16 dot) e1

private theorem parseRej12Candidates_lt_q (bs : List (BitVec 8)) :
    ∀ x ∈ parseRej12Candidates bs, x < mlkemQ := by
  unfold parseRej12Candidates
  intro x hx
  rcases List.mem_flatten.mp hx with ⟨l, hl, hxl⟩
  rcases List.mem_map.mp hl with ⟨t, _, rfl⟩
  simp only [List.mem_append] at hxl
  rcases hxl with h1 | h2
  · split at h1 <;> simp_all
  · split at h2 <;> simp_all

private theorem sampleNtt_canonical (seed34 : List (BitVec 8)) :
    PolyCanonical (sampleNtt seed34) := by
  unfold sampleNtt
  by_cases h : Shake128SeedTerminates seed34
  · simp only [h, ↓reduceDIte]
    have hge := Classical.choose_spec h
    set cands := parseRej12Candidates (shake128FirstBlocks seed34 (Classical.choose h + 3))
    have hsz : (cands.take 256).toArray.size = 256 := by simp [List.length_take, hge]
    refine ⟨hsz, fun i hi => ?_⟩
    have hmem : (cands.take 256).toArray[i]'(by omega) ∈ cands :=
      List.mem_of_mem_take (Array.getElem_mem_toList _)
    simpa [Array.getD, hsz, hi] using parseRej12Candidates_lt_q _ _ hmem
  · simp only [h, ↓reduceDIte]
    exact zeroPoly_canonical

theorem aTransPoly16_spec (rho : List (BitVec 8)) (row col : Nat) :
    PolyBounded16 4095 (aTransPoly16 rho row col) ∧
    PolyRepresents (aTransPoly16 rho row col) (aTransPoly rho row col) := by
  unfold aTransPoly16 aTransPoly
  obtain ⟨hsz, hlt⟩ := sampleNtt_canonical _
  set f := sampleNtt _
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

private theorem seg4AddPoly_eq_barrett_aux {inv : Poly16} (hinv : inv.size = 256) (e1 : Poly16) :
    seg4AddPoly inv e1 =
      (polyAdd16 (inv.map (fun c => neonMontgomeryMul16 c 1441#16)) e1).map neonBarrettReduce16 := by
  unfold seg4AddPoly seg5FinalPoly polyAdd16
  apply Array.ext
  · simp only [Array.size_ofFn, Array.size_map]
  · intro i hi1 _
    have hi : i < 256 := by simpa only [Array.size_ofFn] using hi1
    have hi' : i < inv.size := hinv ▸ hi
    have hrep : (Array.replicate 256 0#16).getD i 0#16 = 0#16 := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ↓reduceIte,
        Option.getD_some]
    have hmap : ∀ (f : BitVec 16 → BitVec 16), (inv.map f).getD i 0#16 = f (inv.getD i 0#16) :=
      fun f => by
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem, hi',
          Option.map_some, Option.getD_some]
    simp only [Array.getElem_ofFn, Array.getElem_map, hrep, hmap, BitVec.add_zero]

private theorem seg4AddPoly_eq_barrett {dot : Poly16} (hdot : dot.size = 256) (e1 : Poly16) :
    seg4AddPoly (neonInvNttMontgomery16 dot) e1 =
      (polyAdd16 (neonPolyInvNttFromMontInv16 dot) e1).map neonBarrettReduce16 := by
  have hinv : (neonInvNttMontgomery16 dot).size = 256 := by
    rw [← upperInvNtt16_lowerInvNtt16 dot, upperInvNtt16_size]
    exact lowerInvNtt16_size hdot
  exact seg4AddPoly_eq_barrett_aux hinv e1

private theorem polyBounded16_mono {b1 b2 : Int} {p : Poly16}
    (hle : b1 ≤ b2) (h : PolyBounded16 b1 p) : PolyBounded16 b2 p :=
  ⟨h.1, fun i hi => ⟨by have := (h.2 i hi).1; omega, by have := (h.2 i hi).2; omega⟩⟩

section PureUVec
attribute [local irreducible] shake256List sampleNtt polyNtt polyInvNtt samplePolyCbd2

set_option maxRecDepth 4000 in
theorem uVecPoly16_spec {rho coins : List (BitVec 8)}
    (hrho : rho.length = 32) (hcoins : coins.length = 32) {row : Nat} (hrow : row < 4) :
    let aTrans := sampleMatrixWith sampleNtt 4 rho false
    let rHat := (sampleVecCbd2 4 coins 0).map polyNtt
    let e1Vec := sampleVecCbd2 4 coins 4
    let uPoly := polyAdd (polyInvNtt (vecDotNtt 4 (aTrans.getD row #[]) rHat))
      (e1Vec.getD row zeroPoly)
    PolyBounded16 1664 (uVecPoly16 rho coins row) ∧
    PolyRepresents (uVecPoly16 rho coins row) uPoly := by
  dsimp only; unfold uVecPoly16
  have hd_sz : (neonDot4
      (aTransPoly16 rho row 0) (aTransPoly16 rho row 1)
      (aTransPoly16 rho row 2) (aTransPoly16 rho row 3)
      (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [3#8])))).size = 256 := polyAdd16_size _ _
  dsimp only [neonDot4, LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure.neonDot3] at hd_sz ⊢
  have htc : coins.take 32 = coins := List.take_of_length_le (Nat.le_of_eq hcoins)
  have hsh (d : BitVec 8) : (shake256List 128 (coins ++ [d])).length = 128 :=
    shake256List_length _ _
  obtain ⟨ha0_b, ha0_r⟩ := aTransPoly16_spec rho row 0
  obtain ⟨ha1_b, ha1_r⟩ := aTransPoly16_spec rho row 1
  obtain ⟨ha2_b, ha2_r⟩ := aTransPoly16_spec rho row 2
  obtain ⟨ha3_b, ha3_r⟩ := aTransPoly16_spec rho row 3
  rw [← sampleMatrixWith_false_getD hrho hrow (by decide : 0 < 4)] at ha0_r
  rw [← sampleMatrixWith_false_getD hrho hrow (by decide : 1 < 4)] at ha1_r
  rw [← sampleMatrixWith_false_getD hrho hrow (by decide : 2 < 4)] at ha2_r
  rw [← sampleMatrixWith_false_getD hrho hrow (by decide : 3 < 4)] at ha3_r
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
  have hr0_eq : BitVec.ofNat 8 0 = 0#8 := rfl
  have hr1_eq : BitVec.ofNat 8 1 = 1#8 := rfl
  have hr2_eq : BitVec.ofNat 8 2 = 2#8 := rfl
  have hr3_eq : BitVec.ofNat 8 3 = 3#8 := rfl
  rw [← hr0_eq, ← hrg 0 (by decide)] at hr0_r
  rw [← hr1_eq, ← hrg 1 (by decide)] at hr1_r
  rw [← hr2_eq, ← hrg 2 (by decide)] at hr2_r
  rw [← hr3_eq, ← hrg 3 (by decide)] at hr3_r
  obtain ⟨hdot_b, hdot_r⟩ := neonVecDotNtt4_spec ha0_b ha1_b ha2_b ha3_b
    (polyBounded16_mono (by decide) hr0_b) (polyBounded16_mono (by decide) hr1_b)
    (polyBounded16_mono (by decide) hr2_b) (polyBounded16_mono (by decide) hr3_b)
    ha0_r ha1_r ha2_r ha3_r hr0_r hr1_r hr2_r hr3_r
  obtain ⟨_, hinv_b, hinv_r⟩ := neonPolyInvNttFromMontInv16_spec
    (polyBounded16_mono (by decide) hdot_b) hdot_r (vecDotNtt_canonical 4 _ _)
  obtain ⟨he1_b, he1_r⟩ := neonCbd2Poly16_spec (hsh (BitVec.ofNat 8 (4 + row)))
  have he1g : (sampleVecCbd2 4 coins 4).getD row zeroPoly =
      samplePolyCbd2 (shake256List 128 (coins ++ [BitVec.ofNat 8 (4 + row)])) := by
    unfold sampleVecCbd2
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [htc, hrow, ↓reduceDIte, Option.getD_some]
  rw [← he1g] at he1_r
  obtain ⟨_, hadd_r⟩ := polyAdd16_spec hinv_b he1_b (by decide) hinv_r he1_r
  rw [seg4AddPoly_eq_barrett hd_sz]
  exact neonBarrettReducePoly16_spec hadd_r

end PureUVec

/-! ## 2. Symbolic Upper `InvNTT` Step (`+0x5ea4 → +0x756c`) -/

private def mkInvEnv (s : State) (t : Spill40) (p2 : Poly16) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := t
  poly0   := Vec32.ofFn (polyVecNat p2)
  src0    := Vec32.zero
  gpr0    := fun r => s.readReg64 (.gpr r)
  pstate0 := s.pstate

private theorem matches_invInit {sp : BitVec 64} {s : State} (t : Spill40) (p2 : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hx25 : s.readReg64 .x25 = 64778#64) (hx26 : s.readReg64 .x26 = 31498#64) :
    SymStateMatches sp (mkInvEnv s t p2) symSeg4InvInit s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 16 => simpa [symSeg4InvInit, SymVRegs.get, evalSExpr] using hv16
    | 17 => simpa [symSeg4InvInit, SymVRegs.get, evalSExpr] using hv17
    | 23 => simpa [symSeg4InvInit, SymVRegs.get, evalSExpr] using hv23
    | 27 => simpa [symSeg4InvInit, SymVRegs.get, evalSExpr] using hv27
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 18 | 19 | 20 | 21 | 22 | 24 | 25 | 26 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 25 => exact hx25
    | 26 => exact hx26
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 27 | 28 | 29 | 30 =>
      simp [symSeg4InvInit, SymGprs.get, evalSymGpr, mkInvEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem spillSlice27_invInit (sp : BitVec 64) (t : Spill40)
    (env : SymEnv) (hsp0 : env.spill0 = t) :
    SpillSliceMem 27 (sp + 2000#64) (symSeg4InvInit.spill.eval env) =
      SpillSliceMem 27 (sp + 2000#64) t :=
  vecRangeMem_congr fun i hi => by
    rw [symSpill40_eval_get env symSeg4InvInit.spill i (by omega)]
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13
    | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 =>
      simp [symSeg4InvInit, SymSpill40.ofFn, SymSpill40.get, evalSExpr, hsp0]
    | _ + 27 => omega

private theorem poly_invInit (ptr : BitVec 64) (p2 : Poly16)
    (env : SymEnv) (hp0 : env.poly0 = Vec32.ofFn (polyVecNat p2)) :
    Poly32Mem ptr (symSeg4InvInit.poly.eval env) = PolyMem ptr (polyVecNat p2) := by
  rw [← poly32Mem_ofFn ptr (polyVecNat p2), ← hp0]
  exact vecRangeMem_congr fun i hi => by
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega

private theorem seg4_inv_upper_ok [MlKemPlacement] {b : BitVec 64}
    (s : State) (sp polyPtrVal : BitVec 64) {dot : Poly16} (hdot : dot.size = 256)
    (t : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + offInvLowEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = 64778#64) (hx26 : s.readReg64 .x26 = 31498#64)
    (hlr : s.readReg64 .lr = polyPtrVal)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offAddStart) s
      (SpillSliceMem 27 (sp + 2000#64) t ∗
        PolyMem polyPtrVal (polyVecNat (lowerInvNtt16 dot)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x3 = 0#64 ∧
        sf.readReg64 .x9 = s.readReg64 .x20 + s.readReg64 .x12 ∧
        sf.readVReg128 16#5 = dup8x16 3329#16 ∧
        sf.readVReg128 17#5 = dup8x16 20159#16 ∧
        sf.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧
        sf.readVReg128 27#5 = dup8x16 1024#16 ∧
        Seg4AddPreserved s sf ∧
        ∃ t' : Spill40, Pf ⊢ SpillSliceMem 27 (sp + 2000#64) t' ∗
          PolyMem polyPtrVal (polyVecNat (neonInvNttMontgomery16 dot)) ∗ Rest) := by
  set p2 := lowerInvNtt16 dot
  set env := mkInvEnv s t p2
  have hp2 : p2.size = 256 := lowerInvNtt16_size hdot
  have hP_sym : SpillSliceMem 27 (sp + 2000#64) t ∗ PolyMem polyPtrVal (polyVecNat p2) ∗ Rest ⊢
      SymSpatial07 false cfgSeg4Inv sp env symSeg4InvInit Rest := by
    dsimp only [SymSpatial07, SymSpatial, cfgSeg4Inv, polyPtr, SrcOptMem, Src12832OptMem]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [spillSlice27_invInit sp t env rfl, show env.gpr0 30#5 = polyPtrVal from hlr,
      poly_invInit polyPtrVal p2 env rfl]
    sep_frame
  refine SepWP.weaken_pre hP_sym (sepWP_of_runSymRange07 (src12832 := false) (cfg := cfgSeg4Inv)
    (env := env) (F := Rest) 1458 6057 noReloc_seg4_inv (by decide) (by decide) (by decide)
    run_seg4_inv (matches_invInit t p2 hsp hspA hv16 hv17 hv23 hv27 hx25 hx26) hpc hrun ?_)
  intro sf _ _ hm
  rcases symSeg4InvEnd_gprs with ⟨g1, g2, g3, g4, g8, g9, g10, g11, g12, g13, g15, g16, g17,
    g18, g19, g20, g25, g26, g27, g28, g29, _⟩
  rcases symSeg4InvEnd_vregs with ⟨vr0, vr16, vr17, vr23, vr27⟩
  have geq (r : Nat) (hr : BitVec.ofNat 5 r ≠ 31#5) (hlt : r < 32) :
      sf.readReg64 (.gpr (BitVec.ofNat 5 r)) = evalSymGpr sp env.gpr0 (symSeg4InvEnd.gprs.get r) :=
    by simpa [Nat.mod_eq_of_lt hlt] using hm.hgprs (BitVec.ofNat 5 r) hr
  have veq (r : Nat) (hlt : r < 32) :
      sf.readVReg128 (BitVec.ofNat 5 r) = evalSExpr env (symSeg4InvEnd.vregs.get r) :=
    by simpa [Nat.mod_eq_of_lt hlt] using hm.hvregs (BitVec.ofNat 5 r)
  have hPf : SymSpatial07 false cfgSeg4Inv sp env symSeg4InvEnd Rest ⊢
      SpillSliceMem 27 (sp + 2000#64) (symSeg4InvEnd.spill.eval env) ∗
        PolyMem polyPtrVal (polyVecNat (neonInvNttMontgomery16 dot)) ∗ Rest := by
    dsimp only [SymSpatial07, SymSpatial, cfgSeg4Inv, polyPtr, SrcOptMem, Src12832OptMem]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show env.gpr0 30#5 = polyPtrVal from hlr,
      poly_eq_upperInvNtt16 polyPtrVal hp2 env rfl symSeg4InvEnd.poly
        seg4_inv_noSpillVreg seg4_inv_ast_eq,
      upperInvNtt16_lowerInvNtt16 dot]
    sep_frame
  exact ⟨hm.hsp, hm.hsp_al,
    by have h := geq 3 (by decide) (by decide); rw [g3] at h; exact h,
    by have h := geq 9 (by decide) (by decide); rw [g9] at h; exact h,
    by have h := veq 16 (by decide); rw [vr16] at h; exact h,
    by have h := veq 17 (by decide); rw [vr17] at h; exact h,
    by have h := veq 23 (by decide); rw [vr23] at h; exact h,
    by have h := veq 27 (by decide); rw [vr27] at h; exact h,
    ⟨by have h := geq 1 (by decide) (by decide); rw [g1] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 2 (by decide) (by decide); rw [g2] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 4 (by decide) (by decide); rw [g4] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 8 (by decide) (by decide); rw [g8] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 10 (by decide) (by decide); rw [g10] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 11 (by decide) (by decide); rw [g11] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 12 (by decide) (by decide); rw [g12] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 13 (by decide) (by decide); rw [g13] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 15 (by decide) (by decide); rw [g15] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 16 (by decide) (by decide); rw [g16] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 17 (by decide) (by decide); rw [g17] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 18 (by decide) (by decide); rw [g18] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 19 (by decide) (by decide); rw [g19] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 20 (by decide) (by decide); rw [g20] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 25 (by decide) (by decide); rw [g25] at h; exact h.trans hx25.symm,
     by have h := geq 26 (by decide) (by decide); rw [g26] at h; exact h.trans hx26.symm,
     by have h := geq 27 (by decide) (by decide); rw [g27] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 28 (by decide) (by decide); rw [g28] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 29 (by decide) (by decide); rw [g29] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := veq 0 (by decide); rw [vr0] at h; exact h,
     by have h := veq 23 (by decide); rw [vr23] at h; exact h.trans hv23.symm,
     by have h := veq 27 (by decide); rw [vr27] at h; exact h.trans hv27.symm⟩,
    symSeg4InvEnd.spill.eval env, hPf⟩

/-! ## 3. Single-Row Composition (`seg4_row_ok`) & Full `Seg4Rows` (`seg4_rows_ok`) -/

private structure Seg4LoopRegs [MlKemPlacement] (sp fpVal : BitVec 64) (row : Nat) (s : State) : Prop where
  x1  : s.readReg64 .x1  = 20159#64
  x2  : s.readReg64 .x2  = mlkemMpl.ρ ro00Sym + 134#64
  x4  : s.readReg64 .x4  = sp + BitVec.ofNat 64 (2560 + 2048 * row)
  x8  : s.readReg64 .x8  = BitVec.ofNat 64 (2048 * row)
  x10 : s.readReg64 .x10 = sp + 28848#64 + BitVec.ofNat 64 (512 * row) + 16#64
  x11 : s.readReg64 .x11 = sp + 26768#64 + BitVec.ofNat 64 (512 * row)
  x12 : s.readReg64 .x12 = 16#64 + BitVec.ofNat 64 (512 * row)
  x13 : s.readReg64 .x13 = BitVec.ofNat 64 row
  x15 : s.readReg64 .x15 = sp + 24720#64
  x16 : s.readReg64 .x16 = 62209#64
  x17 : s.readReg64 .x17 = 3329#64
  x18 : s.readReg64 .x18 = sp + 12832#64
  x19 : s.readReg64 .x19 = sp + 10752#64
  x20 : s.readReg64 .x20 = sp + 28848#64
  x25 : s.readReg64 .x25 = 64778#64
  x26 : s.readReg64 .x26 = 31498#64
  x27 : s.readReg64 .x27 = 1441#64
  x28 : s.readReg64 .x28 = 55457#64
  fp  : s.readReg64 .fp  = fpVal
  v0  : s.readVReg128 0#5  = 0#128
  v23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16
  v27 : s.readVReg128 27#5 = dup8x16 1024#16

private theorem aTransRowAt_eq (sp : BitVec 64) (rho : List (BitVec 8)) (row : Nat) :
    let lhsBase := sp + BitVec.ofNat 64 (2560 + 2048 * row)
    ATransRowAt (sp + 2560#64) rho row =
      (PolyMem lhsBase (polyVecNat (aTransPoly16 rho row 0)) ∗
       PolyMem (lhsBase + 512#64) (polyVecNat (aTransPoly16 rho row 1)) ∗
       PolyMem (lhsBase + 1024#64) (polyVecNat (aTransPoly16 rho row 2)) ∗
       PolyMem (lhsBase + 1536#64) (polyVecNat (aTransPoly16 rho row 3))) := by
  dsimp only [ATransRowAt]
  have h0 : sp + 2560#64 + BitVec.ofNat 64 (2048 * row) =
      sp + BitVec.ofNat 64 (2560 + 2048 * row) := by clear * -; bv_omega
  have h1 : sp + 2560#64 + BitVec.ofNat 64 (2048 * row + 512) =
      sp + BitVec.ofNat 64 (2560 + 2048 * row) + 512#64 := by clear * -; bv_omega
  have h2 : sp + 2560#64 + BitVec.ofNat 64 (2048 * row + 1024) =
      sp + BitVec.ofNat 64 (2560 + 2048 * row) + 1024#64 := by clear * -; bv_omega
  have h3 : sp + 2560#64 + BitVec.ofNat 64 (2048 * row + 1536) =
      sp + BitVec.ofNat 64 (2560 + 2048 * row) + 1536#64 := by clear * -; bv_omega
  rw [h0, h1, h2, h3]

private theorem seg4_row_dot_inv_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl07 b)
    (s : State) (sp fpVal : BitVec 64) (rho coins : List (BitVec 8)) {row : Nat} (hrow : row < 4)
    (t : Spill40) (v12832 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offDotStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hregs : Seg4LoopRegs sp fpVal row s) :
    let uPtr := sp + 28848#64 + BitVec.ofNat 64 (512 * row)
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
    let dot := neonDot4
      (aTransPoly16 rho row 0) (aTransPoly16 rho row 1)
      (aTransPoly16 rho row 2) (aTransPoly16 rho row 3) r0 r1 r2 r3
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offAddStart) s
      (PolyMem uPtr (fun _ => 0#128) ∗ ATransRowAt (sp + 2560#64) rho row ∗
        PolyMem (sp + 24720#64) (polyVecNat r0) ∗
        PolyMem (sp + 25232#64) (polyVecNat r1) ∗
        PolyMem (sp + 25744#64) (polyVecNat r2) ∗
        PolyMem (sp + 26256#64) (polyVecNat r3) ∗
        SpillSliceMem 27 (sp + 2000#64) t ∗
        Poly32Mem (sp + 12832#64) v12832 ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        mlkemMultiLib.CodeLoaded mlkemMpl s3.mem ∧ MlKemRoOk mlkemMpl s3.mem ∧
        s3.readReg64 .x1 = 20159#64 ∧ s3.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s3.readReg64 .x3 = 0#64 ∧ s3.readReg64 .x4 = sp + BitVec.ofNat 64 (2560 + 2048 * row) ∧
        s3.readReg64 .x8 = BitVec.ofNat 64 (2048 * (row + 1)) ∧
        s3.readReg64 .x9 = uPtr + 16#64 ∧
        s3.readReg64 .x10 = uPtr + 16#64 ∧
        s3.readReg64 .x11 = sp + 26768#64 + BitVec.ofNat 64 (512 * row) ∧
        s3.readReg64 .x12 = 16#64 + BitVec.ofNat 64 (512 * row) ∧
        s3.readReg64 .x13 = BitVec.ofNat 64 (row + 1) ∧
        s3.readReg64 .x15 = sp + 24720#64 ∧ s3.readReg64 .x16 = 62209#64 ∧
        s3.readReg64 .x17 = 3329#64 ∧ s3.readReg64 .x18 = sp + 12832#64 ∧
        s3.readReg64 .x19 = sp + 10752#64 ∧ s3.readReg64 .x20 = sp + 28848#64 ∧
        s3.readReg64 .x25 = 64778#64 ∧ s3.readReg64 .x26 = 31498#64 ∧
        s3.readReg64 .x27 = 1441#64 ∧ s3.readReg64 .x28 = 55457#64 ∧
        s3.readReg64 .fp = fpVal ∧ s3.readVReg128 0#5 = 0#128 ∧
        s3.readVReg128 16#5 = dup8x16 3329#16 ∧ s3.readVReg128 17#5 = dup8x16 20159#16 ∧
        s3.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧ s3.readVReg128 27#5 = dup8x16 1024#16 ∧
        ∃ (t' : Spill40) (v12832' : Vec32),
          P3 ⊢ PolyMem uPtr (polyVecNat (neonInvNttMontgomery16 dot)) ∗
            ATransRowAt (sp + 2560#64) rho row ∗
            PolyMem (sp + 24720#64) (polyVecNat r0) ∗
            PolyMem (sp + 25232#64) (polyVecNat r1) ∗
            PolyMem (sp + 25744#64) (polyVecNat r2) ∗
            PolyMem (sp + 26256#64) (polyVecNat r3) ∗
            SpillSliceMem 27 (sp + 2000#64) t' ∗
            Poly32Mem (sp + 12832#64) v12832' ∗ Rest) := by
  intro uPtr r0 r1 r2 r3 dot
  set lhsBase := sp + BitVec.ofNat 64 (2560 + 2048 * row)
  have hr1 : sp + 24720#64 + 512#64 = sp + 25232#64 := by clear * -; bv_omega
  have hr2 : sp + 24720#64 + 1024#64 = sp + 25744#64 := by clear * -; bv_omega
  have hr3 : sp + 24720#64 + 1536#64 = sp + 26256#64 := by clear * -; bv_omega
  have hP0 : PolyMem uPtr (fun _ => 0#128) ∗ ATransRowAt (sp + 2560#64) rho row ∗
      PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
      PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
      SpillSliceMem 27 (sp + 2000#64) t ∗ Poly32Mem (sp + 12832#64) v12832 ∗ Rest ⊢
      PolyMem uPtr (fun _ => 0#128) ∗
      PolyMem lhsBase (polyVecNat (aTransPoly16 rho row 0)) ∗
      PolyMem (lhsBase + 512#64) (polyVecNat (aTransPoly16 rho row 1)) ∗
      PolyMem (lhsBase + 1024#64) (polyVecNat (aTransPoly16 rho row 2)) ∗
      PolyMem (lhsBase + 1536#64) (polyVecNat (aTransPoly16 rho row 3)) ∗
      PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 24720#64 + 512#64) (polyVecNat r1) ∗
      PolyMem (sp + 24720#64 + 1024#64) (polyVecNat r2) ∗
      PolyMem (sp + 24720#64 + 1536#64) (polyVecNat r3) ∗
      Poly32Mem (sp + 12832#64) v12832 ∗ (SpillSliceMem 27 (sp + 2000#64) t ∗ Rest) := by
    rw [aTransRowAt_eq sp rho row, hr1, hr2, hr3]; sep_frame
  refine SepWP.weaken_pre hP0 (sepWP_seq_env hcl hro
    (seg4_dot_ok hb s s sp (sp + 28848#64) lhsBase (sp + 24720#64) hrow
      (aTransPoly16 rho row 0) (aTransPoly16 rho row 1)
      (aTransPoly16 rho row 2) (aTransPoly16 rho row 3) r0 r1 r2 r3 v12832 _
      hpc hrun hsp hspA hcl hro hregs.x2 hregs.x4 hregs.x8 hregs.x13 hregs.x15 hregs.x16 hregs.x17
      hregs.x18 hregs.x20 hregs.v0
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
       rfl, rfl, rfl⟩) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx2_1, hx8_1, hx13_1, hx15_1, hx16_1, hx17_1, hx18_1, hlr_1,
      hv0_1, hv16_1, hv18_1, hd1, rfl⟩
  have hdot : dot.size = 256 := polyAdd16_size _ _
  have hbase12 : (sp + 28848#64) + (16#64 + BitVec.ofNat 64 (512 * row)) = uPtr + 16#64 := by
    dsimp only [uPtr]; clear * -; bv_omega
  refine sepWP_seq_env hcl1 hro1
    (seg4_inv_low_ok hb s1 sp uPtr (sp + 28848#64) (16#64 + BitVec.ofNat 64 (512 * row))
      hbase12 hdot _ hpc1 hrun1 hsp1 hspA1 hcl1 hro1
      (hd1.x1.trans hregs.x1) (hd1.x10.trans hregs.x10) (hd1.x12.trans hregs.x12)
      (hd1.x20.trans hregs.x20) hv16_1 hv18_1 (hd1.v23.trans hregs.v23)
      (hd1.v27.trans hregs.v27)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hv16_2, hv17_2, _, hv23_2, hv27_2, hl2, rfl⟩
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl2 hro2
      (seg4_inv_upper_ok s2 sp uPtr hdot t _ hpc2 hrun2 hsp2 hspA2
        (hl2.x25.trans (hd1.x25.trans hregs.x25)) (hl2.x26.trans (hd1.x26.trans hregs.x26))
        (hl2.lr.trans hlr_1) hv16_2 hv17_2 hv23_2 hv27_2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx3_3, hx9_3, hv16_3, hv17_3, hv23_3, hv27_3, hu3, t', hP3⟩
  have hx9_u : s3.readReg64 .x9 = uPtr + 16#64 := by
    rw [hx9_3, hl2.x20.trans (hd1.x20.trans hregs.x20), hl2.x12.trans (hd1.x12.trans hregs.x12)]
    exact hbase12
  refine SepWP.done hpc3 hrun3
    ⟨hsp3, hspA3, hcl3, hro3,
      hu3.x1.trans (hl2.x1.trans (hd1.x1.trans hregs.x1)),
      hu3.x2.trans (hl2.x2.trans hx2_1),
      hx3_3,
      hu3.x4.trans (hl2.x4.trans (hd1.x4.trans hregs.x4)),
      hu3.x8.trans (hl2.x8.trans hx8_1),
      hx9_u,
      hu3.x10.trans (hl2.x10.trans (hd1.x10.trans hregs.x10)),
      hu3.x11.trans (hl2.x11.trans (hd1.x11.trans hregs.x11)),
      hu3.x12.trans (hl2.x12.trans (hd1.x12.trans hregs.x12)),
      hu3.x13.trans (hl2.x13.trans hx13_1),
      hu3.x15.trans (hl2.x15.trans hx15_1),
      hu3.x16.trans (hl2.x16.trans hx16_1),
      hu3.x17.trans (hl2.x17.trans hx17_1),
      hu3.x18.trans (hl2.x18.trans hx18_1),
      hu3.x19.trans (hl2.x19.trans (hd1.x19.trans hregs.x19)),
      hu3.x20.trans (hl2.x20.trans (hd1.x20.trans hregs.x20)),
      hu3.x25.trans (hl2.x25.trans (hd1.x25.trans hregs.x25)),
      hu3.x26.trans (hl2.x26.trans (hd1.x26.trans hregs.x26)),
      hu3.x27.trans (hl2.x27.trans (hd1.x27.trans hregs.x27)),
      hu3.x28.trans (hl2.x28.trans (hd1.x28.trans hregs.x28)),
      hu3.fp.trans (hl2.fp.trans (hd1.fp.trans hregs.fp)),
      hu3.v0.trans (hl2.v0.trans hv0_1),
      hv16_3, hv17_3, hv23_3, hv27_3,
      t', Vec32.ofFn (polyVecNat (neonPolyNttMul16 (aTransPoly16 rho row 3) r3)), ?_⟩
  refine Entails.trans hP3 ?_
  rw [aTransRowAt_eq sp rho row, hr1, hr2, hr3]
  sep_frame

private theorem seg4_row_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl07 b)
    (s : State) (sp fpVal : BitVec 64) (rho coins : List (BitVec 8)) {row : Nat} (hrow : row < 4)
    (t : Spill40) (v12832 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offDotStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hregs : Seg4LoopRegs sp fpVal row s) :
    let uPtr := sp + 28848#64 + BitVec.ofNat 64 (512 * row)
    let e1Ptr := sp + 26768#64 + BitVec.ofNat 64 (512 * row)
    let e1 := neonCbd2Poly16 (shake256List 128 (coins ++ [BitVec.ofNat 8 (4 + row)]))
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
    SepWP (blkPC07.rebase b (fun _ => none))
      (if row < 3 then b + offDotStart else b + offSeg4RowsEnd) s
      (PolyMem uPtr (fun _ => 0#128) ∗ ATransRowAt (sp + 2560#64) rho row ∗
        PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
        PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
        PolyMem e1Ptr (polyVecNat e1) ∗
        SpillSliceMem 27 (sp + 2000#64) t ∗ Poly32Mem (sp + 12832#64) v12832 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg4LoopRegs sp fpVal (row + 1) sf ∧
        ∃ (t' : Spill40) (v12832' : Vec32),
          Pf ⊢ PolyMem uPtr (polyVecNat (uVecPoly16 rho coins row)) ∗
            ATransRowAt (sp + 2560#64) rho row ∗
            PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
            PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
            PolyMem e1Ptr (polyVecNat e1) ∗
            SpillSliceMem 27 (sp + 2000#64) t' ∗ Poly32Mem (sp + 12832#64) v12832' ∗ Rest) := by
  intro uPtr e1Ptr e1 r0 r1 r2 r3
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl hro
      (seg4_row_dot_inv_ok hb s sp fpVal rho coins hrow t v12832 _
        hpc hrun hsp hspA hcl hro hregs) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, _, _, rx1, rx2, rx3, rx4, rx8, rx9, rx10, rx11, rx12, rx13,
      rx15, rx16, rx17, rx18, rx19, rx20, rx25, rx26, rx27, rx28, rfp, rv0,
      rv16, rv17, rv23, rv27, t', v12832', hP3⟩
  set dot := neonDot4
    (aTransPoly16 rho row 0) (aTransPoly16 rho row 1)
    (aTransPoly16 rho row 2) (aTransPoly16 rho row 3) r0 r1 r2 r3
  refine SepWP.weaken_pre (Entails.trans hP3 (by sep_frame))
    (sepWP_seq_env hcl3 hro3
      (seg4_add_ok hb s3 s3 sp uPtr e1Ptr (neonInvNttMontgomery16 dot) e1 _
        hpc3 hrun3 hsp3 hspA3 hcl3 hro3 rx9 rx11 rx27 rx28 rx3 rv16 rv17 rv23 rv27
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, rfl, rfl⟩) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, ha4, rfl⟩
  have hx8_4 : s4.readReg64 .x8 = BitVec.ofNat 64 (2048 * (row + 1)) := ha4.x8.trans rx8
  refine sepWP_seq_env hcl4 hro4 (seg4_outer_tail hb s4 hrow _ hpc4 hrun4 hx8_4) ?_
  rintro sf Pf hpc_f hrun_f hcl_f hro_f
    ⟨hsp_f, hspA_f, hv_f, hx4_f, hx10_f, hx11_f, hx12_f, hg_f, rfl⟩
  have fv (r : BitVec 5) : sf.readVReg128 r = s4.readVReg128 r := by
    simp [State.readVReg128, hv_f]
  refine SepWP.done hpc_f hrun_f
    ⟨hsp_f.trans hsp4, hspA_f.trans hspA4, hcl_f, hro_f, ?_, t', v12832', ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hg_f 1#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x1.trans rx1)
    · exact (hg_f 2#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x2.trans rx2)
    · rw [hx4_f, ha4.x4.trans rx4]; clear * -; bv_omega
    · exact (hg_f 8#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8_4
    · rw [hx10_f, ha4.x10.trans rx10]; clear * -; bv_omega
    · rw [hx11_f, ha4.x11.trans rx11]; clear * -; bv_omega
    · rw [hx12_f, ha4.x12.trans rx12]; clear * -; bv_omega
    · exact (hg_f 13#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x13.trans rx13)
    · exact (hg_f 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x15.trans rx15)
    · exact (hg_f 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x16.trans rx16)
    · exact (hg_f 17#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x17.trans rx17)
    · exact (hg_f 18#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x18.trans rx18)
    · exact (hg_f 19#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x19.trans rx19)
    · exact (hg_f 20#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x20.trans rx20)
    · exact (hg_f 25#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x25.trans rx25)
    · exact (hg_f 26#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x26.trans rx26)
    · exact (hg_f 27#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x27.trans rx27)
    · exact (hg_f 28#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.x28.trans rx28)
    · exact (hg_f 29#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ha4.fp.trans rfp)
    · exact (fv 0#5).trans (ha4.v0.trans rv0)
    · exact (fv 23#5).trans (ha4.v23.trans rv23)
    · exact (fv 27#5).trans (ha4.v27.trans rv27)
  · change PolyMem uPtr (polyVecNat (uVecPoly16 rho coins row)) ∗ _ ⊢ _
    sep_frame

private theorem seg4_rows_01 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl07 b)
    (s0 : State) (sp fpVal : BitVec 64) (rho coins : List (BitVec 8))
    (t0 : Spill40) (v0 : Vec32) (Rest : SepProp)
    (hpc0 : s0.pc = b + offDotStart) (hrun0 : s0.status = .Running)
    (hsp0 : s0.sp = sp) (hspA0 : s0.spAligned = true)
    (hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro0 : MlKemRoOk mlkemMpl s0.mem)
    (hregs0 : Seg4LoopRegs sp fpVal 0 s0) :
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
    let e1_0 := neonCbd2Poly16 (shake256List 128 (coins ++ [4#8]))
    let e1_1 := neonCbd2Poly16 (shake256List 128 (coins ++ [5#8]))
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offDotStart) s0
      (ATransRowAt (sp + 2560#64) rho 0 ∗ ATransRowAt (sp + 2560#64) rho 1 ∗
        PolyMem (sp + 28848#64) (fun _ => 0#128) ∗ PolyMem (sp + 29360#64) (fun _ => 0#128) ∗
        PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
        PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
        PolyMem (sp + 26768#64) (polyVecNat e1_0) ∗ PolyMem (sp + 27280#64) (polyVecNat e1_1) ∗
        SpillSliceMem 27 (sp + 2000#64) t0 ∗ Poly32Mem (sp + 12832#64) v0 ∗ Rest)
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        mlkemMultiLib.CodeLoaded mlkemMpl s2.mem ∧ MlKemRoOk mlkemMpl s2.mem ∧
        Seg4LoopRegs sp fpVal 2 s2 ∧
        ∃ (t2 : Spill40) (v2 : Vec32),
          P2 ⊢ PolyMem (sp + 28848#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
            PolyMem (sp + 29360#64) (polyVecNat (uVecPoly16 rho coins 1)) ∗
            ATransRowAt (sp + 2560#64) rho 0 ∗ ATransRowAt (sp + 2560#64) rho 1 ∗
            PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
            PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
            PolyMem (sp + 26768#64) (polyVecNat e1_0) ∗ PolyMem (sp + 27280#64) (polyVecNat e1_1) ∗
            SpillSliceMem 27 (sp + 2000#64) t2 ∗ Poly32Mem (sp + 12832#64) v2 ∗ Rest) := by
  intro r0 r1 r2 r3 e1_0 e1_1
  have hu1 : sp + 28848#64 + 512#64 = sp + 29360#64 := by clear * -; bv_omega
  have he1 : sp + 26768#64 + 512#64 = sp + 27280#64 := by clear * -; bv_omega
  refine SepWP.weaken_pre (by simp only [Nat.mul_zero, BitVec.add_zero]; sep_frame)
    (sepWP_seq_env hcl0 hro0
      (seg4_row_ok hb s0 sp fpVal rho coins (by decide : 0 < 4) t0 v0 _
        hpc0 hrun0 hsp0 hspA0 hcl0 hro0 hregs0) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, _, _, hregs1, t1, v1, hP1⟩
  refine SepWP.weaken_pre
    (Entails.trans hP1 (by simp only [Nat.mul_zero, Nat.mul_one, BitVec.add_zero, hu1, he1]; sep_frame))
    (SepWP.mono
      (seg4_row_ok hb s1 sp fpVal rho coins (by decide : 1 < 4) t1 v1 _
        (by simpa using hpc1) hrun1 hsp1 hspA1 hcl1 hro1 hregs1) ?_)
  rintro s2 P2 _ _ ⟨hsp2, hspA2, hcl2, hro2, hregs2, t2, v2, hP2⟩
  refine ⟨hsp2, hspA2, hcl2, hro2, hregs2, t2, v2, Entails.trans hP2 ?_⟩
  simp only [Nat.mul_one, hu1, he1]; sep_frame

private theorem seg4_rows_23 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl07 b)
    (s2 : State) (sp fpVal : BitVec 64) (rho coins : List (BitVec 8))
    (t2 : Spill40) (v2 : Vec32) (Rest : SepProp)
    (hpc2 : s2.pc = b + offDotStart) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = sp) (hspA2 : s2.spAligned = true)
    (hcl2 : mlkemMultiLib.CodeLoaded mlkemMpl s2.mem) (hro2 : MlKemRoOk mlkemMpl s2.mem)
    (hregs2 : Seg4LoopRegs sp fpVal 2 s2) :
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
    let e1_2 := neonCbd2Poly16 (shake256List 128 (coins ++ [6#8]))
    let e1_3 := neonCbd2Poly16 (shake256List 128 (coins ++ [7#8]))
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4RowsEnd) s2
      (ATransRowAt (sp + 2560#64) rho 2 ∗ ATransRowAt (sp + 2560#64) rho 3 ∗
        PolyMem (sp + 29872#64) (fun _ => 0#128) ∗ PolyMem (sp + 30384#64) (fun _ => 0#128) ∗
        PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
        PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
        PolyMem (sp + 27792#64) (polyVecNat e1_2) ∗ PolyMem (sp + 28304#64) (polyVecNat e1_3) ∗
        SpillSliceMem 27 (sp + 2000#64) t2 ∗ Poly32Mem (sp + 12832#64) v2 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 10752#64 ∧ sf.readReg64 .fp = fpVal ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        ∃ (t4 : Spill40) (v4 : Vec32),
          Pf ⊢ PolyMem (sp + 29872#64) (polyVecNat (uVecPoly16 rho coins 2)) ∗
            PolyMem (sp + 30384#64) (polyVecNat (uVecPoly16 rho coins 3)) ∗
            ATransRowAt (sp + 2560#64) rho 2 ∗ ATransRowAt (sp + 2560#64) rho 3 ∗
            PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
            PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
            PolyMem (sp + 27792#64) (polyVecNat e1_2) ∗ PolyMem (sp + 28304#64) (polyVecNat e1_3) ∗
            SpillSliceMem 27 (sp + 2000#64) t4 ∗ Poly32Mem (sp + 12832#64) v4 ∗ Rest) := by
  intro r0 r1 r2 r3 e1_2 e1_3
  have hu2 : sp + 28848#64 + 1024#64 = sp + 29872#64 := by clear * -; bv_omega
  have hu3 : sp + 28848#64 + 1536#64 = sp + 30384#64 := by clear * -; bv_omega
  have he2 : sp + 26768#64 + 1024#64 = sp + 27792#64 := by clear * -; bv_omega
  have he3 : sp + 26768#64 + 1536#64 = sp + 28304#64 := by clear * -; bv_omega
  refine SepWP.weaken_pre (by simp only [Nat.reduceMul, hu2, he2]; sep_frame)
    (sepWP_seq_env hcl2 hro2
      (seg4_row_ok hb s2 sp fpVal rho coins (by decide : 2 < 4) t2 v2 _
        hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hregs2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, _, _, hregs3, t3, v3, hP3⟩
  refine SepWP.weaken_pre
    (Entails.trans hP3 (by simp only [Nat.reduceMul, hu2, hu3, he2, he3]; sep_frame))
    (SepWP.mono
      (seg4_row_ok hb s3 sp fpVal rho coins (by decide : 3 < 4) t3 v3 _
        (by simpa using hpc3) hrun3 hsp3 hspA3 hcl3 hro3 hregs3) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hcl_f, hro_f, hregs4, t4, v4, hPf⟩
  refine ⟨hsp_f, hspA_f, hregs4.x19, hregs4.fp, hcl_f, hro_f, t4, v4, Entails.trans hPf ?_⟩
  simp only [Nat.reduceMul, hu3, he3]; sep_frame

/-- Full 4-row `uVec[0..3]` computation (`+0x59d0 → +0x760c`): computes `uVec[0..3]` at
`[sp + 28848, sp + 30896)` while preserving `ATransAt (sp + 2560#64) rho`, `rHat[0..3]`, `e1[0..3]`,
`x19 = sp + 10752#64`, `fp`, and stack scratch `[sp + 2000, sp + 2432)` + `[sp + 12832, sp + 13344)`. -/
theorem seg4_rows_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl07 b)
    (s : State) (sp : BitVec 64) (rho coins : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4Pre) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 28848#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
    let e1_0 := neonCbd2Poly16 (shake256List 128 (coins ++ [4#8]))
    let e1_1 := neonCbd2Poly16 (shake256List 128 (coins ++ [5#8]))
    let e1_2 := neonCbd2Poly16 (shake256List 128 (coins ++ [6#8]))
    let e1_3 := neonCbd2Poly16 (shake256List 128 (coins ++ [7#8]))
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4RowsEnd) s
      (ATransAt (sp + 2560#64) rho ∗
        PolyMem (sp + 28848#64) (fun _ => 0#128) ∗ PolyMem (sp + 29360#64) (fun _ => 0#128) ∗
        PolyMem (sp + 29872#64) (fun _ => 0#128) ∗ PolyMem (sp + 30384#64) (fun _ => 0#128) ∗
        PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
        PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
        PolyMem (sp + 26768#64) (polyVecNat e1_0) ∗ PolyMem (sp + 27280#64) (polyVecNat e1_1) ∗
        PolyMem (sp + 27792#64) (polyVecNat e1_2) ∗ PolyMem (sp + 28304#64) (polyVecNat e1_3) ∗
        memRegion (sp + 2000#64) 432 ∗ memRegion (sp + 12832#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 10752#64 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem (sp + 28848#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
          PolyMem (sp + 29360#64) (polyVecNat (uVecPoly16 rho coins 1)) ∗
          PolyMem (sp + 29872#64) (polyVecNat (uVecPoly16 rho coins 2)) ∗
          PolyMem (sp + 30384#64) (polyVecNat (uVecPoly16 rho coins 3)) ∗
          ATransAt (sp + 2560#64) rho ∗
          PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
          PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
          PolyMem (sp + 26768#64) (polyVecNat e1_0) ∗ PolyMem (sp + 27280#64) (polyVecNat e1_1) ∗
          PolyMem (sp + 27792#64) (polyVecNat e1_2) ∗ PolyMem (sp + 28304#64) (polyVecNat e1_3) ∗
          memRegion (sp + 2000#64) 432 ∗ memRegion (sp + 12832#64) 512 ∗ Rest)) := by
  intro r0 r1 r2 r3 e1_0 e1_1 e1_2 e1_3
  refine SepWP.of_memRegion_vecRangeMem 27 (sp + 2000#64) (by decide) (by sep_focus) fun fSp => ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 12832#64) (by decide) (by sep_focus) fun f12 => ?_
  have hSp : VecRangeMem 27 (sp + 2000#64) fSp = SpillSliceMem 27 (sp + 2000#64) (Spill40.ofFn fSp) :=
    vecRangeMem_congr fun i hi => (spill40_ofFn_get fSp i (by omega)).symm
  have h12 : VecRangeMem 32 (sp + 12832#64) f12 = Poly32Mem (sp + 12832#64) (Vec32.ofFn f12) :=
    (poly32Mem_ofFn (sp + 12832#64) f12).symm
  rw [hSp, h12]
  refine sepWP_seq_env hcl hro (seg4_init hb s sp _ hpc hrun hsp hspA hx20) ?_
  rintro s0 P0 hpc0 hrun0 hcl0 hro0
    ⟨hsp0, hspA0, r1_0, r2_0, r4_0, r8_0, r10_0, r11_0, r12_0, r13_0, r15_0, r16_0, r17_0,
     r18_0, r19_0, r20_0, r25_0, r26_0, r27_0, r28_0, rfp_0, rv0_0, rv23_0, rv27_0, hP0⟩
  subst hP0
  have hregs0 : Seg4LoopRegs sp (s.readReg64 .fp) 0 s0 :=
    ⟨r1_0, r2_0, by simpa using r4_0, r8_0, by rw [r10_0]; clear * -; bv_omega,
     by simpa using r11_0, by simpa using r12_0, r13_0, r15_0, r16_0, r17_0, r18_0, r19_0,
     r20_0, r25_0, r26_0, r27_0, r28_0, rfp_0, rv0_0, rv23_0, rv27_0⟩
  refine SepWP.weaken_pre (by dsimp only [ATransAt]; sep_frame)
    (sepWP_seq_env hcl0 hro0
      (seg4_rows_01 hb s0 sp (s.readReg64 .fp) rho coins (Spill40.ofFn fSp) (Vec32.ofFn f12) _
        hpc0 hrun0 hsp0 hspA0 hcl0 hro0 hregs0) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, _, _, hregs2, t2, v2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame))
    (SepWP.mono
      (seg4_rows_23 hb s2 sp (s.readReg64 .fp) rho coins t2 v2 _
        hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hregs2) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx19_f, hfp_f, hcl_f, hro_f, t4, v4, hPf⟩
  refine ⟨hsp_f, hspA_f, hx19_f, hfp_f, hcl_f, hro_f, Entails.trans hPf ?_⟩
  dsimp only [ATransAt]
  have hsp27 : SpillSliceMem 27 (sp + 2000#64) t4 ⊢ memRegion (sp + 2000#64) 432 := by
    dsimp only [SpillSliceMem]
    simpa using vecRangeMem_entails_memRegion 27 (sp + 2000#64) (fun i => t4.get i)
  have hp12 : Poly32Mem (sp + 12832#64) v4 ⊢ memRegion (sp + 12832#64) 512 :=
    poly32Mem_entails_memRegion (sp + 12832#64) v4
  refine Entails.trans (entails_sub hsp27 (by sep_frame) (by sep_frame)) ?_
  exact entails_sub hp12 (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Rows

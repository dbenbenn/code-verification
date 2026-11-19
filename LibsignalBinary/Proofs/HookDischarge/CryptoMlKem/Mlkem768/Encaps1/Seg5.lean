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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3 -- proof-setup: allow-public-import
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
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Sym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Dot
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5InvLow
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5InvSym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Add

/-!
# `encapsulate1_serialized` (`B03`) — Segment 5 `u = InvNTT(Âᵀ ∘ r̂) + e₁` (`+0x4e38 .. +0x6a78`)

Composes `Seg5Add.seg5_init`, `Seg5Dot.seg5_dot_ok`, `Seg5InvLow.seg5_inv_low_ok`,
`Seg5InvSym` (`sepWP_of_runSymRange03`), `Seg5Add.seg5_add_ok`, and `Seg5Add.seg5_outer_tail`
across `row = 0, 1, 2` to compute `uVec[0..2]` at `[sp + 2192, sp + 3728)`, and proves pure
soundness (`PolyBounded16 1664` + `PolyRepresents`) against `Spec.mlkem768Encaps1With`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 Shake128SeedTerminates mlkemQ neonBarrettReduce16 neonInvNttMontgomery16
  neonMontgomeryMul16 parseRej12Candidates polyAdd polyInvNtt polyNtt sampleMatrixWith
  sampleNtt samplePolyCbd2 sampleVecCbd2 shake128FirstBlocks shake256List vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonBarrettReducePoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt (
  PolyCanonical neonPolyInvNttFromMontInv16 neonPolyInvNttFromMontInv16_spec
  vecDotNtt_canonical zeroPoly_canonical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents neonVecDotNtt3_spec polyAdd16 polyAdd16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  neonCbd2Poly16 neonCbd2Poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem Vec32 poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat
  vecRangeMem_congr vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16 lowerInvNtt16_size neonDot3 neonDot3_size upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (seg5FinalPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr Spill40 SpillSliceMem SymEnv SymGprs SymSpill40 SymVRegs evalSExpr evalSymGpr
  spill40_ofFn_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SrcOptMem SymSpatial SymStateMatches polyPtr symSpill40_eval_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  poly_eq_upperInvNtt16 symUpperInvNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (blkPC03 blkPl03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2 (
  ATransMem ATransRowMem aTransPoly aTransPoly16 sampleMatrixWith_false_getD)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3 (
  rHatPoly16 rHatPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Sym (
  Src4272OptMem SymSpatial03 sepWP_of_runSymRange03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Dot (
  Seg5DotPreserved offDotEnd offDotStart ro00Sym seg5_dot_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5InvLow (
  Seg5InvLowPreserved offInvLowEnd offInvLowStart seg5_inv_low_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5InvSym (
  cfgSeg5Inv noReloc_seg5_inv run_seg5_inv seg5_inv_ast_eq seg5_inv_noSpillVreg
  symSeg5InvEnd symSeg5InvEnd_gprs symSeg5InvEnd_vregs symSeg5InvInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Add (
  Seg5AddPreserved offAddStart offAddTail seg5AddPoly
  seg5_add_ok seg5_init seg5_outer_tail)

@[simp, arm64_norm, wp_norm] abbrev offSeg5Pre : BitVec 64 := BitVec.ofNat 64 20024
@[simp, arm64_norm, wp_norm] abbrev offSeg5End : BitVec 64 := BitVec.ofNat 64 27256

/-! ## 1. Pure `uVecPoly16` Soundness Against `Spec.mlkem768Encaps1With` -/

/-- `Poly16` result of row `row` in `B03` Segment 5 (`InvNTT(Âᵀ[row] ∘ r̂) + e₁[row]`). -/
noncomputable def uVecPoly16 (rho coins : List (BitVec 8)) (row : Nat) : Poly16 :=
  let dot := neonDot3
    (aTransPoly16 rho row 0) (aTransPoly16 rho row 1) (aTransPoly16 rho row 2)
    (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
  let e1 := neonCbd2Poly16 (shake256List 128 (coins ++ [BitVec.ofNat 8 (3 + row)]))
  seg5AddPoly (neonInvNttMontgomery16 dot) e1

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

private theorem aTransPoly16_spec (rho : List (BitVec 8)) (row col : Nat) :
    PolyBounded16 4095 (aTransPoly16 rho row col) ∧
    PolyRepresents (aTransPoly16 rho row col) (aTransPoly rho row col) := by
  unfold aTransPoly16 aTransPoly
  obtain ⟨hsz, hlt⟩ := sampleNtt_canonical (rho ++ [BitVec.ofNat 8 row, BitVec.ofNat 8 col])
  set f := sampleNtt (rho ++ [BitVec.ofNat 8 row, BitVec.ofNat 8 col])
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

private theorem seg5AddPoly_eq_barrett_aux {inv : Poly16} (hinv : inv.size = 256) (e1 : Poly16) :
    seg5AddPoly inv e1 =
      (polyAdd16 (inv.map (fun c => neonMontgomeryMul16 c 1441#16)) e1).map neonBarrettReduce16 := by
  unfold seg5AddPoly seg5FinalPoly polyAdd16
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

private theorem seg5AddPoly_eq_barrett {dot : Poly16} (hdot : dot.size = 256) (e1 : Poly16) :
    seg5AddPoly (neonInvNttMontgomery16 dot) e1 =
      (polyAdd16 (neonPolyInvNttFromMontInv16 dot) e1).map neonBarrettReduce16 := by
  have hinv : (neonInvNttMontgomery16 dot).size = 256 := by
    rw [← upperInvNtt16_lowerInvNtt16 dot,
      LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure.upperInvNtt16_size]
    exact lowerInvNtt16_size hdot
  exact seg5AddPoly_eq_barrett_aux hinv e1

private theorem polyBounded16_mono {b1 b2 : Int} {p : Poly16}
    (hle : b1 ≤ b2) (h : PolyBounded16 b1 p) : PolyBounded16 b2 p :=
  ⟨h.1, fun i hi => ⟨by have := (h.2 i hi).1; omega, by have := (h.2 i hi).2; omega⟩⟩

section PureUVec
attribute [local irreducible] shake256List sampleNtt polyNtt polyInvNtt samplePolyCbd2

set_option maxRecDepth 4000 in
theorem uVecPoly16_spec {rho coins : List (BitVec 8)}
    (hrho : rho.length = 32) (hcoins : coins.length = 32) {row : Nat} (hrow : row < 3) :
    let aTrans := sampleMatrixWith sampleNtt 3 rho false
    let rHat := (sampleVecCbd2 3 coins 0).map polyNtt
    let e1Vec := sampleVecCbd2 3 coins 3
    let uPoly := polyAdd (polyInvNtt (vecDotNtt 3 (aTrans.getD row #[]) rHat))
      (e1Vec.getD row zeroPoly)
    PolyBounded16 1664 (uVecPoly16 rho coins row) ∧
    PolyRepresents (uVecPoly16 rho coins row) uPoly := by
  dsimp only
  unfold uVecPoly16
  have hd_sz : (neonDot3
      (aTransPoly16 rho row 0) (aTransPoly16 rho row 1) (aTransPoly16 rho row 2)
      (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [2#8])))).size = 256 :=
    neonDot3_size _ _ _ _ _ _
  dsimp only [neonDot3] at hd_sz ⊢
  have htc : coins.take 32 = coins := List.take_of_length_le (Nat.le_of_eq hcoins)
  have hsh (d : BitVec 8) : (shake256List 128 (coins ++ [d])).length = 128 :=
    LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd.shake256List_length _ _
  obtain ⟨ha0_b, ha0_r⟩ := aTransPoly16_spec rho row 0
  obtain ⟨ha1_b, ha1_r⟩ := aTransPoly16_spec rho row 1
  obtain ⟨ha2_b, ha2_r⟩ := aTransPoly16_spec rho row 2
  rw [← sampleMatrixWith_false_getD hrho hrow (by decide : 0 < 3)] at ha0_r
  rw [← sampleMatrixWith_false_getD hrho hrow (by decide : 1 < 3)] at ha1_r
  rw [← sampleMatrixWith_false_getD hrho hrow (by decide : 2 < 3)] at ha2_r
  obtain ⟨_, hr0_b, hr0_r⟩ := rHatPoly16_spec (hsh 0#8)
  obtain ⟨_, hr1_b, hr1_r⟩ := rHatPoly16_spec (hsh 1#8)
  obtain ⟨_, hr2_b, hr2_r⟩ := rHatPoly16_spec (hsh 2#8)
  have hrg (j : Nat) (hj : j < 3) :
      ((sampleVecCbd2 3 coins 0).map polyNtt).getD j zeroPoly =
        polyNtt (samplePolyCbd2 (shake256List 128 (coins ++ [BitVec.ofNat 8 j]))) := by
    unfold sampleVecCbd2
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_ofFn]
    simp only [htc, hj, Nat.zero_add, ↓reduceDIte, Option.map_some, Option.getD_some]
  have hr0_eq : BitVec.ofNat 8 0 = 0#8 := rfl
  have hr1_eq : BitVec.ofNat 8 1 = 1#8 := rfl
  have hr2_eq : BitVec.ofNat 8 2 = 2#8 := rfl
  rw [← hr0_eq, ← hrg 0 (by decide)] at hr0_r
  rw [← hr1_eq, ← hrg 1 (by decide)] at hr1_r
  rw [← hr2_eq, ← hrg 2 (by decide)] at hr2_r
  obtain ⟨hdot_b, hdot_r⟩ := neonVecDotNtt3_spec ha0_b ha1_b ha2_b
    (polyBounded16_mono (by decide) hr0_b)
    (polyBounded16_mono (by decide) hr1_b)
    (polyBounded16_mono (by decide) hr2_b)
    ha0_r ha1_r ha2_r hr0_r hr1_r hr2_r
  obtain ⟨_, hinv_b, hinv_r⟩ := neonPolyInvNttFromMontInv16_spec
    (polyBounded16_mono (by decide) hdot_b) hdot_r (vecDotNtt_canonical 3 _ _)
  obtain ⟨he1_b, he1_r⟩ := neonCbd2Poly16_spec (hsh (BitVec.ofNat 8 (3 + row)))
  have he1g : (sampleVecCbd2 3 coins 3).getD row zeroPoly =
      samplePolyCbd2 (shake256List 128 (coins ++ [BitVec.ofNat 8 (3 + row)])) := by
    unfold sampleVecCbd2
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [htc, hrow, ↓reduceDIte, Option.getD_some]
  rw [← he1g] at he1_r
  obtain ⟨_, hadd_r⟩ := polyAdd16_spec hinv_b he1_b (by decide) hinv_r he1_r
  rw [seg5AddPoly_eq_barrett hd_sz]
  exact neonBarrettReducePoly16_spec hadd_r

end PureUVec


/-! ## 2. Symbolic Upper `InvNTT` Step (`+0x5310 → +0x69d8`) -/

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
    (hx21 : s.readReg64 .x21 = 64778#64) (hx22 : s.readReg64 .x22 = 31498#64) :
    SymStateMatches sp (mkInvEnv s t p2) symSeg5InvInit s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 16 => simpa [symSeg5InvInit, SymVRegs.get, evalSExpr] using hv16
    | 17 => simpa [symSeg5InvInit, SymVRegs.get, evalSExpr] using hv17
    | 23 => simpa [symSeg5InvInit, SymVRegs.get, evalSExpr] using hv23
    | 27 => simpa [symSeg5InvInit, SymVRegs.get, evalSExpr] using hv27
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 18 | 19 | 20 | 21 | 22 | 24 | 25 | 26 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 21 => exact hx21
    | 22 => exact hx22
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symSeg5InvInit, SymGprs.get, evalSymGpr, mkInvEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem spillSlice27_invInit (sp : BitVec 64) (t : Spill40)
    (env : SymEnv) (hsp0 : env.spill0 = t) :
    SpillSliceMem 27 (sp + 1760#64) (symSeg5InvInit.spill.eval env) =
      SpillSliceMem 27 (sp + 1760#64) t :=
  vecRangeMem_congr fun i hi => by
    rw [symSpill40_eval_get env symSeg5InvInit.spill i (by omega)]
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13
    | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 =>
      simp [symSeg5InvInit, SymSpill40.ofFn, SymSpill40.get, evalSExpr, hsp0]
    | _ + 27 => omega

private theorem poly_invInit (ptr : BitVec 64) (p2 : Poly16)
    (env : SymEnv) (hp0 : env.poly0 = Vec32.ofFn (polyVecNat p2)) :
    Poly32Mem ptr (symSeg5InvInit.poly.eval env) = PolyMem ptr (polyVecNat p2) := by
  rw [← poly32Mem_ofFn ptr (polyVecNat p2), ← hp0]
  exact vecRangeMem_congr fun i hi => by
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega

private theorem seg5_inv_upper_ok [MlKemPlacement] {b : BitVec 64}
    (s : State) (sp polyPtrVal : BitVec 64) {dot : Poly16} (hdot : dot.size = 256)
    (t : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + offInvLowEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = 64778#64) (hx22 : s.readReg64 .x22 = 31498#64)
    (hx26 : s.readReg64 .x26 = polyPtrVal)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offAddStart) s
      (SpillSliceMem 27 (sp + 1760#64) t ∗
        PolyMem polyPtrVal (polyVecNat (lowerInvNtt16 dot)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x10 = s.readReg64 .x19 + s.readReg64 .x12 ∧
        sf.readReg64 .x27 = 0#64 ∧
        sf.readVReg128 16#5 = dup8x16 3329#16 ∧
        sf.readVReg128 17#5 = dup8x16 20159#16 ∧
        sf.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧
        sf.readVReg128 27#5 = dup8x16 1024#16 ∧
        Seg5AddPreserved s sf ∧
        ∃ t' : Spill40, Pf ⊢ SpillSliceMem 27 (sp + 1760#64) t' ∗
          PolyMem polyPtrVal (polyVecNat (neonInvNttMontgomery16 dot)) ∗ Rest) := by
  set p2 := lowerInvNtt16 dot
  set env := mkInvEnv s t p2
  have hp2 : p2.size = 256 := lowerInvNtt16_size hdot
  have hP_sym : SpillSliceMem 27 (sp + 1760#64) t ∗ PolyMem polyPtrVal (polyVecNat p2) ∗ Rest ⊢
      SymSpatial03 false cfgSeg5Inv sp env symSeg5InvInit Rest := by
    dsimp only [SymSpatial03, SymSpatial, cfgSeg5Inv, polyPtr, SrcOptMem, Src4272OptMem]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [spillSlice27_invInit sp t env rfl, show env.gpr0 26#5 = polyPtrVal from hx26,
      poly_invInit polyPtrVal p2 env rfl]
    sep_frame
  refine SepWP.weaken_pre hP_sym (sepWP_of_runSymRange03 (src4272 := false) (cfg := cfgSeg5Inv)
    (env := env) (F := Rest) 1458 5316 noReloc_seg5_inv (by decide) (by decide) (by decide)
    run_seg5_inv (matches_invInit t p2 hsp hspA hv16 hv17 hv23 hv27 hx21 hx22) hpc hrun ?_)
  intro sf _ _ hm
  rcases symSeg5InvEnd_gprs with ⟨g1, g4, g8, g9, g10, g11, g12, g13, g14, g16, g17, g18, g19,
    g21, g22, g23, g24, g25, _, g27, g28, _⟩
  rcases symSeg5InvEnd_vregs with ⟨vr0, vr16, vr17, vr23, vr27⟩
  have geq (r : Nat) (hr : BitVec.ofNat 5 r ≠ 31#5) (hlt : r < 32) :
      sf.readReg64 (.gpr (BitVec.ofNat 5 r)) = evalSymGpr sp env.gpr0 (symSeg5InvEnd.gprs.get r) :=
    by simpa [Nat.mod_eq_of_lt hlt] using hm.hgprs (BitVec.ofNat 5 r) hr
  have veq (r : Nat) (hlt : r < 32) :
      sf.readVReg128 (BitVec.ofNat 5 r) = evalSExpr env (symSeg5InvEnd.vregs.get r) :=
    by simpa [Nat.mod_eq_of_lt hlt] using hm.hvregs (BitVec.ofNat 5 r)
  have hPf : SymSpatial03 false cfgSeg5Inv sp env symSeg5InvEnd Rest ⊢
      SpillSliceMem 27 (sp + 1760#64) (symSeg5InvEnd.spill.eval env) ∗
        PolyMem polyPtrVal (polyVecNat (neonInvNttMontgomery16 dot)) ∗ Rest := by
    dsimp only [SymSpatial03, SymSpatial, cfgSeg5Inv, polyPtr, SrcOptMem, Src4272OptMem]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show env.gpr0 26#5 = polyPtrVal from hx26,
      poly_eq_upperInvNtt16 polyPtrVal hp2 env rfl symSeg5InvEnd.poly
        seg5_inv_noSpillVreg seg5_inv_ast_eq,
      upperInvNtt16_lowerInvNtt16 dot]
    sep_frame
  exact ⟨hm.hsp, hm.hsp_al,
    by have h := geq 10 (by decide) (by decide); rw [g10] at h; exact h,
    by have h := geq 27 (by decide) (by decide); rw [g27] at h; exact h,
    by have h := veq 16 (by decide); rw [vr16] at h; exact h,
    by have h := veq 17 (by decide); rw [vr17] at h; exact h,
    by have h := veq 23 (by decide); rw [vr23] at h; exact h,
    by have h := veq 27 (by decide); rw [vr27] at h; exact h,
    ⟨by have h := geq 1 (by decide) (by decide); rw [g1] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 4 (by decide) (by decide); rw [g4] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 8 (by decide) (by decide); rw [g8] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 9 (by decide) (by decide); rw [g9] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 11 (by decide) (by decide); rw [g11] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 12 (by decide) (by decide); rw [g12] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 13 (by decide) (by decide); rw [g13] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 14 (by decide) (by decide); rw [g14] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 16 (by decide) (by decide); rw [g16] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 17 (by decide) (by decide); rw [g17] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 18 (by decide) (by decide); rw [g18] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 19 (by decide) (by decide); rw [g19] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 21 (by decide) (by decide); rw [g21] at h; exact h.trans hx21.symm,
     by have h := geq 22 (by decide) (by decide); rw [g22] at h; exact h.trans hx22.symm,
     by have h := geq 23 (by decide) (by decide); rw [g23] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 24 (by decide) (by decide); rw [g24] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 25 (by decide) (by decide); rw [g25] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := geq 28 (by decide) (by decide); rw [g28] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := veq 0 (by decide); rw [vr0] at h; exact h,
     by have h := veq 23 (by decide); rw [vr23] at h; exact h.trans hv23.symm,
     by have h := veq 27 (by decide); rw [vr27] at h; exact h.trans hv27.symm⟩,
    symSeg5InvEnd.spill.eval env, hPf⟩

/-! ## 3. Single-Row Composition (`seg5_row_ok`) & Full `Seg5` (`seg5_ok`) -/

private structure Seg5LoopRegs [MlKemPlacement] (sp : BitVec 64) (row : Nat) (s : State) : Prop where
  x1  : s.readReg64 .x1  = 20159#64
  x4  : s.readReg64 .x4  = mlkemMpl.ρ ro00Sym + 134#64
  x8  : s.readReg64 .x8  = BitVec.ofNat 64 (1536 * row)
  x9  : s.readReg64 .x9  = sp + 2192#64 + BitVec.ofNat 64 (512 * row) + 16#64
  x11 : s.readReg64 .x11 = sp + 13984#64 + BitVec.ofNat 64 (512 * row)
  x12 : s.readReg64 .x12 = 16#64 + BitVec.ofNat 64 (512 * row)
  x13 : s.readReg64 .x13 = BitVec.ofNat 64 row
  x14 : s.readReg64 .x14 = sp + 12448#64
  x16 : s.readReg64 .x16 = 62209#64
  x17 : s.readReg64 .x17 = 3329#64
  x18 : s.readReg64 .x18 = sp + 4272#64
  x19 : s.readReg64 .x19 = sp + 2192#64
  x21 : s.readReg64 .x21 = 64778#64
  x22 : s.readReg64 .x22 = 31498#64
  x23 : s.readReg64 .x23 = 1441#64
  x24 : s.readReg64 .x24 = 55457#64
  x25 : s.readReg64 .x25 = 4608#64
  x28 : s.readReg64 .x28 = sp + BitVec.ofNat 64 (6832 + 1536 * row)
  v0  : s.readVReg128 0#5  = 0#128
  v23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16
  v27 : s.readVReg128 27#5 = dup8x16 1024#16

private theorem aTransRowMem_eq (sp : BitVec 64) (rho : List (BitVec 8)) (row : Nat) :
    let lhsBase := sp + BitVec.ofNat 64 (6832 + 1536 * row)
    ATransRowMem sp rho row =
      (PolyMem lhsBase (polyVecNat (aTransPoly16 rho row 0)) ∗
       PolyMem (lhsBase + 512#64) (polyVecNat (aTransPoly16 rho row 1)) ∗
       PolyMem (lhsBase + 1024#64) (polyVecNat (aTransPoly16 rho row 2))) := by
  dsimp only [ATransRowMem]
  have h1 : sp + BitVec.ofNat 64 (6832 + 1536 * row + 512) =
      sp + BitVec.ofNat 64 (6832 + 1536 * row) + 512#64 := by clear * -; bv_omega
  have h2 : sp + BitVec.ofNat 64 (6832 + 1536 * row + 1024) =
      sp + BitVec.ofNat 64 (6832 + 1536 * row) + 1024#64 := by clear * -; bv_omega
  rw [h1, h2]

set_option maxHeartbeats 800000 in
private theorem seg5_row_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl03 b)
    (s : State) (sp : BitVec 64) (rho coins : List (BitVec 8)) {row : Nat} (hrow : row < 3)
    (t : Spill40) (v4272 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offDotStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hregs : Seg5LoopRegs sp row s) :
    let uPtr := sp + 2192#64 + BitVec.ofNat 64 (512 * row)
    let e1Ptr := sp + 13984#64 + BitVec.ofNat 64 (512 * row)
    let e1 := neonCbd2Poly16 (shake256List 128 (coins ++ [BitVec.ofNat 8 (3 + row)]))
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    SepWP (blkPC03.rebase b (fun _ => none))
      (if row < 2 then b + offDotStart else b + offSeg5End) s
      (PolyMem uPtr (fun _ => 0#128) ∗ ATransRowMem sp rho row ∗
        PolyMem (sp + 12448#64) (polyVecNat r0) ∗
        PolyMem (sp + 12960#64) (polyVecNat r1) ∗
        PolyMem (sp + 13472#64) (polyVecNat r2) ∗
        PolyMem e1Ptr (polyVecNat e1) ∗
        SpillSliceMem 27 (sp + 1760#64) t ∗
        Poly32Mem (sp + 4272#64) v4272 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg5LoopRegs sp (row + 1) sf ∧
        ∃ (t' : Spill40) (v4272' : Vec32),
          Pf ⊢ PolyMem uPtr (polyVecNat (uVecPoly16 rho coins row)) ∗
            ATransRowMem sp rho row ∗
            PolyMem (sp + 12448#64) (polyVecNat r0) ∗
            PolyMem (sp + 12960#64) (polyVecNat r1) ∗
            PolyMem (sp + 13472#64) (polyVecNat r2) ∗
            PolyMem e1Ptr (polyVecNat e1) ∗
            SpillSliceMem 27 (sp + 1760#64) t' ∗
            Poly32Mem (sp + 4272#64) v4272' ∗ Rest) := by
  intro uPtr e1Ptr e1 r0 r1 r2
  set lhsBase := sp + BitVec.ofNat 64 (6832 + 1536 * row)
  have hr1 : sp + 12448#64 + 512#64 = sp + 12960#64 := by clear * -; bv_omega
  have hr2 : sp + 12448#64 + 1024#64 = sp + 13472#64 := by clear * -; bv_omega
  have hP0 : PolyMem uPtr (fun _ => 0#128) ∗ ATransRowMem sp rho row ∗
      PolyMem (sp + 12448#64) (polyVecNat r0) ∗ PolyMem (sp + 12960#64) (polyVecNat r1) ∗
      PolyMem (sp + 13472#64) (polyVecNat r2) ∗ PolyMem e1Ptr (polyVecNat e1) ∗
      SpillSliceMem 27 (sp + 1760#64) t ∗ Poly32Mem (sp + 4272#64) v4272 ∗ Rest ⊢
      PolyMem uPtr (fun _ => 0#128) ∗
      PolyMem lhsBase (polyVecNat (aTransPoly16 rho row 0)) ∗
      PolyMem (lhsBase + 512#64) (polyVecNat (aTransPoly16 rho row 1)) ∗
      PolyMem (lhsBase + 1024#64) (polyVecNat (aTransPoly16 rho row 2)) ∗
      PolyMem (sp + 12448#64) (polyVecNat r0) ∗
      PolyMem (sp + 12448#64 + 512#64) (polyVecNat r1) ∗
      PolyMem (sp + 12448#64 + 1024#64) (polyVecNat r2) ∗
      Poly32Mem (sp + 4272#64) v4272 ∗
      (PolyMem e1Ptr (polyVecNat e1) ∗ SpillSliceMem 27 (sp + 1760#64) t ∗ Rest) := by
    rw [aTransRowMem_eq sp rho row, hr1, hr2]; sep_frame
  refine SepWP.weaken_pre hP0 (sepWP_seq_env hcl hro
    (seg5_dot_ok hb s s sp (sp + 2192#64) lhsBase (sp + 12448#64) hrow
      (aTransPoly16 rho row 0) (aTransPoly16 rho row 1) (aTransPoly16 rho row 2) r0 r1 r2 v4272 _
      hpc hrun hsp hspA hcl hro hregs.x4 hregs.x8 hregs.x13 hregs.x14 hregs.x16 hregs.x17
      hregs.x18 hregs.x19 hregs.x28 hregs.v0
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
       rfl, rfl, rfl⟩) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx4_1, hx8_1, hx13_1, hx14_1, hx16_1, hx17_1, hx18_1, hx26_1,
      hv0_1, hv16_1, hv18_1, hd1, rfl⟩
  set dot := neonDot3 (aTransPoly16 rho row 0) (aTransPoly16 rho row 1)
    (aTransPoly16 rho row 2) r0 r1 r2
  have hdot : dot.size = 256 := neonDot3_size _ _ _ _ _ _
  have hbase12 : (sp + 2192#64) + (16#64 + BitVec.ofNat 64 (512 * row)) = uPtr + 16#64 := by
    dsimp only [uPtr]; clear * -; bv_omega
  refine sepWP_seq_env hcl1 hro1
    (seg5_inv_low_ok hb s1 sp uPtr (sp + 2192#64) (16#64 + BitVec.ofNat 64 (512 * row))
      hbase12 hdot _ hpc1 hrun1 hsp1 hspA1 hcl1 hro1
      (hd1.x1.trans hregs.x1) (hd1.x9.trans hregs.x9) (hd1.x12.trans hregs.x12)
      (hd1.x19.trans hregs.x19) hv16_1 hv18_1 (hd1.v23.trans hregs.v23)
      (hd1.v27.trans hregs.v27)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hv16_2, hv17_2, _, hv23_2, hv27_2, hl2, rfl⟩
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl2 hro2
      (seg5_inv_upper_ok s2 sp uPtr hdot t _ hpc2 hrun2 hsp2 hspA2
        (hl2.x21.trans (hd1.x21.trans hregs.x21)) (hl2.x22.trans (hd1.x22.trans hregs.x22))
        (hl2.x26.trans hx26_1) hv16_2 hv17_2 hv23_2 hv27_2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx10_3, hx27_3, hv16_3, hv17_3, hv23_3, hv27_3, hu3, t', hP3⟩
  have hx10_u : s3.readReg64 .x10 = uPtr + 16#64 := by
    rw [hx10_3, hl2.x19.trans (hd1.x19.trans hregs.x19), hl2.x12.trans (hd1.x12.trans hregs.x12)]
    exact hbase12
  refine SepWP.weaken_pre (Entails.trans hP3 (by sep_frame))
    (sepWP_seq_env hcl3 hro3
      (seg5_add_ok hb s3 s3 sp uPtr e1Ptr (neonInvNttMontgomery16 dot) e1 _
        hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx10_u
        (hu3.x11.trans (hl2.x11.trans (hd1.x11.trans hregs.x11)))
        (hu3.x23.trans (hl2.x23.trans (hd1.x23.trans hregs.x23)))
        (hu3.x24.trans (hl2.x24.trans (hd1.x24.trans hregs.x24)))
        hx27_3 hv16_3 hv17_3 hv23_3 hv27_3
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, rfl⟩) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, ha4, rfl⟩
  have hx8_4 : s4.readReg64 .x8 = BitVec.ofNat 64 (1536 * (row + 1)) :=
    ha4.x8.trans (hu3.x8.trans (hl2.x8.trans hx8_1))
  have hx25_4 : s4.readReg64 .x25 = 4608#64 :=
    ha4.x25.trans (hu3.x25.trans (hl2.x25.trans (hd1.x25.trans hregs.x25)))
  refine sepWP_seq_env hcl4 hro4 (seg5_outer_tail hb s4 hrow _ hpc4 hrun4 hx8_4 hx25_4) ?_
  rintro sf Pf hpc_f hrun_f hcl_f hro_f ⟨hsp_f, hspA_f, hv_f, hx9_f, hx11_f, hx12_f, hx28_f, hg_f, rfl⟩
  have fv (r : BitVec 5) : sf.readVReg128 r = s4.readVReg128 r := by
    simp [State.readVReg128, hv_f]
  refine SepWP.done hpc_f hrun_f ⟨hsp_f.trans hsp4, hspA_f.trans hspA4, hcl_f, hro_f, ?_, t',
    Vec32.ofFn (polyVecNat
      (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.neonPolyNttMul16
        (aTransPoly16 rho row 2) r2)), ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hg_f 1#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x1.trans (hu3.x1.trans (hl2.x1.trans (hd1.x1.trans hregs.x1))))
    · exact (hg_f 4#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x4.trans (hu3.x4.trans (hl2.x4.trans hx4_1)))
    · exact (hg_f 8#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8_4
    · rw [hx9_f, ha4.x9.trans (hu3.x9.trans (hl2.x9.trans (hd1.x9.trans hregs.x9)))]
      clear * -; bv_omega
    · rw [hx11_f, ha4.x11.trans (hu3.x11.trans (hl2.x11.trans (hd1.x11.trans hregs.x11)))]
      clear * -; bv_omega
    · rw [hx12_f, ha4.x12.trans (hu3.x12.trans (hl2.x12.trans (hd1.x12.trans hregs.x12)))]
      clear * -; bv_omega
    · exact (hg_f 13#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x13.trans (hu3.x13.trans (hl2.x13.trans hx13_1)))
    · exact (hg_f 14#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x14.trans (hu3.x14.trans (hl2.x14.trans hx14_1)))
    · exact (hg_f 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x16.trans (hu3.x16.trans (hl2.x16.trans hx16_1)))
    · exact (hg_f 17#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x17.trans (hu3.x17.trans (hl2.x17.trans hx17_1)))
    · exact (hg_f 18#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x18.trans (hu3.x18.trans (hl2.x18.trans hx18_1)))
    · exact (hg_f 19#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x19.trans (hu3.x19.trans (hl2.x19.trans (hd1.x19.trans hregs.x19))))
    · exact (hg_f 21#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x21.trans (hu3.x21.trans (hl2.x21.trans (hd1.x21.trans hregs.x21))))
    · exact (hg_f 22#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x22.trans (hu3.x22.trans (hl2.x22.trans (hd1.x22.trans hregs.x22))))
    · exact (hg_f 23#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x23.trans (hu3.x23.trans (hl2.x23.trans (hd1.x23.trans hregs.x23))))
    · exact (hg_f 24#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x24.trans (hu3.x24.trans (hl2.x24.trans (hd1.x24.trans hregs.x24))))
    · exact (hg_f 25#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25_4
    · rw [hx28_f, ha4.x28.trans (hu3.x28.trans (hl2.x28.trans (hd1.x28.trans hregs.x28)))]
      clear * -; bv_omega
    · exact (fv 0#5).trans (ha4.v0.trans (hu3.v0.trans (hl2.v0.trans hv0_1)))
    · exact (fv 23#5).trans (ha4.v23.trans hv23_3)
    · exact (fv 27#5).trans (ha4.v27.trans hv27_3)
  · rw [aTransRowMem_eq sp rho row, hr1, hr2]
    change PolyMem uPtr (polyVecNat (uVecPoly16 rho coins row)) ∗ _ ⊢ _
    sep_frame


set_option maxHeartbeats 800000 in
/-- Full `Seg5` (`+0x4e38 → +0x6a78`): computes `uVec[0..2]` at `[sp + 2192, sp + 3728)` while
preserving `ATransMem`, `rHat[0..2]`, `e1[0..2]`, and stack scratch `[sp + 1760, sp + 2192)` +
`[sp + 4272, sp + 4784)`. -/
theorem seg5_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl03 b)
    (s : State) (sp : BitVec 64) (rho coins : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Pre) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = sp + 2192#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let e1_0 := neonCbd2Poly16 (shake256List 128 (coins ++ [3#8]))
    let e1_1 := neonCbd2Poly16 (shake256List 128 (coins ++ [4#8]))
    let e1_2 := neonCbd2Poly16 (shake256List 128 (coins ++ [5#8]))
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg5End) s
      (ATransMem sp rho ∗
        PolyMem (sp + 2192#64) (fun _ => 0#128) ∗
        PolyMem (sp + 2704#64) (fun _ => 0#128) ∗
        PolyMem (sp + 3216#64) (fun _ => 0#128) ∗
        PolyMem (sp + 12448#64) (polyVecNat r0) ∗
        PolyMem (sp + 12960#64) (polyVecNat r1) ∗
        PolyMem (sp + 13472#64) (polyVecNat r2) ∗
        PolyMem (sp + 13984#64) (polyVecNat e1_0) ∗
        PolyMem (sp + 14496#64) (polyVecNat e1_1) ∗
        PolyMem (sp + 15008#64) (polyVecNat e1_2) ∗
        memRegion (sp + 1760#64) 432 ∗
        memRegion (sp + 4272#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem (sp + 2192#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
          PolyMem (sp + 2704#64) (polyVecNat (uVecPoly16 rho coins 1)) ∗
          PolyMem (sp + 3216#64) (polyVecNat (uVecPoly16 rho coins 2)) ∗
          ATransMem sp rho ∗
          PolyMem (sp + 12448#64) (polyVecNat r0) ∗
          PolyMem (sp + 12960#64) (polyVecNat r1) ∗
          PolyMem (sp + 13472#64) (polyVecNat r2) ∗
          PolyMem (sp + 13984#64) (polyVecNat e1_0) ∗
          PolyMem (sp + 14496#64) (polyVecNat e1_1) ∗
          PolyMem (sp + 15008#64) (polyVecNat e1_2) ∗
          memRegion (sp + 1760#64) 432 ∗
          memRegion (sp + 4272#64) 512 ∗ Rest)) := by
  intro r0 r1 r2 e1_0 e1_1 e1_2
  have hu1 : sp + 2192#64 + 512#64 = sp + 2704#64 := by clear * -; bv_omega
  have hu2 : sp + 2192#64 + 1024#64 = sp + 3216#64 := by clear * -; bv_omega
  have he1 : sp + 13984#64 + 512#64 = sp + 14496#64 := by clear * -; bv_omega
  have he2 : sp + 13984#64 + 1024#64 = sp + 15008#64 := by clear * -; bv_omega
  refine LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.SepWP.of_memRegion_vecRangeMem
    27 (sp + 1760#64) (by decide) (by sep_focus) fun fSp => ?_
  refine LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.SepWP.of_memRegion_vecRangeMem
    32 (sp + 4272#64) (by decide) (by sep_focus) fun f42 => ?_
  have hSp : LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.VecRangeMem
      27 (sp + 1760#64) fSp = SpillSliceMem 27 (sp + 1760#64) (Spill40.ofFn fSp) :=
    vecRangeMem_congr fun i hi => (spill40_ofFn_get fSp i (by omega)).symm
  have h42 : LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.VecRangeMem
      32 (sp + 4272#64) f42 = Poly32Mem (sp + 4272#64) (Vec32.ofFn f42) :=
    (poly32Mem_ofFn (sp + 4272#64) f42).symm
  rw [hSp, h42]
  refine sepWP_seq_env hcl hro (seg5_init hb s sp _ hpc hrun hsp hspA hx19) ?_
  rintro s0 P0 hpc0 hrun0 hcl0 hro0
    ⟨hsp0, hspA0, r1_0, r4_0, r8_0, r9_0, r11_0, r12_0, r13_0, r14_0, r16_0, r17_0, r18_0,
     r19_0, r21_0, r22_0, r23_0, r24_0, r25_0, r28_0, rv0_0, rv23_0, rv27_0, hP0⟩
  subst hP0
  have hregs0 : Seg5LoopRegs sp 0 s0 :=
    ⟨r1_0, r4_0, r8_0, by rw [r9_0]; clear * -; bv_omega, by simpa using r11_0,
     by simpa using r12_0, r13_0, r14_0, r16_0, r17_0, r18_0, r19_0, r21_0, r22_0,
     r23_0, r24_0, r25_0, by simpa using r28_0, rv0_0, rv23_0, rv27_0⟩
  refine SepWP.weaken_pre (show _ ⊢
      PolyMem (sp + 2192#64 + BitVec.ofNat 64 (512 * 0)) (fun _ => 0#128) ∗
      ATransRowMem sp rho 0 ∗
      PolyMem (sp + 12448#64) (polyVecNat r0) ∗ PolyMem (sp + 12960#64) (polyVecNat r1) ∗
      PolyMem (sp + 13472#64) (polyVecNat r2) ∗
      PolyMem (sp + 13984#64 + BitVec.ofNat 64 (512 * 0)) (polyVecNat e1_0) ∗
      SpillSliceMem 27 (sp + 1760#64) (Spill40.ofFn fSp) ∗
      Poly32Mem (sp + 4272#64) (Vec32.ofFn f42) ∗
      (ATransRowMem sp rho 1 ∗ ATransRowMem sp rho 2 ∗
        PolyMem (sp + 2704#64) (fun _ => 0#128) ∗ PolyMem (sp + 3216#64) (fun _ => 0#128) ∗
        PolyMem (sp + 14496#64) (polyVecNat e1_1) ∗ PolyMem (sp + 15008#64) (polyVecNat e1_2) ∗ Rest) by
      dsimp only [ATransMem]
      simp only [Nat.mul_zero, BitVec.add_zero]
      sep_frame)
    (sepWP_seq_env hcl0 hro0
      (seg5_row_ok hb s0 sp rho coins (by decide : 0 < 3) (Spill40.ofFn fSp) (Vec32.ofFn f42) _
        hpc0 hrun0 hsp0 hspA0 hcl0 hro0 hregs0) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, _, _, hregs1, t1, v1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (show _ ⊢
      PolyMem (sp + 2192#64 + BitVec.ofNat 64 (512 * 1)) (fun _ => 0#128) ∗
      ATransRowMem sp rho 1 ∗
      PolyMem (sp + 12448#64) (polyVecNat r0) ∗ PolyMem (sp + 12960#64) (polyVecNat r1) ∗
      PolyMem (sp + 13472#64) (polyVecNat r2) ∗
      PolyMem (sp + 13984#64 + BitVec.ofNat 64 (512 * 1)) (polyVecNat e1_1) ∗
      SpillSliceMem 27 (sp + 1760#64) t1 ∗ Poly32Mem (sp + 4272#64) v1 ∗
      (PolyMem (sp + 2192#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
        ATransRowMem sp rho 0 ∗ ATransRowMem sp rho 2 ∗
        PolyMem (sp + 3216#64) (fun _ => 0#128) ∗
        PolyMem (sp + 13984#64) (polyVecNat e1_0) ∗
        PolyMem (sp + 15008#64) (polyVecNat e1_2) ∗ Rest) by
      simp only [Nat.mul_zero, Nat.mul_one, BitVec.add_zero, hu1, he1]
      sep_frame))
    (sepWP_seq_env hcl1 hro1
      (seg5_row_ok hb s1 sp rho coins (by decide : 1 < 3) t1 v1 _
        (by simpa using hpc1) hrun1 hsp1 hspA1 hcl1 hro1 hregs1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, _, _, hregs2, t2, v2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (show _ ⊢
      PolyMem (sp + 2192#64 + BitVec.ofNat 64 (512 * 2)) (fun _ => 0#128) ∗
      ATransRowMem sp rho 2 ∗
      PolyMem (sp + 12448#64) (polyVecNat r0) ∗ PolyMem (sp + 12960#64) (polyVecNat r1) ∗
      PolyMem (sp + 13472#64) (polyVecNat r2) ∗
      PolyMem (sp + 13984#64 + BitVec.ofNat 64 (512 * 2)) (polyVecNat e1_2) ∗
      SpillSliceMem 27 (sp + 1760#64) t2 ∗ Poly32Mem (sp + 4272#64) v2 ∗
      (PolyMem (sp + 2192#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
        PolyMem (sp + 2704#64) (polyVecNat (uVecPoly16 rho coins 1)) ∗
        ATransRowMem sp rho 0 ∗ ATransRowMem sp rho 1 ∗
        PolyMem (sp + 13984#64) (polyVecNat e1_0) ∗
        PolyMem (sp + 14496#64) (polyVecNat e1_1) ∗ Rest) by
      simp only [Nat.mul_one, Nat.reduceMul, hu1, hu2, he1, he2]
      sep_frame))
    (SepWP.mono
      (seg5_row_ok hb s2 sp rho coins (by decide : 2 < 3) t2 v2 _
        (by simpa using hpc2) hrun2 hsp2 hspA2 hcl2 hro2 hregs2) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hcl_f, hro_f, _, t3, v3, hPf⟩
  refine ⟨hsp_f, hspA_f, hcl_f, hro_f, Entails.trans hPf ?_⟩
  simp only [Nat.reduceMul, hu2, he2, ATransMem]
  have hsp27 : SpillSliceMem 27 (sp + 1760#64) t3 ⊢ memRegion (sp + 1760#64) 432 := by
    dsimp only [SpillSliceMem]
    simpa using vecRangeMem_entails_memRegion 27 (sp + 1760#64) (fun i => t3.get i)
  have hp42 : Poly32Mem (sp + 4272#64) v3 ⊢ memRegion (sp + 4272#64) 512 :=
    poly32Mem_entails_memRegion (sp + 4272#64) v3
  refine Entails.trans (entails_sub hsp27 (by sep_frame) (by sep_frame)) ?_
  exact entails_sub hp42 (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5

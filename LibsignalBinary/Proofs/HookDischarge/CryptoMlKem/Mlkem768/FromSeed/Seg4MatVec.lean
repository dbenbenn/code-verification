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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Matrix -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3 -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Epi
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4Dot

/-!
# `generate_keypair_compressed` (`B05`) — Segment 4 Matrix-Vector `tHat = Â ∘ sHat + eHat` (`Seg4MatVec`)

Steps `+0x5c60 → +0x60fc` (`296` instructions): 3-row NTT dot product `Â[i, 0..2] ∘ sHat[0..2]`,
in-place accumulation, `to_standard_domain` (`1353`), `eHat[i]` addition, and Barrett reduction,
storing `THatMem sp (g.take 32) (g.drop 32)` at `[sp + 2208, sp + 3744)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4MatVec
open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 Shake128SeedTerminates mlkemQ neonBarrettReduce16 neonMontgomeryMul16
  neonMontgomeryReduce16 neonPolyNttMul16 parseRej12Candidates polyAdd polyNtt
  sampleMatrixWith sampleNtt samplePolyCbd2 sampleVecCbd2 sha3_512List
  shake128FirstBlocks shake256List sqdmulh16 vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 ext_lane16 lane16 lane16_dup8x16 lane16_pack8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_simdAdd8h lane16_simdMla8h lane16_simdMul8h lane16_simdSqdmulh8h
  lane16_simdSshr8h lane16_simdSub8h simdAdd8h simdMla8h simdMul8h simdSmlal4s
  simdSmull4s simdSqdmulh8h simdSshr8h simdSub8h simdTrn1_4s simdTrn1_8h
  simdTrn2_4s simdTrn2_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  barrett_mla_0xf2ff montgomery_precomp_mul)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonBarrettReducePoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents neonVecDotNtt3_spec polyAdd16 polyAdd16_spec
  polyToStandardDomain_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ldrh16_ro zetaTableAt_zext32_ne_32768)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec32
  poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat step_ldpQ128 step_ldrQ128
  step_stpQ128 step_strQ128 vec32_ofFn_get vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  simdRev64_4s simdUzp1_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_fmov_s_w svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdExt_16b_8 svc_simdIns_h1
  svc_simdIns_h2 svc_simdIns_h3 svc_simdMla_8h svc_simdMovi_8h_1024 svc_simdMul_8h
  svc_simdMvni_8h_f2ff svc_simdRev64_4s svc_simdSmlal_4s svc_simdSmull_4s
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSshr_8h_11 svc_simdSub_8h
  svc_simdTrn1_4s svc_simdTrn1_8h svc_simdTrn2_4s svc_simdTrn2_8h svc_simdUzp1_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  buildZeta4 lane16_buildZeta4 neonDot3 neonDot3_size neonPolyNttMul16_size
  nttMulRawPair nttMulRawPair_eq_polyVecNat polyAdd16_zero_left polyZero16
  simdAdd8h_polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  SavedFrame05 blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (rowSeed)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Matrix (
  AMatrixMem sampleMatrixWith_true_getD)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat (
  SHatMem cbdNttPoly16 cbdNttPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3 (
  EHatMem Seg3Exit off5c60)

open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Epi (RowPolyOut)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure (
  shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow (
  ro00Sym step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4Dot (
  off5cb0 off605c seg4_row_dot seg4_setup)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05 [0x605c → 0x60f8]
end

@[simp, arm64_norm, wp_norm] abbrev off6068 : BitVec 64 := BitVec.ofNat 64 24680
@[simp, arm64_norm, wp_norm] abbrev off60ec : BitVec 64 := BitVec.ofNat 64 24812
@[simp, arm64_norm, wp_norm] abbrev off60fc : BitVec 64 := BitVec.ofNat 64 24828

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem readReg64_orFpsr' (s : State) (fl : BitVec 32) (r : Reg) :
    (s.orFpsr fl).readReg64 r = s.readReg64 r := State.readReg64_orFpsr s fl r
@[simp, arm64_norm, wp_norm]
private theorem readReg32_orFpsr' (s : State) (fl : BitVec 32) (r : Reg) :
    (s.orFpsr fl).readReg32 r = s.readReg32 r := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem readReg_orFpsr' (s : State) (fl : BitVec 32) (w : Width) (r : Reg) :
    (s.orFpsr fl).readReg w r = s.readReg w r := by cases s; cases w <;> rfl
@[simp, arm64_norm, wp_norm]
private theorem readVReg128_orFpsr' (s : State) (fl : BitVec 32) (r : BitVec 5) :
    (s.orFpsr fl).readVReg128 r = s.readVReg128 r := State.readVReg128_orFpsr s fl r
@[simp, arm64_norm, wp_norm]
private theorem status_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).status = s.status := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem pc_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pc = s.pc := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem sp_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).sp = s.sp := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem spAligned_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).spAligned = s.spAligned := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem pstate_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pstate = s.pstate := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem mem_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).mem = s.mem := by cases s; rfl

@[simp, arm64_norm, wp_norm]
private theorem svc_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := rfl

/-- `to_standard_domain` (`1353#16`) + `eHat` addition + Barrett reduction on one polynomial. -/
@[expose] def tHatStdAddPoly (dot e : Poly16) : Poly16 :=
  Array.ofFn (n := 256) fun i =>
    neonBarrettReduce16 (neonMontgomeryMul16 (dot.getD i.1 0#16) 1353#16 + e.getD i.1 0#16)

theorem tHatStdAdd_vec_eq (dot e : Poly16) (idx : Nat) (hidx : idx < 32) :
    let qx := polyVecNat dot idx
    let qe := polyVecNat e idx
    let normal := simdSub8h
      (simdSshr8h (simdSqdmulh8h qx (dup8x16 1353#16)) 1)
      (simdSshr8h (simdSqdmulh8h (simdMul8h qx (dup8x16 20553#16)) (dup8x16 3329#16)) 1)
    let tot := simdAdd8h qe normal
    let quot := simdSshr8h (simdAdd8h (simdSqdmulh8h tot (dup8x16 20159#16)) (dup8x16 1024#16)) 11
    simdMla8h tot quot (dup8x16 0xf2ff#16) = polyVecNat (tHatStdAddPoly dot e) idx := by
  dsimp only
  apply ext_lane16; intro i
  have hi256 : 8 * idx + i.val < 256 := by omega
  have hmont (x : BitVec 16) :
      (sqdmulh16 x 1353#16).sshiftRight 1 -
        (sqdmulh16 (x * 20553#16) 3329#16).sshiftRight 1 =
      neonMontgomeryMul16 x 1353#16 := by
    unfold neonMontgomeryMul16 neonMontgomeryReduce16; dsimp only
    rw [montgomery_precomp_mul x 1353#16]; rfl
  have hget : (tHatStdAddPoly dot e).getD (8 * idx + i.val) 0#16 =
      neonBarrettReduce16
        (neonMontgomeryMul16 (dot.getD (8 * idx + i.val) 0#16) 1353#16 +
          e.getD (8 * idx + i.val) 0#16) := by
    simp [tHatStdAddPoly, Array.getD, hi256]
  simp only [polyVecNat, lane16_pack8x16, lane16_simdMla8h, lane16_simdSshr8h,
    lane16_simdAdd8h, lane16_simdSqdmulh8h, lane16_simdSub8h, lane16_simdMul8h,
    lane16_dup8x16, hmont, hget]
  rw [barrett_mla_0xf2ff, BitVec.add_comm (e.getD (8 * idx + i.val) 0#16) _]; rfl

/-- `Poly16` result of row `col < 3` of `tHat = Â ∘ sHat + eHat`. -/
@[expose] noncomputable def tHatPoly16 (rho sigma : List (BitVec 8)) (col : Nat) : Poly16 :=
  let dot := neonDot3
    ((sampleNtt (rowSeed rho 0 col)).map (BitVec.ofNat 16))
    ((sampleNtt (rowSeed rho 1 col)).map (BitVec.ofNat 16))
    ((sampleNtt (rowSeed rho 2 col)).map (BitVec.ofNat 16))
    (cbdNttPoly16 (shake256List 128 (sigma ++ [0#8])))
    (cbdNttPoly16 (shake256List 128 (sigma ++ [1#8])))
    (cbdNttPoly16 (shake256List 128 (sigma ++ [2#8])))
  tHatStdAddPoly dot (cbdNttPoly16 (shake256List 128 (sigma ++ [BitVec.ofNat 8 (3 + col)])))

/-- `tHat[0..2]` stored at `[sp + 2208, sp + 3744)` (`3 × 512` B). -/
@[expose] noncomputable def THatMem (sp : BitVec 64) (rho sigma : List (BitVec 8)) : SepProp :=
  PolyMem (sp + 2208#64) (polyVecNat (tHatPoly16 rho sigma 0)) ∗
  PolyMem (sp + 2720#64) (polyVecNat (tHatPoly16 rho sigma 1)) ∗
  PolyMem (sp + 3232#64) (polyVecNat (tHatPoly16 rho sigma 2))

private theorem parseRej12Candidates_lt_q (bs : List (BitVec 8)) :
    ∀ x ∈ parseRej12Candidates bs, x < mlkemQ := by
  unfold parseRej12Candidates; intro x hx
  rcases List.mem_flatten.mp hx with ⟨l, hl, hxl⟩
  rcases List.mem_map.mp hl with ⟨_, _, rfl⟩
  rcases List.mem_append.mp hxl with h1 | h2
  · split at h1 <;> simp_all
  · split at h2 <;> simp_all

private theorem sampleNtt_canonical (seed34 : List (BitVec 8)) :
    (sampleNtt seed34).size = 256 ∧ ∀ i < 256, (sampleNtt seed34).getD i 0 < 3329 := by
  unfold sampleNtt
  by_cases h : Shake128SeedTerminates seed34
  · simp only [h, ↓reduceDIte]
    have hge := Classical.choose_spec h
    set cands := parseRej12Candidates (shake128FirstBlocks seed34 (Classical.choose h + 3))
    have hsz : (cands.take 256).toArray.size = 256 := by simp [List.length_take, hge]
    refine ⟨hsz, fun i hi => ?_⟩
    have hmem : (cands.take 256).toArray[i]'(by omega) ∈ cands :=
      List.mem_of_mem_take (Array.getElem_mem_toList _)
    simpa [Array.getD, hsz, hi, mlkemQ] using parseRej12Candidates_lt_q _ _ hmem
  · simp only [h, ↓reduceDIte]
    exact ⟨by simp [zeroPoly], fun i hi => by simp [zeroPoly, Array.getD, hi]⟩

private theorem sampleNtt_poly16_spec (seed34 : List (BitVec 8)) :
    PolyBounded16 4095 ((sampleNtt seed34).map (BitVec.ofNat 16)) ∧
    PolyRepresents ((sampleNtt seed34).map (BitVec.ofNat 16)) (sampleNtt seed34) := by
  obtain ⟨hsz, hlt⟩ := sampleNtt_canonical seed34
  set f := sampleNtt seed34
  have hmsz : (f.map (BitVec.ofNat 16)).size = 256 := by simp [hsz]
  have hint : ∀ i < 256, ((f.map (BitVec.ofNat 16)).getD i 0#16).toInt = (f.getD i 0 : Int) := by
    intro i hi
    have hq : f.getD i 0 < 3329 := hlt i hi
    rw [show (f.map (BitVec.ofNat 16)).getD i 0#16 = BitVec.ofNat 16 (f.getD i 0) by
          simp [Array.getD, hsz, hi], BitVec.toInt_eq_toNat_cond,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  exact ⟨⟨hmsz, fun i hi => by have := hlt i hi; rw [hint i hi]; omega⟩,
    ⟨hmsz, fun i hi => by rw [hint i hi]⟩⟩

private theorem tHatStdAddPoly_eq_barrett {dot : Poly16} (hdot : dot.size = 256) (e : Poly16) :
    tHatStdAddPoly dot e =
      (polyAdd16 (dot.map (fun v => neonMontgomeryMul16 v 1353#16)) e).map neonBarrettReduce16 := by
  unfold tHatStdAddPoly polyAdd16
  apply Array.ext
  · simp only [Array.size_ofFn, Array.size_map]
  · intro i hi1 _
    have hi : i < 256 := by simpa only [Array.size_ofFn] using hi1
    have hi' : i < dot.size := hdot ▸ hi
    have hmap : ∀ (f : BitVec 16 → BitVec 16), (dot.map f).getD i 0#16 = f (dot.getD i 0#16) :=
      fun f => by
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem, hi',
          Option.map_some, Option.getD_some]
    simp only [Array.getElem_ofFn, Array.getElem_map, hmap]

private theorem polyRepresents_congr_right {p : Poly16} {f g : Poly}
    (h : PolyRepresents p f) (heq : g = f) : PolyRepresents p g := heq ▸ h

private theorem polyBounded16_1664_to_4095 {p : Poly16} (h : PolyBounded16 1664 p) :
    PolyBounded16 4095 p :=
  ⟨h.1, fun i hi => ⟨by have := (h.2 i hi).1; omega, by have := (h.2 i hi).2; omega⟩⟩

private theorem tHatDotStdAdd_spec
    {a0 a1 a2 s0 s1 s2 e : Poly16} {aRow sHat : Array Poly} {fe : Poly}
    (ha0_b : PolyBounded16 4095 a0) (ha1_b : PolyBounded16 4095 a1) (ha2_b : PolyBounded16 4095 a2)
    (hs0_b : PolyBounded16 1664 s0) (hs1_b : PolyBounded16 1664 s1) (hs2_b : PolyBounded16 1664 s2)
    (he_b : PolyBounded16 1664 e)
    (ha0_r : PolyRepresents a0 (aRow.getD 0 zeroPoly))
    (ha1_r : PolyRepresents a1 (aRow.getD 1 zeroPoly))
    (ha2_r : PolyRepresents a2 (aRow.getD 2 zeroPoly))
    (hs0_r : PolyRepresents s0 (sHat.getD 0 zeroPoly))
    (hs1_r : PolyRepresents s1 (sHat.getD 1 zeroPoly))
    (hs2_r : PolyRepresents s2 (sHat.getD 2 zeroPoly))
    (he_r : PolyRepresents e fe) :
    PolyBounded16 1664 (tHatStdAddPoly (neonDot3 a0 a1 a2 s0 s1 s2) e) ∧
    PolyRepresents (tHatStdAddPoly (neonDot3 a0 a1 a2 s0 s1 s2) e)
      (polyAdd (vecDotNtt 3 aRow sHat) fe) := by
  obtain ⟨_, hdot_r⟩ := neonVecDotNtt3_spec ha0_b ha1_b ha2_b
    (polyBounded16_1664_to_4095 hs0_b) (polyBounded16_1664_to_4095 hs1_b)
    (polyBounded16_1664_to_4095 hs2_b) ha0_r ha1_r ha2_r hs0_r hs1_r hs2_r
  obtain ⟨hstd_b, hstd_r⟩ := polyToStandardDomain_spec hdot_r
  obtain ⟨_, hadd_r⟩ := polyAdd16_spec hstd_b he_b (by decide) hstd_r he_r
  rw [tHatStdAddPoly_eq_barrett (neonDot3_size a0 a1 a2 s0 s1 s2) e]
  exact neonBarrettReducePoly16_spec hadd_r

private theorem array_ofFn3_map_getD (g : Poly → Poly) (f : Fin 3 → Poly) {j : Nat} (hj : j < 3) :
    ((Array.ofFn f).map g).getD j zeroPoly = g (f ⟨j, hj⟩) := by
  simp [Array.getD, hj]

private theorem sampleVecCbd2_map_getD {sigma : List (BitVec 8)} (hsig : sigma.length = 32)
    (ds j : Nat) (hj : j < 3) :
    ((sampleVecCbd2 3 sigma ds).map polyNtt).getD j zeroPoly =
      polyNtt (samplePolyCbd2 (shake256List 128 (sigma ++ [BitVec.ofNat 8 (ds + j)]))) := by
  have hts : sigma.take 32 = sigma := List.take_of_length_le (Nat.le_of_eq hsig)
  unfold sampleVecCbd2; dsimp only; rw [hts]
  exact array_ofFn3_map_getD polyNtt _ hj

theorem tHatPoly16_spec {rho sigma : List (BitVec 8)}
    (hrho : rho.length = 32) (hsig : sigma.length = 32) {col : Nat} (hcol : col < 3) :
    let aMat := sampleMatrixWith sampleNtt 3 rho true
    let sHat := (sampleVecCbd2 3 sigma 0).map polyNtt
    let eHat := (sampleVecCbd2 3 sigma 3).map polyNtt
    let tPoly := polyAdd (vecDotNtt 3 (aMat.getD col #[]) sHat) (eHat.getD col zeroPoly)
    PolyBounded16 1664 (tHatPoly16 rho sigma col) ∧
    PolyRepresents (tHatPoly16 rho sigma col) tPoly := by
  dsimp only; unfold tHatPoly16
  obtain ⟨ha0_b, ha0_r0⟩ := sampleNtt_poly16_spec (rowSeed rho 0 col)
  obtain ⟨ha1_b, ha1_r0⟩ := sampleNtt_poly16_spec (rowSeed rho 1 col)
  obtain ⟨ha2_b, ha2_r0⟩ := sampleNtt_poly16_spec (rowSeed rho 2 col)
  obtain ⟨_, hs0_b, hs0_r0⟩ := cbdNttPoly16_spec (shake256List_length 128 (sigma ++ [0#8]))
  obtain ⟨_, hs1_b, hs1_r0⟩ := cbdNttPoly16_spec (shake256List_length 128 (sigma ++ [1#8]))
  obtain ⟨_, hs2_b, hs2_r0⟩ := cbdNttPoly16_spec (shake256List_length 128 (sigma ++ [2#8]))
  obtain ⟨_, he_b, he_r0⟩ :=
    cbdNttPoly16_spec (shake256List_length 128 (sigma ++ [BitVec.ofNat 8 (3 + col)]))
  exact tHatDotStdAdd_spec ha0_b ha1_b ha2_b hs0_b hs1_b hs2_b he_b
    (polyRepresents_congr_right ha0_r0 (sampleMatrixWith_true_getD hrho hcol (by decide)))
    (polyRepresents_congr_right ha1_r0 (sampleMatrixWith_true_getD hrho hcol (by decide)))
    (polyRepresents_congr_right ha2_r0 (sampleMatrixWith_true_getD hrho hcol (by decide)))
    (polyRepresents_congr_right hs0_r0 (sampleVecCbd2_map_getD hsig 0 0 (by decide)))
    (polyRepresents_congr_right hs1_r0 (sampleVecCbd2_map_getD hsig 0 1 (by decide)))
    (polyRepresents_congr_right hs2_r0 (sampleVecCbd2_map_getD hsig 0 2 (by decide)))
    (polyRepresents_congr_right he_r0 (sampleVecCbd2_map_getD hsig 3 col hcol))

attribute [local irreducible]
  blkPC05 dup8x16 polyVecNat simdAdd8h simdSub8h simdMul8h simdSqdmulh8h simdSshr8h simdMla8h

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdMla_8h
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSshr_8h_11 svc_simdDup_8h_gpr

private structure Seg4AddPres (s0 s : State) : Prop where
  x0  : s.readReg64 .x0  = s0.readReg64 .x0
  x1  : s.readReg64 .x1  = s0.readReg64 .x1
  x8  : s.readReg64 .x8  = s0.readReg64 .x8
  x9  : s.readReg64 .x9  = s0.readReg64 .x9
  x10 : s.readReg64 .x10 = s0.readReg64 .x10
  x11 : s.readReg64 .x11 = s0.readReg64 .x11
  x12 : s.readReg64 .x12 = s0.readReg64 .x12
  x13 : s.readReg64 .x13 = s0.readReg64 .x13
  x14 : s.readReg64 .x14 = s0.readReg64 .x14
  x15 : s.readReg64 .x15 = s0.readReg64 .x15
  x16 : s.readReg64 .x16 = s0.readReg64 .x16
  x17 : s.readReg64 .x17 = s0.readReg64 .x17
  x18 : s.readReg64 .x18 = s0.readReg64 .x18
  fp  : s.readReg64 .fp  = s0.readReg64 .fp
  v0  : s.readVReg128 0#5 = s0.readVReg128 0#5
  v1  : s.readVReg128 1#5 = s0.readVReg128 1#5
  v2  : s.readVReg128 2#5 = s0.readVReg128 2#5
  v3  : s.readVReg128 3#5 = s0.readVReg128 3#5

private theorem update2_prefix {f g : Nat → BitVec 128} {r : Nat}
    (hf : ∀ j, j < 2 * r → f j = g j) :
    ∀ j, j < 2 * (r + 1) →
      Function.update (Function.update f (2 * r) (g (2 * r))) (2 * r + 1) (g (2 * r + 1)) j = g j := by
  intro j hj
  by_cases h1 : j = 2 * r + 1
  · subst h1; simp
  · rw [Function.update_of_ne h1]
    by_cases h0 : j = 2 * r
    · subst h0; simp
    · rw [Function.update_of_ne h0]; exact hf j (by omega)

private theorem update2_suffix {f h : Nat → BitVec 128} {r : Nat} {v0 v1 : BitVec 128}
    (hf : ∀ j, 2 * r ≤ j → j < 32 → f j = h j) :
    ∀ j, 2 * (r + 1) ≤ j → j < 32 →
      Function.update (Function.update f (2 * r) v0) (2 * r + 1) v1 j = h j := by
  intro j hlo hhi
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  exact hf j (by omega) hhi

private theorem seg4_std_add_init [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s : State) (sp x8v x10v : BitVec 64) (P : SepProp)
    (hpc : s.pc = b + off605c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = x8v) (hx10 : s.readReg64 .x10 = x10v) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off6068) s P
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x2 = x10v ∧ s'.readReg64 .x3 = x8v ∧ s'.readReg64 .x4 = 16#64 ∧
        Seg4AddPres s s' ∧ P' = P) := by
  have _ : b = blkPl05.base := hb
  wp_steps
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp, by simp, by simp,
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp⟩, rfl⟩

set_option maxRecDepth 200000 in
private theorem seg4_std_add_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp eHatPtr : BitVec 64) {i r : Nat} (hi : i < 3) (hr : r < 16)
    (dot e : Poly16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off6068) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = eHatPtr + BitVec.ofNat 64 (16 + 32 * r))
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 (512 * i + 16 + 32 * r))
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 (16 - r))
    (hx12 : s.readReg64 .x12 = sp + 2208#64)
    (hx16 : s.readReg64 .x16 = 1353#64) (hx17 : s.readReg64 .x17 = 20553#64)
    (hx18 : s.readReg64 .x18 = 20159#64)
    (hv1 : s.readVReg128 1#5 = dup8x16 1024#16)
    (hv2 : s.readVReg128 2#5 = dup8x16 0xf2ff#16)
    (hv3 : s.readVReg128 3#5 = dup8x16 3329#16)
    (hpres : Seg4AddPres s0 s)
    (hf0 : f (2 * r) = polyVecNat dot (2 * r))
    (hf1 : f (2 * r + 1) = polyVecNat dot (2 * r + 1)) :
    let polyPtr := sp + 2208#64 + BitVec.ofNat 64 (512 * i)
    let out := tHatStdAddPoly dot e
    SepWP (blkPC05.rebase b (fun _ => none))
      (if r < 15 then b + off6068 else b + off60ec) s
      (PolyMem polyPtr f ∗ PolyMem eHatPtr (polyVecNat e) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x2 = eHatPtr + BitVec.ofNat 64 (16 + 32 * (r + 1)) ∧
        s'.readReg64 .x3 = BitVec.ofNat 64 (512 * i + 16 + 32 * (r + 1)) ∧
        s'.readReg64 .x4 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        Seg4AddPres s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update (Function.update f (2 * r) (polyVecNat out (2 * r)))
            (2 * r + 1) (polyVecNat out (2 * r + 1))) ∗
          PolyMem eHatPtr (polyVecNat e) ∗ Rest)) := by
  intro polyPtr out
  have _ := hi
  rcases hpres with ⟨p0, p1, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, pfp, pv0, pv1, pv2, pv3⟩
  wp_steps 3
  refine step_ldpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat dot (2 * r)) (v2 := polyVecNat dot (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; dsimp only [polyPtr]; clear * - hi hr; bv_omega)
    (by clear * -; bv_omega)
    (hf0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hf1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 15
  refine step_ldpQ128 (wb := none)
    (ea := eHatPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := eHatPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat e (2 * r)) (v2 := polyVecNat e (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx2]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 11
  have hv5_eq := tHatStdAdd_vec_eq dot e (2 * r) (by omega)
  have hv4_eq := tHatStdAdd_vec_eq dot e (2 * r + 1) (by omega)
  dsimp only at hv5_eq hv4_eq
  refine step_stpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat out (2 * r)) (v2 := polyVecNat out (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; dsimp only [polyPtr]; clear * - hi hr; bv_omega)
    (by clear * -; bv_omega)
    (by dsimp only [out]; rw [← hv5_eq]; simp)
    (by dsimp only [out]; rw [← hv4_eq]; simp)
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'
  have hcnd : ConditionHolds .NE
      (AddWithCarry64 (BitVec.ofNat 64 (16 - r)) (~~~1#64) true).2 = decide (r < 15) := by
    clear * - hr
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
        r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  by_cases hr15 : r < 15
  · simp only [hr15, ↓reduceIte]
    refine step_bCond_taken (pc := b + BitVec.ofNat 64 24808) (dst := b + off6068)
      (by wp_norm_lhs) (by simp [hrun]) (by rw [hb]; wp_norm_lhs)
      (by simpa [subsPState64, hr15] using hcnd)
      (by dsimp only [off6068]; clear * -; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * - hr15; bv_omega,
        by simp; clear * - hi hr15; bv_omega,
        by simp; clear * - hr15; bv_omega,
        ⟨by simp [p0], by simp [p1], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
          by simp [p12], by simp [p13], by simp [p14], by simp [p15], by simp [p16],
          by simp [p17], by simp [p18], by simp [pfp], by simp [pv0], by simp [pv1], by simp [pv2], by simp [pv3]⟩, rfl⟩
  · have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    refine step_bCond_not_taken (pc := b + BitVec.ofNat 64 24808) (dst := b + off60ec)
      (by wp_norm_lhs) (by simp [hrun]) (by rw [hb]; wp_norm_lhs)
      (by simpa [subsPState64, hr15] using hcnd)
      (by dsimp only [off60ec]; clear * -; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hr_eq],
        by simp [hr_eq]; clear * - hi; bv_omega,
        by simp [hr_eq],
        ⟨by simp [p0], by simp [p1], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
          by simp [p12], by simp [p13], by simp [p14], by simp [p15], by simp [p16],
          by simp [p17], by simp [p18], by simp [pfp], by simp [pv0], by simp [pv1], by simp [pv2], by simp [pv3]⟩, rfl⟩

private theorem seg4_std_add_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s0 : State) (sp eHatPtr : BitVec 64) {i : Nat} (hi : i < 3)
    (dot e : Poly16) (Rest : SepProp) :
    let polyPtr := sp + 2208#64 + BitVec.ofNat 64 (512 * i)
    let out := tHatStdAddPoly dot e
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + off6068 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x2 = eHatPtr + BitVec.ofNat 64 (16 + 32 * r) →
      s.readReg64 .x3 = BitVec.ofNat 64 (512 * i + 16 + 32 * r) →
      s.readReg64 .x4 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x12 = sp + 2208#64 →
      s.readReg64 .x16 = 1353#64 → s.readReg64 .x17 = 20553#64 → s.readReg64 .x18 = 20159#64 →
      s.readVReg128 1#5 = dup8x16 1024#16 → s.readVReg128 2#5 = dup8x16 0xf2ff#16 →
      s.readVReg128 3#5 = dup8x16 3329#16 →
      Seg4AddPres s0 s →
      (∀ k, k < 2 * r → f k = polyVecNat out k) →
      (∀ k, 2 * r ≤ k → k < 32 → f k = polyVecNat dot k) →
      SepWP (blkPC05.rebase b (fun _ => none)) (b + off60ec) s
        (PolyMem polyPtr f ∗ PolyMem eHatPtr (polyVecNat e) ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ Seg4AddPres s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat out) ∗ PolyMem eHatPtr (polyVecNat e) ∗ Rest)) := by
  intro polyPtr out rem
  induction rem with
  | zero =>
    intro r hr s f hpc hrun hsp hspA _hcl _hro hx2 hx3 hx4 hx12 hx16 hx17 hx18 hv1 hv2 hv3 hpres hpre hsuf
    have hreq : r = 15 := by omega
    subst hreq
    have hiter := seg4_std_add_iter hb s0 s sp eHatPtr hi (by decide : 15 < 16) dot e f Rest
      hpc hrun hsp hspA hx2 hx3 hx4 hx12 hx16 hx17 hx18 hv1 hv2 hv3 hpres
      (hsuf 30 (by decide) (by decide)) (hsuf 31 (by decide) (by decide))
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, hpres', rfl⟩
    refine ⟨hsp', hspA', hpres', ?_⟩
    unfold PolyMem
    rw [vecRangeMem_congr (n := 32) (fun j hj => update2_prefix (r := 15) hpre j hj)]
  | succ rem ih =>
    intro r hr s f hpc hrun hsp hspA hcl hro hx2 hx3 hx4 hx12 hx16 hx17 hx18 hv1 hv2 hv3 hpres hpre hsuf
    have hr15 : r < 15 := by omega
    have hiter := seg4_std_add_iter hb s0 s sp eHatPtr hi (by omega) dot e f Rest
      hpc hrun hsp hspA hx2 hx3 hx4 hx12 hx16 hx17 hx18 hv1 hv2 hv3 hpres
      (hsuf (2 * r) (by omega) (by omega)) (hsuf (2 * r + 1) (by omega) (by omega))
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m ⟨hsp_m, hspA_m, hx2_m, hx3_m, hx4_m, hpres_m, rfl⟩
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx2_m hx3_m hx4_m
      (hpres_m.x12.trans (hpres.x12.symm.trans hx12))
      (hpres_m.x16.trans (hpres.x16.symm.trans hx16))
      (hpres_m.x17.trans (hpres.x17.symm.trans hx17))
      (hpres_m.x18.trans (hpres.x18.symm.trans hx18))
      (hpres_m.v1.trans (hpres.v1.symm.trans hv1))
      (hpres_m.v2.trans (hpres.v2.symm.trans hv2))
      (hpres_m.v3.trans (hpres.v3.symm.trans hv3))
      hpres_m (update2_prefix hpre) (update2_suffix hsuf)

private theorem seg4_outer_tail [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp : BitVec 64) {i : Nat} (hi : i < 3) (P : SepProp)
    (hpc : s.pc = b + off60ec) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 6144#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (512 * i + 16))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (1536 * (i + 2)))
    (hx10 : s.readReg64 .x10 = sp + 17392#64 + BitVec.ofNat 64 (512 * i))
    (hpres : Seg4AddPres s0 s) :
    SepWP (blkPC05.rebase b (fun _ => none))
      (if i < 2 then b + off5cb0 else b + off60fc) s P
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .fp = s0.readReg64 .fp ∧
        s'.readReg64 .x0 = 6144#64 ∧ s'.readReg64 .x1 = s0.readReg64 .x1 ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (512 * (i + 1) + 16) ∧
        s'.readReg64 .x9 = BitVec.ofNat 64 (1536 * (i + 2)) ∧
        s'.readReg64 .x10 = sp + 17392#64 + BitVec.ofNat 64 (512 * (i + 1)) ∧
        s'.readReg64 .x11 = s0.readReg64 .x11 ∧ s'.readReg64 .x12 = s0.readReg64 .x12 ∧
        s'.readReg64 .x13 = s0.readReg64 .x13 ∧ s'.readReg64 .x14 = s0.readReg64 .x14 ∧
        s'.readReg64 .x15 = s0.readReg64 .x15 ∧ s'.readReg64 .x16 = s0.readReg64 .x16 ∧
        s'.readReg64 .x17 = s0.readReg64 .x17 ∧ s'.readReg64 .x18 = s0.readReg64 .x18 ∧
        s'.readVReg128 0#5 = s0.readVReg128 0#5 ∧ s'.readVReg128 1#5 = s0.readVReg128 1#5 ∧
        s'.readVReg128 2#5 = s0.readVReg128 2#5 ∧ P' = P) := by
  have _ : b = blkPl05.base := hb
  rcases hpres with ⟨_, p1, _, _, _, p11, p12, p13, p14, p15, p16, p17, p18, pfp, pv0, pv1, pv2, _⟩
  wp_steps 3
  have hcnd : ConditionHolds .NE
      (AddWithCarry64 (BitVec.ofNat 64 (1536 * (i + 2))) (~~~6144#64) true).2 = decide (i < 2) := by
    clear * - hi; rcases i with _ | _ | _ | _ <;> try omega
    all_goals decide
  by_cases hi2 : i < 2
  · simp only [hi2, ↓reduceIte]
    refine step_bCond_taken (pc := b + BitVec.ofNat 64 24824) (dst := b + off5cb0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simpa [subsPState64, hi2] using hcnd)
      (by dsimp only [off5cb0]; clear * -; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA, by simp [pfp],
        by simp [hx0], by simp [p1],
        by simp; clear * - hi2; bv_omega,
        by simp [hx9],
        by simp; clear * -; bv_omega,
        by simp [p11], by simp [p12], by simp [p13], by simp [p14],
        by simp [p15], by simp [p16], by simp [p17], by simp [p18],
        by simp [pv0], by simp [pv1], by simp [pv2], rfl⟩
  · have hi_eq : i = 2 := by omega
    simp only [hi2, ↓reduceIte]
    refine step_bCond_not_taken (pc := b + BitVec.ofNat 64 24824) (dst := b + off60fc)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simpa [subsPState64, hi2] using hcnd)
      (by dsimp only [off60fc]; clear * -; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA, by simp [pfp],
        by simp [hx0], by simp [p1],
        by simp [hi_eq],
        by simp [hx9],
        by simp [hi_eq],
        by simp [p11], by simp [p12], by simp [p13], by simp [p14],
        by simp [p15], by simp [p16], by simp [p17], by simp [p18],
        by simp [pv0], by simp [pv1], by simp [pv2], rfl⟩

private theorem seg4_row_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s : State) (sp : BitVec 64) {i : Nat} (hi : i < 3)
    (l0 l1 l2 r0 r1 r2 e : Poly16) (vInit vScr : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + off5cb0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = 6144#64) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 i)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (512 * i + 16))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (1536 * (i + 1)))
    (hx10 : s.readReg64 .x10 = sp + 17392#64 + BitVec.ofNat 64 (512 * i))
    (hx11 : s.readReg64 .x11 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx12 : s.readReg64 .x12 = sp + 2208#64)
    (hx13 : s.readReg64 .x13 = 62209#64) (hx14 : s.readReg64 .x14 = 3329#64)
    (hx15 : s.readReg64 .x15 = sp + 9984#64)
    (hx16 : s.readReg64 .x16 = 1353#64) (hx17 : s.readReg64 .x17 = 20553#64)
    (hx18 : s.readReg64 .x18 = 20159#64)
    (hv0 : s.readVReg128 0#5 = 0#128)
    (hv1 : s.readVReg128 1#5 = dup8x16 1024#16)
    (hv2 : s.readVReg128 2#5 = dup8x16 0xf2ff#16) :
    let polyPtr := sp + 2208#64 + BitVec.ofNat 64 (512 * i)
    let lhsBase := sp + 3744#64 + BitVec.ofNat 64 (1536 * i)
    let eHatPtr := sp + 17376#64 + BitVec.ofNat 64 (512 * i)
    let out := tHatStdAddPoly (neonDot3 l0 l1 l2 r0 r1 r2) e
    SepWP (blkPC05.rebase b (fun _ => none))
      (if i < 2 then b + off5cb0 else b + off60fc) s
      (Poly32Mem polyPtr vInit ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem (sp + 8416#64) (polyVecNat r0) ∗ PolyMem (sp + 8928#64) (polyVecNat r1) ∗
        PolyMem (sp + 9440#64) (polyVecNat r2) ∗
        PolyMem eHatPtr (polyVecNat e) ∗
        Poly32Mem (sp + 9984#64) vScr ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readReg64 .x0 = 6144#64 ∧ s'.readReg64 .x1 = BitVec.ofNat 64 (i + 1) ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (512 * (i + 1) + 16) ∧
        s'.readReg64 .x9 = BitVec.ofNat 64 (1536 * (i + 2)) ∧
        s'.readReg64 .x10 = sp + 17392#64 + BitVec.ofNat 64 (512 * (i + 1)) ∧
        s'.readReg64 .x11 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x12 = sp + 2208#64 ∧ s'.readReg64 .x13 = 62209#64 ∧
        s'.readReg64 .x14 = 3329#64 ∧ s'.readReg64 .x15 = sp + 9984#64 ∧
        s'.readReg64 .x16 = 1353#64 ∧ s'.readReg64 .x17 = 20553#64 ∧
        s'.readReg64 .x18 = 20159#64 ∧
        s'.readVReg128 0#5 = 0#128 ∧ s'.readVReg128 1#5 = dup8x16 1024#16 ∧
        s'.readVReg128 2#5 = dup8x16 0xf2ff#16 ∧
        P' = (PolyMem polyPtr (polyVecNat out) ∗
          PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
          PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
          PolyMem (sp + 8416#64) (polyVecNat r0) ∗ PolyMem (sp + 8928#64) (polyVecNat r1) ∗
          PolyMem (sp + 9440#64) (polyVecNat r2) ∗
          PolyMem eHatPtr (polyVecNat e) ∗
          Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 l2 r2))) ∗ Rest)) := by
  intro polyPtr lhsBase eHatPtr out
  let dot := neonDot3 l0 l1 l2 r0 r1 r2
  rw [show (Poly32Mem polyPtr vInit ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem (sp + 8416#64) (polyVecNat r0) ∗ PolyMem (sp + 8928#64) (polyVecNat r1) ∗
        PolyMem (sp + 9440#64) (polyVecNat r2) ∗
        PolyMem eHatPtr (polyVecNat e) ∗ Poly32Mem (sp + 9984#64) vScr ∗ Rest) =
      (Poly32Mem polyPtr vInit ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem (sp + 8416#64) (polyVecNat r0) ∗ PolyMem (sp + 8928#64) (polyVecNat r1) ∗
        PolyMem (sp + 9440#64) (polyVecNat r2) ∗ Poly32Mem (sp + 9984#64) vScr ∗
        (PolyMem eHatPtr (polyVecNat e) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl hro (seg4_row_dot hb s sp hi l0 l1 l2 r0 r1 r2 vInit vScr _
    hpc hrun hsp hspA hcl hro hx0 hx1 hx9 hx11 hx12 hx13 hx14 hx15 hv0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx0_1, hx1_1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1,
      hx15_1, hx16_1, hx17_1, hx18_1, hv0_1, hv1_1, hv2_1, hv3_1, rfl⟩
  refine sepWP_seq_env hcl1 hro1 (seg4_std_add_init hb s1 sp _ _ _
    hpc1 hrun1 hsp1 hspA1 (hx8_1.trans hx8) (hx10_1.trans hx10)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx2_2, hx3_2, hx4_2, hpres2, rfl⟩
  have hx2_2' : s2.readReg64 .x2 = eHatPtr + BitVec.ofNat 64 (16 + 32 * 0) := by
    rw [hx2_2]; dsimp only [eHatPtr]; clear * -; bv_omega
  have hx3_2' : s2.readReg64 .x3 = BitVec.ofNat 64 (512 * i + 16 + 32 * 0) := by
    simpa using hx3_2
  rw [show (PolyMem polyPtr (polyVecNat dot) ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem (sp + 8416#64) (polyVecNat r0) ∗ PolyMem (sp + 8928#64) (polyVecNat r1) ∗
        PolyMem (sp + 9440#64) (polyVecNat r2) ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 l2 r2))) ∗
        (PolyMem eHatPtr (polyVecNat e) ∗ Rest)) =
      (PolyMem polyPtr (polyVecNat dot) ∗ PolyMem eHatPtr (polyVecNat e) ∗
        (PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
          PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
          PolyMem (sp + 8416#64) (polyVecNat r0) ∗ PolyMem (sp + 8928#64) (polyVecNat r1) ∗
          PolyMem (sp + 9440#64) (polyVecNat r2) ∗
          Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 l2 r2))) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl2 hro2 (seg4_std_add_loop hb s1 sp eHatPtr hi dot e _ 15 0 rfl s2 (polyVecNat dot)
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx2_2' hx3_2' hx4_2
    (hpres2.x12.trans hx12_1) (hpres2.x16.trans (hx16_1.trans hx16))
    (hpres2.x17.trans (hx17_1.trans hx17)) (hpres2.x18.trans (hx18_1.trans hx18))
    (hpres2.v1.trans (hv1_1.trans hv1)) (hpres2.v2.trans (hv2_1.trans hv2))
    (hpres2.v3.trans hv3_1) hpres2 (by omega) (fun _ _ _ => rfl)) ?_
  rintro s3 P3 hpc3 hrun3 _hcl3 _hro3 ⟨hsp3, hspA3, hpres3, rfl⟩
  refine SepWP.mono (seg4_outer_tail hb s1 s3 sp hi _ hpc3 hrun3 hsp3 hspA3
    (hpres3.x0.trans hx0_1) (hpres3.x8.trans (hx8_1.trans hx8))
    (hpres3.x9.trans hx9_1) (hpres3.x10.trans (hx10_1.trans hx10)) hpres3) ?_
  rintro s' P' _ _ ⟨hsp', hspA', hfp', hx0', hx1', hx8', hx9', hx10', hx11', hx12', hx13',
    hx14', hx15', hx16', hx17', hx18', hv0', hv1', hv2', rfl⟩
  exact ⟨hsp', hspA', hfp'.trans hfp1, hx0', hx1'.trans hx1_1, hx8', hx9', hx10',
    hx11'.trans hx11_1, hx12'.trans hx12_1, hx13'.trans hx13_1, hx14'.trans hx14_1,
    hx15'.trans hx15_1, hx16'.trans (hx16_1.trans hx16), hx17'.trans (hx17_1.trans hx17),
    hx18'.trans (hx18_1.trans hx18), hv0'.trans hv0_1, hv1'.trans (hv1_1.trans hv1),
    hv2'.trans (hv2_1.trans hv2), sepProp_ext (by sep_frame) (by sep_frame)⟩

/-- Postcondition entering Segment 5 (`+0x60fc`, `b + off60fc`). -/
@[expose] def Seg4Exit [MlKemPlacement]
    (b : BitVec 64) (s0 : State) (seedA outPtr : BitVec 64)
    (seed : List (BitVec 8)) (F : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  let sp := s0.sp - 30080#64
  let g := sha3_512List (seed.take 32 ++ [3#8])
  sf.pc = b + off60fc ∧
  sf.status = .Running ∧
  sf.sp = sp ∧
  sf.spAligned = true ∧
  sf.readReg64 .fp = s0.sp - 96#64 ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
  MlKemRoOk mlkemMpl sf.mem ∧
  (Pf ⊢ SavedFrame05 s0.sp s0 ∗
    stackAt sp 1136 ∗
    (seedA ↦ₛ seed) ∗
    (sp ↦ₛ g.take 32) ∗
    ((sp + 32#64) ↦₆₄ seedA) ∗
    ((sp + 40#64) ↦₆₄ outPtr) ∗
    ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗
    memRegion (sp + 56#64) 80 ∗
    ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
    memRegion (sp + 144#64) 2064 ∗
    THatMem sp (g.take 32) (g.drop 32) ∗
    AMatrixMem sp (g.take 32) ∗
    memRegion (sp + 8352#64) 64 ∗
    SHatMem sp (g.drop 32) ∗
    memRegion (sp + 9952#64) 7424 ∗
    EHatMem sp (g.drop 32) ∗
    memRegion (sp + 18912#64) 10496 ∗
    ((sp + 29408#64) ↦ₛ g.drop 32) ∗
    memRegion (sp + 29440#64) 480 ∗
    F)

private theorem sepWP_alloc_poly32 {prog : Program} {target_pc : BitVec 64}
    {s : State} {ptr : BitVec 64} {R : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : Vec32, SepWP prog target_pc s (Poly32Mem ptr v ∗ R) post) :
    SepWP prog target_pc s (memRegion ptr 512 ∗ R) post := by
  refine SepWP.of_memRegion_vecRangeMem 32 ptr (by decide) rfl ?_
  intro f
  change SepWP prog target_pc s (PolyMem ptr f ∗ R) post
  rw [← poly32Mem_ofFn]; exact h (Vec32.ofFn f)

private theorem aMat_rearrange (sp : BitVec 64) (rho : List (BitVec 8)) :
    AMatrixMem sp rho =
      (PolyMem (sp + 3744#64) (polyVecNat ((sampleNtt (rowSeed rho 0 0)).map (BitVec.ofNat 16))) ∗
       PolyMem ((sp + 3744#64) + 512#64) (polyVecNat ((sampleNtt (rowSeed rho 1 0)).map (BitVec.ofNat 16))) ∗
       PolyMem ((sp + 3744#64) + 1024#64) (polyVecNat ((sampleNtt (rowSeed rho 2 0)).map (BitVec.ofNat 16))) ∗
       PolyMem (sp + 3744#64 + 1536#64) (polyVecNat ((sampleNtt (rowSeed rho 0 1)).map (BitVec.ofNat 16))) ∗
       PolyMem ((sp + 3744#64 + 1536#64) + 512#64) (polyVecNat ((sampleNtt (rowSeed rho 1 1)).map (BitVec.ofNat 16))) ∗
       PolyMem ((sp + 3744#64 + 1536#64) + 1024#64) (polyVecNat ((sampleNtt (rowSeed rho 2 1)).map (BitVec.ofNat 16))) ∗
       PolyMem (sp + 3744#64 + 3072#64) (polyVecNat ((sampleNtt (rowSeed rho 0 2)).map (BitVec.ofNat 16))) ∗
       PolyMem ((sp + 3744#64 + 3072#64) + 512#64) (polyVecNat ((sampleNtt (rowSeed rho 1 2)).map (BitVec.ofNat 16))) ∗
       PolyMem ((sp + 3744#64 + 3072#64) + 1024#64) (polyVecNat ((sampleNtt (rowSeed rho 2 2)).map (BitVec.ofNat 16)))) := by
  unfold AMatrixMem RowPolyOut
  have h00 : sp + 3744#64 + BitVec.ofNat 64 (512 * 0) = sp + 3744#64 := by clear * -; bv_omega
  have h10 : sp + 3744#64 + BitVec.ofNat 64 (512 * 1) = (sp + 3744#64) + 512#64 := by clear * -; bv_omega
  have h20 : sp + 3744#64 + BitVec.ofNat 64 (512 * 2) = (sp + 3744#64) + 1024#64 := by clear * -; bv_omega
  have h01 : sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 0) = sp + 3744#64 + 1536#64 := by clear * -; bv_omega
  have h11 : sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 1) = (sp + 3744#64 + 1536#64) + 512#64 := by clear * -; bv_omega
  have h21 : sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 2) = (sp + 3744#64 + 1536#64) + 1024#64 := by clear * -; bv_omega
  have h02 : sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 0) = sp + 3744#64 + 3072#64 := by clear * -; bv_omega
  have h12 : sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 1) = (sp + 3744#64 + 3072#64) + 512#64 := by clear * -; bv_omega
  have h22 : sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 2) = (sp + 3744#64 + 3072#64) + 1024#64 := by clear * -; bv_omega
  rw [h00, h10, h20, h01, h11, h21, h02, h12, h22]
  exact sepProp_ext (by sep_frame) (by sep_frame)

attribute [local irreducible]
  sha3_512List shake256List sampleNtt cbdNttPoly16 neonDot3 neonPolyNttMul16 tHatStdAddPoly in
theorem seg4_matvec_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s : State) (seedA outPtr : BitVec 64) (seed : List (BitVec 8)) (F : SepProp)
    {P : SepProp} (hexit : Seg3Exit b s0 seedA outPtr seed F s P) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off60fc) s P
      (Seg4Exit b s0 seedA outPtr seed F) := by
  let sp := s0.sp - 30080#64
  let g := sha3_512List (seed.take 32 ++ [3#8])
  let rho := g.take 32
  let sigma := g.drop 32
  rcases hexit with ⟨hpc, hrun, hsp, hspA, hfp, hcl, hro, hP⟩
  have h144 : memRegion (sp + 144#64) 3600 =
      memRegion (sp + 144#64) 2064 ∗ memRegion (sp + 2208#64) 512 ∗
      memRegion (sp + 2720#64) 512 ∗ memRegion (sp + 3232#64) 512 := by
    clear * -
    rw [memRegion_split' (b := sp + 144#64) (b' := sp + 2208#64) (n := 2064) (k := (1536 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 2208#64) (b' := sp + 2720#64) (n := 512) (k := (1024 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 2720#64) (b' := sp + 3232#64) (n := 512) (k := (512 : Nat))
          rfl (by bv_omega) (by decide)]
  have h9952 : memRegion (sp + 9952#64) 7424 =
      memRegion (sp + 9952#64) 32 ∗ memRegion (sp + 9984#64) 512 ∗
      memRegion (sp + 10496#64) 6880 := by
    clear * -
    rw [memRegion_split' (b := sp + 9952#64) (b' := sp + 9984#64) (n := 32) (k := (7392 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 9984#64) (b' := sp + 10496#64) (n := 512) (k := (6880 : Nat))
          rfl (by bv_omega) (by decide)]
  let Frame :=
    SavedFrame05 s0.sp s0 ∗ stackAt sp 1136 ∗ (seedA ↦ₛ seed) ∗ (sp ↦ₛ rho) ∗
    ((sp + 32#64) ↦₆₄ seedA) ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
    ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ memRegion (sp + 56#64) 80 ∗
    ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ memRegion (sp + 144#64) 2064 ∗
    memRegion (sp + 8352#64) 64 ∗ memRegion (sp + 9952#64) 32 ∗
    memRegion (sp + 10496#64) 6880 ∗ memRegion (sp + 18912#64) 10496 ∗
    ((sp + 29408#64) ↦ₛ sigma) ∗ memRegion (sp + 29440#64) 480 ∗ F
  refine SepWP.weaken_pre hP ?_
  refine SepWP.weaken_pre (show _ ⊢
      memRegion (sp + 2208#64) 512 ∗ (memRegion (sp + 2720#64) 512 ∗
      (memRegion (sp + 3232#64) 512 ∗ (memRegion (sp + 9984#64) 512 ∗
      (AMatrixMem sp rho ∗ SHatMem sp sigma ∗ EHatMem sp sigma ∗ Frame)))) by
    rw [h144, h9952]; dsimp only [Frame, rho, sigma]; sep_frame) ?_
  apply sepWP_alloc_poly32; intro vT0
  refine SepWP.weaken_pre (show Poly32Mem (sp + 2208#64) vT0 ∗ _ ⊢
      memRegion (sp + 2720#64) 512 ∗ (Poly32Mem (sp + 2208#64) vT0 ∗ _) by sep_frame) ?_
  apply sepWP_alloc_poly32; intro vT1
  refine SepWP.weaken_pre (show Poly32Mem (sp + 2720#64) vT1 ∗ _ ⊢
      memRegion (sp + 3232#64) 512 ∗ (Poly32Mem (sp + 2208#64) vT0 ∗
        Poly32Mem (sp + 2720#64) vT1 ∗ _) by sep_frame) ?_
  apply sepWP_alloc_poly32; intro vT2
  refine SepWP.weaken_pre (show Poly32Mem (sp + 3232#64) vT2 ∗ _ ⊢
      memRegion (sp + 9984#64) 512 ∗ (Poly32Mem (sp + 2208#64) vT0 ∗
        Poly32Mem (sp + 2720#64) vT1 ∗ Poly32Mem (sp + 3232#64) vT2 ∗ _) by sep_frame) ?_
  apply sepWP_alloc_poly32; intro vScr
  refine sepWP_seq_env hcl hro (seg4_setup hb hbase s sp _ hpc hrun hsp hspA) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx0_1, hx1_1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1,
      hx15_1, hx16_1, hx17_1, hx18_1, hv0_1, hv1_1, hv2_1, rfl⟩
  let a (r c : Nat) := (sampleNtt (rowSeed rho r c)).map (BitVec.ofNat 16)
  let sh (j : Nat) := cbdNttPoly16 (shake256List 128 (sigma ++ [BitVec.ofNat 8 j]))
  let eh (c : Nat) := cbdNttPoly16 (shake256List 128 (sigma ++ [BitVec.ofNat 8 (3 + c)]))
  let Rest0 :=
    Poly32Mem (sp + 2720#64) vT1 ∗ Poly32Mem (sp + 3232#64) vT2 ∗
    PolyMem (sp + 3744#64 + 1536#64) (polyVecNat (a 0 1)) ∗
    PolyMem ((sp + 3744#64 + 1536#64) + 512#64) (polyVecNat (a 1 1)) ∗
    PolyMem ((sp + 3744#64 + 1536#64) + 1024#64) (polyVecNat (a 2 1)) ∗
    PolyMem (sp + 3744#64 + 3072#64) (polyVecNat (a 0 2)) ∗
    PolyMem ((sp + 3744#64 + 3072#64) + 512#64) (polyVecNat (a 1 2)) ∗
    PolyMem ((sp + 3744#64 + 3072#64) + 1024#64) (polyVecNat (a 2 2)) ∗
    PolyMem (sp + 17888#64) (polyVecNat (eh 1)) ∗ PolyMem (sp + 18400#64) (polyVecNat (eh 2)) ∗ Frame
  have hz1 : sp + 2208#64 + BitVec.ofNat 64 (512 * 0) = sp + 2208#64 := by clear * -; bv_omega
  have hz2 : sp + 3744#64 + BitVec.ofNat 64 (1536 * 0) = sp + 3744#64 := by clear * -; bv_omega
  have hz3 : sp + 17376#64 + BitVec.ofNat 64 (512 * 0) = sp + 17376#64 := by clear * -; bv_omega
  have h1a : sp + 2208#64 + BitVec.ofNat 64 (512 * 1) = sp + 2720#64 := by clear * -; bv_omega
  have h1b : sp + 3744#64 + BitVec.ofNat 64 (1536 * 1) = sp + 3744#64 + 1536#64 := by clear * -; bv_omega
  have h1c : sp + 17376#64 + BitVec.ofNat 64 (512 * 1) = sp + 17888#64 := by clear * -; bv_omega
  have h2a : sp + 2208#64 + BitVec.ofNat 64 (512 * 2) = sp + 3232#64 := by clear * -; bv_omega
  have h2b : sp + 3744#64 + BitVec.ofNat 64 (1536 * 2) = sp + 3744#64 + 3072#64 := by clear * -; bv_omega
  have h2c : sp + 17376#64 + BitVec.ofNat 64 (512 * 2) = sp + 18400#64 := by clear * -; bv_omega
  refine SepWP.weaken_pre (show _ ⊢
      Poly32Mem (sp + 2208#64 + BitVec.ofNat 64 (512 * 0)) vT0 ∗
        PolyMem (sp + 3744#64 + BitVec.ofNat 64 (1536 * 0)) (polyVecNat (a 0 0)) ∗
        PolyMem ((sp + 3744#64 + BitVec.ofNat 64 (1536 * 0)) + 512#64) (polyVecNat (a 1 0)) ∗
        PolyMem ((sp + 3744#64 + BitVec.ofNat 64 (1536 * 0)) + 1024#64) (polyVecNat (a 2 0)) ∗
        PolyMem (sp + 8416#64) (polyVecNat (sh 0)) ∗ PolyMem (sp + 8928#64) (polyVecNat (sh 1)) ∗
        PolyMem (sp + 9440#64) (polyVecNat (sh 2)) ∗
        PolyMem (sp + 17376#64 + BitVec.ofNat 64 (512 * 0)) (polyVecNat (eh 0)) ∗
        Poly32Mem (sp + 9984#64) vScr ∗ Rest0 by
    rw [aMat_rearrange]; unfold SHatMem EHatMem
    rw [hz1, hz2, hz3]; dsimp only [Rest0, a, sh, eh]; sep_frame) ?_
  have hi0 := seg4_row_ok hb s1 sp (i := 0) (by decide)
    (a 0 0) (a 1 0) (a 2 0) (sh 0) (sh 1) (sh 2) (eh 0) vT0 vScr Rest0
    hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx0_1 hx1_1 hx8_1 hx9_1
    (by simpa using hx10_1) hx11_1 hx12_1 hx13_1 hx14_1 hx15_1 hx16_1 hx17_1 hx18_1
    hv0_1 hv1_1 hv2_1
  dsimp only at hi0; simp only [Nat.zero_lt_two, ↓reduceIte] at hi0
  refine sepWP_seq_env hcl1 hro1 hi0 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hfp2, hx0_2, hx1_2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx13_2, hx14_2,
      hx15_2, hx16_2, hx17_2, hx18_2, hv0_2, hv1_2, hv2_2, rfl⟩
  let Rest1 :=
    PolyMem (sp + 2208#64) (polyVecNat (tHatPoly16 rho sigma 0)) ∗ Poly32Mem (sp + 3232#64) vT2 ∗
    PolyMem (sp + 3744#64) (polyVecNat (a 0 0)) ∗
    PolyMem ((sp + 3744#64) + 512#64) (polyVecNat (a 1 0)) ∗
    PolyMem ((sp + 3744#64) + 1024#64) (polyVecNat (a 2 0)) ∗
    PolyMem (sp + 3744#64 + 3072#64) (polyVecNat (a 0 2)) ∗
    PolyMem ((sp + 3744#64 + 3072#64) + 512#64) (polyVecNat (a 1 2)) ∗
    PolyMem ((sp + 3744#64 + 3072#64) + 1024#64) (polyVecNat (a 2 2)) ∗
    PolyMem (sp + 17376#64) (polyVecNat (eh 0)) ∗ PolyMem (sp + 18400#64) (polyVecNat (eh 2)) ∗ Frame
  refine SepWP.weaken_pre (show _ ⊢
      Poly32Mem (sp + 2208#64 + BitVec.ofNat 64 (512 * 1)) vT1 ∗
        PolyMem (sp + 3744#64 + BitVec.ofNat 64 (1536 * 1)) (polyVecNat (a 0 1)) ∗
        PolyMem ((sp + 3744#64 + BitVec.ofNat 64 (1536 * 1)) + 512#64) (polyVecNat (a 1 1)) ∗
        PolyMem ((sp + 3744#64 + BitVec.ofNat 64 (1536 * 1)) + 1024#64) (polyVecNat (a 2 1)) ∗
        PolyMem (sp + 8416#64) (polyVecNat (sh 0)) ∗ PolyMem (sp + 8928#64) (polyVecNat (sh 1)) ∗
        PolyMem (sp + 9440#64) (polyVecNat (sh 2)) ∗
        PolyMem (sp + 17376#64 + BitVec.ofNat 64 (512 * 1)) (polyVecNat (eh 1)) ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 (a 2 0) (sh 2)))) ∗ Rest1 by
    rw [hz1, hz2, hz3, h1a, h1b, h1c]
    dsimp only [Rest0, Rest1, tHatPoly16, a, sh, eh]; sep_frame) ?_
  have hi1 := seg4_row_ok hb s2 sp (i := 1) (by decide)
    (a 0 1) (a 1 1) (a 2 1) (sh 0) (sh 1) (sh 2) (eh 1)
    vT1 (Vec32.ofFn (polyVecNat (neonPolyNttMul16 (a 2 0) (sh 2)))) Rest1
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2
    hx11_2 hx12_2 hx13_2 hx14_2 hx15_2 hx16_2 hx17_2 hx18_2 hv0_2 hv1_2 hv2_2
  dsimp only at hi1; simp only [Nat.one_lt_two, ↓reduceIte] at hi1
  refine sepWP_seq_env hcl2 hro2 hi1 ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp3, hx0_3, hx1_3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx13_3, hx14_3,
      hx15_3, hx16_3, hx17_3, hx18_3, hv0_3, hv1_3, hv2_3, rfl⟩
  let Rest2 :=
    PolyMem (sp + 2208#64) (polyVecNat (tHatPoly16 rho sigma 0)) ∗
    PolyMem (sp + 2720#64) (polyVecNat (tHatPoly16 rho sigma 1)) ∗
    PolyMem (sp + 3744#64) (polyVecNat (a 0 0)) ∗
    PolyMem ((sp + 3744#64) + 512#64) (polyVecNat (a 1 0)) ∗
    PolyMem ((sp + 3744#64) + 1024#64) (polyVecNat (a 2 0)) ∗
    PolyMem (sp + 3744#64 + 1536#64) (polyVecNat (a 0 1)) ∗
    PolyMem ((sp + 3744#64 + 1536#64) + 512#64) (polyVecNat (a 1 1)) ∗
    PolyMem ((sp + 3744#64 + 1536#64) + 1024#64) (polyVecNat (a 2 1)) ∗
    PolyMem (sp + 17376#64) (polyVecNat (eh 0)) ∗ PolyMem (sp + 17888#64) (polyVecNat (eh 1)) ∗ Frame
  refine SepWP.weaken_pre (show _ ⊢
      Poly32Mem (sp + 2208#64 + BitVec.ofNat 64 (512 * 2)) vT2 ∗
        PolyMem (sp + 3744#64 + BitVec.ofNat 64 (1536 * 2)) (polyVecNat (a 0 2)) ∗
        PolyMem ((sp + 3744#64 + BitVec.ofNat 64 (1536 * 2)) + 512#64) (polyVecNat (a 1 2)) ∗
        PolyMem ((sp + 3744#64 + BitVec.ofNat 64 (1536 * 2)) + 1024#64) (polyVecNat (a 2 2)) ∗
        PolyMem (sp + 8416#64) (polyVecNat (sh 0)) ∗ PolyMem (sp + 8928#64) (polyVecNat (sh 1)) ∗
        PolyMem (sp + 9440#64) (polyVecNat (sh 2)) ∗
        PolyMem (sp + 17376#64 + BitVec.ofNat 64 (512 * 2)) (polyVecNat (eh 2)) ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 (a 2 1) (sh 2)))) ∗ Rest2 by
    rw [h1a, h1b, h1c, h2a, h2b, h2c]
    dsimp only [Rest1, Rest2, tHatPoly16, a, sh, eh]; sep_frame) ?_
  have hi2 := seg4_row_ok hb s3 sp (i := 2) (by decide)
    (a 0 2) (a 1 2) (a 2 2) (sh 0) (sh 1) (sh 2) (eh 2)
    vT2 (Vec32.ofFn (polyVecNat (neonPolyNttMul16 (a 2 1) (sh 2)))) Rest2
    hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3
    hx11_3 hx12_3 hx13_3 hx14_3 hx15_3 hx16_3 hx17_3 hx18_3 hv0_3 hv1_3 hv2_3
  dsimp only at hi2; simp only [Nat.lt_irrefl, ↓reduceIte] at hi2
  refine sepWP_seq_env hcl3 hro3 hi2 ?_
  rintro sf Pf hpcf hrunf hclf hrof
    ⟨hspf, hspAf, hfpf, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  refine SepWP.done hpcf hrunf ⟨hpcf, hrunf, hspf, hspAf,
    hfpf.trans (hfp3.trans (hfp2.trans (hfp1.trans hfp))), hclf, hrof, ?_⟩
  rw [h2a, h2b, h2c]
  refine entails_sub (poly32Mem_entails_memRegion (sp + 9984#64) _)
    (by sep_frame) ?_
  rw [aMat_rearrange]; unfold THatMem SHatMem EHatMem
  rw [h9952]; dsimp only [Rest2, Frame, tHatPoly16, a, sh, eh, rho, sigma]; sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4MatVec

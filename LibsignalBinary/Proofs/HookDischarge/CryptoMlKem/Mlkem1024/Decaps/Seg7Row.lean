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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Add
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvSym1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvSym1c
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7Dot2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvLow

/-!
# `kyber_decapsulate` (`B06`) — Segment 7 `u = InvNTT(Âᵀ ∘ r̂) + e₁` (`+0x9380 .. +0xafc0`)

Composes `seg7_init`, `Seg7Dot2.seg7_dot_ok`, `Seg7InvLow.seg7_inv_low_ok`,
`Seg7InvSym1c` (`sepWP_of_runSymRange`), `seg7_add_ok`, and `seg7_outer_tail`
across `row = 0..3` to compute `uVec[0..3]` at `[sp + 30448, sp + 32496)`, and proves pure
soundness (`PolyBounded16 1664` + `PolyRepresents`) against `Spec.indCpaEncryptWith`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7Row
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMla8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h)
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
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec32 VecRangeMem
  poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat step_ldpQ128 step_ldrQ128 step_strQ128
  vecRangeMem_congr vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16 lowerInvNtt16_size upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  exec_simdAdd_8h exec_simdDup_8h_gpr exec_simdMla_8h exec_simdMovi_8h_1024
  exec_simdMul_8h exec_simdMvni_8h_f2ff exec_simdSqdmulh_8h exec_simdSshr_8h_1
  exec_simdSshr_8h_11 exec_simdSub_8h sqdmulh8hFlags)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (seg5FinalPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Add (seg5Add_vec_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (rowSeed_eq_of_len32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (exec_simdMovi_2d_0)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr Spill40 SpillSliceMem SymEnv SymGprs SymSpill40 SymVRegs evalSExpr evalSymGpr
  spill40_ofFn_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SrcOptMem SymSpatial SymStateMatches blk06NoRelocInRange polyPtr symSpill40_eval_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym (sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  poly_eq_upperInvNtt16 symUpperInvNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure (
  ATransAt ATransRowAt aTransPoly06 shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt (
  rHatPoly16 rHatPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul (
  neonDot4 neonDot4_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvSym1a (
  cfgSeg7InvSym symSeg7InvSymInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvSym1c (
  run_seg7_inv1 seg7_inv_ast_eq seg7_inv_noSpillVreg symSeg7InvSymEnd)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7Dot2 (
  Seg7DotPreserved offDotEnd offDotStart ro00Sym seg7_dot_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7InvLow (
  Seg7InvLowPreserved offInvLowEnd offInvLowStart seg7_inv_low_ok)
section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x9380 → 0x93e0, 0xaf20 → 0xafbc]
end

@[simp, arm64_norm, wp_norm] abbrev offSeg7Start : BitVec 64 := BitVec.ofNat 64 37760
@[simp, arm64_norm, wp_norm] abbrev offAddStart  : BitVec 64 := BitVec.ofNat 64 44832
@[simp, arm64_norm, wp_norm] abbrev offAddTail   : BitVec 64 := BitVec.ofNat 64 44968
@[simp, arm64_norm, wp_norm] abbrev offSeg7Mid   : BitVec 64 := BitVec.ofNat 64 44992

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl
@[simp, arm64_norm, wp_norm]
private theorem readReg64_orFpsr' (s : State) (fl : BitVec 32) (r : Reg) :
    (s.orFpsr fl).readReg64 r = s.readReg64 r := State.readReg64_orFpsr s fl r
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
    (s.orFpsr fl).sp = s.sp := rfl
@[simp, arm64_norm, wp_norm]
private theorem pstate_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pstate = s.pstate := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdAdd_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdAdd8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdAdd_8h rm rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdSub_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdSub8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdSub_8h rm rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdMul_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10011#5 rn rd) s =
      (s.writeVReg128 rd (simdMul8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdMul_8h rm rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdMla_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10010#5 rn rd) s =
      (s.writeVReg128 rd
        (simdMla8h (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdMla_8h rm rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdSqdmulh_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10110#5 rn rd) s =
      ((s.writeVReg128 rd (simdSqdmulh8h (s.readVReg128 rn) (s.readVReg128 rm))).orFpsr
        (sqdmulh8hFlags (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdSqdmulh_8h rm rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdSshr_8h_1' {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0011#4 0b111#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshr8h (s.readVReg128 rn) 1)).advancePC :=
  exec_simdSshr_8h_1 rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdSshr_8h_11' {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0010#4 0b101#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshr8h (s.readVReg128 rn) 11)).advancePC :=
  exec_simdSshr_8h_11 rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_8h_1024' {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b10100#5 4#5 rd) s =
      (s.writeVReg128 rd (dup8x16 1024#16)).advancePC :=
  exec_simdMovi_8h_1024 rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdMvni_8h_f2ff' {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b10100#5 13#5 rd) s =
      (s.writeVReg128 rd (dup8x16 0xf2ff#16)).advancePC :=
  exec_simdMvni_8h_f2ff rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdDup_8h_gpr' {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 0b00010#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd (dup8x16 ((s.readReg64 (Reg.fromZRBits rn)).truncate 16))).advancePC :=
  exec_simdDup_8h_gpr rn rd s

attribute [local wp_norm ↓ high]
  exec_simdMovi_2d_0 exec_simdAdd_8h' exec_simdSub_8h' exec_simdMul_8h' exec_simdMla_8h'
  exec_simdSqdmulh_8h' exec_simdSshr_8h_1' exec_simdSshr_8h_11'
  exec_simdMovi_8h_1024' exec_simdMvni_8h_f2ff' exec_simdDup_8h_gpr'

/-! ## 1. Pure `uVecPoly06` Soundness Against `Spec.indCpaEncryptWith` (`K = 4`) -/

@[expose] def seg7AddPoly (inv e1 : Poly16) : Poly16 :=
  seg5FinalPoly inv e1 (Array.replicate 256 0#16)

@[expose] noncomputable def uVecPoly06 (rho coins : List (BitVec 8)) (row : Nat) : Poly16 :=
  let dot := neonDot4
    (aTransPoly06 rho row 0) (aTransPoly06 rho row 1)
    (aTransPoly06 rho row 2) (aTransPoly06 rho row 3)
    (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
    (rHatPoly16 (shake256List 128 (coins ++ [3#8])))
  let e1 := neonCbd2Poly16 (shake256List 128 (coins ++ [BitVec.ofNat 8 (4 + row)]))
  seg7AddPoly (neonInvNttMontgomery16 dot) e1
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

private theorem sampleMatrixWith_false_getD4 (rho : List (BitVec 8)) {row col : Nat}
    (hrow : row < 4) (hcol : col < 4) :
    ((sampleMatrixWith sampleNtt 4 rho false).getD row #[]).getD col zeroPoly =
      sampleNtt (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base.rowSeed
        rho row col) := by
  unfold sampleMatrixWith LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base.rowSeed
  dsimp only
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hrow, ↓reduceDIte, Option.getD_some, Array.getElem?_ofFn,
    hcol, Bool.false_eq_true, ↓reduceIte]

private theorem aTransPoly06_spec (rho : List (BitVec 8)) (row col : Nat) :
    PolyBounded16 4095 (aTransPoly06 rho row col) ∧
    PolyRepresents (aTransPoly06 rho row col)
      (sampleNtt (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base.rowSeed
        rho row col)) := by
  unfold aTransPoly06
  set f := sampleNtt (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base.rowSeed
    rho row col)
  obtain ⟨hsz, hlt⟩ := sampleNtt_canonical
    (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base.rowSeed rho row col)
  have hmsz : (f.map (BitVec.ofNat 16)).size = 256 := by simp [f, hsz]
  have hint : ∀ i < 256, ((f.map (BitVec.ofNat 16)).getD i 0#16).toInt = (f.getD i 0 : Int) := by
    intro i hi
    have hq : f.getD i 0 < 3329 := hlt i hi
    have hget : (f.map (BitVec.ofNat 16)).getD i 0#16 = BitVec.ofNat 16 (f.getD i 0) := by
      simp [Array.getD, f, hsz, hi]
    set c := f.getD i 0
    rw [hget, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [show 2 * c < 65536 by omega, ↓reduceIte]
  exact ⟨⟨hmsz, fun i hi => by have hq : f.getD i 0 < 3329 := hlt i hi; rw [hint i hi]; omega⟩,
    ⟨hmsz, fun i hi => by rw [hint i hi]⟩⟩

section BarrettBridge
attribute [local irreducible] neonBarrettReduce16 neonMontgomeryMul16

private theorem seg7AddPoly_eq_barrett {dot : Poly16} (hdot : dot.size = 256) (e1 : Poly16) :
    seg7AddPoly (neonInvNttMontgomery16 dot) e1 =
      (polyAdd16 (neonPolyInvNttFromMontInv16 dot) e1).map neonBarrettReduce16 := by
  have hinv : (neonInvNttMontgomery16 dot).size = 256 := by
    rw [← upperInvNtt16_lowerInvNtt16 dot,
      LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure.upperInvNtt16_size]
    exact lowerInvNtt16_size hdot
  unfold neonPolyInvNttFromMontInv16 seg7AddPoly seg5FinalPoly polyAdd16
  set p := neonInvNttMontgomery16 dot
  apply Array.ext
  · simp
  · intro i hi1 hi2
    have hip : i < p.size := by simp at hi1; omega
    simp [Array.getD, hip]

end BarrettBridge

private theorem polyBounded16_mono {b1 b2 : Int} {p : Poly16}
    (hle : b1 ≤ b2) (h : PolyBounded16 b1 p) : PolyBounded16 b2 p :=
  ⟨h.1, fun i hi => ⟨by have := (h.2 i hi).1; omega, by have := (h.2 i hi).2; omega⟩⟩

section PureUVec
attribute [local irreducible] shake256List sampleNtt polyNtt polyInvNtt samplePolyCbd2

set_option maxRecDepth 4000 in
theorem uVecPoly06_spec (rho : List (BitVec 8)) {coins : List (BitVec 8)}
    (hcoins : coins.length = 32) {row : Nat} (hrow : row < 4) :
    let aTrans := sampleMatrixWith sampleNtt 4 rho false
    let rHat := (sampleVecCbd2 4 coins 0).map polyNtt
    let e1Vec := sampleVecCbd2 4 coins 4
    let uPoly := polyAdd (polyInvNtt (vecDotNtt 4 (aTrans.getD row #[]) rHat))
      (e1Vec.getD row zeroPoly)
    PolyBounded16 1664 (uVecPoly06 rho coins row) ∧
    PolyRepresents (uVecPoly06 rho coins row) uPoly := by
  dsimp only
  unfold uVecPoly06
  have hd_sz : (neonDot4
      (aTransPoly06 rho row 0) (aTransPoly06 rho row 1)
      (aTransPoly06 rho row 2) (aTransPoly06 rho row 3)
      (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [3#8])))).size = 256 :=
    neonDot4_size _ _ _ _ _ _ _ _
  dsimp only [neonDot4,
    LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure.neonDot3] at hd_sz ⊢
  have htc : coins.take 32 = coins := List.take_of_length_le (Nat.le_of_eq hcoins)
  have hsh (d : BitVec 8) : (shake256List 128 (coins ++ [d])).length = 128 :=
    shake256List_length 128 (coins ++ [d])
  obtain ⟨ha0_b, ha0_r⟩ := aTransPoly06_spec rho row 0
  obtain ⟨ha1_b, ha1_r⟩ := aTransPoly06_spec rho row 1
  obtain ⟨ha2_b, ha2_r⟩ := aTransPoly06_spec rho row 2
  obtain ⟨ha3_b, ha3_r⟩ := aTransPoly06_spec rho row 3
  rw [← sampleMatrixWith_false_getD4 rho hrow (by decide : 0 < 4)] at ha0_r
  rw [← sampleMatrixWith_false_getD4 rho hrow (by decide : 1 < 4)] at ha1_r
  rw [← sampleMatrixWith_false_getD4 rho hrow (by decide : 2 < 4)] at ha2_r
  rw [← sampleMatrixWith_false_getD4 rho hrow (by decide : 3 < 4)] at ha3_r
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
  rw [← (rfl : BitVec.ofNat 8 0 = 0#8), ← hrg 0 (by decide)] at hr0_r
  rw [← (rfl : BitVec.ofNat 8 1 = 1#8), ← hrg 1 (by decide)] at hr1_r
  rw [← (rfl : BitVec.ofNat 8 2 = 2#8), ← hrg 2 (by decide)] at hr2_r
  rw [← (rfl : BitVec.ofNat 8 3 = 3#8), ← hrg 3 (by decide)] at hr3_r
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
  rw [seg7AddPoly_eq_barrett hd_sz]
  exact neonBarrettReducePoly16_spec hadd_r

end PureUVec

/-! ## 2. Setup (`seg7_init`), `montgomery(1441) + e1` Loop (`seg7_add_ok`) & Outer Tail -/

attribute [local irreducible]
  blkPC06 dup8x16 polyVecNat simdAdd8h simdSub8h simdMul8h simdSqdmulh8h simdSshr8h simdMla8h

private theorem seg7_init [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s : State) (sp : BitVec 64) (P : SepProp)
    (hpc : s.pc = b + offSeg7Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 30448#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offDotStart) s P
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x1 = 20159#64 ∧
        s'.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x4 = sp + 4160#64 ∧
        s'.readReg64 .x8 = 0#64 ∧
        s'.readReg64 .x10 = sp + 30464#64 ∧
        s'.readReg64 .x11 = sp + 28368#64 ∧
        s'.readReg64 .x12 = 16#64 ∧
        s'.readReg64 .x13 = 0#64 ∧
        s'.readReg64 .x15 = sp + 26320#64 ∧
        s'.readReg64 .x16 = 62209#64 ∧
        s'.readReg64 .x17 = 3329#64 ∧
        s'.readReg64 .x18 = sp + 14432#64 ∧
        s'.readReg64 .x19 = sp + 12352#64 ∧
        s'.readReg64 .x20 = sp + 30448#64 ∧
        s'.readReg64 .x25 = 64778#64 ∧
        s'.readReg64 .x26 = 31498#64 ∧
        s'.readReg64 .x27 = 1441#64 ∧
        s'.readReg64 .x28 = 55457#64 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 0#5 = 0#128 ∧
        s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧
        s'.readVReg128 27#5 = dup8x16 1024#16 ∧
        P' = P) := by
  have _ : b = blkPl06.base := hb
  wp_steps
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp, by simp, by simp, by simp,
      by simp,
      by simp,
      by simp, by simp,
      by simp,
      by simp, by simp,
      by simp,
      by simp,
      by simp [hx20], by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, rfl⟩
private structure Seg7AddPreserved (s0 s : State) : Prop where
  x1  : s.readReg64 .x1  = s0.readReg64 .x1
  x2  : s.readReg64 .x2  = s0.readReg64 .x2
  x4  : s.readReg64 .x4  = s0.readReg64 .x4
  x8  : s.readReg64 .x8  = s0.readReg64 .x8
  x10 : s.readReg64 .x10 = s0.readReg64 .x10
  x11 : s.readReg64 .x11 = s0.readReg64 .x11
  x12 : s.readReg64 .x12 = s0.readReg64 .x12
  x13 : s.readReg64 .x13 = s0.readReg64 .x13
  x15 : s.readReg64 .x15 = s0.readReg64 .x15
  x16 : s.readReg64 .x16 = s0.readReg64 .x16
  x17 : s.readReg64 .x17 = s0.readReg64 .x17
  x18 : s.readReg64 .x18 = s0.readReg64 .x18
  x19 : s.readReg64 .x19 = s0.readReg64 .x19
  x20 : s.readReg64 .x20 = s0.readReg64 .x20
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28
  fp  : s.readReg64 .fp  = s0.readReg64 .fp
  v0  : s.readVReg128 0#5  = s0.readVReg128 0#5
  v23 : s.readVReg128 23#5 = s0.readVReg128 23#5
  v27 : s.readVReg128 27#5 = s0.readVReg128 27#5

set_option maxRecDepth 100000 in
private theorem seg7_add_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp polyPtr e1Ptr : BitVec 64) {r : Nat} (hr : r < 16)
    (inv e1 : Poly16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offAddStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 (32 * r))
    (hx9 : s.readReg64 .x9 = polyPtr + 16#64) (hx11 : s.readReg64 .x11 = e1Ptr)
    (hx27 : s.readReg64 .x27 = 1441#64) (hx28 : s.readReg64 .x28 = 55457#64)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hpres : Seg7AddPreserved s0 s)
    (hf0 : f (2 * r) = polyVecNat inv (2 * r))
    (hf1 : f (2 * r + 1) = polyVecNat inv (2 * r + 1)) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + offAddStart else b + offAddTail) s
      (PolyMem polyPtr f ∗ PolyMem e1Ptr (polyVecNat e1) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x3 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x9 = polyPtr + 16#64 ∧ s'.readReg64 .x11 = e1Ptr ∧
        s'.readReg64 .x27 = 1441#64 ∧ s'.readReg64 .x28 = 55457#64 ∧
        s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
        s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧ s'.readVReg128 27#5 = dup8x16 1024#16 ∧
        Seg7AddPreserved s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update
            (Function.update f (2 * r + 1) (polyVecNat (seg7AddPoly inv e1) (2 * r + 1)))
            (2 * r) (polyVecNat (seg7AddPoly inv e1) (2 * r))) ∗
          PolyMem e1Ptr (polyVecNat e1) ∗ Rest)) := by
  have _ : b = blkPl06.base := hb
  rcases hpres with ⟨p1, p2, p4, p8, p10, p11, p12, p13, p15, p16, p17,
    p18, p19, p20, p25, p26, p27, p28, pfp, pv0, pv23, pv27⟩
  wp_steps 2
  refine step_ldrQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1))) (v := polyVecNat inv (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx9, hx3]; clear * - hr; bv_omega)
    (hf1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r))) (v := polyVecNat inv (2 * r))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega)
    (hf0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 14
  refine step_ldpQ128 (wb := none)
    (ea := e1Ptr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := e1Ptr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat e1 (2 * r)) (v2 := polyVecNat e1 (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 10
  have hv2_eq : _ = polyVecNat (seg7AddPoly inv e1) (2 * r + 1) := seg5Add_vec_eq inv e1 (2 * r + 1) (by omega)
  have hv1_eq : _ = polyVecNat (seg7AddPoly inv e1) (2 * r) := seg5Add_vec_eq inv e1 (2 * r) (by omega)
  refine step_strQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (val := polyVecNat (seg7AddPoly inv e1) (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx9, hx3]; clear * - hr; bv_omega)
    (by simp [← hv2_eq])
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m1; wp_steps 2
  refine step_strQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (val := polyVecNat (seg7AddPoly inv e1) (2 * r))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega)
    (by simp [← hv1_eq])
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m2; wp_step; wp_if hne
  · have hr15 : r < 15 := by
      by_contra hge; have hr_eq : r = 15 := by omega
      subst hr_eq; simp at hne
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * - hr15; bv_omega, by simp [hx9], by simp [hx11],
        by simp [hx27], by simp [hx28],
        by simp [hv16], by simp [hv17], by simp [hv23], by simp [hv27],
        ⟨by simp [p1], by simp [p2], by simp [p4], by simp [p8], by simp [p10], by simp [p11],
          by simp [p12], by simp [p13], by simp [p15], by simp [p16], by simp [p17], by simp [p18],
          by simp [p19], by simp [p20], by simp [p25], by simp [p26], by simp [p27], by simp [p28],
          by simp [pfp], by simp [pv0], by simp [pv23], by simp [pv27]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by intro hlt; clear * - hne hr hlt; bv_omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hr_eq], by simp [hx9], by simp [hx11],
        by simp [hx27], by simp [hx28],
        by simp [hv16], by simp [hv17], by simp [hv23], by simp [hv27],
        ⟨by simp [p1], by simp [p2], by simp [p4], by simp [p8], by simp [p10], by simp [p11],
          by simp [p12], by simp [p13], by simp [p15], by simp [p16], by simp [p17], by simp [p18],
          by simp [p19], by simp [p20], by simp [p25], by simp [p26], by simp [p27], by simp [p28],
          by simp [pfp], by simp [pv0], by simp [pv23], by simp [pv27]⟩, rfl⟩
private theorem seg7_add_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 : State) (sp polyPtr e1Ptr : BitVec 64) (inv e1 : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offAddStart → s.status = .Running →
      s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x3 = BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x9 = polyPtr + 16#64 → s.readReg64 .x11 = e1Ptr →
      s.readReg64 .x27 = 1441#64 → s.readReg64 .x28 = 55457#64 →
      s.readVReg128 16#5 = dup8x16 3329#16 → s.readVReg128 17#5 = dup8x16 20159#16 →
      s.readVReg128 23#5 = dup8x16 0xf2ff#16 → s.readVReg128 27#5 = dup8x16 1024#16 →
      Seg7AddPreserved s0 s →
      (∀ idx, idx < 2 * r → f idx = polyVecNat (seg7AddPoly inv e1) idx) →
      (∀ idx, 2 * r ≤ idx → idx < 32 → f idx = polyVecNat inv idx) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + offAddTail) s
        (PolyMem polyPtr f ∗ PolyMem e1Ptr (polyVecNat e1) ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
          s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧ s'.readVReg128 27#5 = dup8x16 1024#16 ∧
          Seg7AddPreserved s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat (seg7AddPoly inv e1)) ∗
            PolyMem e1Ptr (polyVecNat e1) ∗ Rest)) := by
  intro rem
  induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _ _ hx3 hx9 hx11 hx27 hx28 hv16 hv17 hv23 hv27 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hstep := seg7_add_iter hb s0 s sp polyPtr e1Ptr (r := 15) (by omega) inv e1 f Rest
      hpc hrun hsp hspA hx3 hx9 hx11 hx27 hx28 hv16 hv17 hv23 hv27 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    simp only [Nat.lt_irrefl, ↓reduceIte] at hstep
    refine SepWP.mono hstep ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, hv16', hv17', hv23', hv27', hpres', rfl⟩
    refine ⟨hsp', hspA', hv16', hv17', hv23', hv27', hpres', ?_⟩
    have hmem : PolyMem polyPtr
        (Function.update
          (Function.update f 31 (polyVecNat (seg7AddPoly inv e1) 31))
          30 (polyVecNat (seg7AddPoly inv e1) 30)) =
        PolyMem polyPtr (polyVecNat (seg7AddPoly inv e1)) := by
      apply vecRangeMem_congr; intro idx hidx
      by_cases h30 : idx = 30
      · subst h30; simp
      · by_cases h31 : idx = 31
        · subst h31; simp
        · simp [Function.update_of_ne h30, Function.update_of_ne h31, hlo idx (by omega)]
    rw [hmem]
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx3 hx9 hx11 hx27 hx28 hv16 hv17 hv23 hv27 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hstep := seg7_add_iter hb s0 s sp polyPtr e1Ptr (r := r) (by omega) inv e1 f Rest
      hpc hrun hsp hspA hx3 hx9 hx11 hx27 hx28 hv16 hv17 hv23 hv27 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr15, ↓reduceIte] at hstep
    refine sepWP_seq_env hcl hro hstep ?_
    rintro s1 P1 hpc1 hrun1 hcl1 hro1
      ⟨hsp1, hspA1, hx3_1, hx9_1, hx11_1, hx27_1, hx28_1, hv16_1, hv17_1, hv23_1, hv27_1, hpres1, rfl⟩
    refine ih (r + 1) (by omega) s1 _ hpc1 hrun1 hsp1 hspA1 hcl1 hro1
      hx3_1 hx9_1 hx11_1 hx27_1 hx28_1 hv16_1 hv17_1 hv23_1 hv27_1 hpres1 ?_ ?_
    · intro idx hidx
      by_cases h0 : idx = 2 * r
      · subst h0; simp
      · by_cases h1 : idx = 2 * r + 1
        · subst h1; simp
        · simp [Function.update_of_ne h0, Function.update_of_ne h1, hlo idx (by omega)]
    · intro idx hge hlt
      simp [Function.update_of_ne (show idx ≠ 2 * r by omega),
        Function.update_of_ne (show idx ≠ 2 * r + 1 by omega), hhi idx (by omega) hlt]
private theorem seg7_add_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp polyPtr e1Ptr : BitVec 64) (inv e1 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offAddStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx3 : s.readReg64 .x3 = 0#64) (hx9 : s.readReg64 .x9 = polyPtr + 16#64)
    (hx11 : s.readReg64 .x11 = e1Ptr)
    (hx27 : s.readReg64 .x27 = 1441#64) (hx28 : s.readReg64 .x28 = 55457#64)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16) (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16) (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hpres : Seg7AddPreserved s0 s) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offAddTail) s
      (PolyMem polyPtr (polyVecNat inv) ∗ PolyMem e1Ptr (polyVecNat e1) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ Seg7AddPreserved s0 s' ∧
        P' = (PolyMem polyPtr (polyVecNat (seg7AddPoly inv e1)) ∗
          PolyMem e1Ptr (polyVecNat e1) ∗ Rest)) := by
  refine SepWP.mono (seg7_add_loop hb s0 sp polyPtr e1Ptr inv e1 Rest 15 0 rfl s (polyVecNat inv)
    hpc hrun hsp hspA hcl hro hx3 hx9 hx11 hx27 hx28 hv16 hv17 hv23 hv27 hpres
    (fun _ h => by omega) (fun _ _ _ => rfl)) ?_
  rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, hpres', hP'⟩
  exact ⟨hsp', hspA', hpres', hP'⟩

private theorem seg7_outer_tail [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s : State) {i : Nat} (hi : i < 4) (P : SepProp)
    (hpc : s.pc = b + offAddTail) (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (2048 * (i + 1))) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if i < 3 then b + offDotStart else b + offSeg7Mid) s P
      (fun s' P' =>
        s'.sp = s.sp ∧ s'.spAligned = s.spAligned ∧ s'.vregs = s.vregs ∧
        s'.readReg64 .x4 = s.readReg64 .x4 + 2048#64 ∧
        s'.readReg64 .x10 = s.readReg64 .x10 + 512#64 ∧
        s'.readReg64 .x11 = s.readReg64 .x11 + 512#64 ∧
        s'.readReg64 .x12 = s.readReg64 .x12 + 512#64 ∧
        (∀ r : BitVec 5, r ≠ 4#5 → r ≠ 10#5 → r ≠ 11#5 → r ≠ 12#5 → r ≠ 31#5 →
          s'.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        P' = P) := by
  have _ : b = blkPl06.base := hb
  wp_steps 5; wp_step; wp_if hne
  · have hi3 : i < 3 := by
      by_contra hge; have hi_eq : i = 3 := by omega
      subst hi_eq; simp at hne
    simp only [hi3, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨rfl, rfl, rfl, by simp, by simp, by simp, by simp,
        fun r h4 h10 h11 h12 h31 => by simp [h4, h10, h11, h12, h31], rfl⟩
  · have hi3 : ¬ i < 3 := by
      intro hlt; rcases i with _ | _ | _ | i
      · simp at hne
      · simp at hne
      · simp at hne
      · omega
    simp only [hi3, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨rfl, rfl, rfl, by simp, by simp, by simp, by simp,
        fun r h4 h10 h11 h12 h31 => by simp [h4, h10, h11, h12, h31], rfl⟩

/-! ## 3. Symbolic Upper `InvNTT` Step (`+0x9858 → +0xaf20`) -/

private theorem noReloc_seg7_inv : blk06NoRelocInRange 9750 11208 = true := by decide +kernel

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
    (hv18 : s.readVReg128 18#5 = dup8x16 62209#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hx25 : s.readReg64 .x25 = 64778#64) (hx26 : s.readReg64 .x26 = 31498#64)
    (hx27 : s.readReg64 .x27 = 1441#64) (hx28 : s.readReg64 .x28 = 55457#64) :
    SymStateMatches sp (mkInvEnv s t p2) symSeg7InvSymInit s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 16 => simpa [symSeg7InvSymInit, SymVRegs.get, evalSExpr] using hv16
    | 17 => simpa [symSeg7InvSymInit, SymVRegs.get, evalSExpr] using hv17
    | 18 => simpa [symSeg7InvSymInit, SymVRegs.get, evalSExpr] using hv18
    | 23 => simpa [symSeg7InvSymInit, SymVRegs.get, evalSExpr] using hv23
    | 27 => simpa [symSeg7InvSymInit, SymVRegs.get, evalSExpr] using hv27
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 19 | 20 | 21 | 22 | 24 | 25 | 26 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 25 => exact hx25
    | 26 => exact hx26
    | 27 => exact hx27
    | 28 => exact hx28
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 29 | 30 =>
      simp [symSeg7InvSymInit, SymGprs.get, evalSymGpr, mkInvEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem spillSlice27_invInit (sp : BitVec 64) (t : Spill40)
    (env : SymEnv) (hsp0 : env.spill0 = t) :
    SpillSliceMem 27 (sp + 2000#64) (symSeg7InvSymInit.spill.eval env) =
      SpillSliceMem 27 (sp + 2000#64) t :=
  vecRangeMem_congr fun i hi => by
    rw [symSpill40_eval_get env symSeg7InvSymInit.spill i (by omega)]
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13
    | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 =>
      simp [symSeg7InvSymInit, SymSpill40.get, evalSExpr, hsp0]
    | _ + 27 => omega

private theorem poly_invInit (ptr : BitVec 64) (p2 : Poly16)
    (env : SymEnv) (hp0 : env.poly0 = Vec32.ofFn (polyVecNat p2)) :
    Poly32Mem ptr (symSeg7InvSymInit.poly.eval env) = PolyMem ptr (polyVecNat p2) := by
  rw [← poly32Mem_ofFn ptr (polyVecNat p2), ← hp0]
  exact vecRangeMem_congr fun i hi => by
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
private theorem symSeg7InvEnd_vregs (env : SymEnv) :
    evalSExpr env (symSeg7InvSymEnd.vregs.get 0) = env.vreg0 0 ∧
    evalSExpr env (symSeg7InvSymEnd.vregs.get 16) = dup8x16 3329#16 ∧
    evalSExpr env (symSeg7InvSymEnd.vregs.get 17) = dup8x16 20159#16 ∧
    evalSExpr env (symSeg7InvSymEnd.vregs.get 23) = dup8x16 0xf2ff#16 ∧
    evalSExpr env (symSeg7InvSymEnd.vregs.get 27) = dup8x16 1024#16 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem symSeg7InvEnd_gprs :
    symSeg7InvSymEnd.gprs.get 1 = .gpr0 1#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 2 = .gpr0 2#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 3 = .const64 0#64 ∧
    symSeg7InvSymEnd.gprs.get 4 = .gpr0 4#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 8 = .gpr0 8#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 9 = .addGpr0 20#5 12#5 ∧
    symSeg7InvSymEnd.gprs.get 10 = .gpr0 10#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 11 = .gpr0 11#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 12 = .gpr0 12#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 13 = .gpr0 13#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 15 = .gpr0 15#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 16 = .gpr0 16#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 17 = .gpr0 17#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 18 = .gpr0 18#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 19 = .gpr0 19#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 20 = .gpr0 20#5 0#64 ∧
    symSeg7InvSymEnd.gprs.get 25 = .const64 64778#64 ∧
    symSeg7InvSymEnd.gprs.get 26 = .const64 31498#64 ∧
    symSeg7InvSymEnd.gprs.get 27 = .const64 1441#64 ∧
    symSeg7InvSymEnd.gprs.get 28 = .const64 55457#64 ∧
    symSeg7InvSymEnd.gprs.get 29 = .gpr0 29#5 0#64 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl⟩
private theorem seg7_inv_upper_ok [MlKemPlacement] {b : BitVec 64}
    (s : State) (sp polyPtrVal : BitVec 64) {dot : Poly16} (hdot : dot.size = 256)
    (t : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + offInvLowEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = 64778#64) (hx26 : s.readReg64 .x26 = 31498#64)
    (hx27 : s.readReg64 .x27 = 1441#64) (hx28 : s.readReg64 .x28 = 55457#64)
    (hlr : s.readReg64 .lr = polyPtrVal)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv18 : s.readVReg128 18#5 = dup8x16 62209#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offAddStart) s
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
        Seg7AddPreserved s sf ∧
        ∃ t' : Spill40, Pf ⊢ SpillSliceMem 27 (sp + 2000#64) t' ∗
          PolyMem polyPtrVal (polyVecNat (neonInvNttMontgomery16 dot)) ∗ Rest) := by
  set p2 := lowerInvNtt16 dot
  set env := mkInvEnv s t p2
  have hp2 : p2.size = 256 := lowerInvNtt16_size hdot
  have hP_sym : SpillSliceMem 27 (sp + 2000#64) t ∗ PolyMem polyPtrVal (polyVecNat p2) ∗ Rest ⊢
      SymSpatial cfgSeg7InvSym sp env symSeg7InvSymInit Rest := by
    dsimp only [SymSpatial, cfgSeg7InvSym, polyPtr, SrcOptMem]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [spillSlice27_invInit sp t env rfl, show env.gpr0 30#5 = polyPtrVal from hlr,
      poly_invInit polyPtrVal p2 env rfl]
    sep_frame
  refine SepWP.weaken_pre hP_sym (sepWP_of_runSymRange (cfg := cfgSeg7InvSym)
    (env := env) (F := Rest) 1458 9750 noReloc_seg7_inv (by decide) (by decide) (by decide)
    run_seg7_inv1 (matches_invInit t p2 hsp hspA hv16 hv17 hv18 hv23 hv27 hx25 hx26 hx27 hx28)
    hpc hrun ?_)
  intro sf _ _ hm
  rcases symSeg7InvEnd_gprs with ⟨g1, g2, g3, g4, g8, g9, g10, g11, g12, g13, g15, g16, g17,
    g18, g19, g20, g25, g26, g27, g28, g29⟩
  rcases symSeg7InvEnd_vregs env with ⟨vr0, vr16, vr17, vr23, vr27⟩
  have geq (r : Nat) (hr : BitVec.ofNat 5 r ≠ 31#5) (hlt : r < 32) :
      sf.readReg64 (.gpr (BitVec.ofNat 5 r)) = evalSymGpr sp env.gpr0 (symSeg7InvSymEnd.gprs.get r) :=
    by simpa [Nat.mod_eq_of_lt hlt] using hm.hgprs (BitVec.ofNat 5 r) hr
  have veq (r : Nat) (hlt : r < 32) :
      sf.readVReg128 (BitVec.ofNat 5 r) = evalSExpr env (symSeg7InvSymEnd.vregs.get r) :=
    by simpa [Nat.mod_eq_of_lt hlt] using hm.hvregs (BitVec.ofNat 5 r)
  have hPf : SymSpatial cfgSeg7InvSym sp env symSeg7InvSymEnd Rest ⊢
      SpillSliceMem 27 (sp + 2000#64) (symSeg7InvSymEnd.spill.eval env) ∗
        PolyMem polyPtrVal (polyVecNat (neonInvNttMontgomery16 dot)) ∗ Rest := by
    dsimp only [SymSpatial, cfgSeg7InvSym, polyPtr, SrcOptMem]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show env.gpr0 30#5 = polyPtrVal from hlr,
      poly_eq_upperInvNtt16 polyPtrVal hp2 env rfl symSeg7InvSymEnd.poly
        seg7_inv_noSpillVreg seg7_inv_ast_eq,
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
     by have h := geq 27 (by decide) (by decide); rw [g27] at h; exact h.trans hx27.symm,
     by have h := geq 28 (by decide) (by decide); rw [g28] at h; exact h.trans hx28.symm,
     by have h := geq 29 (by decide) (by decide); rw [g29] at h; simpa [evalSymGpr, env, mkInvEnv] using h,
     by have h := veq 0 (by decide); rw [vr0] at h; exact h,
     by have h := veq 23 (by decide); rw [vr23] at h; exact h.trans hv23.symm,
     by have h := veq 27 (by decide); rw [vr27] at h; exact h.trans hv27.symm⟩,
    symSeg7InvSymEnd.spill.eval env, hPf⟩

/-! ## 4. Single-Row Composition (`seg7_row_ok`) & Full 4-Row `seg7_uvec_ok` (`+0x9380 → +0xafc0`) -/

private structure Seg7LoopRegs [MlKemPlacement] (sp fpVal : BitVec 64) (row : Nat) (s : State) : Prop where
  x1  : s.readReg64 .x1  = 20159#64
  x2  : s.readReg64 .x2  = mlkemMpl.ρ ro00Sym + 134#64
  x4  : s.readReg64 .x4  = sp + BitVec.ofNat 64 (4160 + 2048 * row)
  x8  : s.readReg64 .x8  = BitVec.ofNat 64 (2048 * row)
  x10 : s.readReg64 .x10 = sp + 30448#64 + BitVec.ofNat 64 (512 * row) + 16#64
  x11 : s.readReg64 .x11 = sp + 28368#64 + BitVec.ofNat 64 (512 * row)
  x12 : s.readReg64 .x12 = 16#64 + BitVec.ofNat 64 (512 * row)
  x13 : s.readReg64 .x13 = BitVec.ofNat 64 row
  x15 : s.readReg64 .x15 = sp + 26320#64
  x16 : s.readReg64 .x16 = 62209#64
  x17 : s.readReg64 .x17 = 3329#64
  x18 : s.readReg64 .x18 = sp + 14432#64
  x19 : s.readReg64 .x19 = sp + 12352#64
  x20 : s.readReg64 .x20 = sp + 30448#64
  x25 : s.readReg64 .x25 = 64778#64
  x26 : s.readReg64 .x26 = 31498#64
  x27 : s.readReg64 .x27 = 1441#64
  x28 : s.readReg64 .x28 = 55457#64
  fp  : s.readReg64 .fp  = fpVal
  v0  : s.readVReg128 0#5  = 0#128
  v23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16
  v27 : s.readVReg128 27#5 = dup8x16 1024#16

private theorem aTransRowAt_4160_eq (sp : BitVec 64) (rho : List (BitVec 8)) {row : Nat}
    (hrow : row < 4) :
    ATransRowAt (sp + 4160#64) rho row =
      (PolyMem (sp + BitVec.ofNat 64 (4160 + 2048 * row)) (polyVecNat (aTransPoly06 rho row 0)) ∗
       PolyMem (sp + BitVec.ofNat 64 (4160 + 2048 * row) + 512#64) (polyVecNat (aTransPoly06 rho row 1)) ∗
       PolyMem (sp + BitVec.ofNat 64 (4160 + 2048 * row) + 1024#64) (polyVecNat (aTransPoly06 rho row 2)) ∗
       PolyMem (sp + BitVec.ofNat 64 (4160 + 2048 * row) + 1536#64) (polyVecNat (aTransPoly06 rho row 3))) := by
  have _ := hrow
  dsimp only [ATransRowAt]
  have h0 : (sp + 4160#64) + BitVec.ofNat 64 (2048 * row) =
      sp + BitVec.ofNat 64 (4160 + 2048 * row) := by clear * - hrow; bv_omega
  have h1 : (sp + 4160#64) + BitVec.ofNat 64 (2048 * row + 512) =
      sp + BitVec.ofNat 64 (4160 + 2048 * row) + 512#64 := by clear * - hrow; bv_omega
  have h2 : (sp + 4160#64) + BitVec.ofNat 64 (2048 * row + 1024) =
      sp + BitVec.ofNat 64 (4160 + 2048 * row) + 1024#64 := by clear * - hrow; bv_omega
  have h3 : (sp + 4160#64) + BitVec.ofNat 64 (2048 * row + 1536) =
      sp + BitVec.ofNat 64 (4160 + 2048 * row) + 1536#64 := by clear * - hrow; bv_omega
  rw [h0, h1, h2, h3]
private theorem seg7_row_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s : State) (sp fpVal : BitVec 64) (rho coins : List (BitVec 8)) {row : Nat} (hrow : row < 4)
    (t : Spill40) (v14432 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offDotStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hregs : Seg7LoopRegs sp fpVal row s) :
    let uPtr := sp + 30448#64 + BitVec.ofNat 64 (512 * row)
    let e1Ptr := sp + 28368#64 + BitVec.ofNat 64 (512 * row)
    let e1 := neonCbd2Poly16 (shake256List 128 (coins ++ [BitVec.ofNat 8 (4 + row)]))
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
    SepWP (blkPC06.rebase b (fun _ => none))
      (if row < 3 then b + offDotStart else b + offSeg7Mid) s
      (PolyMem uPtr (fun _ => 0#128) ∗ ATransRowAt (sp + 4160#64) rho row ∗
        PolyMem (sp + 26320#64) (polyVecNat r0) ∗
        PolyMem (sp + 26832#64) (polyVecNat r1) ∗
        PolyMem (sp + 27344#64) (polyVecNat r2) ∗
        PolyMem (sp + 27856#64) (polyVecNat r3) ∗
        PolyMem e1Ptr (polyVecNat e1) ∗
        SpillSliceMem 27 (sp + 2000#64) t ∗
        Poly32Mem (sp + 14432#64) v14432 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg7LoopRegs sp fpVal (row + 1) sf ∧
        ∃ (t' : Spill40) (v14432' : Vec32),
          Pf ⊢ PolyMem uPtr (polyVecNat (uVecPoly06 rho coins row)) ∗
            ATransRowAt (sp + 4160#64) rho row ∗
            PolyMem (sp + 26320#64) (polyVecNat r0) ∗
            PolyMem (sp + 26832#64) (polyVecNat r1) ∗
            PolyMem (sp + 27344#64) (polyVecNat r2) ∗
            PolyMem (sp + 27856#64) (polyVecNat r3) ∗
            PolyMem e1Ptr (polyVecNat e1) ∗
            SpillSliceMem 27 (sp + 2000#64) t' ∗
            Poly32Mem (sp + 14432#64) v14432' ∗ Rest) := by
  intro uPtr e1Ptr e1 r0 r1 r2 r3
  set lhsBase := sp + BitVec.ofNat 64 (4160 + 2048 * row)
  have hr1 : sp + 26320#64 + 512#64 = sp + 26832#64 := by clear * -; bv_omega
  have hr2 : sp + 26320#64 + 1024#64 = sp + 27344#64 := by clear * -; bv_omega
  have hr3 : sp + 26320#64 + 1536#64 = sp + 27856#64 := by clear * -; bv_omega
  have hP0 : PolyMem uPtr (fun _ => 0#128) ∗ ATransRowAt (sp + 4160#64) rho row ∗
      PolyMem (sp + 26320#64) (polyVecNat r0) ∗ PolyMem (sp + 26832#64) (polyVecNat r1) ∗
      PolyMem (sp + 27344#64) (polyVecNat r2) ∗ PolyMem (sp + 27856#64) (polyVecNat r3) ∗
      PolyMem e1Ptr (polyVecNat e1) ∗
      SpillSliceMem 27 (sp + 2000#64) t ∗ Poly32Mem (sp + 14432#64) v14432 ∗ Rest ⊢
      PolyMem uPtr (fun _ => 0#128) ∗
      PolyMem lhsBase (polyVecNat (aTransPoly06 rho row 0)) ∗
      PolyMem (lhsBase + 512#64) (polyVecNat (aTransPoly06 rho row 1)) ∗
      PolyMem (lhsBase + 1024#64) (polyVecNat (aTransPoly06 rho row 2)) ∗
      PolyMem (lhsBase + 1536#64) (polyVecNat (aTransPoly06 rho row 3)) ∗
      PolyMem (sp + 26320#64) (polyVecNat r0) ∗
      PolyMem (sp + 26320#64 + 512#64) (polyVecNat r1) ∗
      PolyMem (sp + 26320#64 + 1024#64) (polyVecNat r2) ∗
      PolyMem (sp + 26320#64 + 1536#64) (polyVecNat r3) ∗
      Poly32Mem (sp + 14432#64) v14432 ∗
      (PolyMem e1Ptr (polyVecNat e1) ∗ SpillSliceMem 27 (sp + 2000#64) t ∗ Rest) := by
    rw [aTransRowAt_4160_eq sp rho hrow, hr1, hr2, hr3]; sep_frame
  refine SepWP.weaken_pre hP0 (sepWP_seq_env hcl hro
    (seg7_dot_ok hb s s sp (sp + 30448#64) lhsBase (sp + 26320#64) hrow
      (aTransPoly06 rho row 0) (aTransPoly06 rho row 1)
      (aTransPoly06 rho row 2) (aTransPoly06 rho row 3) r0 r1 r2 r3 v14432 _
      hpc hrun hsp hspA hcl hro hregs.x2 hregs.x4 hregs.x8 hregs.x13 hregs.x15 hregs.x16
      hregs.x17 hregs.x18 hregs.x20 hregs.v0
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
       rfl, rfl, rfl⟩) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx2_1, hx8_1, hx13_1, hx15_1, hx16_1, hx17_1, hx18_1, hlr_1,
      hv0_1, hv16_1, hv18_1, hd1, rfl⟩
  set dot := neonDot4 (aTransPoly06 rho row 0) (aTransPoly06 rho row 1)
    (aTransPoly06 rho row 2) (aTransPoly06 rho row 3) r0 r1 r2 r3
  have hdot : dot.size = 256 := neonDot4_size _ _ _ _ _ _ _ _
  have hbase12 : (sp + 30448#64) + (16#64 + BitVec.ofNat 64 (512 * row)) = uPtr + 16#64 := by
    dsimp only [uPtr]; clear * -; bv_omega
  refine sepWP_seq_env hcl1 hro1
    (seg7_inv_low_ok hb s1 sp uPtr (sp + 30448#64) (16#64 + BitVec.ofNat 64 (512 * row))
      hbase12 hdot _ hpc1 hrun1 hsp1 hspA1 hcl1 hro1
      (hd1.x1.trans hregs.x1) (hd1.x10.trans hregs.x10) (hd1.x12.trans hregs.x12)
      (hd1.x20.trans hregs.x20) hv16_1 hv18_1 (hd1.v23.trans hregs.v23)
      (hd1.v27.trans hregs.v27)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hv16_2, hv17_2, hv18_2, hv23_2, hv27_2, hl2, rfl⟩
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl2 hro2
      (seg7_inv_upper_ok s2 sp uPtr hdot t _ hpc2 hrun2 hsp2 hspA2
        (hl2.x25.trans (hd1.x25.trans hregs.x25)) (hl2.x26.trans (hd1.x26.trans hregs.x26))
        (hl2.x27.trans (hd1.x27.trans hregs.x27)) (hl2.x28.trans (hd1.x28.trans hregs.x28))
        (hl2.lr.trans hlr_1) hv16_2 hv17_2 hv18_2 hv23_2 hv27_2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx3_3, hx9_3, hv16_3, hv17_3, hv23_3, hv27_3, hu3, t', hP3⟩
  have hx9_u : s3.readReg64 .x9 = uPtr + 16#64 := by
    rw [hx9_3, hl2.x20.trans (hd1.x20.trans hregs.x20), hl2.x12.trans (hd1.x12.trans hregs.x12)]
    exact hbase12
  refine SepWP.weaken_pre (Entails.trans hP3 (by sep_frame))
    (sepWP_seq_env hcl3 hro3
      (seg7_add_ok hb s3 s3 sp uPtr e1Ptr (neonInvNttMontgomery16 dot) e1 _
        hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx3_3 hx9_u
        (hu3.x11.trans (hl2.x11.trans (hd1.x11.trans hregs.x11)))
        (hu3.x27.trans (hl2.x27.trans (hd1.x27.trans hregs.x27)))
        (hu3.x28.trans (hl2.x28.trans (hd1.x28.trans hregs.x28)))
        hv16_3 hv17_3 hv23_3 hv27_3
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, rfl, rfl⟩) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, ha4, rfl⟩
  have hx8_4 : s4.readReg64 .x8 = BitVec.ofNat 64 (2048 * (row + 1)) :=
    ha4.x8.trans (hu3.x8.trans (hl2.x8.trans hx8_1))
  refine sepWP_seq_env hcl4 hro4 (seg7_outer_tail hb s4 hrow _ hpc4 hrun4 hx8_4) ?_
  rintro sf Pf hpc_f hrun_f hcl_f hro_f ⟨hsp_f, hspA_f, hv_f, hx4_f, hx10_f, hx11_f, hx12_f, hg_f, rfl⟩
  have fv (r : BitVec 5) : sf.readVReg128 r = s4.readVReg128 r := by
    simp [State.readVReg128, hv_f]
  have fg (r : BitVec 5) (h4 : r ≠ 4#5) (h10 : r ≠ 10#5) (h11 : r ≠ 11#5)
      (h12 : r ≠ 12#5) (h31 : r ≠ 31#5) : sf.readReg64 (.gpr r) = s4.readReg64 (.gpr r) :=
    hg_f r h4 h10 h11 h12 h31
  refine SepWP.done hpc_f hrun_f ⟨hsp_f.trans hsp4, hspA_f.trans hspA4, hcl_f, hro_f,
    { x1  := (fg 1#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x1.trans (hu3.x1.trans (hl2.x1.trans (hd1.x1.trans hregs.x1))))
      x2  := (fg 2#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x2.trans (hu3.x2.trans (hl2.x2.trans hx2_1)))
      x4  := by
        rw [hx4_f, ha4.x4.trans (hu3.x4.trans (hl2.x4.trans (hd1.x4.trans hregs.x4)))]
        clear * - hrow; bv_omega
      x8  := (fg 8#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx8_4
      x10 := by
        rw [hx10_f, ha4.x10.trans (hu3.x10.trans (hl2.x10.trans (hd1.x10.trans hregs.x10)))]
        clear * - hrow; bv_omega
      x11 := by
        rw [hx11_f, ha4.x11.trans (hu3.x11.trans (hl2.x11.trans (hd1.x11.trans hregs.x11)))]
        clear * - hrow; bv_omega
      x12 := by
        rw [hx12_f, ha4.x12.trans (hu3.x12.trans (hl2.x12.trans (hd1.x12.trans hregs.x12)))]
        clear * - hrow; bv_omega
      x13 := (fg 13#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x13.trans (hu3.x13.trans (hl2.x13.trans hx13_1)))
      x15 := (fg 15#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x15.trans (hu3.x15.trans (hl2.x15.trans hx15_1)))
      x16 := (fg 16#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x16.trans (hu3.x16.trans (hl2.x16.trans hx16_1)))
      x17 := (fg 17#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x17.trans (hu3.x17.trans (hl2.x17.trans hx17_1)))
      x18 := (fg 18#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x18.trans (hu3.x18.trans (hl2.x18.trans hx18_1)))
      x19 := (fg 19#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x19.trans (hu3.x19.trans (hl2.x19.trans (hd1.x19.trans hregs.x19))))
      x20 := (fg 20#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x20.trans (hu3.x20.trans (hl2.x20.trans (hd1.x20.trans hregs.x20))))
      x25 := (fg 25#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x25.trans (hu3.x25.trans (hl2.x25.trans (hd1.x25.trans hregs.x25))))
      x26 := (fg 26#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x26.trans (hu3.x26.trans (hl2.x26.trans (hd1.x26.trans hregs.x26))))
      x27 := (fg 27#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x27.trans (hu3.x27.trans (hl2.x27.trans (hd1.x27.trans hregs.x27))))
      x28 := (fg 28#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.x28.trans (hu3.x28.trans (hl2.x28.trans (hd1.x28.trans hregs.x28))))
      fp  := (fg 29#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (ha4.fp.trans (hu3.fp.trans (hl2.fp.trans (hd1.fp.trans hregs.fp))))
      v0  := (fv 0#5).trans (ha4.v0.trans (hu3.v0.trans (hl2.v0.trans hv0_1)))
      v23 := (fv 23#5).trans (ha4.v23.trans hv23_3)
      v27 := (fv 27#5).trans (ha4.v27.trans hv27_3) },
    t', Vec32.ofFn (polyVecNat
      (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.neonPolyNttMul16
        (aTransPoly06 rho row 3) r3)), ?_⟩
  rw [aTransRowAt_4160_eq sp rho hrow, hr1, hr2, hr3]
  dsimp only [uVecPoly06, dot, e1, r0, r1, r2, r3]
  sep_frame

private theorem spillSlice27_ofFn (ptr : BitVec 64) (f : Nat → BitVec 128) :
    SpillSliceMem 27 ptr (Spill40.ofFn f) = VecRangeMem 27 ptr f :=
  vecRangeMem_congr fun i hi => spill40_ofFn_get f i (by omega)

private theorem spillSlice27_entails_memRegion (ptr : BitVec 64) (t : Spill40) :
    SpillSliceMem 27 ptr t ⊢ memRegion ptr 432 :=
  vecRangeMem_entails_memRegion 27 ptr t.get

/-- Full 4-row `u = InvNTT(Âᵀ ∘ r̂) + e₁` sub-segment (`+0x9380 → +0xafc0`). -/
theorem seg7_uvec_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s : State) (sp fpVal : BitVec 64) (rho coins : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 30448#64) (hfp : s.readReg64 .fp = fpVal)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
    let e1_0 := neonCbd2Poly16 (shake256List 128 (coins ++ [4#8]))
    let e1_1 := neonCbd2Poly16 (shake256List 128 (coins ++ [5#8]))
    let e1_2 := neonCbd2Poly16 (shake256List 128 (coins ++ [6#8]))
    let e1_3 := neonCbd2Poly16 (shake256List 128 (coins ++ [7#8]))
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg7Mid) s
      (memRegion (sp + 2000#64) 432 ∗ ATransAt (sp + 4160#64) rho ∗
        memRegion (sp + 14432#64) 512 ∗
        PolyMem (sp + 26320#64) (polyVecNat r0) ∗
        PolyMem (sp + 26832#64) (polyVecNat r1) ∗
        PolyMem (sp + 27344#64) (polyVecNat r2) ∗
        PolyMem (sp + 27856#64) (polyVecNat r3) ∗
        PolyMem (sp + 28368#64) (polyVecNat e1_0) ∗
        PolyMem (sp + 28880#64) (polyVecNat e1_1) ∗
        PolyMem (sp + 29392#64) (polyVecNat e1_2) ∗
        PolyMem (sp + 29904#64) (polyVecNat e1_3) ∗
        PolyMem (sp + 30448#64) (fun _ => 0#128) ∗
        PolyMem (sp + 30960#64) (fun _ => 0#128) ∗
        PolyMem (sp + 31472#64) (fun _ => 0#128) ∗
        PolyMem (sp + 31984#64) (fun _ => 0#128) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 12352#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ memRegion (sp + 2000#64) 432 ∗ ATransAt (sp + 4160#64) rho ∗
          memRegion (sp + 14432#64) 512 ∗
          PolyMem (sp + 26320#64) (polyVecNat r0) ∗
          PolyMem (sp + 26832#64) (polyVecNat r1) ∗
          PolyMem (sp + 27344#64) (polyVecNat r2) ∗
          PolyMem (sp + 27856#64) (polyVecNat r3) ∗
          PolyMem (sp + 28368#64) (polyVecNat e1_0) ∗
          PolyMem (sp + 28880#64) (polyVecNat e1_1) ∗
          PolyMem (sp + 29392#64) (polyVecNat e1_2) ∗
          PolyMem (sp + 29904#64) (polyVecNat e1_3) ∗
          PolyMem (sp + 30448#64) (polyVecNat (uVecPoly06 rho coins 0)) ∗
          PolyMem (sp + 30960#64) (polyVecNat (uVecPoly06 rho coins 1)) ∗
          PolyMem (sp + 31472#64) (polyVecNat (uVecPoly06 rho coins 2)) ∗
          PolyMem (sp + 31984#64) (polyVecNat (uVecPoly06 rho coins 3)) ∗ Rest)) := by
  intro r0 r1 r2 r3 e1_0 e1_1 e1_2 e1_3
  apply SepWP.of_memRegion_vecRangeMem 27 (sp + 2000#64); intro fSp
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 14432#64); intro fTmp
  have hp32 : VecRangeMem 32 (sp + 14432#64) fTmp =
      Poly32Mem (sp + 14432#64) (Vec32.ofFn fTmp) :=
    (poly32Mem_ofFn (sp + 14432#64) fTmp).symm
  rw [← spillSlice27_ofFn (sp + 2000#64) fSp, hp32]
  refine sepWP_seq_env hcl hro (seg7_init hb s sp _ hpc hrun hsp hspA hx20) ?_
  rintro s0 P0 hpc0 hrun0 hcl0 hro0
    ⟨hsp0, hspA0, rx1, rx2, rx4, rx8, rx10, rx11, rx12, rx13, rx15, rx16, rx17, rx18, rx19,
      rx20, rx25, rx26, rx27, rx28, rfp, rv0, rv23, rv27, rfl⟩
  have hregs0 : Seg7LoopRegs sp fpVal 0 s0 :=
    { x1 := rx1, x2 := rx2, x4 := rx4, x8 := rx8,
      x10 := by rw [rx10]; clear * -; bv_omega,
      x11 := by rw [rx11]; clear * -; bv_omega,
      x12 := rx12, x13 := rx13, x15 := rx15, x16 := rx16, x17 := rx17,
      x18 := rx18, x19 := rx19, x20 := rx20, x25 := rx25, x26 := rx26,
      x27 := rx27, x28 := rx28, fp := rfp.trans hfp, v0 := rv0, v23 := rv23, v27 := rv27 }
  have hu0 : sp + 30448#64 + BitVec.ofNat 64 (512 * 0) = sp + 30448#64 := by clear * -; bv_omega
  have hu1 : sp + 30448#64 + BitVec.ofNat 64 (512 * 1) = sp + 30960#64 := by clear * -; bv_omega
  have hu2 : sp + 30448#64 + BitVec.ofNat 64 (512 * 2) = sp + 31472#64 := by clear * -; bv_omega
  have hu3 : sp + 30448#64 + BitVec.ofNat 64 (512 * 3) = sp + 31984#64 := by clear * -; bv_omega
  have he0 : sp + 28368#64 + BitVec.ofNat 64 (512 * 0) = sp + 28368#64 := by clear * -; bv_omega
  have he1 : sp + 28368#64 + BitVec.ofNat 64 (512 * 1) = sp + 28880#64 := by clear * -; bv_omega
  have he2 : sp + 28368#64 + BitVec.ofNat 64 (512 * 2) = sp + 29392#64 := by clear * -; bv_omega
  have he3 : sp + 28368#64 + BitVec.ofNat 64 (512 * 3) = sp + 29904#64 := by clear * -; bv_omega
  have hb0 : BitVec.ofNat 8 (4 + 0) = 4#8 := rfl
  have hb1 : BitVec.ofNat 8 (4 + 1) = 5#8 := rfl
  have hb2 : BitVec.ofNat 8 (4 + 2) = 6#8 := rfl
  have hb3 : BitVec.ofNat 8 (4 + 3) = 7#8 := rfl
  have hrow0 := seg7_row_ok hb s0 sp fpVal rho coins (row := 0) (by decide)
    (Spill40.ofFn fSp) (Vec32.ofFn fTmp)
    (ATransRowAt (sp + 4160#64) rho 1 ∗ ATransRowAt (sp + 4160#64) rho 2 ∗
      ATransRowAt (sp + 4160#64) rho 3 ∗ PolyMem (sp + 28880#64) (polyVecNat e1_1) ∗
      PolyMem (sp + 29392#64) (polyVecNat e1_2) ∗ PolyMem (sp + 29904#64) (polyVecNat e1_3) ∗
      PolyMem (sp + 30960#64) (fun _ => 0#128) ∗ PolyMem (sp + 31472#64) (fun _ => 0#128) ∗
      PolyMem (sp + 31984#64) (fun _ => 0#128) ∗ Rest)
    hpc0 hrun0 hsp0 hspA0 hcl0 hro0 hregs0
  dsimp only at hrow0; simp only [show (0 : Nat) < 3 by decide, ↓reduceIte, hu0, he0, hb0] at hrow0
  refine SepWP.weaken_pre (by dsimp only [ATransAt]; sep_frame) (sepWP_seq_env hcl0 hro0 hrow0 ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hcl1', hro1', hregs1, t1, v1, hP1⟩
  have hrow1 := seg7_row_ok hb s1 sp fpVal rho coins (row := 1) (by decide) t1 v1
    (PolyMem (sp + 30448#64) (polyVecNat (uVecPoly06 rho coins 0)) ∗
      ATransRowAt (sp + 4160#64) rho 0 ∗ ATransRowAt (sp + 4160#64) rho 2 ∗
      ATransRowAt (sp + 4160#64) rho 3 ∗ PolyMem (sp + 28368#64) (polyVecNat e1_0) ∗
      PolyMem (sp + 29392#64) (polyVecNat e1_2) ∗ PolyMem (sp + 29904#64) (polyVecNat e1_3) ∗
      PolyMem (sp + 31472#64) (fun _ => 0#128) ∗ PolyMem (sp + 31984#64) (fun _ => 0#128) ∗ Rest)
    hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hregs1
  dsimp only at hrow1; simp only [show (1 : Nat) < 3 by decide, ↓reduceIte, hu1, he1, hb1] at hrow1
  refine SepWP.weaken_pre (Entails.trans hP1 (by sep_frame)) (sepWP_seq_env hcl1 hro1 hrow1 ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, _, _, hregs2, t2, v2, hP2⟩
  have hrow2 := seg7_row_ok hb s2 sp fpVal rho coins (row := 2) (by decide) t2 v2
    (PolyMem (sp + 30448#64) (polyVecNat (uVecPoly06 rho coins 0)) ∗
      PolyMem (sp + 30960#64) (polyVecNat (uVecPoly06 rho coins 1)) ∗
      ATransRowAt (sp + 4160#64) rho 0 ∗ ATransRowAt (sp + 4160#64) rho 1 ∗
      ATransRowAt (sp + 4160#64) rho 3 ∗ PolyMem (sp + 28368#64) (polyVecNat e1_0) ∗
      PolyMem (sp + 28880#64) (polyVecNat e1_1) ∗ PolyMem (sp + 29904#64) (polyVecNat e1_3) ∗
      PolyMem (sp + 31984#64) (fun _ => 0#128) ∗ Rest)
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hregs2
  dsimp only at hrow2; simp only [show (2 : Nat) < 3 by decide, ↓reduceIte, hu2, he2, hb2] at hrow2
  refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame)) (sepWP_seq_env hcl2 hro2 hrow2 ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, _, _, hregs3, t3, v3, hP3⟩
  have hrow3 := seg7_row_ok hb s3 sp fpVal rho coins (row := 3) (by decide) t3 v3
    (PolyMem (sp + 30448#64) (polyVecNat (uVecPoly06 rho coins 0)) ∗
      PolyMem (sp + 30960#64) (polyVecNat (uVecPoly06 rho coins 1)) ∗
      PolyMem (sp + 31472#64) (polyVecNat (uVecPoly06 rho coins 2)) ∗
      ATransRowAt (sp + 4160#64) rho 0 ∗ ATransRowAt (sp + 4160#64) rho 1 ∗
      ATransRowAt (sp + 4160#64) rho 2 ∗ PolyMem (sp + 28368#64) (polyVecNat e1_0) ∗
      PolyMem (sp + 28880#64) (polyVecNat e1_1) ∗ PolyMem (sp + 29392#64) (polyVecNat e1_2) ∗ Rest)
    hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hregs3
  dsimp only at hrow3; simp only [Nat.lt_irrefl, ↓reduceIte, hu3, he3, hb3] at hrow3
  refine SepWP.weaken_pre (Entails.trans hP3 (by sep_frame)) (SepWP.mono hrow3 ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hcl_f, hro_f, hregs_f, tf, vf, hPf⟩
  refine ⟨hsp_f, hspA_f, hregs_f.fp, hregs_f.x19, hcl_f, hro_f, Entails.trans hPf ?_⟩
  exact entails_sub (spillSlice27_entails_memRegion (sp + 2000#64) tf) (by sep_frame)
    (entails_sub (poly32Mem_entails_memRegion (sp + 14432#64) vf) (by sep_frame)
      (by dsimp only [ATransAt]; sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7Row

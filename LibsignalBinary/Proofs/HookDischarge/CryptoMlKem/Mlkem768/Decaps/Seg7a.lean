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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Add -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2c
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Inv2LowLoops
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6a

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 7a (`+0x8d00 .. +0xa968`)

Computes the 3-polynomial re-encrypted vector `u'[0..2]` (`InvNTT(Âᵀ[row] ∘ r̂) + e₁[row]`) at
`[sp + 22400, sp + 23936)` via `DotLoops2`, `Inv2LowLoops`, `SymEvalInv2{a,b,c}`, and the 16-step
`montgomery(1441) + e₁[row] + barrett` loop, then copies `1,536` bytes to `[sp + 11872, sp + 13408)`
via `B28` `memcpy`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7a

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ mlkemMpl
  resolve_blk28 resolve_ro00 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 Shake128SeedTerminates mlkemQ neonBarrettReduce16 neonInvNttMontgomery16
  neonMontgomeryMul16 neonPolyNttMul16 parseRej12Candidates polyAdd polyInvNtt polyNtt
  sampleMatrixWith sampleNtt samplePolyCbd2 sampleVecCbd2 shake128FirstBlocks shake256List
  vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMla8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h)
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
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec32 VecRangeMem
  poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat step_ldpQ128 step_ldrQ128 step_strQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16 lowerInvNtt16_size neonDot3 neonDot3_size upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  exec_simdAdd_8h exec_simdDup_8h_gpr exec_simdMla_8h exec_simdMovi_8h_1024
  exec_simdMul_8h exec_simdMvni_8h_f2ff exec_simdSqdmulh_8h exec_simdSshr_8h_1
  exec_simdSshr_8h_11 exec_simdSub_8h sqdmulh8hFlags)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure (upperInvNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (seg5FinalPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2 (
  aTransPoly aTransPoly16 sampleMatrixWith_false_getD)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  exec_simdMovi_2d_0 shake256List_length step_bCond_not_taken step_bCond_taken vecRangeBytes_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Add (
  seg5AddPoly seg5Add_vec_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  Spill21 Spill21Mem Spill6 Spill6Mem spill21Mem_entails_memRegion spill21Mem_ofFn
  spill6Mem_entails_memRegion spill6Mem_ofFn)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (
  SymGprs31 SymVRegs runSymRange runSymRange_add)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval (
  SymEnv SymSpatial SymStateMatches evalSExpr evalSymGpr evalSymSpill13
  evalSymSpill21 evalSymSpill6 evalSymVec32 inPolyMemAt polyAddr spillMemAt symEnvOf)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly (sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge (
  symPoly_eq_upperInvNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2a (
  cfgInv2 run_inv2a symInv2Init)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2b (
  run_inv2b symInv2MidB)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv2c (
  inv2_ast_eq inv2_noSpillVreg run_inv2c symInv2End)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops2 (
  Dot2Preserved dot2_ok ro00Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Inv2LowLoops (
  Inv2Preserved inv2_low_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a (blk28_memcpy_04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5 (
  ATransMemAt ATransRowMemAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6a (fwd2Spill13)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b (
  rHatPoly16 rHatPoly16_spec)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x8d00 → 0x8d60, 0xa89c → 0xa964]
end

@[simp, arm64_norm, wp_norm] abbrev offSeg7Start    : BitVec 64 := BitVec.ofNat 64 36096
@[simp, arm64_norm, wp_norm] abbrev offSeg7Dot      : BitVec 64 := BitVec.ofNat 64 36196
@[simp, arm64_norm, wp_norm] abbrev offSeg7InvLow   : BitVec 64 := BitVec.ofNat 64 37056
@[simp, arm64_norm, wp_norm] abbrev offSeg7InvHi    : BitVec 64 := BitVec.ofNat 64 37332
@[simp, arm64_norm, wp_norm] abbrev offSeg7Add      : BitVec 64 := BitVec.ofNat 64 43164
@[simp, arm64_norm, wp_norm] abbrev offSeg7Tail     : BitVec 64 := BitVec.ofNat 64 43300
@[simp, arm64_norm, wp_norm] abbrev offSeg7Copy     : BitVec 64 := BitVec.ofNat 64 43328
@[simp, arm64_norm, wp_norm] abbrev offSeg7SerStart : BitVec 64 := BitVec.ofNat 64 43368

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

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

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0' {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0b0000#4 0b000#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC :=
  exec_simdMovi_2d_0 rd s

attribute [local irreducible]
  blkPC04 dup8x16 polyVecNat simdAdd8h simdSub8h simdMul8h simdMla8h simdSqdmulh8h simdSshr8h

attribute [local wp_norm ↓ high]
  exec_simdAdd_8h' exec_simdSub_8h' exec_simdMul_8h' exec_simdMla_8h'
  exec_simdSqdmulh_8h' exec_simdSshr_8h_1' exec_simdSshr_8h_11'
  exec_simdMovi_8h_1024' exec_simdMvni_8h_f2ff' exec_simdDup_8h_gpr' exec_simdMovi_2d_0'

/-! ## 1. Pure `uVecPoly16` Soundness Against `Spec` -/

/-- `Poly16` result of row `row` in `B04` Segment 7 (`InvNTT(Âᵀ[row] ∘ r̂) + e₁[row]`). -/
@[expose] noncomputable def uVecPoly16 (rho coins : List (BitVec 8)) (row : Nat) : Poly16 :=
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
  split
  · rename_i h
    have hge := Classical.choose_spec h
    set cands := parseRej12Candidates (shake128FirstBlocks seed34 (Classical.choose h + 3))
    have hsz : (cands.take 256).toArray.size = 256 := by simp [List.length_take, hge]
    refine ⟨hsz, fun i hi => ?_⟩
    have hmem : (cands.take 256).toArray[i]'(by omega) ∈ cands :=
      List.mem_of_mem_take (Array.getElem_mem_toList _)
    have hgd : (cands.take 256).toArray.getD i 0 = (cands.take 256).toArray[i]'(by omega) := by
      simp [Array.getD, hsz, hi]
    rw [hgd]
    exact parseRej12Candidates_lt_q _ _ hmem
  · exact zeroPoly_canonical

private theorem aTransPoly16_spec (rho : List (BitVec 8)) (row col : Nat) :
    PolyBounded16 4095 (aTransPoly16 rho row col) ∧
    PolyRepresents (aTransPoly16 rho row col) (aTransPoly rho row col) := by
  unfold aTransPoly16 aTransPoly
  obtain ⟨hsz, hlt⟩ := sampleNtt_canonical (rho ++ [BitVec.ofNat 8 row, BitVec.ofNat 8 col])
  generalize sampleNtt (rho ++ [BitVec.ofNat 8 row, BitVec.ofNat 8 col]) = f at hsz hlt ⊢
  have hmsz : (f.map (BitVec.ofNat 16)).size = 256 := by simp [hsz]
  have hint : ∀ i < 256, ((f.map (BitVec.ofNat 16)).getD i 0#16).toInt = (f.getD i 0 : Int) := by
    intro i hi
    have hq : f.getD i 0 < 3329 := hlt i hi
    have hget : (f.map (BitVec.ofNat 16)).getD i 0#16 = BitVec.ofNat 16 (f.getD i 0) := by
      simp [Array.getD, hsz, hi]
    rw [hget]
    generalize f.getD i 0 = c at hq ⊢
    unfold BitVec.toInt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 16)]
    have hc2 : 2 * c < 2 ^ 16 := by omega
    simp only [hc2, ↓reduceIte]
  refine ⟨⟨hmsz, fun i hi => ?_⟩, ⟨hmsz, fun i hi => ?_⟩⟩
  · have hq : f.getD i 0 < 3329 := hlt i hi
    rw [hint i hi]; omega
  · rw [hint i hi]

private theorem seg5AddPoly_eq_barrett_aux {inv : Poly16} (hinv : inv.size = 256) (e1 : Poly16) :
    seg5AddPoly inv e1 =
      (polyAdd16 (inv.map (fun x => neonMontgomeryMul16 x 1441#16)) e1).map neonBarrettReduce16 := by
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
    rw [← upperInvNtt16_lowerInvNtt16 dot, upperInvNtt16_size]
    exact lowerInvNtt16_size hdot
  exact seg5AddPoly_eq_barrett_aux hinv e1

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
  have htc : coins.take 32 = coins := List.take_of_length_le (Nat.le_of_eq hcoins)
  have hsh (d : BitVec 8) : (shake256List 128 (coins ++ [d])).length = 128 :=
    shake256List_length 128 (coins ++ [d])
  obtain ⟨ha0_b, ha0_r⟩ := aTransPoly16_spec rho row 0
  obtain ⟨ha1_b, ha1_r⟩ := aTransPoly16_spec rho row 1
  obtain ⟨ha2_b, ha2_r⟩ := aTransPoly16_spec rho row 2
  rw [← sampleMatrixWith_false_getD hrho hrow (by decide : 0 < 3)] at ha0_r
  rw [← sampleMatrixWith_false_getD hrho hrow (by decide : 1 < 3)] at ha1_r
  rw [← sampleMatrixWith_false_getD hrho hrow (by decide : 2 < 3)] at ha2_r
  obtain ⟨_, hr0_b, hr0_r⟩ := rHatPoly16_spec (hsh 0#8)
  obtain ⟨_, hr1_b, hr1_r⟩ := rHatPoly16_spec (hsh 1#8)
  obtain ⟨_, hr2_b, hr2_r⟩ := rHatPoly16_spec (hsh 2#8)
  have hrb (p : Poly16) (h : PolyBounded16 1664 p) : PolyBounded16 4095 p :=
    ⟨h.1, fun i hi => ⟨by have := (h.2 i hi).1; omega, by have := (h.2 i hi).2; omega⟩⟩
  have hrg (j : Nat) (hj : j < 3) :
      ((sampleVecCbd2 3 coins 0).map polyNtt).getD j zeroPoly =
        polyNtt (samplePolyCbd2 (shake256List 128 (coins ++ [BitVec.ofNat 8 j]))) := by
    unfold sampleVecCbd2
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_ofFn, hj,
      ↓reduceDIte, Option.map_some, Option.getD_some, Nat.zero_add, htc]
  rw [← hrg 0 (by decide)] at hr0_r
  rw [← hrg 1 (by decide)] at hr1_r
  rw [← hrg 2 (by decide)] at hr2_r
  obtain ⟨hdot_b, hdot_r⟩ := neonVecDotNtt3_spec ha0_b ha1_b ha2_b
    (hrb _ hr0_b) (hrb _ hr1_b) (hrb _ hr2_b) ha0_r ha1_r ha2_r hr0_r hr1_r hr2_r
  have hdot_b8 : PolyBounded16 8704 _ :=
    ⟨hdot_b.1, fun i hi => ⟨by have := (hdot_b.2 i hi).1; omega, by have := (hdot_b.2 i hi).2; omega⟩⟩
  obtain ⟨_, hinv_b, hinv_r⟩ := neonPolyInvNttFromMontInv16_spec hdot_b8 hdot_r
    (vecDotNtt_canonical 3 _ _)
  obtain ⟨he1_b, he1_r⟩ := neonCbd2Poly16_spec (hsh (BitVec.ofNat 8 (3 + row)))
  have he1g : (sampleVecCbd2 3 coins 3).getD row zeroPoly =
      samplePolyCbd2 (shake256List 128 (coins ++ [BitVec.ofNat 8 (3 + row)])) := by
    unfold sampleVecCbd2
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hrow, ↓reduceDIte,
      Option.getD_some, htc]
  rw [← he1g] at he1_r
  obtain ⟨_, hadd_r⟩ := polyAdd16_spec hinv_b he1_b (by omega) hinv_r he1_r
  unfold uVecPoly16
  rw [seg5AddPoly_eq_barrett (neonDot3_size _ _ _ _ _ _)]
  exact neonBarrettReducePoly16_spec hadd_r

/-! ## 2. Symbolic Upper `InvNTT2` (`+0x91d4 → +0xa89c`) -/

private theorem run_inv2abc : runSymRange cfgInv2 9333 1458 symInv2Init = some symInv2End :=
  runSymRange_add cfgInv2 9333 972 486 _ _ _
    (runSymRange_add cfgInv2 9333 486 486 _ _ _ run_inv2a run_inv2b) run_inv2c

private theorem matches_inv2Init (s : State) (sp polyPtr : BitVec 64)
    (t6 : Spill6) (t21 : Spill21) (p2 : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hx26 : s.readReg64 .x26 = polyPtr)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hx21 : s.readReg64 .x21 = 64778#64) (hx22 : s.readReg64 .x22 = 31498#64) :
    let env := symEnvOf s fwd2Spill13 t6 t21 (Vec32.ofFn (polyVecNat p2)) Vec32.zero
    SymStateMatches cfgInv2 sp polyPtr env symInv2Init s := by
  dsimp only
  refine ⟨hsp, hspA, ?_, ?_, ?_, rfl⟩
  · rintro r ⟨rfl⟩; exact hx26
  · intro r; rcases r with ⟨rv, hrv⟩
    match rv with
    | 16 => simpa [symInv2Init, SymVRegs.get, evalSExpr] using hv16
    | 17 => simpa [symInv2Init, SymVRegs.get, evalSExpr] using hv17
    | 23 => simpa [symInv2Init, SymVRegs.get, evalSExpr] using hv23
    | 27 => simpa [symInv2Init, SymVRegs.get, evalSExpr] using hv27
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 18 | 19 | 20 | 21 | 22 | 24 | 25 | 26 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · intro r hr; rcases r with ⟨rv, hrv⟩
    match rv with
    | 21 => simpa [symInv2Init, SymGprs31.get, evalSymGpr] using hx21
    | 22 => simpa [symInv2Init, SymGprs31.get, evalSymGpr] using hx22
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symInv2Init, SymGprs31.get, evalSymGpr, symEnvOf]
    | 31 => simp at hr
    | _ + 32 => omega

private theorem seg7_upper_inv2 [MlKemPlacement] {b sp polyPtr : BitVec 64}
    (s : State) {dot : Poly16} (hdot : dot.size = 256)
    (t6 : Spill6) (t21 : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7InvHi) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hx26 : s.readReg64 .x26 = polyPtr)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hx21 : s.readReg64 .x21 = 64778#64) (hx22 : s.readReg64 .x22 = 31498#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Add) s
      (PolyMem polyPtr (polyVecNat (lowerInvNtt16 dot)) ∗
        Spill6Mem (sp + 1824#64) t6 ∗ Spill21Mem (sp + 1920#64) t21 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x12 = s.readReg64 .x20 + s.readReg64 .x10 ∧
        sf.readReg64 .x27 = 0#64 ∧
        (∀ r : BitVec 5, r ≠ 12#5 → r ≠ 27#5 → r.toNat < 31 →
          sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        sf.readVReg128 0#5 = s.readVReg128 0#5 ∧
        sf.readVReg128 16#5 = dup8x16 3329#16 ∧
        sf.readVReg128 17#5 = dup8x16 20159#16 ∧
        sf.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧
        sf.readVReg128 27#5 = dup8x16 1024#16 ∧
        ∃ (t6' : Spill6) (t21' : Spill21),
          Pf = (PolyMem polyPtr (polyVecNat (neonInvNttMontgomery16 dot)) ∗
            Spill6Mem (sp + 1824#64) t6' ∗ Spill21Mem (sp + 1920#64) t21' ∗ Rest)) := by
  set p2 := lowerInvNtt16 dot
  have hp2 : p2.size = 256 := lowerInvNtt16_size hdot
  set env := symEnvOf s fwd2Spill13 t6 t21 (Vec32.ofFn (polyVecNat p2)) Vec32.zero
  have hm := matches_inv2Init s sp polyPtr t6 t21 p2 hsp hspA hx26 hv16 hv17 hv23 hv27 hx21 hx22
  have hspatial_in :
      (PolyMem polyPtr (polyVecNat p2) ∗
        Spill6Mem (sp + 1824#64) t6 ∗ Spill21Mem (sp + 1920#64) t21 ∗ Rest) =
      SymSpatial cfgInv2 sp polyPtr env symInv2Init Rest := by
    dsimp only [SymSpatial, cfgInv2, polyAddr, spillMemAt, inPolyMemAt]
    have hs6 : evalSymSpill6 env symInv2Init.spill6 = t6 := by
      dsimp only [symInv2Init, evalSymSpill6, evalSExpr, env, symEnvOf]; cases t6; rfl
    have hs21 : evalSymSpill21 env symInv2Init.spill21 = t21 := by
      dsimp only [symInv2Init, evalSymSpill21, evalSExpr, env, symEnvOf]; cases t21; rfl
    have hpoly : evalSymVec32 env symInv2Init.poly = Vec32.ofFn (polyVecNat p2) := by
      dsimp only [symInv2Init, evalSymVec32, evalSExpr, env, symEnvOf]
      generalize Vec32.ofFn (polyVecNat p2) = v0; cases v0; rfl
    rw [hs6, hs21, hpoly, poly32Mem_ofFn]
    exact sepProp_ext (by sep_frame) (by sep_frame)
  rw [hspatial_in]
  refine sepWP_of_runSymRange (cfg := cfgInv2) (sp := sp) (polyPtr := polyPtr) (env := env) (F := Rest)
    1458 9333
    (fun j h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))
    run_inv2abc hm hpc hrun ?_
  intro sf _ _ hmf
  refine ⟨hmf.hsp, hmf.hsp_al, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    evalSymSpill6 env symInv2End.spill6, evalSymSpill21 env symInv2End.spill21, ?_⟩
  · simpa [symInv2End, SymGprs31.get, evalSymGpr, env, symEnvOf] using hmf.hgprs 12#5 (by decide)
  · simpa [symInv2End, SymGprs31.get, evalSymGpr] using hmf.hgprs 27#5 (by decide)
  · intro r hr12 hr27 hr31
    have hg := hmf.hgprs r hr31
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 21 => simpa [symInv2End, SymGprs31.get, evalSymGpr] using hg.trans hx21.symm
    | 22 => simpa [symInv2End, SymGprs31.get, evalSymGpr] using hg.trans hx22.symm
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 23 | 24 | 25 | 26 | 28 | 29 | 30 =>
      simpa [symInv2End, SymGprs31.get, evalSymGpr, env, symEnvOf] using hg
    | 12 => exact absurd rfl hr12
    | 27 => exact absurd rfl hr27
    | 31 => simp at hr31
    | _ + 32 => omega
  · simpa [symInv2End, SymVRegs.get, evalSExpr, env, symEnvOf] using hmf.hvregs 0#5
  · simpa [symInv2End, SymVRegs.get, evalSExpr] using hmf.hvregs 16#5
  · simpa [symInv2End, SymVRegs.get, evalSExpr] using hmf.hvregs 17#5
  · simpa [symInv2End, SymVRegs.get, evalSExpr] using hmf.hvregs 23#5
  · simpa [symInv2End, SymVRegs.get, evalSExpr] using hmf.hvregs 27#5
  · dsimp only [SymSpatial, cfgInv2, polyAddr, spillMemAt, inPolyMemAt]
    rw [symPoly_eq_upperInvNtt polyPtr symInv2End.poly hp2 env rfl inv2_noSpillVreg inv2_ast_eq,
      upperInvNtt16_lowerInvNtt16]
    exact sepProp_ext (by sep_frame) (by sep_frame)

/-! ## 3. Post-`InvNTT2` `+ e1[row]` Loop (`+0xa89c → +0xa924`) & Outer Tail (`+0xa924 → +0xa940`) -/

private structure Seg7AddPreserved (s0 s : State) : Prop where
  x0  : s.readReg64 .x0  = s0.readReg64 .x0
  x3  : s.readReg64 .x3  = s0.readReg64 .x3
  x8  : s.readReg64 .x8  = s0.readReg64 .x8
  x9  : s.readReg64 .x9  = s0.readReg64 .x9
  x10 : s.readReg64 .x10 = s0.readReg64 .x10
  x11 : s.readReg64 .x11 = s0.readReg64 .x11
  x13 : s.readReg64 .x13 = s0.readReg64 .x13
  x15 : s.readReg64 .x15 = s0.readReg64 .x15
  x16 : s.readReg64 .x16 = s0.readReg64 .x16
  x17 : s.readReg64 .x17 = s0.readReg64 .x17
  x19 : s.readReg64 .x19 = s0.readReg64 .x19
  x20 : s.readReg64 .x20 = s0.readReg64 .x20
  x21 : s.readReg64 .x21 = s0.readReg64 .x21
  x22 : s.readReg64 .x22 = s0.readReg64 .x22
  x23 : s.readReg64 .x23 = s0.readReg64 .x23
  x24 : s.readReg64 .x24 = s0.readReg64 .x24
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x28 : s.readReg64 .x28 = s0.readReg64 .x28
  fp  : s.readReg64 .fp  = s0.readReg64 .fp
  v0  : s.readVReg128 0#5  = s0.readVReg128 0#5
  v23 : s.readVReg128 23#5 = s0.readVReg128 23#5
  v27 : s.readVReg128 27#5 = s0.readVReg128 27#5


set_option maxRecDepth 100000 in
private theorem seg7_add_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp polyPtr e1Ptr : BitVec 64) {r : Nat} (hr : r < 16)
    (inv e1 : Poly16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Add) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx9 : s.readReg64 .x9 = e1Ptr) (hx12 : s.readReg64 .x12 = polyPtr + 16#64)
    (hx23 : s.readReg64 .x23 = 1441#64) (hx24 : s.readReg64 .x24 = 55457#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (32 * r))
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hpres : Seg7AddPreserved s0 s)
    (hf0 : f (2 * r) = polyVecNat inv (2 * r))
    (hf1 : f (2 * r + 1) = polyVecNat inv (2 * r + 1)) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if r < 15 then b + offSeg7Add else b + offSeg7Tail) s
      (PolyMem polyPtr f ∗ PolyMem e1Ptr (polyVecNat e1) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x9 = e1Ptr ∧ s'.readReg64 .x12 = polyPtr + 16#64 ∧
        s'.readReg64 .x23 = 1441#64 ∧ s'.readReg64 .x24 = 55457#64 ∧
        s'.readReg64 .x27 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
        s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧ s'.readVReg128 27#5 = dup8x16 1024#16 ∧
        Seg7AddPreserved s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update
            (Function.update f (2 * r + 1) (polyVecNat (seg5AddPoly inv e1) (2 * r + 1)))
            (2 * r) (polyVecNat (seg5AddPoly inv e1) (2 * r))) ∗
          PolyMem e1Ptr (polyVecNat e1) ∗ Rest)) := by
  have _ : b = blkPl04.base := hb
  rcases hpres with ⟨p0, p3, p8, p9, p10, p11, p13, p15, p16, p17,
    p19, p20, p21, p22, p23, p24, p25, p28, pfp, pv0, pv23, pv27⟩
  wp_steps 2
  refine step_ldrQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1))) (v := polyVecNat inv (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx12, hx27]; clear * - hr; bv_omega)
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
  have hv2_eq := seg5Add_vec_eq inv e1 (2 * r + 1) (by omega)
  have hv1_eq := seg5Add_vec_eq inv e1 (2 * r) (by omega)
  dsimp only at hv2_eq hv1_eq
  refine step_strQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (val := polyVecNat (seg5AddPoly inv e1) (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx12, hx27]; clear * - hr; bv_omega)
    (by simp [← hv2_eq])
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m1; wp_steps 2
  refine step_strQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (val := polyVecNat (seg5AddPoly inv e1) (2 * r))
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
        by simp [hx9], by simp [hx12], by simp [hx23], by simp [hx24],
        by simp; clear * - hr15; bv_omega,
        by simp [hv16], by simp [hv17], by simp [hv23], by simp [hv27],
        ⟨by simp [p0], by simp [p3], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
          by simp [p13], by simp [p15], by simp [p16], by simp [p17], by simp [p19], by simp [p20],
          by simp [p21], by simp [p22], by simp [p23], by simp [p24], by simp [p25], by simp [p28],
          by simp [pfp], by simp [pv0], by simp [pv23], by simp [pv27]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt; clear * - hne hr hlt; bv_omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx9], by simp [hx12], by simp [hx23], by simp [hx24],
        by simp [hr_eq],
        by simp [hv16], by simp [hv17], by simp [hv23], by simp [hv27],
        ⟨by simp [p0], by simp [p3], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
          by simp [p13], by simp [p15], by simp [p16], by simp [p17], by simp [p19], by simp [p20],
          by simp [p21], by simp [p22], by simp [p23], by simp [p24], by simp [p25], by simp [p28],
          by simp [pfp], by simp [pv0], by simp [pv23], by simp [pv27]⟩, rfl⟩

private theorem seg7_add_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 : State) (sp polyPtr e1Ptr : BitVec 64) (inv e1 : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offSeg7Add → s.status = .Running →
      s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x9 = e1Ptr → s.readReg64 .x12 = polyPtr + 16#64 →
      s.readReg64 .x23 = 1441#64 → s.readReg64 .x24 = 55457#64 →
      s.readReg64 .x27 = BitVec.ofNat 64 (32 * r) →
      s.readVReg128 16#5 = dup8x16 3329#16 → s.readVReg128 17#5 = dup8x16 20159#16 →
      s.readVReg128 23#5 = dup8x16 0xf2ff#16 → s.readVReg128 27#5 = dup8x16 1024#16 →
      Seg7AddPreserved s0 s →
      (∀ idx, idx < 2 * r → f idx = polyVecNat (seg5AddPoly inv e1) idx) →
      (∀ idx, 2 * r ≤ idx → idx < 32 → f idx = polyVecNat inv idx) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Tail) s
        (PolyMem polyPtr f ∗ PolyMem e1Ptr (polyVecNat e1) ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ Seg7AddPreserved s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat (seg5AddPoly inv e1)) ∗
            PolyMem e1Ptr (polyVecNat e1) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _ _ hx9 hx12 hx23 hx24 hx27 hv16 hv17 hv23 hv27 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hstep := seg7_add_iter hb s0 s sp polyPtr e1Ptr (r := 15) (by omega) inv e1 f Rest
      hpc hrun hsp hspA hx9 hx12 hx23 hx24 hx27 hv16 hv17 hv23 hv27 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    simp only [Nat.lt_irrefl, ↓reduceIte] at hstep
    refine SepWP.mono hstep ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, _, _, _, _, hpres', rfl⟩
    refine ⟨hsp', hspA', hpres', ?_⟩
    have hmem : PolyMem polyPtr
        (Function.update
          (Function.update f 31 (polyVecNat (seg5AddPoly inv e1) 31))
          30 (polyVecNat (seg5AddPoly inv e1) 30)) =
        PolyMem polyPtr (polyVecNat (seg5AddPoly inv e1)) := by
      apply vecRangeMem_congr; intro idx hidx
      by_cases h30 : idx = 30
      · subst h30; simp
      · by_cases h31 : idx = 31
        · subst h31; simp
        · simp [Function.update_of_ne h30, Function.update_of_ne h31, hlo idx (by omega)]
    rw [hmem]
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx9 hx12 hx23 hx24 hx27 hv16 hv17 hv23 hv27 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hstep := seg7_add_iter hb s0 s sp polyPtr e1Ptr (r := r) (by omega) inv e1 f Rest
      hpc hrun hsp hspA hx9 hx12 hx23 hx24 hx27 hv16 hv17 hv23 hv27 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr15, ↓reduceIte] at hstep
    refine sepWP_seq_env hcl hro hstep ?_
    rintro s1 P1 hpc1 hrun1 hcl1 hro1
      ⟨hsp1, hspA1, hx9_1, hx12_1, hx23_1, hx24_1, hx27_1, hv16_1, hv17_1, hv23_1, hv27_1, hpres1, rfl⟩
    refine ih (r + 1) (by omega) s1 _ hpc1 hrun1 hsp1 hspA1 hcl1 hro1
      hx9_1 hx12_1 hx23_1 hx24_1 hx27_1 hv16_1 hv17_1 hv23_1 hv27_1 hpres1 ?_ ?_
    · intro idx hidx
      by_cases h0 : idx = 2 * r
      · subst h0; simp
      · by_cases h1 : idx = 2 * r + 1
        · subst h1; simp
        · simp [Function.update_of_ne h0, Function.update_of_ne h1, hlo idx (by omega)]
    · intro idx hge hlt
      simp [Function.update_of_ne (show idx ≠ 2 * r by omega),
        Function.update_of_ne (show idx ≠ 2 * r + 1 by omega), hhi idx (by omega) hlt]

private theorem seg7_add_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp polyPtr e1Ptr : BitVec 64) (inv e1 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Add) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx9 : s.readReg64 .x9 = e1Ptr) (hx12 : s.readReg64 .x12 = polyPtr + 16#64)
    (hx23 : s.readReg64 .x23 = 1441#64) (hx24 : s.readReg64 .x24 = 55457#64)
    (hx27 : s.readReg64 .x27 = 0#64)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16) (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16) (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hpres : Seg7AddPreserved s0 s) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Tail) s
      (PolyMem polyPtr (polyVecNat inv) ∗ PolyMem e1Ptr (polyVecNat e1) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ Seg7AddPreserved s0 s' ∧
        P' = (PolyMem polyPtr (polyVecNat (seg5AddPoly inv e1)) ∗
          PolyMem e1Ptr (polyVecNat e1) ∗ Rest)) :=
  seg7_add_loop hb s0 sp polyPtr e1Ptr inv e1 Rest 15 0 rfl s (polyVecNat inv)
    hpc hrun hsp hspA hcl hro hx9 hx12 hx23 hx24 hx27 hv16 hv17 hv23 hv27 hpres
    (fun _ h => by omega) (fun _ _ _ => rfl)

private theorem seg7_outer_tail [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) {i : Nat} (hi : i < 3) (P : SepProp)
    (hpc : s.pc = b + offSeg7Tail) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 (1536 * (i + 1)))
    (hx25 : s.readReg64 .x25 = 6144#64) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if i < 2 then b + offSeg7Dot else b + offSeg7Copy) s P
      (fun s' P' =>
        s'.sp = s.sp ∧ s'.spAligned = s.spAligned ∧ s'.vregs = s.vregs ∧
        s'.readReg64 .x8 = s.readReg64 .x8 + 512#64 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 + 512#64 ∧
        s'.readReg64 .x10 = s.readReg64 .x10 + 512#64 ∧
        s'.readReg64 .x19 = BitVec.ofNat 64 (1536 * (i + 2)) ∧
        s'.readReg64 .x28 = s.readReg64 .x28 + 1536#64 ∧
        (∀ r : BitVec 5, r ≠ 8#5 → r ≠ 9#5 → r ≠ 10#5 → r ≠ 19#5 → r ≠ 28#5 → r ≠ 31#5 →
          s'.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        P' = P) := by
  have _ : b = blkPl04.base := hb
  wp_steps 6; wp_step; wp_if hne
  · have hi2 : i < 2 := by
      by_contra hge; have hi_eq : i = 2 := by omega
      subst hi_eq; simp at hne
    simp only [hi2, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨rfl, rfl, rfl, by simp, by simp, by simp,
        by simp; clear * - hi2; bv_omega, by simp,
        fun r h8 h9 h10 h19 h28 h31 => by simp [h8, h9, h10, h19, h28, h31], by simp, rfl⟩
  · have hi2 : ¬ i < 2 := by
      intro hlt; rcases i with _ | _ | i
      · simp at hne
      · simp at hne
      · omega
    have hi_eq : i = 2 := by omega
    simp only [hi2, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨rfl, rfl, rfl, by simp, by simp, by simp,
        by simp [hi_eq], by simp,
        fun r h8 h9 h10 h19 h28 h31 => by simp [h8, h9, h10, h19, h28, h31], by simp, rfl⟩

/-! ## 4. Setup (`+0x8d00 → +0x8d64`), Per-Row Step (`+0x8d64 → +0xa940`), & `memcpy` (`+0xa940 → +0xa968`) -/

private structure Seg7RowInv [MlKemPlacement] (sp fpVal : BitVec 64) (i : Nat) (s : State) : Prop where
  hsp  : s.sp = sp
  hspA : s.spAligned = true
  hfp  : s.readReg64 .fp  = fpVal
  hx0  : s.readReg64 .x0  = 20159#64
  hx3  : s.readReg64 .x3  = mlkemMpl.ρ ro00Sym + 134#64
  hx8  : s.readReg64 .x8  = sp + BitVec.ofNat 64 (22416 + 512 * i)
  hx9  : s.readReg64 .x9  = sp + BitVec.ofNat 64 (20704 + 512 * i)
  hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (16 + 512 * i)
  hx11 : s.readReg64 .x11 = BitVec.ofNat 64 i
  hx13 : s.readReg64 .x13 = sp + 19168#64
  hx15 : s.readReg64 .x15 = 62209#64
  hx16 : s.readReg64 .x16 = 3329#64
  hx17 : s.readReg64 .x17 = sp + 11856#64
  hx19 : s.readReg64 .x19 = BitVec.ofNat 64 (1536 * (i + 1))
  hx20 : s.readReg64 .x20 = sp + 22400#64
  hx21 : s.readReg64 .x21 = 64778#64
  hx22 : s.readReg64 .x22 = 31498#64
  hx23 : s.readReg64 .x23 = 1441#64
  hx24 : s.readReg64 .x24 = 55457#64
  hx25 : s.readReg64 .x25 = 6144#64
  hx28 : s.readReg64 .x28 = sp + BitVec.ofNat 64 (7216 + 1536 * i)
  hv0  : s.readVReg128 0#5  = 0#128
  hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16
  hv27 : s.readVReg128 27#5 = dup8x16 1024#16

private theorem seg7_setup [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) (P : SepProp)
    (hpc : s.pc = b + offSeg7Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = 1536#64) (hx20 : s.readReg64 .x20 = sp + 22400#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Dot) s P
      (fun s1 P1 => Seg7RowInv sp fpVal 0 s1 ∧ P1 = P) := by
  have _ : b = blkPl04.base := hb
  wp_steps 25
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨⟨by simp [hsp], by simpa [State.spAligned] using hspA, by simp [hfp],
      by simp, by simp,
      by simp, by simp,
      by simp, by simp,
      by simp, by simp, by simp,
      by simp,
      by simp [hx19], by simp [hx20],
      by simp, by simp, by simp, by simp, by simp,
      by simp,
      by simp, by simp, by simp⟩, rfl⟩

private theorem polyMem_zero_eq_poly32Mem (ptr : BitVec 64) :
    PolyMem ptr (fun _ => 0#128) = Poly32Mem ptr Vec32.zero := by
  unfold PolyMem Poly32Mem
  apply vecRangeMem_congr; intro k hk
  rcases (show k < 32 from hk) with _
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
  | _ + 32 => omega

private theorem seg7_row [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) {i : Nat} (hi : i < 3)
    (rho coins : List (BitVec 8)) (v11856 : Vec32) (t6 : Spill6) (t21 : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Dot) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hinv : Seg7RowInv sp fpVal i s) :
    let polyPtr := sp + BitVec.ofNat 64 (22400 + 512 * i)
    let e1Ptr := sp + BitVec.ofNat 64 (20704 + 512 * i)
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let e1 := neonCbd2Poly16 (shake256List 128 (coins ++ [BitVec.ofNat 8 (3 + i)]))
    SepWP (blkPC04.rebase b (fun _ => none))
      (if i < 2 then b + offSeg7Dot else b + offSeg7Copy) s
      (PolyMem polyPtr (fun _ => 0#128) ∗ ATransRowMemAt sp 7216 rho i ∗
        PolyMem (sp + 19168#64) (polyVecNat r0) ∗
        PolyMem (sp + 19680#64) (polyVecNat r1) ∗
        PolyMem (sp + 20192#64) (polyVecNat r2) ∗
        PolyMem e1Ptr (polyVecNat e1) ∗ Poly32Mem (sp + 11856#64) v11856 ∗
        Spill6Mem (sp + 1824#64) t6 ∗ Spill21Mem (sp + 1920#64) t21 ∗ Rest)
      (fun sf Pf =>
        Seg7RowInv sp fpVal (i + 1) sf ∧
        ∃ (v11856' : Vec32) (t6' : Spill6) (t21' : Spill21),
          Pf = (PolyMem polyPtr (polyVecNat (uVecPoly16 rho coins i)) ∗
            ATransRowMemAt sp 7216 rho i ∗
            PolyMem (sp + 19168#64) (polyVecNat r0) ∗
            PolyMem (sp + 19680#64) (polyVecNat r1) ∗
            PolyMem (sp + 20192#64) (polyVecNat r2) ∗
            PolyMem e1Ptr (polyVecNat e1) ∗ Poly32Mem (sp + 11856#64) v11856' ∗
            Spill6Mem (sp + 1824#64) t6' ∗ Spill21Mem (sp + 1920#64) t21' ∗ Rest)) := by
  intro polyPtr e1Ptr r0 r1 r2 e1
  set lhsBase := sp + BitVec.ofNat 64 (7216 + 1536 * i)
  set l0 := aTransPoly16 rho i 0
  set l1 := aTransPoly16 rho i 1
  set l2 := aTransPoly16 rho i 2
  set dot := neonDot3 l0 l1 l2 r0 r1 r2
  have hdot_sz : dot.size = 256 := neonDot3_size l0 l1 l2 r0 r1 r2
  have hl1 : sp + BitVec.ofNat 64 (7216 + 1536 * i + 512) = lhsBase + 512#64 := by
    dsimp only [lhsBase]; clear * - hi; bv_omega
  have hl2 : sp + BitVec.ofNat 64 (7216 + 1536 * i + 1024) = lhsBase + 1024#64 := by
    dsimp only [lhsBase]; clear * - hi; bv_omega
  have hr1 : sp + 19680#64 = (sp + 19168#64) + 512#64 := by clear * -; bv_omega
  have hr2 : sp + 20192#64 = (sp + 19168#64) + 1024#64 := by clear * -; bv_omega
  have hpres0 : Dot2Preserved s s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SepWP.weaken_pre
    (P' := Poly32Mem polyPtr Vec32.zero ∗
      PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
      PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
      PolyMem (sp + 19168#64) (polyVecNat r0) ∗ PolyMem ((sp + 19168#64) + 512#64) (polyVecNat r1) ∗
      PolyMem ((sp + 19168#64) + 1024#64) (polyVecNat r2) ∗
      Poly32Mem (sp + 11856#64) v11856 ∗
      (PolyMem e1Ptr (polyVecNat e1) ∗
        Spill6Mem (sp + 1824#64) t6 ∗ Spill21Mem (sp + 1920#64) t21 ∗ Rest))
    (by
      dsimp only [ATransRowMemAt, lhsBase, l0, l1, l2] at hl1 hl2 ⊢
      rw [polyMem_zero_eq_poly32Mem, hl1, hl2, hr1, hr2]; sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (dot2_ok hb s s sp (sp + 22400#64) polyPtr lhsBase (sp + 19168#64) hi
      (by dsimp only [polyPtr]; clear * - hi; bv_omega)
      l0 l1 l2 r0 r1 r2 v11856 _
      hpc hrun hinv.hsp hinv.hspA hcl hro hinv.hx3 hinv.hx11 hinv.hx13 hinv.hx15 hinv.hx16
      hinv.hx17 hinv.hx20 hinv.hx28 hinv.hv0 hpres0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx11_1, hx26_1, hv16_1, hv18_1, hdp1, rfl⟩
  set v11856' := Vec32.ofFn (polyVecNat (neonPolyNttMul16 l2 r2))
  refine sepWP_seq_env hcl1 hro1
    (inv2_low_ok hb s1 sp polyPtr (sp + 22400#64) (BitVec.ofNat 64 (16 + 512 * i))
      (by dsimp only [polyPtr]; clear * - hi; bv_omega) hdot_sz _
      hpc1 hrun1 hsp1 hspA1 hcl1 hro1 (hdp1.x0.trans hinv.hx0)
      (by rw [hdp1.x8, hinv.hx8]; dsimp only [polyPtr]; clear * - hi; bv_omega)
      (hdp1.x10.trans hinv.hx10) (hdp1.x20.trans hinv.hx20)
      hv16_1 hv18_1 (hdp1.v23.trans hinv.hv23) (hdp1.v27.trans hinv.hv27)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hv16_2, hv17_2, _, hv23_2, hv27_2, hip2, rfl⟩
  refine SepWP.weaken_pre
    (P' := PolyMem polyPtr (polyVecNat (lowerInvNtt16 dot)) ∗
      Spill6Mem (sp + 1824#64) t6 ∗ Spill21Mem (sp + 1920#64) t21 ∗
      (PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem (sp + 19168#64) (polyVecNat r0) ∗ PolyMem ((sp + 19168#64) + 512#64) (polyVecNat r1) ∗
        PolyMem ((sp + 19168#64) + 1024#64) (polyVecNat r2) ∗
        Poly32Mem (sp + 11856#64) v11856' ∗ PolyMem e1Ptr (polyVecNat e1) ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg7_upper_inv2 s2 hdot_sz t6 t21 _ hpc2 hrun2 hsp2 hspA2 (hip2.x26.trans hx26_1)
      hv16_2 hv17_2 hv23_2 hv27_2
      (hip2.x21.trans (hdp1.x21.trans hinv.hx21))
      (hip2.x22.trans (hdp1.x22.trans hinv.hx22))) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx12_3, hx27_3, hgpr3, hv0_3, hv16_3, hv17_3, hv23_3, hv27_3, t6', t21', rfl⟩
  have hx0_3  : s3.readReg64 .x0  = 20159#64 := (hgpr3 0#5 (by decide) (by decide) (by decide)).trans (hip2.x0.trans (hdp1.x0.trans hinv.hx0))
  have hx3_3  : s3.readReg64 .x3  = mlkemMpl.ρ ro00Sym + 134#64 := (hgpr3 3#5 (by decide) (by decide) (by decide)).trans (hip2.x3.trans (hdp1.x3.trans hinv.hx3))
  have hx8_3  : s3.readReg64 .x8  = sp + BitVec.ofNat 64 (22416 + 512 * i) := (hgpr3 8#5 (by decide) (by decide) (by decide)).trans (hip2.x8.trans (hdp1.x8.trans hinv.hx8))
  have hx9_3  : s3.readReg64 .x9  = e1Ptr := (hgpr3 9#5 (by decide) (by decide) (by decide)).trans (hip2.x9.trans (hdp1.x9.trans hinv.hx9))
  have hx10_3 : s3.readReg64 .x10 = BitVec.ofNat 64 (16 + 512 * i) := (hgpr3 10#5 (by decide) (by decide) (by decide)).trans (hip2.x10.trans (hdp1.x10.trans hinv.hx10))
  have hx11_3 : s3.readReg64 .x11 = BitVec.ofNat 64 (i + 1) := (hgpr3 11#5 (by decide) (by decide) (by decide)).trans (hip2.x11.trans hx11_1)
  have hx13_3 : s3.readReg64 .x13 = sp + 19168#64 := (hgpr3 13#5 (by decide) (by decide) (by decide)).trans (hip2.x13.trans (hdp1.x13.trans hinv.hx13))
  have hx15_3 : s3.readReg64 .x15 = 62209#64 := (hgpr3 15#5 (by decide) (by decide) (by decide)).trans (hip2.x15.trans (hdp1.x15.trans hinv.hx15))
  have hx16_3 : s3.readReg64 .x16 = 3329#64 := (hgpr3 16#5 (by decide) (by decide) (by decide)).trans (hip2.x16.trans (hdp1.x16.trans hinv.hx16))
  have hx17_3 : s3.readReg64 .x17 = sp + 11856#64 := (hgpr3 17#5 (by decide) (by decide) (by decide)).trans (hip2.x17.trans (hdp1.x17.trans hinv.hx17))
  have hx19_3 : s3.readReg64 .x19 = BitVec.ofNat 64 (1536 * (i + 1)) := (hgpr3 19#5 (by decide) (by decide) (by decide)).trans (hip2.x19.trans (hdp1.x19.trans hinv.hx19))
  have hx20_3 : s3.readReg64 .x20 = sp + 22400#64 := (hgpr3 20#5 (by decide) (by decide) (by decide)).trans (hip2.x20.trans (hdp1.x20.trans hinv.hx20))
  have hx21_3 : s3.readReg64 .x21 = 64778#64 := (hgpr3 21#5 (by decide) (by decide) (by decide)).trans (hip2.x21.trans (hdp1.x21.trans hinv.hx21))
  have hx22_3 : s3.readReg64 .x22 = 31498#64 := (hgpr3 22#5 (by decide) (by decide) (by decide)).trans (hip2.x22.trans (hdp1.x22.trans hinv.hx22))
  have hx23_3 : s3.readReg64 .x23 = 1441#64 := (hgpr3 23#5 (by decide) (by decide) (by decide)).trans (hip2.x23.trans (hdp1.x23.trans hinv.hx23))
  have hx24_3 : s3.readReg64 .x24 = 55457#64 := (hgpr3 24#5 (by decide) (by decide) (by decide)).trans (hip2.x24.trans (hdp1.x24.trans hinv.hx24))
  have hx25_3 : s3.readReg64 .x25 = 6144#64 := (hgpr3 25#5 (by decide) (by decide) (by decide)).trans (hip2.x25.trans (hdp1.x25.trans hinv.hx25))
  have hx28_3 : s3.readReg64 .x28 = lhsBase := (hgpr3 28#5 (by decide) (by decide) (by decide)).trans (hip2.x28.trans (hdp1.x28.trans hinv.hx28))
  have hfp_3  : s3.readReg64 .fp  = fpVal := (hgpr3 29#5 (by decide) (by decide) (by decide)).trans (hip2.fp.trans (hdp1.fp.trans hinv.hfp))
  have hv0_3' : s3.readVReg128 0#5 = 0#128 := hv0_3.trans (hip2.v0.trans (hdp1.v0.trans hinv.hv0))
  have hx12_3' : s3.readReg64 .x12 = polyPtr + 16#64 := by
    rw [hx12_3, hip2.x20.trans (hdp1.x20.trans hinv.hx20), hip2.x10.trans (hdp1.x10.trans hinv.hx10)]
    dsimp only [polyPtr]; clear * - hi; bv_omega
  have hpres3 : Seg7AddPreserved s3 s3 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SepWP.weaken_pre
    (P' := PolyMem polyPtr (polyVecNat (neonInvNttMontgomery16 dot)) ∗ PolyMem e1Ptr (polyVecNat e1) ∗
      (Spill6Mem (sp + 1824#64) t6' ∗ Spill21Mem (sp + 1920#64) t21' ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem (sp + 19168#64) (polyVecNat r0) ∗ PolyMem ((sp + 19168#64) + 512#64) (polyVecNat r1) ∗
        PolyMem ((sp + 19168#64) + 1024#64) (polyVecNat r2) ∗
        Poly32Mem (sp + 11856#64) v11856' ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl3 hro3
    (seg7_add_ok hb s3 s3 sp polyPtr e1Ptr (neonInvNttMontgomery16 dot) e1 _
      hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx9_3 hx12_3' hx23_3 hx24_3 hx27_3 hv16_3 hv17_3 hv23_3 hv27_3 hpres3) ?_
  rintro s4 P4 hpc4 hrun4 _ _ ⟨hsp4, hspA4, hap4, rfl⟩
  refine SepWP.mono (seg7_outer_tail hb s4 hi _ hpc4 hrun4 (hap4.x19.trans hx19_3) (hap4.x25.trans hx25_3)) ?_
  rintro sf Pf _ _ ⟨hspf, hspAf, hvregf, hx8f, hx9f, hx10f, hx19f, hx28f, hgprf, hfpf, rfl⟩
  refine ⟨⟨hspf.trans hsp4, hspAf.trans hspA4, hfpf.trans (hap4.fp.trans hfp_3),
    (hgprf 0#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x0.trans hx0_3),
    (hgprf 3#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x3.trans hx3_3),
    by rw [hx8f, hap4.x8, hx8_3]; clear * - hi; bv_omega,
    by rw [hx9f, hap4.x9, hx9_3]; dsimp only [e1Ptr]; clear * - hi; bv_omega,
    by rw [hx10f, hap4.x10, hx10_3]; clear * - hi; bv_omega,
    (hgprf 11#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x11.trans hx11_3),
    (hgprf 13#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x13.trans hx13_3),
    (hgprf 15#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x15.trans hx15_3),
    (hgprf 16#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x16.trans hx16_3),
    (hgprf 17#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x17.trans hx17_3),
    hx19f,
    (hgprf 20#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x20.trans hx20_3),
    (hgprf 21#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x21.trans hx21_3),
    (hgprf 22#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x22.trans hx22_3),
    (hgprf 23#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x23.trans hx23_3),
    (hgprf 24#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x24.trans hx24_3),
    (hgprf 25#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hap4.x25.trans hx25_3),
    by rw [hx28f, hap4.x28, hx28_3]; dsimp only [lhsBase]; clear * - hi; bv_omega,
    (congrArg (fun v => v.read 0#5) hvregf).trans (hap4.v0.trans hv0_3'),
    (congrArg (fun v => v.read 23#5) hvregf).trans (hap4.v23.trans hv23_3),
    (congrArg (fun v => v.read 27#5) hvregf).trans (hap4.v27.trans hv27_3)⟩,
    v11856', t6', t21', ?_⟩
  dsimp only [ATransRowMemAt, uVecPoly16, dot, l0, l1, l2, r0, r1, r2, e1, lhsBase] at hl1 hl2 ⊢
  rw [hl1, hl2, hr1, hr2]
  exact sepProp_ext (by sep_frame) (by sep_frame)

theorem polyMem3_eq_pointsToBytes (ptr : BitVec 64) (f0 f1 f2 : Nat → BitVec 128) :
    PolyMem ptr f0 ∗ PolyMem (ptr + 512#64) f1 ∗ PolyMem (ptr + 1024#64) f2 =
      (ptr ↦ₛ (vecRangeBytes 32 f0 ++ (vecRangeBytes 32 f1 ++ vecRangeBytes 32 f2))) := by
  unfold PolyMem
  have h1 : ptr + BitVec.ofNat 64 (16 * 32) = ptr + 512#64 := by clear * -; bv_omega
  have h2 : (ptr + 512#64) + BitVec.ofNat 64 (16 * 32) = ptr + 1024#64 := by clear * -; bv_omega
  rw [pointsToBytes_append, vecRangeBytes_length, h1,
      pointsToBytes_append, vecRangeBytes_length, h2,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes]

private theorem seg7_copy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal : BitVec 64) (u0 u1 u2 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Copy) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7SerStart) s
      (PolyMem (sp + 22400#64) (polyVecNat u0) ∗
        PolyMem (sp + 22912#64) (polyVecNat u1) ∗
        PolyMem (sp + 23424#64) (polyVecNat u2) ∗
        memRegion (sp + 11872#64) 1536 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 22400#64 ∧
        sf.readReg64 .x20 = sp + 11872#64 ∧
        (Pf ⊢ PolyMem (sp + 11872#64) (polyVecNat u0) ∗
          PolyMem (sp + 12384#64) (polyVecNat u1) ∗
          PolyMem (sp + 12896#64) (polyVecNat u2) ∗
          PolyMem (sp + 22400#64) (polyVecNat u0) ∗
          PolyMem (sp + 22912#64) (polyVecNat u1) ∗
          PolyMem (sp + 23424#64) (polyVecNat u2) ∗ Rest)) := by
  subst hbase
  have ha1 : sp + 22912#64 = (sp + 22400#64) + 512#64 := by clear * -; bv_omega
  have ha2 : sp + 23424#64 = (sp + 22400#64) + 1024#64 := by clear * -; bv_omega
  have hb1 : (sp + 11872#64) + 512#64 = sp + 12384#64 := by clear * -; bv_omega
  have hb2 : (sp + 11872#64) + 1024#64 = sp + 12896#64 := by clear * -; bv_omega
  set bs := vecRangeBytes 32 (polyVecNat u0) ++
    (vecRangeBytes 32 (polyVecNat u1) ++ vecRangeBytes 32 (polyVecNat u2))
  have hbs : bs.length = 1536 := by
    simp [bs, List.length_append, vecRangeBytes_length]
  refine SepWP.weaken_pre
    (P' := ((sp + 22400#64) ↦ₛ bs) ∗ memRegion (sp + 11872#64) 1536 ∗ Rest)
    (by
      rw [← polyMem3_eq_pointsToBytes (sp + 22400#64), ← ha1, ← ha2]
      sep_frame) ?_
  wp_steps 9; wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 11872#64, sp + 22400#64, bs)
  apply SepWP.done (by assumption) (by assumption); intro _
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, spAligned_of_sp_eq hspA hsp (hsp_sf.trans hsp),
      hcs_sf.trans hfp, ‹_›, ‹_›, ?_⟩
  have h1 : ((sp + 11872#64) ↦ₛ bs) =
      PolyMem (sp + 11872#64) (polyVecNat u0) ∗
      PolyMem (sp + 12384#64) (polyVecNat u1) ∗
      PolyMem (sp + 12896#64) (polyVecNat u2) := by
    rw [← hb1, ← hb2, polyMem3_eq_pointsToBytes]
  have h2 : ((sp + 22400#64) ↦ₛ bs) =
      PolyMem (sp + 22400#64) (polyVecNat u0) ∗
      PolyMem (sp + 22912#64) (polyVecNat u1) ∗
      PolyMem (sp + 23424#64) (polyVecNat u2) := by
    rw [ha1, ha2, polyMem3_eq_pointsToBytes]
  rw [h1, h2]
  sep_frame


/-- Full `u'[0..2]` sub-segment (`+0x8d00 → +0xa968`). -/
theorem seg7a_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal : BitVec 64) (rho coins : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = 1536#64) (hx20 : s.readReg64 .x20 = sp + 22400#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let e1_0 := neonCbd2Poly16 (shake256List 128 (coins ++ [3#8]))
    let e1_1 := neonCbd2Poly16 (shake256List 128 (coins ++ [4#8]))
    let e1_2 := neonCbd2Poly16 (shake256List 128 (coins ++ [5#8]))
    let u0 := uVecPoly16 rho coins 0
    let u1 := uVecPoly16 rho coins 1
    let u2 := uVecPoly16 rho coins 2
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7SerStart) s
      (memRegion (sp + 1824#64) 432 ∗ ATransMemAt sp 7216 rho ∗
        memRegion (sp + 11856#64) 1552 ∗
        PolyMem (sp + 19168#64) (polyVecNat r0) ∗
        PolyMem (sp + 19680#64) (polyVecNat r1) ∗
        PolyMem (sp + 20192#64) (polyVecNat r2) ∗
        PolyMem (sp + 20704#64) (polyVecNat e1_0) ∗
        PolyMem (sp + 21216#64) (polyVecNat e1_1) ∗
        PolyMem (sp + 21728#64) (polyVecNat e1_2) ∗
        PolyMem (sp + 22400#64) (fun _ => 0#128) ∗
        PolyMem (sp + 22912#64) (fun _ => 0#128) ∗
        PolyMem (sp + 23424#64) (fun _ => 0#128) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 22400#64 ∧
        sf.readReg64 .x20 = sp + 11872#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ memRegion (sp + 1824#64) 432 ∗ ATransMemAt sp 7216 rho ∗
          memRegion (sp + 11856#64) 16 ∗
          PolyMem (sp + 11872#64) (polyVecNat u0) ∗
          PolyMem (sp + 12384#64) (polyVecNat u1) ∗
          PolyMem (sp + 12896#64) (polyVecNat u2) ∗
          PolyMem (sp + 19168#64) (polyVecNat r0) ∗
          PolyMem (sp + 19680#64) (polyVecNat r1) ∗
          PolyMem (sp + 20192#64) (polyVecNat r2) ∗
          PolyMem (sp + 20704#64) (polyVecNat e1_0) ∗
          PolyMem (sp + 21216#64) (polyVecNat e1_1) ∗
          PolyMem (sp + 21728#64) (polyVecNat e1_2) ∗
          PolyMem (sp + 22400#64) (polyVecNat u0) ∗
          PolyMem (sp + 22912#64) (polyVecNat u1) ∗
          PolyMem (sp + 23424#64) (polyVecNat u2) ∗ Rest)) := by
  intro r0 r1 r2 e1_0 e1_1 e1_2 u0 u1 u2
  have hm432 : memRegion (sp + 1824#64) 432 = memRegion (sp + 1824#64) 96 ∗ memRegion (sp + 1920#64) 336 :=
    memRegion_split' (b := sp + 1824#64) (b' := sp + 1920#64) (n := 96) (k := (336 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  have hm1552a : memRegion (sp + 11856#64) 1552 = memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 12368#64) 1040 :=
    memRegion_split' (b := sp + 11856#64) (b' := sp + 12368#64) (n := 512) (k := (1040 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  have hm1552b : memRegion (sp + 11856#64) 1552 = memRegion (sp + 11856#64) 16 ∗ memRegion (sp + 11872#64) 1536 :=
    memRegion_split' (b := sp + 11856#64) (b' := sp + 11872#64) (n := 16) (k := (1536 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  rw [hm432, hm1552a]
  apply SepWP.of_memRegion_vecRangeMem 6 (sp + 1824#64) (by decide) (by sep_focus); intro f6
  apply SepWP.of_memRegion_vecRangeMem 21 (sp + 1920#64) (by decide) (by sep_focus); intro f21
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 11856#64) (by decide) (by sep_focus); intro f11856
  have hp11856 : VecRangeMem 32 (sp + 11856#64) f11856 =
      Poly32Mem (sp + 11856#64) (Vec32.ofFn f11856) := (poly32Mem_ofFn (sp + 11856#64) f11856).symm
  rw [← spill6Mem_ofFn (sp + 1824#64) f6, ← spill21Mem_ofFn (sp + 1920#64) f21, hp11856]
  refine sepWP_seq_env hcl hro (seg7_setup hb s sp fpVal _ hpc hrun hsp hspA hfp hx19 hx20) ?_
  rintro s0 P0 hpc0 hrun0 hcl0 hro0 ⟨hinv0, rfl⟩
  set R0 := ATransRowMemAt sp 7216 rho 1 ∗ ATransRowMemAt sp 7216 rho 2 ∗ memRegion (sp + 12368#64) 1040 ∗
    PolyMem (sp + 21216#64) (polyVecNat e1_1) ∗ PolyMem (sp + 21728#64) (polyVecNat e1_2) ∗
    PolyMem (sp + 22912#64) (fun _ => 0#128) ∗ PolyMem (sp + 23424#64) (fun _ => 0#128) ∗ Rest
  refine SepWP.weaken_pre
    (P' := PolyMem (sp + 22400#64) (fun _ => 0#128) ∗
      ATransRowMemAt sp 7216 rho 0 ∗
      PolyMem (sp + 19168#64) (polyVecNat r0) ∗ PolyMem (sp + 19680#64) (polyVecNat r1) ∗
      PolyMem (sp + 20192#64) (polyVecNat r2) ∗
      PolyMem (sp + 20704#64) (polyVecNat e1_0) ∗
      Poly32Mem (sp + 11856#64) (Vec32.ofFn f11856) ∗
      Spill6Mem (sp + 1824#64) (Spill6.ofFn f6) ∗ Spill21Mem (sp + 1920#64) (Spill21.ofFn f21) ∗ R0)
    (by dsimp only [ATransMemAt, R0]; sep_frame) ?_
  have hr0 := seg7_row hb s0 sp fpVal (i := 0) (by decide) rho coins
    (Vec32.ofFn f11856) (Spill6.ofFn f6) (Spill21.ofFn f21) R0 hpc0 hrun0 hcl0 hro0 hinv0
  dsimp only at hr0
  simp only [Nat.zero_lt_two, ↓reduceIte,
    show BitVec.ofNat 64 (22400 + 512 * 0) = 22400#64 from rfl,
    show BitVec.ofNat 64 (20704 + 512 * 0) = 20704#64 from rfl] at hr0
  refine sepWP_seq_env hcl0 hro0 hr0 ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hinv1, v1, t6_1, t21_1, rfl⟩
  set R1 := PolyMem (sp + 22400#64) (polyVecNat u0) ∗ ATransRowMemAt sp 7216 rho 0 ∗
    ATransRowMemAt sp 7216 rho 2 ∗ memRegion (sp + 12368#64) 1040 ∗
    PolyMem (sp + 20704#64) (polyVecNat e1_0) ∗ PolyMem (sp + 21728#64) (polyVecNat e1_2) ∗
    PolyMem (sp + 23424#64) (fun _ => 0#128) ∗ Rest
  refine SepWP.weaken_pre
    (P' := PolyMem (sp + 22912#64) (fun _ => 0#128) ∗
      ATransRowMemAt sp 7216 rho 1 ∗
      PolyMem (sp + 19168#64) (polyVecNat r0) ∗ PolyMem (sp + 19680#64) (polyVecNat r1) ∗
      PolyMem (sp + 20192#64) (polyVecNat r2) ∗
      PolyMem (sp + 21216#64) (polyVecNat e1_1) ∗
      Poly32Mem (sp + 11856#64) v1 ∗ Spill6Mem (sp + 1824#64) t6_1 ∗ Spill21Mem (sp + 1920#64) t21_1 ∗ R1)
    (by dsimp only [R0, R1]; sep_frame) ?_
  have hr1 := seg7_row hb s1 sp fpVal (i := 1) (by decide) rho coins v1 t6_1 t21_1 R1
    hpc1 hrun1 hcl1 hro1 hinv1
  dsimp only at hr1
  simp only [Nat.one_lt_two, ↓reduceIte,
    show BitVec.ofNat 64 (22400 + 512 * 1) = 22912#64 from rfl,
    show BitVec.ofNat 64 (20704 + 512 * 1) = 21216#64 from rfl] at hr1
  refine sepWP_seq_env hcl1 hro1 hr1 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hinv2, v2, t6_2, t21_2, rfl⟩
  set R2 := PolyMem (sp + 22400#64) (polyVecNat u0) ∗ PolyMem (sp + 22912#64) (polyVecNat u1) ∗
    ATransRowMemAt sp 7216 rho 0 ∗ ATransRowMemAt sp 7216 rho 1 ∗ memRegion (sp + 12368#64) 1040 ∗
    PolyMem (sp + 20704#64) (polyVecNat e1_0) ∗ PolyMem (sp + 21216#64) (polyVecNat e1_1) ∗ Rest
  refine SepWP.weaken_pre
    (P' := PolyMem (sp + 23424#64) (fun _ => 0#128) ∗
      ATransRowMemAt sp 7216 rho 2 ∗
      PolyMem (sp + 19168#64) (polyVecNat r0) ∗ PolyMem (sp + 19680#64) (polyVecNat r1) ∗
      PolyMem (sp + 20192#64) (polyVecNat r2) ∗
      PolyMem (sp + 21728#64) (polyVecNat e1_2) ∗
      Poly32Mem (sp + 11856#64) v2 ∗ Spill6Mem (sp + 1824#64) t6_2 ∗ Spill21Mem (sp + 1920#64) t21_2 ∗ R2)
    (by dsimp only [R1, R2]; sep_frame) ?_
  have hr2 := seg7_row hb s2 sp fpVal (i := 2) (by decide) rho coins v2 t6_2 t21_2 R2
    hpc2 hrun2 hcl2 hro2 hinv2
  dsimp only at hr2
  simp only [Nat.lt_irrefl, ↓reduceIte,
    show BitVec.ofNat 64 (22400 + 512 * 2) = 23424#64 from rfl,
    show BitVec.ofNat 64 (20704 + 512 * 2) = 21728#64 from rfl] at hr2
  refine sepWP_seq_env hcl2 hro2 hr2 ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hinv3, v3, t6_3, t21_3, hP3⟩
  have hm_copy : P3 ⊢ PolyMem (sp + 22400#64) (polyVecNat u0) ∗
      PolyMem (sp + 22912#64) (polyVecNat u1) ∗ PolyMem (sp + 23424#64) (polyVecNat u2) ∗
      memRegion (sp + 11872#64) 1536 ∗
      (memRegion (sp + 1824#64) 432 ∗ ATransMemAt sp 7216 rho ∗ memRegion (sp + 11856#64) 16 ∗
        PolyMem (sp + 19168#64) (polyVecNat r0) ∗ PolyMem (sp + 19680#64) (polyVecNat r1) ∗
        PolyMem (sp + 20192#64) (polyVecNat r2) ∗
        PolyMem (sp + 20704#64) (polyVecNat e1_0) ∗ PolyMem (sp + 21216#64) (polyVecNat e1_1) ∗
        PolyMem (sp + 21728#64) (polyVecNat e1_2) ∗ Rest) := by
    subst hP3
    have hm11856 : Poly32Mem (sp + 11856#64) v3 ∗ memRegion (sp + 12368#64) 1040 ⊢
        memRegion (sp + 11856#64) 16 ∗ memRegion (sp + 11872#64) 1536 := by
      rw [← hm1552b, hm1552a]
      exact sepConj_mono_left (poly32Mem_entails_memRegion (sp + 11856#64) v3)
    have hm432' : Spill6Mem (sp + 1824#64) t6_3 ∗ Spill21Mem (sp + 1920#64) t21_3 ⊢
        memRegion (sp + 1824#64) 432 := by
      rw [hm432]
      exact sepConj_mono (spill6Mem_entails_memRegion _ _) (spill21Mem_entails_memRegion _ _)
    dsimp only [R2]
    exact entails_sub hm11856 (by sep_frame)
      (entails_sub hm432' (by sep_frame) (by dsimp only [ATransMemAt]; sep_frame))
  refine SepWP.weaken_pre hm_copy ?_
  refine sepWP_seq_env hcl3 hro3
    (seg7_copy hb hbase s3 sp fpVal u0 u1 u2 _ hpc3 hrun3 hinv3.hsp hinv3.hspA hinv3.hfp hcl3) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hfpf, hx19f, hx20f, hPf⟩
  exact SepWP.done hpcf hrunf ⟨hspf, hspAf, hfpf, hx19f, hx20f, hclf, hrof, Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7a

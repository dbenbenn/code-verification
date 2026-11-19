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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8a -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops3
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Inv3LowLoops
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv3a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv3b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv3c

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 8b (`+0xb190 .. +0xcfb4`)

Composes `DotLoops3` (`t̂ · r̂`), `Inv3LowLoops`, `SymEvalInv3{a,b,c}`, `B28` (`memcpy` of `inv`
from `sp + 20704` to `sp + 23936`), and the 16-iteration post-`inv_ntt` normalizer + `e₂` +
`msgPoly` + Barrett loop producing `seg5FinalPoly inv e₂ msgPoly` in `[sp + 23936 .. sp + 24448)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8b

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 neonInvNttMontgomery16 neonPolyNttMul16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMla8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 Spill13 Vec32 poly32Mem_entails_memRegion poly32Mem_ofFn
  polyVecNat step_ldpQ128 step_ldrQ128 step_stpQ128 vecRangeBytes vecRangeBytes_length
  vecRangeMem_congr vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16 lowerInvNtt16_size neonDot3 neonDot3_size polyZero16 upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (AccRegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  exec_simdAdd_8h exec_simdDup_8h_gpr exec_simdMla_8h exec_simdMovi_8h_1024
  exec_simdMul_8h exec_simdMvni_8h_f2ff exec_simdSqdmulh_8h exec_simdSshr_8h_1
  exec_simdSshr_8h_11 exec_simdSub_8h sqdmulh8hFlags)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (
  seg5FinalPoly seg5Loop1_vec_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  SepLoad128.spill21 Spill21 Spill21Mem Spill6 spill21Mem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a (sepWP_elim_poly32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1 (AccSpill21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops3 (
  Dot3Preserved dot3_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Inv3LowLoops (inv3_low_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops (Inv13Preserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8a (offSeg8Dot ro00Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (
  runSymRange_add symInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval (
  SymSpatial evalSExpr evalSymSpill21 symEnvOf symInit_matches)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyBridge (InSymWord04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly (sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge (
  symPoly_eq_upperInvNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv3a (cfgInv3 run_inv3a)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv3b (run_inv3b)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv3c (
  inv3_ast_eq inv3_noSpillVreg run_inv3c symInv3End)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0xceec → 0xcfb0]
end

private theorem blk28_memcpy_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk28_memcpy_ok

attribute [local irreducible] blkPC04

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

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
      (s.writeVReg128 rd (dup8x16 1024#16)).advancePC := exec_simdMovi_8h_1024 rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdMvni_8h_f2ff' {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b10100#5 13#5 rd) s =
      (s.writeVReg128 rd (dup8x16 0xf2ff#16)).advancePC := exec_simdMvni_8h_f2ff rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdDup_8h_gpr' {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 0b00010#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd (dup8x16 ((s.readReg64 (Reg.fromZRBits rn)).truncate 16))).advancePC :=
  exec_simdDup_8h_gpr rn rd s

attribute [local wp_norm ↓ high]
  exec_simdAdd_8h' exec_simdSub_8h' exec_simdMul_8h' exec_simdMla_8h'
  exec_simdSqdmulh_8h' exec_simdSshr_8h_1' exec_simdSshr_8h_11'
  exec_simdMovi_8h_1024' exec_simdMvni_8h_f2ff' exec_simdDup_8h_gpr'

@[simp, arm64_norm, wp_norm] abbrev offB540 : BitVec 64 := BitVec.ofNat 64 46400
@[simp, arm64_norm, wp_norm] abbrev offB68c : BitVec 64 := BitVec.ofNat 64 46732
@[simp, arm64_norm, wp_norm] abbrev offCeec : BitVec 64 := BitVec.ofNat 64 52972
@[simp, arm64_norm, wp_norm] abbrev offCef0 : BitVec 64 := BitVec.ofNat 64 52976
@[simp, arm64_norm, wp_norm] abbrev offCf28 : BitVec 64 := BitVec.ofNat 64 53032
@[simp, arm64_norm, wp_norm] abbrev offSeg8bEnd : BitVec 64 := BitVec.ofNat 64 53172

/-! ## 1. Upper 5-Stage Symbolic `InvNTT3` (`+0xb68c → +0xceec`) & `memcpy` (`+0xceec → +0xcef0`) -/

private theorem run_inv3_full :
    SymPolyDefs.runSymRange cfgInv3 11683 1560 symInit = some symInv3End :=
  runSymRange_add cfgInv3 11683 1040 520 _ _ _
    (runSymRange_add cfgInv3 11683 520 520 _ _ _ run_inv3a run_inv3b)
    run_inv3c

private theorem inSym_inv3 (j : Nat) (h1 : 11683 ≤ j) (h2 : j < 11683 + 1560) : InSymWord04 j :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩))))))

private theorem seg8b_inv3_sym [MlKemPlacement] {b : BitVec 64}
    (s : State) (sp : BitVec 64) {dot : Poly16} (hdot : dot.size = 256)
    (tSpill : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + offB68c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offCeec) s
      (PolyMem (sp + 20704#64) (polyVecNat (lowerInvNtt16 dot)) ∗
        Spill21Mem (sp + 1920#64) tSpill ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = sp + 23936#64 ∧ sf.readReg64 .x1 = sp + 20704#64 ∧
        sf.readReg64 .x2 = 512#64 ∧ sf.readReg64 .x19 = sp + 23936#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        ∃ tOut : Spill21,
          tOut.s14 = dup8x16 20159#16 ∧ tOut.s19 = dup8x16 3329#16 ∧
          (Pf ⊢ PolyMem (sp + 20704#64) (polyVecNat (neonInvNttMontgomery16 dot)) ∗
            Spill21Mem (sp + 1920#64) tOut ∗ Rest)) := by
  let poly0 := Vec32.ofFn (polyVecNat (lowerInvNtt16 dot))
  let env := symEnvOf s Spill13.zero Spill6.zero tSpill poly0 Vec32.zero
  obtain ⟨hm0, _, _, hsp21_0, hpoly0⟩ := symInit_matches cfgInv3 s sp 0#64
    Spill13.zero Spill6.zero tSpill poly0 Vec32.zero hsp hspA (by rintro _ ⟨⟩)
  have hpre : PolyMem (sp + 20704#64) (polyVecNat (lowerInvNtt16 dot)) ∗
      Spill21Mem (sp + 1920#64) tSpill ∗ Rest ⊢
      SymSpatial cfgInv3 sp 0#64 env symInit Rest := by
    dsimp only [SymSpatial, SymPolyEval.polyAddr, cfgInv3, SymPolyEval.spillMemAt,
      SymPolyEval.inPolyMemAt]
    rw [hpoly0, hsp21_0, poly32Mem_ofFn]; dsimp only [PolyMem]; sep_frame
  refine SepWP.weaken_pre hpre
    (sepWP_of_runSymRange 1560 11683 inSym_inv3 run_inv3_full hm0 hpc hrun ?_)
  intro sf _ _ hmf
  have hgpr := hmf.hgprs
  have hg0 : sf.readReg64 .x0 = (sp + 20480#64) + 3456#64 := hgpr 0#5 (by decide)
  have hg1 : sf.readReg64 .x1 = (sp + 20480#64) + 224#64 := hgpr 1#5 (by decide)
  have hg2 : sf.readReg64 .x2 = 512#64 := hgpr 2#5 (by decide)
  have hg19 : sf.readReg64 .x19 = (sp + 20480#64) + 3456#64 := hgpr 19#5 (by decide)
  have hg29 : sf.readReg64 .fp = s.readReg64 .fp := hgpr 29#5 (by decide)
  refine ⟨hmf.hsp, hmf.hsp_al,
    by rw [hg0]; clear * -; bv_omega, by rw [hg1]; clear * -; bv_omega, hg2,
    by rw [hg19]; clear * -; bv_omega, hg29,
    evalSymSpill21 env symInv3End.spill21,
    by simp [evalSymSpill21, symInv3End, evalSExpr],
    by simp [evalSymSpill21, symInv3End, evalSExpr], ?_⟩
  dsimp only [SymSpatial, SymPolyEval.polyAddr, cfgInv3, SymPolyEval.spillMemAt,
    SymPolyEval.inPolyMemAt]
  have hpoly_eq := symPoly_eq_upperInvNtt (sp + 20704#64) symInv3End.poly
    (lowerInvNtt16_size hdot) env rfl inv3_noSpillVreg inv3_ast_eq
  rw [hpoly_eq, upperInvNtt16_lowerInvNtt16]
  sep_frame


private theorem seg8b_memcpy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) (inv : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offCeec) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 23936#64) (hx1 : s.readReg64 .x1 = sp + 20704#64)
    (hx2 : s.readReg64 .x2 = 512#64) (hx19 : s.readReg64 .x19 = sp + 23936#64)
    (hfp : s.readReg64 .fp = fpVal) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offCef0) s
      (PolyMem (sp + 20704#64) (polyVecNat inv) ∗ memRegion (sp + 23936#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 23936#64 ∧ sf.readReg64 .fp = fpVal ∧
        Pf = (PolyMem (sp + 20704#64) (polyVecNat inv) ∗
          PolyMem (sp + 23936#64) (polyVecNat inv) ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs_def : vecRangeBytes 32 (polyVecNat inv) = bsInv
  have hbs : bsInv.length = 512 := by rw [← hbs_def, vecRangeBytes_length]
  have hp20704 : PolyMem (sp + 20704#64) (polyVecNat inv) = ((sp + 20704#64) ↦ₛ bsInv) := by
    rw [← hbs_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp23936 : ((sp + 23936#64) ↦ₛ bsInv) = PolyMem (sp + 23936#64) (polyVecNat inv) := by
    rw [← hbs_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  rw [hp20704]
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 23936#64, sp + 20704#64, bsInv)
  rw [← hp20704, hp23936]
  have hsp_sf : sf.sp = sp := by simp [*]
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*], by simp [*],
      sepProp_ext (by sep_frame) (by sep_frame)⟩

private theorem seg8b_setup [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) (spill : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + offCef0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = sp + 23936#64) (hfp : s.readReg64 .fp = fpVal)
    (hs14 : spill.s14 = dup8x16 20159#16) (hs19 : spill.s19 = dup8x16 3329#16) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offCf28) s
      (Spill21Mem (sp + 1920#64) spill ∗ Rest)
      (fun s5 P5 =>
        s5.sp = sp ∧ s5.spAligned = true ∧
        s5.readReg64 .x8 = sp + 23952#64 ∧ s5.readReg64 .x9 = sp + 19184#64 ∧
        s5.readReg64 .x10 = sp + 24464#64 ∧ s5.readReg64 .x11 = 16#64 ∧
        s5.readReg64 .x12 = 1441#64 ∧ s5.readReg64 .x13 = 55457#64 ∧
        s5.readReg64 .fp = fpVal ∧
        s5.readVReg128 16#5 = dup8x16 3329#16 ∧ s5.readVReg128 17#5 = dup8x16 20159#16 ∧
        s5.readVReg128 18#5 = dup8x16 1024#16 ∧ s5.readVReg128 19#5 = dup8x16 0xf2ff#16 ∧
        P5 = (Spill21Mem (sp + 1920#64) spill ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  wp_steps 4
  refine step_ldrQ128 (pc := blkPl04.base + BitVec.ofNat 64 52992) (wb := none)
    (ea := sp + 2144#64) (v := dup8x16 20159#16)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.spill21 (ptr := sp + 1920#64) (ea := sp + 2144#64) (k := 14)
      (by decide) (by clear * -; bv_omega) (by simpa [Spill21.get] using hs14)))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (pc := blkPl04.base + BitVec.ofNat 64 52996) (wb := none)
    (ea := sp + 2224#64) (v := dup8x16 3329#16)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.spill21 (ptr := sp + 1920#64) (ea := sp + 2224#64) (k := 19)
      (by decide) (by clear * -; bv_omega) (by simpa [Spill21.get] using hs19)))
    (by wp_norm_lhs) ?_
  wp_steps 8
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp [hfp], by simp, by simp, by simp, by simp, rfl⟩

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

private theorem seg8b_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) (inv err2 msgPoly : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offCf28) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = sp + 23952#64 + BitVec.ofNat 64 (32 * r))
    (hx9 : s.readReg64 .x9 = sp + 19184#64 + BitVec.ofNat 64 (32 * r))
    (hx10 : s.readReg64 .x10 = sp + 24464#64 + BitVec.ofNat 64 (32 * r))
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (16 - r))
    (hx12 : s.readReg64 .x12 = 1441#64) (hx13 : s.readReg64 .x13 = 55457#64)
    (hfp : s.readReg64 .fp = fpVal)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16) (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv18 : s.readVReg128 18#5 = dup8x16 1024#16) (hv19 : s.readVReg128 19#5 = dup8x16 0xf2ff#16)
    (hhi0 : f (2 * r) = polyVecNat inv (2 * r))
    (hhi1 : f (2 * r + 1) = polyVecNat inv (2 * r + 1)) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if r < 15 then b + offCf28 else b + offSeg8bEnd) s
      (PolyMem (sp + 23936#64) f ∗ PolyMem (sp + 24448#64) (polyVecNat err2) ∗
        PolyMem (sp + 19168#64) (polyVecNat msgPoly) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = sp + 23952#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x9 = sp + 19184#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x10 = sp + 24464#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x11 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x12 = 1441#64 ∧ s'.readReg64 .x13 = 55457#64 ∧
        s'.readReg64 .fp = fpVal ∧
        s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
        s'.readVReg128 18#5 = dup8x16 1024#16 ∧ s'.readVReg128 19#5 = dup8x16 0xf2ff#16 ∧
        P' = (PolyMem (sp + 23936#64)
          (Function.update
            (Function.update f (2 * r) (polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r)))
            (2 * r + 1) (polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r + 1))) ∗
          PolyMem (sp + 24448#64) (polyVecNat err2) ∗
          PolyMem (sp + 19168#64) (polyVecNat msgPoly) ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  wp_step
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 23936#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 23936#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat inv (2 * r)) (v2 := polyVecNat inv (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_step
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 24448#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 24448#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat err2 (2 * r)) (v2 := polyVecNat err2 (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx10]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 6
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 19168#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 19168#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
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
    (ea := (sp + 23936#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 23936#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
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
        by simp [hx12], by simp [hx13], by simp [hfp],
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
        by simp [hx12], by simp [hx13], by simp [hfp],
        by simp [hv16], by simp [hv17], by simp [hv18], by simp [hv19], rfl⟩

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g :=
  vecRangeMem_congr h

private theorem seg8b_loop1 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (sp fpVal : BitVec 64) (inv err2 msgPoly : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 →
    ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offCf28 → s.status = .Running →
      s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem →
      MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = sp + 23952#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x9 = sp + 19184#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x10 = sp + 24464#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x11 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x12 = 1441#64 →
      s.readReg64 .x13 = 55457#64 →
      s.readReg64 .fp = fpVal →
      s.readVReg128 16#5 = dup8x16 3329#16 →
      s.readVReg128 17#5 = dup8x16 20159#16 →
      s.readVReg128 18#5 = dup8x16 1024#16 →
      s.readVReg128 19#5 = dup8x16 0xf2ff#16 →
      (∀ j, j < 2 * r → f j = polyVecNat (seg5FinalPoly inv err2 msgPoly) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat inv j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg8bEnd) s
        (PolyMem (sp + 23936#64) f ∗
          PolyMem (sp + 24448#64) (polyVecNat err2) ∗
          PolyMem (sp + 19168#64) (polyVecNat msgPoly) ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .fp = fpVal ∧
          P' = (PolyMem (sp + 23936#64) (polyVecNat (seg5FinalPoly inv err2 msgPoly)) ∗
            PolyMem (sp + 24448#64) (polyVecNat err2) ∗
            PolyMem (sp + 19168#64) (polyVecNat msgPoly) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl _hro hx8 hx9 hx10 hx11 hx12 hx13 hfp
      hv16 hv17 hv18 hv19 hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hstep := seg8b_iter hb s sp fpVal inv err2 msgPoly (r := 15) (by decide) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx13 hfp hv16 hv17 hv18 hv19
      (hhi 30 (by decide) (by decide)) (hhi 31 (by decide) (by decide))
    simp only [show ¬ (15 < 15) by decide, ↓reduceIte] at hstep
    refine SepWP.mono hstep ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, _, hfp', _, _, _, _, hP'⟩
    refine ⟨hsp', hspA', hfp', ?_⟩
    rw [hP', polyMem_congr (update2_split (r := 15) hlo hhi).1]
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hfp
      hv16 hv17 hv18 hv19 hlo hhi
    have hr_lt : r < 15 := by omega
    have hstep := seg8b_iter hb s sp fpVal inv err2 msgPoly (r := r) (by omega) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx13 hfp hv16 hv17 hv18 hv19
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr_lt, ↓reduceIte] at hstep
    refine sepWP_seq_env hcl hro hstep ?_
    rintro sm Pm hpc' hrun' hcl' hro'
      ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hfp', hv16', hv17', hv18', hv19', rfl⟩
    have ⟨hlo', hhi'⟩ := update2_split (r := r) hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc' hrun' hsp' hspA' hcl' hro'
      hx8' hx9' hx10' hx11' hx12' hx13' hfp' hv16' hv17' hv18' hv19' hlo' hhi'

attribute [local irreducible]
  neonInvNttMontgomery16 neonPolyNttMul16 neonDot3 seg5FinalPoly

/-- Segment 8b (`+0xb190 → +0xcfb4`): `DotLoops3` (`t̂ · r̂`), `Inv3LowLoops`, `SymEvalInv3{a,b,c}`,
    `B28` `memcpy`, and 16-iter normalizer + `e₂` + `msgPoly` + Barrett loop. -/
theorem seg8b_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) (t0 : Spill21)
    (tHat0 tHat1 tHat2 rHat0 rHat1 rHat2 e2 msgPoly : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Dot) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = sp + 5680#64) (hx11 : s.readReg64 .x11 = 62209#64)
    (hx12 : s.readReg64 .x12 = 3329#64) (hx13 : s.readReg64 .x13 = sp + 22400#64)
    (hx19 : s.readReg64 .x19 = sp + 11856#64) (hfp : s.readReg64 .fp = fpVal)
    (hacc : AccRegs polyZero16 s) :
    let inv := neonInvNttMontgomery16 (neonDot3 tHat0 tHat1 tHat2 rHat0 rHat1 rHat2)
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg8bEnd) s
      (Spill21Mem (sp + 1920#64) (AccSpill21 t0 polyZero16) ∗
        PolyMem (sp + 5680#64) (polyVecNat tHat0) ∗ PolyMem (sp + 6192#64) (polyVecNat tHat1) ∗
        PolyMem (sp + 6704#64) (polyVecNat tHat2) ∗ PolyMem (sp + 11856#64) (polyVecNat rHat0) ∗
        PolyMem (sp + 12368#64) (polyVecNat rHat1) ∗ PolyMem (sp + 12880#64) (polyVecNat rHat2) ∗
        PolyMem (sp + 19168#64) (polyVecNat msgPoly) ∗ Poly32Mem (sp + 20704#64) Vec32.zero ∗
        memRegion (sp + 22400#64) 512 ∗ memRegion (sp + 23936#64) 512 ∗
        PolyMem (sp + 24448#64) (polyVecNat e2) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        (Pf ⊢ memRegion (sp + 1920#64) 336 ∗
          PolyMem (sp + 5680#64) (polyVecNat tHat0) ∗ PolyMem (sp + 6192#64) (polyVecNat tHat1) ∗
          PolyMem (sp + 6704#64) (polyVecNat tHat2) ∗ PolyMem (sp + 11856#64) (polyVecNat rHat0) ∗
          PolyMem (sp + 12368#64) (polyVecNat rHat1) ∗ PolyMem (sp + 12880#64) (polyVecNat rHat2) ∗
          PolyMem (sp + 19168#64) (polyVecNat msgPoly) ∗ memRegion (sp + 20704#64) 512 ∗
          memRegion (sp + 22400#64) 512 ∗
          PolyMem (sp + 23936#64) (polyVecNat (seg5FinalPoly inv e2 msgPoly)) ∗
          PolyMem (sp + 24448#64) (polyVecNat e2) ∗ Rest)) := by
  dsimp only
  let dot := neonDot3 tHat0 tHat1 tHat2 rHat0 rHat1 rHat2
  let inv := neonInvNttMontgomery16 dot
  have hdot : dot.size = 256 := neonDot3_size tHat0 tHat1 tHat2 rHat0 rHat1 rHat2
  sep_frame_apply (sepWP_elim_poly32 (a := sp + 22400#64)); intro v22400
  have stepf : ∀ {prog : Program} {pc1 pc2 : BitVec 64} {st : State} {P P1 : SepProp}
      {Q1 Q2 : State → SepProp → Prop},
      mlkemMultiLib.CodeLoaded mlkemMpl st.mem → MlKemRoOk mlkemMpl st.mem →
      SepWP prog pc1 st P1 Q1 → (P ⊢ P1) →
      (∀ s' P', s'.pc = pc1 → s'.status = .Running →
        mlkemMultiLib.CodeLoaded mlkemMpl s'.mem → MlKemRoOk mlkemMpl s'.mem →
        Q1 s' P' → SepWP prog pc2 s' P' Q2) →
      SepWP prog pc2 st P Q2 :=
    fun hcl' hro' h1 hP' h2 => SepWP.weaken_pre hP' (sepWP_seq_env hcl' hro' h1 h2)
  have h5680_512 : (sp + 5680#64) + 512#64 = sp + 6192#64 := by clear * -; bv_omega
  have h5680_1024 : (sp + 5680#64) + 1024#64 = sp + 6704#64 := by clear * -; bv_omega
  have h11856_512 : (sp + 11856#64) + 512#64 = sp + 12368#64 := by clear * -; bv_omega
  have h11856_1024 : (sp + 11856#64) + 1024#64 = sp + 12880#64 := by clear * -; bv_omega
  refine stepf hcl hro
    (dot3_ok hb s s sp (sp + 5680#64) (sp + 11856#64) t0
      tHat0 tHat1 tHat2 rHat0 rHat1 rHat2 Vec32.zero v22400 _
      hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hx19 hacc
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by rw [h5680_512, h5680_1024, h11856_512, h11856_1024]; sep_frame) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, _, hpres1, rfl⟩
  have hfp1 : s1.readReg64 .fp = fpVal := Eq.trans hpres1.fp hfp
  refine stepf hcl1 hro1
    (inv3_low_ok hb s1 sp hdot _ hpc1 hrun1 hsp1 hspA1 hcl1 hro1) (by sep_frame) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hpres2, rfl⟩
  have hfp2 : s2.readReg64 .fp = fpVal := Eq.trans hpres2.fp hfp1
  refine stepf hcl2 hro2
    (seg8b_inv3_sym s2 sp hdot (AccSpill21 t0 dot) _ hpc2 hrun2 hsp2 hspA2) (by sep_frame) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx0_3, hx1_3, hx2_3, hx19_3, hfp3_eq, tOut, hs14, hs19, hP3⟩
  have hfp3 : s3.readReg64 .fp = fpVal := Eq.trans hfp3_eq hfp2
  refine stepf hcl3 hro3
    (seg8b_memcpy hb s3 sp fpVal inv _ hpc3 hrun3 hsp3 hspA3 hx0_3 hx1_3 hx2_3 hx19_3 hfp3 hcl3)
    (Entails.trans hP3 (by sep_frame)) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hx19_4, hfp4, rfl⟩
  refine stepf hcl4 hro4
    (seg8b_setup hb s4 sp fpVal tOut _ hpc4 hrun4 hsp4 hspA4 hx19_4 hfp4 hs14 hs19)
    (by sep_frame) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 hro5
    ⟨hsp5, hspA5, hx8_5, hx9_5, hx10_5, hx11_5, hx12_5, hx13_5, hfp5,
      hv16_5, hv17_5, hv18_5, hv19_5, rfl⟩
  refine stepf hcl5 hro5
    (seg8b_loop1 hb sp fpVal inv e2 msgPoly _ 15 0 rfl s5 (polyVecNat inv)
      hpc5 hrun5 hsp5 hspA5 hcl5 hro5
      (by simpa using hx8_5) (by simpa using hx9_5) (by simpa using hx10_5)
      hx11_5 hx12_5 hx13_5 hfp5
      hv16_5 hv17_5 hv18_5 hv19_5 (fun _ h => by omega) (fun _ _ _ => rfl))
    (by sep_frame) ?_
  rintro sf Pf hpcf hrunf _ _ ⟨hspf, hspAf, hfpf, rfl⟩
  refine SepWP.done hpcf hrunf ⟨hspf, hspAf, hfpf, ?_⟩
  rw [h5680_512, h5680_1024, h11856_512, h11856_1024,
    show PolyMem (sp + 20704#64) (polyVecNat inv) = Poly32Mem (sp + 20704#64) (Vec32.ofFn (polyVecNat inv))
      from (poly32Mem_ofFn _ _).symm]
  have hent1 := spill21Mem_entails_memRegion (sp + 1920#64) tOut
  have hent2 := poly32Mem_entails_memRegion (sp + 20704#64) (Vec32.ofFn (polyVecNat inv))
  have hent3 := poly32Mem_entails_memRegion (sp + 22400#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 tHat2 rHat2)))
  have hsub := sepConj_mono hent1 (sepConj_mono hent2 hent3)
  exact Entails.trans (by sep_frame) (Entails.trans (sepConj_mono_left hsub) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8b

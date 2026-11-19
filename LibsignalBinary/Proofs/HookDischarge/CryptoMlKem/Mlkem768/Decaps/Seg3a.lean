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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv1c

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 3a (`+0x199c → +0x3860`)

Proves the first half of Segment 3:
1. Pre-`DotLoops1` zeroing & GPR/spill initialization (`+0x199c → +0x1b04`),
2. 3-way inner product `sHat · uHat` (`DotLoops1.dot1_ok`, `+0x1b04 → +0x1eb4`),
3. Lower 2-stage inverse NTT (`InvLowLoops.inv1_low_ok`, `+0x1eb4 → +0x2000`),
4. Upper 5-stage symbolic inverse NTT (`SymEvalInv1{a,b,c}`, `+0x2000 → +0x3860`),
yielding `neonInvNttMontgomery16 (neonDot3 sHat0 sHat1 sHat2 uHat0 uHat1 uHat2)` at `sp + 20704`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3a

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 neonInvNttMontgomery16 neonPolyNttMul16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 Spill13 Vec32 poly32Mem_entails_memRegion
  poly32Mem_ofFn polyVecNat step_ldrQ128 step_strQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16 lowerInvNtt16_size neonDot3 neonDot3_size polyZero16 upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (AccRegs accRegs_zero_iff)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  SepStore128.spill21 Spill21 Spill21Mem Spill6)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a (sepWP_elim_poly32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b (exec_simdMovi_2d_0)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1 (
  AccSpill21 accSpill21_zero_iff dot1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops (
  Inv13Preserved inv1_low_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (
  SymGpr SymGprs31 SymSpill21 runSymRange_add symInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval (
  SymSpatial SymStateMatches evalSExpr evalSymGpr evalSymSpill21 symEnvOf symInit_matches)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyBridge (InSymWord04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly (sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge (
  symPoly_eq_upperInvNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv1a (cfgInv1 run_inv1a)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv1b (run_inv1b)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalInv1c (
  inv1_ast_eq inv1_noSpillVreg run_inv1c symInv1End)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x199c → 0x1b00]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC04 polyVecNat dup8x16

private abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"
abbrev offSeg3aEnd : BitVec 64 := 14432#64

local macro "p_str " k:num : tactic => `(tactic| (
  apply step_strQ128 (val := 0#128)
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.set] } }
  { wp_norm_lhs }; intro _))

local macro "p_ldr " k:num : tactic => `(tactic| (
  apply step_ldrQ128 (v := 0#128)
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepLoad128.left; apply SepLoad128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { rfl } }
  { wp_norm_lhs }))

local macro "sp21_str " k:num : tactic => `(tactic| (
  apply step_strQ128 (val := 0#128)
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.right; apply SepStore128.left; apply SepStore128.spill21 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Spill21.set] } }
  { wp_norm_lhs }; intro _))

/-! ## 1. Pre-`DotLoops1` Setup (`+0x199c → +0x1b04`) -/

private def setupMidVec32 (v : Vec32) : Vec32 :=
  ⟨0#128, 0#128, 0#128, 0#128, 0#128, 0#128, 0#128, 0#128,
   0#128, 0#128, 0#128, 0#128, 0#128, v.v13, v.v14, v.v15,
   v.v16, v.v17, v.v18, v.v19, v.v20, v.v21, v.v22, v.v23,
   v.v24, v.v25, v.v26, 0#128, v.v28, v.v29, v.v30, v.v31⟩

private def setupMidSpill21 (t0 : Spill21) : Spill21 :=
  ⟨t0.s0, t0.s1, t0.s2, t0.s3, t0.s4, t0.s5, t0.s6, t0.s7,
   t0.s8, 0#128, 0#128, 0#128, 0#128, 0#128, 0#128, 0#128,
   0#128, 0#128, 0#128, 0#128, 0#128⟩

private theorem seg3a_setup_a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (_hbase : blkPl04.base = b)
    (s : State) (sp x23Val : BitVec 64) (v0 : Vec32) (t0 : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + 6556#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 6760#64) s
      (Poly32Mem (sp + 20704#64) v0 ∗ Spill21Mem (sp + 1920#64) t0 ∗
        ((sp + 1888#64) ↦₆₄ x23Val) ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x8 = 0#64 ∧ s1.readReg64 .x9 = sp + 22400#64 ∧
        s1.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s1.readReg64 .x11 = sp + 5680#64 ∧
        s1.readReg64 .x12 = 62209#64 ∧ s1.readReg64 .x13 = 3329#64 ∧
        s1.readReg64 .x14 = sp + 11856#64 ∧ s1.readReg64 .x23 = x23Val ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readVReg128 0#5 = 0#128 ∧
        P1 = (Poly32Mem (sp + 20704#64) (setupMidVec32 v0) ∗
          Spill21Mem (sp + 1920#64) (setupMidSpill21 t0) ∗
          ((sp + 1888#64) ↦₆₄ x23Val) ∗ Rest)) := by
  have _ : b = blkPl04.base := _hb
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  cases v0; cases t0
  conv => arg 4; rw [show sp + 1888#64 = s.sp + 1888#64 by rw [hsp]]
  wp_steps 12
  p_str 0; wp_steps 1; p_ldr 0; p_str 1; p_str 2; sp21_str 20
  p_ldr 1; p_str 3; sp21_str 19; p_ldr 2; p_str 4; sp21_str 18
  p_ldr 3; p_str 5; sp21_str 17; p_ldr 4; p_str 6; sp21_str 16
  p_ldr 5; p_str 7; sp21_str 15; p_ldr 6; p_str 8; sp21_str 14
  p_ldr 7; p_str 9; sp21_str 13; p_ldr 8; p_str 10; sp21_str 12
  p_ldr 9; p_str 11; sp21_str 11; p_ldr 10; p_str 12; sp21_str 10
  p_ldr 11; p_str 27; sp21_str 9
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp, by simp, by simp [ro00Sym],
      by simp, by simp, by simp,
      by simp, by simp,
      by simp, by simp, by simp, by simp, ?_⟩
  exact congrArg₂ sepConj (congrArg (Poly32Mem (sp + 20704#64)) rfl)
    (congrArg₂ sepConj (congrArg (Spill21Mem (sp + 1920#64)) rfl) (by rw [hsp]))

private theorem seg3a_setup_b [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp : BitVec 64) (v0 : Vec32) (t0 : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + 6760#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hv0 : s.readVReg128 0#5 = 0#128) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 6916#64) s
      (Poly32Mem (sp + 20704#64) (setupMidVec32 v0) ∗
        Spill21Mem (sp + 1920#64) (setupMidSpill21 t0) ∗ Rest)
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        (∀ g : BitVec 5, s2.readReg64 (.gpr g) = s.readReg64 (.gpr g)) ∧
        AccRegs polyZero16 s2 ∧
        P2 = (Poly32Mem (sp + 20704#64) Vec32.zero ∗
          Spill21Mem (sp + 1920#64) (AccSpill21 t0 polyZero16) ∗ Rest)) := by
  have _ : b = blkPl04.base := _hb
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  cases v0; cases t0
  dsimp only [setupMidVec32, setupMidSpill21]
  p_ldr 12; p_ldr 27; p_str 25; p_str 23; p_ldr 25; p_str 21; p_ldr 23
  p_str 19; p_ldr 21; p_str 17; p_ldr 19; p_str 15; p_ldr 17; p_str 13
  p_ldr 15; p_str 14; p_ldr 13; p_str 16; p_ldr 14; p_str 18; p_ldr 16
  p_str 20; p_ldr 18; p_str 22; p_ldr 20; p_str 24; p_ldr 22; p_str 26
  p_ldr 24; p_str 29; p_ldr 26; p_str 28; p_ldr 29; p_str 31; p_ldr 28
  p_str 30; sp21_str 8; p_ldr 30; p_ldr 31
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk], fun _ => by simp, ?_, ?_⟩
  · rw [accRegs_zero_iff]; simp [hv0]
  · exact congrArg₂ sepConj
      (congrArg (Poly32Mem (sp + 20704#64)) (by simp [Vec32.zero, Vec32.ofFn]))
      (congrArg₂ sepConj (congrArg (Spill21Mem (sp + 1920#64)) (by simp [AccSpill21])) rfl)

/-! ## 2. Upper 5-Stage Symbolic `InvNTT1` (`+0x2000 → +0x3860`) & Composed `seg3a_ok` -/

private theorem run_inv1_full :
    SymPolyDefs.runSymRange cfgInv1 2048 1560 symInit = some symInv1End :=
  runSymRange_add cfgInv1 2048 1040 520 _ _ _
    (runSymRange_add cfgInv1 2048 520 520 _ _ _ run_inv1a run_inv1b)
    run_inv1c

private theorem inSym_inv1 (j : Nat) (h1 : 2048 ≤ j) (h2 : j < 2048 + 1560) : InSymWord04 j :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, by omega⟩)))

private theorem seg3a_inv1_sym [MlKemPlacement] {b : BitVec 64}
    (s : State) (sp : BitVec 64) {dot : Poly16} (hdot : dot.size = 256)
    (tSpill : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + 8192#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg3aEnd) s
      (PolyMem (sp + 20704#64) (polyVecNat (lowerInvNtt16 dot)) ∗
        Spill21Mem (sp + 1920#64) tSpill ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = sp + 11856#64 ∧ sf.readReg64 .x1 = sp + 20704#64 ∧
        sf.readReg64 .x2 = 512#64 ∧ sf.readReg64 .x20 = sp + 11856#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        ∃ tOut : Spill21,
          tOut.s14 = dup8x16 20159#16 ∧ tOut.s19 = dup8x16 3329#16 ∧
          (Pf ⊢ PolyMem (sp + 20704#64) (polyVecNat (neonInvNttMontgomery16 dot)) ∗
            Spill21Mem (sp + 1920#64) tOut ∗ Rest)) := by
  let poly0 := Vec32.ofFn (polyVecNat (lowerInvNtt16 dot))
  let env := symEnvOf s Spill13.zero Spill6.zero tSpill poly0 Vec32.zero
  obtain ⟨hm0, _, _, hsp21_0, hpoly0⟩ := symInit_matches cfgInv1 s sp 0#64
    Spill13.zero Spill6.zero tSpill poly0 Vec32.zero hsp hspA (by rintro _ ⟨⟩)
  have hpre : PolyMem (sp + 20704#64) (polyVecNat (lowerInvNtt16 dot)) ∗
      Spill21Mem (sp + 1920#64) tSpill ∗ Rest ⊢
      SymSpatial cfgInv1 sp 0#64 env symInit Rest := by
    dsimp only [SymSpatial, SymPolyEval.polyAddr, cfgInv1, SymPolyEval.spillMemAt,
      SymPolyEval.inPolyMemAt]
    rw [hpoly0, hsp21_0, poly32Mem_ofFn]; dsimp only [PolyMem]; sep_frame
  refine SepWP.weaken_pre hpre
    (sepWP_of_runSymRange 1560 2048 inSym_inv1 run_inv1_full hm0 hpc hrun ?_)
  intro sf _ _ hmf
  have hgpr := hmf.hgprs
  have hg0 : sf.readReg64 .x0 = (sp + 8192#64) + 3664#64 := hgpr 0#5 (by decide)
  have hg1 : sf.readReg64 .x1 = (sp + 20480#64) + 224#64 := hgpr 1#5 (by decide)
  have hg2 : sf.readReg64 .x2 = 512#64 := hgpr 2#5 (by decide)
  have hg20 : sf.readReg64 .x20 = (sp + 8192#64) + 3664#64 := hgpr 20#5 (by decide)
  have hg23 : sf.readReg64 .x23 = s.readReg64 .x23 := hgpr 23#5 (by decide)
  have hg26 : sf.readReg64 .x26 = s.readReg64 .x26 := hgpr 26#5 (by decide)
  have hg28 : sf.readReg64 .x28 = s.readReg64 .x28 := hgpr 28#5 (by decide)
  have hg29 : sf.readReg64 .fp = s.readReg64 .fp := hgpr 29#5 (by decide)
  refine ⟨hmf.hsp, hmf.hsp_al,
    by rw [hg0]; clear * -; bv_omega, by rw [hg1]; clear * -; bv_omega, hg2,
    by rw [hg20]; clear * -; bv_omega, hg23, hg26, hg28, hg29,
    evalSymSpill21 env symInv1End.spill21,
    by simp [evalSymSpill21, symInv1End, evalSExpr],
    by simp [evalSymSpill21, symInv1End, evalSExpr], ?_⟩
  dsimp only [SymSpatial, SymPolyEval.polyAddr, cfgInv1, SymPolyEval.spillMemAt,
    SymPolyEval.inPolyMemAt]
  have hpoly_eq := symPoly_eq_upperInvNtt (sp + 20704#64) symInv1End.poly
    (lowerInvNtt16_size hdot) env rfl inv1_noSpillVreg inv1_ast_eq
  rw [hpoly_eq, upperInvNtt16_lowerInvNtt16]
  sep_frame

/-- Segment 3a (`+0x199c → +0x3860`): inner product `sHat · uHat` + full `InvNTT1`. -/
theorem seg3a_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp x23Val : BitVec 64)
    (t0 : Spill21) (sHat0 sHat1 sHat2 uHat0 uHat1 uHat2 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + 6556#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let dot := neonDot3 sHat0 sHat1 sHat2 uHat0 uHat1 uHat2
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg3aEnd) s
      (((sp + 1888#64) ↦₆₄ x23Val) ∗ Spill21Mem (sp + 1920#64) t0 ∗
        PolyMem (sp + 5680#64) (polyVecNat uHat0) ∗
        PolyMem (sp + 6192#64) (polyVecNat uHat1) ∗
        PolyMem (sp + 6704#64) (polyVecNat uHat2) ∗
        memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 20704#64) 512 ∗
        PolyMem (sp + 22400#64) (polyVecNat sHat0) ∗
        PolyMem (sp + 22912#64) (polyVecNat sHat1) ∗
        PolyMem (sp + 23424#64) (polyVecNat sHat2) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = sp + 11856#64 ∧ sf.readReg64 .x1 = sp + 20704#64 ∧
        sf.readReg64 .x2 = 512#64 ∧ sf.readReg64 .x20 = sp + 11856#64 ∧
        sf.readReg64 .x23 = x23Val ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        ∃ tOut : Spill21,
          tOut.s14 = dup8x16 20159#16 ∧ tOut.s19 = dup8x16 3329#16 ∧
          (Pf ⊢ ((sp + 1888#64) ↦₆₄ x23Val) ∗ Spill21Mem (sp + 1920#64) tOut ∗
            PolyMem (sp + 5680#64) (polyVecNat uHat0) ∗
            PolyMem (sp + 6192#64) (polyVecNat uHat1) ∗
            PolyMem (sp + 6704#64) (polyVecNat uHat2) ∗
            memRegion (sp + 11856#64) 512 ∗
            PolyMem (sp + 20704#64) (polyVecNat (neonInvNttMontgomery16 dot)) ∗
            PolyMem (sp + 22400#64) (polyVecNat sHat0) ∗
            PolyMem (sp + 22912#64) (polyVecNat sHat1) ∗
            PolyMem (sp + 23424#64) (polyVecNat sHat2) ∗ Rest)) := by
  intro dot
  sep_frame_apply (sepWP_elim_poly32 (a := sp + 20704#64)); intro v20
  sep_frame_apply (sepWP_elim_poly32 (a := sp + 11856#64)); intro v11
  set R0 := Poly32Mem (sp + 11856#64) v11 ∗
    PolyMem (sp + 5680#64) (polyVecNat uHat0) ∗ PolyMem (sp + 6192#64) (polyVecNat uHat1) ∗
    PolyMem (sp + 6704#64) (polyVecNat uHat2) ∗ PolyMem (sp + 22400#64) (polyVecNat sHat0) ∗
    PolyMem (sp + 22912#64) (polyVecNat sHat1) ∗ PolyMem (sp + 23424#64) (polyVecNat sHat2) ∗ Rest
  have hpre0 : Poly32Mem (sp + 11856#64) v11 ∗
        (Poly32Mem (sp + 20704#64) v20 ∗
          (((sp + 1888#64) ↦₆₄ x23Val) ∗ Spill21Mem (sp + 1920#64) t0 ∗
            PolyMem (sp + 5680#64) (polyVecNat uHat0) ∗
            PolyMem (sp + 6192#64) (polyVecNat uHat1) ∗
            PolyMem (sp + 6704#64) (polyVecNat uHat2) ∗
            PolyMem (sp + 22400#64) (polyVecNat sHat0) ∗
            PolyMem (sp + 22912#64) (polyVecNat sHat1) ∗
            PolyMem (sp + 23424#64) (polyVecNat sHat2) ∗ Rest)) ⊢
      Poly32Mem (sp + 20704#64) v20 ∗ Spill21Mem (sp + 1920#64) t0 ∗
        ((sp + 1888#64) ↦₆₄ x23Val) ∗ R0 := by dsimp only [R0]; sep_frame
  refine SepWP.weaken_pre hpre0 (sepWP_seq_env hcl hro
    (seg3a_setup_a hb hbase s sp x23Val v20 t0 R0 hpc hrun hsp hspA) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx23_1, hfp1, hx26_1, hx28_1, hv0_1, hP1⟩
  subst hP1
  refine sepWP_seq_env hcl1 hro1
    (seg3a_setup_b hb s1 sp v20 t0 (((sp + 1888#64) ↦₆₄ x23Val) ∗ R0)
      hpc1 hrun1 hsp1 hspA1 hv0_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hr2, hacc2, hP2⟩
  subst hP2
  have hpres_init : Inv13Preserved s2 s2 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  set Rdot := ((sp + 1888#64) ↦₆₄ x23Val) ∗ Rest
  have hpre_dot : Poly32Mem (sp + 20704#64) Vec32.zero ∗
      Spill21Mem (sp + 1920#64) (AccSpill21 t0 polyZero16) ∗ (((sp + 1888#64) ↦₆₄ x23Val) ∗ R0) ⊢
      Spill21Mem (sp + 1920#64) (AccSpill21 t0 polyZero16) ∗
        PolyMem (sp + 22400#64) (polyVecNat sHat0) ∗
        PolyMem ((sp + 22400#64) + 512#64) (polyVecNat sHat1) ∗
        PolyMem ((sp + 22400#64) + 1024#64) (polyVecNat sHat2) ∗
        PolyMem (sp + 5680#64) (polyVecNat uHat0) ∗
        PolyMem ((sp + 5680#64) + 512#64) (polyVecNat uHat1) ∗
        PolyMem ((sp + 5680#64) + 1024#64) (polyVecNat uHat2) ∗
        Poly32Mem (sp + 20704#64) Vec32.zero ∗
        Poly32Mem (sp + 11856#64) v11 ∗ Rdot := by
    dsimp only [R0, Rdot]
    rw [show (sp + 22400#64) + 512#64 = sp + 22912#64 by clear * -; bv_omega,
      show (sp + 22400#64) + 1024#64 = sp + 23424#64 by clear * -; bv_omega,
      show (sp + 5680#64) + 512#64 = sp + 6192#64 by clear * -; bv_omega,
      show (sp + 5680#64) + 1024#64 = sp + 6704#64 by clear * -; bv_omega]
    sep_frame
  refine SepWP.weaken_pre hpre_dot (sepWP_seq_env hcl2 hro2
    (dot1_ok hb s2 s2 sp (sp + 22400#64) (sp + 5680#64) t0 sHat0 sHat1 sHat2 uHat0 uHat1 uHat2
      Vec32.zero v11 Rdot hpc2 hrun2 hsp2 hspA2 hcl2 hro2
      ((hr2 _).trans hx8_1) ((hr2 _).trans hx9_1) ((hr2 _).trans hx10_1)
      ((hr2 _).trans hx11_1) ((hr2 _).trans hx12_1) ((hr2 _).trans hx13_1)
      ((hr2 _).trans hx14_1) hacc2 hpres_init) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hpres3, hP3⟩
  subst hP3
  set Rinv := Spill21Mem (sp + 1920#64) (AccSpill21 t0 dot) ∗
    PolyMem (sp + 22400#64) (polyVecNat sHat0) ∗
    PolyMem ((sp + 22400#64) + 512#64) (polyVecNat sHat1) ∗
    PolyMem ((sp + 22400#64) + 1024#64) (polyVecNat sHat2) ∗
    PolyMem (sp + 5680#64) (polyVecNat uHat0) ∗
    PolyMem ((sp + 5680#64) + 512#64) (polyVecNat uHat1) ∗
    PolyMem ((sp + 5680#64) + 1024#64) (polyVecNat uHat2) ∗
    Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (Spec.neonPolyNttMul16 sHat2 uHat2))) ∗ Rdot
  have hpre_inv : Spill21Mem (sp + 1920#64) (AccSpill21 t0 dot) ∗
      PolyMem (sp + 22400#64) (polyVecNat sHat0) ∗
      PolyMem ((sp + 22400#64) + 512#64) (polyVecNat sHat1) ∗
      PolyMem ((sp + 22400#64) + 1024#64) (polyVecNat sHat2) ∗
      PolyMem (sp + 5680#64) (polyVecNat uHat0) ∗
      PolyMem ((sp + 5680#64) + 512#64) (polyVecNat uHat1) ∗
      PolyMem ((sp + 5680#64) + 1024#64) (polyVecNat uHat2) ∗
      PolyMem (sp + 20704#64) (polyVecNat dot) ∗
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (Spec.neonPolyNttMul16 sHat2 uHat2))) ∗ Rdot ⊢
      PolyMem (sp + 20704#64) (polyVecNat dot) ∗ Rinv := by dsimp only [Rinv]; sep_frame
  refine SepWP.weaken_pre hpre_inv (sepWP_seq_env hcl3 hro3
    (inv1_low_ok hb s3 sp (neonDot3_size sHat0 sHat1 sHat2 uHat0 uHat1 uHat2) Rinv
      hpc3 hrun3 hsp3 hspA3 hcl3 hro3) ?_)
  rintro s4 P4 hpc4 hrun4 _ _ ⟨hsp4, hspA4, hpres4, hP4⟩
  subst hP4
  set Rsym := PolyMem (sp + 22400#64) (polyVecNat sHat0) ∗
    PolyMem ((sp + 22400#64) + 512#64) (polyVecNat sHat1) ∗
    PolyMem ((sp + 22400#64) + 1024#64) (polyVecNat sHat2) ∗
    PolyMem (sp + 5680#64) (polyVecNat uHat0) ∗
    PolyMem ((sp + 5680#64) + 512#64) (polyVecNat uHat1) ∗
    PolyMem ((sp + 5680#64) + 1024#64) (polyVecNat uHat2) ∗
    Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (Spec.neonPolyNttMul16 sHat2 uHat2))) ∗ Rdot
  have hpre_sym : PolyMem (sp + 20704#64) (polyVecNat (lowerInvNtt16 dot)) ∗ Rinv ⊢
      PolyMem (sp + 20704#64) (polyVecNat (lowerInvNtt16 dot)) ∗
        Spill21Mem (sp + 1920#64) (AccSpill21 t0 dot) ∗ Rsym := by
    dsimp only [Rinv, Rsym]; sep_frame
  refine SepWP.weaken_pre hpre_sym
    (SepWP.mono (seg3a_inv1_sym s4 sp (neonDot3_size sHat0 sHat1 sHat2 uHat0 uHat1 uHat2)
      (AccSpill21 t0 dot) Rsym hpc4 hrun4 hsp4 hspA4) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx0_f, hx1_f, hx2_f, hx20_f, hx23_f, hx26_f, hx28_f, hfp_f,
    tOut, ht14, ht19, hPf⟩
  refine ⟨hsp_f, hspA_f, hx0_f, hx1_f, hx2_f, hx20_f,
    hx23_f.trans (hpres4.x23.trans (hpres3.x23.trans ((hr2 _).trans hx23_1))),
    hx26_f.trans (hpres4.x26.trans (hpres3.x26.trans ((hr2 _).trans hx26_1))),
    hx28_f.trans (hpres4.x28.trans (hpres3.x28.trans ((hr2 _).trans hx28_1))),
    hfp_f.trans (hpres4.fp.trans (hpres3.fp.trans ((hr2 _).trans hfp1))),
    tOut, ht14, ht19, Entails.trans hPf ?_⟩
  dsimp only [Rsym, Rdot]
  rw [show (sp + 22400#64) + 512#64 = sp + 22912#64 by clear * -; bv_omega,
    show (sp + 22400#64) + 1024#64 = sp + 23424#64 by clear * -; bv_omega,
    show (sp + 5680#64) + 512#64 = sp + 6192#64 by clear * -; bv_omega,
    show (sp + 5680#64) + 1024#64 = sp + 6704#64 by clear * -; bv_omega]
  have hm11 := poly32Mem_entails_memRegion (sp + 11856#64)
    (Vec32.ofFn (polyVecNat (Spec.neonPolyNttMul16 sHat2 uHat2)))
  exact Entails.trans
    (by sep_frame : _ ⊢
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (Spec.neonPolyNttMul16 sHat2 uHat2))) ∗
      (((sp + 1888#64) ↦₆₄ x23Val) ∗ Spill21Mem (sp + 1920#64) tOut ∗
        PolyMem (sp + 5680#64) (polyVecNat uHat0) ∗
        PolyMem (sp + 6192#64) (polyVecNat uHat1) ∗
        PolyMem (sp + 6704#64) (polyVecNat uHat2) ∗
        PolyMem (sp + 20704#64) (polyVecNat (neonInvNttMontgomery16 dot)) ∗
        PolyMem (sp + 22400#64) (polyVecNat sHat0) ∗
        PolyMem (sp + 22912#64) (polyVecNat sHat1) ∗
        PolyMem (sp + 23424#64) (polyVecNat sHat2) ∗ Rest))
    (Entails.trans (sepConj_mono_left hm11) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3a

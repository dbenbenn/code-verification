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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Sym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Prf
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3FwdLow

/-!
# `encapsulate1_serialized` (`B03`) — Segment 3 (`+0x3280 .. +0x4728`) (`Seg3`)

Composes `Seg3Prf` (`+0x3280 → +0x3624`) and three iterations (`idx = 0, 1, 2`) of
`Seg3Cbd` (`+0x3624 → +0x3754`), upper 5-stage binomial `NTT` (`Seg3Sym`, `+0x3760 → +0x4398`),
lower 2-stage `NTT` (`Seg3FwdLow`, `+0x4398 → +0x4484`), and Barrett reduction (`Seg3Sym`,
`+0x4484 → +0x4728`) to produce `rHat[0..2]` at `[sp + 12448, sp + 13984)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 neonBarrettReduce16 polyNtt samplePolyCbd2 shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16 neonCbd2Poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (
  neonNttStage16 neonPolyNttBinomial16 neonPolyNttBinomial16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 Vec32 VecRangeMem poly32Mem_ofFn polyVecNat step_ldrQ128
  vecRangeMem_congr vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure (
  barrett_lowerFwdNtt16_upperBinomial lowerFwdNtt16 lowerFwdNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr Spill40 SpillSliceMem SymEnv SymGprs SymSpill40 SymState SymVRegs SymVec32
  evalSExpr evalSymGpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SrcOptMem SymSpatial SymStateMatches polyPtr symSpill40_eval_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  lowerNttBinomial5_16 lowerNttBinomial5_16_size poly_eq_barrett poly_eq_lowerNttBinomial5_src)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03 blkPlaceable03 blkTree03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Sym (
  Src4272OptMem SymSpatial03 cfgSeg3Bar cfgSeg3Ntt noReloc_seg3_bar_a noReloc_seg3_bar_b
  noReloc_seg3_ntt run_seg3_bar_a run_seg3_bar_b run_seg3_ntt seg3SpillConsts
  seg3_bar_ast_eq seg3_bar_noSpillVreg seg3_ntt_ast_eq seg3_ntt_noSpillVreg
  sepWP_of_runSymRange03 symSeg3BarEnd symSeg3BarEnd_gprs symSeg3BarEnd_vreg3
  symSeg3BarInit symSeg3BarMid symSeg3BarMid_gpr4 symSeg3NttEnd symSeg3NttEnd_gprs
  symSeg3NttEnd_spill_const symSeg3NttEnd_vreg3 symSeg3NttInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  offSeg3CbdEnd offSeg3CbdStart ro00Sym seg3_cbd2_loop shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Prf (seg3_prf_setup)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3FwdLow (
  offFwd4 offFwdEnd seg3_fwd_low_ok)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03
  [0x3758 → 0x375c, 0x44b0 → 0x44b0, 0x4720 → 0x4724]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl03_ρ [MlKemPlacement] (sym : String) :
    blkPl03.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC03 polyVecNat

@[simp, arm64_norm, wp_norm] abbrev offSeg3Start    : BitVec 64 := BitVec.ofNat 64 12928
@[simp, arm64_norm, wp_norm] abbrev offSeg3NttStart : BitVec 64 := BitVec.ofNat 64 14176
@[simp, arm64_norm, wp_norm] abbrev offSeg3Cmp      : BitVec 64 := BitVec.ofNat 64 17584
@[simp, arm64_norm, wp_norm] abbrev offSeg3BarB     : BitVec 64 := BitVec.ofNat 64 17588
@[simp, arm64_norm, wp_norm] abbrev offSeg3Tail     : BitVec 64 := BitVec.ofNat 64 18208
@[simp, arm64_norm, wp_norm] abbrev offSeg3End      : BitVec 64 := BitVec.ofNat 64 18216

/-! ## 1. Pure `rHatPoly16` Soundness & Symbolic Environment Helpers -/

/-- `Poly16` result of `cbd2` followed by 7-stage binomial NEON `NTT` + Barrett reduction. -/
def rHatPoly16 (prf : List (BitVec 8)) : Poly16 :=
  neonPolyNttBinomial16 (neonCbd2Poly16 prf)

theorem rHatPoly16_spec {prf : List (BitVec 8)} (hprf : prf.length = 128) :
    (polyNtt (samplePolyCbd2 prf)).size = 256 ∧
    PolyBounded16 1664 (rHatPoly16 prf) ∧
    PolyRepresents (rHatPoly16 prf) (polyNtt (samplePolyCbd2 prf)) := by
  unfold rHatPoly16
  obtain ⟨⟨hsz, hb2⟩, hr⟩ := neonCbd2Poly16_spec hprf
  have hb3 : PolyBounded16 3 (neonCbd2Poly16 prf) :=
    ⟨hsz, fun i hi => ⟨by have := (hb2 i hi).1; omega, by have := (hb2 i hi).2; omega⟩⟩
  exact neonPolyNttBinomial16_spec hb3 hr (by simp [samplePolyCbd2])

private theorem barrett_lowerFwd_lowerBinomial5 (p0 : Poly16) :
    (lowerFwdNtt16 (lowerNttBinomial5_16 p0)).map neonBarrettReduce16 =
      neonPolyNttBinomial16 p0 :=
  barrett_lowerFwdNtt16_upperBinomial p0

private def mkNttEnv (s : State) (t : Spill40) (fDst : Nat → BitVec 128) (cbd : Poly16) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := t
  poly0   := Vec32.ofFn fDst
  src0    := Vec32.ofFn (polyVecNat cbd)
  gpr0    := fun r => s.readReg64 (.gpr r)
  pstate0 := s.pstate

private def mkBarEnv (s : State) (q : Poly16) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := Spill40.ofFn (fun _ => 0#128)
  poly0   := Vec32.ofFn (polyVecNat q)
  src0    := Vec32.zero
  gpr0    := fun r => s.readReg64 (.gpr r)
  pstate0 := s.pstate

private theorem matches_nttInit {sp : BitVec 64} {s : State}
    (t : Spill40) (fDst : Nat → BitVec 128) (cbd : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hv0 : s.readVReg128 0#5 = polyVecNat cbd 16)
    (hv2 : s.readVReg128 2#5 = polyVecNat cbd 18)
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16)
    (hx1 : s.readReg64 .x1 = 0xf301#64) (hx3 : s.readReg64 .x3 = 0x4ebf#64)
    (hx12 : s.readReg64 .x12 = 0xf9fa#64) (hx13 : s.readReg64 .x13 = 0x47fa#64)
    (hx14 : s.readReg64 .x14 = 0x019b#64) (hx15 : s.readReg64 .x15 = 0x229b#64)
    (hx16 : s.readReg64 .x16 = 0x6833#64) (hx17 : s.readReg64 .x17 = 0xf9dd#64)
    (hx18 : s.readReg64 .x18 = 0xc0dd#64) :
    SymStateMatches sp (mkNttEnv s t fDst cbd) symSeg3NttInit s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 => simpa [symSeg3NttInit, SymVRegs.get, evalSExpr, mkNttEnv, Vec32.ofFn, Vec32.get] using hv0
    | 2 => simpa [symSeg3NttInit, SymVRegs.get, evalSExpr, mkNttEnv, Vec32.ofFn, Vec32.get] using hv2
    | 3 => simpa [symSeg3NttInit, SymVRegs.get, evalSExpr] using hv3
    | 1 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 1 => exact hx1
    | 3 => exact hx3
    | 12 => exact hx12 | 13 => exact hx13 | 14 => exact hx14 | 15 => exact hx15
    | 16 => exact hx16 | 17 => exact hx17 | 18 => exact hx18
    | 0 | 2 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 19 | 20 | 21
    | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symSeg3NttInit, SymGprs.get, evalSymGpr, mkNttEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem matches_barInit {sp : BitVec 64} {s : State} (q : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16)
    (hx1 : s.readReg64 .x1 = 0xf301#64) (hx3 : s.readReg64 .x3 = 0x4ebf#64)
    (hx12 : s.readReg64 .x12 = 0xf9fa#64) (hx13 : s.readReg64 .x13 = 0x47fa#64)
    (hx14 : s.readReg64 .x14 = 0x019b#64) (hx15 : s.readReg64 .x15 = 0x229b#64)
    (hx16 : s.readReg64 .x16 = 0x6833#64) (hx17 : s.readReg64 .x17 = 0xf9dd#64)
    (hx18 : s.readReg64 .x18 = 0xc0dd#64) :
    SymStateMatches sp (mkBarEnv s q) symSeg3BarInit s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 3 => simpa [symSeg3BarInit, SymVRegs.get, evalSExpr] using hv3
    | 0 | 1 | 2 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 1 => exact hx1
    | 3 => exact hx3
    | 12 => exact hx12 | 13 => exact hx13 | 14 => exact hx14 | 15 => exact hx15
    | 16 => exact hx16 | 17 => exact hx17 | 18 => exact hx18
    | 0 | 2 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 19 | 20 | 21
    | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symSeg3BarInit, SymGprs.get, evalSymGpr, mkBarEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem evalSExpr_pstate0_irrel (env : SymEnv) (ps : PState) (e : SExpr) :
    evalSExpr { env with pstate0 := ps } e = evalSExpr env e := by
  induction e <;> simp [evalSExpr, *]

private theorem spillSlice40_nttInit (sp : BitVec 64) {t : Spill40}
    (ht : ∀ env i, i < 24 → t.get i = evalSExpr env (seg3SpillConsts.get i))
    (env : SymEnv) (hsp0 : env.spill0 = t) :
    SpillSliceMem 40 (sp + 1552#64) (symSeg3NttInit.spill.eval env) =
      SpillSliceMem 40 (sp + 1552#64) t :=
  vecRangeMem_congr fun i hi => by
    rw [symSpill40_eval_get env symSeg3NttInit.spill i hi]
    dsimp only [symSeg3NttInit]
    by_cases h24 : i < 24
    · exact (ht env i h24).symm
    · match i with
      | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31
      | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 =>
        simp [seg3SpillConsts, SymSpill40.get, evalSExpr, hsp0]
      | _ + 40 => omega

private theorem spill_consts24_nttEnd (env0 env : SymEnv) (i : Nat) (hi : i < 24) :
    (symSeg3NttEnd.spill.eval env0).get i = evalSExpr env (seg3SpillConsts.get i) := by
  rw [symSpill40_eval_get env0 symSeg3NttEnd.spill i (by omega), symSeg3NttEnd_spill_const i hi]
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11
  | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 =>
    rfl
  | _ + 24 => omega

/-! ## 2. Glue Lemmas (`+0x3754 → +0x3760`, `+0x44b0 → +0x44b4`, `+0x4720 → +0x3624/+0x4728`) -/

private theorem seg3_pre_ntt [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (_hidx : idx < 3) (cbd : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg3CbdEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 idx)
    (hx20 : s.readReg64 .x20 = sp + 12448#64) :
    let polyAddr := sp + 12448#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg3NttStart) s
      (PolyMem (sp + 4272#64) (polyVecNat cbd) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readVReg128 0#5 = polyVecNat cbd 16 ∧
        sf.readVReg128 2#5 = polyVecNat cbd 18 ∧
        sf.readVReg128 3#5 = s.readVReg128 3#5 ∧
        sf.readReg64 .x5 = polyAddr ∧
        (∀ r : BitVec 5, r ≠ 5#5 → r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = (PolyMem (sp + 4272#64) (polyVecNat cbd) ∗ Rest)) := by
  dsimp only
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine step_ldrQ128 (wb := none) (ea := sp + 4272#64 + BitVec.ofNat 64 (16 * 16)) (v := polyVecNat cbd 16)
    (by wp_norm_lhs) hrun (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 16) (by omega) rfl))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := sp + 4272#64 + BitVec.ofNat 64 (16 * 18)) (v := polyVecNat cbd 18)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 18) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
      by simp, by simp, by simp,
      by simp; clear * -; bv_omega,
      fun r hr5 hr31 => ?_, rfl⟩
  rcases r with ⟨rv, hrv⟩
  match rv with
  | 0 | 1 | 2 | 3 | 4 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
  | 5 => exact absurd rfl hr5
  | 31 => exact absurd rfl hr31
  | _ + 32 => omega

set_option maxRecDepth 100000 in
private theorem seg3_cmp3 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) {idx : Nat} (hidx : idx < 3) (P : SepProp)
    (hpc : s.pc = b + offSeg3Cmp) (hrun : s.status = .Running)
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 (idx + 1)) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg3BarB) s P
      (fun sf Pf =>
        sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        sf.vregs = s.vregs ∧
        (∀ r : BitVec 5, r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        sf.pstate.z = decide (idx = 2) ∧
        Pf = P) := by
  subst hbase
  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 by omega) with rfl | rfl | rfl <;> {
    wp_step
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], rfl, fun r hr => ?_,
       by simp [subsPState64, AddWithCarry64], rfl⟩
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
    | 31 => exact absurd rfl hr
    | _ + 32 => omega
  }

set_option maxRecDepth 100000 in
private theorem seg3_loop_tail [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) {idx : Nat} (hidx : idx < 3) (P : SepProp)
    (hpc : s.pc = b + offSeg3Tail) (hrun : s.status = .Running)
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 (idx + 1))
    (hpz : s.pstate.z = decide (idx = 2)) :
    SepWP (blkPC03.rebase b (fun _ => none))
      (if idx < 2 then b + offSeg3CbdStart else b + offSeg3End) s P
      (fun sf Pf =>
        sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        sf.vregs = s.vregs ∧
        sf.readReg64 .x5 = BitVec.ofNat 64 (idx + 1) ∧
        (∀ r : BitVec 5, r ≠ 5#5 → r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = P) := by
  subst hbase
  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 by omega) with rfl | rfl | rfl <;> {
    simp only [show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide,
      show ¬((2 : Nat) < 2) by decide, ↓reduceIte]
    wp_steps 2
    refine SepWP.done (by simp [ConditionHolds, hpz]) (by simp [hrun])
      ⟨rfl, rfl, rfl, by simp, fun r hr5 hr31 => ?_, rfl⟩
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
    | 5 => exact absurd rfl hr5
    | 31 => exact absurd rfl hr31
    | _ + 32 => omega
  }

/-! ## 3. Single-Iteration `cbd2 + Fwd2 NTT + Barrett` Body (`+0x3624 → +0x3624 / +0x4728`) -/

private theorem seg3_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3)
    (prf : List (BitVec 8)) (hprf : prf.length = 128)
    (t : Spill40) (ht : ∀ env i, i < 24 → t.get i = evalSExpr env (seg3SpillConsts.get i))
    (fDst : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg3CbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx1 : s.readReg64 .x1 = 0xf301#64)
    (hx2 : s.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx3 : s.readReg64 .x3 = 0x4ebf#64)
    (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 idx)
    (hx7 : s.readReg64 .x7 = sp + 2193#64 + BitVec.ofNat 64 (128 * idx))
    (hx9 : s.readReg64 .x9 = sp + 12464#64 + BitVec.ofNat 64 (512 * idx))
    (hx10 : s.readReg64 .x10 = 16#64 + BitVec.ofNat 64 (512 * idx))
    (hx12 : s.readReg64 .x12 = 0xf9fa#64) (hx13 : s.readReg64 .x13 = 0x47fa#64)
    (hx14 : s.readReg64 .x14 = 0x019b#64) (hx15 : s.readReg64 .x15 = 0x229b#64)
    (hx16 : s.readReg64 .x16 = 0x6833#64) (hx17 : s.readReg64 .x17 = 0xf9dd#64)
    (hx18 : s.readReg64 .x18 = 0xc0dd#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 12448#64)
    (hx21 : s.readReg64 .x21 = sp + 4272#64)
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16) :
    let prfPtr := sp + BitVec.ofNat 64 (2192 + 128 * idx)
    let polyAddr := sp + 12448#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC03.rebase b (fun _ => none))
      (if idx < 2 then b + offSeg3CbdStart else b + offSeg3End) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 4272#64) 512 ∗
        SpillSliceMem 40 (sp + 1552#64) t ∗ PolyMem polyAddr fDst ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧
        sf.readReg64 .x1 = 0xf301#64 ∧
        sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        sf.readReg64 .x3 = 0x4ebf#64 ∧
        sf.readReg64 .x5 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x7 = sp + 2193#64 + BitVec.ofNat 64 (128 * (idx + 1)) ∧
        sf.readReg64 .x9 = sp + 12464#64 + BitVec.ofNat 64 (512 * (idx + 1)) ∧
        sf.readReg64 .x10 = 16#64 + BitVec.ofNat 64 (512 * (idx + 1)) ∧
        sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
        sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
        sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
        sf.readReg64 .x18 = 0xc0dd#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 12448#64 ∧
        sf.readReg64 .x21 = sp + 4272#64 ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        ∃ t' : Spill40, (∀ env i, i < 24 → t'.get i = evalSExpr env (seg3SpillConsts.get i)) ∧
          (Pf ⊢ (prfPtr ↦ₛ prf) ∗ memRegion (sp + 4272#64) 512 ∗
            SpillSliceMem 40 (sp + 1552#64) t' ∗
            PolyMem polyAddr (polyVecNat (rHatPoly16 prf)) ∗ Rest)) := by
  dsimp only
  set prfPtr := sp + BitVec.ofNat 64 (2192 + 128 * idx)
  set polyAddr := sp + 12448#64 + BitVec.ofNat 64 (512 * idx)
  set cbd := neonCbd2Poly16 prf
  have hcbd : cbd.size = 256 := (neonCbd2Poly16_spec hprf).1.1
  have hx7' : s.readReg64 .x7 = prfPtr + 1#64 := by
    rw [hx7]; dsimp only [prfPtr]; clear * -; bv_omega
  refine sepWP_seq_env hcl hro
    (seg3_cbd2_loop hb hbase s sp prfPtr prf
      (SpillSliceMem 40 (sp + 1552#64) t ∗ PolyMem polyAddr fDst ∗ Rest)
      hprf hpc hrun hsp hspA hx7' hx19 hx21) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, r0, r1, r2, r3, r4, r5, r7, r9, r10, r12, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, _, rv3, rfl⟩
  refine SepWP.weaken_pre
    (show (prfPtr ↦ₛ prf) ∗ PolyMem (sp + 4272#64) (polyVecNat cbd) ∗
        (SpillSliceMem 40 (sp + 1552#64) t ∗ PolyMem polyAddr fDst ∗ Rest) ⊢
      PolyMem (sp + 4272#64) (polyVecNat cbd) ∗
        ((prfPtr ↦ₛ prf) ∗ SpillSliceMem 40 (sp + 1552#64) t ∗ PolyMem polyAddr fDst ∗ Rest) by
      sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg3_pre_ntt hb hbase s1 sp hidx cbd _ hpc1 hrun1 hsp1 hspA1
      (r5.trans hx5) (r20.trans hx20)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hv0_2, hv2_2, hv3_2, hx5_2, hgpr2, rfl⟩
  have hx0_2 : s2.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 :=
    (hgpr2 0#5 (by decide) (by decide)).trans (r0.trans hx0)
  have hx1_2 : s2.readReg64 .x1 = 0xf301#64 :=
    (hgpr2 1#5 (by decide) (by decide)).trans (r1.trans hx1)
  have hx2_2 : s2.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 :=
    (hgpr2 2#5 (by decide) (by decide)).trans (r2.trans hx2)
  have hx3_2 : s2.readReg64 .x3 = 0x4ebf#64 :=
    (hgpr2 3#5 (by decide) (by decide)).trans (r3.trans hx3)
  have hx4_2 : s2.readReg64 .x4 = BitVec.ofNat 64 (idx + 1) := by
    have h4 := (hgpr2 4#5 (by decide) (by decide)).trans r4
    rw [show s2.readReg64 (.gpr 4#5) = s2.readReg64 .x4 from rfl] at h4
    rw [h4, hx5]; clear * -; bv_omega
  have hx7_2 : s2.readReg64 .x7 = prfPtr + 1#64 :=
    (hgpr2 7#5 (by decide) (by decide)).trans r7
  have hx9_2 : s2.readReg64 .x9 = polyAddr + 16#64 := by
    have h9 := (hgpr2 9#5 (by decide) (by decide)).trans (r9.trans hx9)
    rw [show s2.readReg64 (.gpr 9#5) = s2.readReg64 .x9 from rfl] at h9
    rw [h9]; dsimp only [polyAddr]; clear * -; bv_omega
  have hx10_2 : s2.readReg64 .x10 = 16#64 + BitVec.ofNat 64 (512 * idx) :=
    (hgpr2 10#5 (by decide) (by decide)).trans (r10.trans hx10)
  have hx12_2 : s2.readReg64 .x12 = 0xf9fa#64 :=
    (hgpr2 12#5 (by decide) (by decide)).trans (r12.trans hx12)
  have hx13_2 : s2.readReg64 .x13 = 0x47fa#64 :=
    (hgpr2 13#5 (by decide) (by decide)).trans (r13.trans hx13)
  have hx14_2 : s2.readReg64 .x14 = 0x019b#64 :=
    (hgpr2 14#5 (by decide) (by decide)).trans (r14.trans hx14)
  have hx15_2 : s2.readReg64 .x15 = 0x229b#64 :=
    (hgpr2 15#5 (by decide) (by decide)).trans (r15.trans hx15)
  have hx16_2 : s2.readReg64 .x16 = 0x6833#64 :=
    (hgpr2 16#5 (by decide) (by decide)).trans (r16.trans hx16)
  have hx17_2 : s2.readReg64 .x17 = 0xf9dd#64 :=
    (hgpr2 17#5 (by decide) (by decide)).trans (r17.trans hx17)
  have hx18_2 : s2.readReg64 .x18 = 0xc0dd#64 :=
    (hgpr2 18#5 (by decide) (by decide)).trans (r18.trans hx18)
  have hx19_2 : s2.readReg64 .x19 = 0x55555555#64 :=
    (hgpr2 19#5 (by decide) (by decide)).trans r19
  have hx20_2 : s2.readReg64 .x20 = sp + 12448#64 :=
    (hgpr2 20#5 (by decide) (by decide)).trans (r20.trans hx20)
  have hx21_2 : s2.readReg64 .x21 = sp + 4272#64 :=
    (hgpr2 21#5 (by decide) (by decide)).trans r21
  set envN := mkNttEnv s2 t fDst cbd
  set F_ntt := (prfPtr ↦ₛ prf) ∗ Rest
  have hP2_sym : PolyMem (sp + 4272#64) (polyVecNat cbd) ∗
      ((prfPtr ↦ₛ prf) ∗ SpillSliceMem 40 (sp + 1552#64) t ∗ PolyMem polyAddr fDst ∗ Rest) ⊢
      SymSpatial03 true cfgSeg3Ntt sp envN symSeg3NttInit F_ntt := by
    have hpoly_init : symSeg3NttInit.poly.eval envN = Vec32.ofFn fDst := rfl
    have hsrc_init : envN.src0 = Vec32.ofFn (polyVecNat cbd) := rfl
    dsimp only [SymSpatial03, SymSpatial, cfgSeg3Ntt, polyPtr, SrcOptMem, Src4272OptMem, F_ntt]
    rw [spillSlice40_nttInit sp ht envN rfl,
        show envN.gpr0 5#5 = polyAddr from hx5_2, hpoly_init, hsrc_init,
        ← poly32Mem_ofFn polyAddr fDst,
        ← poly32Mem_ofFn (sp + 4272#64) (polyVecNat cbd)]
    change Poly32Mem (sp + 4272#64) _ ∗ ((prfPtr ↦ₛ prf) ∗ SpillSliceMem 40 (sp + 1552#64) t ∗
        Poly32Mem polyAddr _ ∗ Rest) ⊢
      SpillSliceMem 40 (sp + 1552#64) t ∗ Poly32Mem polyAddr _ ∗ emp ∗
        (Poly32Mem (sp + 4272#64) _ ∗ ((prfPtr ↦ₛ prf) ∗ Rest))
    sep_frame
  refine SepWP.weaken_pre hP2_sym
    (sepWP_seq_env hcl2 hro2
      (sepWP_of_runSymRange03 (src4272 := true) (cfg := cfgSeg3Ntt) (env := envN) (F := F_ntt)
        782 3544 noReloc_seg3_ntt (by decide) (by decide) (by decide)
        run_seg3_ntt
        (matches_nttInit t fDst cbd hsp2 hspA2 hv0_2 hv2_2 (hv3_2.trans (rv3.trans hv3))
          hx1_2 hx3_2 hx12_2 hx13_2 hx14_2 hx15_2 hx16_2 hx17_2 hx18_2)
        hpc2 hrun2
        (post := fun s3 P3 => SymStateMatches sp envN symSeg3NttEnd s3 ∧
          P3 = SymSpatial03 true cfgSeg3Ntt sp envN symSeg3NttEnd F_ntt)
        (fun s3 _ _ hm3 => ⟨hm3, rfl⟩)) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hm3, rfl⟩
  rcases symSeg3NttEnd_gprs with ⟨ng0, ng1, ng2, ng3, ng4, ng5, ng6, ng7, ng8, ng9, ng10,
    ng12, ng13, ng14, ng15, ng16, ng17, ng18, ng19, ng20, ng21, ng22, _, _⟩
  have gpr3_eq : ∀ (r : Nat) (_hr : BitVec.ofNat 5 r ≠ 31#5) (_hlt : r < 32),
      s3.readReg64 (.gpr (BitVec.ofNat 5 r)) = evalSymGpr sp envN.gpr0 (symSeg3NttEnd.gprs.get r) :=
    fun r hr hlt => by simpa [Nat.mod_eq_of_lt hlt] using hm3.hgprs (BitVec.ofNat 5 r) hr
  have hx0_3 : s3.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 := by
    have h := gpr3_eq 0 (by decide) (by decide); rw [ng0] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx0_2
  have hx1_3 : s3.readReg64 .x1 = 0xf301#64 := by
    have h := gpr3_eq 1 (by decide) (by decide); rw [ng1] at h; exact h
  have hx2_3 : s3.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 := by
    have h := gpr3_eq 2 (by decide) (by decide); rw [ng2] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx2_2
  have hx3_3 : s3.readReg64 .x3 = 0x4ebf#64 := by
    have h := gpr3_eq 3 (by decide) (by decide); rw [ng3] at h; exact h
  have hx4_3 : s3.readReg64 .x4 = BitVec.ofNat 64 (idx + 1) := by
    have h := gpr3_eq 4 (by decide) (by decide); rw [ng4] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx4_2
  have hx5_3 : s3.readReg64 .x5 = polyAddr := by
    have h := gpr3_eq 5 (by decide) (by decide); rw [ng5] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx5_2
  have hx6_3 : s3.readReg64 .x6 = polyAddr + 16#64 := by
    have h := gpr3_eq 6 (by decide) (by decide); rw [ng6] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx9_2
  have hx7_3 : s3.readReg64 .x7 = prfPtr + 1#64 := by
    have h := gpr3_eq 7 (by decide) (by decide); rw [ng7] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx7_2
  have hx8_3 : s3.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64 := by
    have h := gpr3_eq 8 (by decide) (by decide); rw [ng8] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx0_2
  have hx9_3 : s3.readReg64 .x9 = polyAddr + 16#64 := by
    have h := gpr3_eq 9 (by decide) (by decide); rw [ng9] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx9_2
  have hx10_3 : s3.readReg64 .x10 = 16#64 + BitVec.ofNat 64 (512 * idx) := by
    have h := gpr3_eq 10 (by decide) (by decide); rw [ng10] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx10_2
  have hx12_3 : s3.readReg64 .x12 = 0xf9fa#64 := by
    have h := gpr3_eq 12 (by decide) (by decide); rw [ng12] at h; exact h
  have hx13_3 : s3.readReg64 .x13 = 0x47fa#64 := by
    have h := gpr3_eq 13 (by decide) (by decide); rw [ng13] at h; exact h
  have hx14_3 : s3.readReg64 .x14 = 0x019b#64 := by
    have h := gpr3_eq 14 (by decide) (by decide); rw [ng14] at h; exact h
  have hx15_3 : s3.readReg64 .x15 = 0x229b#64 := by
    have h := gpr3_eq 15 (by decide) (by decide); rw [ng15] at h; exact h
  have hx16_3 : s3.readReg64 .x16 = 0x6833#64 := by
    have h := gpr3_eq 16 (by decide) (by decide); rw [ng16] at h; exact h
  have hx17_3 : s3.readReg64 .x17 = 0xf9dd#64 := by
    have h := gpr3_eq 17 (by decide) (by decide); rw [ng17] at h; exact h
  have hx18_3 : s3.readReg64 .x18 = 0xc0dd#64 := by
    have h := gpr3_eq 18 (by decide) (by decide); rw [ng18] at h; exact h
  have hx19_3 : s3.readReg64 .x19 = 0x55555555#64 := by
    have h := gpr3_eq 19 (by decide) (by decide); rw [ng19] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = sp + 12448#64 := by
    have h := gpr3_eq 20 (by decide) (by decide); rw [ng20] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = sp + 4272#64 := by
    have h := gpr3_eq 21 (by decide) (by decide); rw [ng21] at h
    simp only [evalSymGpr, envN, mkNttEnv, BitVec.add_zero] at h; exact h.trans hx21_2
  have hx22_3 : s3.readReg64 .x22 = 16#64 := by
    have h := gpr3_eq 22 (by decide) (by decide); rw [ng22] at h; exact h
  have hv3_3 : s3.readVReg128 3#5 = dup8x16 3329#16 := by
    have h : s3.readVReg128 3#5 = evalSExpr envN (symSeg3NttEnd.vregs.get 3) := hm3.hvregs 3#5
    rw [symSeg3NttEnd_vreg3] at h; exact h

  set t1 := symSeg3NttEnd.spill.eval envN
  have ht1 : ∀ env i, i < 24 → t1.get i = evalSExpr env (seg3SpillConsts.get i) :=
    fun env i hi => spill_consts24_nttEnd envN env i hi
  set p3 := lowerNttBinomial5_16 cbd
  have hp3 : p3.size = 256 := (lowerNttBinomial5_16_size cbd).trans hcbd
  have hp3_mem : Poly32Mem (polyPtr cfgSeg3Ntt sp envN) (symSeg3NttEnd.poly.eval envN) =
      PolyMem polyAddr (polyVecNat p3) := by
    have hptr : polyPtr cfgSeg3Ntt sp envN = polyAddr := hx5_2
    rw [hptr]
    exact poly_eq_lowerNttBinomial5_src polyAddr hcbd envN rfl symSeg3NttEnd.poly
      seg3_ntt_noSpillVreg seg3_ntt_ast_eq
  have hsrc3 : Src4272OptMem true sp envN.src0 ⊢ memRegion (sp + 4272#64) 512 := by
    dsimp only [Src4272OptMem, Poly32Mem, PolyMem]
    simpa using vecRangeMem_entails_memRegion 32 (sp + 4272#64) (fun i => envN.src0.get i)
  set F_low := memRegion (sp + 4272#64) 512 ∗ SpillSliceMem 40 (sp + 1552#64) t1 ∗ F_ntt
  have hP3_low : SymSpatial03 true cfgSeg3Ntt sp envN symSeg3NttEnd F_ntt ⊢
      PolyMem polyAddr (polyVecNat p3) ∗ F_low := by
    dsimp only [SymSpatial03, SymSpatial, SrcOptMem, F_low, t1]
    rw [hp3_mem]
    dsimp only [cfgSeg3Ntt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact entails_sub hsrc3 (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP3_low
    (sepWP_seq_env hcl3 hro3
      (seg3_fwd_low_ok hb s3 sp polyAddr hp3 F_low
        hpc3 hrun3 hm3.hsp hm3.hsp_al hcl3 hro3 hx8_3 hx2_3 hx6_3 hx22_3 hx1_3
        (by rw [hx20_3, hx10_3]; dsimp only [polyAddr]; clear * -; bv_omega) hv3_3) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hpres4, _, _, rfl⟩
  set q := lowerFwdNtt16 p3
  have hq : q.size = 256 := (lowerFwdNtt16_size p3).trans hp3
  set envB := mkBarEnv s4 q
  have hP4_bar : PolyMem polyAddr (polyVecNat q) ∗ F_low ⊢
      SymSpatial03 false cfgSeg3Bar sp envB symSeg3BarInit F_low := by
    dsimp only [SymSpatial03, SymSpatial, cfgSeg3Bar, polyPtr, SrcOptMem, Src4272OptMem,
      SpillSliceMem, VecRangeMem, envB, mkBarEnv]
    rw [hpres4.x5.trans hx5_3, ← poly32Mem_ofFn polyAddr (polyVecNat q)]
    change Poly32Mem polyAddr _ ∗ F_low ⊢ emp ∗ Poly32Mem polyAddr _ ∗ emp ∗ (emp ∗ F_low)
    sep_frame
  refine SepWP.weaken_pre hP4_bar
    (sepWP_seq_env hcl4 hro4
      (sepWP_of_runSymRange03 (src4272 := false) (cfg := cfgSeg3Bar) (env := envB) (F := F_low)
        11 4385 noReloc_seg3_bar_a (by decide) (by decide) (by decide)
        run_seg3_bar_a
        (matches_barInit q hsp4 hspA4 (hpres4.v3.trans hv3_3)
          (hpres4.x1.trans hx1_3) (hpres4.x3.trans hx3_3)
          (hpres4.x12.trans hx12_3) (hpres4.x13.trans hx13_3)
          (hpres4.x14.trans hx14_3) (hpres4.x15.trans hx15_3)
          (hpres4.x16.trans hx16_3) (hpres4.x17.trans hx17_3)
          (hpres4.x18.trans hx18_3))
        hpc4 hrun4
        (post := fun s5 P5 => SymStateMatches sp envB symSeg3BarMid s5 ∧
          P5 = SymSpatial03 false cfgSeg3Bar sp envB symSeg3BarMid F_low)
        (fun s5 _ _ hm5 => ⟨hm5, rfl⟩)) ?_)
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hm5, rfl⟩
  have hx4_5 : s5.readReg64 .x4 = BitVec.ofNat 64 (idx + 1) := by
    have h : s5.readReg64 (.gpr 4#5) = evalSymGpr sp envB.gpr0 (symSeg3BarMid.gprs.get 4) :=
      hm5.hgprs 4#5 (by decide)
    rw [symSeg3BarMid_gpr4] at h
    simp only [evalSymGpr, envB, mkBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x4.trans hx4_3)
  refine sepWP_seq_env hcl5 hro5
    (seg3_cmp3 hb hbase s5 hidx _ hpc5 hrun5 hx4_5) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 hro6 ⟨hsp6, hspA6, hvregs6, hgpr6, hpz6, rfl⟩
  set envB' : SymEnv := { envB with pstate0 := s6.pstate }
  have hm6 : SymStateMatches sp envB' symSeg3BarMid s6 := by
    refine ⟨hsp6.trans hm5.hsp, hspA6.trans hm5.hsp_al, rfl, fun r => ?_, fun r hr => ?_⟩
    · rw [State.readVReg128, hvregs6]
      exact (hm5.hvregs r).trans (evalSExpr_pstate0_irrel envB s6.pstate _).symm
    · exact (hgpr6 r hr).trans (hm5.hgprs r hr)
  have hP6_bar : SymSpatial03 false cfgSeg3Bar sp envB symSeg3BarMid F_low ⊢
      SymSpatial03 false cfgSeg3Bar sp envB' symSeg3BarMid F_low := by
    have hpoly : symSeg3BarMid.poly.eval envB = symSeg3BarMid.poly.eval envB' :=
      congrArg Vec32.ofFn (funext fun _ => (evalSExpr_pstate0_irrel envB s6.pstate _).symm)
    dsimp only [SymSpatial03, SymSpatial, cfgSeg3Bar, polyPtr, SrcOptMem, Src4272OptMem,
      SpillSliceMem, VecRangeMem, envB']
    rw [hpoly]; exact Entails.refl _
  refine SepWP.weaken_pre hP6_bar
    (sepWP_seq_env hcl6 hro6
      (sepWP_of_runSymRange03 (src4272 := false) (cfg := cfgSeg3Bar) (env := envB') (F := F_low)
        155 4397 noReloc_seg3_bar_b (by decide) (by decide) (by decide)
        run_seg3_bar_b hm6 hpc6 hrun6
        (post := fun s7 P7 => SymStateMatches sp envB' symSeg3BarEnd s7 ∧
          P7 = SymSpatial03 false cfgSeg3Bar sp envB' symSeg3BarEnd F_low)
        (fun s7 _ _ hm7 => ⟨hm7, rfl⟩)) ?_)
  rintro s7 P7 hpc7 hrun7 hcl7 hro7 ⟨hm7, rfl⟩
  rcases symSeg3BarEnd_gprs with ⟨bg0, bg1, bg2, bg3, bg4, bg5, bg7, bg9, bg10,
    bg12, bg13, bg14, bg15, bg16, bg17, bg18, bg19, bg20, bg21, _, _⟩
  have gpr7_eq : ∀ (r : Nat) (_hr : BitVec.ofNat 5 r ≠ 31#5) (_hlt : r < 32),
      s7.readReg64 (.gpr (BitVec.ofNat 5 r)) = evalSymGpr sp envB.gpr0 (symSeg3BarEnd.gprs.get r) :=
    fun r hr hlt => by simpa [Nat.mod_eq_of_lt hlt] using hm7.hgprs (BitVec.ofNat 5 r) hr
  have hx4_7 : s7.readReg64 .x4 = BitVec.ofNat 64 (idx + 1) := by
    have h := gpr7_eq 4 (by decide) (by decide); rw [bg4] at h
    simp only [evalSymGpr, envB, mkBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x4.trans hx4_3)
  have hpz7 : s7.pstate.z = decide (idx = 2) := hm7.hpstate ▸ hpz6
  have hp7_mem : Poly32Mem (polyPtr cfgSeg3Bar sp envB') (symSeg3BarEnd.poly.eval envB') =
      PolyMem polyAddr (polyVecNat (rHatPoly16 prf)) := by
    have hptr : polyPtr cfgSeg3Bar sp envB' = polyAddr := hpres4.x5.trans hx5_3
    rw [hptr, poly_eq_barrett polyAddr hq envB' rfl symSeg3BarEnd.poly
      seg3_bar_noSpillVreg seg3_bar_ast_eq, barrett_lowerFwd_lowerBinomial5 cbd]
    rfl
  have hP7 : SymSpatial03 false cfgSeg3Bar sp envB' symSeg3BarEnd F_low ⊢
      (prfPtr ↦ₛ prf) ∗ memRegion (sp + 4272#64) 512 ∗
        SpillSliceMem 40 (sp + 1552#64) t1 ∗ PolyMem polyAddr (polyVecNat (rHatPoly16 prf)) ∗ Rest := by
    dsimp only [SymSpatial03, SymSpatial, SrcOptMem, Src4272OptMem, F_low, F_ntt]
    rw [hp7_mem]
    dsimp only [cfgSeg3Bar, SpillSliceMem, VecRangeMem]
    change emp ∗ PolyMem polyAddr (polyVecNat (rHatPoly16 prf)) ∗ emp ∗
        (emp ∗ (memRegion (sp + 4272#64) 512 ∗ VecRangeMem 40 (sp + 1552#64) (fun i => t1.get i) ∗
          ((prfPtr ↦ₛ prf) ∗ Rest))) ⊢
      (prfPtr ↦ₛ prf) ∗ memRegion (sp + 4272#64) 512 ∗
        VecRangeMem 40 (sp + 1552#64) (fun i => t1.get i) ∗
        PolyMem polyAddr (polyVecNat (rHatPoly16 prf)) ∗ Rest
    sep_frame
  refine SepWP.weaken_pre hP7
    (sepWP_seq_env hcl7 hro7 (seg3_loop_tail hb hbase s7 hidx _ hpc7 hrun7 hx4_7 hpz7) ?_)
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hvregsf, hx5f, hgprf, rfl⟩
  have hvf : ∀ r : BitVec 5, sf.readVReg128 r = s7.readVReg128 r :=
    fun r => by simp [State.readVReg128, hvregsf]
  have hx0_f : sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 := by
    rw [show sf.readReg64 .x0 = sf.readReg64 (.gpr 0#5) from rfl, hgprf 0#5 (by decide) (by decide)]
    have h := gpr7_eq 0 (by decide) (by decide); rw [bg0] at h
    simp only [evalSymGpr, envB, mkBarEnv, BitVec.add_zero] at h; exact h.trans (hpres4.x0.trans hx0_3)
  have hx1_f : sf.readReg64 .x1 = 0xf301#64 := by
    rw [show sf.readReg64 .x1 = sf.readReg64 (.gpr 1#5) from rfl, hgprf 1#5 (by decide) (by decide)]
    have h := gpr7_eq 1 (by decide) (by decide); rw [bg1] at h; exact h
  have hx2_f : sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 := by
    rw [show sf.readReg64 .x2 = sf.readReg64 (.gpr 2#5) from rfl, hgprf 2#5 (by decide) (by decide)]
    have h := gpr7_eq 2 (by decide) (by decide); rw [bg2] at h
    simp only [evalSymGpr, envB, mkBarEnv, BitVec.add_zero] at h; exact h.trans (hpres4.x2.trans hx2_3)
  have hx3_f : sf.readReg64 .x3 = 0x4ebf#64 := by
    rw [show sf.readReg64 .x3 = sf.readReg64 (.gpr 3#5) from rfl, hgprf 3#5 (by decide) (by decide)]
    have h := gpr7_eq 3 (by decide) (by decide); rw [bg3] at h; exact h
  have hx7_f : sf.readReg64 .x7 = sp + 2193#64 + BitVec.ofNat 64 (128 * (idx + 1)) := by
    rw [show sf.readReg64 .x7 = sf.readReg64 (.gpr 7#5) from rfl, hgprf 7#5 (by decide) (by decide)]
    have h := gpr7_eq 7 (by decide) (by decide); rw [bg7] at h
    simp only [evalSymGpr, envB, mkBarEnv] at h
    rw [h, show s4.readReg64 (.gpr 7#5) = s4.readReg64 .x7 from rfl, hpres4.x7, hx7_3]
    dsimp only [prfPtr]; clear * - hidx; bv_omega
  have hx9_f : sf.readReg64 .x9 = sp + 12464#64 + BitVec.ofNat 64 (512 * (idx + 1)) := by
    rw [show sf.readReg64 .x9 = sf.readReg64 (.gpr 9#5) from rfl, hgprf 9#5 (by decide) (by decide)]
    have h := gpr7_eq 9 (by decide) (by decide); rw [bg9] at h
    simp only [evalSymGpr, envB, mkBarEnv] at h
    rw [h, show s4.readReg64 (.gpr 9#5) = s4.readReg64 .x9 from rfl, hpres4.x9, hx9_3]
    dsimp only [polyAddr]; clear * - hidx; bv_omega
  have hx10_f : sf.readReg64 .x10 = 16#64 + BitVec.ofNat 64 (512 * (idx + 1)) := by
    rw [show sf.readReg64 .x10 = sf.readReg64 (.gpr 10#5) from rfl, hgprf 10#5 (by decide) (by decide)]
    have h := gpr7_eq 10 (by decide) (by decide); rw [bg10] at h
    simp only [evalSymGpr, envB, mkBarEnv] at h
    rw [h, show s4.readReg64 (.gpr 10#5) = s4.readReg64 .x10 from rfl, hpres4.x10, hx10_3]
    clear * - hidx; bv_omega
  have hconst_f : sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
      sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
      sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
      sf.readReg64 .x18 = 0xc0dd#64 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show sf.readReg64 .x12 = sf.readReg64 (.gpr 12#5) from rfl, hgprf 12#5 (by decide) (by decide)]
      have h := gpr7_eq 12 (by decide) (by decide); rw [bg12] at h; exact h
    · rw [show sf.readReg64 .x13 = sf.readReg64 (.gpr 13#5) from rfl, hgprf 13#5 (by decide) (by decide)]
      have h := gpr7_eq 13 (by decide) (by decide); rw [bg13] at h; exact h
    · rw [show sf.readReg64 .x14 = sf.readReg64 (.gpr 14#5) from rfl, hgprf 14#5 (by decide) (by decide)]
      have h := gpr7_eq 14 (by decide) (by decide); rw [bg14] at h; exact h
    · rw [show sf.readReg64 .x15 = sf.readReg64 (.gpr 15#5) from rfl, hgprf 15#5 (by decide) (by decide)]
      have h := gpr7_eq 15 (by decide) (by decide); rw [bg15] at h; exact h
    · rw [show sf.readReg64 .x16 = sf.readReg64 (.gpr 16#5) from rfl, hgprf 16#5 (by decide) (by decide)]
      have h := gpr7_eq 16 (by decide) (by decide); rw [bg16] at h; exact h
    · rw [show sf.readReg64 .x17 = sf.readReg64 (.gpr 17#5) from rfl, hgprf 17#5 (by decide) (by decide)]
      have h := gpr7_eq 17 (by decide) (by decide); rw [bg17] at h; exact h
    · rw [show sf.readReg64 .x18 = sf.readReg64 (.gpr 18#5) from rfl, hgprf 18#5 (by decide) (by decide)]
      have h := gpr7_eq 18 (by decide) (by decide); rw [bg18] at h; exact h
  rcases hconst_f with ⟨hx12_f, hx13_f, hx14_f, hx15_f, hx16_f, hx17_f, hx18_f⟩
  have hx19_f : sf.readReg64 .x19 = 0x55555555#64 := by
    rw [show sf.readReg64 .x19 = sf.readReg64 (.gpr 19#5) from rfl, hgprf 19#5 (by decide) (by decide)]
    have h := gpr7_eq 19 (by decide) (by decide); rw [bg19] at h
    simp only [evalSymGpr, envB, mkBarEnv, BitVec.add_zero] at h; exact h.trans (hpres4.x19.trans hx19_3)
  have hx20_f : sf.readReg64 .x20 = sp + 12448#64 := by
    rw [show sf.readReg64 .x20 = sf.readReg64 (.gpr 20#5) from rfl, hgprf 20#5 (by decide) (by decide)]
    have h := gpr7_eq 20 (by decide) (by decide); rw [bg20] at h
    simp only [evalSymGpr, envB, mkBarEnv, BitVec.add_zero] at h; exact h.trans (hpres4.x20.trans hx20_3)
  have hx21_f : sf.readReg64 .x21 = sp + 4272#64 := by
    rw [show sf.readReg64 .x21 = sf.readReg64 (.gpr 21#5) from rfl, hgprf 21#5 (by decide) (by decide)]
    have h := gpr7_eq 21 (by decide) (by decide); rw [bg21] at h
    simp only [evalSymGpr, envB, mkBarEnv, BitVec.add_zero] at h; exact h.trans (hpres4.x21.trans hx21_3)
  have hv3_f : sf.readVReg128 3#5 = dup8x16 0x0d01#16 := by
    rw [hvf 3#5]
    have h : s7.readVReg128 3#5 = evalSExpr envB' (symSeg3BarEnd.vregs.get 3) := hm7.hvregs 3#5
    rw [symSeg3BarEnd_vreg3] at h; exact h
  exact SepWP.done hpcf hrunf
    ⟨hspf.trans hm7.hsp, hspAf.trans hm7.hsp_al, hx0_f, hx1_f, hx2_f, hx3_f,
      hx5f, hx7_f, hx9_f, hx10_f, hx12_f, hx13_f, hx14_f, hx15_f, hx16_f, hx17_f, hx18_f,
      hx19_f, hx20_f, hx21_f, hv3_f, hclf, hrof, t1, ht1, Entails.refl _⟩

/-! ## 4. Top-Level `Seg3` Composition (`+0x3280 → +0x4728`) -/

attribute [local irreducible] rHatPoly16 shake256List

/-- Full `Seg3` (`+0x3280 → +0x4728`): generates `prf0..2 = PRF(coins, 0..2)`, executes 3 iterations
of `cbd2 + Fwd2 NTT + Barrett`, and stores `rHat[0..2]` at `[sp + 12448, sp + 13984)`. -/
theorem seg3_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + offSeg3Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let coins := hashed.drop 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg3End) s
      (((sp + 6768#64) ↦ₛ hashed) ∗
       memRegion (sp + 1552#64) 640 ∗ memRegion (sp + 2192#64) 384 ∗
       memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 11440#64) 960 ∗
       memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12448#64) 1536 ∗
       memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
       memRegion (sp + 16208#64) 99 ∗ memRegion (sp + 16528#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 12448#64 ∧
        sf.readReg64 .x21 = sp + 4272#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ ((sp + 6768#64) ↦ₛ hashed) ∗
          memRegion (sp + 1552#64) 640 ∗
          ((sp + 2192#64) ↦ₛ prf0) ∗ ((sp + 2320#64) ↦ₛ prf1) ∗ ((sp + 2448#64) ↦ₛ prf2) ∗
          memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 11440#64) 960 ∗
          ((sp + 12400#64) ↦ₛ coins) ∗ ((sp + 12432#64) ↦₈ 0#8) ∗
          PolyMem (sp + 12448#64) (polyVecNat (rHatPoly16 prf0)) ∗
          PolyMem (sp + 12960#64) (polyVecNat (rHatPoly16 prf1)) ∗
          PolyMem (sp + 13472#64) (polyVecNat (rHatPoly16 prf2)) ∗
          memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
          memRegion (sp + 16208#64) 99 ∗ memRegion (sp + 16528#64) 128 ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro coins prf0 prf1 prf2
  have ha_12960 : sp + 12448#64 + 512#64 = sp + 12960#64 := by clear * -; bv_omega
  have ha_13472 : sp + 12448#64 + 1024#64 = sp + 13472#64 := by clear * -; bv_omega
  refine sepWP_seq_env hcl hro
    (seg3_prf_setup hb hbase s sp hashed Rest hh hpc hrun hsp hspA hcl hro) ?_
  rintro s0 P0 hpc0 hrun0 hcl0 hro0
    ⟨hsp0, hspA0, r0_0, r1_0, r2_0, r3_0, r5_0, r7_0, r9_0, r10_0, r12_0, r13_0,
      r14_0, r15_0, r16_0, r17_0, r18_0, r19_0, r20_0, r21_0, rv3_0, _, _, t0, ht0, hP0⟩
  have hP0' : P0 ⊢ ((sp + BitVec.ofNat 64 (2192 + 128 * 0)) ↦ₛ prf0) ∗ memRegion (sp + 4272#64) 512 ∗
      SpillSliceMem 40 (sp + 1552#64) t0 ∗
      PolyMem (sp + 12448#64 + BitVec.ofNat 64 (512 * 0)) (fun _ => 0#128) ∗
      (((sp + 2320#64) ↦ₛ prf1) ∗ ((sp + 2448#64) ↦ₛ prf2) ∗
        PolyMem (sp + 12960#64) (fun _ => 0#128) ∗ PolyMem (sp + 13472#64) (fun _ => 0#128) ∗
        ((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 11440#64) 960 ∗
        ((sp + 12400#64) ↦ₛ coins) ∗ ((sp + 12432#64) ↦₈ 0#8) ∗
        memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
        memRegion (sp + 16208#64) 99 ∗ memRegion (sp + 16528#64) 128 ∗ stackAt sp 1136 ∗ Rest) := by
    refine Entails.trans hP0 ?_
    simp only [Nat.mul_zero, Nat.add_zero, BitVec.add_zero]
    sep_frame
  refine SepWP.weaken_pre hP0'
    (sepWP_seq_env hcl0 hro0
      (seg3_iter hb hbase s0 sp (idx := 0) (by decide) prf0 (shake256List_length 128 _)
        t0 ht0 (fun _ => 0#128) _ hpc0 hrun0 hsp0 hspA0 hcl0 hro0
        r0_0 r1_0 r2_0 r3_0 r5_0 (by simpa using r7_0) (by simpa using r9_0) (by simpa using r10_0)
        r12_0 r13_0 r14_0 r15_0 r16_0 r17_0 r18_0 r19_0 r20_0 r21_0 rv3_0) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, r0_1, r1_1, r2_1, r3_1, r5_1, r7_1, r9_1, r10_1, r12_1, r13_1,
      r14_1, r15_1, r16_1, r17_1, r18_1, r19_1, r20_1, r21_1, rv3_1, _, _, t1, ht1, hP1⟩
  simp only [show (0 : Nat) < 2 by decide, ↓reduceIte] at hpc1
  have hP1' : P1 ⊢ ((sp + BitVec.ofNat 64 (2192 + 128 * 1)) ↦ₛ prf1) ∗ memRegion (sp + 4272#64) 512 ∗
      SpillSliceMem 40 (sp + 1552#64) t1 ∗
      PolyMem (sp + 12448#64 + BitVec.ofNat 64 (512 * 1)) (fun _ => 0#128) ∗
      (((sp + 2192#64) ↦ₛ prf0) ∗ ((sp + 2448#64) ↦ₛ prf2) ∗
        PolyMem (sp + 12448#64) (polyVecNat (rHatPoly16 prf0)) ∗
        PolyMem (sp + 13472#64) (fun _ => 0#128) ∗
        ((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 11440#64) 960 ∗
        ((sp + 12400#64) ↦ₛ coins) ∗ ((sp + 12432#64) ↦₈ 0#8) ∗
        memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
        memRegion (sp + 16208#64) 99 ∗ memRegion (sp + 16528#64) 128 ∗ stackAt sp 1136 ∗ Rest) := by
    refine Entails.trans hP1 ?_
    simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, BitVec.add_zero, ha_12960]
    sep_frame
  refine SepWP.weaken_pre hP1'
    (sepWP_seq_env hcl1 hro1
      (seg3_iter hb hbase s1 sp (idx := 1) (by decide) prf1 (shake256List_length 128 _)
        t1 ht1 (fun _ => 0#128) _ hpc1 hrun1 hsp1 hspA1 hcl1 hro1
        r0_1 r1_1 r2_1 r3_1 r5_1 r7_1 r9_1 r10_1
        r12_1 r13_1 r14_1 r15_1 r16_1 r17_1 r18_1 r19_1 r20_1 r21_1 rv3_1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, r0_2, r1_2, r2_2, r3_2, r5_2, r7_2, r9_2, r10_2, r12_2, r13_2,
      r14_2, r15_2, r16_2, r17_2, r18_2, r19_2, r20_2, r21_2, rv3_2, _, _, t2, ht2, hP2⟩
  simp only [show (1 : Nat) < 2 by decide, ↓reduceIte] at hpc2
  have hP2' : P2 ⊢ ((sp + BitVec.ofNat 64 (2192 + 128 * 2)) ↦ₛ prf2) ∗ memRegion (sp + 4272#64) 512 ∗
      SpillSliceMem 40 (sp + 1552#64) t2 ∗
      PolyMem (sp + 12448#64 + BitVec.ofNat 64 (512 * 2)) (fun _ => 0#128) ∗
      (((sp + 2192#64) ↦ₛ prf0) ∗ ((sp + 2320#64) ↦ₛ prf1) ∗
        PolyMem (sp + 12448#64) (polyVecNat (rHatPoly16 prf0)) ∗
        PolyMem (sp + 12960#64) (polyVecNat (rHatPoly16 prf1)) ∗
        ((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 11440#64) 960 ∗
        ((sp + 12400#64) ↦ₛ coins) ∗ ((sp + 12432#64) ↦₈ 0#8) ∗
        memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
        memRegion (sp + 16208#64) 99 ∗ memRegion (sp + 16528#64) 128 ∗ stackAt sp 1136 ∗ Rest) := by
    refine Entails.trans hP2 ?_
    simp only [Nat.mul_one, ha_12960, ha_13472]
    sep_frame
  refine SepWP.weaken_pre hP2'
    (sepWP_seq_env hcl2 hro2
      (seg3_iter hb hbase s2 sp (idx := 2) (by decide) prf2 (shake256List_length 128 _)
        t2 ht2 (fun _ => 0#128) _ hpc2 hrun2 hsp2 hspA2 hcl2 hro2
        r0_2 r1_2 r2_2 r3_2 r5_2 r7_2 r9_2 r10_2
        r12_2 r13_2 r14_2 r15_2 r16_2 r17_2 r18_2 r19_2 r20_2 r21_2 rv3_2) ?_)
  rintro sf Pf hpcf hrunf hclf hrof
    ⟨hspf, hspAf, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r19_f, r20_f, r21_f, _, _, _, t3, _, hPf⟩
  simp only [Nat.lt_irrefl, ↓reduceIte] at hpcf
  have hsp640 : SpillSliceMem 40 (sp + 1552#64) t3 ⊢ memRegion (sp + 1552#64) 640 := by
    dsimp only [SpillSliceMem]
    simpa using vecRangeMem_entails_memRegion 40 (sp + 1552#64) (fun i => t3.get i)
  refine SepWP.done hpcf hrunf ⟨hspf, hspAf, r19_f, r20_f, r21_f, hclf, hrof, ?_⟩
  refine Entails.trans hPf ?_
  simp only [ha_13472]
  exact entails_sub hsp640 (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3

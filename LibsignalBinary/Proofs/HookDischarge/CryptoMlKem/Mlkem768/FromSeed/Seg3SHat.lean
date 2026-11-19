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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3Sym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHatPrf -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow

/-!
# `generate_keypair` (`B05`) — Segment 3a `sHat` (`+0x3480 .. +0x48cc`) (`Seg3SHat`)

Composes `Seg3SHatPrf` (`+0x3480 → +0x38f4`), upper 5-stage binomial `NTT` (`Seg3Sym`,
`+0x38f4 → +0x453c` with stack reload `[sp + 136]` at `+0x3a04` and pointer shift at `+0x3aa0`),
lower 2-stage `NTT` (`Seg3FwdLow`, `+0x453c → +0x4628`), and Barrett reduction (`Seg3Sym`,
`+0x4628 → +0x48cc`) across `idx = 0, 1, 2` to produce `sHat[0..2]` at `[sp + 8416, sp + 9952)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat

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
  neonPolyNttBinomial16 neonPolyNttBinomial16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepWP.of_memRegion_vecRangeMem Vec32 poly32Mem_entails_memRegion poly32Mem_ofFn
  polyVecNat vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure (
  barrett_lowerFwdNtt16_upperBinomial lowerFwdNtt16 lowerFwdNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr Spill40 SpillSliceMem SymEnv SymGprs SymSpill40 SymState SymVRegs evalSExpr evalSymGpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SrcOptMem SymSpatial SymStateMatches matches_setPC matches_writeGpr polyPtr
  symGprs_set_get symSpill40_eval_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  lowerNttBinomial5_16 lowerNttBinomial5_16_size poly_eq_barrett poly_eq_lowerNttBinomial5_src)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3Sym (
  SrcOptMem05 SymSpatial05 cfgSHatBar cfgSHatNtt noReloc_sHat_bar_a noReloc_sHat_bar_b
  noReloc_sHat_ntt_a noReloc_sHat_ntt_b noReloc_sHat_ntt_c run_sHat_bar_a run_sHat_bar_b
  run_sHat_ntt_a run_sHat_ntt_b run_sHat_ntt_c sHat_bar_ast_eq sHat_bar_noSpillVreg
  sHat_ntt_ast_eq sHat_ntt_noSpillVreg seg3SpillConsts sepWP_of_runSymRange05
  symSHatBarEnd symSHatBarEnd_gprs symSHatBarEnd_vreg3 symSHatBarInit symSHatBarMid
  symSHatBarMid_gpr5 symSHatNttA symSHatNttA' symSHatNttB symSHatNttB' symSHatNttB_gpr6
  symSHatNttB_gpr8 symSHatNttEnd symSHatNttEnd_gprs symSHatNttEnd_spill_const
  symSHatNttEnd_vreg3 symSHatNttInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure (
  shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow (
  offSFwd4 offSFwdEnd ro00Sym sHat_fwd_low_ok step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHatPrf (
  off3480 off35a4 off37c4 off38f4 sHat_cbd2_loop sHat_copy_and_zetas sHat_prf_calls)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05
  [0x3a04 → 0x3a08, 0x3aa0 → 0x3aa4, 0x4654 → 0x4658, 0x48c4 → 0x48cc]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkLib05 blkPC05 polyVecNat shake256List dup8x16

@[simp, arm64_norm, wp_norm] abbrev off3a04 : BitVec 64 := BitVec.ofNat 64 14852
@[simp, arm64_norm, wp_norm] abbrev off3a08 : BitVec 64 := BitVec.ofNat 64 14856
@[simp, arm64_norm, wp_norm] abbrev off3aa0 : BitVec 64 := BitVec.ofNat 64 15008
@[simp, arm64_norm, wp_norm] abbrev off3aa4 : BitVec 64 := BitVec.ofNat 64 15012
@[simp, arm64_norm, wp_norm] abbrev off4654 : BitVec 64 := BitVec.ofNat 64 18004
@[simp, arm64_norm, wp_norm] abbrev off4658 : BitVec 64 := BitVec.ofNat 64 18008
@[simp, arm64_norm, wp_norm] abbrev off48c4 : BitVec 64 := BitVec.ofNat 64 18628
@[simp, arm64_norm, wp_norm] abbrev off48c8 : BitVec 64 := BitVec.ofNat 64 18632
@[simp, arm64_norm, wp_norm] abbrev off48cc : BitVec 64 := BitVec.ofNat 64 18636

/-! ## 1. Pure `cbdNttPoly16` Soundness & Symbolic Environment Helpers -/

/-- `Poly16` result of `cbd2` followed by 7-stage binomial NEON `NTT` + Barrett reduction. -/
@[expose] def cbdNttPoly16 (prf : List (BitVec 8)) : Poly16 :=
  neonPolyNttBinomial16 (neonCbd2Poly16 prf)

theorem cbdNttPoly16_spec {prf : List (BitVec 8)} (hprf : prf.length = 128) :
    (polyNtt (samplePolyCbd2 prf)).size = 256 ∧
    PolyBounded16 1664 (cbdNttPoly16 prf) ∧
    PolyRepresents (cbdNttPoly16 prf) (polyNtt (samplePolyCbd2 prf)) := by
  unfold cbdNttPoly16
  obtain ⟨⟨hsz, hb2⟩, hr⟩ := neonCbd2Poly16_spec hprf
  have hb3 : PolyBounded16 3 (neonCbd2Poly16 prf) :=
    ⟨hsz, fun i hi => ⟨by have := (hb2 i hi).1; omega, by have := (hb2 i hi).2; omega⟩⟩
  exact neonPolyNttBinomial16_spec hb3 hr (by unfold samplePolyCbd2; simp)

private theorem barrett_lowerFwd_lowerBinomial5 (p0 : Poly16) :
    (lowerFwdNtt16 (lowerNttBinomial5_16 p0)).map neonBarrettReduce16 =
      neonPolyNttBinomial16 p0 :=
  barrett_lowerFwdNtt16_upperBinomial p0

private def mkSHatNttEnv (s : State) (polyAddr : BitVec 64) (t : Spill40)
    (fDst : Nat → BitVec 128) (cbd : Poly16) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := t
  poly0   := Vec32.ofFn fDst
  src0    := Vec32.ofFn (polyVecNat cbd)
  gpr0    := fun r =>
    if r = 6#5 then polyAddr
    else if r = 31#5 then s.readReg64 .x6
    else s.readReg64 (.gpr r)
  pstate0 := s.pstate

private def mkSHatBarEnv (s : State) (q : Poly16) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := Spill40.ofFn (fun _ => 0#128)
  poly0   := Vec32.ofFn (polyVecNat q)
  src0    := Vec32.zero
  gpr0    := fun r => s.readReg64 (.gpr r)
  pstate0 := s.pstate

private theorem matches_sHatNttInit {sp : BitVec 64} {s : State}
    (polyAddr : BitVec 64) (t : Spill40) (fDst : Nat → BitVec 128) (cbd : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16)
    (hx0 : s.readReg64 .x0 = 0xc0dd#64) (hx2 : s.readReg64 .x2 = 0xf301#64)
    (hx4 : s.readReg64 .x4 = 0x4ebf#64) (hx13 : s.readReg64 .x13 = 0xf9fa#64)
    (hx14 : s.readReg64 .x14 = 0x47fa#64) (hx15 : s.readReg64 .x15 = 0x019b#64)
    (hx16 : s.readReg64 .x16 = 0x229b#64) (hx17 : s.readReg64 .x17 = 0x6833#64)
    (hx18 : s.readReg64 .x18 = 0xf9dd#64) :
    SymStateMatches sp (mkSHatNttEnv s polyAddr t fDst cbd) symSHatNttInit s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 3 => simpa [symSHatNttInit, SymVRegs.get, evalSExpr] using hv3
    | 0 | 1 | 2 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 => exact hx0 | 2 => exact hx2 | 4 => exact hx4
    | 6 => simp [symSHatNttInit, SymGprs.get, evalSymGpr, mkSHatNttEnv]
    | 13 => exact hx13 | 14 => exact hx14 | 15 => exact hx15
    | 16 => exact hx16 | 17 => exact hx17 | 18 => exact hx18
    | 1 | 3 | 5 | 7 | 8 | 9 | 10 | 11 | 12 | 19 | 20 | 21
    | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symSHatNttInit, SymGprs.get, evalSymGpr, mkSHatNttEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem matches_sHatBarInit {sp : BitVec 64} {s : State} (q : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16)
    (hx0 : s.readReg64 .x0 = 0xc0dd#64) (hx2 : s.readReg64 .x2 = 0xf301#64)
    (hx4 : s.readReg64 .x4 = 0x4ebf#64) (hx13 : s.readReg64 .x13 = 0xf9fa#64)
    (hx14 : s.readReg64 .x14 = 0x47fa#64) (hx15 : s.readReg64 .x15 = 0x019b#64)
    (hx16 : s.readReg64 .x16 = 0x229b#64) (hx17 : s.readReg64 .x17 = 0x6833#64)
    (hx18 : s.readReg64 .x18 = 0xf9dd#64) :
    SymStateMatches sp (mkSHatBarEnv s q) symSHatBarInit s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 3 => simpa [symSHatBarInit, symSHatNttInit, SymVRegs.get, evalSExpr] using hv3
    | 0 | 1 | 2 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 => exact hx0 | 2 => exact hx2 | 4 => exact hx4
    | 13 => exact hx13 | 14 => exact hx14 | 15 => exact hx15
    | 16 => exact hx16 | 17 => exact hx17 | 18 => exact hx18
    | 1 | 3 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 19 | 20 | 21
    | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symSHatBarInit, symSHatNttInit, SymGprs.get, SymGprs.set, evalSymGpr, mkSHatBarEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem evalSExpr_pstate0_irrel (env : SymEnv) (ps : PState) (e : SExpr) :
    evalSExpr { env with pstate0 := ps } e = evalSExpr env e := by
  induction e <;> simp [evalSExpr, *]

private theorem symVec32_eval_pstate0_irrel (env : SymEnv) (ps : PState)
    (t : Mlkem1024.Decaps.PolySymDefs.SymVec32) :
    t.eval { env with pstate0 := ps } = t.eval env := by
  have hf : (fun k => evalSExpr { env with pstate0 := ps } (t.get k)) =
      (fun k => evalSExpr env (t.get k)) := by
    funext k; exact evalSExpr_pstate0_irrel env ps (t.get k)
  dsimp only [Mlkem1024.Decaps.PolySymDefs.SymVec32.eval]
  rw [hf]

private theorem spillSlice40_sHatNttInit (sp : BitVec 64) {t : Spill40}
    (ht : ∀ env i, i < 24 → t.get i = evalSExpr env (seg3SpillConsts.get i))
    (env : SymEnv) (hsp0 : env.spill0 = t) :
    SpillSliceMem 40 (sp + 1568#64) (symSHatNttInit.spill.eval env) =
      SpillSliceMem 40 (sp + 1568#64) t :=
  vecRangeMem_congr fun i hi => by
    rw [symSpill40_eval_get env symSHatNttInit.spill i hi]
    dsimp only [symSHatNttInit]
    by_cases h24 : i < 24
    · exact (ht env i h24).symm
    · match i with
      | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31
      | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 =>
        simp [seg3SpillConsts, SymSpill40.get, evalSExpr, hsp0]
      | _ + 40 => omega

private theorem spill_consts24_sHatNttEnd (env0 env : SymEnv) (i : Nat) (hi : i < 24) :
    (symSHatNttEnd.spill.eval env0).get i = evalSExpr env (seg3SpillConsts.get i) := by
  rw [symSpill40_eval_get env0 symSHatNttEnd.spill i (by omega), symSHatNttEnd_spill_const i hi]
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11
  | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 => rfl
  | _ + 24 => omega

/-! ## 2. Glue Lemmas (`+0x3a04`, `+0x3aa0`, `+0x4654`, `+0x48c4`) -/

private theorem sHat_ldr_x8_136 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + off3a04) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off3a08) s
      (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.pstate = s.pstate ∧ sf.vregs = s.vregs ∧
        sf.readReg64 .x8 = sp + 8416#64 ∧
        (∀ r : BitVec 5, r ≠ 8#5 → r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk, rfl, rfl,
      by simp, fun r hr8 hr31 => ?_, rfl⟩
  rcases r with ⟨rv, hrv⟩
  match rv with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
  | 8 => exact absurd rfl hr8
  | 31 => exact absurd rfl hr31
  | _ + 32 => omega

private theorem sHat_add_x6_x8 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (_hidx : idx < 3) (P : SepProp)
    (hpc : s.pc = b + off3aa0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = sp + 8416#64)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 idx) :
    let polyAddr := sp + 8416#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off3aa4) s P
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.pstate = s.pstate ∧ sf.vregs = s.vregs ∧
        sf.readReg64 .x6 = polyAddr ∧
        (∀ r : BitVec 5, r ≠ 6#5 → r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = P) := by
  dsimp only; subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk, rfl, rfl,
      by simp only [State.readReg64_setPC];
         change sp + 8416#64 + BitVec.ofNat 64 idx <<< 9 = sp + 8416#64 + BitVec.ofNat 64 (512 * idx);
         clear * -; bv_omega,
      fun r hr6 hr31 => ?_, rfl⟩
  rcases r with ⟨rv, hrv⟩
  match rv with
  | 0 | 1 | 2 | 3 | 4 | 5 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
  | 6 => exact absurd rfl hr6
  | 31 => exact absurd rfl hr31
  | _ + 32 => omega

private theorem sHat_cmp3 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) {idx : Nat} (hidx : idx < 3) (P : SepProp)
    (hpc : s.pc = b + off4654) (hrun : s.status = .Running)
    (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 (idx + 1)) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off4658) s P
      (fun sf Pf =>
        sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ sf.vregs = s.vregs ∧
        (∀ r : BitVec 5, r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        sf.pstate.z = decide (idx = 2) ∧ Pf = P) := by
  subst hbase
  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 by omega) with rfl | rfl | rfl <;> {
    wp_step
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], by simp [State.setPC, State.setPState], fun r hr => ?_,
        by simp [subsPState64, AddWithCarry64], rfl⟩
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
    | 31 => exact absurd rfl hr
    | _ + 32 => omega
  }

private theorem sHat_loop_tail [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) {idx : Nat} (hidx : idx < 3) (P : SepProp)
    (hpc : s.pc = b + off48c4) (hrun : s.status = .Running)
    (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 (idx + 1))
    (hpz : s.pstate.z = decide (idx = 2)) :
    SepWP (blkPC05.rebase b (fun _ => none))
      (if idx < 2 then b + off37c4 else b + off48cc) s P
      (fun sf Pf =>
        sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ sf.vregs = s.vregs ∧
        sf.readReg64 .x6 = BitVec.ofNat 64 (idx + 1) ∧
        (∀ r : BitVec 5, r ≠ 6#5 → r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = P) := by
  subst hbase
  wp_step
  by_cases hlt : idx < 2
  · simp only [hlt, ↓reduceIte]
    have hne2 : idx ≠ 2 := by omega
    refine step_bCond_taken (dst := blkPl05.base + off37c4)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [ConditionHolds, hpz, hne2]) (by clear * -; dsimp [off48c8, off37c4]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], rfl, by simp, fun r hr6 hr31 => ?_, rfl⟩
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
    | 6 => exact absurd rfl hr6 | 31 => exact absurd rfl hr31 | _ + 32 => omega
  · simp only [hlt, ↓reduceIte]
    have heq2 : idx = 2 := by omega
    refine step_bCond_not_taken (dst := blkPl05.base + off48cc)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [ConditionHolds, hpz, heq2]) (by clear * -; dsimp [off48c8, off48cc]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], rfl, by simp, fun r hr6 hr31 => ?_, rfl⟩
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
    | 6 => exact absurd rfl hr6 | 31 => exact absurd rfl hr31 | _ + 32 => omega

private theorem matches_nttA_to_A' {sp : BitVec 64} {env : SymEnv} {s s' : State}
    (hm : SymStateMatches sp env symSHatNttA s)
    (hsp : s'.sp = sp) (hspA : s'.spAligned = true)
    (hpst : s'.pstate = s.pstate) (hvr : s'.vregs = s.vregs)
    (hx8 : s'.readReg64 .x8 = sp + 8416#64)
    (hgpr : ∀ r : BitVec 5, r ≠ 8#5 → r ≠ 31#5 → s'.readReg64 (.gpr r) = s.readReg64 (.gpr r)) :
    SymStateMatches sp env symSHatNttA' s' := by
  refine ⟨hsp, hspA, hpst.trans hm.hpstate, fun r => ?_, fun r hr => ?_⟩
  · rw [State.readVReg128, hvr]; exact hm.hvregs r
  · by_cases hr8 : r = 8#5
    · subst hr8; exact hx8
    · rw [hgpr r hr8 hr]
      have hlt : r.toNat < 31 := by
        have := r.isLt; have : r.toNat ≠ 31 := fun h => hr (BitVec.eq_of_toNat_eq h); omega
      have hne : r.toNat ≠ 8 := fun h => hr8 (BitVec.eq_of_toNat_eq h)
      rw [show symSHatNttA'.gprs.get r.toNat = symSHatNttA.gprs.get r.toNat by
        unfold symSHatNttA'
        rw [symGprs_set_get symSHatNttA.gprs 8 r.toNat (by decide) hlt]; simp [hne]]
      exact hm.hgprs r hr

private theorem matches_nttB_to_B' {sp polyAddr : BitVec 64} {env : SymEnv} {s s' : State}
    (hm : SymStateMatches sp env symSHatNttB s)
    (henv6 : env.gpr0 6#5 = polyAddr)
    (hsp : s'.sp = sp) (hspA : s'.spAligned = true)
    (hpst : s'.pstate = s.pstate) (hvr : s'.vregs = s.vregs)
    (hx6 : s'.readReg64 .x6 = polyAddr)
    (hgpr : ∀ r : BitVec 5, r ≠ 6#5 → r ≠ 31#5 → s'.readReg64 (.gpr r) = s.readReg64 (.gpr r)) :
    SymStateMatches sp env symSHatNttB' s' := by
  refine ⟨hsp, hspA, hpst.trans hm.hpstate, fun r => ?_, fun r hr => ?_⟩
  · rw [State.readVReg128, hvr]; exact hm.hvregs r
  · by_cases hr6 : r = 6#5
    · subst hr6
      simpa [symSHatNttB', SymGprs.get, SymGprs.set, evalSymGpr, henv6] using hx6
    · rw [hgpr r hr6 hr]
      have hlt : r.toNat < 31 := by
        have := r.isLt; have : r.toNat ≠ 31 := fun h => hr (BitVec.eq_of_toNat_eq h); omega
      have hne : r.toNat ≠ 6 := fun h => hr6 (BitVec.eq_of_toNat_eq h)
      rw [show symSHatNttB'.gprs.get r.toNat = symSHatNttB.gprs.get r.toNat by
        unfold symSHatNttB'
        rw [symGprs_set_get symSHatNttB.gprs 6 r.toNat (by decide) hlt]; simp [hne]]
      exact hm.hgprs r hr

/-! ## 3. Single-Iteration `sHat` Body (`+0x37c4 → +0x37c4 / +0x48cc`) -/

attribute [local irreducible] symSHatNttA symSHatNttB symSHatNttEnd symSHatBarMid symSHatBarEnd

private theorem sym_gpr_at {sp : BitVec 64} {env : SymEnv} {st : SymState} {s : State}
    (hm : SymStateMatches sp env st s) (k : Nat) (hk : k < 31) :
    s.readReg64 (.gpr (BitVec.ofNat 5 k)) = evalSymGpr sp env.gpr0 (st.gprs.get k) := by
  have hne : BitVec.ofNat 5 k ≠ 31#5 := by
    intro h; have := congrArg BitVec.toNat h
    have h31 : (31#5 : BitVec 5).toNat = 31 := rfl
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), h31] at this; omega
  have h := hm.hgprs (BitVec.ofNat 5 k) hne
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1200000 in
private theorem sHat_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3)
    (prf : List (BitVec 8)) (hprf : prf.length = 128)
    (t : Spill40) (ht : ∀ env i, i < 24 → t.get i = evalSExpr env (seg3SpillConsts.get i))
    (fDst : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off37c4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx0 : s.readReg64 .x0 = 0xc0dd#64)
    (hx1 : s.readReg64 .x1 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx2 : s.readReg64 .x2 = 0xf301#64)
    (hx3 : s.readReg64 .x3 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx4 : s.readReg64 .x4 = 0x4ebf#64)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 idx)
    (hx9 : s.readReg64 .x9 = 6224#64 + BitVec.ofNat 64 (512 * idx))
    (hx10 : s.readReg64 .x10 = sp + 2208#64)
    (hx11 : s.readReg64 .x11 = sp + 8432#64 + BitVec.ofNat 64 (512 * idx))
    (hx13 : s.readReg64 .x13 = 0xf9fa#64) (hx14 : s.readReg64 .x14 = 0x47fa#64)
    (hx15 : s.readReg64 .x15 = 0x019b#64) (hx16 : s.readReg64 .x16 = 0x229b#64)
    (hx17 : s.readReg64 .x17 = 0x6833#64) (hx18 : s.readReg64 .x18 = 0xf9dd#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 17376#64)
    (hx21 : s.readReg64 .x21 = sp + 9985#64 + BitVec.ofNat 64 (128 * idx))
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16) :
    let prfPtr := sp + BitVec.ofNat 64 (9984 + 128 * idx)
    let polyAddr := sp + 8416#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC05.rebase b (fun _ => none))
      (if idx < 2 then b + off37c4 else b + off48cc) s
      (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ (prfPtr ↦ₛ prf) ∗
        memRegion (sp + 17376#64) 512 ∗
        SpillSliceMem 40 (sp + 1568#64) t ∗ PolyMem polyAddr fDst ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x0 = 0xc0dd#64 ∧ sf.readReg64 .x1 = mlkemMpl.ρ ro00Sym + 66#64 ∧
        sf.readReg64 .x2 = 0xf301#64 ∧ sf.readReg64 .x3 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        sf.readReg64 .x4 = 0x4ebf#64 ∧ sf.readReg64 .x6 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x9 = 6224#64 + BitVec.ofNat 64 (512 * (idx + 1)) ∧
        sf.readReg64 .x10 = sp + 2208#64 ∧
        sf.readReg64 .x11 = sp + 8432#64 + BitVec.ofNat 64 (512 * (idx + 1)) ∧
        sf.readReg64 .x13 = 0xf9fa#64 ∧ sf.readReg64 .x14 = 0x47fa#64 ∧
        sf.readReg64 .x15 = 0x019b#64 ∧ sf.readReg64 .x16 = 0x229b#64 ∧
        sf.readReg64 .x17 = 0x6833#64 ∧ sf.readReg64 .x18 = 0xf9dd#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = sp + 17376#64 ∧
        sf.readReg64 .x21 = sp + 9985#64 + BitVec.ofNat 64 (128 * (idx + 1)) ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        ∃ t' : Spill40, (∀ env i, i < 24 → t'.get i = evalSExpr env (seg3SpillConsts.get i)) ∧
          (Pf ⊢ ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ (prfPtr ↦ₛ prf) ∗
            memRegion (sp + 17376#64) 512 ∗
            SpillSliceMem 40 (sp + 1568#64) t' ∗
            PolyMem polyAddr (polyVecNat (cbdNttPoly16 prf)) ∗ Rest)) := by
  dsimp only
  set prfPtr := sp + BitVec.ofNat 64 (9984 + 128 * idx)
  set polyAddr := sp + 8416#64 + BitVec.ofNat 64 (512 * idx)
  set cbd := neonCbd2Poly16 prf
  have hcbd : cbd.size = 256 := (neonCbd2Poly16_spec hprf).1.1
  have hx21' : s.readReg64 .x21 = prfPtr + 1#64 := by
    rw [hx21]; dsimp only [prfPtr]; clear * -; bv_omega
  refine SepWP.weaken_pre
    (show ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ (prfPtr ↦ₛ prf) ∗ memRegion (sp + 17376#64) 512 ∗
        SpillSliceMem 40 (sp + 1568#64) t ∗ PolyMem polyAddr fDst ∗ Rest ⊢
      (prfPtr ↦ₛ prf) ∗ memRegion (sp + 17376#64) 512 ∗
        (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ SpillSliceMem 40 (sp + 1568#64) t ∗
          PolyMem polyAddr fDst ∗ Rest) by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (sHat_cbd2_loop hb hbase s sp prfPtr prf
      (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ SpillSliceMem 40 (sp + 1568#64) t ∗
        PolyMem polyAddr fDst ∗ Rest)
      hprf hpc hrun hsp hspA hx19 hx20 hx21') ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, r0, r1, r2, r3, r4, r5, r6, r9, r10, r11, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, rfp, rv3, rfl⟩
  have hx5_1 : s1.readReg64 .x5 = BitVec.ofNat 64 (idx + 1) := by
    rw [r5, hx6]; clear * -; bv_omega
  have hx6_1 : s1.readReg64 .x6 = BitVec.ofNat 64 idx := r6.trans hx6
  set envN := mkSHatNttEnv s1 polyAddr t fDst cbd
  set F_ntt := ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ (prfPtr ↦ₛ prf) ∗ Rest
  have henv6 : envN.gpr0 6#5 = polyAddr := by simp [envN, mkSHatNttEnv]
  have hP1_sym : (prfPtr ↦ₛ prf) ∗ PolyMem (sp + 17376#64) (polyVecNat cbd) ∗
      (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ SpillSliceMem 40 (sp + 1568#64) t ∗
        PolyMem polyAddr fDst ∗ Rest) ⊢
      SymSpatial05 (some 17376) cfgSHatNtt sp envN symSHatNttInit F_ntt := by
    have hptr : polyPtr cfgSHatNtt sp envN = polyAddr := henv6
    dsimp only [SymSpatial05, SymSpatial, SrcOptMem, F_ntt]
    rw [hptr,
        show cfgSHatNtt.spillLen = 40 from rfl, show cfgSHatNtt.spillOff = 1568 from rfl,
        spillSlice40_sHatNttInit sp ht envN rfl,
        ← poly32Mem_ofFn polyAddr fDst,
        show SrcOptMem05 (some 17376) sp envN.src0 = PolyMem (sp + 17376#64) (polyVecNat cbd) from by
          dsimp only [SrcOptMem05, envN, mkSHatNttEnv]
          exact poly32Mem_ofFn (sp + 17376#64) (polyVecNat cbd)]
    dsimp only [cfgSHatNtt]; simp only [Bool.false_eq_true, ↓reduceIte]
    change (prfPtr ↦ₛ prf) ∗ PolyMem (sp + 17376#64) (polyVecNat cbd) ∗
        (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ SpillSliceMem 40 (sp + 1568#64) t ∗
          PolyMem polyAddr fDst ∗ Rest) ⊢
      SpillSliceMem 40 (sp + 1568#64) t ∗ PolyMem polyAddr fDst ∗ emp ∗
        (PolyMem (sp + 17376#64) (polyVecNat cbd) ∗
          (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ (prfPtr ↦ₛ prf) ∗ Rest))
    sep_frame
  refine SepWP.weaken_pre hP1_sym
    (sepWP_seq_env hcl1 hro1
      (sepWP_of_runSymRange05 (srcBase := some 17376) (cfg := cfgSHatNtt) (env := envN) (F := F_ntt)
        68 3645 noReloc_sHat_ntt_a (by decide) (by decide) (by decide)
        run_sHat_ntt_a
        (matches_sHatNttInit polyAddr t fDst cbd hsp1 hspA1 (rv3.trans hv3)
          (r0.trans hx0) (r2.trans hx2) (r4.trans hx4) (r13.trans hx13) (r14.trans hx14)
          (r15.trans hx15) (r16.trans hx16) (r17.trans hx17) (r18.trans hx18))
        hpc1 hrun1
        (post := fun s2a P2a => SymStateMatches sp envN symSHatNttA s2a ∧
          P2a = SymSpatial05 (some 17376) cfgSHatNtt sp envN symSHatNttA F_ntt)
        (fun s2a _ _ hm2a => ⟨hm2a, rfl⟩)) ?_)
  rintro s2a P2a hpc2a hrun2a hcl2a hro2a ⟨hm2a, rfl⟩
  have hP2a_ldr : SymSpatial05 (some 17376) cfgSHatNtt sp envN symSHatNttA F_ntt ⊢
      ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
        (SpillSliceMem 40 (sp + 1568#64) (symSHatNttA.spill.eval envN) ∗
          Poly32Mem (polyPtr cfgSHatNtt sp envN) (symSHatNttA.poly.eval envN) ∗
          SrcOptMem05 (some 17376) sp envN.src0 ∗ ((prfPtr ↦ₛ prf) ∗ Rest)) := by
    dsimp only [SymSpatial05, SymSpatial, cfgSHatNtt, SrcOptMem, F_ntt]
    change SpillSliceMem 40 (sp + 1568#64) _ ∗ Poly32Mem _ _ ∗ emp ∗
        (SrcOptMem05 (some 17376) sp envN.src0 ∗
          (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ (prfPtr ↦ₛ prf) ∗ Rest)) ⊢ _
    sep_frame
  refine SepWP.weaken_pre hP2a_ldr
    (sepWP_seq_env hcl2a hro2a
      (sHat_ldr_x8_136 hb hbase s2a sp _ hpc2a hrun2a hm2a.hsp hm2a.hsp_al) ?_)
  rintro s2b P2b hpc2b hrun2b hcl2b hro2b
    ⟨hsp2b, hspA2b, hpst2b, hvr2b, hx8_2b, hgpr2b, rfl⟩
  have hm2b : SymStateMatches sp envN symSHatNttA' s2b :=
    matches_nttA_to_A' hm2a hsp2b hspA2b hpst2b hvr2b hx8_2b hgpr2b
  have hP2b_sym : ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
      (SpillSliceMem 40 (sp + 1568#64) (symSHatNttA.spill.eval envN) ∗
        Poly32Mem (polyPtr cfgSHatNtt sp envN) (symSHatNttA.poly.eval envN) ∗
        SrcOptMem05 (some 17376) sp envN.src0 ∗ ((prfPtr ↦ₛ prf) ∗ Rest)) ⊢
      SymSpatial05 (some 17376) cfgSHatNtt sp envN symSHatNttA' F_ntt := by
    dsimp only [SymSpatial05, SymSpatial, cfgSHatNtt, SrcOptMem, symSHatNttA', F_ntt]
    change ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
        (SpillSliceMem 40 (sp + 1568#64) _ ∗ Poly32Mem _ _ ∗
          SrcOptMem05 (some 17376) sp envN.src0 ∗ ((prfPtr ↦ₛ prf) ∗ Rest)) ⊢
      SpillSliceMem 40 (sp + 1568#64) _ ∗ Poly32Mem _ _ ∗ emp ∗
        (SrcOptMem05 (some 17376) sp envN.src0 ∗
          (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ (prfPtr ↦ₛ prf) ∗ Rest))
    sep_frame
  refine SepWP.weaken_pre hP2b_sym
    (sepWP_seq_env hcl2b hro2b
      (sepWP_of_runSymRange05 (srcBase := some 17376) (cfg := cfgSHatNtt) (env := envN) (F := F_ntt)
        38 3714 noReloc_sHat_ntt_b (by decide) (by decide) (by decide)
        run_sHat_ntt_b hm2b hpc2b hrun2b
        (post := fun s2c P2c => SymStateMatches sp envN symSHatNttB s2c ∧
          P2c = SymSpatial05 (some 17376) cfgSHatNtt sp envN symSHatNttB F_ntt)
        (fun s2c _ _ hm2c => ⟨hm2c, rfl⟩)) ?_)
  rintro s2c P2c hpc2c hrun2c hcl2c hro2c ⟨hm2c, rfl⟩
  have hx8_2c : s2c.readReg64 .x8 = sp + 8416#64 := by
    have h := sym_gpr_at hm2c 8 (by decide); rw [symSHatNttB_gpr8] at h; exact h
  have hx6_2c : s2c.readReg64 .x6 = BitVec.ofNat 64 idx := by
    have h := sym_gpr_at hm2c 6 (by decide); rw [symSHatNttB_gpr6] at h
    rw [show s2c.readReg64 .x6 = s2c.readReg64 (.gpr 6#5) from rfl, h]
    simpa [evalSymGpr, envN, mkSHatNttEnv] using hx6_1
  refine sepWP_seq_env hcl2c hro2c
    (sHat_add_x6_x8 hb hbase s2c sp hidx _ hpc2c hrun2c hm2c.hsp hm2c.hsp_al hx8_2c hx6_2c) ?_
  rintro s2d P2d hpc2d hrun2d hcl2d hro2d
    ⟨hsp2d, hspA2d, hpst2d, hvr2d, hx6_2d, hgpr2d, rfl⟩
  have hm2d : SymStateMatches sp envN symSHatNttB' s2d :=
    matches_nttB_to_B' hm2c henv6 hsp2d hspA2d hpst2d hvr2d hx6_2d hgpr2d
  have hP2d_sym : SymSpatial05 (some 17376) cfgSHatNtt sp envN symSHatNttB F_ntt ⊢
      SymSpatial05 (some 17376) cfgSHatNtt sp envN symSHatNttB' F_ntt := by
    dsimp only [SymSpatial05, SymSpatial, symSHatNttB']
    exact Entails.refl _
  refine SepWP.weaken_pre hP2d_sym
    (sepWP_seq_env hcl2d hro2d
      (sepWP_of_runSymRange05 (srcBase := some 17376) (cfg := cfgSHatNtt) (env := envN) (F := F_ntt)
        678 3753 noReloc_sHat_ntt_c (by decide) (by decide) (by decide)
        run_sHat_ntt_c hm2d hpc2d hrun2d
        (post := fun s3 P3 => SymStateMatches sp envN symSHatNttEnd s3 ∧
          P3 = SymSpatial05 (some 17376) cfgSHatNtt sp envN symSHatNttEnd F_ntt)
        (fun s3 _ _ hm3 => ⟨hm3, rfl⟩)) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hm3, rfl⟩
  rcases symSHatNttEnd_gprs with ⟨ng0, ng1, ng2, ng3, ng4, ng5, ng6, ng7, ng8, ng9, ng10, ng11,
    ng13, ng14, ng15, ng16, ng17, ng18, ng19, ng20, ng21, ng22, ng29, _⟩
  have gpr3_eq : ∀ (k : Nat) (hk : k < 31),
      s3.readReg64 (.gpr (BitVec.ofNat 5 k)) = evalSymGpr sp envN.gpr0 (symSHatNttEnd.gprs.get k) :=
    fun k hk => sym_gpr_at hm3 k hk
  have hx0_3 : s3.readReg64 .x0 = 0xc0dd#64 := by
    have h := gpr3_eq 0 (by decide); rw [ng0] at h; exact h
  have hx1_3 : s3.readReg64 .x1 = mlkemMpl.ρ ro00Sym + 66#64 := by
    have h := gpr3_eq 1 (by decide); rw [ng1] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans (r1.trans hx1)
  have hx2_3 : s3.readReg64 .x2 = 0xf301#64 := by
    have h := gpr3_eq 2 (by decide); rw [ng2] at h; exact h
  have hx3_3 : s3.readReg64 .x3 = mlkemMpl.ρ ro00Sym + 134#64 := by
    have h := gpr3_eq 3 (by decide); rw [ng3] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans (r3.trans hx3)
  have hx4_3 : s3.readReg64 .x4 = 0x4ebf#64 := by
    have h := gpr3_eq 4 (by decide); rw [ng4] at h; exact h
  have hx5_3 : s3.readReg64 .x5 = BitVec.ofNat 64 (idx + 1) := by
    have h := gpr3_eq 5 (by decide); rw [ng5] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans hx5_1
  have hx6_3 : s3.readReg64 .x6 = polyAddr := by
    have h := gpr3_eq 6 (by decide); rw [ng6] at h
    simpa [evalSymGpr, envN, mkSHatNttEnv] using h
  have hx11_1 : s1.readReg64 .x11 = polyAddr + 16#64 := by
    rw [r11, hx11]; dsimp only [polyAddr]; clear * -; bv_omega
  have hx7_3 : s3.readReg64 .x7 = polyAddr + 16#64 := by
    have h := gpr3_eq 7 (by decide); rw [ng7] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans hx11_1
  have hx8_3 : s3.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64 := by
    have h := gpr3_eq 8 (by decide); rw [ng8] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans (r1.trans hx1)
  have hx9_3 : s3.readReg64 .x9 = 6224#64 + BitVec.ofNat 64 (512 * idx) := by
    have h := gpr3_eq 9 (by decide); rw [ng9] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans (r9.trans hx9)
  have hx10_3 : s3.readReg64 .x10 = sp + 2208#64 := by
    have h := gpr3_eq 10 (by decide); rw [ng10] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans (r10.trans hx10)
  have hx11_3 : s3.readReg64 .x11 = sp + 8432#64 + BitVec.ofNat 64 (512 * idx) := by
    have h := gpr3_eq 11 (by decide); rw [ng11] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans (r11.trans hx11)
  have hx13_3 : s3.readReg64 .x13 = 0xf9fa#64 := by
    have h := gpr3_eq 13 (by decide); rw [ng13] at h; exact h
  have hx14_3 : s3.readReg64 .x14 = 0x47fa#64 := by
    have h := gpr3_eq 14 (by decide); rw [ng14] at h; exact h
  have hx15_3 : s3.readReg64 .x15 = 0x019b#64 := by
    have h := gpr3_eq 15 (by decide); rw [ng15] at h; exact h
  have hx16_3 : s3.readReg64 .x16 = 0x229b#64 := by
    have h := gpr3_eq 16 (by decide); rw [ng16] at h; exact h
  have hx17_3 : s3.readReg64 .x17 = 0x6833#64 := by
    have h := gpr3_eq 17 (by decide); rw [ng17] at h; exact h
  have hx18_3 : s3.readReg64 .x18 = 0xf9dd#64 := by
    have h := gpr3_eq 18 (by decide); rw [ng18] at h; exact h
  have hx19_3 : s3.readReg64 .x19 = 0x55555555#64 := by
    have h := gpr3_eq 19 (by decide); rw [ng19] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans r19
  have hx20_3 : s3.readReg64 .x20 = sp + 17376#64 := by
    have h := gpr3_eq 20 (by decide); rw [ng20] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans r20
  have hx21_3 : s3.readReg64 .x21 = prfPtr + 1#64 := by
    have h := gpr3_eq 21 (by decide); rw [ng21] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans r21
  have hx22_3 : s3.readReg64 .x22 = 16#64 := by
    have h := gpr3_eq 22 (by decide); rw [ng22] at h; exact h
  have hfp_3 : s3.readReg64 .fp = sp + 29984#64 := by
    have h := gpr3_eq 29 (by decide); rw [ng29] at h
    simp only [evalSymGpr, envN, mkSHatNttEnv, BitVec.add_zero] at h; exact h.trans (rfp.trans hfp)
  have hv3_3 : s3.readVReg128 3#5 = dup8x16 3329#16 := by
    have h := hm3.hvregs 3#5; rw [show (3#5 : BitVec 5).toNat = 3 from rfl, symSHatNttEnd_vreg3] at h
    exact h
  set t1 := symSHatNttEnd.spill.eval envN
  have ht1 : ∀ env i, i < 24 → t1.get i = evalSExpr env (seg3SpillConsts.get i) :=
    fun env i hi => spill_consts24_sHatNttEnd envN env i hi
  set p3 := lowerNttBinomial5_16 cbd
  have hp3 : p3.size = 256 := (lowerNttBinomial5_16_size cbd).trans hcbd
  have hp3_mem : Poly32Mem (polyPtr cfgSHatNtt sp envN) (symSHatNttEnd.poly.eval envN) =
      PolyMem polyAddr (polyVecNat p3) := by
    have hptr : polyPtr cfgSHatNtt sp envN = polyAddr := henv6
    rw [hptr]
    exact poly_eq_lowerNttBinomial5_src polyAddr hcbd envN rfl symSHatNttEnd.poly
      sHat_ntt_noSpillVreg sHat_ntt_ast_eq
  have hsrc3 : SrcOptMem05 (some 17376) sp envN.src0 ⊢ memRegion (sp + 17376#64) 512 := by
    dsimp only [SrcOptMem05]
    exact poly32Mem_entails_memRegion (sp + 17376#64) envN.src0
  set F_low := memRegion (sp + 17376#64) 512 ∗ SpillSliceMem 40 (sp + 1568#64) t1 ∗ F_ntt
  have hP3_low : SymSpatial05 (some 17376) cfgSHatNtt sp envN symSHatNttEnd F_ntt ⊢
      PolyMem polyAddr (polyVecNat p3) ∗ F_low := by
    dsimp only [SymSpatial05, SymSpatial, SrcOptMem, F_low, t1]
    rw [hp3_mem]
    dsimp only [cfgSHatNtt]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact entails_sub hsrc3 (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP3_low
    (sepWP_seq_env hcl3 hro3
      (sHat_fwd_low_ok hb s3 sp polyAddr hp3 F_low
        hpc3 hrun3 hm3.hsp hm3.hsp_al hcl3 hro3 hx8_3 hx3_3 hx7_3 hx22_3 hx2_3
        (by rw [hx10_3, hx9_3]; dsimp only [polyAddr]; clear * -; bv_omega) hv3_3) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hpres4, _, _, rfl⟩
  set q := lowerFwdNtt16 p3
  have hq : q.size = 256 := (lowerFwdNtt16_size p3).trans hp3
  set envB := mkSHatBarEnv s4 q
  have hP4_bar : PolyMem polyAddr (polyVecNat q) ∗ F_low ⊢
      SymSpatial05 none cfgSHatBar sp envB symSHatBarInit F_low := by
    dsimp only [SymSpatial05, SymSpatial, cfgSHatBar, polyPtr, SrcOptMem, SrcOptMem05,
      SpillSliceMem, Encaps2.VecMem.VecRangeMem, envB, mkSHatBarEnv]
    rw [show s4.readReg64 (.gpr 6#5) = polyAddr from hpres4.x6.trans hx6_3,
        ← poly32Mem_ofFn polyAddr (polyVecNat q)]
    change Poly32Mem polyAddr _ ∗ F_low ⊢ emp ∗ Poly32Mem polyAddr _ ∗ emp ∗ (emp ∗ F_low)
    sep_frame
  refine SepWP.weaken_pre hP4_bar
    (sepWP_seq_env hcl4 hro4
      (sepWP_of_runSymRange05 (srcBase := none) (cfg := cfgSHatBar) (env := envB) (F := F_low)
        11 4490 noReloc_sHat_bar_a (by decide) (by decide) (by decide)
        run_sHat_bar_a
        (matches_sHatBarInit q hsp4 hspA4 (hpres4.v3.trans hv3_3)
          (hpres4.x0.trans hx0_3) (hpres4.x2.trans hx2_3) (hpres4.x4.trans hx4_3)
          (hpres4.x13.trans hx13_3) (hpres4.x14.trans hx14_3) (hpres4.x15.trans hx15_3)
          (hpres4.x16.trans hx16_3) (hpres4.x17.trans hx17_3) (hpres4.x18.trans hx18_3))
        hpc4 hrun4
        (post := fun s5 P5 => SymStateMatches sp envB symSHatBarMid s5 ∧
          P5 = SymSpatial05 none cfgSHatBar sp envB symSHatBarMid F_low)
        (fun s5 _ _ hm5 => ⟨hm5, rfl⟩)) ?_)
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hm5, rfl⟩
  have hx5_5 : s5.readReg64 .x5 = BitVec.ofNat 64 (idx + 1) := by
    have h := sym_gpr_at hm5 5 (by decide); rw [symSHatBarMid_gpr5] at h
    simp only [evalSymGpr, envB, mkSHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x5.trans hx5_3)
  refine sepWP_seq_env hcl5 hro5
    (sHat_cmp3 hb hbase s5 hidx _ hpc5 hrun5 hx5_5) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 hro6 ⟨hsp6, hspA6, hvregs6, hgpr6, hpz6, rfl⟩
  set envB' : SymEnv := { envB with pstate0 := s6.pstate }
  have hm6 : SymStateMatches sp envB' symSHatBarMid s6 := by
    refine ⟨hsp6.trans hm5.hsp, hspA6.trans hm5.hsp_al, rfl, fun r => ?_, fun r hr => ?_⟩
    · rw [State.readVReg128, hvregs6]
      exact (hm5.hvregs r).trans (evalSExpr_pstate0_irrel envB s6.pstate _).symm
    · exact (hgpr6 r hr).trans (hm5.hgprs r hr)
  have hP6_bar : SymSpatial05 none cfgSHatBar sp envB symSHatBarMid F_low ⊢
      SymSpatial05 none cfgSHatBar sp envB' symSHatBarMid F_low := by
    dsimp only [SymSpatial05, SymSpatial, cfgSHatBar, polyPtr, SrcOptMem, SrcOptMem05,
      SpillSliceMem, Encaps2.VecMem.VecRangeMem, envB']
    rw [symVec32_eval_pstate0_irrel envB s6.pstate symSHatBarMid.poly]
    exact Entails.refl _
  refine SepWP.weaken_pre hP6_bar
    (sepWP_seq_env hcl6 hro6
      (sepWP_of_runSymRange05 (srcBase := none) (cfg := cfgSHatBar) (env := envB') (F := F_low)
        155 4502 noReloc_sHat_bar_b (by decide) (by decide) (by decide)
        run_sHat_bar_b hm6 hpc6 hrun6
        (post := fun s7 P7 => SymStateMatches sp envB' symSHatBarEnd s7 ∧
          P7 = SymSpatial05 none cfgSHatBar sp envB' symSHatBarEnd F_low)
        (fun s7 _ _ hm7 => ⟨hm7, rfl⟩)) ?_)
  rintro s7 P7 hpc7 hrun7 hcl7 hro7 ⟨hm7, rfl⟩
  rcases symSHatBarEnd_gprs with ⟨bg0, bg1, bg2, bg3, bg4, bg5, _, bg9, bg10, bg11,
    bg13, bg14, bg15, bg16, bg17, bg18, bg19, bg20, bg21, bg29, _⟩
  have gpr7_eq : ∀ (k : Nat) (hk : k < 31),
      s7.readReg64 (.gpr (BitVec.ofNat 5 k)) = evalSymGpr sp envB.gpr0 (symSHatBarEnd.gprs.get k) :=
    fun k hk => sym_gpr_at hm7 k hk
  have hx5_7 : s7.readReg64 .x5 = BitVec.ofNat 64 (idx + 1) := by
    have h := gpr7_eq 5 (by decide); rw [bg5] at h
    simp only [evalSymGpr, envB, mkSHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x5.trans hx5_3)
  have hpz7 : s7.pstate.z = decide (idx = 2) := hm7.hpstate ▸ hpz6
  have hp7_mem : Poly32Mem (polyPtr cfgSHatBar sp envB') (symSHatBarEnd.poly.eval envB') =
      PolyMem polyAddr (polyVecNat (cbdNttPoly16 prf)) := by
    have hptr : polyPtr cfgSHatBar sp envB' = polyAddr := hpres4.x6.trans hx6_3
    rw [hptr, poly_eq_barrett polyAddr hq envB' rfl symSHatBarEnd.poly
      sHat_bar_noSpillVreg sHat_bar_ast_eq, barrett_lowerFwd_lowerBinomial5 cbd]
    rfl
  have hP7 : SymSpatial05 none cfgSHatBar sp envB' symSHatBarEnd F_low ⊢
      ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ (prfPtr ↦ₛ prf) ∗
        memRegion (sp + 17376#64) 512 ∗
        SpillSliceMem 40 (sp + 1568#64) t1 ∗
        PolyMem polyAddr (polyVecNat (cbdNttPoly16 prf)) ∗ Rest := by
    dsimp only [SymSpatial05, SymSpatial, SrcOptMem, SrcOptMem05, F_low, F_ntt]
    rw [hp7_mem]
    dsimp only [cfgSHatBar, SpillSliceMem, Encaps2.VecMem.VecRangeMem]
    change emp ∗ PolyMem polyAddr (polyVecNat (cbdNttPoly16 prf)) ∗
        (if false = true then _ else emp) ∗
        (emp ∗ (memRegion (sp + 17376#64) 512 ∗
          Encaps2.VecMem.VecRangeMem 40 (sp + 1568#64) (fun i => t1.get i) ∗
          (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ (prfPtr ↦ₛ prf) ∗ Rest))) ⊢
      ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ (prfPtr ↦ₛ prf) ∗ memRegion (sp + 17376#64) 512 ∗
        Encaps2.VecMem.VecRangeMem 40 (sp + 1568#64) (fun i => t1.get i) ∗
        PolyMem polyAddr (polyVecNat (cbdNttPoly16 prf)) ∗ Rest
    simp only [Bool.false_eq_true, ↓reduceIte]; sep_frame
  refine SepWP.weaken_pre hP7
    (sepWP_seq_env hcl7 hro7 (sHat_loop_tail hb hbase s7 hidx _ hpc7 hrun7 hx5_7 hpz7) ?_)
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hvregsf, hx6f, hgprf, rfl⟩
  have hvf : ∀ r : BitVec 5, sf.readVReg128 r = s7.readVReg128 r :=
    fun r => by simp [State.readVReg128, hvregsf]
  have hfp_f : sf.readReg64 .fp = sp + 29984#64 := by
    rw [show sf.readReg64 .fp = sf.readReg64 (.gpr 29#5) from rfl, hgprf 29#5 (by decide) (by decide)]
    have h := gpr7_eq 29 (by decide); rw [bg29] at h
    simp only [evalSymGpr, envB, mkSHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.fp.trans hfp_3)
  have hx0_f : sf.readReg64 .x0 = 0xc0dd#64 := by
    rw [show sf.readReg64 .x0 = sf.readReg64 (.gpr 0#5) from rfl, hgprf 0#5 (by decide) (by decide)]
    have h := gpr7_eq 0 (by decide); rw [bg0] at h; exact h
  have hx1_f : sf.readReg64 .x1 = mlkemMpl.ρ ro00Sym + 66#64 := by
    rw [show sf.readReg64 .x1 = sf.readReg64 (.gpr 1#5) from rfl, hgprf 1#5 (by decide) (by decide)]
    have h := gpr7_eq 1 (by decide); rw [bg1] at h
    simp only [evalSymGpr, envB, mkSHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x1.trans hx1_3)
  have hx2_f : sf.readReg64 .x2 = 0xf301#64 := by
    rw [show sf.readReg64 .x2 = sf.readReg64 (.gpr 2#5) from rfl, hgprf 2#5 (by decide) (by decide)]
    have h := gpr7_eq 2 (by decide); rw [bg2] at h; exact h
  have hx3_f : sf.readReg64 .x3 = mlkemMpl.ρ ro00Sym + 134#64 := by
    rw [show sf.readReg64 .x3 = sf.readReg64 (.gpr 3#5) from rfl, hgprf 3#5 (by decide) (by decide)]
    have h := gpr7_eq 3 (by decide); rw [bg3] at h
    simp only [evalSymGpr, envB, mkSHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x3.trans hx3_3)
  have hx4_f : sf.readReg64 .x4 = 0x4ebf#64 := by
    rw [show sf.readReg64 .x4 = sf.readReg64 (.gpr 4#5) from rfl, hgprf 4#5 (by decide) (by decide)]
    have h := gpr7_eq 4 (by decide); rw [bg4] at h; exact h
  have hx9_f : sf.readReg64 .x9 = 6224#64 + BitVec.ofNat 64 (512 * (idx + 1)) := by
    rw [show sf.readReg64 .x9 = sf.readReg64 (.gpr 9#5) from rfl, hgprf 9#5 (by decide) (by decide)]
    have h := gpr7_eq 9 (by decide); rw [bg9] at h
    simp only [evalSymGpr, envB, mkSHatBarEnv] at h
    rw [h, show s4.readReg64 (.gpr 9#5) = s4.readReg64 .x9 from rfl, hpres4.x9, hx9_3]
    clear * - hidx; bv_omega
  have hx10_f : sf.readReg64 .x10 = sp + 2208#64 := by
    rw [show sf.readReg64 .x10 = sf.readReg64 (.gpr 10#5) from rfl, hgprf 10#5 (by decide) (by decide)]
    have h := gpr7_eq 10 (by decide); rw [bg10] at h
    simp only [evalSymGpr, envB, mkSHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x10.trans hx10_3)
  have hx11_f : sf.readReg64 .x11 = sp + 8432#64 + BitVec.ofNat 64 (512 * (idx + 1)) := by
    rw [show sf.readReg64 .x11 = sf.readReg64 (.gpr 11#5) from rfl, hgprf 11#5 (by decide) (by decide)]
    have h := gpr7_eq 11 (by decide); rw [bg11] at h
    simp only [evalSymGpr, envB, mkSHatBarEnv] at h
    rw [h, show s4.readReg64 (.gpr 11#5) = s4.readReg64 .x11 from rfl, hpres4.x11, hx11_3]
    clear * - hidx; bv_omega
  have hconst_f : sf.readReg64 .x13 = 0xf9fa#64 ∧ sf.readReg64 .x14 = 0x47fa#64 ∧
      sf.readReg64 .x15 = 0x019b#64 ∧ sf.readReg64 .x16 = 0x229b#64 ∧
      sf.readReg64 .x17 = 0x6833#64 ∧ sf.readReg64 .x18 = 0xf9dd#64 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show sf.readReg64 .x13 = sf.readReg64 (.gpr 13#5) from rfl, hgprf 13#5 (by decide) (by decide)]
      have h := gpr7_eq 13 (by decide); rw [bg13] at h; exact h
    · rw [show sf.readReg64 .x14 = sf.readReg64 (.gpr 14#5) from rfl, hgprf 14#5 (by decide) (by decide)]
      have h := gpr7_eq 14 (by decide); rw [bg14] at h; exact h
    · rw [show sf.readReg64 .x15 = sf.readReg64 (.gpr 15#5) from rfl, hgprf 15#5 (by decide) (by decide)]
      have h := gpr7_eq 15 (by decide); rw [bg15] at h; exact h
    · rw [show sf.readReg64 .x16 = sf.readReg64 (.gpr 16#5) from rfl, hgprf 16#5 (by decide) (by decide)]
      have h := gpr7_eq 16 (by decide); rw [bg16] at h; exact h
    · rw [show sf.readReg64 .x17 = sf.readReg64 (.gpr 17#5) from rfl, hgprf 17#5 (by decide) (by decide)]
      have h := gpr7_eq 17 (by decide); rw [bg17] at h; exact h
    · rw [show sf.readReg64 .x18 = sf.readReg64 (.gpr 18#5) from rfl, hgprf 18#5 (by decide) (by decide)]
      have h := gpr7_eq 18 (by decide); rw [bg18] at h; exact h
  rcases hconst_f with ⟨hx13_f, hx14_f, hx15_f, hx16_f, hx17_f, hx18_f⟩
  have hx19_f : sf.readReg64 .x19 = 0x55555555#64 := by
    rw [show sf.readReg64 .x19 = sf.readReg64 (.gpr 19#5) from rfl, hgprf 19#5 (by decide) (by decide)]
    have h := gpr7_eq 19 (by decide); rw [bg19] at h
    simp only [evalSymGpr, envB, mkSHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x19.trans hx19_3)
  have hx20_f : sf.readReg64 .x20 = sp + 17376#64 := by
    rw [show sf.readReg64 .x20 = sf.readReg64 (.gpr 20#5) from rfl, hgprf 20#5 (by decide) (by decide)]
    have h := gpr7_eq 20 (by decide); rw [bg20] at h
    simp only [evalSymGpr, envB, mkSHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x20.trans hx20_3)
  have hx21_f : sf.readReg64 .x21 = sp + 9985#64 + BitVec.ofNat 64 (128 * (idx + 1)) := by
    rw [show sf.readReg64 .x21 = sf.readReg64 (.gpr 21#5) from rfl, hgprf 21#5 (by decide) (by decide)]
    have h := gpr7_eq 21 (by decide); rw [bg21] at h
    simp only [evalSymGpr, envB, mkSHatBarEnv] at h
    rw [h, show s4.readReg64 (.gpr 21#5) = s4.readReg64 .x21 from rfl, hpres4.x21, hx21_3]
    dsimp only [prfPtr]; clear * - hidx; bv_omega
  have hv3_f : sf.readVReg128 3#5 = dup8x16 0x0d01#16 := by
    rw [hvf 3#5]
    have h := hm7.hvregs 3#5; rw [show (3#5 : BitVec 5).toNat = 3 from rfl, symSHatBarEnd_vreg3] at h
    exact h
  exact SepWP.done hpcf hrunf
    ⟨hspf.trans hm7.hsp, hspAf.trans hm7.hsp_al, hfp_f, hx0_f, hx1_f, hx2_f, hx3_f, hx4_f,
      hx6f, hx9_f, hx10_f, hx11_f, hx13_f, hx14_f, hx15_f, hx16_f, hx17_f, hx18_f,
      hx19_f, hx20_f, hx21_f, hv3_f, hclf, hrof, t1, ht1, Entails.refl _⟩


/-! ## 4. Full 3-Iteration `sHat` Loop & Segment 3a Composition (`+0x3480 → +0x48cc`) -/

/-- `sHat[0..2]` stored at `[sp + 8416, sp + 9952)` (`3 × 512` B). -/
@[expose] def SHatMem (sp : BitVec 64) (sigma : List (BitVec 8)) : SepProp :=
  PolyMem (sp + 8416#64) (polyVecNat (cbdNttPoly16 (shake256List 128 (sigma ++ [0#8])))) ∗
  PolyMem (sp + 8928#64) (polyVecNat (cbdNttPoly16 (shake256List 128 (sigma ++ [1#8])))) ∗
  PolyMem (sp + 9440#64) (polyVecNat (cbdNttPoly16 (shake256List 128 (sigma ++ [2#8]))))

private theorem sHat_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (sigma : List (BitVec 8))
    (t : Spill40) (ht : ∀ env i, i < 24 → t.get i = evalSExpr env (seg3SpillConsts.get i))
    (Rest : SepProp)
    (hpc : s.pc = b + off37c4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx0 : s.readReg64 .x0 = 0xc0dd#64) (hx1 : s.readReg64 .x1 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx2 : s.readReg64 .x2 = 0xf301#64) (hx3 : s.readReg64 .x3 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx4 : s.readReg64 .x4 = 0x4ebf#64) (hx6 : s.readReg64 .x6 = 0#64)
    (hx9 : s.readReg64 .x9 = 6224#64) (hx10 : s.readReg64 .x10 = sp + 2208#64)
    (hx11 : s.readReg64 .x11 = sp + 8432#64) (hx13 : s.readReg64 .x13 = 0xf9fa#64)
    (hx14 : s.readReg64 .x14 = 0x47fa#64) (hx15 : s.readReg64 .x15 = 0x019b#64)
    (hx16 : s.readReg64 .x16 = 0x229b#64) (hx17 : s.readReg64 .x17 = 0x6833#64)
    (hx18 : s.readReg64 .x18 = 0xf9dd#64) (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 17376#64) (hx21 : s.readReg64 .x21 = sp + 9985#64)
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16) :
    let prf0 := shake256List 128 (sigma ++ [0#8])
    let prf1 := shake256List 128 (sigma ++ [1#8])
    let prf2 := shake256List 128 (sigma ++ [2#8])
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off48cc) s
      (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
       ((sp + 9984#64) ↦ₛ prf0) ∗ ((sp + 10112#64) ↦ₛ prf1) ∗ ((sp + 10240#64) ↦ₛ prf2) ∗
       memRegion (sp + 8416#64) 1536 ∗ memRegion (sp + 17376#64) 512 ∗
       SpillSliceMem 40 (sp + 1568#64) t ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = sp + 17376#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        ∃ t' : Spill40, (∀ env i, i < 24 → t'.get i = evalSExpr env (seg3SpillConsts.get i)) ∧
          (Pf ⊢ ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ SHatMem sp sigma ∗
            memRegion (sp + 9984#64) 384 ∗ memRegion (sp + 17376#64) 512 ∗
            SpillSliceMem 40 (sp + 1568#64) t' ∗ Rest)) := by
  dsimp only
  set prf0 := shake256List 128 (sigma ++ [0#8])
  set prf1 := shake256List 128 (sigma ++ [1#8])
  set prf2 := shake256List 128 (sigma ++ [2#8])
  have hp0 : prf0.length = 128 := shake256List_length 128 _
  have hp1 : prf1.length = 128 := shake256List_length 128 _
  have hp2 : prf2.length = 128 := shake256List_length 128 _
  rw [memRegion_split' (b := sp + 8416#64) (b' := sp + 8928#64) (n := 512) (k := (1024 : Nat))
        rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 8928#64) (b' := sp + 9440#64) (n := 512) (k := (512 : Nat))
        rfl (by clear * -; bv_omega) (by decide)]
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 8416#64) (by decide) (by sep_focus); intro fd0
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 8928#64) (by decide) (by sep_focus); intro fd1
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 9440#64) (by decide) (by sep_focus); intro fd2
  change SepWP _ _ _ (PolyMem (sp + 9440#64) fd2 ∗
    (PolyMem (sp + 8928#64) fd1 ∗ (PolyMem (sp + 8416#64) fd0 ∗ _))) _
  -- idx = 0
  refine SepWP.weaken_pre
    (P' := ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ ((sp + BitVec.ofNat 64 (9984 + 128 * 0)) ↦ₛ prf0) ∗
      memRegion (sp + 17376#64) 512 ∗ SpillSliceMem 40 (sp + 1568#64) t ∗
      PolyMem (sp + 8416#64 + BitVec.ofNat 64 (512 * 0)) fd0 ∗
      (((sp + 10112#64) ↦ₛ prf1) ∗ ((sp + 10240#64) ↦ₛ prf2) ∗
        PolyMem (sp + 8928#64) fd1 ∗ PolyMem (sp + 9440#64) fd2 ∗ Rest))
    (by simp only [Nat.mul_zero, Nat.add_zero, BitVec.add_zero]; sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (sHat_iter hb hbase s sp (idx := 0) (by decide) prf0 hp0 t ht fd0 _
      hpc hrun hsp hspA hcl hro hfp hx0 hx1 hx2 hx3 hx4 hx6
      (by simpa using hx9) hx10 (by simpa using hx11)
      hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 (by simpa using hx21) hv3) ?_
  rintro s1 P1 hpc1 hrun1 _ _
    ⟨hsp1, hspA1, hfp1, r0_1, r1_1, r2_1, r3_1, r4_1, r6_1, r9_1, r10_1, r11_1,
     r13_1, r14_1, r15_1, r16_1, r17_1, r18_1, r19_1, r20_1, r21_1, rv3_1,
     hcl1, hro1, t1, ht1, hP1⟩
  simp only [show (0 : Nat) < 2 from by decide, ite_true] at hpc1
  refine SepWP.weaken_pre hP1 ?_
  -- idx = 1
  refine SepWP.weaken_pre
    (P' := ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ ((sp + BitVec.ofNat 64 (9984 + 128 * 1)) ↦ₛ prf1) ∗
      memRegion (sp + 17376#64) 512 ∗ SpillSliceMem 40 (sp + 1568#64) t1 ∗
      PolyMem (sp + 8416#64 + BitVec.ofNat 64 (512 * 1)) fd1 ∗
      (((sp + 9984#64) ↦ₛ prf0) ∗ ((sp + 10240#64) ↦ₛ prf2) ∗
        PolyMem (sp + 8416#64) (polyVecNat (cbdNttPoly16 prf0)) ∗
        PolyMem (sp + 9440#64) fd2 ∗ Rest))
    (by simp only [Nat.mul_zero, Nat.add_zero, BitVec.add_zero,
          show sp + 8416#64 + BitVec.ofNat 64 (512 * 1) = sp + 8928#64 by clear * -; bv_omega,
          show sp + BitVec.ofNat 64 (9984 + 128 * 1) = sp + 10112#64 from rfl]; sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (sHat_iter hb hbase s1 sp (idx := 1) (by decide) prf1 hp1 t1 ht1 fd1 _
      hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hfp1 r0_1 r1_1 r2_1 r3_1 r4_1 r6_1
      r9_1 r10_1 r11_1 r13_1 r14_1 r15_1 r16_1 r17_1 r18_1 r19_1 r20_1 r21_1 rv3_1) ?_
  rintro s2 P2 hpc2 hrun2 _ _
    ⟨hsp2, hspA2, hfp2, r0_2, r1_2, r2_2, r3_2, r4_2, r6_2, r9_2, r10_2, r11_2,
     r13_2, r14_2, r15_2, r16_2, r17_2, r18_2, r19_2, r20_2, r21_2, rv3_2,
     hcl2, hro2, t2, ht2, hP2⟩
  simp only [show (1 : Nat) < 2 from by decide, ite_true] at hpc2
  refine SepWP.weaken_pre hP2 ?_
  -- idx = 2
  refine SepWP.weaken_pre
    (P' := ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ ((sp + BitVec.ofNat 64 (9984 + 128 * 2)) ↦ₛ prf2) ∗
      memRegion (sp + 17376#64) 512 ∗ SpillSliceMem 40 (sp + 1568#64) t2 ∗
      PolyMem (sp + 8416#64 + BitVec.ofNat 64 (512 * 2)) fd2 ∗
      (((sp + 9984#64) ↦ₛ prf0) ∗ ((sp + 10112#64) ↦ₛ prf1) ∗
        PolyMem (sp + 8416#64) (polyVecNat (cbdNttPoly16 prf0)) ∗
        PolyMem (sp + 8928#64) (polyVecNat (cbdNttPoly16 prf1)) ∗ Rest))
    (by simp only [show sp + 8416#64 + BitVec.ofNat 64 (512 * 1) = sp + 8928#64 by clear * -; bv_omega,
          show sp + 8416#64 + BitVec.ofNat 64 (512 * 2) = sp + 9440#64 by clear * -; bv_omega,
          show sp + BitVec.ofNat 64 (9984 + 128 * 1) = sp + 10112#64 from rfl,
          show sp + BitVec.ofNat 64 (9984 + 128 * 2) = sp + 10240#64 from rfl]; sep_frame) ?_
  refine sepWP_seq_env hcl2 hro2
    (sHat_iter hb hbase s2 sp (idx := 2) (by decide) prf2 hp2 t2 ht2 fd2 _
      hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hfp2 r0_2 r1_2 r2_2 r3_2 r4_2 r6_2
      r9_2 r10_2 r11_2 r13_2 r14_2 r15_2 r16_2 r17_2 r18_2 r19_2 r20_2 r21_2 rv3_2) ?_
  rintro sf Pf hpcf hrunf _ _
    ⟨hspf, hspAf, hfpf, _, _, _, _, _, _, _, _, _,
     _, _, _, _, _, _, r19f, r20f, _, _, hclf, hrof, t3, ht3, hPf⟩
  simp only [show ¬ ((2 : Nat) < 2) from by decide, ite_false] at hpcf
  refine SepWP.done hpcf hrunf ⟨hspf, hspAf, hfpf, r19f, r20f, hclf, hrof, t3, ht3, ?_⟩
  refine Entails.trans hPf ?_
  have hm0 : ((sp + 9984#64) ↦ₛ prf0) ⊢ memRegion (sp + 9984#64) 128 := by
    simpa [hp0] using pointsToBytes_entails_memRegion (sp + 9984#64) prf0
  have hm1 : ((sp + 10112#64) ↦ₛ prf1) ⊢ memRegion (sp + 10112#64) 128 := by
    simpa [hp1] using pointsToBytes_entails_memRegion (sp + 10112#64) prf1
  have hm2 : ((sp + 10240#64) ↦ₛ prf2) ⊢ memRegion (sp + 10240#64) 128 := by
    simpa [hp2] using pointsToBytes_entails_memRegion (sp + 10240#64) prf2
  rw [memRegion_split' (b := sp + 9984#64) (b' := sp + 10112#64) (n := 128) (k := (256 : Nat))
        rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 10112#64) (b' := sp + 10240#64) (n := 128) (k := (128 : Nat))
        rfl (by clear * -; bv_omega) (by decide)]
  unfold SHatMem
  simp only [show sp + 8416#64 + BitVec.ofNat 64 (512 * 2) = sp + 9440#64 by clear * -; bv_omega,
    show sp + BitVec.ofNat 64 (9984 + 128 * 2) = sp + 10240#64 from rfl]
  exact entails_sub hm0 (by sep_frame)
    (entails_sub hm1 (by sep_frame) (entails_sub hm2 (by sep_frame) (by sep_frame)))

theorem seg3_sHat_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (sigma : List (BitVec 8)) (Rest : SepProp)
    (hsig : sigma.length = 32)
    (hpc : s.pc = b + off3480) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off48cc) s
      (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
       ((sp + 29408#64) ↦ₛ sigma) ∗
       memRegion (sp + 1568#64) 640 ∗
       memRegion (sp + 8416#64) 1536 ∗
       memRegion (sp + 9984#64) 384 ∗
       memRegion (sp + 17376#64) 512 ∗
       memRegion (sp + 27840#64) 128 ∗
       memRegion (sp + 29024#64) 128 ∗
       memRegion (sp + 29440#64) 32 ∗
       memRegion (sp + 29616#64) 99 ∗
       memRegion (sp + 29744#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = sp + 17376#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        ∃ t' : Spill40, (∀ env i, i < 24 → t'.get i = evalSExpr env (seg3SpillConsts.get i)) ∧
          (Pf ⊢ ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
            ((sp + 29408#64) ↦ₛ sigma) ∗ ((sp + 29440#64) ↦ₛ sigma) ∗
            SHatMem sp sigma ∗ SpillSliceMem 40 (sp + 1568#64) t' ∗
            memRegion (sp + 9984#64) 384 ∗ memRegion (sp + 17376#64) 512 ∗
            memRegion (sp + 27840#64) 128 ∗ memRegion (sp + 29024#64) 128 ∗
            memRegion (sp + 29616#64) 99 ∗ memRegion (sp + 29744#64) 128 ∗
            stackAt sp 1136 ∗ Rest)) := by
  have h384 : memRegion (sp + 9984#64) 384 =
      memRegion (sp + 9984#64) 32 ∗ memRegion (sp + 10016#64) 352 :=
    memRegion_split' (b := sp + 9984#64) (b' := sp + 10016#64) (n := 32) (k := (352 : Nat))
      rfl (by bv_omega) (by decide)
  have h512 : memRegion (sp + 17376#64) 512 =
      memRegion (sp + 17376#64) 128 ∗ memRegion (sp + 17504#64) 384 :=
    memRegion_split' (b := sp + 17376#64) (b' := sp + 17504#64) (n := 128) (k := (384 : Nat))
      rfl (by bv_omega) (by decide)
  rw [h384, h512]
  refine SepWP.weaken_pre
    (P' := ((sp + 29408#64) ↦ₛ sigma) ∗ memRegion (sp + 9984#64) 32 ∗
      memRegion (sp + 17376#64) 128 ∗ memRegion (sp + 27840#64) 128 ∗
      memRegion (sp + 29024#64) 128 ∗ memRegion (sp + 29440#64) 32 ∗
      memRegion (sp + 29616#64) 99 ∗ memRegion (sp + 29744#64) 128 ∗ stackAt sp 1136 ∗
      (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ memRegion (sp + 1568#64) 640 ∗
        memRegion (sp + 8416#64) 1536 ∗ memRegion (sp + 10016#64) 352 ∗
        memRegion (sp + 17504#64) 384 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (sHat_prf_calls hb hbase s sp sigma _ hsig hpc hrun hsp hspA hfp hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, hx20_1, hx21_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [← h384, ← h512]
  set prf0 := shake256List 128 (sigma ++ [0#8])
  set prf1 := shake256List 128 (sigma ++ [1#8])
  set prf2 := shake256List 128 (sigma ++ [2#8])
  refine SepWP.weaken_pre
    (P' := ((sp + 29744#64) ↦ₛ prf0) ∗ ((sp + 29024#64) ↦ₛ prf1) ∗ ((sp + 27840#64) ↦ₛ prf2) ∗
      memRegion (sp + 9984#64) 384 ∗ memRegion (sp + 1568#64) 640 ∗
      (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ ((sp + 29408#64) ↦ₛ sigma) ∗
        ((sp + 29440#64) ↦ₛ sigma) ∗ memRegion (sp + 8416#64) 1536 ∗
        memRegion (sp + 17376#64) 512 ∗ memRegion (sp + 29616#64) 99 ∗
        stackAt sp 1136 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (sHat_copy_and_zetas hb hbase s1 sp prf0 prf1 prf2 _
      (shake256List_length 128 _) (shake256List_length 128 _) (shake256List_length 128 _)
      hpc1 hrun1 hsp1 hspA1 hfp1 hx19_1 hx20_1 hx21_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hfp2, r0, r1, r2, r3, r4, r6, r9, r10, r11,
     r13, r14, r15, r16, r17, r18, r19, r20, r21, rv3, t0, ht0, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.weaken_pre
    (P' := ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
      ((sp + 9984#64) ↦ₛ prf0) ∗ ((sp + 10112#64) ↦ₛ prf1) ∗ ((sp + 10240#64) ↦ₛ prf2) ∗
      memRegion (sp + 8416#64) 1536 ∗ memRegion (sp + 17376#64) 512 ∗
      SpillSliceMem 40 (sp + 1568#64) t0 ∗
      (((sp + 29408#64) ↦ₛ sigma) ∗ ((sp + 29440#64) ↦ₛ sigma) ∗
        memRegion (sp + 27840#64) 128 ∗ memRegion (sp + 29024#64) 128 ∗
        memRegion (sp + 29616#64) 99 ∗ memRegion (sp + 29744#64) 128 ∗
        stackAt sp 1136 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl2 hro2
    (sHat_loop hb hbase s2 sp sigma t0 ht0 _
      hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hfp2 r0 r1 r2 r3 r4 r6
      r9 r10 r11 r13 r14 r15 r16 r17 r18 r19 r20 r21 rv3) ?_
  rintro sf Pf hpcf hrunf _ _ ⟨hspf, hspAf, hfpf, r19f, r20f, hclf, hrof, t', ht', hPf⟩
  refine SepWP.done hpcf hrunf ⟨hspf, hspAf, hfpf, r19f, r20f, hclf, hrof, t', ht', ?_⟩
  exact Entails.trans hPf (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat

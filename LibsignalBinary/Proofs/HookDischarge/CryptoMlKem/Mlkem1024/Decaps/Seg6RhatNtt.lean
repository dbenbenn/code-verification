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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6FwdLow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Cbd -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1c

/-!
# `kyber_decapsulate` (`B06`) — Segment 6 `rHat[0..3]` Loop (`+0x7ad4 .. +0x8bd8`) (`Seg6RhatNtt`)

Executes 4 iterations (`idx = 0..3`) of `cbd2` (`Seg6Cbd`), upper 5-stage binomial `NTT`
(`Seg6RhatSym1a..c`), lower 2-stage `NTT` (`Seg6FwdLow`), and Barrett reduction (`Seg6RhatSym1c`)
to produce `rHat[0..3]` at `[sp + 26320, sp + 28368)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 neonBarrettReduce16 polyNtt samplePolyCbd2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16 neonCbd2Poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (
  neonPolyNttBinomial16 neonPolyNttBinomial16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 Vec32 VecRangeMem poly32Mem_ofFn polyVecNat step_ldrQ128
  vecRangeMem_congr vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure (
  barrett_lowerFwdNtt16_upperBinomial lowerFwdNtt16 lowerFwdNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr Spill40 SpillSliceMem SymEnv SymGprs SymSpill40 SymVec32 evalSExpr evalSymGpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SrcOptMem SymSpatial SymStateMatches blk06NoRelocInRange polyPtr symSpill40_eval_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym (sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  lowerNttBinomial5_16 lowerNttBinomial5_16_size poly_eq_barrett poly_eq_lowerNttBinomial5_src)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1a (
  cfgSeg6Fwd symSeg6FwdInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1b (symSeg6FwdEnd)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1c (
  cfgSeg6Barrett run_seg6_bar1 run_seg6_bar2 run_seg6_fwd seg6_bar_ast_eq seg6_bar_noSpillVreg
  seg6_fwd_ast_eq seg6_fwd_noSpillVreg symSeg6BarEnd symSeg6BarInit symSeg6BarMid)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure (
  step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Cbd (
  offRhatCbdEnd offRhatCbdStart seg6_cbd2_rhat_loop)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6FwdLow (
  ro00Sym seg6_fwd_low_ok)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x7c04 → 0x7c0c, 0x8960 → 0x8960, 0x8bd0 → 0x8bd4]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC06 polyVecNat

@[simp, arm64_norm, wp_norm] abbrev offSeg6NttStart : BitVec 64 := BitVec.ofNat 64 31760
@[simp, arm64_norm, wp_norm] abbrev offSeg6Cmp      : BitVec 64 := BitVec.ofNat 64 35168
@[simp, arm64_norm, wp_norm] abbrev offSeg6BarB     : BitVec 64 := BitVec.ofNat 64 35172
@[simp, arm64_norm, wp_norm] abbrev offSeg6Tail     : BitVec 64 := BitVec.ofNat 64 35792
@[simp, arm64_norm, wp_norm] abbrev offSeg6RhatEnd  : BitVec 64 := BitVec.ofNat 64 35800

theorem noReloc_seg6_fwd  : blk06NoRelocInRange 7940 8722 = true := by rfl_kernel
theorem noReloc_seg6_bar1 : blk06NoRelocInRange 8781 8792 = true := by rfl_kernel
theorem noReloc_seg6_bar2 : blk06NoRelocInRange 8793 8948 = true := by rfl_kernel

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
    (hx12 : s.readReg64 .x12 = 0xf9fa#64) (hx13 : s.readReg64 .x13 = 0x47fa#64)
    (hx14 : s.readReg64 .x14 = 0x019b#64) (hx15 : s.readReg64 .x15 = 0x229b#64)
    (hx16 : s.readReg64 .x16 = 0x6833#64) (hx17 : s.readReg64 .x17 = 0xf9dd#64)
    (hx18 : s.readReg64 .x18 = 0xc0dd#64) :
    SymStateMatches sp (mkNttEnv s t fDst cbd) symSeg6FwdInit s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 => exact hv0
    | 2 => exact hv2
    | 3 => exact hv3
    | 1 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 12 => exact hx12 | 13 => exact hx13 | 14 => exact hx14 | 15 => exact hx15
    | 16 => exact hx16 | 17 => exact hx17 | 18 => exact hx18
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 19 | 20 | 21
    | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symSeg6FwdInit, SymGprs.get, evalSymGpr, mkNttEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem matches_barInit {sp : BitVec 64} {s : State} (q : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16)
    (hx3 : s.readReg64 .x3 = 0x4ebf#64) :
    SymStateMatches sp (mkBarEnv s q) symSeg6BarInit s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 3 => exact hv3
    | 0 | 1 | 2 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 3 => exact hx3
    | 0 | 1 | 2 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symSeg6BarInit, SymGprs.get, evalSymGpr, mkBarEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem evalSExpr_pstate0_irrel (env : SymEnv) (ps : PState) (e : SExpr) :
    evalSExpr { env with pstate0 := ps } e = evalSExpr env e := by
  induction e <;> simp [evalSExpr, *]

private theorem spillSlice40_nttInit (sp : BitVec 64) {t : Spill40}
    (ht : ∀ env i, i < 24 → t.get i = evalSExpr env (symSeg6FwdInit.spill.get i))
    (env : SymEnv) (hsp0 : env.spill0 = t) :
    SpillSliceMem 40 (sp + 1792#64) (symSeg6FwdInit.spill.eval env) =
      SpillSliceMem 40 (sp + 1792#64) t :=
  vecRangeMem_congr fun i hi => by
    rw [symSpill40_eval_get env symSeg6FwdInit.spill i hi]
    by_cases h24 : i < 24
    · exact (ht env i h24).symm
    · match i with
      | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31
      | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 =>
        simp [symSeg6FwdInit, SymSpill40.get, evalSExpr, hsp0]
      | _ + 40 => omega
        | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11
        | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 => omega

private theorem spill_consts24_nttEnd (env0 env : SymEnv) (i : Nat) (hi : i < 24) :
    (symSeg6FwdEnd.spill.eval env0).get i = evalSExpr env (symSeg6FwdInit.spill.get i) := by
  rw [symSpill40_eval_get env0 symSeg6FwdEnd.spill i (by omega)]
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11
  | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 =>
    rfl
  | _ + 24 => omega

private theorem seg6_pre_ntt [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (_hidx : idx < 4) (cbd : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offRhatCbdEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 idx)
    (hx22 : s.readReg64 .x22 = sp + 26320#64) :
    let polyAddr := sp + 26320#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg6NttStart) s
      (PolyMem (sp + 14432#64) (polyVecNat cbd) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readVReg128 0#5 = polyVecNat cbd 16 ∧
        sf.readVReg128 2#5 = polyVecNat cbd 18 ∧
        sf.readVReg128 3#5 = s.readVReg128 3#5 ∧
        sf.readReg64 .x5 = polyAddr ∧
        (∀ r : BitVec 5, r ≠ 5#5 → r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = (PolyMem (sp + 14432#64) (polyVecNat cbd) ∗ Rest)) := by
  dsimp only
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine step_ldrQ128 (wb := none) (ea := sp + 14432#64 + BitVec.ofNat 64 (16 * 16)) (v := polyVecNat cbd 16)
    (by wp_norm_lhs) hrun (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 16) (by omega) rfl))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := sp + 14432#64 + BitVec.ofNat 64 (16 * 18)) (v := polyVecNat cbd 18)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 18) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
      by simp, by simp, by simp,
      by simp [Reg.x5]; clear * - _hidx; bv_omega,
      fun r hr5 hr31 => ?_, rfl⟩
  rcases r with ⟨rv, hrv⟩
  match rv with
  | 0 | 1 | 2 | 3 | 4 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
  | 5 => exact absurd rfl hr5
  | 31 => exact absurd rfl hr31
  | _ + 32 => omega

private theorem subsPState64_z (x y : BitVec 64) : (subsPState64 x y).z = (x == y) :=
  conditionHolds_eq_subsPState64 x y

set_option maxRecDepth 50000 in
private theorem seg6_cmp4 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) {idx : Nat} (hidx : idx < 4) (P : SepProp)
    (hpc : s.pc = b + offSeg6Cmp) (hrun : s.status = .Running)
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 (idx + 1)) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg6BarB) s P
      (fun sf Pf =>
        sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        sf.vregs = s.vregs ∧
        (∀ r : BitVec 5, r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        sf.pstate.z = decide (idx = 3) ∧
        Pf = P) := by
  subst hbase
  wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp [State.spAligned], rfl, fun r hr => ?_,
     by simp only [State.setPC, State.setPState, subsPState64_z]
        rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 by omega) with rfl | rfl | rfl | rfl <;> decide,
     rfl⟩
  rcases r with ⟨rv, hrv⟩
  match rv with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
  | 31 => exact absurd rfl hr
  | _ + 32 => omega

@[simp, arm64_norm, wp_norm] private abbrev offSeg6TailBr : BitVec 64 := BitVec.ofNat 64 35796

private theorem seg6_loop_tail [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) {idx : Nat} (hidx : idx < 4) (P : SepProp)
    (hpc : s.pc = b + offSeg6Tail) (hrun : s.status = .Running)
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 (idx + 1))
    (hpz : s.pstate.z = decide (idx = 3)) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if idx < 3 then b + offRhatCbdStart else b + offSeg6RhatEnd) s P
      (fun sf Pf =>
        sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        sf.vregs = s.vregs ∧
        sf.readReg64 .x5 = BitVec.ofNat 64 (idx + 1) ∧
        (∀ r : BitVec 5, r ≠ 5#5 → r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = P) := by
  subst hbase
  by_cases hlt : idx < 3
  · simp only [hlt, ↓reduceIte]
    wp_step
    refine step_bCond_taken (dst := blkPl06.base + offRhatCbdStart)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [ConditionHolds, hpz, show idx ≠ 3 by omega])
      (by clear * -; dsimp [offSeg6TailBr, offRhatCbdStart]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], rfl, by simp, fun r hr5 hr31 => ?_, rfl⟩
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
    | 5 => exact absurd rfl hr5
    | 31 => exact absurd rfl hr31
    | _ + 32 => omega
  · have h3 : idx = 3 := by omega
    subst h3
    simp only [Nat.lt_irrefl, ↓reduceIte]
    wp_step
    refine step_bCond_not_taken (dst := blkPl06.base + offSeg6RhatEnd)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [ConditionHolds, hpz])
      (by clear * -; dsimp [offSeg6TailBr, offSeg6RhatEnd]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], rfl, by simp, fun r hr5 hr31 => ?_, rfl⟩
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
    | 5 => exact absurd rfl hr5
    | 31 => exact absurd rfl hr31
    | _ + 32 => omega

theorem seg6_rhat_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 4)
    (prf : List (BitVec 8)) (hprf : prf.length = 128)
    (t : Spill40) (ht : ∀ env i, i < 24 → t.get i = evalSExpr env (symSeg6FwdInit.spill.get i))
    (fDst : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offRhatCbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx1 : s.readReg64 .x1 = 0xf301#64)
    (hx2 : s.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx3 : s.readReg64 .x3 = 0x4ebf#64)
    (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 idx)
    (hx7 : s.readReg64 .x7 = sp + 30449#64 + BitVec.ofNat 64 (128 * idx))
    (hx9 : s.readReg64 .x9 = sp + 26336#64 + BitVec.ofNat 64 (512 * idx))
    (hx10 : s.readReg64 .x10 = 16#64 + BitVec.ofNat 64 (512 * idx))
    (hx12 : s.readReg64 .x12 = 0xf9fa#64) (hx13 : s.readReg64 .x13 = 0x47fa#64)
    (hx14 : s.readReg64 .x14 = 0x019b#64) (hx15 : s.readReg64 .x15 = 0x229b#64)
    (hx16 : s.readReg64 .x16 = 0x6833#64) (hx17 : s.readReg64 .x17 = 0xf9dd#64)
    (hx18 : s.readReg64 .x18 = 0xc0dd#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = sp + 14432#64)
    (hx22 : s.readReg64 .x22 = sp + 26320#64)
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16) :
    let prfPtr := sp + BitVec.ofNat 64 (30448 + 128 * idx)
    let polyAddr := sp + 26320#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC06.rebase b (fun _ => none))
      (if idx < 3 then b + offRhatCbdStart else b + offSeg6RhatEnd) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 14432#64) 512 ∗
        SpillSliceMem 40 (sp + 1792#64) t ∗ PolyMem polyAddr fDst ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧
        sf.readReg64 .x1 = 0xf301#64 ∧
        sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        sf.readReg64 .x3 = 0x4ebf#64 ∧
        sf.readReg64 .x5 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x7 = sp + 30449#64 + BitVec.ofNat 64 (128 * (idx + 1)) ∧
        sf.readReg64 .x9 = sp + 26336#64 + BitVec.ofNat 64 (512 * (idx + 1)) ∧
        sf.readReg64 .x10 = 16#64 + BitVec.ofNat 64 (512 * (idx + 1)) ∧
        sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
        sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
        sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
        sf.readReg64 .x18 = 0xc0dd#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x21 = sp + 14432#64 ∧
        sf.readReg64 .x22 = sp + 26320#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        ∃ t' : Spill40, (∀ env i, i < 24 → t'.get i = evalSExpr env (symSeg6FwdInit.spill.get i)) ∧
          (Pf ⊢ (prfPtr ↦ₛ prf) ∗ memRegion (sp + 14432#64) 512 ∗
            SpillSliceMem 40 (sp + 1792#64) t' ∗
            PolyMem polyAddr (polyVecNat (rHatPoly16 prf)) ∗ Rest)) := by
  dsimp only
  set prfPtr := sp + BitVec.ofNat 64 (30448 + 128 * idx)
  set polyAddr := sp + 26320#64 + BitVec.ofNat 64 (512 * idx)
  set cbd := neonCbd2Poly16 prf
  have hcbd : cbd.size = 256 := (neonCbd2Poly16_spec hprf).1.1
  have hx7' : s.readReg64 .x7 = prfPtr + 1#64 := by
    rw [hx7]; dsimp only [prfPtr]; clear * -; bv_omega
  refine sepWP_seq_env hcl hro
    (seg6_cbd2_rhat_loop hb hbase s sp prfPtr prf
      (SpillSliceMem 40 (sp + 1792#64) t ∗ PolyMem polyAddr fDst ∗ Rest)
      hprf hpc hrun hsp hspA hx7' hx19 hx21) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, r0, r1, r2, r3, r4, r5, r7, r9, r10, r12, r13, r14, r15,
      r16, r17, r18, r19, r21, r22, rfp, rv3, rfl⟩
  refine SepWP.weaken_pre
    (show (prfPtr ↦ₛ prf) ∗ PolyMem (sp + 14432#64) (polyVecNat cbd) ∗
        (SpillSliceMem 40 (sp + 1792#64) t ∗ PolyMem polyAddr fDst ∗ Rest) ⊢
      PolyMem (sp + 14432#64) (polyVecNat cbd) ∗
        ((prfPtr ↦ₛ prf) ∗ SpillSliceMem 40 (sp + 1792#64) t ∗ PolyMem polyAddr fDst ∗ Rest) by
      sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6_pre_ntt hb hbase s1 sp hidx cbd _ hpc1 hrun1 hsp1 hspA1
      (r5.trans hx5) (r22.trans hx22)) ?_
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
  have hx21_2 : s2.readReg64 .x21 = sp + 14432#64 :=
    (hgpr2 21#5 (by decide) (by decide)).trans r21
  have hx22_2 : s2.readReg64 .x22 = sp + 26320#64 :=
    (hgpr2 22#5 (by decide) (by decide)).trans (r22.trans hx22)
  have hfp_2 : s2.readReg64 .fp = s.readReg64 .fp :=
    (hgpr2 29#5 (by decide) (by decide)).trans rfp
  set envN := mkNttEnv s2 t fDst cbd
  set F_ntt := (prfPtr ↦ₛ prf) ∗ Rest
  have hP2_sym : PolyMem (sp + 14432#64) (polyVecNat cbd) ∗
      ((prfPtr ↦ₛ prf) ∗ SpillSliceMem 40 (sp + 1792#64) t ∗ PolyMem polyAddr fDst ∗ Rest) ⊢
      SymSpatial cfgSeg6Fwd sp envN symSeg6FwdInit F_ntt := by
    dsimp only [SymSpatial, cfgSeg6Fwd, polyPtr, SrcOptMem, F_ntt]
    rw [spillSlice40_nttInit sp ht envN rfl]
    dsimp only [envN, mkNttEnv]
    rw [show s2.readReg64 (.gpr 5#5) = polyAddr from hx5_2,
        ← poly32Mem_ofFn polyAddr fDst,
        ← poly32Mem_ofFn (sp + 14432#64) (polyVecNat cbd)]
    change Poly32Mem (sp + 14432#64) _ ∗ ((prfPtr ↦ₛ prf) ∗ SpillSliceMem 40 (sp + 1792#64) t ∗
        Poly32Mem polyAddr _ ∗ Rest) ⊢
      SpillSliceMem 40 (sp + 1792#64) t ∗ Poly32Mem polyAddr _ ∗
        Poly32Mem (sp + 14432#64) _ ∗ ((prfPtr ↦ₛ prf) ∗ Rest)
    sep_frame
  refine SepWP.weaken_pre hP2_sym
    (sepWP_seq_env hcl2 hro2
      (sepWP_of_runSymRange (cfg := cfgSeg6Fwd) (env := envN) (F := F_ntt)
        782 7940 noReloc_seg6_fwd (by decide) (by decide) (by decide)
        run_seg6_fwd
        (matches_nttInit t fDst cbd hsp2 hspA2 hv0_2 hv2_2 (hv3_2.trans (rv3.trans hv3))
          hx12_2 hx13_2 hx14_2 hx15_2 hx16_2 hx17_2 hx18_2)
        hpc2 hrun2
        (post := fun s3 P3 => SymStateMatches sp envN symSeg6FwdEnd s3 ∧
          P3 = SymSpatial cfgSeg6Fwd sp envN symSeg6FwdEnd F_ntt)
        (fun s3 _ _ hm3 => ⟨hm3, rfl⟩)) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hm3, rfl⟩
  have gpr3_eq : ∀ (r : BitVec 5) (hr : r ≠ 31#5),
      s3.readReg64 (.gpr r) = evalSymGpr sp envN.gpr0 (symSeg6FwdEnd.gprs.get r.toNat) :=
    fun r hr => hm3.hgprs r hr
  have hx0_3 : s3.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx0_2] using gpr3_eq 0#5 (by decide)
  have hx1_3 : s3.readReg64 .x1 = 0xf301#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx1_2] using gpr3_eq 1#5 (by decide)
  have hx2_3 : s3.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx2_2] using gpr3_eq 2#5 (by decide)
  have hx3_3 : s3.readReg64 .x3 = 0x4ebf#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx3_2] using gpr3_eq 3#5 (by decide)
  have hx4_3 : s3.readReg64 .x4 = BitVec.ofNat 64 (idx + 1) := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx4_2] using gpr3_eq 4#5 (by decide)
  have hx5_3 : s3.readReg64 .x5 = polyAddr := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx5_2] using gpr3_eq 5#5 (by decide)
  have hx6_3 : s3.readReg64 .x6 = polyAddr + 16#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx9_2] using gpr3_eq 6#5 (by decide)
  have hx7_3 : s3.readReg64 .x7 = prfPtr + 1#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx7_2] using gpr3_eq 7#5 (by decide)
  have hx8_3 : s3.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx0_2] using gpr3_eq 8#5 (by decide)
  have hx9_3 : s3.readReg64 .x9 = polyAddr + 16#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx9_2] using gpr3_eq 9#5 (by decide)
  have hx10_3 : s3.readReg64 .x10 = 16#64 + BitVec.ofNat 64 (512 * idx) := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx10_2] using gpr3_eq 10#5 (by decide)
  have hx12_3 : s3.readReg64 .x12 = 0xf9fa#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr] using gpr3_eq 12#5 (by decide)
  have hx13_3 : s3.readReg64 .x13 = 0x47fa#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr] using gpr3_eq 13#5 (by decide)
  have hx14_3 : s3.readReg64 .x14 = 0x019b#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr] using gpr3_eq 14#5 (by decide)
  have hx15_3 : s3.readReg64 .x15 = 0x229b#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr] using gpr3_eq 15#5 (by decide)
  have hx16_3 : s3.readReg64 .x16 = 0x6833#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr] using gpr3_eq 16#5 (by decide)
  have hx17_3 : s3.readReg64 .x17 = 0xf9dd#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr] using gpr3_eq 17#5 (by decide)
  have hx18_3 : s3.readReg64 .x18 = 0xc0dd#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr] using gpr3_eq 18#5 (by decide)
  have hx19_3 : s3.readReg64 .x19 = 0x55555555#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx19_2] using gpr3_eq 19#5 (by decide)
  have hx20_3 : s3.readReg64 .x20 = 16#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr] using gpr3_eq 20#5 (by decide)
  have hx21_3 : s3.readReg64 .x21 = sp + 14432#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx21_2] using gpr3_eq 21#5 (by decide)
  have hx22_3 : s3.readReg64 .x22 = sp + 26320#64 := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hx22_2] using gpr3_eq 22#5 (by decide)
  have hfp_3 : s3.readReg64 .fp = s.readReg64 .fp := by
    simpa [symSeg6FwdEnd, SymGprs.get, evalSymGpr, envN, mkNttEnv, hfp_2] using gpr3_eq 29#5 (by decide)
  have hv3_3 : s3.readVReg128 3#5 = dup8x16 3329#16 := hm3.hvregs 3#5
  set t1 := symSeg6FwdEnd.spill.eval envN
  have ht1 : ∀ env i, i < 24 → t1.get i = evalSExpr env (symSeg6FwdInit.spill.get i) :=
    fun env i hi => spill_consts24_nttEnd envN env i hi
  set p3 := lowerNttBinomial5_16 cbd
  have hp3 : p3.size = 256 := (lowerNttBinomial5_16_size cbd).trans hcbd
  have hp3_mem : Poly32Mem (polyPtr cfgSeg6Fwd sp envN) (symSeg6FwdEnd.poly.eval envN) =
      PolyMem polyAddr (polyVecNat p3) := by
    have hptr : polyPtr cfgSeg6Fwd sp envN = polyAddr := hx5_2
    rw [hptr]
    exact poly_eq_lowerNttBinomial5_src polyAddr hcbd envN rfl symSeg6FwdEnd.poly
      seg6_fwd_noSpillVreg seg6_fwd_ast_eq
  have hsrc3 : SrcOptMem true sp envN.src0 ⊢ memRegion (sp + 14432#64) 512 := by
    dsimp only [SrcOptMem, Poly32Mem, PolyMem]
    simpa using vecRangeMem_entails_memRegion 32 (sp + 14432#64) (fun i => envN.src0.get i)
  set F_low := memRegion (sp + 14432#64) 512 ∗ SpillSliceMem 40 (sp + 1792#64) t1 ∗ F_ntt
  have hP3_low : SymSpatial cfgSeg6Fwd sp envN symSeg6FwdEnd F_ntt ⊢
      PolyMem polyAddr (polyVecNat p3) ∗ F_low := by
    dsimp only [SymSpatial, F_low, t1]
    rw [hp3_mem]
    dsimp only [cfgSeg6Fwd]
    exact entails_sub hsrc3 (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP3_low
    (sepWP_seq_env hcl3 hro3
      (seg6_fwd_low_ok hb s3 sp polyAddr hp3 F_low
        hpc3 hrun3 hm3.hsp hm3.hsp_al hcl3 hro3 hx8_3 hx2_3 hx6_3 hx20_3 hx1_3
        (by rw [hx22_3, hx10_3]; dsimp only [polyAddr]; clear * -; bv_omega) hv3_3) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hpres4, rfl⟩
  set q := lowerFwdNtt16 p3
  have hq : q.size = 256 := (lowerFwdNtt16_size p3).trans hp3
  set envB := mkBarEnv s4 q
  have hP4_bar : PolyMem polyAddr (polyVecNat q) ∗ F_low ⊢
      SymSpatial cfgSeg6Barrett sp envB symSeg6BarInit F_low := by
    dsimp only [SymSpatial, cfgSeg6Barrett, polyPtr, SrcOptMem,
      SpillSliceMem, VecRangeMem, envB, mkBarEnv]
    rw [hpres4.hx5.trans hx5_3, ← poly32Mem_ofFn polyAddr (polyVecNat q)]
    change Poly32Mem polyAddr _ ∗ F_low ⊢ emp ∗ Poly32Mem polyAddr _ ∗ emp ∗ F_low
    sep_frame
  refine SepWP.weaken_pre hP4_bar
    (sepWP_seq_env hcl4 hro4
      (sepWP_of_runSymRange (cfg := cfgSeg6Barrett) (env := envB) (F := F_low)
        11 8781 noReloc_seg6_bar1 (by decide) (by decide) (by decide)
        run_seg6_bar1
        (matches_barInit q hsp4 hspA4 (hpres4.hv3.trans hv3_3) (hpres4.hx3.trans hx3_3))
        hpc4 hrun4
        (post := fun s5 P5 => SymStateMatches sp envB symSeg6BarMid s5 ∧
          P5 = SymSpatial cfgSeg6Barrett sp envB symSeg6BarMid F_low)
        (fun s5 _ _ hm5 => ⟨hm5, rfl⟩)) ?_)
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hm5, rfl⟩
  have hx4_5 : s5.readReg64 .x4 = BitVec.ofNat 64 (idx + 1) := by
    simpa [symSeg6BarMid, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx4.trans hx4_3]
      using hm5.hgprs 4#5 (by decide)
  refine sepWP_seq_env hcl5 hro5
    (seg6_cmp4 hb hbase s5 hidx _ hpc5 hrun5 hx4_5) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 hro6 ⟨hsp6, hspA6, hvregs6, hgpr6, hpz6, rfl⟩
  set envB' : SymEnv := { envB with pstate0 := s6.pstate }
  have hm6 : SymStateMatches sp envB' symSeg6BarMid s6 := by
    refine ⟨hsp6.trans hm5.hsp, hspA6.trans hm5.hsp_al, rfl, fun r => ?_, fun r hr => ?_⟩
    · rw [State.readVReg128, hvregs6]
      exact (hm5.hvregs r).trans (evalSExpr_pstate0_irrel envB s6.pstate _).symm
    · exact (hgpr6 r hr).trans (hm5.hgprs r hr)
  have hP6_bar : SymSpatial cfgSeg6Barrett sp envB symSeg6BarMid F_low ⊢
      SymSpatial cfgSeg6Barrett sp envB' symSeg6BarMid F_low := by
    dsimp only [SymSpatial, cfgSeg6Barrett, polyPtr, SrcOptMem, SpillSliceMem, VecRangeMem,
      SymVec32.eval, envB']
    simp only [evalSExpr_pstate0_irrel]
    exact Entails.refl _
  refine SepWP.weaken_pre hP6_bar
    (sepWP_seq_env hcl6 hro6
      (sepWP_of_runSymRange (cfg := cfgSeg6Barrett) (env := envB') (F := F_low)
        155 8793 noReloc_seg6_bar2 (by decide) (by decide) (by decide)
        run_seg6_bar2 hm6 hpc6 hrun6
        (post := fun s7 P7 => SymStateMatches sp envB' symSeg6BarEnd s7 ∧
          P7 = SymSpatial cfgSeg6Barrett sp envB' symSeg6BarEnd F_low)
        (fun s7 _ _ hm7 => ⟨hm7, rfl⟩)) ?_)
  rintro s7 P7 hpc7 hrun7 hcl7 hro7 ⟨hm7, rfl⟩
  have gpr7_eq : ∀ (r : BitVec 5) (hr : r ≠ 31#5),
      s7.readReg64 (.gpr r) = evalSymGpr sp envB.gpr0 (symSeg6BarEnd.gprs.get r.toNat) :=
    fun r hr => hm7.hgprs r hr
  have hx4_7 : s7.readReg64 .x4 = BitVec.ofNat 64 (idx + 1) := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx4.trans hx4_3]
      using gpr7_eq 4#5 (by decide)
  have hpz7 : s7.pstate.z = decide (idx = 3) := hm7.hpstate ▸ hpz6
  have hp7_mem : Poly32Mem (polyPtr cfgSeg6Barrett sp envB') (symSeg6BarEnd.poly.eval envB') =
      PolyMem polyAddr (polyVecNat (rHatPoly16 prf)) := by
    have hptr : polyPtr cfgSeg6Barrett sp envB' = polyAddr := hpres4.hx5.trans hx5_3
    rw [hptr, poly_eq_barrett polyAddr hq envB' rfl symSeg6BarEnd.poly
      seg6_bar_noSpillVreg seg6_bar_ast_eq, barrett_lowerFwd_lowerBinomial5 cbd]
    rfl
  have hP7 : SymSpatial cfgSeg6Barrett sp envB' symSeg6BarEnd F_low ⊢
      (prfPtr ↦ₛ prf) ∗ memRegion (sp + 14432#64) 512 ∗
        SpillSliceMem 40 (sp + 1792#64) t1 ∗ PolyMem polyAddr (polyVecNat (rHatPoly16 prf)) ∗ Rest := by
    dsimp only [SymSpatial, F_low, F_ntt]
    rw [hp7_mem]
    dsimp only [cfgSeg6Barrett, SrcOptMem, SpillSliceMem, VecRangeMem]
    change emp ∗ PolyMem polyAddr (polyVecNat (rHatPoly16 prf)) ∗ emp ∗
        (memRegion (sp + 14432#64) 512 ∗ VecRangeMem 40 (sp + 1792#64) (fun i => t1.get i) ∗
          ((prfPtr ↦ₛ prf) ∗ Rest)) ⊢
      (prfPtr ↦ₛ prf) ∗ memRegion (sp + 14432#64) 512 ∗
        VecRangeMem 40 (sp + 1792#64) (fun i => t1.get i) ∗
        PolyMem polyAddr (polyVecNat (rHatPoly16 prf)) ∗ Rest
    sep_frame
  refine SepWP.weaken_pre hP7
    (sepWP_seq_env hcl7 hro7 (seg6_loop_tail hb hbase s7 hidx _ hpc7 hrun7 hx4_7 hpz7) ?_)
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hvregsf, hx5f, hgprf, rfl⟩
  have hvf : ∀ r : BitVec 5, sf.readVReg128 r = s7.readVReg128 r :=
    fun r => by simp [State.readVReg128, hvregsf]
  have gprf_eq : ∀ (r : BitVec 5) (hr5 : r ≠ 5#5) (hr31 : r ≠ 31#5),
      sf.readReg64 (.gpr r) = evalSymGpr sp envB.gpr0 (symSeg6BarEnd.gprs.get r.toNat) :=
    fun r hr5 hr31 => (hgprf r hr5 hr31).trans (gpr7_eq r hr31)
  have hx0_f : sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx0.trans hx0_3]
      using gprf_eq 0#5 (by decide) (by decide)
  have hx1_f : sf.readReg64 .x1 = 0xf301#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx1.trans hx1_3]
      using gprf_eq 1#5 (by decide) (by decide)
  have hx2_f : sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx2.trans hx2_3]
      using gprf_eq 2#5 (by decide) (by decide)
  have hx3_f : sf.readReg64 .x3 = 0x4ebf#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr] using gprf_eq 3#5 (by decide) (by decide)
  have hx7_f : sf.readReg64 .x7 = sp + 30449#64 + BitVec.ofNat 64 (128 * (idx + 1)) := by
    have h := gprf_eq 7#5 (by decide) (by decide)
    simp only [BitVec.toNat_ofNat, symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv] at h
    rw [show sf.readReg64 .x7 = sf.readReg64 (.gpr 7#5) from rfl, h,
      show s4.readReg64 (.gpr 7#5) = s4.readReg64 .x7 from rfl, hpres4.hx7, hx7_3]
    dsimp only [prfPtr]; clear * - hidx; bv_omega
  have hx9_f : sf.readReg64 .x9 = sp + 26336#64 + BitVec.ofNat 64 (512 * (idx + 1)) := by
    have h := gprf_eq 9#5 (by decide) (by decide)
    simp only [BitVec.toNat_ofNat, symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv] at h
    rw [show sf.readReg64 .x9 = sf.readReg64 (.gpr 9#5) from rfl, h,
      show s4.readReg64 (.gpr 9#5) = s4.readReg64 .x9 from rfl, hpres4.hx9, hx9_3]
    dsimp only [polyAddr]; clear * - hidx; bv_omega
  have hx10_f : sf.readReg64 .x10 = 16#64 + BitVec.ofNat 64 (512 * (idx + 1)) := by
    have h := gprf_eq 10#5 (by decide) (by decide)
    simp only [BitVec.toNat_ofNat, symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv] at h
    rw [show sf.readReg64 .x10 = sf.readReg64 (.gpr 10#5) from rfl, h,
      show s4.readReg64 (.gpr 10#5) = s4.readReg64 .x10 from rfl, hpres4.hx10, hx10_3]
    clear * - hidx; bv_omega
  have hx12_f : sf.readReg64 .x12 = 0xf9fa#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx12.trans hx12_3]
      using gprf_eq 12#5 (by decide) (by decide)
  have hx13_f : sf.readReg64 .x13 = 0x47fa#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx13.trans hx13_3]
      using gprf_eq 13#5 (by decide) (by decide)
  have hx14_f : sf.readReg64 .x14 = 0x019b#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx14.trans hx14_3]
      using gprf_eq 14#5 (by decide) (by decide)
  have hx15_f : sf.readReg64 .x15 = 0x229b#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx15.trans hx15_3]
      using gprf_eq 15#5 (by decide) (by decide)
  have hx16_f : sf.readReg64 .x16 = 0x6833#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx16.trans hx16_3]
      using gprf_eq 16#5 (by decide) (by decide)
  have hx17_f : sf.readReg64 .x17 = 0xf9dd#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx17.trans hx17_3]
      using gprf_eq 17#5 (by decide) (by decide)
  have hx18_f : sf.readReg64 .x18 = 0xc0dd#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx18.trans hx18_3]
      using gprf_eq 18#5 (by decide) (by decide)
  have hx19_f : sf.readReg64 .x19 = 0x55555555#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx19.trans hx19_3]
      using gprf_eq 19#5 (by decide) (by decide)
  have hx21_f : sf.readReg64 .x21 = sp + 14432#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx21.trans hx21_3]
      using gprf_eq 21#5 (by decide) (by decide)
  have hx22_f : sf.readReg64 .x22 = sp + 26320#64 := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hx22.trans hx22_3]
      using gprf_eq 22#5 (by decide) (by decide)
  have hfp_f : sf.readReg64 .fp = s.readReg64 .fp := by
    simpa [symSeg6BarEnd, SymGprs.get, evalSymGpr, envB, mkBarEnv, hpres4.hfp.trans hfp_3]
      using gprf_eq 29#5 (by decide) (by decide)
  have hv3_f : sf.readVReg128 3#5 = dup8x16 0x0d01#16 := by
    rw [hvf 3#5]; exact hm7.hvregs 3#5
  exact SepWP.done hpcf hrunf
    ⟨hspf.trans hm7.hsp, hspAf.trans hm7.hsp_al, hx0_f, hx1_f, hx2_f, hx3_f,
      hx5f, hx7_f, hx9_f, hx10_f, hx12_f, hx13_f, hx14_f, hx15_f, hx16_f, hx17_f, hx18_f,
      hx19_f, hx21_f, hx22_f, hfp_f, hv3_f, hclf, hrof, t1, ht1, Entails.refl _⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt

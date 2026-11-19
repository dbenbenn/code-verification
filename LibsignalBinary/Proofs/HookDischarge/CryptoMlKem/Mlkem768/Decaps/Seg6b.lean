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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6a -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2c
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Fwd2LowLoops

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 6b (`rHat[0..2]`, `+0x7134 .. +0x85d8`) (`Seg6b`)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b

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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  shake256List_length step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 Spill13 Spill13Mem Vec32 poly32Mem_entails_memRegion
  poly32Mem_ofFn polyVecNat step_ldrQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  Spill21 Spill21Mem Spill6 Spill6Mem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (
  SymGprs31 SymVRegs runSymRange runSymRange_add symInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval (
  SymEnv SymSpatial SymStateMatches evalSExpr evalSymGpr evalSymPState evalSymSpill13
  evalSymSpill21 evalSymSpill6 evalSymVec32 inPolyMemAt polyAddr spillMemAt symEnvOf)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly (sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure (
  upperFwdNttBinomial16 upperFwdNttBinomial16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge (
  symPoly_eq_barrettMap symPoly_eq_upperFwdNttBinomial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2a (
  cfgFwd2 run_fwd2a symFwd2Init)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2b (
  fwd2_hi_ast_eq fwd2_hi_noSpillVreg run_fwd2b symFwd2HiEnd)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd2c (
  cfgFwd2Tail fwd2_tail_ast_eq fwd2_tail_noSpillVreg run_fwd2_tail symFwd2TailEnd symFwd2TailInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure (
  barrett_lowerFwdNtt16_upperBinomial lowerFwdNtt16 lowerFwdNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Fwd2LowLoops (fwd2_low_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6a (
  fwd2Spill13 fwd2Spill6 offSeg6CbdEnd offSeg6CbdStart offSeg6Start ro00Sym
  seg6_cbd2_loop seg6_prf_setup setFwd2Spill21)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x7608 → 0x760c, 0x85d0 → 0x85d4]
end

attribute [local irreducible] blkPC04 polyVecNat

@[simp, arm64_norm, wp_norm] abbrev offSeg6NttStart : BitVec 64 := BitVec.ofNat 64 30224
@[simp, arm64_norm, wp_norm] abbrev offSeg6Tail     : BitVec 64 := BitVec.ofNat 64 34256
@[simp, arm64_norm, wp_norm] abbrev offSeg6RhatEnd  : BitVec 64 := BitVec.ofNat 64 34264

/-- `Poly16` result of `cbd2` followed by 7-stage binomial NEON `NTT` + Barrett reduction. -/
@[expose] def rHatPoly16 (prf : List (BitVec 8)) : Poly16 :=
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

private theorem shake256List_len128 (bs : List (BitVec 8)) :
    (shake256List 128 bs).length = 128 :=
  shake256List_length 128 bs

private theorem neonCbd2Poly16_size {prf : List (BitVec 8)} (hprf : prf.length = 128) :
    (neonCbd2Poly16 prf).size = 256 :=
  (neonCbd2Poly16_spec hprf).1.1

private theorem run_fwd2ab : runSymRange cfgFwd2 7556 782 symFwd2Init = some symFwd2HiEnd :=
  runSymRange_add cfgFwd2 7556 391 391 _ _ _ run_fwd2a run_fwd2b

private theorem spill_fwd2Init (env : SymEnv) (t21 : Spill21)
    (ht : env.spill21_0 = setFwd2Spill21 t21) :
    evalSymSpill13 env symFwd2Init.spill13 = fwd2Spill13 ∧
    evalSymSpill6 env symFwd2Init.spill6 = fwd2Spill6 ∧
    evalSymSpill21 env symFwd2Init.spill21 = setFwd2Spill21 t21 := by
  refine ⟨rfl, rfl, ?_⟩
  dsimp only [symFwd2Init, evalSymSpill21, evalSExpr]
  rw [ht]; cases t21; rfl

private theorem spill_fwd2HiEnd (env : SymEnv) :
    evalSymSpill13 env symFwd2HiEnd.spill13 = fwd2Spill13 ∧
    evalSymSpill6 env symFwd2HiEnd.spill6 = fwd2Spill6 ∧
    evalSymSpill21 env symFwd2HiEnd.spill21 =
      setFwd2Spill21 (evalSymSpill21 env symFwd2HiEnd.spill21) :=
  ⟨rfl, rfl, rfl⟩

private theorem matches_fwd2Init (s : State) (sp polyPtr : BitVec 64)
    (t21 : Spill21) (fOut : Nat → BitVec 128) (p : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hx5 : s.readReg64 .x5 = polyPtr)
    (hv0 : s.readVReg128 0#5 = polyVecNat p 16)
    (hv2 : s.readVReg128 2#5 = polyVecNat p 18)
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16)
    (hx12 : s.readReg64 .x12 = 0xf9fa#64) (hx13 : s.readReg64 .x13 = 0x47fa#64)
    (hx14 : s.readReg64 .x14 = 0x019b#64) (hx15 : s.readReg64 .x15 = 0x229b#64)
    (hx16 : s.readReg64 .x16 = 0x6833#64) (hx17 : s.readReg64 .x17 = 0xf9dd#64)
    (hx18 : s.readReg64 .x18 = 0xc0dd#64) :
    let env := symEnvOf s fwd2Spill13 fwd2Spill6 (setFwd2Spill21 t21)
      (Vec32.ofFn fOut) (Vec32.ofFn (polyVecNat p))
    SymStateMatches cfgFwd2 sp polyPtr env symFwd2Init s := by
  dsimp only
  refine ⟨hsp, hspA, ?_, ?_, ?_, rfl⟩
  · rintro r ⟨rfl⟩; exact hx5
  · intro r; rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 => simpa [symFwd2Init, SymVRegs.get, evalSExpr, symEnvOf, Vec32.ofFn, Vec32.get] using hv0
    | 2 => simpa [symFwd2Init, SymVRegs.get, evalSExpr, symEnvOf, Vec32.ofFn, Vec32.get] using hv2
    | 3 => simpa [symFwd2Init, SymVRegs.get, evalSExpr] using hv3
    | 1 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · intro r hr; rcases r with ⟨rv, hrv⟩
    match rv with
    | 12 => simpa [symFwd2Init, SymGprs31.get, evalSymGpr] using hx12
    | 13 => simpa [symFwd2Init, SymGprs31.get, evalSymGpr] using hx13
    | 14 => simpa [symFwd2Init, SymGprs31.get, evalSymGpr] using hx14
    | 15 => simpa [symFwd2Init, SymGprs31.get, evalSymGpr] using hx15
    | 16 => simpa [symFwd2Init, SymGprs31.get, evalSymGpr] using hx16
    | 17 => simpa [symFwd2Init, SymGprs31.get, evalSymGpr] using hx17
    | 18 => simpa [symFwd2Init, SymGprs31.get, evalSymGpr] using hx18
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11
    | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symFwd2Init, SymGprs31.get, evalSymGpr, symEnvOf]
    | 31 => simp at hr
    | _ + 32 => omega

private theorem matches_fwd2TailInit (s : State) (sp polyPtr : BitVec 64)
    (t21 : Spill21) (q : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hx5 : s.readReg64 .x5 = polyPtr)
    (hx3 : s.readReg64 .x3 = 20159#64) :
    let env := symEnvOf s fwd2Spill13 fwd2Spill6 t21 (Vec32.ofFn (polyVecNat q)) Vec32.zero
    SymStateMatches cfgFwd2Tail sp polyPtr env symFwd2TailInit s := by
  dsimp only
  refine ⟨hsp, hspA, ?_, ?_, ?_, rfl⟩
  · rintro r ⟨rfl⟩; exact hx5
  · intro r; rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · intro r hr; rcases r with ⟨rv, hrv⟩
    match rv with
    | 3 => simpa [symFwd2TailInit, symInit, SymGprs31.ofFn, SymGprs31.get, evalSymGpr] using hx3
    | 0 | 1 | 2 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18
    | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symFwd2TailInit, symInit, SymGprs31.ofFn, SymGprs31.get, evalSymGpr, symEnvOf]
    | 31 => simp at hr
    | _ + 32 => omega

private theorem seg6_pre_ntt [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (_hidx : idx < 3) (cbd : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6CbdEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 idx)
    (hx21 : s.readReg64 .x21 = sp + 19168#64) :
    let pPtr := sp + BitVec.ofNat 64 (19168 + 512 * idx)
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6NttStart) s
      (PolyMem (sp + 11856#64) (polyVecNat cbd) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readVReg128 0#5 = polyVecNat cbd 16 ∧
        sf.readVReg128 2#5 = polyVecNat cbd 18 ∧
        sf.readVReg128 3#5 = s.readVReg128 3#5 ∧
        sf.readReg64 .x5 = pPtr ∧
        (∀ r : BitVec 5, r ≠ 5#5 → r.toNat < 31 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = (PolyMem (sp + 11856#64) (polyVecNat cbd) ∗ Rest)) := by
  dsimp only
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine step_ldrQ128 (wb := none) (ea := (sp + 11856#64) + BitVec.ofNat 64 (16 * 16))
    (v := polyVecNat cbd 16)
    (by wp_norm_lhs) hrun (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 16) (by omega) rfl))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := (sp + 11856#64) + BitVec.ofNat 64 (16 * 18))
    (v := polyVecNat cbd 18)
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
  | 31 => simp at hr31
  | _ + 32 => omega

private theorem seg6_loop_tail [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) {idx : Nat} (hidx : idx < 3) (P : SepProp)
    (hpc : s.pc = b + offSeg6Tail) (hrun : s.status = .Running)
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 (idx + 1))
    (hpst : s.pstate = (AddWithCarry64 (BitVec.ofNat 64 (idx + 1)) (~~~3#64) true).2) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if idx < 2 then b + offSeg6CbdStart else b + offSeg6RhatEnd) s P
      (fun sf Pf =>
        sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ sf.vregs = s.vregs ∧
        sf.readReg64 .x5 = BitVec.ofNat 64 (idx + 1) ∧
        (∀ r : BitVec 5, r ≠ 5#5 → r.toNat < 31 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = P) := by
  subst hbase
  wp_step
  have hother : ∀ (v pc1 pc2 : BitVec 64) (r : BitVec 5), r ≠ 5#5 → r.toNat < 31 →
      (((s.writeReg64 (.gpr 5#5) v).setPC pc1).setPC pc2).readReg64 (.gpr r) =
      s.readReg64 (.gpr r) := fun v pc1 pc2 r hr5 hr31 => by
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
    | 5 => exact absurd rfl hr5
    | 31 => simp at hr31
    | _ + 32 => omega
  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 by omega) with rfl | rfl | rfl
  · simp only [show (0 : Nat) < 2 by decide, ↓reduceIte]
    refine step_bCond_taken (dst := blkPl04.base + offSeg6CbdStart)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [hpst]; exact (by decide +kernel : ConditionHolds .NE (AddWithCarry64 1#64 (~~~3#64) true).2 = true))
      (by clear * -; dsimp only [offSeg6CbdStart]; bv_omega) ?_
    exact SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], rfl, by simp,
       fun r hr5 hr31 => hother 1#64 _ _ r hr5 hr31, rfl⟩
  · simp only [show (1 : Nat) < 2 by decide, ↓reduceIte]
    refine step_bCond_taken (dst := blkPl04.base + offSeg6CbdStart)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [hpst]; exact (by decide +kernel : ConditionHolds .NE (AddWithCarry64 2#64 (~~~3#64) true).2 = true))
      (by clear * -; dsimp only [offSeg6CbdStart]; bv_omega) ?_
    exact SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], rfl, by simp,
       fun r hr5 hr31 => hother 2#64 _ _ r hr5 hr31, rfl⟩
  · simp only [Nat.lt_irrefl, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl04.base + offSeg6RhatEnd)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [hpst]; exact (by decide +kernel : ConditionHolds .NE (AddWithCarry64 3#64 (~~~3#64) true).2 = false))
      (by clear * -; dsimp only [offSeg6RhatEnd]; bv_omega) ?_
    exact SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], rfl, by simp,
       fun r hr5 hr31 => hother 3#64 _ _ r hr5 hr31, rfl⟩

private theorem seg6_rhat_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3)
    (prf : List (BitVec 8)) (hprf : prf.length = 128)
    (t21 : Spill21) (fOut : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6CbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx1 : s.readReg64 .x1 = 0xf301#64)
    (hx2 : s.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx3 : s.readReg64 .x3 = 0x4ebf#64)
    (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 idx)
    (hx7 : s.readReg64 .x7 = sp + BitVec.ofNat 64 (22401 + 128 * idx))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (19184 + 512 * idx))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (16 + 512 * idx))
    (hx12 : s.readReg64 .x12 = 0xf9fa#64) (hx13 : s.readReg64 .x13 = 0x47fa#64)
    (hx14 : s.readReg64 .x14 = 0x019b#64) (hx15 : s.readReg64 .x15 = 0x229b#64)
    (hx16 : s.readReg64 .x16 = 0x6833#64) (hx17 : s.readReg64 .x17 = 0xf9dd#64)
    (hx18 : s.readReg64 .x18 = 0xc0dd#64) (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64) (hx21 : s.readReg64 .x21 = sp + 19168#64)
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16) :
    let prfPtr := sp + BitVec.ofNat 64 (22400 + 128 * idx)
    let pPtr := sp + BitVec.ofNat 64 (19168 + 512 * idx)
    SepWP (blkPC04.rebase b (fun _ => none))
      (if idx < 2 then b + offSeg6CbdStart else b + offSeg6RhatEnd) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 11856#64) 512 ∗ PolyMem pPtr fOut ∗
        Spill13Mem (sp + 1616#64) fwd2Spill13 ∗ Spill6Mem (sp + 1824#64) fwd2Spill6 ∗
        Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧ sf.readReg64 .x1 = 0xf301#64 ∧
        sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧ sf.readReg64 .x3 = 0x4ebf#64 ∧
        sf.readReg64 .x5 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x7 = sp + BitVec.ofNat 64 (22401 + 128 * (idx + 1)) ∧
        sf.readReg64 .x9 = sp + BitVec.ofNat 64 (19184 + 512 * (idx + 1)) ∧
        sf.readReg64 .x10 = BitVec.ofNat 64 (16 + 512 * (idx + 1)) ∧
        sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
        sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
        sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
        sf.readReg64 .x18 = 0xc0dd#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 11856#64 ∧ sf.readReg64 .x21 = sp + 19168#64 ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        ∃ t21' : Spill21,
          (Pf ⊢ (prfPtr ↦ₛ prf) ∗ memRegion (sp + 11856#64) 512 ∗
            PolyMem pPtr (polyVecNat (rHatPoly16 prf)) ∗
            Spill13Mem (sp + 1616#64) fwd2Spill13 ∗ Spill6Mem (sp + 1824#64) fwd2Spill6 ∗
            Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21') ∗ Rest)) := by
  intro prfPtr pPtr
  set p0 := neonCbd2Poly16 prf
  have hp0 : p0.size = 256 := neonCbd2Poly16_size hprf
  have hx7' : s.readReg64 .x7 = prfPtr + 1#64 := by
    rw [hx7]; dsimp only [prfPtr]; clear * - hidx; bv_omega
  refine sepWP_seq_env hcl hro
    (seg6_cbd2_loop hb hbase s sp prfPtr prf _ hprf hpc hrun hsp hspA hx7' hx19 hx20) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, g0, g1, g2, g3, g4, g5, g7, g9, g10, g12, g13, g14, g15,
      g16, g17, g18, g19, g20, g21, gfp, gv3, rfl⟩
  refine SepWP.weaken_pre
    (show (prfPtr ↦ₛ prf) ∗ PolyMem (sp + 11856#64) (polyVecNat p0) ∗
        (PolyMem pPtr fOut ∗ Spill13Mem (sp + 1616#64) fwd2Spill13 ∗
          Spill6Mem (sp + 1824#64) fwd2Spill6 ∗ Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21) ∗ Rest) ⊢
      PolyMem (sp + 11856#64) (polyVecNat p0) ∗
        ((prfPtr ↦ₛ prf) ∗ PolyMem pPtr fOut ∗ Spill13Mem (sp + 1616#64) fwd2Spill13 ∗
          Spill6Mem (sp + 1824#64) fwd2Spill6 ∗ Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21) ∗ Rest)
      by sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6_pre_ntt hb hbase s1 sp hidx p0 _ hpc1 hrun1 hsp1 hspA1 (g5.trans hx5) (g21.trans hx21)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hv0_2, hv2_2, hv3_2, hx5_2, hgpr2, rfl⟩
  set env := symEnvOf s2 fwd2Spill13 fwd2Spill6 (setFwd2Spill21 t21)
    (Vec32.ofFn fOut) (Vec32.ofFn (polyVecNat p0))
  set F_fwd := (prfPtr ↦ₛ prf) ∗ Rest
  have hm2 : SymStateMatches cfgFwd2 sp pPtr env symFwd2Init s2 :=
    matches_fwd2Init s2 sp pPtr t21 fOut p0 hsp2 hspA2 hx5_2 hv0_2 hv2_2
      (hv3_2.trans (gv3.trans hv3))
      ((hgpr2 12#5 (by decide) (by decide)).trans (g12.trans hx12))
      ((hgpr2 13#5 (by decide) (by decide)).trans (g13.trans hx13))
      ((hgpr2 14#5 (by decide) (by decide)).trans (g14.trans hx14))
      ((hgpr2 15#5 (by decide) (by decide)).trans (g15.trans hx15))
      ((hgpr2 16#5 (by decide) (by decide)).trans (g16.trans hx16))
      ((hgpr2 17#5 (by decide) (by decide)).trans (g17.trans hx17))
      ((hgpr2 18#5 (by decide) (by decide)).trans (g18.trans hx18))
  have hP2_sym : PolyMem (sp + 11856#64) (polyVecNat p0) ∗
      ((prfPtr ↦ₛ prf) ∗ PolyMem pPtr fOut ∗ Spill13Mem (sp + 1616#64) fwd2Spill13 ∗
        Spill6Mem (sp + 1824#64) fwd2Spill6 ∗ Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21) ∗ Rest) ⊢
      SymSpatial cfgFwd2 sp pPtr env symFwd2Init F_fwd := by
    dsimp only [SymSpatial, cfgFwd2, polyAddr, spillMemAt, inPolyMemAt, F_fwd]
    obtain ⟨hs13, hs6, hs21⟩ := spill_fwd2Init env t21 rfl
    have hp_init : evalSymVec32 env symFwd2Init.poly = Vec32.ofFn fOut := by
      dsimp only [env, symEnvOf]; generalize Vec32.ofFn fOut = v0; cases v0; rfl
    have hin_init : env.inPoly0 = Vec32.ofFn (polyVecNat p0) := rfl
    rw [hs13, hs6, hs21, hp_init, hin_init, poly32Mem_ofFn pPtr fOut, poly32Mem_ofFn (sp + 11856#64) (polyVecNat p0)]
    sep_frame
  refine SepWP.weaken_pre hP2_sym
    (sepWP_seq_env hcl2 hro2
      (sepWP_of_runSymRange (cfg := cfgFwd2) (sp := sp) (polyPtr := pPtr) (env := env) (F := F_fwd)
        782 7556 (fun j h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))
        run_fwd2ab hm2 hpc2 hrun2
        (post := fun s3 P3 => SymStateMatches cfgFwd2 sp pPtr env symFwd2HiEnd s3 ∧
          P3 = SymSpatial cfgFwd2 sp pPtr env symFwd2HiEnd F_fwd)
        (fun s3 _ _ hm3 => ⟨hm3, rfl⟩)) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hm3, rfl⟩
  have h2g : ∀ r : BitVec 5, r ≠ 5#5 → r.toNat < 31 → s2.readReg64 (.gpr r) = s1.readReg64 (.gpr r) := hgpr2
  have hx0_3 : s3.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 :=
    (hm3.hgprs 0#5 (by decide)).trans ((h2g 0#5 (by decide) (by decide)).trans (g0.trans hx0))
  have hx1_3 : s3.readReg64 .x1 = 0xf301#64 :=
    (hm3.hgprs 1#5 (by decide)).trans ((h2g 1#5 (by decide) (by decide)).trans (g1.trans hx1))
  have hx2_3 : s3.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 :=
    (hm3.hgprs 2#5 (by decide)).trans ((h2g 2#5 (by decide) (by decide)).trans (g2.trans hx2))
  have hx3_3 : s3.readReg64 .x3 = 0x4ebf#64 :=
    (hm3.hgprs 3#5 (by decide)).trans ((h2g 3#5 (by decide) (by decide)).trans (g3.trans hx3))
  have hx4_3 : s3.readReg64 .x4 = BitVec.ofNat 64 (idx + 1) :=
    (hm3.hgprs 4#5 (by decide)).trans ((h2g 4#5 (by decide) (by decide)).trans
      (by rw [g4, hx5]; clear * - hidx; bv_omega))
  have hx5_3 : s3.readReg64 .x5 = pPtr := hm3.hpoly 5#5 rfl
  have hx6_3 : s3.readReg64 .x6 = pPtr + 16#64 :=
    (hm3.hgprs 6#5 (by decide)).trans ((h2g 9#5 (by decide) (by decide)).trans
      (by rw [g9, hx9]; dsimp only [pPtr]; clear * - hidx; bv_omega))
  have hx7_3 : s3.readReg64 .x7 = sp + BitVec.ofNat 64 (22401 + 128 * idx) :=
    (hm3.hgprs 7#5 (by decide)).trans ((h2g 7#5 (by decide) (by decide)).trans
      (by rw [g7]; dsimp only [prfPtr]; clear * - hidx; bv_omega))
  have hx8_3 : s3.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64 :=
    (hm3.hgprs 8#5 (by decide)).trans ((h2g 0#5 (by decide) (by decide)).trans (g0.trans hx0))
  have hx9_3 : s3.readReg64 .x9 = sp + BitVec.ofNat 64 (19184 + 512 * idx) :=
    (hm3.hgprs 9#5 (by decide)).trans ((h2g 9#5 (by decide) (by decide)).trans (g9.trans hx9))
  have hx10_3 : s3.readReg64 .x10 = BitVec.ofNat 64 (16 + 512 * idx) :=
    (hm3.hgprs 10#5 (by decide)).trans ((h2g 10#5 (by decide) (by decide)).trans (g10.trans hx10))
  have hx12_3 : s3.readReg64 .x12 = 0xf9fa#64 := hm3.hgprs 12#5 (by decide)
  have hx13_3 : s3.readReg64 .x13 = 0x47fa#64 := hm3.hgprs 13#5 (by decide)
  have hx14_3 : s3.readReg64 .x14 = 0x019b#64 := hm3.hgprs 14#5 (by decide)
  have hx15_3 : s3.readReg64 .x15 = 0x229b#64 := hm3.hgprs 15#5 (by decide)
  have hx16_3 : s3.readReg64 .x16 = 0x6833#64 := hm3.hgprs 16#5 (by decide)
  have hx17_3 : s3.readReg64 .x17 = 0xf9dd#64 := hm3.hgprs 17#5 (by decide)
  have hx18_3 : s3.readReg64 .x18 = 0xc0dd#64 := hm3.hgprs 18#5 (by decide)
  have hx19_3 : s3.readReg64 .x19 = 0x55555555#64 :=
    (hm3.hgprs 19#5 (by decide)).trans ((h2g 19#5 (by decide) (by decide)).trans g19)
  have hx20_3 : s3.readReg64 .x20 = sp + 11856#64 :=
    (hm3.hgprs 20#5 (by decide)).trans ((h2g 20#5 (by decide) (by decide)).trans g20)
  have hx21_3 : s3.readReg64 .x21 = sp + 19168#64 :=
    (hm3.hgprs 21#5 (by decide)).trans ((h2g 21#5 (by decide) (by decide)).trans (g21.trans hx21))
  have hx22_3 : s3.readReg64 .x22 = 16#64 := hm3.hgprs 22#5 (by decide)
  have hfp_3 : s3.readReg64 .fp = s.readReg64 .fp :=
    (hm3.hgprs 29#5 (by decide)).trans ((h2g 29#5 (by decide) (by decide)).trans gfp)
  have hv3_3 : s3.readVReg128 3#5 = dup8x16 3329#16 := hm3.hvregs 3#5
  set pUp := upperFwdNttBinomial16 p0
  have hpUp : pUp.size = 256 := (upperFwdNttBinomial16_size p0).trans hp0
  have hp3_mem : Poly32Mem pPtr (evalSymVec32 env symFwd2HiEnd.poly) =
      PolyMem pPtr (polyVecNat pUp) :=
    symPoly_eq_upperFwdNttBinomial pPtr symFwd2HiEnd.poly hp0 env rfl fwd2_hi_noSpillVreg fwd2_hi_ast_eq
  set t21' := evalSymSpill21 env symFwd2HiEnd.spill21
  set F_low := memRegion (sp + 11856#64) 512 ∗ Spill13Mem (sp + 1616#64) fwd2Spill13 ∗
    Spill6Mem (sp + 1824#64) fwd2Spill6 ∗ Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21') ∗ F_fwd
  have hP3 : SymSpatial cfgFwd2 sp pPtr env symFwd2HiEnd F_fwd ⊢
      PolyMem pPtr (polyVecNat pUp) ∗ F_low := by
    dsimp only [SymSpatial, cfgFwd2, polyAddr, spillMemAt, inPolyMemAt, F_low]
    obtain ⟨hs13, hs6, hs21⟩ := spill_fwd2HiEnd env
    rw [hp3_mem, hs13, hs6, hs21]
    exact entails_sub (poly32Mem_entails_memRegion (sp + 11856#64) _) (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP3
    (sepWP_seq_env hcl3 hro3
      (fwd2_low_ok hb s3 sp pPtr hpUp F_low
        hpc3 hrun3 hm3.hsp hm3.hsp_al hcl3 hro3 hx8_3 hx2_3 hx6_3 hx22_3 hx1_3
        (by rw [hx21_3, hx10_3]; dsimp only [pPtr]; clear * - hidx; bv_omega) hv3_3) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hpres4, rfl⟩
  set q := lowerFwdNtt16 pUp
  have hq : q.size = 256 := (lowerFwdNtt16_size pUp).trans hpUp
  set envB := symEnvOf s4 fwd2Spill13 fwd2Spill6 (setFwd2Spill21 t21') (Vec32.ofFn (polyVecNat q)) Vec32.zero
  have hm4 : SymStateMatches cfgFwd2Tail sp pPtr envB symFwd2TailInit s4 :=
    matches_fwd2TailInit s4 sp pPtr (setFwd2Spill21 t21') q hsp4 hspA4
      (hpres4.x5.trans hx5_3) (hpres4.x3.trans hx3_3)
  have hP4 : PolyMem pPtr (polyVecNat q) ∗ F_low ⊢
      SymSpatial cfgFwd2Tail sp pPtr envB symFwd2TailInit F_low := by
    dsimp only [SymSpatial, cfgFwd2Tail, polyAddr, spillMemAt, inPolyMemAt]
    have hp_init4 : evalSymVec32 envB symFwd2TailInit.poly = Vec32.ofFn (polyVecNat q) := by
      dsimp only [symFwd2TailInit, symInit, envB, symEnvOf]
      generalize Vec32.ofFn (polyVecNat q) = vq; cases vq; rfl
    rw [hp_init4, poly32Mem_ofFn pPtr (polyVecNat q)]
    sep_frame
  refine SepWP.weaken_pre hP4
    (sepWP_seq_env hcl4 hro4
      (sepWP_of_runSymRange (cfg := cfgFwd2Tail) (sp := sp) (polyPtr := pPtr) (env := envB) (F := F_low)
        167 8397 (fun j h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))
        run_fwd2_tail hm4 hpc4 hrun4
        (post := fun s5 P5 => SymStateMatches cfgFwd2Tail sp pPtr envB symFwd2TailEnd s5 ∧
          P5 = SymSpatial cfgFwd2Tail sp pPtr envB symFwd2TailEnd F_low)
        (fun s5 _ _ hm5 => ⟨hm5, rfl⟩)) ?_)
  rintro s5 P5 hpc5 hrun5 _ _ ⟨hm5, rfl⟩
  have hp5_mem : Poly32Mem pPtr (evalSymVec32 envB symFwd2TailEnd.poly) =
      PolyMem pPtr (polyVecNat (rHatPoly16 prf)) := by
    rw [symPoly_eq_barrettMap pPtr symFwd2TailEnd.poly hq envB rfl
      fwd2_tail_noSpillVreg fwd2_tail_ast_eq, barrett_lowerFwdNtt16_upperBinomial p0]
    dsimp only [rHatPoly16, p0]
  have hx4_4 : s4.readReg64 .x4 = BitVec.ofNat 64 (idx + 1) := hpres4.x4.trans hx4_3
  have hx4_5 : s5.readReg64 .x4 = BitVec.ofNat 64 (idx + 1) :=
    (hm5.hgprs 4#5 (by decide)).trans hx4_4
  have hpst5 : s5.pstate = (AddWithCarry64 (BitVec.ofNat 64 (idx + 1)) (~~~3#64) true).2 := by
    have hp := hm5.hpstate
    simpa [symFwd2TailEnd, evalSymPState, evalSymGpr, envB, symEnvOf, hx4_4] using hp
  refine SepWP.mono (seg6_loop_tail hb hbase s5 hidx _ hpc5 hrun5 hx4_5 hpst5) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hvregs_f, hx5_f, hgpr_f, rfl⟩
  have hv3_f : sf.readVReg128 3#5 = dup8x16 0x0d01#16 := by
    have hvr : sf.readVReg128 3#5 = s5.readVReg128 3#5 := by simp [State.readVReg128, hvregs_f]
    exact hvr.trans ((hm5.hvregs 3#5).trans (hpres4.v3.trans hv3_3))
  refine ⟨hsp_f.trans hm5.hsp, hspA_f.trans hm5.hsp_al,
    (hgpr_f 29#5 (by decide) (by decide)).trans ((hm5.hgprs 29#5 (by decide)).trans (hpres4.fp.trans hfp_3)),
    (hgpr_f 0#5 (by decide) (by decide)).trans ((hm5.hgprs 0#5 (by decide)).trans (hpres4.x0.trans hx0_3)),
    (hgpr_f 1#5 (by decide) (by decide)).trans ((hm5.hgprs 1#5 (by decide)).trans (hpres4.x1.trans hx1_3)),
    (hgpr_f 2#5 (by decide) (by decide)).trans ((hm5.hgprs 2#5 (by decide)).trans (hpres4.x2.trans hx2_3)),
    (hgpr_f 3#5 (by decide) (by decide)).trans (hm5.hgprs 3#5 (by decide)),
    hx5_f,
    (hgpr_f 7#5 (by decide) (by decide)).trans ((hm5.hgprs 7#5 (by decide)).trans
      (by change s4.readReg64 .x7 + 128#64 = _
          rw [hpres4.x7.trans hx7_3]; clear * - hidx; bv_omega)),
    (hgpr_f 9#5 (by decide) (by decide)).trans ((hm5.hgprs 9#5 (by decide)).trans
      (by change s4.readReg64 .x9 + 512#64 = _
          rw [hpres4.x9.trans hx9_3]; clear * - hidx; bv_omega)),
    (hgpr_f 10#5 (by decide) (by decide)).trans ((hm5.hgprs 10#5 (by decide)).trans
      (by change s4.readReg64 .x10 + 512#64 = _
          rw [hpres4.x10.trans hx10_3]; clear * - hidx; bv_omega)),
    (hgpr_f 12#5 (by decide) (by decide)).trans ((hm5.hgprs 12#5 (by decide)).trans (hpres4.x12.trans hx12_3)),
    (hgpr_f 13#5 (by decide) (by decide)).trans ((hm5.hgprs 13#5 (by decide)).trans (hpres4.x13.trans hx13_3)),
    (hgpr_f 14#5 (by decide) (by decide)).trans ((hm5.hgprs 14#5 (by decide)).trans (hpres4.x14.trans hx14_3)),
    (hgpr_f 15#5 (by decide) (by decide)).trans ((hm5.hgprs 15#5 (by decide)).trans (hpres4.x15.trans hx15_3)),
    (hgpr_f 16#5 (by decide) (by decide)).trans ((hm5.hgprs 16#5 (by decide)).trans (hpres4.x16.trans hx16_3)),
    (hgpr_f 17#5 (by decide) (by decide)).trans ((hm5.hgprs 17#5 (by decide)).trans (hpres4.x17.trans hx17_3)),
    (hgpr_f 18#5 (by decide) (by decide)).trans ((hm5.hgprs 18#5 (by decide)).trans (hpres4.x18.trans hx18_3)),
    (hgpr_f 19#5 (by decide) (by decide)).trans ((hm5.hgprs 19#5 (by decide)).trans (hpres4.x19.trans hx19_3)),
    (hgpr_f 20#5 (by decide) (by decide)).trans ((hm5.hgprs 20#5 (by decide)).trans (hpres4.x20.trans hx20_3)),
    (hgpr_f 21#5 (by decide) (by decide)).trans ((hm5.hgprs 21#5 (by decide)).trans (hpres4.x21.trans hx21_3)),
    hv3_f, t21', ?_⟩
  dsimp only [SymSpatial, cfgFwd2Tail, polyAddr, spillMemAt, inPolyMemAt, F_low, F_fwd]
  rw [hp5_mem]
  sep_frame

set_option maxRecDepth 200000 in
/-- Full `rHat[0..2]` sub-segment (`+0x7134 → +0x85d8`). -/
theorem seg6_rhat_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + offSeg6Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let coins := hashed.drop 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6RhatEnd) s
      (((sp + 4496#64) ↦ₛ hashed) ∗
       memRegion (sp + 1616#64) 640 ∗
       memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 18032#64) 1088 ∗
       memRegion (sp + 19120#64) 33 ∗ memRegion (sp + 19168#64) 1536 ∗
       memRegion (sp + 20704#64) 128 ∗ memRegion (sp + 22400#64) 384 ∗
       memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 99 ∗
       memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        ∃ t21 : Spill21,
          (Pf ⊢ ((sp + 4496#64) ↦ₛ hashed) ∗
            Spill13Mem (sp + 1616#64) fwd2Spill13 ∗ Spill6Mem (sp + 1824#64) fwd2Spill6 ∗
            Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21) ∗
            memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 18032#64) 1088 ∗
            ((sp + 19120#64) ↦ₛ coins) ∗ ((sp + 19152#64) ↦₈ 0#8) ∗
            PolyMem (sp + 19168#64) (polyVecNat (rHatPoly16 prf0)) ∗
            PolyMem (sp + 19680#64) (polyVecNat (rHatPoly16 prf1)) ∗
            PolyMem (sp + 20192#64) (polyVecNat (rHatPoly16 prf2)) ∗
            memRegion (sp + 20704#64) 128 ∗
            ((sp + 22400#64) ↦ₛ prf0) ∗ ((sp + 22528#64) ↦ₛ prf1) ∗ ((sp + 22656#64) ↦ₛ prf2) ∗
            memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 99 ∗
            memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest)) := by
  intro coins prf0 prf1 prf2
  refine sepWP_seq_env hcl hro
    (seg6_prf_setup hb hbase s sp hashed Rest hh hpc hrun hsp hspA hx19 hx20 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx0_1, hx1_1, hx2_1, hx3_1, hx5_1, hx7_1, hx9_1, hx10_1,
      hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx18_1, hx19_1, hx20_1, hx21_1,
      hv3_1, _, _, t21_0, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have h0 := seg6_rhat_iter hb hbase s1 sp (idx := 0) (by decide)
    prf0 (shake256List_len128 _) t21_0 (fun _ => 0#128)
    (((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 18032#64) 1088 ∗
      ((sp + 19120#64) ↦ₛ coins) ∗ ((sp + 19152#64) ↦₈ 0#8) ∗
      PolyMem (sp + 19680#64) (fun _ => 0#128) ∗ PolyMem (sp + 20192#64) (fun _ => 0#128) ∗
      memRegion (sp + 20704#64) 128 ∗ ((sp + 22528#64) ↦ₛ prf1) ∗ ((sp + 22656#64) ↦ₛ prf2) ∗
      memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 99 ∗
      memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest)
    hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx0_1 hx1_1 hx2_1 hx3_1 hx5_1 hx7_1 hx9_1 hx10_1
    hx12_1 hx13_1 hx14_1 hx15_1 hx16_1 hx17_1 hx18_1 hx19_1 hx20_1 hx21_1 hv3_1
  dsimp only at h0
  simp only [show (0 : Nat) < 2 by decide, ↓reduceIte,
    show BitVec.ofNat 64 (22400 + 128 * 0) = 22400#64 by decide,
    show BitVec.ofNat 64 (19168 + 512 * 0) = 19168#64 by decide] at h0
  refine SepWP.weaken_pre (by sep_frame) (sepWP_seq_env hcl1 hro1 h0 ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hfp2, hx0_2, hx1_2, hx2_2, hx3_2, hx5_2, hx7_2, hx9_2, hx10_2,
      hx12_2, hx13_2, hx14_2, hx15_2, hx16_2, hx17_2, hx18_2, hx19_2, hx20_2, hx21_2,
      hv3_2, t21_1, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  have h1 := seg6_rhat_iter hb hbase s2 sp (idx := 1) (by decide)
    prf1 (shake256List_len128 _) t21_1 (fun _ => 0#128)
    (((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 18032#64) 1088 ∗
      ((sp + 19120#64) ↦ₛ coins) ∗ ((sp + 19152#64) ↦₈ 0#8) ∗
      PolyMem (sp + 19168#64) (polyVecNat (rHatPoly16 prf0)) ∗
      PolyMem (sp + 20192#64) (fun _ => 0#128) ∗
      memRegion (sp + 20704#64) 128 ∗ ((sp + 22400#64) ↦ₛ prf0) ∗ ((sp + 22656#64) ↦ₛ prf2) ∗
      memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 99 ∗
      memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest)
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx0_2 hx1_2 hx2_2 hx3_2 hx5_2 hx7_2 hx9_2 hx10_2
    hx12_2 hx13_2 hx14_2 hx15_2 hx16_2 hx17_2 hx18_2 hx19_2 hx20_2 hx21_2 hv3_2
  dsimp only at h1
  simp only [show (1 : Nat) < 2 by decide, ↓reduceIte,
    show BitVec.ofNat 64 (22400 + 128 * 1) = 22528#64 by decide,
    show BitVec.ofNat 64 (19168 + 512 * 1) = 19680#64 by decide] at h1
  refine SepWP.weaken_pre (by sep_frame) (sepWP_seq_env hcl2 hro2 h1 ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp3, hx0_3, hx1_3, hx2_3, hx3_3, hx5_3, hx7_3, hx9_3, hx10_3,
      hx12_3, hx13_3, hx14_3, hx15_3, hx16_3, hx17_3, hx18_3, hx19_3, hx20_3, hx21_3,
      hv3_3, t21_2, hP3⟩
  refine SepWP.weaken_pre hP3 ?_
  have h2 := seg6_rhat_iter hb hbase s3 sp (idx := 2) (by decide)
    prf2 (shake256List_len128 _) t21_2 (fun _ => 0#128)
    (((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 18032#64) 1088 ∗
      ((sp + 19120#64) ↦ₛ coins) ∗ ((sp + 19152#64) ↦₈ 0#8) ∗
      PolyMem (sp + 19168#64) (polyVecNat (rHatPoly16 prf0)) ∗
      PolyMem (sp + 19680#64) (polyVecNat (rHatPoly16 prf1)) ∗
      memRegion (sp + 20704#64) 128 ∗ ((sp + 22400#64) ↦ₛ prf0) ∗ ((sp + 22528#64) ↦ₛ prf1) ∗
      memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 99 ∗
      memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest)
    hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx0_3 hx1_3 hx2_3 hx3_3 hx5_3 hx7_3 hx9_3 hx10_3
    hx12_3 hx13_3 hx14_3 hx15_3 hx16_3 hx17_3 hx18_3 hx19_3 hx20_3 hx21_3 hv3_3
  dsimp only at h2
  simp only [Nat.lt_irrefl, ↓reduceIte,
    show BitVec.ofNat 64 (22400 + 128 * 2) = 22656#64 by decide,
    show BitVec.ofNat 64 (19168 + 512 * 2) = 20192#64 by decide] at h2
  refine SepWP.weaken_pre (by sep_frame) (SepWP.mono h2 ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, hx19_f, _, _, _, t21_3, hPf⟩
  exact ⟨hsp_f, hspA_f, hfp_f.trans (hfp3.trans (hfp2.trans hfp1)), hx19_f,
    t21_3, Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b

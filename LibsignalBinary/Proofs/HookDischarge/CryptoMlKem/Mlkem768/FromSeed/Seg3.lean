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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Matrix -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3Sym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SymE
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3EHatPrf -- proof-setup: allow-public-import

/-!
# `generate_keypair_compressed` (`B05`): Segment 3b `eHat` and full `Seg3` (`+0x3480 .. +0x5c60`)

1. `seg3_eHat_ok` (`+0x48cc → +0x5c60`): `eHat` zeroing, PRF calls, `cbd2`, 7-stage `NTT`, and
   Barrett reduction across `idx = 0, 1, 2` producing `EHatMem sp sigma` at `[sp + 17376, sp + 18912)`.
2. `seg3_secvecs_ok` (`+0x3480 → +0x5c60`): composes `seg3_sHat_ok` and `seg3_eHat_ok` starting from
   `Seg2MatrixExit`, establishing both `SHatMem` and `EHatMem` entering Segment 4 (`+0x5c60`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3
open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 neonBarrettReduce16 polyNtt samplePolyCbd2 sampleVecCbd2 sha3_512List shake256List zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (keccakSponge)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16 neonCbd2Poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonPolyNttBinomial16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepWP.of_memRegion_vecRangeMem Vec32 VecRangeMem poly32Mem_entails_memRegion
  poly32Mem_ofFn polyVecNat vecRangeMem_congr vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure (
  barrett_lowerFwdNtt16_upperBinomial lowerFwdNtt16 lowerFwdNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr Spill40 SpillSliceMem SymEnv SymGprs SymState SymVec32 evalSExpr evalSymGpr spill40_ofFn_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SrcOptMem SymSpatial SymStateMatches polyPtr symGprs_set_get symSpill40_eval_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  lowerNttBinomial5_16 lowerNttBinomial5_16_size poly_eq_barrett poly_eq_lowerNttBinomial5_src)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  SavedFrame05 blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05
  sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (offSeg3Entry)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Matrix (
  AMatrixMem Seg2MatrixExit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure (
  shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow (
  eHat_fwd_low_ok offEFwd4 offEFwdEnd ro00Sym step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3Sym (
  SrcOptMem05 SymSpatial05 sepWP_of_runSymRange05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SymE (
  cfgEHatBar cfgEHatNtt eHat_bar_ast_eq eHat_bar_noSpillVreg eHat_ntt_ast_eq eHat_ntt_noSpillVreg
  noReloc_eHat_bar_a noReloc_eHat_bar_b noReloc_eHat_ntt_a noReloc_eHat_ntt_b
  run_eHat_bar_a run_eHat_bar_b run_eHat_ntt_a run_eHat_ntt_b symEHatBarEnd symEHatBarEnd_gprs
  symEHatBarInit symEHatBarMid symEHatBarMid_gpr0 symEHatNttA symEHatNttA' symEHatNttA_gpr1
  symEHatNttA_gpr8 symEHatNttEnd symEHatNttEnd_gprs symEHatNttEnd_vreg7 symEHatNttInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat (
  SHatMem cbdNttPoly16 cbdNttPoly16_spec seg3_sHat_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3EHatPrf (
  eHat_cbd2_loop eHat_copy_regs eHat_memset eHat_prf_calls off48cc off48e8 off4a04 off4afc off4c2c)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05
  [0x51c4 → 0x51c8, 0x59e0 → 0x59e4, 0x5c58 → 0x5c60]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkLib05 blkPC05 polyVecNat shake256List dup8x16
attribute [local irreducible] symEHatNttA symEHatNttEnd symEHatBarMid symEHatBarEnd

@[simp, arm64_norm, wp_norm] abbrev off51c4 : BitVec 64 := BitVec.ofNat 64 20932
@[simp, arm64_norm, wp_norm] abbrev off51c8 : BitVec 64 := BitVec.ofNat 64 20936
@[simp, arm64_norm, wp_norm] abbrev off59e0 : BitVec 64 := BitVec.ofNat 64 23008
@[simp, arm64_norm, wp_norm] abbrev off59e4 : BitVec 64 := BitVec.ofNat 64 23012
@[simp, arm64_norm, wp_norm] abbrev off5c58 : BitVec 64 := BitVec.ofNat 64 23640
@[simp, arm64_norm, wp_norm] abbrev off5c5c : BitVec 64 := BitVec.ofNat 64 23644
@[simp, arm64_norm, wp_norm] abbrev off5c60 : BitVec 64 := BitVec.ofNat 64 23648

/-! ## 1. `eHat` Symbolic Environment & Glue Lemmas (`+0x51c4`, `+0x59e0`, `+0x5c58`) -/

private def mkEHatNttEnv (s : State) (polyAddr : BitVec 64) (t : Spill40)
    (fDst : Nat → BitVec 128) (cbd : Poly16) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := t
  poly0   := Vec32.ofFn fDst
  src0    := Vec32.ofFn (polyVecNat cbd)
  gpr0    := fun r =>
    if r = 1#5 then polyAddr
    else if r = 31#5 then s.readReg64 .x1
    else s.readReg64 (.gpr r)
  pstate0 := s.pstate

private def mkEHatBarEnv (s : State) (q : Poly16) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := Spill40.ofFn (fun _ => 0#128)
  poly0   := Vec32.ofFn (polyVecNat q)
  src0    := Vec32.zero
  gpr0    := fun r => s.readReg64 (.gpr r)
  pstate0 := s.pstate

private theorem matches_eHatNttInit {sp : BitVec 64} {s : State}
    (polyAddr : BitVec 64) (t : Spill40) (fDst : Nat → BitVec 128) (cbd : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx10 : s.readReg64 .x10 = 0x019b#64) (hx11 : s.readReg64 .x11 = 0x229b#64)
    (hx12 : s.readReg64 .x12 = 0x6833#64) (hx13 : s.readReg64 .x13 = 0xf9dd#64)
    (hx14 : s.readReg64 .x14 = 0xc0dd#64) (hx16 : s.readReg64 .x16 = 0xf301#64)
    (hx18 : s.readReg64 .x18 = 0x4ebf#64) (hx20 : s.readReg64 .x20 = 0x47fa#64)
    (hx27 : s.readReg64 .x27 = 0x0260#64) (hx28 : s.readReg64 .x28 = 0x2260#64)
    (hlr  : s.readReg64 .lr = 0xf9fa#64) :
    SymStateMatches sp (mkEHatNttEnv s polyAddr t fDst cbd) symEHatNttInit s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 1 => simp [symEHatNttInit, SymGprs.get, evalSymGpr, mkEHatNttEnv]
    | 10 => exact hx10 | 11 => exact hx11 | 12 => exact hx12 | 13 => exact hx13
    | 14 => exact hx14 | 16 => exact hx16 | 18 => exact hx18 | 20 => exact hx20
    | 27 => exact hx27 | 28 => exact hx28 | 30 => exact hlr
    | 0 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 15 | 17 | 19 | 21 | 22 | 23 | 24 | 25 | 26 | 29 =>
      simp [symEHatNttInit, SymGprs.get, evalSymGpr, mkEHatNttEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem matches_eHatBarInit {sp : BitVec 64} {s : State} (q : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx10 : s.readReg64 .x10 = 0x019b#64) (hx11 : s.readReg64 .x11 = 0x229b#64)
    (hx12 : s.readReg64 .x12 = 0x6833#64) (hx13 : s.readReg64 .x13 = 0xf9dd#64)
    (hx14 : s.readReg64 .x14 = 0xc0dd#64) (hx16 : s.readReg64 .x16 = 0xf301#64)
    (hx18 : s.readReg64 .x18 = 0x4ebf#64) (hx20 : s.readReg64 .x20 = 0x47fa#64)
    (hx27 : s.readReg64 .x27 = 0x0260#64) (hx28 : s.readReg64 .x28 = 0x2260#64)
    (hlr  : s.readReg64 .lr = 0xf9fa#64) :
    SymStateMatches sp (mkEHatBarEnv s q) symEHatBarInit s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 10 => exact hx10 | 11 => exact hx11 | 12 => exact hx12 | 13 => exact hx13
    | 14 => exact hx14 | 16 => exact hx16 | 18 => exact hx18 | 20 => exact hx20
    | 27 => exact hx27 | 28 => exact hx28 | 30 => exact hlr
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 15 | 17 | 19 | 21 | 22 | 23 | 24 | 25 | 26 | 29 =>
      simp [symEHatBarInit, symEHatNttInit, SymGprs.get, SymGprs.set, evalSymGpr, mkEHatBarEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem evalSExpr_pstate0_irrel (env : SymEnv) (ps : PState) (e : SExpr) :
    evalSExpr { env with pstate0 := ps } e = evalSExpr env e := by
  induction e <;> simp [evalSExpr, *]

private theorem symVec32_eval_pstate0_irrel (env : SymEnv) (ps : PState) (t : SymVec32) :
    t.eval { env with pstate0 := ps } = t.eval env := by
  have hf : (fun k => evalSExpr { env with pstate0 := ps } (t.get k)) =
      (fun k => evalSExpr env (t.get k)) := by
    funext k; exact evalSExpr_pstate0_irrel env ps (t.get k)
  dsimp only [SymVec32.eval]; rw [hf]

private theorem spillSlice16_eHatNttInit (sp : BitVec 64) (t : Spill40)
    (env : SymEnv) (hsp0 : env.spill0 = t) :
    SpillSliceMem 16 (sp + 1952#64) (symEHatNttInit.spill.eval env) =
      SpillSliceMem 16 (sp + 1952#64) t :=
  vecRangeMem_congr fun i hi => by
    rw [symSpill40_eval_get env symEHatNttInit.spill i (by omega)]
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
      simp [symEHatNttInit, Mlkem768.FromSeed.Seg3SymE.symEHatSpillInit,
        Mlkem1024.Decaps.PolySymDefs.SymSpill40.get, evalSExpr, hsp0]
    | _ + 16 => omega

private theorem eHat_add_x1_x8 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (P : SepProp)
    (hpc : s.pc = b + off51c4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = sp + 17376#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 idx) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off51c8) s P
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.pstate = s.pstate ∧ sf.vregs = s.vregs ∧
        sf.readReg64 .x1 = sp + 17376#64 + BitVec.ofNat 64 (512 * idx) ∧
        (∀ r : BitVec 5, r ≠ 1#5 → r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = P) := by
  subst hbase
  wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [State.setPC, State.writeReg64], by simp [State.setPC, State.writeReg64], ?_, ?_, rfl⟩
  · simp only [State.readReg64_setPC]
    change sp + 17376#64 + BitVec.ofNat 64 idx <<< 9 = sp + 17376#64 + BitVec.ofNat 64 (512 * idx)
    clear * -; bv_omega
  · intro r hr1 hr31
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
    | 1 => exact absurd rfl hr1
    | 31 => exact absurd rfl hr31
    | _ + 32 => omega

private theorem eHat_cmp3 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) {idx : Nat} (hidx : idx < 3) (P : SepProp)
    (hpc : s.pc = b + off59e0) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (idx + 1)) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off59e4) s P
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

private theorem eHat_loop_tail [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) {idx : Nat} (hidx : idx < 3) (P : SepProp)
    (hpc : s.pc = b + off5c58) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (idx + 1))
    (hpz : s.pstate.z = decide (idx = 2)) :
    SepWP (blkPC05.rebase b (fun _ => none))
      (if idx < 2 then b + off4afc else b + off5c60) s P
      (fun sf Pf =>
        sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ sf.vregs = s.vregs ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 (idx + 1) ∧
        (∀ r : BitVec 5, r ≠ 1#5 → r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = P) := by
  subst hbase
  wp_step
  by_cases hlt : idx < 2
  · simp only [hlt, ↓reduceIte]
    refine step_bCond_taken (dst := blkPl05.base + off4afc)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [ConditionHolds, hpz, show ¬(idx = 2) by omega])
      (by clear * -; dsimp [off5c5c, off4afc]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], by simp [State.setPC, State.writeReg64], by simp, ?_, rfl⟩
    intro r hr1 hr31
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
    | 1 => exact absurd rfl hr1
    | 31 => exact absurd rfl hr31
    | _ + 32 => omega
  · have h2 : idx = 2 := by omega
    subst h2
    simp only [show ¬(2 < 2) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl05.base + off5c60)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [ConditionHolds, hpz])
      (by clear * -; dsimp [off5c5c, off5c60]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp, by simp [State.spAligned], by simp [State.setPC, State.writeReg64], by simp, ?_, rfl⟩
    intro r hr1 hr31
    rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
    | 1 => exact absurd rfl hr1
    | 31 => exact absurd rfl hr31
    | _ + 32 => omega

private theorem matches_nttA_to_A' {sp polyAddr : BitVec 64} {env : SymEnv} {s s' : State}
    (hm : SymStateMatches sp env symEHatNttA s)
    (henv1 : env.gpr0 1#5 = polyAddr)
    (hsp : s'.sp = sp) (hspA : s'.spAligned = true)
    (hpst : s'.pstate = s.pstate) (hvr : s'.vregs = s.vregs)
    (hx1 : s'.readReg64 .x1 = polyAddr)
    (hgpr : ∀ r : BitVec 5, r ≠ 1#5 → r ≠ 31#5 → s'.readReg64 (.gpr r) = s.readReg64 (.gpr r)) :
    SymStateMatches sp env symEHatNttA' s' := by
  refine ⟨hsp, hspA, hpst.trans hm.hpstate, fun r => ?_, fun r hr => ?_⟩
  · rw [State.readVReg128, hvr]; exact hm.hvregs r
  · by_cases hr1 : r = 1#5
    · subst hr1
      simpa [symEHatNttA', SymGprs.get, SymGprs.set, evalSymGpr, henv1] using hx1
    · rw [hgpr r hr1 hr]
      have hlt : r.toNat < 31 := by
        have := r.isLt; have : r.toNat ≠ 31 := fun h => hr (BitVec.eq_of_toNat_eq h); omega
      have hne : r.toNat ≠ 1 := fun h => hr1 (BitVec.eq_of_toNat_eq h)
      rw [show symEHatNttA'.gprs.get r.toNat = symEHatNttA.gprs.get r.toNat by
        unfold symEHatNttA'
        rw [symGprs_set_get symEHatNttA.gprs 1 r.toNat (by decide) hlt]; simp [hne]]
      exact hm.hgprs r hr

private theorem sym_gpr_at {sp : BitVec 64} {env : SymEnv} {st : SymState} {s : State}
    (hm : SymStateMatches sp env st s) (k : Nat) (hk : k < 31) :
    s.readReg64 (.gpr (BitVec.ofNat 5 k)) = evalSymGpr sp env.gpr0 (st.gprs.get k) := by
  have hne : BitVec.ofNat 5 k ≠ 31#5 := by
    intro h; have := congrArg BitVec.toNat h
    have h31 : (31#5 : BitVec 5).toNat = 31 := rfl
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), h31] at this; omega
  have h := hm.hgprs (BitVec.ofNat 5 k) hne
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h

/-! ## 2. Single-Iteration `eHat` Body (`+0x4afc → +0x4afc / +0x5c60`) -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1200000 in
private theorem eHat_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3)
    (prf : List (BitVec 8)) (hprf : prf.length = 128)
    (t : Spill40) (fDst : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off4afc) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 idx)
    (hx3 : s.readReg64 .x3 = sp + 27841#64 + BitVec.ofNat 64 (128 * idx))
    (hx9 : s.readReg64 .x9 = sp + 17392#64 + BitVec.ofNat 64 (512 * idx))
    (hx10 : s.readReg64 .x10 = 0x019b#64) (hx11 : s.readReg64 .x11 = 0x229b#64)
    (hx12 : s.readReg64 .x12 = 0x6833#64) (hx13 : s.readReg64 .x13 = 0xf9dd#64)
    (hx14 : s.readReg64 .x14 = 0xc0dd#64) (hx15 : s.readReg64 .x15 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx16 : s.readReg64 .x16 = 0xf301#64) (hx17 : s.readReg64 .x17 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx18 : s.readReg64 .x18 = 0x4ebf#64) (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = 0x47fa#64) (hx21 : s.readReg64 .x21 = sp + 9984#64)
    (hx27 : s.readReg64 .x27 = 0x0260#64) (hx28 : s.readReg64 .x28 = 0x2260#64)
    (hlr  : s.readReg64 .lr = 0xf9fa#64) :
    let prfPtr := sp + BitVec.ofNat 64 (27840 + 128 * idx)
    let polyAddr := sp + 17376#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC05.rebase b (fun _ => none))
      (if idx < 2 then b + off4afc else b + off5c60) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 9984#64) 512 ∗
        SpillSliceMem 16 (sp + 1952#64) t ∗ PolyMem polyAddr fDst ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x3 = sp + 27841#64 + BitVec.ofNat 64 (128 * (idx + 1)) ∧
        sf.readReg64 .x9 = sp + 17392#64 + BitVec.ofNat 64 (512 * (idx + 1)) ∧
        sf.readReg64 .x10 = 0x019b#64 ∧ sf.readReg64 .x11 = 0x229b#64 ∧
        sf.readReg64 .x12 = 0x6833#64 ∧ sf.readReg64 .x13 = 0xf9dd#64 ∧
        sf.readReg64 .x14 = 0xc0dd#64 ∧ sf.readReg64 .x15 = mlkemMpl.ρ ro00Sym + 66#64 ∧
        sf.readReg64 .x16 = 0xf301#64 ∧ sf.readReg64 .x17 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        sf.readReg64 .x18 = 0x4ebf#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = 0x47fa#64 ∧ sf.readReg64 .x21 = sp + 9984#64 ∧
        sf.readReg64 .x27 = 0x0260#64 ∧ sf.readReg64 .x28 = 0x2260#64 ∧
        sf.readReg64 .lr = 0xf9fa#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        ∃ t' : Spill40,
          (Pf ⊢ (prfPtr ↦ₛ prf) ∗ memRegion (sp + 9984#64) 512 ∗
            SpillSliceMem 16 (sp + 1952#64) t' ∗
            PolyMem polyAddr (polyVecNat (cbdNttPoly16 prf)) ∗ Rest)) := by
  dsimp only
  set prfPtr := sp + BitVec.ofNat 64 (27840 + 128 * idx)
  set polyAddr := sp + 17376#64 + BitVec.ofNat 64 (512 * idx)
  set cbd := neonCbd2Poly16 prf
  have hcbd : cbd.size = 256 := (neonCbd2Poly16_spec hprf).1.1
  have hx3' : s.readReg64 .x3 = prfPtr + 1#64 := by
    rw [hx3]; dsimp only [prfPtr]; clear * -; bv_omega
  refine SepWP.weaken_pre
    (show (prfPtr ↦ₛ prf) ∗ memRegion (sp + 9984#64) 512 ∗
        SpillSliceMem 16 (sp + 1952#64) t ∗ PolyMem polyAddr fDst ∗ Rest ⊢
      (prfPtr ↦ₛ prf) ∗ memRegion (sp + 9984#64) 512 ∗
        (SpillSliceMem 16 (sp + 1952#64) t ∗ PolyMem polyAddr fDst ∗ Rest) by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (eHat_cbd2_loop hb hbase s sp prfPtr prf
      (SpillSliceMem 16 (sp + 1952#64) t ∗ PolyMem polyAddr fDst ∗ Rest)
      hprf hpc hrun hsp hspA hx3' hx19 hx21) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, r0, r1, r3, r9, r10, r11, r12, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, r27, r28, rfp, rlr, rfl⟩
  have hx0_1 : s1.readReg64 .x0 = BitVec.ofNat 64 (idx + 1) := by
    rw [r0, hx1]; clear * -; bv_omega
  have hx1_1 : s1.readReg64 .x1 = BitVec.ofNat 64 idx := r1.trans hx1
  set envN := mkEHatNttEnv s1 polyAddr t fDst cbd
  set F_ntt := (prfPtr ↦ₛ prf) ∗ Rest
  have henv1 : envN.gpr0 1#5 = polyAddr := by simp [envN, mkEHatNttEnv]
  have hP1_sym : (prfPtr ↦ₛ prf) ∗ PolyMem (sp + 9984#64) (polyVecNat cbd) ∗
      (SpillSliceMem 16 (sp + 1952#64) t ∗ PolyMem polyAddr fDst ∗ Rest) ⊢
      SymSpatial05 (some 9984) cfgEHatNtt sp envN symEHatNttInit F_ntt := by
    have hptr : polyPtr cfgEHatNtt sp envN = polyAddr := henv1
    dsimp only [SymSpatial05, SymSpatial, SrcOptMem, F_ntt]
    rw [hptr, show cfgEHatNtt.spillLen = 16 from rfl, show cfgEHatNtt.spillOff = 1952 from rfl,
        spillSlice16_eHatNttInit sp t envN rfl, ← poly32Mem_ofFn polyAddr fDst,
        show SrcOptMem05 (some 9984) sp envN.src0 = PolyMem (sp + 9984#64) (polyVecNat cbd) from by
          dsimp only [SrcOptMem05, envN, mkEHatNttEnv]
          exact poly32Mem_ofFn (sp + 9984#64) (polyVecNat cbd)]
    dsimp only [cfgEHatNtt]; simp only [Bool.false_eq_true, ↓reduceIte]
    change (prfPtr ↦ₛ prf) ∗ PolyMem (sp + 9984#64) (polyVecNat cbd) ∗
        (SpillSliceMem 16 (sp + 1952#64) t ∗ PolyMem polyAddr fDst ∗ Rest) ⊢
      SpillSliceMem 16 (sp + 1952#64) t ∗ PolyMem polyAddr fDst ∗ emp ∗
        (PolyMem (sp + 9984#64) (polyVecNat cbd) ∗ ((prfPtr ↦ₛ prf) ∗ Rest))
    sep_frame
  refine SepWP.weaken_pre hP1_sym
    (sepWP_seq_env hcl1 hro1
      (sepWP_of_runSymRange05 (srcBase := some 9984) (cfg := cfgEHatNtt) (env := envN) (F := F_ntt)
        358 4875 noReloc_eHat_ntt_a (by decide) (by decide) (by decide)
        run_eHat_ntt_a
        (matches_eHatNttInit polyAddr t fDst cbd hsp1 hspA1
          (r10.trans hx10) (r11.trans hx11) (r12.trans hx12) (r13.trans hx13)
          (r14.trans hx14) (r16.trans hx16) (r18.trans hx18) (r20.trans hx20)
          (r27.trans hx27) (r28.trans hx28) (rlr.trans hlr))
        hpc1 hrun1
        (post := fun s2a P2a => SymStateMatches sp envN symEHatNttA s2a ∧
          P2a = SymSpatial05 (some 9984) cfgEHatNtt sp envN symEHatNttA F_ntt)
        (fun s2a _ _ hm2a => ⟨hm2a, rfl⟩)) ?_)
  rintro s2a P2a hpc2a hrun2a hcl2a hro2a ⟨hm2a, rfl⟩
  have hx8_2a : s2a.readReg64 .x8 = sp + 17376#64 := by
    have h := sym_gpr_at hm2a 8 (by decide); rw [symEHatNttA_gpr8] at h; exact h
  have hx1_2a : s2a.readReg64 .x1 = BitVec.ofNat 64 idx := by
    have h := sym_gpr_at hm2a 1 (by decide); rw [symEHatNttA_gpr1] at h
    rw [show s2a.readReg64 .x1 = s2a.readReg64 (.gpr 1#5) from rfl, h]
    simpa [evalSymGpr, envN, mkEHatNttEnv] using hx1_1
  refine sepWP_seq_env hcl2a hro2a
    (eHat_add_x1_x8 hb hbase s2a sp _ hpc2a hrun2a hm2a.hsp hm2a.hsp_al hx8_2a hx1_2a) ?_
  rintro s2b P2b hpc2b hrun2b hcl2b hro2b
    ⟨hsp2b, hspA2b, hpst2b, hvr2b, hx1_2b, hgpr2b, rfl⟩
  have hm2b : SymStateMatches sp envN symEHatNttA' s2b :=
    matches_nttA_to_A' hm2a henv1 hsp2b hspA2b hpst2b hvr2b hx1_2b hgpr2b
  have hP2b_sym : SymSpatial05 (some 9984) cfgEHatNtt sp envN symEHatNttA F_ntt ⊢
      SymSpatial05 (some 9984) cfgEHatNtt sp envN symEHatNttA' F_ntt := by
    dsimp only [SymSpatial05, SymSpatial, symEHatNttA']; exact Entails.refl _
  refine SepWP.weaken_pre hP2b_sym
    (sepWP_seq_env hcl2b hro2b
      (sepWP_of_runSymRange05 (srcBase := some 9984) (cfg := cfgEHatNtt) (env := envN) (F := F_ntt)
        452 5234 noReloc_eHat_ntt_b (by decide) (by decide) (by decide)
        run_eHat_ntt_b hm2b hpc2b hrun2b
        (post := fun s3 P3 => SymStateMatches sp envN symEHatNttEnd s3 ∧
          P3 = SymSpatial05 (some 9984) cfgEHatNtt sp envN symEHatNttEnd F_ntt)
        (fun s3 _ _ hm3 => ⟨hm3, rfl⟩)) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hm3, rfl⟩
  rcases symEHatNttEnd_gprs with ⟨ng0, ng1, ng2, ng3, ng4, ng8, ng9, ng10, ng11, ng12, ng13,
    ng14, ng15, ng16, ng17, ng18, ng19, ng20, ng21, _, ng27, ng28, ng29, ng30⟩
  have gpr3_eq : ∀ (k : Nat) (hk : k < 31),
      s3.readReg64 (.gpr (BitVec.ofNat 5 k)) = evalSymGpr sp envN.gpr0 (symEHatNttEnd.gprs.get k) :=
    fun k hk => sym_gpr_at hm3 k hk
  have hx0_3 : s3.readReg64 .x0 = BitVec.ofNat 64 (idx + 1) := by
    have h := gpr3_eq 0 (by decide); rw [ng0] at h
    simp only [evalSymGpr, envN, mkEHatNttEnv, BitVec.add_zero] at h; exact h.trans hx0_1
  have hx1_3 : s3.readReg64 .x1 = polyAddr := by
    have h := gpr3_eq 1 (by decide); rw [ng1] at h
    simpa [evalSymGpr, henv1] using h
  have hx2_3 : s3.readReg64 .x2 = polyAddr + 16#64 := by
    have h := gpr3_eq 2 (by decide); rw [ng2] at h
    have henv9 : envN.gpr0 9#5 = s1.readReg64 .x9 := rfl
    simp only [evalSymGpr, henv9, BitVec.add_zero] at h
    rw [show s3.readReg64 .x2 = s3.readReg64 (.gpr 2#5) from rfl, h, r9, hx9]
    dsimp only [polyAddr]; clear * -; bv_omega
  have hx3_3 : s3.readReg64 .x3 = prfPtr + 1#64 := by
    have h := gpr3_eq 3 (by decide); rw [ng3] at h
    simp only [evalSymGpr, envN, mkEHatNttEnv, BitVec.add_zero] at h; exact h.trans r3
  have hx4_3 : s3.readReg64 .x4 = 16#64 := by
    have h := gpr3_eq 4 (by decide); rw [ng4] at h; exact h
  have hx8_3 : s3.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64 := by
    have h := gpr3_eq 8 (by decide); rw [ng8] at h
    simp only [evalSymGpr, envN, mkEHatNttEnv, BitVec.add_zero] at h; exact h.trans (r15.trans hx15)
  have hx9_3 : s3.readReg64 .x9 = sp + 17392#64 + BitVec.ofNat 64 (512 * idx) := by
    have h := gpr3_eq 9 (by decide); rw [ng9] at h
    simp only [evalSymGpr, envN, mkEHatNttEnv, BitVec.add_zero] at h; exact h.trans (r9.trans hx9)
  have hx10_3 : s3.readReg64 .x10 = 0x019b#64 := by
    have h := gpr3_eq 10 (by decide); rw [ng10] at h; exact h
  have hx11_3 : s3.readReg64 .x11 = 0x229b#64 := by
    have h := gpr3_eq 11 (by decide); rw [ng11] at h; exact h
  have hx12_3 : s3.readReg64 .x12 = 0x6833#64 := by
    have h := gpr3_eq 12 (by decide); rw [ng12] at h; exact h
  have hx13_3 : s3.readReg64 .x13 = 0xf9dd#64 := by
    have h := gpr3_eq 13 (by decide); rw [ng13] at h; exact h
  have hx14_3 : s3.readReg64 .x14 = 0xc0dd#64 := by
    have h := gpr3_eq 14 (by decide); rw [ng14] at h; exact h
  have hx15_3 : s3.readReg64 .x15 = mlkemMpl.ρ ro00Sym + 66#64 := by
    have h := gpr3_eq 15 (by decide); rw [ng15] at h
    simp only [evalSymGpr, envN, mkEHatNttEnv, BitVec.add_zero] at h; exact h.trans (r15.trans hx15)
  have hx16_3 : s3.readReg64 .x16 = 0xf301#64 := by
    have h := gpr3_eq 16 (by decide); rw [ng16] at h; exact h
  have hx17_3 : s3.readReg64 .x17 = mlkemMpl.ρ ro00Sym + 134#64 := by
    have h := gpr3_eq 17 (by decide); rw [ng17] at h
    simp only [evalSymGpr, envN, mkEHatNttEnv, BitVec.add_zero] at h; exact h.trans (r17.trans hx17)
  have hx18_3 : s3.readReg64 .x18 = 0x4ebf#64 := by
    have h := gpr3_eq 18 (by decide); rw [ng18] at h; exact h
  have hx19_3 : s3.readReg64 .x19 = 0x55555555#64 := by
    have h := gpr3_eq 19 (by decide); rw [ng19] at h
    simp only [evalSymGpr, envN, mkEHatNttEnv, BitVec.add_zero] at h; exact h.trans r19
  have hx20_3 : s3.readReg64 .x20 = 0x47fa#64 := by
    have h := gpr3_eq 20 (by decide); rw [ng20] at h; exact h
  have hx21_3 : s3.readReg64 .x21 = sp + 9984#64 := by
    have h := gpr3_eq 21 (by decide); rw [ng21] at h
    simp only [evalSymGpr, envN, mkEHatNttEnv, BitVec.add_zero] at h; exact h.trans r21
  have hx27_3 : s3.readReg64 .x27 = 0x0260#64 := by
    have h := gpr3_eq 27 (by decide); rw [ng27] at h; exact h
  have hx28_3 : s3.readReg64 .x28 = 0x2260#64 := by
    have h := gpr3_eq 28 (by decide); rw [ng28] at h; exact h
  have hfp_3 : s3.readReg64 .fp = sp + 29984#64 := by
    have h := gpr3_eq 29 (by decide); rw [ng29] at h
    simp only [evalSymGpr, envN, mkEHatNttEnv, BitVec.add_zero] at h; exact h.trans (rfp.trans hfp)
  have hlr_3 : s3.readReg64 .lr = 0xf9fa#64 := by
    have h := gpr3_eq 30 (by decide); rw [ng30] at h; exact h
  have hv7_3 : s3.readVReg128 7#5 = dup8x16 3329#16 := by
    have h := hm3.hvregs 7#5; rw [show (7#5 : BitVec 5).toNat = 7 from rfl, symEHatNttEnd_vreg7] at h
    exact h
  set t1 := symEHatNttEnd.spill.eval envN
  set p3 := lowerNttBinomial5_16 cbd
  have hp3 : p3.size = 256 := (lowerNttBinomial5_16_size cbd).trans hcbd
  have hp3_mem : Poly32Mem (polyPtr cfgEHatNtt sp envN) (symEHatNttEnd.poly.eval envN) =
      PolyMem polyAddr (polyVecNat p3) := by
    have hptr : polyPtr cfgEHatNtt sp envN = polyAddr := henv1
    rw [hptr]
    exact poly_eq_lowerNttBinomial5_src polyAddr hcbd envN rfl symEHatNttEnd.poly
      eHat_ntt_noSpillVreg eHat_ntt_ast_eq
  have hsrc3 : SrcOptMem05 (some 9984) sp envN.src0 ⊢ memRegion (sp + 9984#64) 512 := by
    dsimp only [SrcOptMem05]
    exact poly32Mem_entails_memRegion (sp + 9984#64) envN.src0
  set F_low := memRegion (sp + 9984#64) 512 ∗ SpillSliceMem 16 (sp + 1952#64) t1 ∗ F_ntt
  have hP3_low : SymSpatial05 (some 9984) cfgEHatNtt sp envN symEHatNttEnd F_ntt ⊢
      PolyMem polyAddr (polyVecNat p3) ∗ F_low := by
    dsimp only [SymSpatial05, SymSpatial, SrcOptMem, F_low, t1]
    rw [hp3_mem]
    dsimp only [cfgEHatNtt]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact entails_sub hsrc3 (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP3_low
    (sepWP_seq_env hcl3 hro3
      (eHat_fwd_low_ok hb s3 sp polyAddr hp3 F_low
        hpc3 hrun3 hm3.hsp hm3.hsp_al hcl3 hro3 hx8_3 hx17_3 hx2_3 hx4_3 hx16_3
        (by rw [hx9_3]; dsimp only [polyAddr]; clear * -; bv_omega) hv7_3) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hpres4, _, _, rfl⟩
  set q := lowerFwdNtt16 p3
  have hq : q.size = 256 := (lowerFwdNtt16_size p3).trans hp3
  set envB := mkEHatBarEnv s4 q
  have hP4_bar : PolyMem polyAddr (polyVecNat q) ∗ F_low ⊢
      SymSpatial05 none cfgEHatBar sp envB symEHatBarInit F_low := by
    dsimp only [SymSpatial05, SymSpatial, cfgEHatBar, polyPtr, SrcOptMem, SrcOptMem05,
      SpillSliceMem, Encaps2.VecMem.VecRangeMem, envB, mkEHatBarEnv]
    rw [show s4.readReg64 (.gpr 1#5) = polyAddr from hpres4.x1.trans hx1_3,
        ← poly32Mem_ofFn polyAddr (polyVecNat q)]
    change Poly32Mem polyAddr _ ∗ F_low ⊢ emp ∗ Poly32Mem polyAddr _ ∗ emp ∗ (emp ∗ F_low)
    sep_frame
  refine SepWP.weaken_pre hP4_bar
    (sepWP_seq_env hcl4 hro4
      (sepWP_of_runSymRange05 (srcBase := none) (cfg := cfgEHatBar) (env := envB) (F := F_low)
        8 5744 noReloc_eHat_bar_a (by decide) (by decide) (by decide)
        run_eHat_bar_a
        (matches_eHatBarInit q hsp4 hspA4
          (hpres4.x10.trans hx10_3) (hpres4.x11.trans hx11_3) (hpres4.x12.trans hx12_3)
          (hpres4.x13.trans hx13_3) (hpres4.x14.trans hx14_3) (hpres4.x16.trans hx16_3)
          (hpres4.x18.trans hx18_3) (hpres4.x20.trans hx20_3) (hpres4.x27.trans hx27_3)
          (hpres4.x28.trans hx28_3) (hpres4.lr.trans hlr_3))
        hpc4 hrun4
        (post := fun s5 P5 => SymStateMatches sp envB symEHatBarMid s5 ∧
          P5 = SymSpatial05 none cfgEHatBar sp envB symEHatBarMid F_low)
        (fun s5 _ _ hm5 => ⟨hm5, rfl⟩)) ?_)
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hm5, rfl⟩
  have hx0_5 : s5.readReg64 .x0 = BitVec.ofNat 64 (idx + 1) := by
    have h := sym_gpr_at hm5 0 (by decide); rw [symEHatBarMid_gpr0] at h
    simp only [evalSymGpr, envB, mkEHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x0.trans hx0_3)
  refine sepWP_seq_env hcl5 hro5
    (eHat_cmp3 hb hbase s5 hidx _ hpc5 hrun5 hx0_5) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 hro6 ⟨hsp6, hspA6, hvregs6, hgpr6, hpz6, rfl⟩
  set envB' : SymEnv := { envB with pstate0 := s6.pstate }
  have hm6 : SymStateMatches sp envB' symEHatBarMid s6 := by
    refine ⟨hsp6.trans hm5.hsp, hspA6.trans hm5.hsp_al, rfl, fun r => ?_, fun r hr => ?_⟩
    · rw [State.readVReg128, hvregs6]
      exact (hm5.hvregs r).trans (evalSExpr_pstate0_irrel envB s6.pstate _).symm
    · exact (hgpr6 r hr).trans (hm5.hgprs r hr)
  have hP6_bar : SymSpatial05 none cfgEHatBar sp envB symEHatBarMid F_low ⊢
      SymSpatial05 none cfgEHatBar sp envB' symEHatBarMid F_low := by
    dsimp only [SymSpatial05, SymSpatial, cfgEHatBar, polyPtr, SrcOptMem, SrcOptMem05,
      SpillSliceMem, Encaps2.VecMem.VecRangeMem, envB']
    rw [symVec32_eval_pstate0_irrel envB s6.pstate symEHatBarMid.poly]
    exact Entails.refl _
  refine SepWP.weaken_pre hP6_bar
    (sepWP_seq_env hcl6 hro6
      (sepWP_of_runSymRange05 (srcBase := none) (cfg := cfgEHatBar) (env := envB') (F := F_low)
        157 5753 noReloc_eHat_bar_b (by decide) (by decide) (by decide)
        run_eHat_bar_b hm6 hpc6 hrun6
        (post := fun s7 P7 => SymStateMatches sp envB' symEHatBarEnd s7 ∧
          P7 = SymSpatial05 none cfgEHatBar sp envB' symEHatBarEnd F_low)
        (fun s7 _ _ hm7 => ⟨hm7, rfl⟩)) ?_)
  rintro s7 P7 hpc7 hrun7 hcl7 hro7 ⟨hm7, rfl⟩
  rcases symEHatBarEnd_gprs with ⟨bg0, _, bg3, bg9, bg10, bg11, bg12, bg13, bg14, bg15,
    bg16, bg17, bg18, bg19, bg20, bg21, _, bg27, bg28, bg29, bg30⟩
  have gpr7_eq : ∀ (k : Nat) (hk : k < 31),
      s7.readReg64 (.gpr (BitVec.ofNat 5 k)) = evalSymGpr sp envB.gpr0 (symEHatBarEnd.gprs.get k) :=
    fun k hk => sym_gpr_at hm7 k hk
  have hx0_7 : s7.readReg64 .x0 = BitVec.ofNat 64 (idx + 1) := by
    have h := gpr7_eq 0 (by decide); rw [bg0] at h
    simp only [evalSymGpr, envB, mkEHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x0.trans hx0_3)
  have hpz7 : s7.pstate.z = decide (idx = 2) := hm7.hpstate ▸ hpz6
  have hp7_mem : Poly32Mem (polyPtr cfgEHatBar sp envB') (symEHatBarEnd.poly.eval envB') =
      PolyMem polyAddr (polyVecNat (cbdNttPoly16 prf)) := by
    have hptr : polyPtr cfgEHatBar sp envB' = polyAddr := hpres4.x1.trans hx1_3
    have hbar_eq : (lowerFwdNtt16 (lowerNttBinomial5_16 cbd)).map neonBarrettReduce16 =
        neonPolyNttBinomial16 cbd := barrett_lowerFwdNtt16_upperBinomial cbd
    rw [hptr, poly_eq_barrett polyAddr hq envB' rfl symEHatBarEnd.poly
      eHat_bar_noSpillVreg eHat_bar_ast_eq]
    dsimp only [q, p3]
    rw [hbar_eq]
    rfl
  have hP7 : SymSpatial05 none cfgEHatBar sp envB' symEHatBarEnd F_low ⊢
      (prfPtr ↦ₛ prf) ∗ memRegion (sp + 9984#64) 512 ∗
        SpillSliceMem 16 (sp + 1952#64) t1 ∗
        PolyMem polyAddr (polyVecNat (cbdNttPoly16 prf)) ∗ Rest := by
    dsimp only [SymSpatial05, SymSpatial, SrcOptMem, SrcOptMem05, F_low, F_ntt]
    rw [hp7_mem]
    dsimp only [cfgEHatBar, SpillSliceMem, Encaps2.VecMem.VecRangeMem]
    change emp ∗ PolyMem polyAddr (polyVecNat (cbdNttPoly16 prf)) ∗
        (if false = true then _ else emp) ∗
        (emp ∗ (memRegion (sp + 9984#64) 512 ∗
          Encaps2.VecMem.VecRangeMem 16 (sp + 1952#64) (fun i => t1.get i) ∗
          ((prfPtr ↦ₛ prf) ∗ Rest))) ⊢
      (prfPtr ↦ₛ prf) ∗ memRegion (sp + 9984#64) 512 ∗
        Encaps2.VecMem.VecRangeMem 16 (sp + 1952#64) (fun i => t1.get i) ∗
        PolyMem polyAddr (polyVecNat (cbdNttPoly16 prf)) ∗ Rest
    simp only [Bool.false_eq_true, ↓reduceIte]; sep_frame
  refine SepWP.weaken_pre hP7
    (sepWP_seq_env hcl7 hro7 (eHat_loop_tail hb hbase s7 hidx _ hpc7 hrun7 hx0_7 hpz7) ?_)
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, _, hx1f, hgprf, rfl⟩
  have hfp_f : sf.readReg64 .fp = sp + 29984#64 := by
    rw [show sf.readReg64 .fp = sf.readReg64 (.gpr 29#5) from rfl, hgprf 29#5 (by decide) (by decide)]
    have h := gpr7_eq 29 (by decide); rw [bg29] at h
    simp only [evalSymGpr, envB, mkEHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.fp.trans hfp_3)
  have hx3_f : sf.readReg64 .x3 = sp + 27841#64 + BitVec.ofNat 64 (128 * (idx + 1)) := by
    rw [show sf.readReg64 .x3 = sf.readReg64 (.gpr 3#5) from rfl, hgprf 3#5 (by decide) (by decide)]
    have h := gpr7_eq 3 (by decide); rw [bg3] at h
    simp only [evalSymGpr, envB, mkEHatBarEnv] at h
    rw [h, show s4.readReg64 (.gpr 3#5) = s4.readReg64 .x3 from rfl, hpres4.x3, hx3_3]
    dsimp only [prfPtr]; clear * - hidx; bv_omega
  have hx9_f : sf.readReg64 .x9 = sp + 17392#64 + BitVec.ofNat 64 (512 * (idx + 1)) := by
    rw [show sf.readReg64 .x9 = sf.readReg64 (.gpr 9#5) from rfl, hgprf 9#5 (by decide) (by decide)]
    have h := gpr7_eq 9 (by decide); rw [bg9] at h
    simp only [evalSymGpr, envB, mkEHatBarEnv] at h
    rw [h, show s4.readReg64 (.gpr 9#5) = s4.readReg64 .x9 from rfl, hpres4.x9, hx9_3]
    clear * - hidx; bv_omega
  have hx10_f : sf.readReg64 .x10 = 0x019b#64 := by
    rw [show sf.readReg64 .x10 = sf.readReg64 (.gpr 10#5) from rfl, hgprf 10#5 (by decide) (by decide)]
    have h := gpr7_eq 10 (by decide); rw [bg10] at h; exact h
  have hx11_f : sf.readReg64 .x11 = 0x229b#64 := by
    rw [show sf.readReg64 .x11 = sf.readReg64 (.gpr 11#5) from rfl, hgprf 11#5 (by decide) (by decide)]
    have h := gpr7_eq 11 (by decide); rw [bg11] at h; exact h
  have hx12_f : sf.readReg64 .x12 = 0x6833#64 := by
    rw [show sf.readReg64 .x12 = sf.readReg64 (.gpr 12#5) from rfl, hgprf 12#5 (by decide) (by decide)]
    have h := gpr7_eq 12 (by decide); rw [bg12] at h; exact h
  have hx13_f : sf.readReg64 .x13 = 0xf9dd#64 := by
    rw [show sf.readReg64 .x13 = sf.readReg64 (.gpr 13#5) from rfl, hgprf 13#5 (by decide) (by decide)]
    have h := gpr7_eq 13 (by decide); rw [bg13] at h; exact h
  have hx14_f : sf.readReg64 .x14 = 0xc0dd#64 := by
    rw [show sf.readReg64 .x14 = sf.readReg64 (.gpr 14#5) from rfl, hgprf 14#5 (by decide) (by decide)]
    have h := gpr7_eq 14 (by decide); rw [bg14] at h; exact h
  have hx15_f : sf.readReg64 .x15 = mlkemMpl.ρ ro00Sym + 66#64 := by
    rw [show sf.readReg64 .x15 = sf.readReg64 (.gpr 15#5) from rfl, hgprf 15#5 (by decide) (by decide)]
    have h := gpr7_eq 15 (by decide); rw [bg15] at h
    simp only [evalSymGpr, envB, mkEHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x15.trans hx15_3)
  have hx16_f : sf.readReg64 .x16 = 0xf301#64 := by
    rw [show sf.readReg64 .x16 = sf.readReg64 (.gpr 16#5) from rfl, hgprf 16#5 (by decide) (by decide)]
    have h := gpr7_eq 16 (by decide); rw [bg16] at h; exact h
  have hx17_f : sf.readReg64 .x17 = mlkemMpl.ρ ro00Sym + 134#64 := by
    rw [show sf.readReg64 .x17 = sf.readReg64 (.gpr 17#5) from rfl, hgprf 17#5 (by decide) (by decide)]
    have h := gpr7_eq 17 (by decide); rw [bg17] at h
    simp only [evalSymGpr, envB, mkEHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x17.trans hx17_3)
  have hx18_f : sf.readReg64 .x18 = 0x4ebf#64 := by
    rw [show sf.readReg64 .x18 = sf.readReg64 (.gpr 18#5) from rfl, hgprf 18#5 (by decide) (by decide)]
    have h := gpr7_eq 18 (by decide); rw [bg18] at h; exact h
  have hx19_f : sf.readReg64 .x19 = 0x55555555#64 := by
    rw [show sf.readReg64 .x19 = sf.readReg64 (.gpr 19#5) from rfl, hgprf 19#5 (by decide) (by decide)]
    have h := gpr7_eq 19 (by decide); rw [bg19] at h
    simp only [evalSymGpr, envB, mkEHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x19.trans hx19_3)
  have hx20_f : sf.readReg64 .x20 = 0x47fa#64 := by
    rw [show sf.readReg64 .x20 = sf.readReg64 (.gpr 20#5) from rfl, hgprf 20#5 (by decide) (by decide)]
    have h := gpr7_eq 20 (by decide); rw [bg20] at h; exact h
  have hx21_f : sf.readReg64 .x21 = sp + 9984#64 := by
    rw [show sf.readReg64 .x21 = sf.readReg64 (.gpr 21#5) from rfl, hgprf 21#5 (by decide) (by decide)]
    have h := gpr7_eq 21 (by decide); rw [bg21] at h
    simp only [evalSymGpr, envB, mkEHatBarEnv, BitVec.add_zero] at h
    exact h.trans (hpres4.x21.trans hx21_3)
  have hx27_f : sf.readReg64 .x27 = 0x0260#64 := by
    rw [show sf.readReg64 .x27 = sf.readReg64 (.gpr 27#5) from rfl, hgprf 27#5 (by decide) (by decide)]
    have h := gpr7_eq 27 (by decide); rw [bg27] at h; exact h
  have hx28_f : sf.readReg64 .x28 = 0x2260#64 := by
    rw [show sf.readReg64 .x28 = sf.readReg64 (.gpr 28#5) from rfl, hgprf 28#5 (by decide) (by decide)]
    have h := gpr7_eq 28 (by decide); rw [bg28] at h; exact h
  have hlr_f : sf.readReg64 .lr = 0xf9fa#64 := by
    rw [show sf.readReg64 .lr = sf.readReg64 (.gpr 30#5) from rfl, hgprf 30#5 (by decide) (by decide)]
    have h := gpr7_eq 30 (by decide); rw [bg30] at h; exact h
  refine SepWP.done hpcf hrunf
    ⟨hspf.trans hm7.hsp, hspAf.trans hm7.hsp_al, hfp_f, hx1f, hx3_f, hx9_f,
      hx10_f, hx11_f, hx12_f, hx13_f, hx14_f, hx15_f, hx16_f, hx17_f, hx18_f,
      hx19_f, hx20_f, hx21_f, hx27_f, hx28_f, hlr_f, hclf, hrof,
      t1, Entails.refl _⟩

/-! ## 3. Full 3-Iteration `eHat` Loop & Segment 3b (`+0x48cc → +0x5c60`) -/

/-- `eHat[0..2]` stored at `[sp + 17376, sp + 18912)` (`3 × 512` B). -/
@[expose] def EHatMem (sp : BitVec 64) (sigma : List (BitVec 8)) : SepProp :=
  PolyMem (sp + 17376#64) (polyVecNat (cbdNttPoly16 (shake256List 128 (sigma ++ [3#8])))) ∗
  PolyMem (sp + 17888#64) (polyVecNat (cbdNttPoly16 (shake256List 128 (sigma ++ [4#8])))) ∗
  PolyMem (sp + 18400#64) (polyVecNat (cbdNttPoly16 (shake256List 128 (sigma ++ [5#8]))))

private theorem eHat_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (sigma : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + off4afc) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx1 : s.readReg64 .x1 = 0#64) (hx3 : s.readReg64 .x3 = sp + 27841#64)
    (hx9 : s.readReg64 .x9 = sp + 17392#64) (hx10 : s.readReg64 .x10 = 0x019b#64)
    (hx11 : s.readReg64 .x11 = 0x229b#64) (hx12 : s.readReg64 .x12 = 0x6833#64)
    (hx13 : s.readReg64 .x13 = 0xf9dd#64) (hx14 : s.readReg64 .x14 = 0xc0dd#64)
    (hx15 : s.readReg64 .x15 = mlkemMpl.ρ ro00Sym + 66#64) (hx16 : s.readReg64 .x16 = 0xf301#64)
    (hx17 : s.readReg64 .x17 = mlkemMpl.ρ ro00Sym + 134#64) (hx18 : s.readReg64 .x18 = 0x4ebf#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64) (hx20 : s.readReg64 .x20 = 0x47fa#64)
    (hx21 : s.readReg64 .x21 = sp + 9984#64)
    (hx27 : s.readReg64 .x27 = 0x0260#64) (hx28 : s.readReg64 .x28 = 0x2260#64)
    (hlr  : s.readReg64 .lr = 0xf9fa#64) :
    let prf3 := shake256List 128 (sigma ++ [3#8])
    let prf4 := shake256List 128 (sigma ++ [4#8])
    let prf5 := shake256List 128 (sigma ++ [5#8])
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off5c60) s
      (((sp + 27840#64) ↦ₛ prf3) ∗ ((sp + 27968#64) ↦ₛ prf4) ∗ ((sp + 28096#64) ↦ₛ prf5) ∗
       memRegion (sp + 1952#64) 256 ∗ memRegion (sp + 9984#64) 512 ∗
       memRegion (sp + 17376#64) 1536 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ EHatMem sp sigma ∗ memRegion (sp + 1952#64) 256 ∗
          memRegion (sp + 9984#64) 512 ∗ memRegion (sp + 27840#64) 384 ∗ Rest)) := by
  dsimp only
  set prf3 := shake256List 128 (sigma ++ [3#8])
  set prf4 := shake256List 128 (sigma ++ [4#8])
  set prf5 := shake256List 128 (sigma ++ [5#8])
  have hp3 : prf3.length = 128 := shake256List_length 128 _
  have hp4 : prf4.length = 128 := shake256List_length 128 _
  have hp5 : prf5.length = 128 := shake256List_length 128 _
  rw [memRegion_split' (b := sp + 17376#64) (b' := sp + 17888#64) (n := 512) (k := (1024 : Nat))
        rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 17888#64) (b' := sp + 18400#64) (n := 512) (k := (512 : Nat))
        rfl (by clear * -; bv_omega) (by decide)]
  apply SepWP.of_memRegion_vecRangeMem 16 (sp + 1952#64) (by decide) (by sep_focus); intro fs
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 17376#64) (by decide) (by sep_focus); intro fd0
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 17888#64) (by decide) (by sep_focus); intro fd1
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 18400#64) (by decide) (by sep_focus); intro fd2
  set t0 : Spill40 := Spill40.ofFn fs
  have ht0_mem : VecRangeMem 16 (sp + 1952#64) fs = SpillSliceMem 16 (sp + 1952#64) t0 :=
    vecRangeMem_congr fun i hi => (spill40_ofFn_get fs i (by omega)).symm
  change SepWP _ _ _ (PolyMem (sp + 18400#64) fd2 ∗
    (PolyMem (sp + 17888#64) fd1 ∗ (PolyMem (sp + 17376#64) fd0 ∗
      (VecRangeMem 16 (sp + 1952#64) fs ∗ _)))) _
  rw [ht0_mem]
  -- idx = 0
  refine SepWP.weaken_pre
    (P' := ((sp + BitVec.ofNat 64 (27840 + 128 * 0)) ↦ₛ prf3) ∗ memRegion (sp + 9984#64) 512 ∗
      SpillSliceMem 16 (sp + 1952#64) t0 ∗ PolyMem (sp + 17376#64 + BitVec.ofNat 64 (512 * 0)) fd0 ∗
      (((sp + 27968#64) ↦ₛ prf4) ∗ ((sp + 28096#64) ↦ₛ prf5) ∗
        PolyMem (sp + 17888#64) fd1 ∗ PolyMem (sp + 18400#64) fd2 ∗ Rest))
    (by simp only [Nat.mul_zero, Nat.add_zero, BitVec.add_zero]; sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (eHat_iter hb hbase s sp (idx := 0) (by decide) prf3 hp3 t0 fd0 _
      hpc hrun hsp hspA hcl hro hfp hx1 (by simpa using hx3) (by simpa using hx9)
      hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx20 hx21 hx27 hx28 hlr) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, r1_1, r3_1, r9_1, r10_1, r11_1, r12_1, r13_1, r14_1, r15_1,
     r16_1, r17_1, r18_1, r19_1, r20_1, r21_1, r27_1, r28_1, rlr_1, _, _, t1, hP1⟩
  simp only [show (0 : Nat) < 2 from by decide, ite_true] at hpc1
  refine SepWP.weaken_pre hP1 ?_
  -- idx = 1
  refine SepWP.weaken_pre
    (P' := ((sp + BitVec.ofNat 64 (27840 + 128 * 1)) ↦ₛ prf4) ∗ memRegion (sp + 9984#64) 512 ∗
      SpillSliceMem 16 (sp + 1952#64) t1 ∗ PolyMem (sp + 17376#64 + BitVec.ofNat 64 (512 * 1)) fd1 ∗
      (((sp + 27840#64) ↦ₛ prf3) ∗ ((sp + 28096#64) ↦ₛ prf5) ∗
        PolyMem (sp + 17376#64) (polyVecNat (cbdNttPoly16 prf3)) ∗
        PolyMem (sp + 18400#64) fd2 ∗ Rest))
    (by simp only [Nat.mul_zero, Nat.add_zero, BitVec.add_zero,
          show sp + 17376#64 + BitVec.ofNat 64 (512 * 1) = sp + 17888#64 by clear * -; bv_omega,
          show sp + BitVec.ofNat 64 (27840 + 128 * 1) = sp + 27968#64 from rfl]; sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (eHat_iter hb hbase s1 sp (idx := 1) (by decide) prf4 hp4 t1 fd1 _
      hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hfp1 r1_1 r3_1 r9_1
      r10_1 r11_1 r12_1 r13_1 r14_1 r15_1 r16_1 r17_1 r18_1 r19_1 r20_1 r21_1 r27_1 r28_1 rlr_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hfp2, r1_2, r3_2, r9_2, r10_2, r11_2, r12_2, r13_2, r14_2, r15_2,
     r16_2, r17_2, r18_2, r19_2, r20_2, r21_2, r27_2, r28_2, rlr_2, _, _, t2, hP2⟩
  simp only [show (1 : Nat) < 2 from by decide, ite_true] at hpc2
  refine SepWP.weaken_pre hP2 ?_
  -- idx = 2
  refine SepWP.weaken_pre
    (P' := ((sp + BitVec.ofNat 64 (27840 + 128 * 2)) ↦ₛ prf5) ∗ memRegion (sp + 9984#64) 512 ∗
      SpillSliceMem 16 (sp + 1952#64) t2 ∗ PolyMem (sp + 17376#64 + BitVec.ofNat 64 (512 * 2)) fd2 ∗
      (((sp + 27840#64) ↦ₛ prf3) ∗ ((sp + 27968#64) ↦ₛ prf4) ∗
        PolyMem (sp + 17376#64) (polyVecNat (cbdNttPoly16 prf3)) ∗
        PolyMem (sp + 17888#64) (polyVecNat (cbdNttPoly16 prf4)) ∗ Rest))
    (by simp only [show sp + 17376#64 + BitVec.ofNat 64 (512 * 1) = sp + 17888#64 by clear * -; bv_omega,
          show sp + 17376#64 + BitVec.ofNat 64 (512 * 2) = sp + 18400#64 by clear * -; bv_omega,
          show sp + BitVec.ofNat 64 (27840 + 128 * 1) = sp + 27968#64 from rfl,
          show sp + BitVec.ofNat 64 (27840 + 128 * 2) = sp + 28096#64 from rfl]; sep_frame) ?_
  refine sepWP_seq_env hcl2 hro2
    (eHat_iter hb hbase s2 sp (idx := 2) (by decide) prf5 hp5 t2 fd2 _
      hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hfp2 r1_2 r3_2 r9_2
      r10_2 r11_2 r12_2 r13_2 r14_2 r15_2 r16_2 r17_2 r18_2 r19_2 r20_2 r21_2 r27_2 r28_2 rlr_2) ?_
  rintro sf Pf hpcf hrunf _ _
    ⟨hspf, hspAf, hfpf, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hclf, hrof, t3, hPf⟩
  simp only [show ¬ ((2 : Nat) < 2) from by decide, ite_false] at hpcf
  refine SepWP.done hpcf hrunf ⟨hspf, hspAf, hfpf, hclf, hrof, ?_⟩
  refine Entails.trans hPf ?_
  have hs3 : SpillSliceMem 16 (sp + 1952#64) t3 ⊢ memRegion (sp + 1952#64) 256 :=
    vecRangeMem_entails_memRegion 16 (sp + 1952#64) _
  have hm3 : ((sp + 27840#64) ↦ₛ prf3) ⊢ memRegion (sp + 27840#64) 128 := by
    simpa [hp3] using pointsToBytes_entails_memRegion (sp + 27840#64) prf3
  have hm4 : ((sp + 27968#64) ↦ₛ prf4) ⊢ memRegion (sp + 27968#64) 128 := by
    simpa [hp4] using pointsToBytes_entails_memRegion (sp + 27968#64) prf4
  have hm5 : ((sp + 28096#64) ↦ₛ prf5) ⊢ memRegion (sp + 28096#64) 128 := by
    simpa [hp5] using pointsToBytes_entails_memRegion (sp + 28096#64) prf5
  rw [memRegion_split' (b := sp + 27840#64) (b' := sp + 27968#64) (n := 128) (k := (256 : Nat))
        rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 27968#64) (b' := sp + 28096#64) (n := 128) (k := (128 : Nat))
        rfl (by clear * -; bv_omega) (by decide)]
  unfold EHatMem
  simp only [show sp + 17376#64 + BitVec.ofNat 64 (512 * 2) = sp + 18400#64 by clear * -; bv_omega,
    show sp + BitVec.ofNat 64 (27840 + 128 * 2) = sp + 28096#64 from rfl]
  exact entails_sub hs3 (by sep_frame)
    (entails_sub hm3 (by sep_frame)
      (entails_sub hm4 (by sep_frame) (entails_sub hm5 (by sep_frame) (by sep_frame))))

theorem seg3_eHat_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (sigma : List (BitVec 8)) (Rest : SepProp)
    (hsig : sigma.length = 32)
    (hpc : s.pc = b + off48cc) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off5c60) s
      (((sp + 29440#64) ↦ₛ sigma) ∗
       memRegion (sp + 1952#64) 256 ∗
       memRegion (sp + 9984#64) 512 ∗
       memRegion (sp + 17376#64) 1536 ∗
       memRegion (sp + 27840#64) 384 ∗
       memRegion (sp + 29024#64) 128 ∗
       memRegion (sp + 29504#64) 99 ∗
       memRegion (sp + 29616#64) 128 ∗
       memRegion (sp + 29744#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ ((sp + 29440#64) ↦ₛ sigma) ∗ EHatMem sp sigma ∗
          memRegion (sp + 1952#64) 256 ∗ memRegion (sp + 9984#64) 512 ∗
          memRegion (sp + 27840#64) 384 ∗ memRegion (sp + 29024#64) 128 ∗
          memRegion (sp + 29504#64) 99 ∗ memRegion (sp + 29616#64) 128 ∗
          memRegion (sp + 29744#64) 128 ∗ stackAt sp 1136 ∗ Rest)) := by
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 17376#64) 1536 ∗
      (((sp + 29440#64) ↦ₛ sigma) ∗ memRegion (sp + 1952#64) 256 ∗
        memRegion (sp + 9984#64) 512 ∗ memRegion (sp + 27840#64) 384 ∗
        memRegion (sp + 29024#64) 128 ∗ memRegion (sp + 29504#64) 99 ∗
        memRegion (sp + 29616#64) 128 ∗ memRegion (sp + 29744#64) 128 ∗
        stackAt sp 1136 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (eHat_memset hb hbase s sp _ hpc hrun hsp hspA hfp hx19 hcl) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, hx23_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have h512 : memRegion (sp + 9984#64) 512 =
      memRegion (sp + 9984#64) 128 ∗ memRegion (sp + 10112#64) 384 :=
    memRegion_split' (b := sp + 9984#64) (b' := sp + 10112#64) (n := 128) (k := (384 : Nat))
      rfl (by bv_omega) (by decide)
  have h384 : memRegion (sp + 27840#64) 384 =
      memRegion (sp + 27840#64) 32 ∗ memRegion (sp + 27872#64) 352 :=
    memRegion_split' (b := sp + 27840#64) (b' := sp + 27872#64) (n := 32) (k := (352 : Nat))
      rfl (by bv_omega) (by decide)
  rw [h512, h384]
  refine SepWP.weaken_pre
    (P' := ((sp + 29440#64) ↦ₛ sigma) ∗ memRegion (sp + 9984#64) 128 ∗
      memRegion (sp + 27840#64) 32 ∗ memRegion (sp + 29024#64) 128 ∗
      memRegion (sp + 29504#64) 99 ∗ memRegion (sp + 29616#64) 128 ∗
      memRegion (sp + 29744#64) 128 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 1952#64) 256 ∗ memRegion (sp + 10112#64) 384 ∗
        memRegion (sp + 17376#64) 1536 ∗ memRegion (sp + 27872#64) 352 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (eHat_prf_calls hb hbase s1 sp sigma _ hsig hpc1 hrun1 hsp1 hspA1 hfp1 hx19_1 hx23_1 hcl1 hro1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx19_2, hx20_2, hx21_2, hx23_2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  rw [← h512, ← h384]
  set prf3 := shake256List 128 (sigma ++ [3#8])
  set prf4 := shake256List 128 (sigma ++ [4#8])
  set prf5 := shake256List 128 (sigma ++ [5#8])
  refine SepWP.weaken_pre
    (P' := ((sp + 29616#64) ↦ₛ prf3) ∗ ((sp + 29744#64) ↦ₛ prf4) ∗ ((sp + 29024#64) ↦ₛ prf5) ∗
      memRegion (sp + 27840#64) 384 ∗
      (((sp + 29440#64) ↦ₛ sigma) ∗ memRegion (sp + 1952#64) 256 ∗
        memRegion (sp + 9984#64) 512 ∗ memRegion (sp + 17376#64) 1536 ∗
        memRegion (sp + 29504#64) 99 ∗ stackAt sp 1136 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl2 hro2
    (eHat_copy_regs hb hbase s2 sp prf3 prf4 prf5 _
      (shake256List_length 128 _) (shake256List_length 128 _) (shake256List_length 128 _)
      hpc2 hrun2 hsp2 hspA2 hfp2 hx19_2 hx20_2 hx21_2 hx23_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp3, r1, r3, r9, r10, r11, r12, r13, r14, r15,
     r16, r17, r18, r19, r20, r21, _, r27, r28, rlr, hP3⟩
  refine SepWP.weaken_pre hP3 ?_
  refine SepWP.weaken_pre
    (P' := ((sp + 27840#64) ↦ₛ prf3) ∗ ((sp + 27968#64) ↦ₛ prf4) ∗ ((sp + 28096#64) ↦ₛ prf5) ∗
      memRegion (sp + 1952#64) 256 ∗ memRegion (sp + 9984#64) 512 ∗
      memRegion (sp + 17376#64) 1536 ∗
      (((sp + 29440#64) ↦ₛ sigma) ∗ memRegion (sp + 29024#64) 128 ∗
        memRegion (sp + 29504#64) 99 ∗ memRegion (sp + 29616#64) 128 ∗
        memRegion (sp + 29744#64) 128 ∗ stackAt sp 1136 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl3 hro3
    (eHat_loop hb hbase s3 sp sigma _
      hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hfp3 r1 r3 r9
      r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r27 r28 rlr) ?_
  rintro sf Pf hpcf hrunf _ _ ⟨hspf, hspAf, hfpf, hclf, hrof, hPf⟩
  exact SepWP.done hpcf hrunf ⟨hspf, hspAf, hfpf, hclf, hrof, Entails.trans hPf (by sep_frame)⟩

/-! ## 4. Full Segment 3 Composition (`+0x3480 → +0x5c60`) -/

private theorem split_3600_seg3 (sp : BitVec 64) :
    memRegion (sp + 144#64) 3600 =
      memRegion (sp + 144#64) 1424 ∗ memRegion (sp + 1568#64) 640 ∗ memRegion (sp + 2208#64) 1536 := by
  rw [memRegion_split' (b := sp + 144#64) (b' := sp + 1568#64) (n := 1424) (k := (2176 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 1568#64) (b' := sp + 2208#64) (n := 640) (k := (1536 : Nat))
        rfl (by bv_omega) (by decide), ← sepConj_assoc]

private theorem split_640_seg3 (sp : BitVec 64) :
    memRegion (sp + 1568#64) 640 =
      memRegion (sp + 1568#64) 384 ∗ memRegion (sp + 1952#64) 256 :=
  memRegion_split' (b := sp + 1568#64) (b' := sp + 1952#64) (n := 384) (k := (256 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_21056_seg3 (sp : BitVec 64) :
    memRegion (sp + 8352#64) 21056 =
      memRegion (sp + 8352#64) 64 ∗
      memRegion (sp + 8416#64) 1536 ∗
      memRegion (sp + 9952#64) 32 ∗
      memRegion (sp + 9984#64) 384 ∗
      memRegion (sp + 10368#64) 128 ∗
      memRegion (sp + 10496#64) 6880 ∗
      memRegion (sp + 17376#64) 512 ∗
      memRegion (sp + 17888#64) 1024 ∗
      memRegion (sp + 18912#64) 8928 ∗
      memRegion (sp + 27840#64) 128 ∗
      memRegion (sp + 27968#64) 256 ∗
      memRegion (sp + 28224#64) 800 ∗
      memRegion (sp + 29024#64) 128 ∗
      memRegion (sp + 29152#64) 256 := by
  rw [memRegion_split' (b := sp + 8352#64) (b' := sp + 8416#64) (n := 64) (k := (20992 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 8416#64) (b' := sp + 9952#64) (n := 1536) (k := (19456 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 9952#64) (b' := sp + 9984#64) (n := 32) (k := (19424 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 9984#64) (b' := sp + 10368#64) (n := 384) (k := (19040 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 10368#64) (b' := sp + 10496#64) (n := 128) (k := (18912 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 10496#64) (b' := sp + 17376#64) (n := 6880) (k := (12032 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 17376#64) (b' := sp + 17888#64) (n := 512) (k := (11520 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 17888#64) (b' := sp + 18912#64) (n := 1024) (k := (10496 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 18912#64) (b' := sp + 27840#64) (n := 8928) (k := (1568 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 27840#64) (b' := sp + 27968#64) (n := 128) (k := (1440 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 27968#64) (b' := sp + 28224#64) (n := 256) (k := (1184 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 28224#64) (b' := sp + 29024#64) (n := 800) (k := (384 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 29024#64) (b' := sp + 29152#64) (n := 128) (k := (256 : Nat))
        rfl (by bv_omega) (by decide)]

private theorem split_480_seg3 (sp : BitVec 64) :
    memRegion (sp + 29440#64) 480 =
      memRegion (sp + 29440#64) 32 ∗
      memRegion (sp + 29472#64) 32 ∗
      memRegion (sp + 29504#64) 99 ∗
      memRegion (sp + 29603#64) 13 ∗
      memRegion (sp + 29616#64) 99 ∗
      memRegion (sp + 29715#64) 29 ∗
      memRegion (sp + 29744#64) 128 ∗
      memRegion (sp + 29872#64) 48 := by
  rw [memRegion_split' (b := sp + 29440#64) (b' := sp + 29472#64) (n := 32) (k := (448 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 29472#64) (b' := sp + 29504#64) (n := 32) (k := (416 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 29504#64) (b' := sp + 29603#64) (n := 99) (k := (317 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 29603#64) (b' := sp + 29616#64) (n := 13) (k := (304 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 29616#64) (b' := sp + 29715#64) (n := 99) (k := (205 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 29715#64) (b' := sp + 29744#64) (n := 29) (k := (176 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 29744#64) (b' := sp + 29872#64) (n := 128) (k := (48 : Nat))
        rfl (by bv_omega) (by decide)]

private theorem join_7424_seg3 (sp : BitVec 64) :
    memRegion (sp + 9952#64) 7424 =
      memRegion (sp + 9952#64) 32 ∗ memRegion (sp + 9984#64) 512 ∗ memRegion (sp + 10496#64) 6880 := by
  rw [memRegion_split' (b := sp + 9952#64) (b' := sp + 9984#64) (n := 32) (k := (7392 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 9984#64) (b' := sp + 10496#64) (n := 512) (k := (6880 : Nat))
        rfl (by bv_omega) (by decide), ← sepConj_assoc]

private theorem join_10496_seg3 (sp : BitVec 64) :
    memRegion (sp + 18912#64) 10496 =
      memRegion (sp + 18912#64) 8928 ∗ memRegion (sp + 27840#64) 384 ∗
      memRegion (sp + 28224#64) 800 ∗ memRegion (sp + 29024#64) 128 ∗
      memRegion (sp + 29152#64) 256 := by
  rw [memRegion_split' (b := sp + 18912#64) (b' := sp + 27840#64) (n := 8928) (k := (1568 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 27840#64) (b' := sp + 28224#64) (n := 384) (k := (1184 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 28224#64) (b' := sp + 29024#64) (n := 800) (k := (384 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 29024#64) (b' := sp + 29152#64) (n := 128) (k := (256 : Nat))
        rfl (by bv_omega) (by decide)]

/-- Postcondition entering Segment 4 (`+0x5c60`, `b + off5c60`). -/
@[expose] def Seg3Exit [MlKemPlacement]
    (b : BitVec 64) (s0 : State) (seedA outPtr : BitVec 64)
    (seed : List (BitVec 8)) (F : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  let sp := s0.sp - 30080#64
  let g := sha3_512List (seed.take 32 ++ [3#8])
  sf.pc = b + off5c60 ∧
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
    memRegion (sp + 144#64) 3600 ∗
    AMatrixMem sp (g.take 32) ∗
    memRegion (sp + 8352#64) 64 ∗
    SHatMem sp (g.drop 32) ∗
    memRegion (sp + 9952#64) 7424 ∗
    EHatMem sp (g.drop 32) ∗
    memRegion (sp + 18912#64) 10496 ∗
    ((sp + 29408#64) ↦ₛ g.drop 32) ∗
    memRegion (sp + 29440#64) 480 ∗
    F)

theorem seg3_secvecs_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s : State) (seedA outPtr : BitVec 64) (seed : List (BitVec 8)) (F : SepProp)
    {P : SepProp} (hexit : Seg2MatrixExit b s0 seedA outPtr seed F s P) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off5c60) s P
      (Seg3Exit b s0 seedA outPtr seed F) := by
  let sp := s0.sp - 30080#64
  let g := sha3_512List (seed.take 32 ++ [3#8])
  let sigma := g.drop 32
  have hsig : sigma.length = 32 := by
    have hg : g.length = 64 := by simp [g, sha3_512List, keccakSponge]
    simp [sigma, hg]
  have hfp_val : s0.sp - 96#64 = sp + 29984#64 := by dsimp [sp]; bv_omega
  rcases hexit with ⟨hpc, hrun, hcl, hro, ⟨⟨hsp, hspA, hfp, _⟩, _⟩, hP⟩
  refine SepWP.weaken_pre hP ?_
  rw [split_3600_seg3 sp, split_21056_seg3 sp, split_480_seg3 sp]
  let Idle1 := SavedFrame05 s0.sp s0 ∗ (seedA ↦ₛ seed) ∗ (sp ↦ₛ g.take 32) ∗
    ((sp + 32#64) ↦₆₄ seedA) ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗ ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗
    memRegion (sp + 56#64) 80 ∗ memRegion (sp + 144#64) 1424 ∗ memRegion (sp + 2208#64) 1536 ∗
    AMatrixMem sp (g.take 32) ∗ memRegion (sp + 8352#64) 64 ∗ memRegion (sp + 9952#64) 32 ∗
    memRegion (sp + 10368#64) 128 ∗ memRegion (sp + 10496#64) 6880 ∗ memRegion (sp + 17888#64) 1024 ∗
    memRegion (sp + 18912#64) 8928 ∗ memRegion (sp + 27968#64) 256 ∗ memRegion (sp + 28224#64) 800 ∗
    memRegion (sp + 29152#64) 256 ∗ memRegion (sp + 29472#64) 32 ∗ memRegion (sp + 29504#64) 99 ∗
    memRegion (sp + 29603#64) 13 ∗ memRegion (sp + 29715#64) 29 ∗ memRegion (sp + 29872#64) 48 ∗ F
  refine SepWP.weaken_pre
    (P' := ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ ((sp + 29408#64) ↦ₛ sigma) ∗
      memRegion (sp + 1568#64) 640 ∗ memRegion (sp + 8416#64) 1536 ∗
      memRegion (sp + 9984#64) 384 ∗ memRegion (sp + 17376#64) 512 ∗
      memRegion (sp + 27840#64) 128 ∗ memRegion (sp + 29024#64) 128 ∗
      memRegion (sp + 29440#64) 32 ∗ memRegion (sp + 29616#64) 99 ∗
      memRegion (sp + 29744#64) 128 ∗ stackAt sp 1136 ∗ Idle1)
    (by dsimp only [Idle1]; sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg3_sHat_ok hb hbase s sp sigma Idle1 hsig hpc hrun hsp hspA (hfp.trans hfp_val) hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, _, _, _, t', _, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have ht640 : SpillSliceMem 40 (sp + 1568#64) t' ⊢
      memRegion (sp + 1568#64) 384 ∗ memRegion (sp + 1952#64) 256 := by
    rw [← split_640_seg3 sp]; exact vecRangeMem_entails_memRegion 40 (sp + 1568#64) _
  have h512_join : memRegion (sp + 9984#64) 384 ∗ memRegion (sp + 10368#64) 128 =
      memRegion (sp + 9984#64) 512 :=
    (memRegion_split' (b := sp + 9984#64) (b' := sp + 10368#64) (n := 384) (k := (128 : Nat))
      rfl (by bv_omega) (by decide)).symm
  have h1536_join : memRegion (sp + 17376#64) 512 ∗ memRegion (sp + 17888#64) 1024 =
      memRegion (sp + 17376#64) 1536 :=
    (memRegion_split' (b := sp + 17376#64) (b' := sp + 17888#64) (n := 512) (k := (1024 : Nat))
      rfl (by bv_omega) (by decide)).symm
  have h384_join : memRegion (sp + 27840#64) 128 ∗ memRegion (sp + 27968#64) 256 =
      memRegion (sp + 27840#64) 384 :=
    (memRegion_split' (b := sp + 27840#64) (b' := sp + 27968#64) (n := 128) (k := (256 : Nat))
      rfl (by bv_omega) (by decide)).symm
  have h128_join : memRegion (sp + 29616#64) 99 ∗ memRegion (sp + 29715#64) 29 =
      memRegion (sp + 29616#64) 128 :=
    (memRegion_split' (b := sp + 29616#64) (b' := sp + 29715#64) (n := 99) (k := (29 : Nat))
      rfl (by bv_omega) (by decide)).symm
  dsimp only [Idle1]
  refine SepWP.weaken_pre
    (P' := ((sp + 29440#64) ↦ₛ sigma) ∗ memRegion (sp + 1952#64) 256 ∗
      memRegion (sp + 9984#64) 512 ∗ memRegion (sp + 17376#64) 1536 ∗
      memRegion (sp + 27840#64) 384 ∗ memRegion (sp + 29024#64) 128 ∗
      memRegion (sp + 29504#64) 99 ∗ memRegion (sp + 29616#64) 128 ∗
      memRegion (sp + 29744#64) 128 ∗ stackAt sp 1136 ∗
      (((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ ((sp + 29408#64) ↦ₛ sigma) ∗ SHatMem sp sigma ∗
        memRegion (sp + 1568#64) 384 ∗
        SavedFrame05 s0.sp s0 ∗ (seedA ↦ₛ seed) ∗ (sp ↦ₛ g.take 32) ∗
        ((sp + 32#64) ↦₆₄ seedA) ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗ ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗
        memRegion (sp + 56#64) 80 ∗ memRegion (sp + 144#64) 1424 ∗ memRegion (sp + 2208#64) 1536 ∗
        AMatrixMem sp (g.take 32) ∗ memRegion (sp + 8352#64) 64 ∗ memRegion (sp + 9952#64) 32 ∗
        memRegion (sp + 10496#64) 6880 ∗ memRegion (sp + 18912#64) 8928 ∗
        memRegion (sp + 28224#64) 800 ∗ memRegion (sp + 29152#64) 256 ∗
        memRegion (sp + 29472#64) 32 ∗ memRegion (sp + 29603#64) 13 ∗
        memRegion (sp + 29872#64) 48 ∗ F))
    (by
      rw [← h512_join, ← h1536_join, ← h384_join, ← h128_join]
      exact entails_sub ht640 (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg3_eHat_ok hb hbase s1 sp sigma _ hsig hpc1 hrun1 hsp1 hspA1 hfp1 hx19_1 hcl1 hro1) ?_
  rintro sf Pf hpcf hrunf _ _ ⟨hspf, hspAf, hfpf, hclf, hrof, hPf⟩
  refine SepWP.done hpcf hrunf
    ⟨hpcf, hrunf, hspf, hspAf, hfpf.trans hfp_val.symm, hclf, hrof, ?_⟩
  refine Entails.trans hPf ?_
  have hsig32 : ((sp + 29440#64) ↦ₛ sigma) ⊢ memRegion (sp + 29440#64) 32 := by
    simpa [hsig] using pointsToBytes_entails_memRegion (sp + 29440#64) sigma
  rw [split_3600_seg3 sp, split_640_seg3 sp, join_7424_seg3 sp, join_10496_seg3 sp,
      split_480_seg3 sp, ← h128_join]
  exact entails_sub hsig32 (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3

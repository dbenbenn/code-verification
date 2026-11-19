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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1c -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2Simd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1c
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2FwdLowFp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2a

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 2b (`uHat[0..2]` Loop & Copy, `+0x052c .. +0x1884`)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2b

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonPolyNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPure (upperFwdNtt16 upperFwdNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup4hLow dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem Spill13 Vec32 poly32Mem_entails_memRegion poly32Mem_ofFn
  polyVecNat vecRangeBytes vecRangeBytes_length vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (Spill21Mem Spill6)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs (
  SExpr SymGpr SymGprs31 SymVRegs runSymRange runSymRange_add symInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval (
  SymEnv SymSpatial SymStateMatches evalSExpr evalSymGpr evalSymPState evalSymSpill21
  inPolyMemAt polyAddr spillMemAt symEnvOf symInit_matches)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyBridge (InSymWord04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly (sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyPureBridge (
  symPoly_eq_barrettMap symPoly_eq_upperFwdNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1a (cfgFwd1 run_fwd1a symFwd1Init)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1b (run_fwd1b symFwd1MidB)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymEvalFwd1c (
  cfgFwd1Tail fwd1_hi_ast_eq fwd1_hi_noSpillVreg fwd1_tail_ast_eq fwd1_tail_noSpillVreg
  run_fwd1_hi2 run_fwd1_tail symFwd1HiEnd symFwd1PreHi2 symFwd1TailEnd)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure (
  barrett_lowerFwdNtt16_upper lowerFwdNtt16 lowerFwdNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2FwdLowFp (fwd1_low_v8_fp_ok ro00Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a (sepWP_elim_poly32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b (blk28_memcpy_04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1c (uHatZetaSpill21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2Simd (
  decompPoly16 decompPoly16_size uHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2a (seg2a_iter_ok)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x1460 → 0x1464, 0x1868 → 0x1880]
end

attribute [local irreducible] blkPC04 polyVecNat

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

private theorem run_fwd1ab : runSymRange cfgFwd1 461 843 symFwd1Init = some symFwd1MidB :=
  runSymRange_add cfgFwd1 461 422 421 _ _ _ run_fwd1a run_fwd1b

private theorem evalSExpr_gpr0_irrel (env : SymEnv) (g' : Nat → BitVec 64) (e : SExpr) :
    evalSExpr { env with gpr0 := g' } e = evalSExpr env e := by
  induction e <;> simp [evalSExpr, *]

private theorem spill21_fwd1Init (env : SymEnv) :
    evalSymSpill21 env symFwd1Init.spill21 = uHatZetaSpill21 := rfl

private theorem spill21_fwd1HiEnd (env : SymEnv) :
    evalSymSpill21 env symFwd1HiEnd.spill21 = uHatZetaSpill21 := rfl

private theorem matches_fwd1Init (s : State) (sp polyPtr : BitVec 64) (p : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hx21 : s.readReg64 .x21 = polyPtr) :
    let env := symEnvOf s Spill13.zero ⟨0#128, 0#128, 0#128, 0#128, 0#128, 0#128⟩
      uHatZetaSpill21 (Vec32.ofFn (polyVecNat p)) Vec32.zero
    SymStateMatches cfgFwd1 sp polyPtr env symFwd1Init s := by
  dsimp only
  refine ⟨hsp, hspA, ?_, ?_, ?_, rfl⟩
  · rintro r ⟨rfl⟩; exact hx21
  · intro r; rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · intro r hr; rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symFwd1Init, SymGprs31.get, evalSymGpr, symEnvOf]
    | 31 => simp at hr
    | _ + 32 => omega

private theorem seg2_adrp_ro00 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (P : SepProp)
    (hpc : s.pc = b + 5216#64) (hrun : s.status = .Running) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 5224#64) s P
      (fun sf Pf =>
        sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ sf.pstate = s.pstate ∧
        sf.vregs = s.vregs ∧
        sf.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64 ∧
        (∀ r : BitVec 5, r ≠ 8#5 → r.toNat < 31 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = P) := by
  subst hbase
  wp_steps 2
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨rfl, rfl, rfl, rfl, by simp [ro00Sym], fun r hr8 hr31 => ?_, rfl⟩
  rcases r with ⟨rv, hrv⟩
  match rv with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
  | 8 => exact absurd rfl hr8
  | 31 => simp at hr31
  | _ + 32 => omega

private theorem seg2_loop_tail [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) {idx : Nat} (hidx : idx < 3) (P : SepProp)
    (hpc : s.pc = b + 6248#64) (hrun : s.status = .Running)
    (hpst : s.pstate = (AddWithCarry64 (BitVec.ofNat 64 (idx + 1)) (~~~3#64) true).2) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if idx < 2 then b + 1324#64 else b + 6252#64) s P
      (fun sf Pf =>
        sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ sf.vregs = s.vregs ∧
        sf.regs = s.regs ∧ Pf = P) := by
  set off : BitVec 64 := BitVec.ofInt 64 (-4924)
  have hf : (blkPC04.rebase b (fun _ => none)).fetch (b + 6248#64) =
      some (.bCond .NE off) := by subst hbase; wp_norm_lhs
  have hpc_tgt : (b + 6248#64) + off = b + 1324#64 := by dsimp only [off]; clear * -; bv_omega
  have hpc_fall : (b + 6248#64) + 4#64 = b + 6252#64 := by clear * -; bv_omega
  rcases s with ⟨regs, vregs, sp, pc, ps, mem, tpidr, fpsr, brkS, brk, fs, orc, oidx, excls, tr, st, sym, sigA, sigS, sigM, sigP, phys⟩
  dsimp only at hpc hrun hpst ⊢
  subst hpc
  let s0 : State := ⟨regs, vregs, sp, b + 6248#64, ps, mem, tpidr, fpsr, brkS, brk, fs, orc, oidx, excls, tr, st, sym, sigA, sigS, sigM, sigP, phys⟩
  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 by omega) with rfl | rfl | rfl
  · simp only [show (0 : Nat) < 2 by decide, ↓reduceIte]
    have hcond : ConditionHolds .NE ps = true := by
      rw [hpst]; exact (by decide +kernel : ConditionHolds .NE (AddWithCarry64 1#64 (~~~3#64) true).2 = true)
    refine SepWP.step_pure (s' := s0.setPC (b + 1324#64)) rfl hrun hf ?_ (by simp [s0, State.setPC]) ?_
    · simp only [s0, Program.evalInst, State.setPC, execInstWithSvc, hcond, ↓reduceIte, hpc_tgt]
    · exact SepWP.done (by simp [s0, State.setPC]) (by simp [s0, State.setPC, hrun]) (by simp [s0, State.setPC, State.spAligned])
  · simp only [show (1 : Nat) < 2 by decide, ↓reduceIte]
    have hcond : ConditionHolds .NE ps = true := by
      rw [hpst]; exact (by decide +kernel : ConditionHolds .NE (AddWithCarry64 2#64 (~~~3#64) true).2 = true)
    refine SepWP.step_pure (s' := s0.setPC (b + 1324#64)) rfl hrun hf ?_ (by simp [s0, State.setPC]) ?_
    · simp only [s0, Program.evalInst, State.setPC, execInstWithSvc, hcond, ↓reduceIte, hpc_tgt]
    · exact SepWP.done (by simp [s0, State.setPC]) (by simp [s0, State.setPC, hrun]) (by simp [s0, State.setPC, State.spAligned])
  · simp only [Nat.lt_irrefl, ↓reduceIte]
    have hcond : ConditionHolds .NE ps = false := by
      rw [hpst]; exact (by decide +kernel : ConditionHolds .NE (AddWithCarry64 3#64 (~~~3#64) true).2 = false)
    refine SepWP.step_pure (s' := s0.setPC (b + 6252#64)) rfl hrun hf ?_ (by simp [s0, State.setPC]) ?_
    · simp only [s0, Program.evalInst, State.setPC, State.advancePC, execInstWithSvc, hcond, Bool.false_eq_true, ↓reduceIte, hpc_fall]
    · exact SepWP.done (by simp [s0, State.setPC]) (by simp [s0, State.setPC, hrun]) (by simp [s0, State.setPC, State.spAligned])

/-- Single iteration `idx < 3` of `uHat[idx]` (`+0x052c → +0x052c / +0x186c`). -/
private theorem seg2_uhat_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3)
    (bs : List (BitVec 8)) (hbs : bs.length = 320) (Rest : SepProp)
    (hpc : s.pc = b + 1324#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 idx)
    (hx20 : s.readReg64 .x20 = 62209#64)
    (hx22 : s.readReg64 .x22 = sp + 11856#64)
    (hx23 : s.readReg64 .x23 = sp + BitVec.ofNat 64 (11872 + 512 * idx))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (16 + 512 * idx))
    (hx25 : s.readReg64 .x25 = sp + BitVec.ofNat 64 (3353 + 320 * idx))
    (hx27 : s.readReg64 .x27 = sp + 5680#64)
    (hv8 : (s.readVReg128 8#5).truncate 64 = (dup4hLow 3329#16).truncate 64) :
    let src := sp + BitVec.ofNat 64 (3344 + 320 * idx)
    let polyPtr := sp + BitVec.ofNat 64 (11856 + 512 * idx)
    SepWP (blkPC04.rebase b (fun _ => none))
      (if idx < 2 then b + 1324#64 else b + 6252#64) s
      (Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
        memRegion (sp + 5680#64) 512 ∗ (src ↦ₛ bs) ∗ memRegion polyPtr 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x8 = BitVec.ofNat 64 (idx + 1) ∧ sf.readReg64 .x20 = 62209#64 ∧
        sf.readReg64 .x22 = sp + 11856#64 ∧
        sf.readReg64 .x23 = sp + BitVec.ofNat 64 (11872 + 512 * (idx + 1)) ∧
        sf.readReg64 .x24 = BitVec.ofNat 64 (16 + 512 * (idx + 1)) ∧
        sf.readReg64 .x25 = sp + BitVec.ofNat 64 (3353 + 320 * (idx + 1)) ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = sp + 5680#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (sf.readVReg128 8#5).truncate 64 = (dup4hLow 3329#16).truncate 64 ∧
        (Pf ⊢ Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
          memRegion (sp + 5680#64) 512 ∗ (src ↦ₛ bs) ∗
          PolyMem polyPtr (polyVecNat (neonPolyNtt16 (decompPoly16 10 bs))) ∗ Rest)) := by
  intro src polyPtr
  set p0 := decompPoly16 10 bs
  have hp0 : p0.size = 256 := decompPoly16_size 10 bs
  refine SepWP.weaken_pre (by sep_frame) ?_
  sep_frame_apply (sepWP_elim_poly32 (a := sp + 5680#64)); intro vScratch
  refine SepWP.weaken_pre
    (show Poly32Mem (sp + 5680#64) vScratch ∗
        (Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗ (src ↦ₛ bs) ∗ memRegion polyPtr 512 ∗ Rest) ⊢
      Poly32Mem (sp + 5680#64) vScratch ∗ (src ↦ₛ bs) ∗ memRegion polyPtr 512 ∗
        (Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗ Rest) by sep_frame)
    (sepWP_seq_env hcl hro
      (seg2a_iter_ok hb hbase s sp idx hidx vScratch bs hbs _
        hpc hrun hsp hspA hcl hro hx8 hx22 hx25 hx27 hv8) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx19_1, hfp1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1,
      hx25_1, hx26_1, hx27_1, hx28_1, hv8_1, hP1⟩
  set z6 : Spill6 := ⟨0#128, 0#128, 0#128, 0#128, 0#128, 0#128⟩
  set env := symEnvOf s1 Spill13.zero z6 uHatZetaSpill21 (Vec32.ofFn (polyVecNat p0)) Vec32.zero
  set F_fwd := memRegion (sp + 5680#64) 512 ∗ (src ↦ₛ bs) ∗ Rest
  have hP1_sym : P1 ⊢ SymSpatial cfgFwd1 sp polyPtr env symFwd1Init F_fwd := by
    refine Entails.trans hP1 ?_
    dsimp only [SymSpatial, cfgFwd1, polyAddr, spillMemAt, inPolyMemAt, F_fwd]
    rw [spill21_fwd1Init]
    have hp_init : SymPolyEval.evalSymVec32 env symFwd1Init.poly = Vec32.ofFn (polyVecNat p0) := by
      dsimp only [env, symEnvOf]
      generalize Vec32.ofFn (polyVecNat p0) = v0
      cases v0; rfl
    rw [hp_init]
    exact entails_sub (poly32Mem_entails_memRegion (sp + 5680#64) _) (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP1_sym
    (sepWP_seq_env hcl1 hro1
      (sepWP_of_runSymRange (cfg := cfgFwd1) (sp := sp) (polyPtr := polyPtr) (env := env) (F := F_fwd)
        843 461 (fun j h1 h2 => Or.inl ⟨h1, h2⟩)
        run_fwd1ab (matches_fwd1Init s1 sp polyPtr p0 hsp1 hspA1 hx21_1) hpc1 hrun1
        (post := fun s2 P2 => SymStateMatches cfgFwd1 sp polyPtr env symFwd1MidB s2 ∧
          P2 = SymSpatial cfgFwd1 sp polyPtr env symFwd1MidB F_fwd)
        (fun s2 _ _ hm2 => ⟨hm2, rfl⟩)) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hm2, rfl⟩
  refine sepWP_seq_env hcl2 hro2 (seg2_adrp_ro00 hb hbase s2 _ hpc2 hrun2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hpst3, hvregs3, hx8_3, hgpr3, rfl⟩
  let env' : SymEnv :=
    { env with gpr0 := fun r => if r = 8 then mlkemMpl.ρ ro00Sym + 66#64 else env.gpr0 r }
  have hm3 : SymStateMatches cfgFwd1 sp polyPtr env' symFwd1PreHi2 s3 := by
    refine ⟨hsp3.trans hm2.hsp, hspA3.trans hm2.hsp_al, ?_, fun r => ?_, fun r hr => ?_,
      hpst3.trans hm2.hpstate⟩
    · rintro r ⟨rfl⟩
      rw [hgpr3 21#5 (by decide) (by decide)]
      exact hm2.hpoly 21#5 rfl
    · have hvr : s3.readVReg128 r = s2.readVReg128 r := by simp [State.readVReg128, hvregs3]
      rw [hvr, hm2.hvregs r]; exact (evalSExpr_gpr0_irrel env _ _).symm
    · by_cases hr8 : r = 8#5
      · subst hr8
        simpa [symFwd1PreHi2, SymGprs31.get, evalSymGpr, env'] using hx8_3
      · rw [hgpr3 r hr8 hr, hm2.hgprs r hr]
        rcases r with ⟨rv, hrv⟩
        match rv with
        | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 | 10 | 11 | 12 | 13 | 14 | 15
        | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => rfl
        | 8 => exact absurd rfl hr8
        | 31 => simp at hr
        | _ + 32 => omega
  have hspat3 : SymSpatial cfgFwd1 sp polyPtr env symFwd1MidB F_fwd =
      SymSpatial cfgFwd1 sp polyPtr env' symFwd1PreHi2 F_fwd := by
    dsimp only [SymSpatial, cfgFwd1, polyAddr, spillMemAt, inPolyMemAt, symFwd1PreHi2,
      SymPolyEval.evalSymSpill21, SymPolyEval.evalSymVec32, env']
    simp only [evalSExpr_gpr0_irrel]
  rw [hspat3]
  refine sepWP_seq_env hcl3 hro3
    (sepWP_of_runSymRange (cfg := cfgFwd1) (sp := sp) (polyPtr := polyPtr) (env := env') (F := F_fwd)
      27 1306 (fun j h1 h2 => Or.inr (Or.inl ⟨h1, h2⟩))
      run_fwd1_hi2 hm3 hpc3 hrun3
      (post := fun s4 P4 => SymStateMatches cfgFwd1 sp polyPtr env' symFwd1HiEnd s4 ∧
        P4 = SymSpatial cfgFwd1 sp polyPtr env' symFwd1HiEnd F_fwd)
      (fun s4 _ _ hm4 => ⟨hm4, rfl⟩)) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hm4, rfl⟩
  have hx23_s1 : s1.readReg64 .x23 = polyPtr + 16#64 := by
    rw [hx23_1, hx23]; dsimp only [polyPtr]; clear * - hidx; bv_omega
  have hx8_4 : s4.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64 := hm4.hgprs 8#5 (by decide)
  have hx9_4 : s4.readReg64 .x9 = polyPtr + 16#64 :=
    (hm4.hgprs 9#5 (by decide)).trans hx23_s1
  have hx10_4 : s4.readReg64 .x10 = 16#64 := hm4.hgprs 10#5 (by decide)
  have hx19_4 : s4.readReg64 .x19 = BitVec.ofNat 64 (idx + 1) :=
    (hm4.hgprs 19#5 (by decide)).trans hx19_1
  have hx20_4 : s4.readReg64 .x20 = 62209#64 :=
    (hm4.hgprs 20#5 (by decide)).trans (hx20_1.trans hx20)
  have hx21_4 : s4.readReg64 .x21 = polyPtr := hm4.hpoly 21#5 rfl
  have hx22_4 : s4.readReg64 .x22 = sp + 11856#64 :=
    (hm4.hgprs 22#5 (by decide)).trans hx22_1
  have hx23_4 : s4.readReg64 .x23 = sp + BitVec.ofNat 64 (11872 + 512 * idx) :=
    (hm4.hgprs 23#5 (by decide)).trans (hx23_1.trans hx23)
  have hx24_4 : s4.readReg64 .x24 = BitVec.ofNat 64 (16 + 512 * idx) :=
    (hm4.hgprs 24#5 (by decide)).trans (hx24_1.trans hx24)
  have hx25_4 : s4.readReg64 .x25 = sp + BitVec.ofNat 64 (3353 + 320 * idx) :=
    (hm4.hgprs 25#5 (by decide)).trans hx25_1
  have hx26_4 : s4.readReg64 .x26 = s.readReg64 .x26 :=
    (hm4.hgprs 26#5 (by decide)).trans hx26_1
  have hx27_4 : s4.readReg64 .x27 = sp + 5680#64 :=
    (hm4.hgprs 27#5 (by decide)).trans hx27_1
  have hx28_4 : s4.readReg64 .x28 = s.readReg64 .x28 :=
    (hm4.hgprs 28#5 (by decide)).trans hx28_1
  have hfp_4 : s4.readReg64 .fp = s.readReg64 .fp :=
    (hm4.hgprs 29#5 (by decide)).trans hfp1
  have hv8_4 : (s4.readVReg128 8#5).truncate 64 = (dup4hLow 3329#16).truncate 64 := by
    have hv : s4.readVReg128 8#5 = s1.readVReg128 8#5 := hm4.hvregs 8#5
    exact hv ▸ hv8_1
  have hv11_4 : s4.readVReg128 11#5 = dup8x16 3329#16 := hm4.hvregs 11#5
  set pUp := upperFwdNtt16 p0
  have hpUp : pUp.size = 256 := (upperFwdNtt16_size p0).trans hp0
  have hp4_mem : Poly32Mem polyPtr (SymPolyEval.evalSymVec32 env' symFwd1HiEnd.poly) =
      PolyMem polyPtr (polyVecNat pUp) :=
    symPoly_eq_upperFwdNtt polyPtr symFwd1HiEnd.poly hp0 env' rfl fwd1_hi_noSpillVreg fwd1_hi_ast_eq
  set F_low := Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗ F_fwd
  have hP4 : SymSpatial cfgFwd1 sp polyPtr env' symFwd1HiEnd F_fwd ⊢
      PolyMem polyPtr (polyVecNat pUp) ∗ F_low := by
    dsimp only [SymSpatial, cfgFwd1, polyAddr, spillMemAt, inPolyMemAt, F_low]
    rw [hp4_mem, spill21_fwd1HiEnd]; sep_frame
  refine SepWP.weaken_pre hP4
    (sepWP_seq_env hcl4 hro4
      (fwd1_low_v8_fp_ok hb s4 sp polyPtr hpUp F_low
        hpc4 hrun4 hm4.hsp hm4.hsp_al hcl4 hro4 hx8_4 hx9_4 hx10_4 hx20_4
        (by rw [hx22_4, hx24_4]; dsimp only [polyPtr]; clear * - hidx; bv_omega) hv11_4) ?_)
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hsp5, hspA5, hpres5, rfl⟩
  rcases hpres5 with ⟨hp8, _, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hpfp⟩
  set q := lowerFwdNtt16 pUp
  have hq : q.size = 256 := (lowerFwdNtt16_size pUp).trans hpUp
  have hinit5 := symInit_matches cfgFwd1Tail s5 sp polyPtr
    Spill13.zero z6 uHatZetaSpill21 (Vec32.ofFn (polyVecNat q)) Vec32.zero hsp5 hspA5
    (by rintro r ⟨rfl⟩; exact hp21.trans hx21_4)
  set envB := symEnvOf s5 Spill13.zero z6 uHatZetaSpill21 (Vec32.ofFn (polyVecNat q)) Vec32.zero
  have hP5 : PolyMem polyPtr (polyVecNat q) ∗ F_low ⊢
      SymSpatial cfgFwd1Tail sp polyPtr envB symInit F_low := by
    dsimp only [SymSpatial, cfgFwd1Tail, polyAddr, spillMemAt, inPolyMemAt]
    rw [hinit5.2.2.2.2, ← poly32Mem_ofFn polyPtr (polyVecNat q)]
    sep_frame
  refine SepWP.weaken_pre hP5
    (sepWP_seq_env hcl5 hro5
      (sepWP_of_runSymRange (cfg := cfgFwd1Tail) (sp := sp) (polyPtr := polyPtr) (env := envB) (F := F_low)
        169 1393 (fun j h1 h2 => Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
        run_fwd1_tail hinit5.1 hpc5 hrun5
        (post := fun s6 P6 => SymStateMatches cfgFwd1Tail sp polyPtr envB symFwd1TailEnd s6 ∧
          P6 = SymSpatial cfgFwd1Tail sp polyPtr envB symFwd1TailEnd F_low)
        (fun s6 _ _ hm6 => ⟨hm6, rfl⟩)) ?_)
  rintro s6 P6 hpc6 hrun6 _ _ ⟨hm6, rfl⟩
  have hp6_mem : Poly32Mem polyPtr (SymPolyEval.evalSymVec32 envB symFwd1TailEnd.poly) =
      PolyMem polyPtr (polyVecNat (neonPolyNtt16 p0)) := by
    rw [symPoly_eq_barrettMap polyPtr symFwd1TailEnd.poly hq envB rfl
      fwd1_tail_noSpillVreg fwd1_tail_ast_eq, barrett_lowerFwdNtt16_upper p0]
  have hx19_5 : s5.readReg64 .x19 = BitVec.ofNat 64 (idx + 1) := hp19.trans hx19_4
  have hpst6 : s6.pstate = (AddWithCarry64 (BitVec.ofNat 64 (idx + 1)) (~~~3#64) true).2 := by
    have hp := hm6.hpstate
    simpa [symFwd1TailEnd, evalSymPState, evalSymGpr, envB, symEnvOf, hx19_5] using hp
  refine SepWP.mono (seg2_loop_tail hb hbase s6 hidx _ hpc6 hrun6 hpst6) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hvregs_f, hregs_f, rfl⟩
  have hreg_eq : ∀ r : Reg, sf.readReg64 r = s6.readReg64 r := fun r => by
    cases r <;> simp [State.readReg64, hregs_f, hsp_f]
  have hfp_6 : s6.readReg64 .fp = s.readReg64 .fp :=
    (hm6.hgprs 29#5 (by decide)).trans (hpfp.trans hfp_4)
  have hx8_6 : s6.readReg64 .x8 = BitVec.ofNat 64 (idx + 1) :=
    (hm6.hgprs 8#5 (by decide)).trans hx19_5
  have hx20_6 : s6.readReg64 .x20 = 62209#64 :=
    (hm6.hgprs 20#5 (by decide)).trans (hp20.trans hx20_4)
  have hx22_6 : s6.readReg64 .x22 = sp + 11856#64 :=
    (hm6.hgprs 22#5 (by decide)).trans (hp22.trans hx22_4)
  have hx23_6 : s6.readReg64 .x23 = sp + BitVec.ofNat 64 (11872 + 512 * (idx + 1)) := by
    have h6 := hm6.hgprs 23#5 (by decide)
    simp only [BitVec.toNat_ofNat, symFwd1TailEnd, SymGprs31.get, evalSymGpr, envB, symEnvOf] at h6
    rw [show s6.readReg64 (.gpr 23#5) = s6.readReg64 .x23 from rfl,
      show s5.readReg64 (.gpr 23#5) = s5.readReg64 .x23 from rfl, hp23, hx23_4] at h6
    rw [h6]; clear * - hidx; bv_omega
  have hx24_6 : s6.readReg64 .x24 = BitVec.ofNat 64 (16 + 512 * (idx + 1)) := by
    have h6 := hm6.hgprs 24#5 (by decide)
    simp only [BitVec.toNat_ofNat, symFwd1TailEnd, SymGprs31.get, evalSymGpr, envB, symEnvOf] at h6
    rw [show s6.readReg64 (.gpr 24#5) = s6.readReg64 .x24 from rfl,
      show s5.readReg64 (.gpr 24#5) = s5.readReg64 .x24 from rfl, hp24, hx24_4] at h6
    rw [h6]; clear * - hidx; bv_omega
  have hx25_6 : s6.readReg64 .x25 = sp + BitVec.ofNat 64 (3353 + 320 * (idx + 1)) := by
    have h6 := hm6.hgprs 25#5 (by decide)
    simp only [BitVec.toNat_ofNat, symFwd1TailEnd, SymGprs31.get, evalSymGpr, envB, symEnvOf] at h6
    rw [show s6.readReg64 (.gpr 25#5) = s6.readReg64 .x25 from rfl,
      show s5.readReg64 (.gpr 25#5) = s5.readReg64 .x25 from rfl, hp25, hx25_4] at h6
    rw [h6]; clear * - hidx; bv_omega
  have hx26_6 : s6.readReg64 .x26 = s.readReg64 .x26 :=
    (hm6.hgprs 26#5 (by decide)).trans (hp26.trans hx26_4)
  have hx27_6 : s6.readReg64 .x27 = sp + 5680#64 :=
    (hm6.hgprs 27#5 (by decide)).trans (hp27.trans hx27_4)
  have hx28_6 : s6.readReg64 .x28 = s.readReg64 .x28 :=
    (hm6.hgprs 28#5 (by decide)).trans (hp28.trans hx28_4)
  have hv8_f : (sf.readVReg128 8#5).truncate 64 = (dup4hLow 3329#16).truncate 64 := by
    have h6 : s6.readVReg128 8#5 = s5.readVReg128 8#5 := hm6.hvregs 8#5
    have hf6 : sf.readVReg128 8#5 = s6.readVReg128 8#5 := by simp [State.readVReg128, hvregs_f]
    rw [hf6, h6, hp8]; exact hv8_4
  refine ⟨hsp_f.trans hm6.hsp, hspA_f.trans hm6.hsp_al,
    (hreg_eq .fp).trans hfp_6, (hreg_eq .x8).trans hx8_6, (hreg_eq .x20).trans hx20_6,
    (hreg_eq .x22).trans hx22_6, (hreg_eq .x23).trans hx23_6, (hreg_eq .x24).trans hx24_6,
    (hreg_eq .x25).trans hx25_6, (hreg_eq .x26).trans hx26_6, (hreg_eq .x27).trans hx27_6,
    (hreg_eq .x28).trans hx28_6, hv8_f, ?_⟩
  dsimp only [SymSpatial, cfgFwd1Tail, polyAddr, spillMemAt, inPolyMemAt, F_low, F_fwd]
  rw [hp6_mem]; sep_frame

theorem ct_pointsTo_split (ptr : BitVec 64) {ct1 ct2 : List (BitVec 8)}
    (hct1 : ct1.length = 960) :
    (ptr ↦ₛ (ct1 ++ ct2)) =
      (ptr ↦ₛ ct1.take 320) ∗
      ((ptr + 320#64) ↦ₛ (ct1.drop 320).take 320) ∗
      ((ptr + 640#64) ↦ₛ (ct1.drop 640).take 320) ∗
      ((ptr + 960#64) ↦ₛ ct2) := by
  have h0 : ct1 = ct1.take 320 ++ ct1.drop 320 := (List.take_append_drop 320 ct1).symm
  have h1 : ct1.drop 320 = (ct1.drop 320).take 320 ++ ct1.drop 640 := by
    simpa [List.drop_drop] using (List.take_append_drop 320 (ct1.drop 320)).symm
  have h2 : ct1.drop 640 = (ct1.drop 640).take 320 := by
    rw [List.take_of_length_le (by simp [hct1])]
  have hl0 : (ct1.take 320).length = 320 := by simp [hct1]
  have hl1 : ((ct1.drop 320).take 320).length = 320 := by simp [hct1]
  have hl2 : ((ct1.drop 640).take 320).length = 320 := by simp [hct1]
  have heq : ct1 ++ ct2 =
      ct1.take 320 ++ ((ct1.drop 320).take 320 ++ ((ct1.drop 640).take 320 ++ ct2)) := by
    conv_lhs => lhs; rw [h0, h1, h2]
    simp [List.append_assoc]
  conv_lhs => rw [heq]
  rw [pointsToBytes_append, hl0, show BitVec.ofNat 64 320 = 320#64 from rfl,
    pointsToBytes_append, hl1, show ptr + 320#64 + BitVec.ofNat 64 320 = ptr + 640#64 by bv_omega,
    pointsToBytes_append, hl2, show ptr + 640#64 + BitVec.ofNat 64 320 = ptr + 960#64 by bv_omega]

private theorem threePolys_eq_pointsToBytes (ptr : BitVec 64) (u0 u1 u2 : Poly16) :
    PolyMem ptr (polyVecNat u0) ∗
      PolyMem (ptr + 512#64) (polyVecNat u1) ∗
      PolyMem (ptr + 1024#64) (polyVecNat u2) =
      (ptr ↦ₛ (vecRangeBytes 32 (polyVecNat u0) ++ vecRangeBytes 32 (polyVecNat u1) ++
        vecRangeBytes 32 (polyVecNat u2))) := by
  set b0 := vecRangeBytes 32 (polyVecNat u0)
  set b1 := vecRangeBytes 32 (polyVecNat u1)
  have h0 : b0.length = 512 := vecRangeBytes_length 32 _
  have h1 : b1.length = 512 := vecRangeBytes_length 32 _
  rw [List.append_assoc,
    pointsToBytes_append, h0, show BitVec.ofNat 64 512 = 512#64 from rfl,
    pointsToBytes_append, h1, show ptr + 512#64 + BitVec.ofNat 64 512 = ptr + 1024#64 by bv_omega,
    ← vecRangeMem_eq_pointsToBytes 32 ptr (polyVecNat u0),
    ← vecRangeMem_eq_pointsToBytes 32 (ptr + 512#64) (polyVecNat u1),
    ← vecRangeMem_eq_pointsToBytes 32 (ptr + 1024#64) (polyVecNat u2)]
  rfl

private theorem seg2_copy_uhat [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (u0 u1 u2 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + 6252#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 6276#64) s
      (memRegion (sp + 5680#64) 1536 ∗
        PolyMem (sp + 11856#64) (polyVecNat u0) ∗
        PolyMem (sp + 12368#64) (polyVecNat u1) ∗
        PolyMem (sp + 12880#64) (polyVecNat u2) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Pf ⊢ PolyMem (sp + 5680#64) (polyVecNat u0) ∗
          PolyMem (sp + 6192#64) (polyVecNat u1) ∗
          PolyMem (sp + 6704#64) (polyVecNat u2) ∗
          memRegion (sp + 11856#64) 1536 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs_def :
    vecRangeBytes 32 (polyVecNat u0) ++ vecRangeBytes 32 (polyVecNat u1) ++
      vecRangeBytes 32 (polyVecNat u2) = bs
  have hbs_len : bs.length = 1536 := by
    rw [← hbs_def]; simp only [List.length_append, vecRangeBytes_length]
  have hsrc : PolyMem (sp + 11856#64) (polyVecNat u0) ∗
      PolyMem (sp + 12368#64) (polyVecNat u1) ∗
      PolyMem (sp + 12880#64) (polyVecNat u2) = ((sp + 11856#64) ↦ₛ bs) := by
    rw [← hbs_def,
      show sp + 12368#64 = sp + 11856#64 + 512#64 by clear * -; bv_omega,
      show sp + 12880#64 = sp + 11856#64 + 1024#64 by clear * -; bv_omega]
    exact threePolys_eq_pointsToBytes (sp + 11856#64) u0 u1 u2
  have hdst : ((sp + 5680#64) ↦ₛ bs) =
      PolyMem (sp + 5680#64) (polyVecNat u0) ∗
      PolyMem (sp + 6192#64) (polyVecNat u1) ∗
      PolyMem (sp + 6704#64) (polyVecNat u2) := by
    rw [← hbs_def,
      show sp + 6192#64 = sp + 5680#64 + 512#64 by clear * -; bv_omega,
      show sp + 6704#64 = sp + 5680#64 + 1024#64 by clear * -; bv_omega]
    exact (threePolys_eq_pointsToBytes (sp + 5680#64) u0 u1 u2).symm
  have h11856_reg : ((sp + 11856#64) ↦ₛ bs) ⊢ memRegion (sp + 11856#64) 1536 := by
    simpa [hbs_len] using pointsToBytes_entails_memRegion (sp + 11856#64) bs
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion (sp + 5680#64) 1536 ∗ ((sp + 11856#64) ↦ₛ bs) ∗ Rest by
      rw [← hsrc]; sep_frame) ?_
  wp_cut_codeLoaded
  wp_steps 5
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 5680#64, sp + 11856#64, bs)
  rw [hdst]
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  exact entails_sub h11856_reg (by sep_frame) (by sep_frame)

/-- Composed Segment 2b contract (`uHat[0..2]` loop & copy, `+0x052c → +0x1884`). -/
theorem seg2b_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (ct1 ct2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 1324#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = 0#64) (hx20 : s.readReg64 .x20 = 62209#64)
    (hx22 : s.readReg64 .x22 = sp + 11856#64) (hx23 : s.readReg64 .x23 = sp + 11872#64)
    (hx24 : s.readReg64 .x24 = 16#64) (hx25 : s.readReg64 .x25 = sp + 3353#64)
    (hx27 : s.readReg64 .x27 = sp + 5680#64)
    (hv8 : (s.readVReg128 8#5).truncate 64 = (dup4hLow 3329#16).truncate 64)
    (hct1 : ct1.length = 960) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 6276#64) s
      (Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗ ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
        memRegion (sp + 5680#64) 1536 ∗ memRegion (sp + 11856#64) 1536 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = sp + 5680#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Pf ⊢ Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗ ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
          PolyMem (sp + 5680#64) (polyVecNat (uHatPoly16 ct1 0)) ∗
          PolyMem (sp + 6192#64) (polyVecNat (uHatPoly16 ct1 1)) ∗
          PolyMem (sp + 6704#64) (polyVecNat (uHatPoly16 ct1 2)) ∗
          memRegion (sp + 11856#64) 1536 ∗ Rest)) := by
  have hsplit5680 : memRegion (sp + 5680#64) 1536 =
      memRegion (sp + 5680#64) 512 ∗ memRegion (sp + 6192#64) 1024 :=
    memRegion_split' (b := sp + 5680#64) (b' := sp + 6192#64) (n := 512) (k := (1024 : Nat)) rfl (by bv_omega) (by decide)
  have hsplit11856 : memRegion (sp + 11856#64) 1536 =
      (memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 12368#64) 512 ∗
        memRegion (sp + 12880#64) 512) := by
    rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 12368#64) (n := 512) (k := (1024 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 12368#64) (b' := sp + 12880#64) (n := 512) (k := (512 : Nat)) rfl (by bv_omega) (by decide)]
  have hl0 : (ct1.take 320).length = 320 := by simp [hct1]
  have hl1 : ((ct1.drop 320).take 320).length = 320 := by simp [hct1]
  have hl2 : ((ct1.drop 640).take 320).length = 320 := by simp [hct1]
  set R0 := memRegion (sp + 6192#64) 1024 ∗ memRegion (sp + 12368#64) 512 ∗
    memRegion (sp + 12880#64) 512 ∗
    ((sp + 3664#64) ↦ₛ (ct1.drop 320).take 320) ∗
    ((sp + 3984#64) ↦ₛ (ct1.drop 640).take 320) ∗
    ((sp + 4304#64) ↦ₛ ct2) ∗ Rest
  have hP0 : Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
      ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
      memRegion (sp + 5680#64) 1536 ∗ memRegion (sp + 11856#64) 1536 ∗ Rest ⊢
      Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
      memRegion (sp + 5680#64) 512 ∗
      ((sp + BitVec.ofNat 64 (3344 + 320 * 0)) ↦ₛ ct1.take 320) ∗
      memRegion (sp + BitVec.ofNat 64 (11856 + 512 * 0)) 512 ∗ R0 := by
    dsimp only [R0]
    rw [hsplit5680, hsplit11856, ct_pointsTo_split (sp + 3344#64) hct1,
      show sp + 3344#64 + 320#64 = sp + 3664#64 by clear * -; bv_omega,
      show sp + 3344#64 + 640#64 = sp + 3984#64 by clear * -; bv_omega,
      show sp + 3344#64 + 960#64 = sp + 4304#64 by clear * -; bv_omega]
    sep_frame
  have it0 := seg2_uhat_iter hb hbase s sp (idx := 0) (by decide) (ct1.take 320) hl0 R0
    hpc hrun hsp hspA hcl hro hx8 hx20 hx22 hx23 hx24 hx25 hx27 hv8
  simp only [show (0 : Nat) < 2 by decide, ↓reduceIte] at it0
  refine SepWP.weaken_pre hP0 (sepWP_seq_env hcl hro it0 ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx8_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hv8_1, hP1⟩
  set R1 := memRegion (sp + 6192#64) 1024 ∗
    PolyMem (sp + 11856#64) (polyVecNat (uHatPoly16 ct1 0)) ∗
    memRegion (sp + 12880#64) 512 ∗
    ((sp + 3344#64) ↦ₛ ct1.take 320) ∗
    ((sp + 3984#64) ↦ₛ (ct1.drop 640).take 320) ∗
    ((sp + 4304#64) ↦ₛ ct2) ∗ Rest
  have hP1' : P1 ⊢ Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
      memRegion (sp + 5680#64) 512 ∗
      ((sp + BitVec.ofNat 64 (3344 + 320 * 1)) ↦ₛ (ct1.drop 320).take 320) ∗
      memRegion (sp + BitVec.ofNat 64 (11856 + 512 * 1)) 512 ∗ R1 := by
    refine Entails.trans hP1 ?_
    dsimp only [R0, R1, uHatPoly16, Seg2Simd.uPoly16, List.drop_zero]
    sep_frame
  have it1 := seg2_uhat_iter hb hbase s1 sp (idx := 1) (by decide) ((ct1.drop 320).take 320) hl1 R1
    hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hv8_1
  simp only [show (1 : Nat) < 2 by decide, ↓reduceIte] at it1
  refine SepWP.weaken_pre hP1' (sepWP_seq_env hcl1 hro1 it1 ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hfp2, hx8_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hv8_2, hP2⟩
  set R2 := memRegion (sp + 6192#64) 1024 ∗
    PolyMem (sp + 11856#64) (polyVecNat (uHatPoly16 ct1 0)) ∗
    PolyMem (sp + 12368#64) (polyVecNat (uHatPoly16 ct1 1)) ∗
    ((sp + 3344#64) ↦ₛ ct1.take 320) ∗
    ((sp + 3664#64) ↦ₛ (ct1.drop 320).take 320) ∗
    ((sp + 4304#64) ↦ₛ ct2) ∗ Rest
  have hP2' : P2 ⊢ Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
      memRegion (sp + 5680#64) 512 ∗
      ((sp + BitVec.ofNat 64 (3344 + 320 * 2)) ↦ₛ (ct1.drop 640).take 320) ∗
      memRegion (sp + BitVec.ofNat 64 (11856 + 512 * 2)) 512 ∗ R2 := by
    refine Entails.trans hP2 ?_
    dsimp only [R1, R2, uHatPoly16, Seg2Simd.uPoly16]
    sep_frame
  have it2 := seg2_uhat_iter hb hbase s2 sp (idx := 2) (by decide) ((ct1.drop 640).take 320) hl2 R2
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx8_2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hv8_2
  simp only [Nat.lt_irrefl, ↓reduceIte] at it2
  refine SepWP.weaken_pre hP2' (sepWP_seq_env hcl2 hro2 it2 ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 _
    ⟨hsp3, hspA3, hfp3, _, _, _, _, _, _, hx26_3, hx27_3, hx28_3, _, hP3⟩
  have hP3' : P3 ⊢ memRegion (sp + 5680#64) 1536 ∗
      PolyMem (sp + 11856#64) (polyVecNat (uHatPoly16 ct1 0)) ∗
      PolyMem (sp + 12368#64) (polyVecNat (uHatPoly16 ct1 1)) ∗
      PolyMem (sp + 12880#64) (polyVecNat (uHatPoly16 ct1 2)) ∗
      (Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
        ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗ Rest) := by
    refine Entails.trans hP3 ?_
    dsimp only [R2, uHatPoly16, Seg2Simd.uPoly16]
    rw [hsplit5680, ct_pointsTo_split (sp + 3344#64) hct1,
      show sp + 3344#64 + 320#64 = sp + 3664#64 by clear * -; bv_omega,
      show sp + 3344#64 + 640#64 = sp + 3984#64 by clear * -; bv_omega,
      show sp + 3344#64 + 960#64 = sp + 4304#64 by clear * -; bv_omega]
    sep_frame
  refine SepWP.weaken_pre hP3'
    (SepWP.mono (seg2_copy_uhat hb hbase s3 sp _ _ _ _ hpc3 hrun3 hsp3 hspA3 hcl3) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx26_f, hx27_f, hx28_f, hPf⟩
  exact ⟨hsp_f, hspA_f,
    hfp_f.trans (hfp3.trans (hfp2.trans hfp1)),
    hx26_f.trans (hx26_3.trans (hx26_2.trans hx26_1)),
    hx27_f.trans hx27_3,
    hx28_f.trans (hx28_3.trans (hx28_2.trans hx28_1)),
    Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2b

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymBridge

/-!
# `kyber_decapsulate` (`B06`): Configurable Symbolic Stepper Soundness

Proves 1-step (`sepWP_of_stepSymInst`) and `N`-step (`sepWP_of_runSymRange`) separation-logic
soundness for any relocation-free straight-line NEON slice `[wLo, wHi)` of `B06`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (ext_lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h
  simdMla8h
  simdMul8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem
  SepLoad128
  SepStore128
  step_ldpQ128
  step_ldrQ128
  step_stpQ128
  step_strQ128
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymBridge (
  not_rep8_eq_dup8x16
  rep8_eq_dup8x16
  setPC_self
  simdAdd_eval
  simdDup_eval
  simdMul_eval
  simdSqdmulh_eval
  simdSshr_eval
  simdSub_eval
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (blkPC06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  PolyLoc
  SExpr
  SepLoad128.spillSlice
  SepStore128.spillSlice
  SpillSliceMem
  SymCfg
  SymEnv
  SymGpr
  SymState
  evalSExpr
  evalSymGpr
  eval_smartMla
  eval_smartSub
  fetchWordTree06
  runSymRange
  smartMla
  smartSub
  stepSymInst
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SrcOptMem
  SymSpatial
  SymStateMatches
  blk06NoRelocInRange
  fetch_blk06_range
  gpr_poly_off
  gpr_poly_off16
  matches_advancePC
  matches_getFromZRBits
  matches_getGpr
  matches_orFpsr
  matches_setPC
  matches_store
  matches_writeGpr
  matches_writeVReg
  polyPtr
  sp_range_off
  symSpill40_eval_get
  symSpill40_eval_set
  symVec32_eval_get
  symVec32_eval_set
)

private theorem polyPtr_of_spPolyOff {cfg : SymCfg} {pOff : Nat} {sp : BitVec 64} {env : SymEnv}
    (hp : cfg.spPolyOff? = some pOff) :
    polyPtr cfg sp env = sp + BitVec.ofNat 64 pOff := by
  rcases cfg with ⟨_, _, pl, _⟩
  cases pl <;> simp [SymCfg.spPolyOff?, polyPtr] at hp ⊢
  subst hp; rfl

private theorem polyPtr_of_gpr {cfg : SymCfg} {rb : BitVec 5} {sp : BitVec 64} {env : SymEnv}
    (hp : cfg.polyLoc = .gpr rb) :
    polyPtr cfg sp env = env.gpr0 rb := by
  simp [polyPtr, hp]

theorem sepWP_of_stepSymInst {prog : Program} {tgt pc : BitVec 64} {cfg : SymCfg}
    {s : State} {sp : BitVec 64} {env : SymEnv} {st st' : SymState}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {inst : Instr}
    (hm : SymStateMatches sp env st s)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hstep : stepSymInst cfg inst st = some st')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      SymStateMatches sp env st' s' →
      SepWP prog tgt s' (SymSpatial cfg sp env st' F) post oom) :
    SepWP prog tgt s (SymSpatial cfg sp env st F) post oom := by
  unfold stepSymInst at hstep
  split at hstep <;> try contradiction
  · rename_i vt off
    have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
    have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
      simp [evalAddrMode, State.readReg64, hm.hsp]
    by_cases c1 : (cfg.spillLen ≤ 40 && cfg.spillOff ≤ off.toNat &&
        off.toNat < cfg.spillOff + 16 * cfg.spillLen && (off.toNat - cfg.spillOff) % 16 == 0) = true
    · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1
      obtain ⟨hk, ha⟩ := sp_range_off (sp := sp) c1.1.1.2 c1.1.2 c1.2
      exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr
        (SepLoad128.left (SepLoad128.spillSlice hk ha (symSpill40_eval_get env st.spill _ (by omega)))) rfl
        (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
    · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
      cases hp : cfg.spPolyOff? with
      | some pOff =>
        simp only [hp] at hstep
        by_cases c2 : (pOff ≤ off.toNat && off.toNat < pOff + 512 &&
            (off.toNat - pOff) % 16 == 0) = true
        · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c2
          obtain ⟨hk, ha⟩ := sp_range_off (sp := sp) (len := 32) c2.1.1 (by omega) c2.2
          have hld : SepLoad128 (sp + off) (Poly32Mem (polyPtr cfg sp env) (st.poly.eval env))
              (evalSExpr env (st.poly.get ((off.toNat - pOff) / 16))) := by
            rw [polyPtr_of_spPolyOff hp]
            exact SepLoad128.vec32 hk ha (symVec32_eval_get env st.poly _ hk)
          exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr
            (SepLoad128.right (SepLoad128.left hld)) rfl
            (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
        · simp only [Bool.eq_false_iff.mpr c2, Bool.false_eq_true, ↓reduceIte] at hstep
          by_cases c3 : (cfg.hasSrc && 14432 ≤ off.toNat && off.toNat < 14944 &&
              (off.toNat - 14432) % 16 == 0) = true
          · simp only [c3, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c3
            obtain ⟨hk, ha⟩ := sp_range_off (sp := sp) (base := 14432) (len := 32) c3.1.1.2 (by omega) c3.2
            have hld : SepLoad128 (sp + off) (SrcOptMem cfg.hasSrc sp env.src0)
                (evalSExpr env (.src ((off.toNat - 14432) / 16))) := by
              simp only [SrcOptMem, c3.1.1.1, ↓reduceIte, evalSExpr]
              exact SepLoad128.vec32 hk ha rfl
            exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr
              (SepLoad128.right (SepLoad128.right (SepLoad128.left hld))) rfl
              (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
          · simp [Bool.eq_false_iff.mpr c3] at hstep
      | none =>
        simp only [hp] at hstep
        by_cases c3 : (cfg.hasSrc && 14432 ≤ off.toNat && off.toNat < 14944 &&
            (off.toNat - 14432) % 16 == 0) = true
        · simp only [c3, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c3
          obtain ⟨hk, ha⟩ := sp_range_off (sp := sp) (base := 14432) (len := 32) c3.1.1.2 (by omega) c3.2
          have hld : SepLoad128 (sp + off) (SrcOptMem cfg.hasSrc sp env.src0)
              (evalSExpr env (.src ((off.toNat - 14432) / 16))) := by
            simp only [SrcOptMem, c3.1.1.1, ↓reduceIte, evalSExpr]
            exact SepLoad128.vec32 hk ha rfl
          exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr
            (SepLoad128.right (SepLoad128.right (SepLoad128.left hld))) rfl
            (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
        · simp [Bool.eq_false_iff.mpr c3] at hstep
  · rename_i vt off
    have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
    have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
      simp [evalAddrMode, State.readReg64, hm.hsp]
    by_cases c1 : (cfg.spillLen ≤ 40 && cfg.spillOff ≤ off.toNat &&
        off.toNat < cfg.spillOff + 16 * cfg.spillLen && (off.toNat - cfg.spillOff) % 16 == 0) = true
    · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1
      obtain ⟨hk, ha⟩ := sp_range_off (sp := sp) c1.1.1.2 c1.1.2 c1.2
      exact step_strQ128 hpc hrun hfetch hsp_chk haddr (hm.hvregs vt)
        (SepStore128.left (SepStore128.spillSlice hk c1.1.1.1 ha (symSpill40_eval_set env st.spill _ _).symm)) rfl
        (fun m' => hnext _ rfl hrun (matches_store hm _ st.poly _ m'))
    · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
      cases hp : cfg.spPolyOff? with
      | some pOff =>
        simp only [hp] at hstep
        by_cases c2 : (pOff ≤ off.toNat && off.toNat < pOff + 512 &&
            (off.toNat - pOff) % 16 == 0) = true
        · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c2
          obtain ⟨hk, ha⟩ := sp_range_off (sp := sp) (len := 32) c2.1.1 (by omega) c2.2
          have hst_mem : SepStore128 (sp + off) (evalSExpr env (st.vregs.get vt.toNat))
              (Poly32Mem (polyPtr cfg sp env) (st.poly.eval env))
              (Poly32Mem (polyPtr cfg sp env) ((st.poly.set ((off.toNat - pOff) / 16) (st.vregs.get vt.toNat)).eval env)) := by
            rw [polyPtr_of_spPolyOff hp]
            exact SepStore128.vec32 hk ha (symVec32_eval_set env st.poly _ _).symm
          exact step_strQ128 hpc hrun hfetch hsp_chk haddr (hm.hvregs vt)
            (SepStore128.right (SepStore128.left hst_mem)) rfl
            (fun m' => hnext _ rfl hrun (matches_store hm st.spill _ _ m'))
        · simp [Bool.eq_false_iff.mpr c2] at hstep
      | none => simp [hp] at hstep
  · rename_i vt rb off
    by_cases c : (rb != 31#5 && cfg.polyLoc == .gpr rb && st.gprs.get rb.toNat == .gpr0 rb 0#64 &&
        off.toNat < 512 && off.toNat % 16 == 0) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at c
      rcases c with ⟨⟨⟨⟨hrb, hpl⟩, hgr⟩, hhi⟩, hmod⟩
      have hptr : s.readReg64 (.gpr rb) = polyPtr cfg sp env := by
        rw [matches_getGpr hm hrb, hgr, evalSymGpr, BitVec.add_zero, polyPtr_of_gpr hpl]
      have haddr : evalAddrMode s (.Offset (.gpr rb) off) = (polyPtr cfg sp env + off, none) := by
        simp [evalAddrMode, hptr]
      obtain ⟨hk, ha⟩ := gpr_poly_off (ptr := polyPtr cfg sp env) hhi hmod
      exact step_ldrQ128 hpc hrun hfetch rfl haddr
        (SepLoad128.right (SepLoad128.left (SepLoad128.vec32 hk ha (symVec32_eval_get env st.poly _ hk)))) rfl
        (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i vt rb off
    by_cases c : (rb != 31#5 && cfg.polyLoc == .gpr rb && st.gprs.get rb.toNat == .gpr0 rb 0#64 &&
        off.toNat < 512 && off.toNat % 16 == 0) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at c
      rcases c with ⟨⟨⟨⟨hrb, hpl⟩, hgr⟩, hhi⟩, hmod⟩
      have hptr : s.readReg64 (.gpr rb) = polyPtr cfg sp env := by
        rw [matches_getGpr hm hrb, hgr, evalSymGpr, BitVec.add_zero, polyPtr_of_gpr hpl]
      have haddr : evalAddrMode s (.Offset (.gpr rb) off) = (polyPtr cfg sp env + off, none) := by
        simp [evalAddrMode, hptr]
      obtain ⟨hk, ha⟩ := gpr_poly_off (ptr := polyPtr cfg sp env) hhi hmod
      exact step_strQ128 hpc hrun hfetch rfl haddr (hm.hvregs vt)
        (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha (symVec32_eval_set env st.poly _ _).symm))) rfl
        (fun m' => hnext _ rfl hrun (matches_store hm st.spill _ _ m'))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i vt1 vt2 rb off
    by_cases c : (rb != 31#5 && cfg.polyLoc == .gpr rb && st.gprs.get rb.toNat == .gpr0 rb 0#64 &&
        off.toNat + 16 < 512 && off.toNat % 16 == 0) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at c
      rcases c with ⟨⟨⟨⟨hrb, hpl⟩, hgr⟩, hhi⟩, hmod⟩
      have hptr : s.readReg64 (.gpr rb) = polyPtr cfg sp env := by
        rw [matches_getGpr hm hrb, hgr, evalSymGpr, BitVec.add_zero, polyPtr_of_gpr hpl]
      have haddr : evalAddrMode s (.Offset (.gpr rb) off) = (polyPtr cfg sp env + off, none) := by
        simp [evalAddrMode, hptr]
      obtain ⟨hk, ha⟩ := gpr_poly_off (ptr := polyPtr cfg sp env) (by omega) hmod
      obtain ⟨hk1, ha1⟩ := gpr_poly_off16 (ptr := polyPtr cfg sp env) hhi hmod
      exact step_ldpQ128 hpc hrun hfetch rfl haddr rfl
        (SepLoad128.right (SepLoad128.left (SepLoad128.vec32 hk ha (symVec32_eval_get env st.poly _ hk))))
        (SepLoad128.right (SepLoad128.left (SepLoad128.vec32 hk1 ha1.symm (symVec32_eval_get env st.poly _ hk1)))) rfl
        (hnext _ rfl hrun (matches_setPC (matches_writeVReg (matches_writeVReg hm vt1 _) vt2 _) _))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i vt1 vt2 rb off
    by_cases c : (rb != 31#5 && cfg.polyLoc == .gpr rb && st.gprs.get rb.toNat == .gpr0 rb 0#64 &&
        off.toNat + 16 < 512 && off.toNat % 16 == 0) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at c
      rcases c with ⟨⟨⟨⟨hrb, hpl⟩, hgr⟩, hhi⟩, hmod⟩
      have hptr : s.readReg64 (.gpr rb) = polyPtr cfg sp env := by
        rw [matches_getGpr hm hrb, hgr, evalSymGpr, BitVec.add_zero, polyPtr_of_gpr hpl]
      have haddr : evalAddrMode s (.Offset (.gpr rb) off) = (polyPtr cfg sp env + off, none) := by
        simp [evalAddrMode, hptr]
      obtain ⟨hk, ha⟩ := gpr_poly_off (ptr := polyPtr cfg sp env) (by omega) hmod
      obtain ⟨hk1, ha1⟩ := gpr_poly_off16 (ptr := polyPtr cfg sp env) hhi hmod
      exact step_stpQ128 hpc hrun hfetch rfl haddr rfl (hm.hvregs vt1) (hm.hvregs vt2)
        (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha (symVec32_eval_set env st.poly _ _).symm)))
        (SepStore128.right (SepStore128.left (SepStore128.vec32 hk1 ha1.symm (symVec32_eval_set env _ _ _).symm))) rfl
        (fun m' => hnext _ rfl hrun (matches_store hm st.spill _ _ m'))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i rd imm16
    by_cases hrd : (rd != 31#5) = true
    · simp only [hrd, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      have hrd_ne : rd ≠ 31#5 := bne_iff_ne.mp hrd
      refine SepWP.step_pure hpc hrun hfetch (s' := (s.writeReg64 (.gpr rd) (imm16.zeroExtend 64)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, execMoveWide]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrd_ne _ rfl))
    · simp [Bool.eq_false_iff.mpr hrd] at hstep
  · rename_i rd imm12 shift12
    by_cases hrd : (rd != 31#5) = true
    · simp only [hrd, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      have hrd_ne : rd ≠ 31#5 := bne_iff_ne.mp hrd
      set off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
      refine SepWP.step_pure hpc hrun hfetch (s' := (s.writeReg64 (.gpr rd) (sp + off64)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.readReg64, hm.hsp, off64]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrd_ne _ rfl))
    · simp [Bool.eq_false_iff.mpr hrd] at hstep
  · rename_i rd rn imm12 shift12
    by_cases hc : (rd != 31#5 && rn != 31#5) = true
    · simp only [hc, ↓reduceIte] at hstep
      simp only [Bool.and_eq_true, bne_iff_ne] at hc; rcases hc with ⟨hrd_ne, hrn_ne⟩
      set off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
      cases hgn : st.gprs.get rn.toNat with
      | gpr0 r0 o0 =>
        simp only [hgn, Option.some.injEq] at hstep; subst hstep
        refine SepWP.step_pure hpc hrun hfetch
          (s' := (s.writeReg64 (.gpr rd) (s.readReg64 (.gpr rn) + off64)).advancePC) ?_ rfl ?_
        · rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, off64]
        · exact hnext _ (by simp [State.advancePC, hpc]) hrun
            (matches_advancePC (matches_writeGpr hm hrd_ne _ (by rw [matches_getGpr hm hrn_ne, hgn, evalSymGpr, evalSymGpr, BitVec.add_assoc])))
      | spAdd o0 =>
        simp only [hgn, Option.some.injEq] at hstep; subst hstep
        refine SepWP.step_pure hpc hrun hfetch
          (s' := (s.writeReg64 (.gpr rd) (s.readReg64 (.gpr rn) + off64)).advancePC) ?_ rfl ?_
        · rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, off64]
        · exact hnext _ (by simp [State.advancePC, hpc]) hrun
            (matches_advancePC (matches_writeGpr hm hrd_ne _ (by rw [matches_getGpr hm hrn_ne, hgn, evalSymGpr, evalSymGpr, BitVec.add_assoc])))
      | const64 v =>
        simp only [hgn, Option.some.injEq] at hstep; subst hstep
        refine SepWP.step_pure hpc hrun hfetch
          (s' := (s.writeReg64 (.gpr rd) (s.readReg64 (.gpr rn) + off64)).advancePC) ?_ rfl ?_
        · rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, off64]
        · exact hnext _ (by simp [State.advancePC, hpc]) hrun
            (matches_advancePC (matches_writeGpr hm hrd_ne _ (by rw [matches_getGpr hm hrn_ne, hgn, evalSymGpr, evalSymGpr])))
      | addGpr0 _ _ => simp [hgn] at hstep
    · simp [Bool.eq_false_iff.mpr hc] at hstep
  · rename_i rd
    by_cases hrd : (rd != 31#5) = true
    · simp only [hrd, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      have hrd_ne : rd ≠ 31#5 := bne_iff_ne.mp hrd
      refine SepWP.step_pure hpc hrun hfetch (s' := (s.writeReg64 (.gpr rd) 0#64).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execLogicalShift, shiftVal, shift64, evalLogical, State.readReg]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrd_ne _ rfl))
    · simp [Bool.eq_false_iff.mpr hrd] at hstep
  · rename_i rd rm
    by_cases hc : (rd != 31#5 && rm != 31#5) = true
    · simp only [hc, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, bne_iff_ne] at hc; rcases hc with ⟨hrd_ne, hrm_ne⟩
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) (s.readReg64 (.gpr rm))).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execLogicalShift, shiftVal, shift64, evalLogical, State.readReg]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrd_ne _ (matches_getGpr hm hrm_ne)))
    · simp [Bool.eq_false_iff.mpr hc] at hstep
  · rename_i rd rn rm
    by_cases hc : (rd != 31#5 && rn != 31#5 && rm != 31#5) = true
    · simp only [hc, ↓reduceIte] at hstep
      simp only [Bool.and_eq_true, bne_iff_ne] at hc; rcases hc with ⟨⟨hrd_ne, hrn_ne⟩, hrm_ne⟩
      generalize hgn : st.gprs.get rn.toNat = gn at hstep
      generalize hgm : st.gprs.get rm.toNat = gm at hstep
      split at hstep <;> try contradiction
      rename_i r1 r2
      simp only [Option.some.injEq] at hstep; subst hstep
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) (s.readReg64 (.gpr rn) + s.readReg64 (.gpr rm))).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execAddSubShift, shiftVal, shift64, State.readReg]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrd_ne _ (by
            rw [matches_getGpr hm hrn_ne, matches_getGpr hm hrm_ne, hgn, hgm,
                evalSymGpr, evalSymGpr, evalSymGpr, BitVec.add_zero, BitVec.add_zero])))
    · simp [Bool.eq_false_iff.mpr hc] at hstep
  · rename_i rn rd
    by_cases hrn : (rn != 31#5) = true
    · simp only [hrn, ↓reduceIte] at hstep
      have hrn_ne : rn ≠ 31#5 := bne_iff_ne.mp hrn
      cases hg : st.gprs.get rn.toNat with
      | const64 v =>
        simp only [hg, Option.some.injEq] at hstep; subst hstep
        refine SepWP.step_pure hpc hrun hfetch
          (s' := (s.writeVReg128 rd (evalSExpr env (.const (v.truncate 16)))).advancePC) ?_ rfl ?_
        · rw [setPC_self hpc]
          have hzr : s.readReg64 (Reg.fromZRBits rn) = v := by
            rw [matches_getFromZRBits hm hrn_ne, hg, evalSymGpr]
          simp [Program.evalInst, execInstWithSvc, hzr, simdDup_eval v, evalSExpr]
        · exact hnext _ (by simp [State.advancePC, hpc]) hrun
            (matches_advancePC (matches_writeVReg hm rd (.const (v.truncate 16))))
      | gpr0 _ _ => simp [hg] at hstep
      | spAdd _ => simp [hg] at hstep
      | addGpr0 _ _ => simp [hg] at hstep
    · simp [Bool.eq_false_iff.mpr hrn] at hstep
  · rename_i u sz rm opcode rn rd
    by_cases c1 : (!u && sz == 2#2 && opcode == 0b00011#5 && rm == rn) = true
    · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c1
      rcases c1 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeVReg128 rd (evalSExpr env (st.vregs.get rm.toNat))).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hm.hvregs rm]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
    · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
      by_cases c2 : (!u && sz == 1#2 && opcode == 0b10000#5) = true
      · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c2
        rcases c2 with ⟨⟨rfl, rfl⟩, rfl⟩
        refine SepWP.step_pure hpc hrun hfetch
          (s' := (s.writeVReg128 rd (evalSExpr env (.add (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)))).advancePC) ?_ rfl ?_
        · rw [setPC_self hpc]
          simp [Program.evalInst, execInstWithSvc, hm.hvregs rn, hm.hvregs rm,
            simdAdd_eval (evalSExpr env (st.vregs.get rn.toNat)) (evalSExpr env (st.vregs.get rm.toNat)), evalSExpr]
        · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
      · simp only [Bool.eq_false_iff.mpr c2, Bool.false_eq_true, ↓reduceIte] at hstep
        by_cases c3 : (u && sz == 1#2 && opcode == 0b10000#5) = true
        · simp only [c3, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          simp only [Bool.and_eq_true, beq_iff_eq] at c3
          rcases c3 with ⟨⟨rfl, rfl⟩, rfl⟩
          refine SepWP.step_pure hpc hrun hfetch
            (s' := (s.writeVReg128 rd (evalSExpr env (smartSub (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)))).advancePC) ?_ rfl ?_
          · rw [setPC_self hpc]
            simp [Program.evalInst, execInstWithSvc, hm.hvregs rn, hm.hvregs rm,
              simdSub_eval (evalSExpr env (st.vregs.get rn.toNat)) (evalSExpr env (st.vregs.get rm.toNat)), eval_smartSub]
          · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
        · simp only [Bool.eq_false_iff.mpr c3, Bool.false_eq_true, ↓reduceIte] at hstep
          by_cases c4 : (!u && sz == 1#2 && opcode == 0b10011#5) = true
          · simp only [c4, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
            simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c4
            rcases c4 with ⟨⟨rfl, rfl⟩, rfl⟩
            refine SepWP.step_pure hpc hrun hfetch
              (s' := (s.writeVReg128 rd (evalSExpr env (.mul (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)))).advancePC) ?_ rfl ?_
            · rw [setPC_self hpc]
              simp [Program.evalInst, execInstWithSvc, evalSimdThreeSameExt, evalSimdThreeSameExtSatFlags,
                hm.hvregs rn, hm.hvregs rm,
                simdMul_eval (evalSExpr env (st.vregs.get rn.toNat)) (evalSExpr env (st.vregs.get rm.toNat)), evalSExpr]
            · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
          · simp only [Bool.eq_false_iff.mpr c4, Bool.false_eq_true, ↓reduceIte] at hstep
            by_cases c5 : (!u && sz == 1#2 && opcode == 0b10010#5) = true
            · simp only [c5, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
              simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c5
              rcases c5 with ⟨⟨rfl, rfl⟩, rfl⟩
              refine SepWP.step_pure hpc hrun hfetch
                (s' := (s.writeVReg128 rd (evalSExpr env (smartMla (st.vregs.get rd.toNat) (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)))).advancePC) ?_ rfl ?_
              · rw [setPC_self hpc]
                have hmla : ∀ vd vn vm : BitVec 128, simdAdd8h vd (simdMul8h vn vm) = simdMla8h vd vn vm := by
                  intro vd vn vm; apply ext_lane16; intro i; simp
                simp [Program.evalInst, execInstWithSvc, evalSimdThreeSameExt, evalSimdThreeSameExtSatFlags,
                  hm.hvregs rd, hm.hvregs rn, hm.hvregs rm,
                  simdMul_eval (evalSExpr env (st.vregs.get rn.toNat)) (evalSExpr env (st.vregs.get rm.toNat)),
                  simdAdd_eval (evalSExpr env (st.vregs.get rd.toNat))
                    (simdMul8h (evalSExpr env (st.vregs.get rn.toNat)) (evalSExpr env (st.vregs.get rm.toNat))),
                  hmla, eval_smartMla]
              · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
            · simp only [Bool.eq_false_iff.mpr c5, Bool.false_eq_true, ↓reduceIte] at hstep
              by_cases c6 : (!u && sz == 1#2 && opcode == 0b10110#5) = true
              · simp only [c6, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
                simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c6
                rcases c6 with ⟨⟨rfl, rfl⟩, rfl⟩
                set fl := if anyZipSimdLane true 16 (s.readVReg128 rn) (s.readVReg128 rm)
                  (fun a b => aslSignedSatFlag 16 (aslRShr (2 * simdLaneSInt 16 a * simdLaneSInt 16 b) 16 false))
                  then fpsrQC else 0#32
                refine SepWP.step_pure hpc hrun hfetch
                  (s' := ((s.writeVReg128 rd (evalSExpr env (.sqdmulh (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)))).orFpsr fl).advancePC) ?_ rfl ?_
                · rw [setPC_self hpc]
                  simp [Program.evalInst, execInstWithSvc, evalSimdThreeSameExt, evalSimdThreeSameExtSatFlags,
                    hm.hvregs rn, hm.hvregs rm,
                    simdSqdmulh_eval (evalSExpr env (st.vregs.get rn.toNat)) (evalSExpr env (st.vregs.get rm.toNat)),
                    evalSExpr, fl]
                · exact hnext _ (by simp [State.advancePC, State.orFpsr, hpc]) hrun
                    (matches_advancePC (matches_orFpsr (matches_writeVReg hm rd _) fl))
              · simp [Bool.eq_false_iff.mpr c6] at hstep
  · rename_i op immh immb opcode rn rd
    by_cases c1 : (immh == 0#4 && opcode == 0b10000#5) = true
    · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, beq_iff_eq] at c1; rcases c1 with ⟨rfl, rfl⟩
      set c16 := (immb ++ rn).zeroExtend 16
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeVReg128 rd (evalSExpr env (.const (if op then ~~~c16 else c16)))).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        cases op
        · simp [Program.evalInst, execInstWithSvc, c16, evalSExpr]
          rw [rep8_eq_dup8x16]
        · simp [Program.evalInst, execInstWithSvc, evalSimdModImmExt, advSimdExpandImm, c16, evalSExpr]
          rw [not_rep8_eq_dup8x16]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
    · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
      by_cases c2 : (immh == 0#4 && opcode == 0b10100#5) = true
      · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        simp only [Bool.and_eq_true, beq_iff_eq] at c2; rcases c2 with ⟨rfl, rfl⟩
        set c16 := ((immb ++ rn).zeroExtend 16) <<< 8
        refine SepWP.step_pure hpc hrun hfetch
          (s' := (s.writeVReg128 rd (evalSExpr env (.const (if op then ~~~c16 else c16)))).advancePC) ?_ rfl ?_
        · rw [setPC_self hpc]
          cases op
          · simp [Program.evalInst, execInstWithSvc, c16, evalSExpr]
            rw [rep8_eq_dup8x16]
          · simp [Program.evalInst, execInstWithSvc, evalSimdModImmExt, advSimdExpandImm, c16, evalSExpr]
            rw [not_rep8_eq_dup8x16]
        · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
      · simp only [Bool.eq_false_iff.mpr c2, Bool.false_eq_true, ↓reduceIte] at hstep
        by_cases c3 : (!op && immh == 0b0011#4 && immb == 0b111#3 && opcode == 0b00000#5) = true
        · simp only [c3, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c3
          rcases c3 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
          refine SepWP.step_pure hpc hrun hfetch
            (s' := (s.writeVReg128 rd (evalSExpr env (.sshr (st.vregs.get rn.toNat) 1))).advancePC) ?_ rfl ?_
          · rw [setPC_self hpc]
            simp [Program.evalInst, execInstWithSvc, evalSimdImmShiftNonZeroExt,
              evalSimdImmShiftNonZeroExtSatFlags, hm.hvregs rn, simdSshr_eval _ _ 1 (by omega) (by omega), evalSExpr]
          · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
        · simp only [Bool.eq_false_iff.mpr c3, Bool.false_eq_true, ↓reduceIte] at hstep
          by_cases c4 : (!op && immh == 0b0010#4 && immb == 0b101#3 && opcode == 0b00000#5) = true
          · simp only [c4, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
            simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c4
            rcases c4 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
            refine SepWP.step_pure hpc hrun hfetch
              (s' := (s.writeVReg128 rd (evalSExpr env (.sshr (st.vregs.get rn.toNat) 11))).advancePC) ?_ rfl ?_
            · rw [setPC_self hpc]
              simp [Program.evalInst, execInstWithSvc, evalSimdImmShiftNonZeroExt,
                evalSimdImmShiftNonZeroExtSatFlags, hm.hvregs rn, simdSshr_eval _ _ 11 (by omega) (by omega), evalSExpr]
            · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
          · simp [Bool.eq_false_iff.mpr c4] at hstep

theorem sepWP_of_runSymRange [MlKemPlacement] {b : BitVec 64} {cfg : SymCfg} {sp : BitVec 64}
    {env : SymEnv} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {wLo wHi : Nat} (count w : Nat) {st stEnd : SymState} {s : State}
    (hnr : blk06NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 13979)
    (hlo : wLo ≤ w) (hhi : w + count ≤ wHi)
    (hrun_sym : runSymRange cfg w count st = some stEnd)
    (hm : SymStateMatches sp env st s)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hpost : ∀ sf : State, sf.pc = b + BitVec.ofNat 64 (4 * (w + count)) →
      sf.status = .Running → SymStateMatches sp env stEnd sf →
      post sf (SymSpatial cfg sp env stEnd F)) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (b + BitVec.ofNat 64 (4 * (w + count))) s (SymSpatial cfg sp env st F) post oom := by
  induction count generalizing w st s with
  | zero =>
    simp only [runSymRange, Option.some.injEq] at hrun_sym; subst hrun_sym
    have hpc0 : s.pc = b + BitVec.ofNat 64 (4 * (w + 0)) := by simpa using hpc
    exact SepWP.done hpc0 hrun (hpost s hpc0 hrun hm)
  | succ n ih =>
    unfold runSymRange at hrun_sym
    cases hfw : fetchWordTree06 w with
    | none => simp [hfw] at hrun_sym
    | some inst =>
      simp only [hfw] at hrun_sym
      cases hst : stepSymInst cfg inst st with
      | none => simp [hst] at hrun_sym
      | some st1 =>
        simp only [hst] at hrun_sym
        have hfetch := fetch_blk06_range (b := b) hnr hmax hlo (by omega) hfw
        refine sepWP_of_stepSymInst hm hpc hrun hfetch hst ?_
        intro s' hpc' hrun' hm'
        have hpc_eq : b + BitVec.ofNat 64 (4 * w) + 4#64 = b + BitVec.ofNat 64 (4 * (w + 1)) := by
          rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        rw [hpc_eq] at hpc'
        have hend_eq : 4 * (w + (n + 1)) = 4 * (w + 1 + n) := by omega
        rw [hend_eq]
        exact ih (w + 1) (by omega) (by omega) hrun_sym hm' hpc' hrun'
          (fun sf h1 h2 h3 => hpost sf (by rwa [hend_eq]) h2 h3)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym

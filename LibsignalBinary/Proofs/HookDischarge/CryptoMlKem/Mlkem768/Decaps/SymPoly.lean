/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymBridge

/-!
# `decapsulate_compressed_key` (`B04`) — Symbolic Stepper Soundness (`SymPoly`)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (ext_lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (simdAdd8h simdMul8h simdMla8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (step_ldrQ128 step_strQ128 step_ldpQ128 step_stpQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymBridge
  (rep8_eq_dup8x16 not_rep8_eq_dup8x16 simdDup_eval simdSshr_eval simdSqdmulh_eval
   simdAdd_eval simdSub_eval simdMul_eval setPC_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (blkPC04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
  (SymCfg SymState smartMla smartSub fetchWordTree04 stepSymInst runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval
  (SymEnv evalSExpr evalSymGpr evalSymPState eval_smartMla eval_smartSub
   SymSpatial SymStateMatches)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyBridge
  (InSymWord04 fetch_blk04_sym fromZRBits_lt31
   matches_writeVReg matches_writeGpr matches_setPState matches_orFpsr
   matches_setPC matches_advancePC matches_store
   ptr_off_k ptr_off_k16 base_off_k base_off_k16
   load_polyReg store_polyReg load_polySp store_polySp
   load_spill13 store_spill13 load_spill6 store_spill6 load_spill21 store_spill21 load_inPoly)

/-! ## 1. `sp`-Relative Load & Store Step Helpers -/

private theorem step_ldrSp {prog : Program} {tgt pc sp polyPtr : BitVec 64}
    {cfg : SymCfg} {env : SymEnv} {st st' : SymState} {s : State}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt : BitVec 5} {off : BitVec 64}
    (hm : SymStateMatches cfg sp polyPtr env st s)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt (.Offset .sp off)))
    (hstep : stepSymInst cfg (.ldrSimd .Q128 vt (.Offset .sp off)) st = some st')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      SymStateMatches cfg sp polyPtr env st' s' →
      SepWP prog tgt s' (SymSpatial cfg sp polyPtr env st' F) post oom) :
    SepWP prog tgt s (SymSpatial cfg sp polyPtr env st F) post oom := by
  have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
  have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
    simp [evalAddrMode, State.readReg64, hm.hsp]
  dsimp only [stepSymInst] at hstep
  by_cases c1 : (cfg.spillMode == .s40 && decide (1616 ≤ off.toNat) && decide (off.toNat < 1824) && (off.toNat - 1616) % 16 == 0) = true
  · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1
    obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1616 13 c1.1.1.2 c1.1.2 c1.2
    exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr (load_spill13 c1.1.1.1 hk ha) rfl
      (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
  · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
    by_cases c2 : ((cfg.spillMode == .s27 || cfg.spillMode == .s40) && decide (1824 ≤ off.toNat) && decide (off.toNat < 1920) && (off.toNat - 1824) % 16 == 0) = true
    · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at c2
      obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1824 6 c2.1.1.2 c2.1.2 c2.2
      exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr (load_spill6 c2.1.1.1 hk ha) rfl
        (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
    · simp only [Bool.eq_false_iff.mpr c2, Bool.false_eq_true, ↓reduceIte] at hstep
      by_cases c3 : ((cfg.spillMode != .none) && decide (1920 ≤ off.toNat) && decide (off.toNat < 2256) && (off.toNat - 1920) % 16 == 0) = true
      · simp only [c3, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at c3
        obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1920 21 c3.1.1.2 c3.1.2 c3.2
        exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr (load_spill21 c3.1.1.1 hk ha) rfl
          (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
      · simp only [Bool.eq_false_iff.mpr c3, Bool.false_eq_true, ↓reduceIte] at hstep
        by_cases c4 : (cfg.hasInPoly && decide (11856 ≤ off.toNat) && decide (off.toNat < 12368) && (off.toNat - 11856) % 16 == 0) = true
        · simp only [c4, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c4
          obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 11856 32 c4.1.1.2 c4.1.2 c4.2
          exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr (load_inPoly c4.1.1.1 hk ha) rfl
            (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
        · simp only [Bool.eq_false_iff.mpr c4, Bool.false_eq_true, ↓reduceIte] at hstep
          simp only [Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hstep
          rcases hstep with ⟨⟨⟨⟨hpr, hlo⟩, hhi⟩, hm16⟩, rfl⟩
          obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 20704 32 hlo hhi hm16
          exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr (load_polySp hpr hk ha) rfl
            (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))

private theorem step_strSp {prog : Program} {tgt pc sp polyPtr : BitVec 64}
    {cfg : SymCfg} {env : SymEnv} {st st' : SymState} {s : State}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt : BitVec 5} {off : BitVec 64}
    (hm : SymStateMatches cfg sp polyPtr env st s)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp off)))
    (hstep : stepSymInst cfg (.strSimd .Q128 vt (.Offset .sp off)) st = some st')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      SymStateMatches cfg sp polyPtr env st' s' →
      SepWP prog tgt s' (SymSpatial cfg sp polyPtr env st' F) post oom) :
    SepWP prog tgt s (SymSpatial cfg sp polyPtr env st F) post oom := by
  have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
  have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
    simp [evalAddrMode, State.readReg64, hm.hsp]
  dsimp only [stepSymInst] at hstep
  by_cases c1 : (cfg.spillMode == .s40 && decide (1616 ≤ off.toNat) && decide (off.toNat < 1824) && (off.toNat - 1616) % 16 == 0) = true
  · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1
    obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1616 13 c1.1.1.2 c1.1.2 c1.2
    exact step_strQ128 hpc hrun hfetch hsp_chk haddr (hm.hvregs vt) (store_spill13 c1.1.1.1 hk ha) rfl
      (fun m' => hnext _ rfl hrun (matches_store hm _ st.spill6 st.spill21 st.poly _ m'))
  · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
    by_cases c2 : ((cfg.spillMode == .s27 || cfg.spillMode == .s40) && decide (1824 ≤ off.toNat) && decide (off.toNat < 1920) && (off.toNat - 1824) % 16 == 0) = true
    · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at c2
      obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1824 6 c2.1.1.2 c2.1.2 c2.2
      exact step_strQ128 hpc hrun hfetch hsp_chk haddr (hm.hvregs vt) (store_spill6 c2.1.1.1 hk ha) rfl
        (fun m' => hnext _ rfl hrun (matches_store hm st.spill13 _ st.spill21 st.poly _ m'))
    · simp only [Bool.eq_false_iff.mpr c2, Bool.false_eq_true, ↓reduceIte] at hstep
      by_cases c3 : ((cfg.spillMode != .none) && decide (1920 ≤ off.toNat) && decide (off.toNat < 2256) && (off.toNat - 1920) % 16 == 0) = true
      · simp only [c3, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at c3
        obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1920 21 c3.1.1.2 c3.1.2 c3.2
        exact step_strQ128 hpc hrun hfetch hsp_chk haddr (hm.hvregs vt) (store_spill21 c3.1.1.1 hk ha) rfl
          (fun m' => hnext _ rfl hrun (matches_store hm st.spill13 st.spill6 _ st.poly _ m'))
      · simp only [Bool.eq_false_iff.mpr c3, Bool.false_eq_true, ↓reduceIte] at hstep
        simp only [Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hstep
        rcases hstep with ⟨⟨⟨⟨hpr, hlo⟩, hhi⟩, hm16⟩, rfl⟩
        obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 20704 32 hlo hhi hm16
        exact step_strQ128 hpc hrun hfetch hsp_chk haddr (hm.hvregs vt) (store_polySp hpr hk ha) rfl
          (fun m' => hnext _ rfl hrun (matches_store hm st.spill13 st.spill6 st.spill21 _ _ m'))

private theorem step_ldpSp {prog : Program} {tgt pc sp polyPtr : BitVec 64}
    {cfg : SymCfg} {env : SymEnv} {st st' : SymState} {s : State}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt1 vt2 : BitVec 5} {off : BitVec 64}
    (hm : SymStateMatches cfg sp polyPtr env st s)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .Q128 vt1 vt2 (.Offset .sp off)))
    (hstep : stepSymInst cfg (.ldpSimd .Q128 vt1 vt2 (.Offset .sp off)) st = some st')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      SymStateMatches cfg sp polyPtr env st' s' →
      SepWP prog tgt s' (SymSpatial cfg sp polyPtr env st' F) post oom) :
    SepWP prog tgt s (SymSpatial cfg sp polyPtr env st F) post oom := by
  have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
  have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
    simp [evalAddrMode, State.readReg64, hm.hsp]
  dsimp only [stepSymInst] at hstep
  by_cases c1 : (cfg.spillMode == .s40 && decide (1616 ≤ off.toNat) && decide (off.toNat + 16 < 1824) && (off.toNat - 1616) % 16 == 0) = true
  · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1
    obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1616 13 c1.1.1.2 (by omega) c1.2
    obtain ⟨hk1, ha1⟩ := base_off_k16 (sp := sp) (off := off) 1616 13 c1.1.1.2 c1.1.2 c1.2
    exact step_ldpQ128 hpc hrun hfetch hsp_chk haddr rfl
      (load_spill13 c1.1.1.1 hk ha) (load_spill13 c1.1.1.1 hk1 ha1.symm) rfl
      (hnext _ rfl hrun (matches_setPC (matches_writeVReg (matches_writeVReg hm vt1 _) vt2 _) _))
  · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
    by_cases c2 : ((cfg.spillMode == .s27 || cfg.spillMode == .s40) && decide (1824 ≤ off.toNat) && decide (off.toNat + 16 < 1920) && (off.toNat - 1824) % 16 == 0) = true
    · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at c2
      obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1824 6 c2.1.1.2 (by omega) c2.2
      obtain ⟨hk1, ha1⟩ := base_off_k16 (sp := sp) (off := off) 1824 6 c2.1.1.2 c2.1.2 c2.2
      exact step_ldpQ128 hpc hrun hfetch hsp_chk haddr rfl
        (load_spill6 c2.1.1.1 hk ha) (load_spill6 c2.1.1.1 hk1 ha1.symm) rfl
        (hnext _ rfl hrun (matches_setPC (matches_writeVReg (matches_writeVReg hm vt1 _) vt2 _) _))
    · simp only [Bool.eq_false_iff.mpr c2, Bool.false_eq_true, ↓reduceIte] at hstep
      by_cases c3 : ((cfg.spillMode != .none) && decide (1920 ≤ off.toNat) && decide (off.toNat + 16 < 2256) && (off.toNat - 1920) % 16 == 0) = true
      · simp only [c3, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at c3
        obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1920 21 c3.1.1.2 (by omega) c3.2
        obtain ⟨hk1, ha1⟩ := base_off_k16 (sp := sp) (off := off) 1920 21 c3.1.1.2 c3.1.2 c3.2
        exact step_ldpQ128 hpc hrun hfetch hsp_chk haddr rfl
          (load_spill21 c3.1.1.1 hk ha) (load_spill21 c3.1.1.1 hk1 ha1.symm) rfl
          (hnext _ rfl hrun (matches_setPC (matches_writeVReg (matches_writeVReg hm vt1 _) vt2 _) _))
      · simp only [Bool.eq_false_iff.mpr c3, Bool.false_eq_true, ↓reduceIte] at hstep
        by_cases c4 : (cfg.hasInPoly && decide (11856 ≤ off.toNat) && decide (off.toNat + 16 < 12368) && (off.toNat - 11856) % 16 == 0) = true
        · simp only [c4, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c4
          obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 11856 32 c4.1.1.2 (by omega) c4.2
          obtain ⟨hk1, ha1⟩ := base_off_k16 (sp := sp) (off := off) 11856 32 c4.1.1.2 c4.1.2 c4.2
          exact step_ldpQ128 hpc hrun hfetch hsp_chk haddr rfl
            (load_inPoly c4.1.1.1 hk ha) (load_inPoly c4.1.1.1 hk1 ha1.symm) rfl
            (hnext _ rfl hrun (matches_setPC (matches_writeVReg (matches_writeVReg hm vt1 _) vt2 _) _))
        · simp only [Bool.eq_false_iff.mpr c4, Bool.false_eq_true, ↓reduceIte] at hstep
          simp only [Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hstep
          rcases hstep with ⟨⟨⟨⟨hpr, hlo⟩, hhi⟩, hm16⟩, rfl⟩
          obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 20704 32 hlo (by omega) hm16
          obtain ⟨hk1, ha1⟩ := base_off_k16 (sp := sp) (off := off) 20704 32 hlo hhi hm16
          exact step_ldpQ128 hpc hrun hfetch hsp_chk haddr rfl
            (load_polySp hpr hk ha) (load_polySp hpr hk1 ha1.symm) rfl
            (hnext _ rfl hrun (matches_setPC (matches_writeVReg (matches_writeVReg hm vt1 _) vt2 _) _))

private theorem step_stpSp {prog : Program} {tgt pc sp polyPtr : BitVec 64}
    {cfg : SymCfg} {env : SymEnv} {st st' : SymState} {s : State}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt1 vt2 : BitVec 5} {off : BitVec 64}
    (hm : SymStateMatches cfg sp polyPtr env st s)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 vt1 vt2 (.Offset .sp off)))
    (hstep : stepSymInst cfg (.stpSimd .Q128 vt1 vt2 (.Offset .sp off)) st = some st')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      SymStateMatches cfg sp polyPtr env st' s' →
      SepWP prog tgt s' (SymSpatial cfg sp polyPtr env st' F) post oom) :
    SepWP prog tgt s (SymSpatial cfg sp polyPtr env st F) post oom := by
  have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
  have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
    simp [evalAddrMode, State.readReg64, hm.hsp]
  dsimp only [stepSymInst] at hstep
  by_cases c1 : (cfg.spillMode == .s40 && decide (1616 ≤ off.toNat) && decide (off.toNat + 16 < 1824) && (off.toNat - 1616) % 16 == 0) = true
  · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1
    obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1616 13 c1.1.1.2 (by omega) c1.2
    obtain ⟨hk1, ha1⟩ := base_off_k16 (sp := sp) (off := off) 1616 13 c1.1.1.2 c1.1.2 c1.2
    exact step_stpQ128 hpc hrun hfetch hsp_chk haddr rfl (hm.hvregs vt1) (hm.hvregs vt2)
      (store_spill13 c1.1.1.1 hk ha)
      (store_spill13 (st := { st with spill13 := st.spill13.set _ _ }) c1.1.1.1 hk1 ha1.symm) rfl
      (fun m' => hnext _ rfl hrun (matches_store hm _ st.spill6 st.spill21 st.poly _ m'))
  · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
    by_cases c2 : ((cfg.spillMode == .s27 || cfg.spillMode == .s40) && decide (1824 ≤ off.toNat) && decide (off.toNat + 16 < 1920) && (off.toNat - 1824) % 16 == 0) = true
    · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at c2
      obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1824 6 c2.1.1.2 (by omega) c2.2
      obtain ⟨hk1, ha1⟩ := base_off_k16 (sp := sp) (off := off) 1824 6 c2.1.1.2 c2.1.2 c2.2
      exact step_stpQ128 hpc hrun hfetch hsp_chk haddr rfl (hm.hvregs vt1) (hm.hvregs vt2)
        (store_spill6 c2.1.1.1 hk ha)
        (store_spill6 (st := { st with spill6 := st.spill6.set _ _ }) c2.1.1.1 hk1 ha1.symm) rfl
        (fun m' => hnext _ rfl hrun (matches_store hm st.spill13 _ st.spill21 st.poly _ m'))
    · simp only [Bool.eq_false_iff.mpr c2, Bool.false_eq_true, ↓reduceIte] at hstep
      by_cases c3 : ((cfg.spillMode != .none) && decide (1920 ≤ off.toNat) && decide (off.toNat + 16 < 2256) && (off.toNat - 1920) % 16 == 0) = true
      · simp only [c3, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at c3
        obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 1920 21 c3.1.1.2 (by omega) c3.2
        obtain ⟨hk1, ha1⟩ := base_off_k16 (sp := sp) (off := off) 1920 21 c3.1.1.2 c3.1.2 c3.2
        exact step_stpQ128 hpc hrun hfetch hsp_chk haddr rfl (hm.hvregs vt1) (hm.hvregs vt2)
          (store_spill21 c3.1.1.1 hk ha)
          (store_spill21 (st := { st with spill21 := st.spill21.set _ _ }) c3.1.1.1 hk1 ha1.symm) rfl
          (fun m' => hnext _ rfl hrun (matches_store hm st.spill13 st.spill6 _ st.poly _ m'))
      · simp only [Bool.eq_false_iff.mpr c3, Bool.false_eq_true, ↓reduceIte] at hstep
        simp only [Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hstep
        rcases hstep with ⟨⟨⟨⟨hpr, hlo⟩, hhi⟩, hm16⟩, rfl⟩
        obtain ⟨hk, ha⟩ := base_off_k (sp := sp) (off := off) 20704 32 hlo (by omega) hm16
        obtain ⟨hk1, ha1⟩ := base_off_k16 (sp := sp) (off := off) 20704 32 hlo hhi hm16
        exact step_stpQ128 hpc hrun hfetch hsp_chk haddr rfl (hm.hvregs vt1) (hm.hvregs vt2)
          (store_polySp hpr hk ha)
          (store_polySp (st := { st with poly := st.poly.set _ _ }) hpr hk1 ha1.symm) rfl
          (fun m' => hnext _ rfl hrun (matches_store hm st.spill13 st.spill6 st.spill21 _ _ m'))

/-! ## 2. 1-Step (`sepWP_of_stepSymInst`) & `N`-Step (`sepWP_of_runSymRange`) Soundness -/

theorem sepWP_of_stepSymInst {prog : Program} {tgt pc sp polyPtr : BitVec 64}
    {cfg : SymCfg} {env : SymEnv} {st st' : SymState} {s : State}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {inst : Instr}
    (hm : SymStateMatches cfg sp polyPtr env st s)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hstep : stepSymInst cfg inst st = some st')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      SymStateMatches cfg sp polyPtr env st' s' →
      SepWP prog tgt s' (SymSpatial cfg sp polyPtr env st' F) post oom) :
    SepWP prog tgt s (SymSpatial cfg sp polyPtr env st F) post oom := by
  have hstep0 := hstep
  unfold stepSymInst at hstep
  split at hstep <;> try contradiction
  · rename_i vt base off
    by_cases c : (cfg.polyReg? == some base && decide (off.toNat < 512) && off.toNat % 16 == 0) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c
      have haddr : evalAddrMode s (.Offset (.gpr base) off) = (polyPtr + off, none) := by
        simp [evalAddrMode, hm.hpoly base c.1.1]
      obtain ⟨hk, ha⟩ := ptr_off_k (ptr := polyPtr) (off := off) (n := 32) (by omega) c.2
      exact step_ldrQ128 hpc hrun hfetch rfl haddr (load_polyReg c.1.1 hk ha) rfl
        (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i vt base off
    by_cases c : (cfg.polyReg? == some base && decide (off.toNat < 512) && off.toNat % 16 == 0) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c
      have haddr : evalAddrMode s (.Offset (.gpr base) off) = (polyPtr + off, none) := by
        simp [evalAddrMode, hm.hpoly base c.1.1]
      obtain ⟨hk, ha⟩ := ptr_off_k (ptr := polyPtr) (off := off) (n := 32) (by omega) c.2
      exact step_strQ128 hpc hrun hfetch rfl haddr (hm.hvregs vt) (store_polyReg c.1.1 hk ha) rfl
        (fun m' => hnext _ rfl hrun (matches_store hm st.spill13 st.spill6 st.spill21 _ _ m'))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i vt1 vt2 base off
    by_cases c : (cfg.polyReg? == some base && decide (off.toNat + 16 < 512) && off.toNat % 16 == 0) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c
      have haddr : evalAddrMode s (.Offset (.gpr base) off) = (polyPtr + off, none) := by
        simp [evalAddrMode, hm.hpoly base c.1.1]
      obtain ⟨hk, ha⟩ := ptr_off_k (ptr := polyPtr) (off := off) (n := 32) (by omega) c.2
      obtain ⟨hk1, ha1⟩ := ptr_off_k16 (ptr := polyPtr) (off := off) (n := 32) (by omega) c.2
      exact step_ldpQ128 hpc hrun hfetch rfl haddr rfl
        (load_polyReg c.1.1 hk ha) (load_polyReg c.1.1 hk1 ha1.symm) rfl
        (hnext _ rfl hrun (matches_setPC (matches_writeVReg (matches_writeVReg hm vt1 _) vt2 _) _))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i vt1 vt2 base off
    by_cases c : (cfg.polyReg? == some base && decide (off.toNat + 16 < 512) && off.toNat % 16 == 0) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c
      have haddr : evalAddrMode s (.Offset (.gpr base) off) = (polyPtr + off, none) := by
        simp [evalAddrMode, hm.hpoly base c.1.1]
      obtain ⟨hk, ha⟩ := ptr_off_k (ptr := polyPtr) (off := off) (n := 32) (by omega) c.2
      obtain ⟨hk1, ha1⟩ := ptr_off_k16 (ptr := polyPtr) (off := off) (n := 32) (by omega) c.2
      exact step_stpQ128 hpc hrun hfetch rfl haddr rfl (hm.hvregs vt1) (hm.hvregs vt2)
        (store_polyReg c.1.1 hk ha)
        (store_polyReg (st := { st with poly := st.poly.set _ _ }) c.1.1 hk1 ha1.symm) rfl
        (fun m' => hnext _ rfl hrun (matches_store hm st.spill13 st.spill6 st.spill21 _ _ m'))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · exact step_ldrSp hm hpc hrun hfetch hstep0 hnext
  · exact step_strSp hm hpc hrun hfetch hstep0 hnext
  · exact step_ldpSp hm hpc hrun hfetch hstep0 hnext
  · exact step_stpSp hm hpc hrun hfetch hstep0 hnext
  · rename_i rd imm16
    by_cases c : ((cfg.polyReg? != some rd) && decide (rd.toNat < 31)) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at c
      refine SepWP.step_pure hpc hrun hfetch (s' := (s.writeReg64 (.gpr rd) (imm16.zeroExtend 64)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, execMoveWide]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeGpr hm c.2 c.1 rfl))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i rd rm
    by_cases c : ((cfg.polyReg? != some rd) && decide (rd.toNat < 31)) = true
    · simp only [c, ↓reduceIte] at hstep
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at c
      cases rm with
      | xzr =>
        simp only [Option.some.injEq] at hstep; subst hstep
        refine SepWP.step_pure hpc hrun hfetch (s' := (s.writeReg64 (.gpr rd) 0#64).advancePC) ?_ rfl ?_
        · rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, execLogicalShift, evalLogical, shiftVal, shift64]
        · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeGpr hm c.2 c.1 rfl))
      | gpr rs =>
        by_cases hrs : rs.toNat < 31
        · simp only [hrs, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          refine SepWP.step_pure hpc hrun hfetch
            (s' := (s.writeReg64 (.gpr rd) (evalSymGpr sp env (st.gprs.get rs.toNat))).advancePC) ?_ rfl ?_
          · rw [setPC_self hpc]
            have hread : s.readReg .W64 (.gpr rs) = evalSymGpr sp env (st.gprs.get rs.toNat) := hm.hgprs rs hrs
            simp [Program.evalInst, execInstWithSvc, execLogicalShift, evalLogical, shiftVal, shift64, hread]
          · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeGpr hm c.2 c.1 rfl))
        · simp [hrs] at hstep
      | sp => contradiction
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i rd imm12 shift12
    by_cases c : ((cfg.polyReg? != some rd) && decide (rd.toNat < 31)) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at c
      set off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
      refine SepWP.step_pure hpc hrun hfetch (s' := (s.writeReg64 (.gpr rd) (sp + off64)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.readReg64, hm.hsp, off64]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeGpr hm c.2 c.1 rfl))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i rd rn imm12 shift12
    by_cases c : ((cfg.polyReg? != some rd) && decide (rd.toNat < 31) && decide (rn.toNat < 31)) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at c
      set off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) (evalSymGpr sp env (st.gprs.get rn.toNat) + off64)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        have hread : s.readReg .W64 (.gpr rn) = evalSymGpr sp env (st.gprs.get rn.toNat) := hm.hgprs rn c.2
        simp [Program.evalInst, execInstWithSvc, execAddSubImm, hread, off64]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeGpr hm c.1.2 c.1.1 rfl))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i rd rn rm
    by_cases c : ((cfg.polyReg? != some rd) && decide (rd.toNat < 31) && decide (rn.toNat < 31) && decide (rm.toNat < 31)) = true
    · simp only [c, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at c
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) (evalSymGpr sp env (st.gprs.get rn.toNat) + evalSymGpr sp env (st.gprs.get rm.toNat))).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        have hrn : s.readReg .W64 (.gpr rn) = evalSymGpr sp env (st.gprs.get rn.toNat) := hm.hgprs rn c.1.2
        have hrm : s.readReg .W64 (.gpr rm) = evalSymGpr sp env (st.gprs.get rm.toNat) := hm.hgprs rm c.2
        simp [Program.evalInst, execInstWithSvc, execAddSubShift, shiftVal, shift64, hrn, hrm]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeGpr hm c.1.1.2 c.1.1.1 rfl))
    · simp [Bool.eq_false_iff.mpr c] at hstep
  · rename_i rn imm12
    by_cases hrn : rn.toNat < 31
    · simp only [hrn, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.setPState (evalSymPState sp env (.cmpImm64 (st.gprs.get rn.toNat) (imm12.zeroExtend 64)))).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        have hread : s.readReg .W64 (.gpr rn) = evalSymGpr sp env (st.gprs.get rn.toNat) := hm.hgprs rn hrn
        simp [Program.evalInst, execInstWithSvc, execAddSubImm, subsPState64, hread, evalSymPState]
      · exact hnext _ (by simp [State.advancePC, State.setPState, hpc]) hrun
          (matches_advancePC (matches_setPState hm rfl))
    · simp [hrn] at hstep
  · rename_i rn rd
    by_cases hrn : rn.toNat < 31
    · simp only [hrn, ↓reduceIte] at hstep
      cases hg : st.gprs.get rn.toNat with
      | const64 v =>
        simp only [hg, Option.some.injEq] at hstep; subst hstep
        refine SepWP.step_pure hpc hrun hfetch
          (s' := (s.writeVReg128 rd (evalSExpr env (.const (v.truncate 16)))).advancePC) ?_ rfl ?_
        · rw [setPC_self hpc]
          have hr_val : s.readReg64 (Reg.fromZRBits rn) = v := by
            rw [fromZRBits_lt31 hrn, hm.hgprs rn hrn, hg]; rfl
          simp [Program.evalInst, execInstWithSvc, hr_val, simdDup_eval v, evalSExpr]
        · exact hnext _ (by simp [State.advancePC, hpc]) hrun
            (matches_advancePC (matches_writeVReg hm rd (.const (v.truncate 16))))
      | _ => simp [hg] at hstep
    · simp [hrn] at hstep
  · rename_i u sz rm opcode rn rd
    by_cases c1 : (!u && sz == 2#2 && opcode == 0b00011#5 && rm == rn) = true
    · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c1; rcases c1 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeVReg128 rd (evalSExpr env (st.vregs.get rm.toNat))).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hm.hvregs rm]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
    · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
      by_cases c2 : (!u && sz == 1#2 && opcode == 0b10000#5) = true
      · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c2; rcases c2 with ⟨⟨rfl, rfl⟩, rfl⟩
        refine SepWP.step_pure hpc hrun hfetch
          (s' := (s.writeVReg128 rd (evalSExpr env (.add (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)))).advancePC) ?_ rfl ?_
        · rw [setPC_self hpc]
          simp [Program.evalInst, execInstWithSvc, hm.hvregs rn, hm.hvregs rm,
            simdAdd_eval (evalSExpr env (st.vregs.get rn.toNat)) (evalSExpr env (st.vregs.get rm.toNat)), evalSExpr]
        · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
      · simp only [Bool.eq_false_iff.mpr c2, Bool.false_eq_true, ↓reduceIte] at hstep
        by_cases c3 : (u && sz == 1#2 && opcode == 0b10000#5) = true
        · simp only [c3, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          simp only [Bool.and_eq_true, beq_iff_eq] at c3; rcases c3 with ⟨⟨rfl, rfl⟩, rfl⟩
          refine SepWP.step_pure hpc hrun hfetch
            (s' := (s.writeVReg128 rd (evalSExpr env (smartSub (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)))).advancePC) ?_ rfl ?_
          · rw [setPC_self hpc]
            simp [Program.evalInst, execInstWithSvc, hm.hvregs rn, hm.hvregs rm,
              simdSub_eval (evalSExpr env (st.vregs.get rn.toNat)) (evalSExpr env (st.vregs.get rm.toNat)), eval_smartSub]
          · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
        · simp only [Bool.eq_false_iff.mpr c3, Bool.false_eq_true, ↓reduceIte] at hstep
          by_cases c4 : (!u && sz == 1#2 && opcode == 0b10011#5) = true
          · simp only [c4, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
            simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c4; rcases c4 with ⟨⟨rfl, rfl⟩, rfl⟩
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
              simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c5; rcases c5 with ⟨⟨rfl, rfl⟩, rfl⟩
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
                simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c6; rcases c6 with ⟨⟨rfl, rfl⟩, rfl⟩
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
        · simp [Program.evalInst, execInstWithSvc, c16, evalSExpr]; rw [rep8_eq_dup8x16]
        · simp [Program.evalInst, execInstWithSvc, evalSimdModImmExt, advSimdExpandImm, c16, evalSExpr]; rw [not_rep8_eq_dup8x16]
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
          · simp [Program.evalInst, execInstWithSvc, c16, evalSExpr]; rw [rep8_eq_dup8x16]
          · simp [Program.evalInst, execInstWithSvc, evalSimdModImmExt, advSimdExpandImm, c16, evalSExpr]; rw [not_rep8_eq_dup8x16]
        · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
      · simp only [Bool.eq_false_iff.mpr c2, Bool.false_eq_true, ↓reduceIte] at hstep
        by_cases c3 : (!op && immh == 0b0011#4 && immb == 0b111#3 && opcode == 0b00000#5) = true
        · simp only [c3, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c3; rcases c3 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
          refine SepWP.step_pure hpc hrun hfetch
            (s' := (s.writeVReg128 rd (evalSExpr env (.sshr (st.vregs.get rn.toNat) 1))).advancePC) ?_ rfl ?_
          · rw [setPC_self hpc]
            simp [Program.evalInst, execInstWithSvc, evalSimdImmShiftNonZeroExt,
              evalSimdImmShiftNonZeroExtSatFlags, hm.hvregs rn, simdSshr_eval _ _ 1 (by omega) (by omega), evalSExpr]
          · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
        · simp only [Bool.eq_false_iff.mpr c3, Bool.false_eq_true, ↓reduceIte] at hstep
          by_cases c4 : (!op && immh == 0b0010#4 && immb == 0b101#3 && opcode == 0b00000#5) = true
          · simp only [c4, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
            simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c4; rcases c4 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
            refine SepWP.step_pure hpc hrun hfetch
              (s' := (s.writeVReg128 rd (evalSExpr env (.sshr (st.vregs.get rn.toNat) 11))).advancePC) ?_ rfl ?_
            · rw [setPC_self hpc]
              simp [Program.evalInst, execInstWithSvc, evalSimdImmShiftNonZeroExt,
                evalSimdImmShiftNonZeroExtSatFlags, hm.hvregs rn, simdSshr_eval _ _ 11 (by omega) (by omega), evalSExpr]
            · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_writeVReg hm rd _))
          · simp [Bool.eq_false_iff.mpr c4] at hstep

theorem sepWP_of_runSymRange [MlKemPlacement] {b sp polyPtr : BitVec 64}
    {cfg : SymCfg} {env : SymEnv} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (count w : Nat) {st stEnd : SymState} {s : State}
    (hrange : ∀ j, w ≤ j → j < w + count → InSymWord04 j)
    (hrun_sym : runSymRange cfg w count st = some stEnd)
    (hm : SymStateMatches cfg sp polyPtr env st s)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hpost : ∀ sf : State, sf.pc = b + BitVec.ofNat 64 (4 * (w + count)) →
      sf.status = .Running → SymStateMatches cfg sp polyPtr env stEnd sf →
      post sf (SymSpatial cfg sp polyPtr env stEnd F)) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (b + BitVec.ofNat 64 (4 * (w + count))) s (SymSpatial cfg sp polyPtr env st F) post oom := by
  induction count generalizing w st s with
  | zero =>
    simp only [runSymRange, Option.some.injEq] at hrun_sym; subst hrun_sym
    have hpc0 : s.pc = b + BitVec.ofNat 64 (4 * (w + 0)) := by simpa using hpc
    exact SepWP.done hpc0 hrun (hpost s hpc0 hrun hm)
  | succ n ih =>
    unfold runSymRange at hrun_sym
    cases hfw : fetchWordTree04 w with
    | none => simp [hfw] at hrun_sym
    | some inst =>
      simp only [hfw] at hrun_sym
      cases hst : stepSymInst cfg inst st with
      | none => simp [hst] at hrun_sym
      | some st1 =>
        simp only [hst] at hrun_sym
        have hfetch := fetch_blk04_sym (b := b) (hrange w (by omega) (by omega)) hfw
        refine sepWP_of_stepSymInst hm hpc hrun hfetch hst ?_
        intro s' hpc' hrun' hm'
        have hpc_eq : b + BitVec.ofNat 64 (4 * w) + 4#64 = b + BitVec.ofNat 64 (4 * (w + 1)) := by
          rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        rw [hpc_eq] at hpc'
        have hend_eq : 4 * (w + (n + 1)) = 4 * (w + 1 + n) := by omega
        rw [hend_eq]
        exact ih (w + 1) (fun j h1 h2 => hrange j (by omega) (by omega))
          hrun_sym hm' hpc' hrun' (fun sf h1 h2 h3 => hpost sf (by rwa [hend_eq]) h2 h3)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPoly

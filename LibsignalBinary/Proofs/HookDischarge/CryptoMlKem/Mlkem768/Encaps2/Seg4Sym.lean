/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymBridge

/-!
# `encapsulate2` (`B20`) — Symbolic Stepper Soundness (`Seg4Sym`)

Proves 1-step (`sepWP_of_stepSymInst`) and `N`-step (`sepWP_of_runSymRange`) separation-logic
soundness for the relocation-free straight-line region `[0x10a0 .. 0x28e8)` of `B20`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Sym

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
  (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
  (blkPC20)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (SepLoad128 SepStore128 step_ldrQ128 step_strQ128 step_ldpQ128 step_stpQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
  (SymSpill13 SymVec32 SymState fetchWordTree20 stepSymInst runSymRange
   SymEnv evalSExpr eval_smartMla eval_smartSub
   symSpill13_eval_get symSpill13_eval_set
   symVec32_eval_get symVec32_eval_set
   SymStateMatches SymSpatial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymBridge
  (fetch_blk20_seg4 rep8_eq_dup8x16 not_rep8_eq_dup8x16
   simdDup_eval simdSshr_eval simdSqdmulh_eval simdAdd_eval simdSub_eval simdMul_eval simdMla_eval
   matches_writeVReg matches_orFpsr matches_setPC matches_advancePC
   matches_getGpr_const matches_setGpr setPC_self
   sp_spill_off sp_spill_off16 sp_poly_off sp_poly_off16)

private theorem matches_store {s0 s : State} {sp ret : BitVec 64} {env : SymEnv} {st : SymState}
    (hm : SymStateMatches s0 sp ret env st s) (sp' : SymSpill13) (p' : SymVec32)
    (pc' : BitVec 64) (m' : Memory) :
    SymStateMatches s0 sp ret env { st with spill := sp', poly := p' }
      (((applyWriteback s none).setPC pc').setMem m') :=
  ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, hm.hvregs, hm.hx0, hm.hx1, hm.hx2, hm.hx8, hm.hx9, hm.hx20⟩

theorem sepWP_of_stepSymInst {prog : Program} {tgt pc : BitVec 64}
    {s0 s : State} {sp ret : BitVec 64} {env : SymEnv} {st st' : SymState}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} {inst : Instr}
    (hm : SymStateMatches s0 sp ret env st s)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hstep : stepSymInst inst st = some st')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      SymStateMatches s0 sp ret env st' s' →
      SepWP prog tgt s' (SymSpatial sp env st' F) post oom) :
    SepWP prog tgt s (SymSpatial sp env st F) post oom := by
  unfold stepSymInst at hstep
  split at hstep <;> try contradiction
  · rename_i vt off
    have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
    have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
      simp [evalAddrMode, State.readReg64, hm.hsp]
    by_cases c1 : (off.toNat < 208 && off.toNat % 16 == 0) = true
    · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1
      obtain ⟨hk, ha⟩ := sp_spill_off c1.1 c1.2
      exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr
        (SepLoad128.left (SepLoad128.spill13 hk ha (symSpill13_eval_get env st.spill _ hk))) rfl
        (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
    · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
      by_cases c2 : (2928 ≤ off.toNat && off.toNat < 3440 && (off.toNat - 2928) % 16 == 0) = true
      · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c2
        obtain ⟨hk, ha⟩ := sp_poly_off c2.1.1 c2.1.2 c2.2
        exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr
          (SepLoad128.right (SepLoad128.left (SepLoad128.vec32 hk ha (symVec32_eval_get env st.poly _ hk)))) rfl
          (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
      · simp [Bool.eq_false_iff.mpr c2] at hstep
  · rename_i vt off
    have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
    have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
      simp [evalAddrMode, State.readReg64, hm.hsp]
    by_cases c1 : (off.toNat < 208 && off.toNat % 16 == 0) = true
    · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1
      obtain ⟨hk, ha⟩ := sp_spill_off c1.1 c1.2
      exact step_strQ128 hpc hrun hfetch hsp_chk haddr (hm.hvregs vt)
        (SepStore128.left (SepStore128.spill13 hk ha (symSpill13_eval_set env st.spill _ _).symm)) rfl
        (fun m' => hnext _ rfl hrun (matches_store hm _ st.poly _ m'))
    · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
      by_cases c2 : (2928 ≤ off.toNat && off.toNat < 3440 && (off.toNat - 2928) % 16 == 0) = true
      · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c2
        obtain ⟨hk, ha⟩ := sp_poly_off c2.1.1 c2.1.2 c2.2
        exact step_strQ128 hpc hrun hfetch hsp_chk haddr (hm.hvregs vt)
          (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha (symVec32_eval_set env st.poly _ _).symm))) rfl
          (fun m' => hnext _ rfl hrun (matches_store hm st.spill _ _ m'))
      · simp [Bool.eq_false_iff.mpr c2] at hstep
  · rename_i vt1 vt2 off
    have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
    have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
      simp [evalAddrMode, State.readReg64, hm.hsp]
    by_cases c1 : (off.toNat + 16 < 208 && off.toNat % 16 == 0) = true
    · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1
      obtain ⟨hk, ha⟩ := sp_spill_off (by omega) c1.2
      obtain ⟨hk1, ha1⟩ := sp_spill_off16 c1.1 c1.2
      exact step_ldpQ128 hpc hrun hfetch hsp_chk haddr rfl
        (SepLoad128.left (SepLoad128.spill13 hk ha (symSpill13_eval_get env st.spill _ hk)))
        (SepLoad128.left (SepLoad128.spill13 hk1 ha1.symm (symSpill13_eval_get env st.spill _ hk1))) rfl
        (hnext _ rfl hrun (matches_setPC (matches_writeVReg (matches_writeVReg hm vt1 _) vt2 _) _))
    · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
      by_cases c2 : (2928 ≤ off.toNat && off.toNat + 16 < 3440 && (off.toNat - 2928) % 16 == 0) = true
      · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c2
        obtain ⟨hk, ha⟩ := sp_poly_off c2.1.1 (by omega) c2.2
        obtain ⟨hk1, ha1⟩ := sp_poly_off16 c2.1.1 c2.1.2 c2.2
        exact step_ldpQ128 hpc hrun hfetch hsp_chk haddr rfl
          (SepLoad128.right (SepLoad128.left (SepLoad128.vec32 hk ha (symVec32_eval_get env st.poly _ hk))))
          (SepLoad128.right (SepLoad128.left (SepLoad128.vec32 hk1 ha1.symm (symVec32_eval_get env st.poly _ hk1)))) rfl
          (hnext _ rfl hrun (matches_setPC (matches_writeVReg (matches_writeVReg hm vt1 _) vt2 _) _))
      · simp [Bool.eq_false_iff.mpr c2] at hstep
  · rename_i vt1 vt2 off
    have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
    have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
      simp [evalAddrMode, State.readReg64, hm.hsp]
    by_cases c1 : (off.toNat + 16 < 208 && off.toNat % 16 == 0) = true
    · simp only [c1, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c1
      obtain ⟨hk, ha⟩ := sp_spill_off (by omega) c1.2
      obtain ⟨hk1, ha1⟩ := sp_spill_off16 c1.1 c1.2
      exact step_stpQ128 hpc hrun hfetch hsp_chk haddr rfl (hm.hvregs vt1) (hm.hvregs vt2)
        (SepStore128.left (SepStore128.spill13 hk ha (symSpill13_eval_set env st.spill _ _).symm))
        (SepStore128.left (SepStore128.spill13 hk1 ha1.symm (symSpill13_eval_set env _ _ _).symm)) rfl
        (fun m' => hnext _ rfl hrun (matches_store hm _ st.poly _ m'))
    · simp only [Bool.eq_false_iff.mpr c1, Bool.false_eq_true, ↓reduceIte] at hstep
      by_cases c2 : (2928 ≤ off.toNat && off.toNat + 16 < 3440 && (off.toNat - 2928) % 16 == 0) = true
      · simp only [c2, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c2
        obtain ⟨hk, ha⟩ := sp_poly_off c2.1.1 (by omega) c2.2
        obtain ⟨hk1, ha1⟩ := sp_poly_off16 c2.1.1 c2.1.2 c2.2
        exact step_stpQ128 hpc hrun hfetch hsp_chk haddr rfl (hm.hvregs vt1) (hm.hvregs vt2)
          (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha (symVec32_eval_set env st.poly _ _).symm)))
          (SepStore128.right (SepStore128.left (SepStore128.vec32 hk1 ha1.symm (symVec32_eval_set env _ _ _).symm))) rfl
          (fun m' => hnext _ rfl hrun (matches_store hm st.spill _ _ m'))
      · simp [Bool.eq_false_iff.mpr c2] at hstep
  · rename_i rd imm16
    cases hset : st.gprs.set? rd (.const64 (imm16.zeroExtend 64)) with
    | none => simp [hset] at hstep
    | some g' =>
      simp only [hset, Option.some.injEq] at hstep; subst hstep
      refine SepWP.step_pure hpc hrun hfetch (s' := (s.writeReg64 (.gpr rd) (imm16.zeroExtend 64)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, execMoveWide]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_setGpr hm hset rfl))
  · rename_i rd imm12 shift12
    set off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
    cases hset : st.gprs.set? rd (.spAdd off64) with
    | none => simp [hset] at hstep
    | some g' =>
      simp only [hset, Option.some.injEq] at hstep; subst hstep
      refine SepWP.step_pure hpc hrun hfetch (s' := (s.writeReg64 (.gpr rd) (sp + off64)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.readReg64,
          hm.hsp, off64]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun (matches_advancePC (matches_setGpr hm hset rfl))
  · rename_i rn rd
    cases hg : st.gprs.get? rn with
    | none => simp [hg] at hstep
    | some sg =>
      cases sg with
      | unknown => simp [hg] at hstep
      | spAdd _ => simp [hg] at hstep
      | const64 v =>
        simp only [hg, Option.some.injEq] at hstep; subst hstep
        refine SepWP.step_pure hpc hrun hfetch
          (s' := (s.writeVReg128 rd (evalSExpr env (.const (v.truncate 16)))).advancePC) ?_ rfl ?_
        · rw [setPC_self hpc]
          simp [Program.evalInst, execInstWithSvc, matches_getGpr_const hm hg, simdDup_eval v, evalSExpr]
        · exact hnext _ (by simp [State.advancePC, hpc]) hrun
            (matches_advancePC (matches_writeVReg hm rd (.const (v.truncate 16))))
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
            (s' := (s.writeVReg128 rd (evalSExpr env (Seg4SymDefs.smartSub (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)))).advancePC) ?_ rfl ?_
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
                (s' := (s.writeVReg128 rd (evalSExpr env (Seg4SymDefs.smartMla (st.vregs.get rd.toNat) (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)))).advancePC) ?_ rfl ?_
              · rw [setPC_self hpc]
                have hmla : ∀ vd vn vm : BitVec 128,
                    Poly.SimdOps.simdAdd8h vd (Poly.SimdOps.simdMul8h vn vm) =
                      Poly.SimdOps.simdMla8h vd vn vm := by
                  intro vd vn vm; apply Poly.Lane16.ext_lane16; intro i; simp
                simp [Program.evalInst, execInstWithSvc, evalSimdThreeSameExt, evalSimdThreeSameExtSatFlags,
                  hm.hvregs rd, hm.hvregs rn, hm.hvregs rm,
                  simdMul_eval (evalSExpr env (st.vregs.get rn.toNat)) (evalSExpr env (st.vregs.get rm.toNat)),
                  simdAdd_eval (evalSExpr env (st.vregs.get rd.toNat))
                    (Poly.SimdOps.simdMul8h (evalSExpr env (st.vregs.get rn.toNat)) (evalSExpr env (st.vregs.get rm.toNat))),
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

theorem sepWP_of_runSymRange [MlKemPlacement] {b : BitVec 64} {s0 : State} {sp ret : BitVec 64}
    {env : SymEnv} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (count w : Nat) {st stEnd : SymState} {s : State}
    (hlo : 1064 ≤ w) (hhi : w + count ≤ 2618)
    (hrun_sym : runSymRange w count st = some stEnd)
    (hm : SymStateMatches s0 sp ret env st s)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hpost : ∀ sf : State, sf.pc = b + BitVec.ofNat 64 (4 * (w + count)) →
      sf.status = .Running → SymStateMatches s0 sp ret env stEnd sf →
      post sf (SymSpatial sp env stEnd F)) :
    SepWP (blkPC20.rebase b (fun _ => none))
      (b + BitVec.ofNat 64 (4 * (w + count))) s (SymSpatial sp env st F) post oom := by
  induction count generalizing w st s with
  | zero =>
    simp only [runSymRange, Option.some.injEq] at hrun_sym; subst hrun_sym
    have hpc0 : s.pc = b + BitVec.ofNat 64 (4 * (w + 0)) := by simpa using hpc
    exact SepWP.done hpc0 hrun (hpost s hpc0 hrun hm)
  | succ n ih =>
    unfold runSymRange at hrun_sym
    cases hfw : fetchWordTree20 w with
    | none => simp [hfw] at hrun_sym
    | some inst =>
      simp only [hfw] at hrun_sym
      cases hst : stepSymInst inst st with
      | none => simp [hst] at hrun_sym
      | some st1 =>
        simp only [hst] at hrun_sym
        have hfetch := fetch_blk20_seg4 (b := b) hlo (by omega) hfw
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

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Sym

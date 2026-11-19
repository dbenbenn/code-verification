/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

/-!
# `generate_keypair_compressed` (`B05`): symbolic `stepKInst` and `runKRange` soundness

Proves `sepWP_of_stepKInst` across all 39 instruction patterns of `stepKInst` and lifts it by
induction to `sepWP_of_runKRange` over relocation-free `B05` `Seg2` code slices (`w = 183 .. 3296`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1r_2d)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
  (extractLsb_lo_append extractLsb_hi_append eor_append bic_append or_append orr_self_128
   execInst_zip1_2d execInst_zip2_2d fneg_2d_eval fneg_2d_satFlags usra_2d_satFlags
   add_2d_lanes dup_2d_lane0 dup_2d_lane1 mov_d1_d0)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (blkPC05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
  (KExpr KEnv evalKExpr eval_smartAdd64 eval_smartUsra smartAdd64 smartUsra usraShift?
   KCfg KState resolveMemIdx? readMemWord writeMemWord
   fetchWordTree05 stepKInst runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem
  (fetch_blk05_seg2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge
  (lt31_of_beq_false fromZRBits_of_beq_false condHolds_HI_255
   KCfgWf KStateMatches KSpatial sepLoad64_rcBase
   matches_writeVReg matches_writeGpr matches_setPState matches_setPC
   matches_advancePC matches_setMem matches_writeMemWord
   resolveMemIdx_bounds sepLoad64_kmem sepStore64_kmem
   bit_append bsl_append ins_b0_append dupScalar_d1_append umov_d1_append
   fmov_d0_append shl_2d_eval usra_2d_eval addSubImm_delta_eq
   movz_w32_eq_writeReg64 writeReg_w32_zero_eq_writeReg64)

/-! ## 1. Generic Pure Step Combinators -/

private theorem step_vreg_pure {prog : Program} {target_pc pc : BitVec 64}
    {cfg : KCfg} {env : KEnv} {st : KState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {inst : Instr} {rd : BitVec 5} {p : KExpr × KExpr} {res : BitVec 128}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = ((s.setPC pc).writeVReg128 rd res).advancePC)
    (hres : res = evalKExpr env p.2 ++ evalKExpr env p.1)
    (hm : KStateMatches env st s)
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      KStateMatches env { st with vregs := st.vregs.set rd.toNat p } s' →
      SepWP prog target_pc s' (KSpatial cfg env { st with vregs := st.vregs.set rd.toNat p } F) post oom) :
    SepWP prog target_pc s (KSpatial cfg env st F) post oom :=
  SepWP.step_pure hpc hrun hfetch hexec rfl
    (hnext _ rfl hrun (matches_advancePC (matches_writeVReg (matches_setPC hm pc) rd p hres)))

private theorem step_gpr_pure {prog : Program} {target_pc pc : BitVec 64}
    {cfg : KCfg} {env : KEnv} {st : KState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {inst : Instr} {rd : BitVec 5} {e : KExpr} {res : BitVec 64}
    (hrd : rd.toNat < 31)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = ((s.setPC pc).writeReg64 (.gpr rd) res).advancePC)
    (hres : res = evalKExpr env e)
    (hm : KStateMatches env st s)
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      KStateMatches env { st with gprs := st.gprs.set rd.toNat e } s' →
      SepWP prog target_pc s' (KSpatial cfg env { st with gprs := st.gprs.set rd.toNat e } F) post oom) :
    SepWP prog target_pc s (KSpatial cfg env st F) post oom :=
  SepWP.step_pure hpc hrun hfetch hexec rfl
    (hnext _ rfl hrun (matches_advancePC (matches_writeGpr (matches_setPC hm pc) hrd e hres)))

private theorem step_pstate_pure {prog : Program} {target_pc pc : BitVec 64}
    {cfg : KCfg} {env : KEnv} {st : KState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {inst : Instr} {lhs rhs : KExpr} {pst : PState}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = ((s.setPC pc).setPState pst).advancePC)
    (hpst : pst = (AddWithCarry64 (evalKExpr env lhs) (~~~(evalKExpr env rhs)) true).2)
    (hm : KStateMatches env st s)
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      KStateMatches env { st with pstate := some (lhs, rhs) } s' →
      SepWP prog target_pc s' (KSpatial cfg env { st with pstate := some (lhs, rhs) } F) post oom) :
    SepWP prog target_pc s (KSpatial cfg env st F) post oom :=
  SepWP.step_pure hpc hrun hfetch hexec rfl
    (hnext _ rfl hrun (matches_advancePC (matches_setPState (matches_setPC hm pc) lhs rhs hpst)))

/-! ## 2. Single-Step Soundness (`sepWP_of_stepKInst`) -/

theorem sepWP_of_stepKInst {prog : Program} {target_pc pc : BitVec 64}
    {cfg : KCfg} {env : KEnv} {st st' : KState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {inst : Instr}
    (hcfg : KCfgWf cfg)
    (hrloop : env.rLoop < 24)
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hstep : stepKInst cfg inst st = some st')
    (hm : KStateMatches env st s)
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      KStateMatches env st' s' →
      SepWP prog target_pc s' (KSpatial cfg env st' F) post oom) :
    SepWP prog target_pc s (KSpatial cfg env st F) post oom := by
  unfold stepKInst at hstep
  split at hstep
  · -- 1. ADD Vd.2D, Vn.2D, Vm.2D
    next rm rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change zipSimdLanes true 64 (s.readVReg128 rn) (s.readVReg128 rm) (· + ·) = _
      rw [hm.hvregs rn, hm.hvregs rm]
      simp only [zipSimdLanes_true_64, zipLanes, laneMask_64, Nat.zero_mul, Nat.one_mul,
        add_2d_lanes, extractLsb_hi_append, extractLsb_lo_append, evalKExpr]
  · -- 2. EOR Vd.16B, Vn.16B, Vm.16B
    next rm rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change s.readVReg128 rn ^^^ s.readVReg128 rm = _
      rw [hm.hvregs rn, hm.hvregs rm, eor_append]; rfl
  · -- 3. BIC Vd.16B, Vn.16B, Vm.16B
    next rm rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change s.readVReg128 rn &&& ~~~(s.readVReg128 rm) = _
      rw [hm.hvregs rn, hm.hvregs rm, bic_append]; rfl
  · -- 4. ORR Vd.16B, Vn.16B, Vm.16B (including MOV Vd, Vn)
    next rm rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change s.readVReg128 rn ||| s.readVReg128 rm = _
      by_cases hrm : (rm == rn) = true
      · have hrmEq := beq_iff_eq.mp hrm; subst hrmEq
        simp only [beq_self_eq_true, ↓reduceIte, orr_self_128, hm.hvregs rm]
      · have hrmF : (rm == rn) = false := Bool.eq_false_iff.mpr hrm
        simp only [hrmF, Bool.false_eq_true, ↓reduceIte]
        rw [hm.hvregs rn, hm.hvregs rm, or_append]; rfl
  · -- 5. BSL Vd.16B, Vn.16B, Vm.16B
    next rm rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change ((s.readVReg128 rn ^^^ s.readVReg128 rm) &&& s.readVReg128 rd) ^^^ s.readVReg128 rm = _
      rw [hm.hvregs rd, hm.hvregs rn, hm.hvregs rm, bsl_append]; rfl
  · -- 6. BIT Vd.16B, Vn.16B, Vm.16B
    next rm rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change s.readVReg128 rd ^^^ ((s.readVReg128 rd ^^^ s.readVReg128 rn) &&& s.readVReg128 rm) = _
      rw [hm.hvregs rd, hm.hvregs rn, hm.hvregs rm, bit_append]; rfl
  · -- 7. ZIP1 Vd.2D, Vn.2D, Vm.2D
    next rm rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure
        (res := (s.readVReg128 rm).extractLsb' 0 64 ++ (s.readVReg128 rn).extractLsb' 0 64)
        hpc hrun hfetch ?_ ?_ hm hnext
      · change execInst (.simdPermute true 0x3#2 rm 0x3#3 rn rd) (s.setPC pc) = _
        rw [execInst_zip1_2d]; rfl
      · rw [hm.hvregs rn, hm.hvregs rm, extractLsb_lo_append, extractLsb_lo_append]
  · -- 8. ZIP2 Vd.2D, Vn.2D, Vm.2D
    next rm rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      exact step_vreg_pure (res := (s.readVReg128 rm).extractLsb' 64 64 ++ (s.readVReg128 rn).extractLsb' 64 64)
        hpc hrun hfetch (by change execInst (.simdPermute true 0x3#2 rm 0x7#3 rn rd) (s.setPC pc) = _; rw [execInst_zip2_2d]; rfl)
        (by rw [hm.hvregs rn, hm.hvregs rm, extractLsb_hi_append, extractLsb_hi_append]) hm hnext
  · -- 9. FNEG Vd.2D, Vn.2D
    next rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      exact step_vreg_pure (res := ((s.readVReg128 rn).extractLsb' 64 64 ^^^ 0x8000000000000000#64) ++
          ((s.readVReg128 rn).extractLsb' 0 64 ^^^ 0x8000000000000000#64)) hpc hrun hfetch
        (by simp only [Program.evalInst, execInstWithSvc, ↓reduceIte, Bool.not_true,
              fneg_2d_eval, fneg_2d_satFlags, applySimdSatResult]; rfl)
        (by rw [hm.hvregs rn, extractLsb_hi_append, extractLsb_lo_append]; rfl) hm hnext
  · -- 10. MOVI Vd.2D, #0
    next rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      exact step_vreg_pure (res := 0#128) hpc hrun hfetch (by simp [Program.evalInst, execInstWithSvc])
        (by change 0#128 = 0#64 ++ 0#64; decide) hm hnext
  · -- 11. MOVI Vd.8H, #31
    next rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      exact step_vreg_pure (res := 0x001f001f001f001f001f001f001f001f#128) hpc hrun hfetch
        (by simp [Program.evalInst, execInstWithSvc])
        (by change 0x001f001f001f001f001f001f001f001f#128 =
              0x001f001f001f001f#64 ++ 0x001f001f001f001f#64; decide) hm hnext
  · -- 12. SHL Vd.2D, Vn.2D, #sh
    next immh immb rn rd =>
      by_cases hlt8 : Nat.blt immh.toNat 8 = true
      · simp [hlt8] at hstep
      · have hlt8F : Nat.blt immh.toNat 8 = false := Bool.eq_false_iff.mpr hlt8
        simp only [hlt8F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        have hge : ¬(immh.toNat < 8) := by simp [Nat.blt_eq] at hlt8; omega
        have hnez : (immh == 0#4) = false := beq_eq_false_iff_ne.mpr fun h0 => by subst h0; simp at hge
        let immhb := (immh ++ immb).toNat
        let esize := if immhb >= 64 then 64 else if immhb >= 32 then 32 else if immhb >= 16 then 16 else 8
        refine step_vreg_pure
          (res := mapSimdLanes true esize (s.readVReg128 rn) (fun lane => lane <<< (immhb - esize)))
          hpc hrun hfetch ?_ ?_ hm hnext
        · simp only [Program.evalInst, execInstWithSvc, hnez, Bool.false_eq_true, ↓reduceIte,
            Bool.not_false, Bool.not_true, Bool.and_false, Bool.true_and,
            show (0x0a#5 == 0b01010#5) = true from rfl]; rfl
        · rw [hm.hvregs rn]; exact shl_2d_eval immh immb hge _ _
  · -- 13. USRA Vd.2D, Vn.2D, #r
    next immh immb rn rd =>
      cases husra : usraShift? immh immb with
      | none => simp [husra] at hstep
      | some r =>
        simp only [husra, Option.some.injEq] at hstep; subst hstep
        rcases usra_2d_eval husra (evalKExpr env (st.vregs.get rd.toNat).2)
          (evalKExpr env (st.vregs.get rd.toNat).1) (evalKExpr env (st.vregs.get rn.toNat).2)
          (evalKExpr env (st.vregs.get rn.toNat).1) with ⟨hnez, hev⟩
        have hnezB : (immh == 0#4) = false := beq_eq_false_iff_ne.mpr hnez
        refine step_vreg_pure hpc hrun hfetch ?_ (by rw [eval_smartUsra, eval_smartUsra]) hm hnext
        simp only [Program.evalInst, execInstWithSvc, hnezB, Bool.false_eq_true, ↓reduceIte,
          Bool.not_true, Bool.true_and, Bool.false_and,
          show (0x02#5 == 0b10100#5) = false from rfl, show (0x02#5 == 0b00000#5) = false from rfl,
          show (0x02#5 == 0b01000#5) = false from rfl, show (0x02#5 == 0b01010#5) = false from rfl,
          Bool.or_self, show (s.setPC pc).readVReg128 rd = s.readVReg128 rd from rfl,
          show (s.setPC pc).readVReg128 rn = s.readVReg128 rn from rfl,
          hm.hvregs rd, hm.hvregs rn, hev, usra_2d_satFlags, applySimdSatResult]
  · -- 14. DUP Vd.2D, Vn.D[0]
    next rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change mapSimdLanes true 64 0#128 (fun _ => getSimdLane (s.readVReg128 rn) 64 0) = _
      rw [hm.hvregs rn]
      simp only [mapSimdLanes_true_64, mapLanes, laneMask_64, getSimdLane, Nat.zero_mul, Nat.one_mul,
        show (1#128 <<< 64 - 1#128) = 0xffffffffffffffff#128 from rfl,
        dup_2d_lane0, extractLsb_lo_append]
  · -- 15. DUP Vd.2D, Vn.D[1]
    next rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change mapSimdLanes true 64 0#128 (fun _ => getSimdLane (s.readVReg128 rn) 64 1) = _
      rw [hm.hvregs rn]
      simp only [mapSimdLanes_true_64, mapLanes, laneMask_64, getSimdLane, Nat.zero_mul, Nat.one_mul,
        show (1#128 <<< 64 - 1#128) = 0xffffffffffffffff#128 from rfl,
        dup_2d_lane1, extractLsb_hi_append]
  · -- 16. MOV Vd.B[0], Wn
    next rn rd =>
      by_cases hr31 : (rn == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rn == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
        change ((s.readVReg128 rd &&& ~~~(((1#128 <<< 8) - 1#128) <<< 0)) |||
          ((((s.readReg64 (Reg.fromZRBits rn)).zeroExtend 128) &&& ((1#128 <<< 8) - 1#128)) <<< 0)) = _
        rw [fromZRBits_of_beq_false hr31F, hm.hgprs rn (lt31_of_beq_false hr31F), hm.hvregs rd, ins_b0_append]; rfl
  · -- 17. MOV Vd.D[1], Vn.D[0]
    next rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change ((s.readVReg128 rd &&& ~~~(((1#128 <<< 64) - 1#128) <<< 64)) |||
        (getSimdLane (s.readVReg128 rn) 64 0 <<< 64)) = _
      rw [hm.hvregs rd, hm.hvregs rn]; unfold getSimdLane
      have hm1 : (~~~(((1#128 <<< 64) - 1#128) <<< 64) : BitVec 128) = 0xffffffffffffffff#128 := by decide
      have hm2 : ((1#128 <<< 64) - 1#128 : BitVec 128) = 0xffffffffffffffff#128 := by decide
      rw [hm1, hm2, mov_d1_d0, extractLsb_lo_append, extractLsb_lo_append]
  · -- 18. MOV Dd, Vn.D[1]
    next rn rd =>
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change evalSimdDupScalar 0x18#5 (s.readVReg128 rn) = _
      rw [hm.hvregs rn, dupScalar_d1_append]; rfl
  · -- 19. UMOV Xd, Vn.D[1]
    next rn rd =>
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        exact step_gpr_pure (res := (getSimdLane (s.readVReg128 rn) 64 1).truncate 64)
          (lt31_of_beq_false hr31F) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, fromZRBits_of_beq_false hr31F]; rfl)
          (by rw [hm.hvregs rn, umov_d1_append]) hm hnext
  · -- 20. FMOV Xd, Dn
    next rn rd =>
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        exact step_gpr_pure (res := s.readVReg64 rn) (lt31_of_beq_false hr31F) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, fromZRBits_of_beq_false hr31F]; rfl)
          (fmov_d0_append s rn _ _ (hm.hvregs rn)) hm hnext
  · -- 21. LD1R {Vt.2D}, [Xn]
    next rn vt =>
      by_cases hr31 : (rn == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rn == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte] at hstep
        have hlt : rn.toNat < 31 := lt31_of_beq_false hr31F
        cases hg : st.gprs.get rn.toNat <;> simp only [hg] at hstep <;> try contradiction
        case rcLoopPtr =>
          simp only [Option.some.injEq] at hstep; subst hstep
          have hea : s.readReg64 (.gpr rn) = env.rcBase + BitVec.ofNat 64 (8 * env.rLoop) := by
            rw [hm.hgprs rn hlt, hg]; rfl
          exact step_simdLd1r_2d hpc hrun hfetch rfl hea
            (sepLoad64_rcBase hrloop rfl) rfl
            (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt (.rcLoopVal, .rcLoopVal) rfl) (pc + 4#64)))
        case rcAdd off =>
          split at hstep <;> [skip; contradiction]
          next hc =>
            simp only [Option.some.injEq] at hstep; subst hstep
            simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, beq_iff_eq] at hc
            rcases hc with ⟨⟨hm8, hk24⟩, hoff⟩
            have hea : s.readReg64 (.gpr rn) = env.rcBase + BitVec.ofNat 64 (8 * (off.toNat / 8)) := by
              rw [hm.hgprs rn hlt, hg]; dsimp [evalKExpr]
              conv_lhs => rw [hoff]
              congr 2; omega
            exact step_simdLd1r_2d hpc hrun hfetch rfl hea (sepLoad64_rcBase hk24 rfl) rfl
              (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _ rfl) (pc + 4#64)))
  · -- 22. ADD Xd, SP, #imm12{, LSL #12}
    next rd imm12 shift12 =>
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        refine step_gpr_pure (res := (AddWithCarry64 ((s.setPC pc).readReg .W64 .sp)
            (if shift12 then imm12.zeroExtend 64 <<< 12 else imm12.zeroExtend 64) false).1)
          (lt31_of_beq_false hr31F) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, execAddSubImm, evalAddSub, State.writeReg,
                Bool.false_eq_true, ↓reduceIte]) ?_ hm hnext
        rw [show (s.setPC pc).readReg .W64 .sp = s.sp from rfl,
            addWithCarry64_add_fst, hm.hsp, addSubImm_delta_eq]; rfl
  · -- 23. ADD Xd, Xn, #imm12{, LSL #12}
    next rd rn imm12 shift12 =>
      by_cases hrr : (rd == 31#5 || rn == 31#5) = true
      · simp [hrr] at hstep
      · have hrrF : (rd == 31#5 || rn == 31#5) = false := Bool.eq_false_iff.mpr hrr
        simp only [hrrF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        rcases Bool.or_eq_false_iff.mp hrrF with ⟨hrdF, hrnF⟩
        refine step_gpr_pure (res := (AddWithCarry64 ((s.setPC pc).readReg .W64 (.gpr rn))
            (if shift12 then imm12.zeroExtend 64 <<< 12 else imm12.zeroExtend 64) false).1)
          (lt31_of_beq_false hrdF) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, execAddSubImm, evalAddSub, State.writeReg,
                Bool.false_eq_true, ↓reduceIte]) ?_ hm hnext
        rw [show (s.setPC pc).readReg .W64 (.gpr rn) = s.readReg64 (.gpr rn) from rfl,
            addWithCarry64_add_fst, hm.hgprs rn (lt31_of_beq_false hrnF),
            addSubImm_delta_eq, eval_smartAdd64]; rfl
  · -- 24. ADD Xd, Xn, Xm, LSL #0
    next rd rn rm =>
      by_cases hrr : (rd == 31#5 || rn == 31#5 || rm == 31#5) = true
      · simp [hrr] at hstep
      · have hrrF : (rd == 31#5 || rn == 31#5 || rm == 31#5) = false := Bool.eq_false_iff.mpr hrr
        simp only [hrrF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        rcases Bool.or_eq_false_iff.mp hrrF with ⟨hrdnF, hrmF⟩
        rcases Bool.or_eq_false_iff.mp hrdnF with ⟨hrdF, hrnF⟩
        refine step_gpr_pure (res := (AddWithCarry64 ((s.setPC pc).readReg .W64 (.gpr rn))
            (shiftVal .W64 ((s.setPC pc).readReg .W64 (.gpr rm)) .LSL 0) false).1)
          (lt31_of_beq_false hrdF) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, execAddSubShift, evalAddSub, State.writeReg,
                Bool.false_eq_true, ↓reduceIte]) ?_ hm hnext
        rw [show (s.setPC pc).readReg .W64 (.gpr rn) = s.readReg64 (.gpr rn) from rfl,
            show (s.setPC pc).readReg .W64 (.gpr rm) = s.readReg64 (.gpr rm) from rfl,
            addWithCarry64_add_fst, hm.hgprs rn (lt31_of_beq_false hrnF),
            hm.hgprs rm (lt31_of_beq_false hrmF), eval_smartAdd64]
        simp [shiftVal, shift64]
  · -- 25. SUBS XZR, Xn, #imm12
    next rn imm12 =>
      by_cases hr31 : (rn == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rn == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        refine step_pstate_pure (pst := (AddWithCarry64 ((s.setPC pc).readReg .W64 (.gpr rn))
            (~~~(imm12.zeroExtend 64)) true).2) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, execAddSubImm, evalAddSub, State.writeReg,
                ↓reduceIte]; rfl) ?_ hm hnext
        rw [show (s.setPC pc).readReg .W64 (.gpr rn) = s.readReg64 (.gpr rn) from rfl,
            hm.hgprs rn (lt31_of_beq_false hr31F)]; rfl
  · -- 26. SUBS XZR, Xn, XZR, LSL #0
    next rn =>
      by_cases hr31 : (rn == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rn == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        refine step_pstate_pure (pst := (AddWithCarry64 ((s.setPC pc).readReg .W64 (.gpr rn))
            (~~~(shiftVal .W64 ((s.setPC pc).readReg .W64 .xzr) .LSL 0)) true).2) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, execAddSubShift, evalAddSub, State.writeReg,
                ↓reduceIte]; rfl) ?_ hm hnext
        rw [show (s.setPC pc).readReg .W64 (.gpr rn) = s.readReg64 (.gpr rn) from rfl,
            hm.hgprs rn (lt31_of_beq_false hr31F)]; rfl
  · -- 27. CSEL Xd, Xn, Xm, HI
    next rd rn rm =>
      by_cases hrr : (rd == 31#5 || rn == 31#5 || rm == 31#5) = true
      · simp [hrr] at hstep
      · have hrrF : (rd == 31#5 || rn == 31#5 || rm == 31#5) = false := Bool.eq_false_iff.mpr hrr
        simp only [hrrF, Bool.false_eq_true, ↓reduceIte] at hstep
        rcases Bool.or_eq_false_iff.mp hrrF with ⟨hrdnF, hrmF⟩
        rcases Bool.or_eq_false_iff.mp hrdnF with ⟨hrdF, hrnF⟩
        split at hstep <;> [skip; contradiction]
        next lhs hpst =>
          simp only [Option.some.injEq] at hstep; subst hstep
          refine step_gpr_pure (lt31_of_beq_false hrdF) hpc hrun hfetch rfl ?_ hm hnext
          change (if ConditionHolds .HI s.pstate = true then s.readReg64 (.gpr rn)
            else s.readReg64 (.gpr rm)) = _
          simp only [hm.hpstate lhs (.const64 255#64) hpst,
            condHolds_HI_255, decide_eq_true_eq,
            hm.hgprs rn (lt31_of_beq_false hrnF), hm.hgprs rm (lt31_of_beq_false hrmF), evalKExpr]
  · -- 28. MOVZ Wd, #imm16
    next rd imm16 =>
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        refine step_gpr_pure (lt31_of_beq_false hr31F) hpc hrun hfetch ?_ rfl hm hnext
        change (((s.setPC pc).writeReg .W32 (.gpr rd) ((imm16.zeroExtend 64) <<< 0)).advancePC) = _
        rw [movz_w32_eq_writeReg64]; rfl
  · -- 29. ORR Wd, WZR, WZR (MOV Wd, #0)
    next rd =>
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        exact step_gpr_pure (res := 0#64) (lt31_of_beq_false hr31F) hpc hrun hfetch
          (by simp [Program.evalInst, execInstWithSvc, execLogicalShift, evalLogical,
                shiftVal, shift32, State.writeReg, State.readReg, State.readReg32, State.readReg64])
          rfl hm hnext
  · -- 30. ORR Xd, XZR, XZR (MOV Xd, #0)
    next rd =>
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        exact step_gpr_pure (lt31_of_beq_false hr31F) hpc hrun hfetch
          (by dsimp only [Program.evalInst, execInstWithSvc, execLogicalShift, evalLogical,
                shiftVal, shift64, State.writeReg, State.readReg, State.readReg64]; rfl)
          rfl hm hnext
  · -- 31. ORR Xd, XZR, Xm (MOV Xd, Xm)
    next rd rm =>
      by_cases hrr : (rd == 31#5 || rm == 31#5) = true
      · simp [hrr] at hstep
      · have hrrF : (rd == 31#5 || rm == 31#5) = false := Bool.eq_false_iff.mpr hrr
        simp only [hrrF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        rcases Bool.or_eq_false_iff.mp hrrF with ⟨hrdF, hrmF⟩
        refine step_gpr_pure (res := 0#64 ||| shiftVal .W64 (s.readReg64 (.gpr rm)) .LSL 0)
          (lt31_of_beq_false hrdF) hpc hrun hfetch
          (by dsimp only [Program.evalInst, execInstWithSvc, execLogicalShift, evalLogical, State.writeReg]; rfl)
          ?_ hm hnext
        rw [hm.hgprs rm (lt31_of_beq_false hrmF)]
        simp [shiftVal, shift64]
  · -- 32. LDR Qt, [addr]
    next vt addr =>
      cases hmi : resolveMemIdx? cfg st addr 2 with
      | none => simp [hmi] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩; simp only [hmi, Option.some.injEq] at hstep; subst hstep
        rcases resolveMemIdx_bounds hcfg hm hmi with ⟨byteOff, hsp, haddr, hoff, hbnd⟩
        have hl0 := sepLoad64_kmem (env := env) (F := F) st hcfg hoff hbnd (j := 0) (by omega) (BitVec.add_zero _)
        rw [Nat.add_zero] at hl0
        have hl1 := sepLoad64_kmem (env := env) (F := F) st hcfg hoff hbnd (j := 1) (by omega) rfl
        exact SepWP.step_ldrSimd128 hpc hrun hfetch hsp haddr rfl hl0 hl1 rfl
          (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _ rfl) (pc + 4#64)))
  · -- 33. LDP Qt1, Qt2, [addr]
    next vt1 vt2 addr =>
      by_cases hvt : (vt1 == vt2) = true
      · simp [hvt] at hstep
      · have hvtF : (vt1 == vt2) = false := Bool.eq_false_iff.mpr hvt
        simp only [hvtF, Bool.false_eq_true, ↓reduceIte] at hstep
        cases hmi : resolveMemIdx? cfg st addr 4 with
        | none => simp [hmi] at hstep
        | some p =>
          rcases p with ⟨inB, idx⟩; simp only [hmi, Option.some.injEq] at hstep; subst hstep
          rcases resolveMemIdx_bounds hcfg hm hmi with ⟨byteOff, hsp, haddr, hoff, hbnd⟩
          have hl0 := sepLoad64_kmem (env := env) (F := F) st hcfg hoff hbnd (j := 0) (by omega) (BitVec.add_zero _)
          rw [Nat.add_zero] at hl0
          have hl1 := sepLoad64_kmem (env := env) (F := F) st hcfg hoff hbnd (j := 1) (by omega) rfl
          have hl2 := sepLoad64_kmem (env := env) (F := F) st hcfg hoff hbnd (j := 2) (by omega) rfl
          have hl3 := sepLoad64_kmem (env := env) (F := F) st hcfg hoff hbnd (j := 3) (by omega)
            (ea := (env.sp + BitVec.ofNat 64 byteOff + 16#64) + 8#64)
            (by rw [BitVec.add_assoc _ 16#64 8#64]; rfl)
          exact SepWP.step_ldpSimd128 hpc hrun hfetch hsp haddr rfl rfl rfl hl0 hl1 hl2 hl3 rfl
            (hnext _ rfl hrun (matches_setPC
              (matches_writeVReg (matches_writeVReg hm vt1 _ rfl) vt2 _ rfl) (pc + 4#64)))
  · -- 34. STR Qt, [addr]
    next vt addr =>
      cases hmi : resolveMemIdx? cfg st addr 2 with
      | none => simp [hmi] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩; simp only [hmi, Option.some.injEq] at hstep; subst hstep
        rcases resolveMemIdx_bounds hcfg hm hmi with ⟨byteOff, hsp, haddr, hoff, hbnd⟩
        let vp := st.vregs.get vt.toNat
        have hv0 : (s.readVReg128 vt).extractLsb' 0 64 = evalKExpr env vp.1 := by rw [hm.hvregs vt, extractLsb_lo_append]
        have hv1 : (s.readVReg128 vt).extractLsb' 64 64 = evalKExpr env vp.2 := by rw [hm.hvregs vt, extractLsb_hi_append]
        have hs0 := sepStore64_kmem (env := env) (F := F) st vp.1 hcfg hoff hbnd (j := 0) (by omega) (BitVec.add_zero _)
        rw [Nat.add_zero] at hs0
        have hs1 := sepStore64_kmem (env := env) (F := F) (writeMemWord st inB idx vp.1) vp.2 hcfg hoff hbnd (j := 1) (by omega) rfl
        refine SepWP.step_strSimd128 hpc hrun hfetch hsp haddr rfl hv0 hv1 hs0 hs1 rfl ?_
        intro m'
        exact hnext _ rfl hrun (matches_setMem (matches_setPC
          (matches_writeMemWord (matches_writeMemWord hm inB idx vp.1) inB (idx + 1) vp.2) (pc + 4#64)) m')
  · -- 35. STP Qt1, Qt2, [addr]
    next vt1 vt2 addr =>
      cases hmi : resolveMemIdx? cfg st addr 4 with
      | none => simp [hmi] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩; simp only [hmi, Option.some.injEq] at hstep; subst hstep
        rcases resolveMemIdx_bounds hcfg hm hmi with ⟨byteOff, hsp, haddr, hoff, hbnd⟩
        let v1 := st.vregs.get vt1.toNat; let v2 := st.vregs.get vt2.toNat
        let s1 := writeMemWord (writeMemWord st inB idx v1.1) inB (idx + 1) v1.2
        have hv10 : (s.readVReg128 vt1).extractLsb' 0 64 = evalKExpr env v1.1 := by rw [hm.hvregs vt1, extractLsb_lo_append]
        have hv11 : (s.readVReg128 vt1).extractLsb' 64 64 = evalKExpr env v1.2 := by rw [hm.hvregs vt1, extractLsb_hi_append]
        have hv20 : (s.readVReg128 vt2).extractLsb' 0 64 = evalKExpr env v2.1 := by rw [hm.hvregs vt2, extractLsb_lo_append]
        have hv21 : (s.readVReg128 vt2).extractLsb' 64 64 = evalKExpr env v2.2 := by rw [hm.hvregs vt2, extractLsb_hi_append]
        have hs0 := sepStore64_kmem (env := env) (F := F) st v1.1 hcfg hoff hbnd (j := 0) (by omega) (BitVec.add_zero _)
        rw [Nat.add_zero] at hs0
        have hs1 := sepStore64_kmem (env := env) (F := F) (writeMemWord st inB idx v1.1) v1.2 hcfg hoff hbnd (j := 1) (by omega) rfl
        have hs2 := sepStore64_kmem (env := env) (F := F) s1 v2.1 hcfg hoff hbnd (j := 2) (by omega) rfl
        have hs3 := sepStore64_kmem (env := env) (F := F) (writeMemWord s1 inB (idx + 2) v2.1) v2.2
          hcfg hoff hbnd (j := 3) (by omega) (ea := (env.sp + BitVec.ofNat 64 byteOff + 16#64) + 8#64)
          (by rw [BitVec.add_assoc _ 16#64 8#64]; rfl)
        refine SepWP.step_stpSimd128 hpc hrun hfetch hsp haddr rfl rfl rfl hv10 hv11 hv20 hv21 hs0 hs1 hs2 hs3 rfl ?_
        intro m'
        exact hnext _ rfl hrun (matches_setMem (matches_setPC
          (matches_writeMemWord (matches_writeMemWord
            (matches_writeMemWord (matches_writeMemWord hm inB idx v1.1) inB (idx + 1) v1.2)
            inB (idx + 2) v2.1) inB (idx + 3) v2.2) (pc + 4#64)) m')
  · -- 36. STR Dt, [addr]
    next vt addr =>
      cases hmi : resolveMemIdx? cfg st addr 1 with
      | none => simp [hmi] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩; simp only [hmi, Option.some.injEq] at hstep; subst hstep
        rcases resolveMemIdx_bounds hcfg hm hmi with ⟨byteOff, hsp, haddr, hoff, hbnd⟩
        have hv0 : (s.readVReg128 vt).extractLsb' 0 64 = evalKExpr env (st.vregs.get vt.toNat).1 := by
          rw [hm.hvregs vt, extractLsb_lo_append]
        have hs0 := sepStore64_kmem (env := env) (F := F) st (st.vregs.get vt.toNat).1
          hcfg hoff hbnd (j := 0) (by omega) (BitVec.add_zero _)
        rw [Nat.add_zero] at hs0
        refine SepWP.step_strSimd64 hpc hrun hfetch hsp haddr hv0 hs0 rfl ?_
        intro m'; exact hnext _ rfl hrun (matches_setMem (matches_setPC (matches_writeMemWord hm inB idx _) (pc + 4#64)) m')
  · -- 37. LDR Xt, [addr]
    next rt addr =>
      by_cases hr31 : (rt == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rt == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte] at hstep
        cases hmi : resolveMemIdx? cfg st addr 1 with
        | none => simp [hmi] at hstep
        | some p =>
          rcases p with ⟨inB, idx⟩; simp only [hmi, Option.some.injEq] at hstep; subst hstep
          rcases resolveMemIdx_bounds hcfg hm hmi with ⟨byteOff, hsp, haddr, hoff, hbnd⟩
          have hl0 := sepLoad64_kmem (env := env) (F := F) st hcfg hoff hbnd (j := 0) (by omega) (BitVec.add_zero _)
          rw [Nat.add_zero] at hl0
          exact SepWP.step_ldr64 hpc hrun hfetch hsp haddr hl0 rfl
            (hnext _ rfl hrun (matches_setPC (matches_writeGpr hm (lt31_of_beq_false hr31F) _ rfl) (pc + 4#64)))
  · -- 38. STR XZR, [addr]
    next addr =>
      cases hmi : resolveMemIdx? cfg st addr 1 with
      | none => simp [hmi] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩; simp only [hmi, Option.some.injEq] at hstep; subst hstep
        rcases resolveMemIdx_bounds hcfg hm hmi with ⟨byteOff, hsp, haddr, hoff, hbnd⟩
        have hs0 := sepStore64_kmem (env := env) (F := F) st (.const64 0#64)
          hcfg hoff hbnd (j := 0) (by omega) (BitVec.add_zero _)
        rw [Nat.add_zero] at hs0
        refine SepWP.step_str64 hpc hrun hfetch hsp haddr rfl hs0 rfl ?_
        intro m'; exact hnext _ rfl hrun (matches_setMem (matches_setPC (matches_writeMemWord hm inB idx (.const64 0#64)) (pc + 4#64)) m')
  · -- 39. STR Xt, [addr]
    next rt addr =>
      by_cases hr31 : (rt == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rt == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte] at hstep
        cases hmi : resolveMemIdx? cfg st addr 1 with
        | none => simp [hmi] at hstep
        | some p =>
          rcases p with ⟨inB, idx⟩; simp only [hmi, Option.some.injEq] at hstep; subst hstep
          rcases resolveMemIdx_bounds hcfg hm hmi with ⟨byteOff, hsp, haddr, hoff, hbnd⟩
          have hs0 := sepStore64_kmem (env := env) (F := F) st (st.gprs.get rt.toNat)
            hcfg hoff hbnd (j := 0) (by omega) (BitVec.add_zero _)
          rw [Nat.add_zero] at hs0
          refine SepWP.step_str64 hpc hrun hfetch hsp haddr (hm.hgprs rt (lt31_of_beq_false hr31F)) hs0 rfl ?_
          intro m'; exact hnext _ rfl hrun (matches_setMem (matches_setPC (matches_writeMemWord hm inB idx _) (pc + 4#64)) m')
  · contradiction

/-! ## 3. Multi-Step Range Soundness (`sepWP_of_runKRange`) -/

theorem sepWP_of_runKRange [MlKemPlacement] {b target_pc : BitVec 64}
    {cfg : KCfg} {env : KEnv} {w count : Nat} {st st' : KState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcfg : KCfgWf cfg)
    (hrloop : env.rLoop < 24)
    (hlo : 183 ≤ w)
    (hhi : w + count ≤ 3297)
    (hrun_k : runKRange cfg w count st = some st')
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w))
    (hrun : s.status = .Running)
    (hm : KStateMatches env st s)
    (hnext : ∀ s' : State, s'.pc = b + BitVec.ofNat 64 (4 * (w + count)) → s'.status = .Running →
      KStateMatches env st' s' →
      SepWP (blkPC05.rebase b (fun _ => none)) target_pc s' (KSpatial cfg env st' F) post oom) :
    SepWP (blkPC05.rebase b (fun _ => none)) target_pc s (KSpatial cfg env st F) post oom := by
  induction count generalizing w st s with
  | zero =>
    simp only [runKRange, Option.some.injEq] at hrun_k
    subst hrun_k
    exact hnext s (by simpa [Nat.add_zero] using hpc) hrun hm
  | succ n ih =>
    simp only [runKRange] at hrun_k
    cases hfw : fetchWordTree05 w with
    | none => simp [hfw] at hrun_k
    | some inst =>
      simp only [hfw] at hrun_k
      cases hst : stepKInst cfg inst st with
      | none => simp [hst] at hrun_k
      | some stm =>
        simp only [hst] at hrun_k
        have hfetch := fetch_blk05_seg2 (b := b) hlo (by omega) hfw
        refine sepWP_of_stepKInst hcfg hrloop hpc hrun hfetch hst hm ?_
        intro s1 hpc1 hrun1 hm1
        have hpc1' : s1.pc = b + BitVec.ofNat 64 (4 * (w + 1)) := by
          rw [hpc1, BitVec.add_assoc]; congr 1
          have hmul : 4 * (w + 1) = 4 * w + 4 := by omega
          rw [hmul, BitVec.ofNat_add]
        exact ih (by omega) (by omega) hrun_k hpc1' hrun1 hm1 (fun s2 hpc2 hrun2 hm2 =>
          hnext s2 (by simpa [Nat.add_right_comm, Nat.add_assoc] using hpc2) hrun2 hm2)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep

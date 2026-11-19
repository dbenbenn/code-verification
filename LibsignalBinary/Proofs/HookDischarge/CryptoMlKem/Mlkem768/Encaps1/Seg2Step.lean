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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem

/-!
# `encapsulate1_serialized` (`B03`) — `stepKInst` & `runKRange` Soundness (`Seg2Step`)

Single-instruction (`sepWP_stepKInst`) and multi-instruction (`sepWP_runKRange_seg2a`,
`sepWP_runKRange_seg2b`) `SepWP` bridges for `Seg2` of `B03`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1r_2d)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
  (add_2d_lanes bic_append dup_2d_lane0 dup_2d_lane1 eor_append execInst_zip1_2d execInst_zip2_2d
   extractLsb_hi_append extractLsb_lo_append fneg_2d_eval fneg_2d_satFlags mov_d1_d0
   or_append orr_self_128 usra_2d_satFlags)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (step_ldpQ128 step_ldrQ128 step_stpQ128 step_strQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge
  (addSubImm_delta_eq fmov_d0_append movz_w32_eq_writeReg64 shl_2d_eval)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (blkPC03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
  (KCfg KEnv KExpr KState evalKExpr eval_smartAdd64 eval_smartUsra fetchWordTree03
   readMemWord resolveMemIdx? runKRange stepKInst usraRot? writeMemWord)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem
  (fetch_blk03_seg2a fetch_blk03_seg2b)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge
  (KCfgWf KPFlagMatches KSpatial KStateMatches bsl_append dupScalar_d1_append
   fromZRBits_of_beq_false insByte0_append matches_advancePC matches_setMem matches_setPC
   matches_setPFlag matches_writeGpr matches_writeMemWord matches_writeVReg ne31_of_beq_false
   sepLoad128_constsLo_48 sepLoad128_constsLo_64 sepLoad128_kspatial sepLoad256_kspatial
   sepLoad64_constsLo_40 sepLoad64_constsLo_88 sepLoad64_kspatial sepLoad64_rcBase
   sepStore128_kspatial sepStore256_kspatial sepStore64_kspatial step_strSimd64
   umov_d1_append usra_eval_of_usraRot?)

/-! ## 1. Pure & GPR Memory Step Combinators -/

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
    (hrd : rd ≠ 31#5)
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

private theorem truncate64_append (a1 a0 : BitVec 64) : (a1 ++ a0).truncate 64 = a0 := by bv_bits

private theorem addr_eq_sp_off {addr : AddrMode} {off : BitVec 64}
    (h : (addr == .Offset .sp off) = true) : addr = .Offset .sp off := by
  cases addr with
  | Offset base off' =>
    cases base with
    | sp => change (true && (off' == off)) = true at h; exact congrArg _ (beq_iff_eq.mp h)
    | gpr _ | xzr => cases h
  | _ => cases h

/-! ## 2. Single-Instruction Symbolic Stepper Soundness (`sepWP_stepKInst`) -/

theorem sepWP_stepKInst {prog : Program} {target_pc pc : BitVec 64}
    {cfg : KCfg} (hv : KCfgWf cfg) {env : KEnv} {st st' : KState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {inst : Instr}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some inst)
    (hm : KStateMatches env st s) (hrBound : env.rLoop < 24)
    (hstep : stepKInst cfg inst st = some st')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      KStateMatches env st' s' → SepWP prog target_pc s' (KSpatial cfg env st' F) post oom) :
    SepWP prog target_pc s (KSpatial cfg env st F) post oom := by
  unfold stepKInst at hstep; split at hstep
  · next rm rn rd => -- 1. ADD Vd.2D, Vn.2D, Vm.2D
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change zipSimdLanes true 64 (s.readVReg128 rn) (s.readVReg128 rm) (· + ·) = _
      rw [hm.hvregs rn, hm.hvregs rm]
      simp only [zipSimdLanes_true_64, zipLanes, laneMask_64, Nat.zero_mul, Nat.one_mul,
        add_2d_lanes, extractLsb_hi_append, extractLsb_lo_append, evalKExpr]
  · next rm rn rd => -- 2. EOR Vd.16B, Vn.16B, Vm.16B
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change s.readVReg128 rn ^^^ s.readVReg128 rm = _
      rw [hm.hvregs rn, hm.hvregs rm, eor_append]; rfl
  · next rm rn rd => -- 3. BIC Vd.16B, Vn.16B, Vm.16B
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change s.readVReg128 rn &&& ~~~(s.readVReg128 rm) = _
      rw [hm.hvregs rn, hm.hvregs rm, bic_append]; rfl
  · next rm rn rd => -- 4. ORR Vd.16B, Vn.16B, Vm.16B
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change s.readVReg128 rn ||| s.readVReg128 rm = _
      by_cases hrm : (rm == rn) = true
      · have hrmEq : rm = rn := beq_iff_eq.mp hrm
        subst hrmEq; simp only [beq_self_eq_true, ↓reduceIte, orr_self_128, hm.hvregs]
      · simp only [Bool.eq_false_iff.mpr hrm, Bool.false_eq_true, ↓reduceIte]
        rw [hm.hvregs rn, hm.hvregs rm, or_append]; rfl
  · next rm rn rd => -- 5. BSL Vd.16B, Vn.16B, Vm.16B
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change ((s.readVReg128 rn ^^^ s.readVReg128 rm) &&& s.readVReg128 rd) ^^^ s.readVReg128 rm = _
      rw [hm.hvregs rd, hm.hvregs rn, hm.hvregs rm, bsl_append]; rfl
  · next rm rn rd => -- 6. ZIP1 Vd.2D, Vn.2D, Vm.2D
      simp only [Option.some.injEq] at hstep; subst hstep
      exact step_vreg_pure
        (res := (s.readVReg128 rm).extractLsb' 0 64 ++ (s.readVReg128 rn).extractLsb' 0 64)
        hpc hrun hfetch
        (by change execInst (.simdPermute true 0x3#2 rm 0x3#3 rn rd) (s.setPC pc) = _; rw [execInst_zip1_2d]; rfl)
        (by rw [hm.hvregs rn, hm.hvregs rm, extractLsb_lo_append, extractLsb_lo_append]) hm hnext
  · next rm rn rd => -- 7. ZIP2 Vd.2D, Vn.2D, Vm.2D
      simp only [Option.some.injEq] at hstep; subst hstep
      exact step_vreg_pure
        (res := (s.readVReg128 rm).extractLsb' 64 64 ++ (s.readVReg128 rn).extractLsb' 64 64)
        hpc hrun hfetch
        (by change execInst (.simdPermute true 0x3#2 rm 0x7#3 rn rd) (s.setPC pc) = _; rw [execInst_zip2_2d]; rfl)
        (by rw [hm.hvregs rn, hm.hvregs rm, extractLsb_hi_append, extractLsb_hi_append]) hm hnext
  · next rn rd => -- 8. FNEG Vd.2D, Vn.2D
      simp only [Option.some.injEq] at hstep; subst hstep
      exact step_vreg_pure
        (res := ((s.readVReg128 rn).extractLsb' 64 64 ^^^ 0x8000000000000000#64) ++
          ((s.readVReg128 rn).extractLsb' 0 64 ^^^ 0x8000000000000000#64)) hpc hrun hfetch
        (by simp only [Program.evalInst, execInstWithSvc, ↓reduceIte, Bool.not_true,
              fneg_2d_eval, fneg_2d_satFlags, applySimdSatResult]; rfl)
        (by rw [hm.hvregs rn, extractLsb_hi_append, extractLsb_lo_append]; rfl) hm hnext
  · next rd => -- 9. MOVI Vd.2D, #0
      simp only [Option.some.injEq] at hstep; subst hstep
      exact step_vreg_pure (res := 0#128) hpc hrun hfetch
        (by simp [Program.evalInst, execInstWithSvc])
        (by change 0#128 = 0#64 ++ 0#64; decide) hm hnext
  · next rd => -- 10. MOVI Vd.8H, #31
      simp only [Option.some.injEq] at hstep; subst hstep
      exact step_vreg_pure (res := 0x001f001f001f001f001f001f001f001f#128) hpc hrun hfetch
        (by simp [Program.evalInst, execInstWithSvc])
        (by change 0x001f001f001f001f001f001f001f001f#128 =
              0x001f001f001f001f#64 ++ 0x001f001f001f001f#64; decide) hm hnext
  · next immh immb rn rd => -- 11. SHL Vd.2D, Vn.2D, #sh
      by_cases hlt8 : Nat.blt immh.toNat 8 = true
      · simp [hlt8] at hstep
      · have hlt8F : Nat.blt immh.toNat 8 = false := Bool.eq_false_iff.mpr hlt8
        simp only [hlt8F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        have hge : ¬(immh.toNat < 8) := fun h => hlt8 (Nat.blt_eq.mpr h)
        have hnez : (immh == 0#4) = false := beq_eq_false_iff_ne.mpr fun h0 => by
          subst h0; exact hge (by decide)
        let immhb := (immh ++ immb).toNat
        let esize := if immhb >= 64 then 64 else if immhb >= 32 then 32 else if immhb >= 16 then 16 else 8
        refine step_vreg_pure
          (res := mapSimdLanes true esize (s.readVReg128 rn) (fun lane => lane <<< (immhb - esize)))
          hpc hrun hfetch ?_ ?_ hm hnext
        · simp only [Program.evalInst, execInstWithSvc, hnez, Bool.false_eq_true, ↓reduceIte,
            Bool.not_false, Bool.not_true, Bool.and_false, Bool.true_and,
            show (0x0a#5 == 0b01010#5) = true from rfl]; rfl
        · rw [hm.hvregs rn]; exact shl_2d_eval immh immb hge _ _
  · next immh immb rn rd => -- 12. USRA Vd.2D, Vn.2D, #r
      cases husra : usraRot? immh immb with
      | none => simp [husra] at hstep
      | some r =>
        simp only [husra, Option.some.injEq] at hstep; subst hstep
        rcases usra_eval_of_usraRot? husra (evalKExpr env (st.vregs.get rd.toNat).2)
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
  · next rn rd => -- 13. INS Vd.B[0], Wn
      by_cases hr31 : (rn == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rn == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
        change ((s.readVReg128 rd &&& ~~~(((1#128 <<< 8) - 1#128) <<< 0)) |||
          ((((s.readReg64 (Reg.fromZRBits rn)).zeroExtend 128) &&& ((1#128 <<< 8) - 1#128)) <<< 0)) = _
        rw [fromZRBits_of_beq_false hr31F, hm.hgprs rn (ne31_of_beq_false hr31F),
            hm.hvregs rd, insByte0_append]; rfl
  · next rn rd => -- 14. DUP Vd.2D, Vn.D[0]
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change mapSimdLanes true 64 0#128 (fun _ => getSimdLane (s.readVReg128 rn) 64 0) = _
      rw [hm.hvregs rn]
      simp only [mapSimdLanes_true_64, mapLanes, laneMask_64, getSimdLane, Nat.zero_mul, Nat.one_mul,
        show (1#128 <<< 64 - 1#128) = 0xffffffffffffffff#128 from rfl,
        dup_2d_lane0, extractLsb_lo_append]
  · next rn rd => -- 15. DUP Vd.2D, Vn.D[1]
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change mapSimdLanes true 64 0#128 (fun _ => getSimdLane (s.readVReg128 rn) 64 1) = _
      rw [hm.hvregs rn]
      simp only [mapSimdLanes_true_64, mapLanes, laneMask_64, getSimdLane, Nat.zero_mul, Nat.one_mul,
        show (1#128 <<< 64 - 1#128) = 0xffffffffffffffff#128 from rfl,
        dup_2d_lane1, extractLsb_hi_append]
  · next rn rd => -- 16. MOV Vd.D[1], Vn.D[0]
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change ((s.readVReg128 rd &&& ~~~(((1#128 <<< 64) - 1#128) <<< 64)) |||
        (getSimdLane (s.readVReg128 rn) 64 0 <<< 64)) = _
      rw [hm.hvregs rd, hm.hvregs rn]; unfold getSimdLane
      have hm1 : (~~~(((1#128 <<< 64) - 1#128) <<< 64) : BitVec 128) = 0xffffffffffffffff#128 := by decide
      have hm2 : ((1#128 <<< 64) - 1#128 : BitVec 128) = 0xffffffffffffffff#128 := by decide
      rw [hm1, hm2, mov_d1_d0, extractLsb_lo_append, extractLsb_lo_append]
  · next rn rd => -- 17. MOV Dd, Vn.D[1]
      simp only [Option.some.injEq] at hstep; subst hstep
      refine step_vreg_pure hpc hrun hfetch rfl ?_ hm hnext
      change evalSimdDupScalar 0x18#5 (s.readVReg128 rn) = _
      rw [hm.hvregs rn, dupScalar_d1_append]; rfl
  · next rn rd => -- 18. UMOV Xd, Vn.D[1]
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        exact step_gpr_pure (res := (getSimdLane (s.readVReg128 rn) 64 1).truncate 64)
          (ne31_of_beq_false hr31F) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, fromZRBits_of_beq_false hr31F]; rfl)
          (by rw [hm.hvregs rn, umov_d1_append]) hm hnext
  · next rn rd => -- 19. FMOV Xd, Dn
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        exact step_gpr_pure (res := s.readVReg64 rn) (ne31_of_beq_false hr31F) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, fromZRBits_of_beq_false hr31F]; rfl)
          (fmov_d0_append s rn _ _ (hm.hvregs rn)) hm hnext
  · -- 20. LD1R {Vt.2D}, [Xn]
    next rn vt =>
      by_cases hr31 : (rn == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rn == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte] at hstep
        have hrnNe := ne31_of_beq_false hr31F
        cases hg : st.gprs.get rn.toNat <;> simp only [hg] at hstep <;> try contradiction
        case rcLoopPtr =>
          simp only [Option.some.injEq] at hstep; subst hstep
          have hea : s.readReg64 (.gpr rn) = env.rcBase + BitVec.ofNat 64 (8 * env.rLoop) := by
            rw [hm.hgprs rn hrnNe, hg]; rfl
          exact step_simdLd1r_2d hpc hrun hfetch rfl hea
            (sepLoad64_rcBase hrBound rfl) rfl
            (hnext _ rfl hrun
              (matches_setPC (matches_writeVReg hm vt (.rcLoopVal, .rcLoopVal) rfl) (pc + 4#64)))
        case rcAdd off =>
          split at hstep <;> [skip; contradiction]
          next hc =>
            simp only [Option.some.injEq] at hstep; subst hstep
            simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, beq_iff_eq] at hc
            rcases hc with ⟨⟨_, hk24⟩, hoff⟩
            have hea : s.readReg64 (.gpr rn) = env.rcBase + BitVec.ofNat 64 (8 * (off.toNat / 8)) := by
              rw [hm.hgprs rn hrnNe, hg]; dsimp [evalKExpr]
              conv_lhs => rw [hoff]
              congr 2; omega
            exact step_simdLd1r_2d hpc hrun hfetch rfl hea (sepLoad64_rcBase hk24 rfl) rfl
              (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _ rfl) (pc + 4#64)))
  · -- 21. ADD Xd, SP, #imm12{, LSL #12}
    next rd imm12 shift12 =>
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        refine step_gpr_pure (res := (AddWithCarry64 ((s.setPC pc).readReg .W64 .sp)
            (if shift12 then imm12.zeroExtend 64 <<< 12 else imm12.zeroExtend 64) false).1)
          (ne31_of_beq_false hr31F) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, execAddSubImm, evalAddSub, State.writeReg,
                Bool.false_eq_true, ↓reduceIte]) ?_ hm hnext
        rw [show (s.setPC pc).readReg .W64 .sp = s.sp from rfl,
            addWithCarry64_add_fst, hm.hsp, addSubImm_delta_eq]; rfl
  · -- 22. ADD Xd, Xn, #imm12{, LSL #12}
    next rd rn imm12 shift12 =>
      by_cases hrr : (rd == 31#5 || rn == 31#5) = true
      · simp [hrr] at hstep
      · have hrrF : (rd == 31#5 || rn == 31#5) = false := Bool.eq_false_iff.mpr hrr
        simp only [hrrF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        rcases Bool.or_eq_false_iff.mp hrrF with ⟨hrdF, hrnF⟩
        refine step_gpr_pure (res := (AddWithCarry64 ((s.setPC pc).readReg .W64 (.gpr rn))
            (if shift12 then imm12.zeroExtend 64 <<< 12 else imm12.zeroExtend 64) false).1)
          (ne31_of_beq_false hrdF) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, execAddSubImm, evalAddSub, State.writeReg,
                Bool.false_eq_true, ↓reduceIte]) ?_ hm hnext
        rw [show (s.setPC pc).readReg .W64 (.gpr rn) = s.readReg64 (.gpr rn) from rfl,
            addWithCarry64_add_fst, hm.hgprs rn (ne31_of_beq_false hrnF),
            addSubImm_delta_eq, eval_smartAdd64]; rfl
  · -- 23. ADD Xd, Xn, Xm, LSL #0
    next rd rn rm =>
      by_cases hrr : (rd == 31#5 || rn == 31#5 || rm == 31#5) = true
      · simp [hrr] at hstep
      · have hrrF : (rd == 31#5 || rn == 31#5 || rm == 31#5) = false := Bool.eq_false_iff.mpr hrr
        simp only [hrrF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        rcases Bool.or_eq_false_iff.mp hrrF with ⟨hrdnF, hrmF⟩
        rcases Bool.or_eq_false_iff.mp hrdnF with ⟨hrdF, hrnF⟩
        refine step_gpr_pure (res := (AddWithCarry64 ((s.setPC pc).readReg .W64 (.gpr rn))
            (shiftVal .W64 ((s.setPC pc).readReg .W64 (.gpr rm)) .LSL 0) false).1)
          (ne31_of_beq_false hrdF) hpc hrun hfetch
          (by simp only [Program.evalInst, execInstWithSvc, execAddSubShift, evalAddSub, State.writeReg,
                Bool.false_eq_true, ↓reduceIte]) ?_ hm hnext
        rw [show (s.setPC pc).readReg .W64 (.gpr rn) = s.readReg64 (.gpr rn) from rfl,
            show (s.setPC pc).readReg .W64 (.gpr rm) = s.readReg64 (.gpr rm) from rfl,
            addWithCarry64_add_fst, hm.hgprs rn (ne31_of_beq_false hrnF),
            hm.hgprs rm (ne31_of_beq_false hrmF), eval_smartAdd64]
        simp [shiftVal, shift64]
  · -- 24. SUBS XZR, Xn, #imm12
    next rn imm12 =>
      by_cases hr31 : (rn == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rn == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte] at hstep
        have hrnNe := ne31_of_beq_false hr31F
        have hexec : prog.evalInst (.addSubImm .W64 .SUBS .xzr (.gpr rn) imm12 false) (s.setPC pc) =
            ((s.setPC pc).setPState (subsPState64 (s.readReg64 (.gpr rn)) (imm12.zeroExtend 64))).advancePC := by
          simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.writeReg]
        cases hg : st.gprs.get rn.toNat
        all_goals simp only [hg] at hstep
        case rcLoopNext =>
          split at hstep <;> [skip; contradiction]
          next himm =>
            have himmEq : imm12 = 192#12 := beq_iff_eq.mp himm
            subst himmEq
            simp only [Option.some.injEq] at hstep; subst hstep
            exact SepWP.step_pure hpc hrun hfetch hexec rfl
              (hnext _ rfl hrun (matches_advancePC (matches_setPFlag (matches_setPC hm pc) (some .loopDone)
                (by simpa [KPFlagMatches, hg, evalKExpr] using
                  congrArg (subsPState64 · 192#64) (hm.hgprs rn hrnNe)))))
        all_goals
          simp only [Option.some.injEq] at hstep; subst hstep
          exact SepWP.step_pure hpc hrun hfetch hexec rfl
            (hnext _ rfl hrun (matches_advancePC (matches_setPFlag (matches_setPC hm pc) _
              (by simpa [KPFlagMatches, hg] using
                congrArg (subsPState64 · (imm12.zeroExtend 64)) (hm.hgprs rn hrnNe)))))
  · -- 25. CSEL Xd, Xn, Xm, HI
    next rd rn rm =>
      by_cases hrr : (rd == 31#5 || rn == 31#5 || rm == 31#5) = true
      · simp [hrr] at hstep
      · have hrrF : (rd == 31#5 || rn == 31#5 || rm == 31#5) = false := Bool.eq_false_iff.mpr hrr
        simp only [hrrF, Bool.false_eq_true, ↓reduceIte] at hstep
        rcases Bool.or_eq_false_iff.mp hrrF with ⟨hrdnF, hrmF⟩
        rcases Bool.or_eq_false_iff.mp hrdnF with ⟨hrdF, hrnF⟩
        split at hstep <;> [skip; contradiction]
        next lhs hpst =>
          split at hstep <;> [skip; contradiction]
          next hchk =>
            simp only [Option.some.injEq] at hstep; subst hstep
            rw [Bool.and_eq_true] at hchk
            have hrnE : st.gprs.get rn.toNat = .const64 256#64 := beq_iff_eq.mp hchk.1
            have hrmE : st.gprs.get rm.toNat = lhs := KExpr.beq_eq_true hchk.2
            have hps : s.pstate = subsPState64 (evalKExpr env lhs) 255#64 := by
              simpa [KPFlagMatches, hpst] using hm.hpflag
            refine step_gpr_pure (ne31_of_beq_false hrdF) hpc hrun hfetch rfl ?_ hm hnext
            change (if ConditionHolds .HI s.pstate = true then s.readReg64 (.gpr rn)
              else s.readReg64 (.gpr rm)) = _
            rw [hps, hm.hgprs rn (ne31_of_beq_false hrnF), hm.hgprs rm (ne31_of_beq_false hrmF),
                hrnE, hrmE]; rfl
  · -- 26. MOVZ Wd, #imm16
    next rd imm16 =>
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        refine step_gpr_pure (ne31_of_beq_false hr31F) hpc hrun hfetch ?_ rfl hm hnext
        change (((s.setPC pc).writeReg .W32 (.gpr rd) ((imm16.zeroExtend 64) <<< 0)).advancePC) = _
        rw [movz_w32_eq_writeReg64]; rfl
  · -- 27. ORR Wd, WZR, WZR
    next rd =>
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        exact step_gpr_pure (res := 0#64) (ne31_of_beq_false hr31F) hpc hrun hfetch
          (by simp [Program.evalInst, execInstWithSvc, execLogicalShift, evalLogical,
                shiftVal, shift32, State.writeReg, State.readReg, State.readReg32, State.readReg64])
          rfl hm hnext
  · -- 28. ORR Xd, XZR, XZR
    next rd =>
      by_cases hr31 : (rd == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rd == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        exact step_gpr_pure (ne31_of_beq_false hr31F) hpc hrun hfetch
          (by dsimp only [Program.evalInst, execInstWithSvc, execLogicalShift, evalLogical,
                shiftVal, shift64, State.writeReg, State.readReg, State.readReg64]; rfl)
          rfl hm hnext
  · -- 29. ORR Xd, XZR, Xm
    next rd rm =>
      by_cases hrr : (rd == 31#5 || rm == 31#5) = true
      · simp [hrr] at hstep
      · have hrrF : (rd == 31#5 || rm == 31#5) = false := Bool.eq_false_iff.mpr hrr
        simp only [hrrF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        rcases Bool.or_eq_false_iff.mp hrrF with ⟨hrdF, hrmF⟩
        refine step_gpr_pure (res := 0#64 ||| shiftVal .W64 (s.readReg64 (.gpr rm)) .LSL 0)
          (ne31_of_beq_false hrdF) hpc hrun hfetch
          (by dsimp only [Program.evalInst, execInstWithSvc, execLogicalShift, evalLogical, State.writeReg]; rfl)
          ?_ hm hnext
        rw [hm.hgprs rm (ne31_of_beq_false hrmF)]
        simp [shiftVal, shift64]
  · -- 30. LDR Qt, [addr]
    next vt addr =>
      by_cases hc48 : (cfg.hasConstsLo && addr == .Offset .sp 48#64) = true
      · simp only [hc48, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
        rw [Bool.and_eq_true] at hc48; rw [addr_eq_sp_off hc48.2] at hfetch
        exact step_ldrQ128 (wb := none) hpc hrun hfetch
          (by simp [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, hm.hsp_al])
          (by simp [evalAddrMode, hm.hsp]) (sepLoad128_constsLo_48 hc48.1) rfl
          (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _ rfl) (pc + 4#64)))
      · simp only [Bool.eq_false_iff.mpr hc48, Bool.false_eq_true, ↓reduceIte] at hstep
        by_cases hc64 : (cfg.hasConstsLo && addr == .Offset .sp 64#64) = true
        · simp only [hc64, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          rw [Bool.and_eq_true] at hc64; rw [addr_eq_sp_off hc64.2] at hfetch
          exact step_ldrQ128 (wb := none) hpc hrun hfetch
            (by simp [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, hm.hsp_al])
            (by simp [evalAddrMode, hm.hsp]) (sepLoad128_constsLo_64 hc64.1) rfl
            (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _ rfl) (pc + 4#64)))
        · simp only [Bool.eq_false_iff.mpr hc64, Bool.false_eq_true, ↓reduceIte] at hstep
          cases hr : resolveMemIdx? cfg st addr 2 with
          | none => simp [hr] at hstep
          | some p =>
            rcases p with ⟨inB, idx⟩
            simp only [hr, Option.some.injEq] at hstep; subst hstep
            rcases sepLoad128_kspatial hv hm hr F with ⟨ea, hsp, haddr, hload⟩
            exact step_ldrQ128 hpc hrun hfetch hsp haddr hload rfl
              (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _ rfl) (pc + 4#64)))
  · -- 31. LDP Qt1, Qt2, [addr]
    next vt1 vt2 addr =>
      by_cases hvt : (vt1 == vt2) = true
      · simp [hvt] at hstep
      · have hvtF : (vt1 == vt2) = false := Bool.eq_false_iff.mpr hvt
        simp only [hvtF, Bool.false_eq_true, ↓reduceIte] at hstep
        cases hr : resolveMemIdx? cfg st addr 4 with
        | none => simp [hr] at hstep
        | some p =>
          rcases p with ⟨inB, idx⟩
          simp only [hr, Option.some.injEq] at hstep; subst hstep
          rcases sepLoad256_kspatial hv hm hr F with ⟨ea, hsp, haddr, hl1, hl2⟩
          exact step_ldpQ128 hpc hrun hfetch hsp haddr rfl hl1 hl2 rfl
            (hnext _ rfl hrun (matches_setPC
              (matches_writeVReg (matches_writeVReg hm vt1 _ rfl) vt2 _ rfl) (pc + 4#64)))
  · -- 32. STR Qt, [addr]
    next vt addr =>
      cases hr : resolveMemIdx? cfg st addr 2 with
      | none => simp [hr] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩
        simp only [hr, Option.some.injEq] at hstep; subst hstep
        rcases sepStore128_kspatial hv hm hr (st.vregs.get vt.toNat).1
          (st.vregs.get vt.toNat).2 F with ⟨ea, hsp, haddr, hstr⟩
        refine step_strQ128 hpc hrun hfetch hsp haddr (hm.hvregs vt) hstr rfl (fun m' => ?_)
        exact hnext _ (by simp [State.setMem, State.setPC, applyWriteback])
          (by simp [State.setMem, State.setPC, applyWriteback, hrun])
          (matches_setMem (matches_setPC
            (matches_writeMemWord (matches_writeMemWord hm inB idx _) inB (idx + 1) _)
            (pc + 4#64)) m')
  · -- 33. STP Qt1, Qt2, [addr]
    next vt1 vt2 addr =>
      cases hr : resolveMemIdx? cfg st addr 4 with
      | none => simp [hr] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩
        simp only [hr, Option.some.injEq] at hstep; subst hstep
        rcases sepStore256_kspatial hv hm hr
          (st.vregs.get vt1.toNat).1 (st.vregs.get vt1.toNat).2
          (st.vregs.get vt2.toNat).1 (st.vregs.get vt2.toNat).2 F with ⟨ea, hsp, haddr, hs1, hs2⟩
        refine step_stpQ128 hpc hrun hfetch hsp haddr rfl (hm.hvregs vt1) (hm.hvregs vt2)
          hs1 hs2 rfl (fun m' => ?_)
        exact hnext _ (by simp [State.setMem, State.setPC, applyWriteback])
          (by simp [State.setMem, State.setPC, applyWriteback, hrun])
          (matches_setMem (matches_setPC
            (matches_writeMemWord (matches_writeMemWord
              (matches_writeMemWord (matches_writeMemWord hm inB idx _) inB (idx + 1) _)
              inB (idx + 2) _) inB (idx + 3) _) (pc + 4#64)) m')
  · -- 34. STR Dt, [addr]
    next vt addr =>
      cases hr : resolveMemIdx? cfg st addr 1 with
      | none => simp [hr] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩
        simp only [hr, Option.some.injEq] at hstep; subst hstep
        rcases sepStore64_kspatial hv hm hr (st.vregs.get vt.toNat).1 F with ⟨ea, hsp, haddr, hstr⟩
        refine step_strSimd64 hpc hrun hfetch hsp haddr
          (by rw [hm.hvregs vt, truncate64_append]) hstr rfl (fun m' => ?_)
        exact hnext _ (by simp [State.setMem, State.setPC, applyWriteback])
          (by simp [State.setMem, State.setPC, applyWriteback, hrun])
          (matches_setMem (matches_setPC (matches_writeMemWord hm inB idx _) (pc + 4#64)) m')
  · -- 35. LDR Xt, [addr]
    next rt addr =>
      by_cases hr31 : (rt == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rt == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte] at hstep
        have hrtNe := ne31_of_beq_false hr31F
        by_cases hc40 : (cfg.hasConstsLo && addr == .Offset .sp 40#64) = true
        · simp only [hc40, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          rw [Bool.and_eq_true] at hc40; rw [addr_eq_sp_off hc40.2] at hfetch
          exact SepWP.step_ldr64 (wb := none) hpc hrun hfetch
            (by simp [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, hm.hsp_al])
            (by simp [evalAddrMode, hm.hsp]) (sepLoad64_constsLo_40 hc40.1) rfl
            (hnext _ rfl hrun (matches_setPC (matches_writeGpr hm hrtNe (.spAdd 3496#64) rfl) (pc + 4#64)))
        · simp only [Bool.eq_false_iff.mpr hc40, Bool.false_eq_true, ↓reduceIte] at hstep
          by_cases hc88 : (cfg.hasConstsLo && addr == .Offset .sp 88#64) = true
          · simp only [hc88, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
            rw [Bool.and_eq_true] at hc88; rw [addr_eq_sp_off hc88.2] at hfetch
            exact SepWP.step_ldr64 (wb := none) hpc hrun hfetch
              (by simp [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, hm.hsp_al])
              (by simp [evalAddrMode, hm.hsp]) (sepLoad64_constsLo_88 hc88.1) rfl
              (hnext _ rfl hrun (matches_setPC (matches_writeGpr hm hrtNe (.spAdd 2203#64) rfl) (pc + 4#64)))
          · simp only [Bool.eq_false_iff.mpr hc88, Bool.false_eq_true, ↓reduceIte] at hstep
            cases hr : resolveMemIdx? cfg st addr 1 with
            | none => simp [hr] at hstep
            | some p =>
              rcases p with ⟨inB, idx⟩
              simp only [hr, Option.some.injEq] at hstep; subst hstep
              rcases sepLoad64_kspatial hv hm hr F with ⟨ea, hsp, haddr, hload⟩
              exact SepWP.step_ldr64 hpc hrun hfetch hsp haddr hload rfl
                (hnext _ rfl hrun (matches_setPC (matches_writeGpr hm hrtNe _ rfl) (pc + 4#64)))
  · -- 36. STR XZR, [addr]
    next addr =>
      cases hr : resolveMemIdx? cfg st addr 1 with
      | none => simp [hr] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩
        simp only [hr, Option.some.injEq] at hstep; subst hstep
        rcases sepStore64_kspatial hv hm hr (.const64 0#64) F with ⟨ea, hsp, haddr, hs0⟩
        exact SepWP.step_str64 hpc hrun hfetch hsp haddr rfl hs0 rfl (fun m' =>
          hnext _ rfl hrun (matches_setMem
            (matches_setPC (matches_writeMemWord hm inB idx (.const64 0#64)) (pc + 4#64)) m'))
  · -- 37. STR Xt, [addr]
    next rt addr =>
      by_cases hr31 : (rt == 31#5) = true
      · simp [hr31] at hstep
      · have hr31F : (rt == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hr31F, Bool.false_eq_true, ↓reduceIte] at hstep
        cases hr : resolveMemIdx? cfg st addr 1 with
        | none => simp [hr] at hstep
        | some p =>
          rcases p with ⟨inB, idx⟩
          simp only [hr, Option.some.injEq] at hstep; subst hstep
          rcases sepStore64_kspatial hv hm hr (st.gprs.get rt.toNat) F with ⟨ea, hsp, haddr, hs0⟩
          exact SepWP.step_str64 hpc hrun hfetch hsp haddr
            (hm.hgprs rt (ne31_of_beq_false hr31F)) hs0 rfl (fun m' =>
              hnext _ rfl hrun (matches_setMem
                (matches_setPC (matches_writeMemWord hm inB idx _) (pc + 4#64)) m'))
  · contradiction

/-! ## 3. Multi-Instruction Symbolic Range Soundness (`sepWP_runKRange_seg2a`, `sepWP_runKRange_seg2b`) -/

private theorem sepWP_runKRange_gen {prog : Program} {b target_pc : BitVec 64} {cfg : KCfg}
    (hv : KCfgWf cfg) {env : KEnv} (hrBound : env.rLoop < 24) {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {w n : Nat} {st st' : KState} {s : State}
    (hfetches : ∀ j inst, w ≤ j → j < w + n → fetchWordTree03 j = some inst →
      prog.fetch (b + BitVec.ofNat 64 (4 * j)) = some inst)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hm : KStateMatches env st s) (hkr : runKRange cfg w n st = some st')
    (hnext : ∀ s' : State, s'.pc = b + BitVec.ofNat 64 (4 * (w + n)) → s'.status = .Running →
      KStateMatches env st' s' → SepWP prog target_pc s' (KSpatial cfg env st' F) post oom) :
    SepWP prog target_pc s (KSpatial cfg env st F) post oom := by
  induction n generalizing w st s with
  | zero => simp only [runKRange, Option.some.injEq] at hkr; subst hkr; exact hnext s (by simpa using hpc) hrun hm
  | succ n' ih =>
      simp only [runKRange] at hkr
      cases hfw : fetchWordTree03 w with
      | none => simp [hfw] at hkr
      | some inst =>
          simp only [hfw] at hkr
          cases hst : stepKInst cfg inst st with
          | none => simp [hst] at hkr
          | some stm =>
              simp only [hst] at hkr
              refine sepWP_stepKInst hv hpc hrun (hfetches w inst (Nat.le_refl w) (by omega) hfw)
                hm hrBound hst (fun s1 hpc1 hrun1 hm1 => ?_)
              exact ih (fun j i hj1 hj2 hfi => hfetches j i (by omega) (by omega) hfi)
                (by rw [hpc1]; bv_omega) hrun1 hm1 hkr (fun s' hpc' hrun' hm' => hnext s'
                  (by simpa [Nat.add_assoc, Nat.add_comm 1 n'] using hpc') hrun' hm')

theorem sepWP_runKRange_seg2a [MlKemPlacement] {b target_pc : BitVec 64} {cfg : KCfg}
    (hv : KCfgWf cfg) {env : KEnv} (hrBound : env.rLoop < 24) {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {w n : Nat} {st st' : KState} {s : State}
    (hlo : 155 ≤ w) (hhi : w + n ≤ 329)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hm : KStateMatches env st s) (hkr : runKRange cfg w n st = some st')
    (hnext : ∀ s' : State, s'.pc = b + BitVec.ofNat 64 (4 * (w + n)) → s'.status = .Running →
      KStateMatches env st' s' →
      SepWP (blkPC03.rebase b (fun _ => none)) target_pc s' (KSpatial cfg env st' F) post oom) :
    SepWP (blkPC03.rebase b (fun _ => none)) target_pc s (KSpatial cfg env st F) post oom :=
  sepWP_runKRange_gen hv hrBound
    (fun _ _ hj1 hj2 hfw => fetch_blk03_seg2a (by omega) (by omega) hfw)
    hpc hrun hm hkr hnext

theorem sepWP_runKRange_seg2b [MlKemPlacement] {b target_pc : BitVec 64} {cfg : KCfg}
    (hv : KCfgWf cfg) {env : KEnv} (hrBound : env.rLoop < 24) {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {w n : Nat} {st st' : KState} {s : State}
    (hlo : 330 ≤ w) (hhi : w + n ≤ 3237)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hm : KStateMatches env st s) (hkr : runKRange cfg w n st = some st')
    (hnext : ∀ s' : State, s'.pc = b + BitVec.ofNat 64 (4 * (w + n)) → s'.status = .Running →
      KStateMatches env st' s' →
      SepWP (blkPC03.rebase b (fun _ => none)) target_pc s' (KSpatial cfg env st' F) post oom) :
    SepWP (blkPC03.rebase b (fun _ => none)) target_pc s (KSpatial cfg env st F) post oom :=
  sepWP_runKRange_gen hv hrBound
    (fun _ _ hj1 hj2 hfw => fetch_blk03_seg2b (by omega) (by omega) hfw)
    hpc hrun hm hkr hnext

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step

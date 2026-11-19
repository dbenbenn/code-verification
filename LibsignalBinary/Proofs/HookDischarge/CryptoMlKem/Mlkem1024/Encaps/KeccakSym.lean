/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval

/-!
# `kyber_encapsulate` (`B07`) — Symbolic Keccak & Slot Stepper Soundness (`KeccakSym`)

Proves 1-step (`sepWP_of_stepKInst`) and `N`-step (`sepWP_of_runKRange`) separation-logic
soundness for `stepKInst` and `runKRange` over any relocation-free instruction range of `B07`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSym

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1r_2d)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp (
  bic_append eor_append extractLsb_lo_append fneg_2d_eval fneg_2d_satFlags usra_2d_satFlags
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  step_ldpQ128 step_ldrQ128 step_stpQ128 step_strQ128
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blkPC07 fetchWordTree07
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  KCfg KEnv KExpr KState evalKExpr eval_smartAdd64 eval_smartUsra resolveMemIdx? runKRange
  smartAdd64 smartUsra stepKInst usraShift?
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  KCfgValid KSpatial KStateMatches blk07NoRelocInRange fetch_blk07_range kzMatches_subs64_const
  kzMatches_subs64_loopDone matches_setMem matches_writeGpr matches_writeVReg sepLoad128_kspatial
  sepLoad256_kspatial sepLoad64_kspatial sepLoad64_rcAt sepStore128_kspatial sepStore256_kspatial
  sepStore64_kspatial
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval (
  add2d_eval addImm_delta_eq bit_append bsl_append dupScalar_d1_eq fromZRBits_ne31 insByte0_eval
  matches_advancePC matches_setPC matches_setPState matches_writeMemWord mov_d1_d0_eval
  movi_31_eval setPC_self shl_2d_eval umov_d1_eq usra_2d_of_shift zip1_eval zip2_eval
)

/-! ## 1. One-Step Symbolic Soundness (`sepWP_of_stepKInst`) -/

theorem sepWP_of_stepKInst {prog : Program} {tgt pc : BitVec 64} {cfg : KCfg}
    (hv : KCfgValid cfg) {env : KEnv} (hrLoop : env.rLoop < 24)
    {s : State} {st st' : KState} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {inst : Instr}
    (hm : KStateMatches env st s)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hstep : stepKInst cfg inst st = some st')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      KStateMatches env st' s' →
      SepWP prog tgt s' (KSpatial cfg env st' F) post oom) :
    SepWP prog tgt s (KSpatial cfg env st F) post oom := by
  unfold stepKInst at hstep
  split at hstep <;> try contradiction
  · rename_i rm rn rd
    simp only [Option.some.injEq] at hstep; subst hstep
    let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd ((evalKExpr env vn.2 + evalKExpr env vm.2) ++
        (evalKExpr env vn.1 + evalKExpr env vm.1))).advancePC) ?_ rfl ?_
    · rw [setPC_self hpc, Program.evalInst, add2d_eval _ _ _ _ _ rm rn rd s (hm.hvregs rn) (hm.hvregs rm)]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rm rn rd
    simp only [Option.some.injEq] at hstep; subst hstep
    let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd ((evalKExpr env vn.2 ^^^ evalKExpr env vm.2) ++
        (evalKExpr env vn.1 ^^^ evalKExpr env vm.1))).advancePC) ?_ rfl ?_
    · rw [setPC_self hpc]
      simp [Program.evalInst, execInstWithSvc, hm.hvregs rn, hm.hvregs rm, eor_append, vn, vm]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rm rn rd
    simp only [Option.some.injEq] at hstep; subst hstep
    let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd ((~~~(evalKExpr env vm.2) &&& evalKExpr env vn.2) ++
        (~~~(evalKExpr env vm.1) &&& evalKExpr env vn.1))).advancePC) ?_ rfl ?_
    · rw [setPC_self hpc]
      simp [Program.evalInst, execInstWithSvc, hm.hvregs rn, hm.hvregs rm, bic_append, vn, vm]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rm rn rd
    simp only [Option.some.injEq] at hstep; subst hstep
    let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
    let p := if rm == rn then vn else (.or64 vn.1 vm.1, .or64 vn.2 vm.2)
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd (evalKExpr env p.2 ++ evalKExpr env p.1)).advancePC) ?_ rfl ?_
    · rw [setPC_self hpc]
      by_cases hrr : rm = rn
      · subst hrr
        simp [Program.evalInst, execInstWithSvc, hm.hvregs rm, p, vn]
      · have hrrF : (rm == rn) = false := beq_false_of_ne hrr
        simp [Program.evalInst, execInstWithSvc, hm.hvregs rn, hm.hvregs rm, hrrF,
          LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp.or_append,
          evalKExpr, p, vn, vm]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd p rfl))
  · rename_i rm rn rd
    simp only [Option.some.injEq] at hstep; subst hstep
    let vd := st.vregs.get rd.toNat; let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd
        (evalKExpr env (.bsl vd.2 vn.2 vm.2) ++ evalKExpr env (.bsl vd.1 vn.1 vm.1))).advancePC)
      ?_ rfl ?_
    · rw [setPC_self hpc]
      simp [Program.evalInst, execInstWithSvc, hm.hvregs rd, hm.hvregs rn, hm.hvregs rm,
        bsl_append, evalKExpr, vd, vn, vm]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rm rn rd
    simp only [Option.some.injEq] at hstep; subst hstep
    let vd := st.vregs.get rd.toNat; let vn := st.vregs.get rn.toNat; let vm := st.vregs.get rm.toNat
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd
        (evalKExpr env (.bitOp vd.2 vn.2 vm.2) ++ evalKExpr env (.bitOp vd.1 vn.1 vm.1))).advancePC)
      ?_ rfl ?_
    · rw [setPC_self hpc]
      simp [Program.evalInst, execInstWithSvc, evalSimdThreeSameExt, evalSimdThreeSameExtSatFlags,
        applySimdSatResult, hm.hvregs rd, hm.hvregs rn, hm.hvregs rm, bit_append, evalKExpr, vd, vn, vm]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rm rn rd
    simp only [Option.some.injEq] at hstep; subst hstep
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd (evalKExpr env (st.vregs.get rm.toNat).1 ++
        evalKExpr env (st.vregs.get rn.toNat).1)).advancePC) ?_ rfl ?_
    · rw [setPC_self hpc, Program.evalInst, zip1_eval _ _ _ _ _ rm rn rd s (hm.hvregs rn) (hm.hvregs rm)]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rm rn rd
    simp only [Option.some.injEq] at hstep; subst hstep
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd (evalKExpr env (st.vregs.get rm.toNat).2 ++
        evalKExpr env (st.vregs.get rn.toNat).2)).advancePC) ?_ rfl ?_
    · rw [setPC_self hpc, Program.evalInst, zip2_eval _ _ _ _ _ rm rn rd s (hm.hvregs rn) (hm.hvregs rm)]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rn rd
    simp only [Option.some.injEq] at hstep; subst hstep
    let vn := st.vregs.get rn.toNat; let m := KExpr.const64 (1#64 <<< 63)
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd
        (evalKExpr env (.xor vn.2 m) ++ evalKExpr env (.xor vn.1 m))).advancePC) ?_ rfl ?_
    · rw [setPC_self hpc]
      have hm64 : (1#64 <<< 63 : BitVec 64) = 0x8000000000000000#64 := by decide
      simp [Program.evalInst, execInstWithSvc, fneg_2d_eval, fneg_2d_satFlags, applySimdSatResult,
        hm.hvregs rn, evalKExpr, hm64, vn, m]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rd
    simp only [Option.some.injEq] at hstep; subst hstep
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd (0#64 ++ 0#64)).advancePC) ?_ rfl ?_
    · rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rd
    simp only [Option.some.injEq] at hstep; subst hstep
    let m := KExpr.const64 ((31#64 <<< 48) ||| (31#64 <<< 32) ||| (31#64 <<< 16) ||| 31#64)
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd (evalKExpr env m ++ evalKExpr env m)).advancePC) ?_ rfl ?_
    · rw [setPC_self hpc, Program.evalInst, movi_31_eval _ rd s]; rfl
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i immh immb rn rd
    by_cases hlt : Nat.blt immh.toNat 8 = true
    · simp [hlt] at hstep
    · have hltF : Nat.blt immh.toNat 8 = false := Bool.eq_false_iff.mpr hlt
      have hge : ¬ immh.toNat < 8 := fun hc => hlt (Nat.blt_eq.mpr hc)
      simp only [hltF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      let sh := immh.toNat * 8 + immb.toNat - 64; let vn := st.vregs.get rn.toNat
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeVReg128 rd ((evalKExpr env vn.2 <<< sh) ++
          (evalKExpr env vn.1 <<< sh))).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc, Program.evalInst, shl_2d_eval _ immb hge _ _ rn rd s (hm.hvregs rn)]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i immh immb rn rd
    cases hus : usraShift? immh immb with
    | none => simp [hus] at hstep
    | some r =>
      simp only [hus, Option.some.injEq] at hstep; subst hstep
      let vd := st.vregs.get rd.toNat; let vn := st.vregs.get rn.toNat
      rcases usra_2d_of_shift hus (evalKExpr env vd.2) (evalKExpr env vd.1)
        (evalKExpr env vn.2) (evalKExpr env vn.1) with ⟨hne0, hev⟩
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeVReg128 rd
          (evalKExpr env (smartUsra vd.2 vn.2 r) ++
            evalKExpr env (smartUsra vd.1 vn.1 r))).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, hne0, hm.hvregs rd, hm.hvregs rn,
          hev, usra_2d_satFlags, applySimdSatResult, eval_smartUsra, vd, vn]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rn rd
    by_cases hrn : (rn == 31#5) = true
    · simp [hrn] at hstep
    · have hrnF : (rn == 31#5) = false := Bool.eq_false_iff.mpr hrn
      have hrnNe : rn ≠ 31#5 := fun h => hrn (beq_iff_eq.mpr h)
      simp only [hrnF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      let vd := st.vregs.get rd.toNat; let gr := st.gprs.get rn.toNat
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeVReg128 rd
          (evalKExpr env vd.2 ++ evalKExpr env (.insByte0 vd.1 gr))).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc, Program.evalInst,
          insByte0_eval _ hrnNe _ _ _ s (hm.hvregs rd) (hm.hgprs rn hrnNe)]; rfl
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rn rd
    simp only [Option.some.injEq] at hstep; subst hstep
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd (evalKExpr env (st.vregs.get rn.toNat).1 ++
        evalKExpr env (st.vregs.get rd.toNat).1)).advancePC) ?_ rfl ?_
    · rw [setPC_self hpc, Program.evalInst,
        mov_d1_d0_eval _ rn rd _ _ _ _ s (hm.hvregs rd) (hm.hvregs rn)]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rn rd
    simp only [Option.some.injEq] at hstep; subst hstep
    refine SepWP.step_pure hpc hrun hfetch
      (s' := (s.writeVReg128 rd (0#64 ++ evalKExpr env (st.vregs.get rn.toNat).2)).advancePC) ?_ rfl ?_
    · rw [setPC_self hpc]
      simp [Program.evalInst, execInstWithSvc, hm.hvregs rn, dupScalar_d1_eq]
    · exact hnext _ (by simp [State.advancePC, hpc]) hrun
        (matches_advancePC (matches_writeVReg hm rd _ rfl))
  · rename_i rn rd
    by_cases hrd : (rd == 31#5) = true
    · simp [hrd] at hstep
    · have hrdF : (rd == 31#5) = false := Bool.eq_false_iff.mpr hrd
      have hrdNe : rd ≠ 31#5 := fun h => hrd (beq_iff_eq.mpr h)
      simp only [hrdF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) (evalKExpr env (st.vregs.get rn.toNat).2)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, fromZRBits_ne31 hrdNe, State.writeReg,
          hm.hvregs rn, umov_d1_eq]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrdNe _ rfl))
  · rename_i rn rd
    by_cases hrd : (rd == 31#5) = true
    · simp [hrd] at hstep
    · have hrdF : (rd == 31#5) = false := Bool.eq_false_iff.mpr hrd
      have hrdNe : rd ≠ 31#5 := fun h => hrd (beq_iff_eq.mpr h)
      simp only [hrdF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) (evalKExpr env (st.vregs.get rn.toNat).1)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, fromZRBits_ne31 hrdNe, State.readVReg64,
          hm.hvregs rn]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrdNe _ rfl))
  · rename_i rn vt
    by_cases hrn : (rn == 31#5) = true
    · simp [hrn] at hstep
    · have hrnF : (rn == 31#5) = false := Bool.eq_false_iff.mpr hrn
      have hrnNe : rn ≠ 31#5 := fun h => hrn (beq_iff_eq.mpr h)
      simp only [hrnF, Bool.false_eq_true, ↓reduceIte] at hstep
      cases hg : st.gprs.get rn.toNat <;> simp only [hg] at hstep <;> try contradiction
      case rcLoopPtr =>
        simp only [Option.some.injEq] at hstep; subst hstep
        have hea : s.readReg64 (.gpr rn) = env.rcBase + BitVec.ofNat 64 (8 * env.rLoop) := by
          rw [hm.hgprs rn hrnNe, hg]; rfl
        exact step_simdLd1r_2d hpc hrun hfetch rfl hea (sepLoad64_rcAt hrLoop rfl) rfl
          (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _ rfl) _))
      case rcAdd off =>
        by_cases hc : (Nat.beq (off.toNat % 8) 0 && Nat.blt (off.toNat / 8) 24 &&
            off == BitVec.ofNat 64 off.toNat) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
          have hc' : Nat.beq (off.toNat % 8) 0 = true ∧ off.toNat / 8 < 24 ∧
              (off == BitVec.ofNat 64 off.toNat) = true := by
            simpa [Bool.and_eq_true, Nat.blt_eq, _root_.and_assoc] using hc
          have hea : s.readReg64 (.gpr rn) =
              env.rcBase + BitVec.ofNat 64 (8 * (off.toNat / 8)) := by
            rw [hm.hgprs rn hrnNe, hg, evalKExpr]
            congr 1
            have hdiv : 8 * (off.toNat / 8) = off.toNat := by
              have := Nat.eq_of_beq_eq_true hc'.1; omega
            rw [hdiv]
            exact beq_iff_eq.mp hc'.2.2
          exact step_simdLd1r_2d hpc hrun hfetch rfl hea (sepLoad64_rcAt hc'.2.1 rfl) rfl
            (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _ rfl) _))
        · simp only [Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte] at hstep
          contradiction
  · rename_i rd imm12 shift12
    by_cases hrd : (rd == 31#5) = true
    · simp [hrd] at hstep
    · have hrdF : (rd == 31#5) = false := Bool.eq_false_iff.mpr hrd
      have hrdNe : rd ≠ 31#5 := fun h => hrd (beq_iff_eq.mpr h)
      simp only [hrdF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      let delta := if shift12 then imm12.toNat <<< 12 else imm12.toNat
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) (env.sp + BitVec.ofNat 64 delta)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.readReg64,
          State.writeReg, hm.hsp, addImm_delta_eq, delta]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrdNe _ rfl))
  · rename_i rd rn imm12 shift12
    by_cases hc : (rd == 31#5 || rn == 31#5) = true
    · simp [hc] at hstep
    · have hcF : (rd == 31#5 || rn == 31#5) = false := Bool.eq_false_iff.mpr hc
      rw [Bool.or_eq_false_iff] at hcF
      have hrdNe : rd ≠ 31#5 := fun h => by rw [beq_iff_eq.mpr h] at hcF; cases hcF.1
      have hrnNe : rn ≠ 31#5 := fun h => by rw [beq_iff_eq.mpr h] at hcF; cases hcF.2
      simp only [hcF.1, hcF.2, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      let delta := if shift12 then imm12.toNat <<< 12 else imm12.toNat
      let g' := smartAdd64 (st.gprs.get rn.toNat) (.const64 (BitVec.ofNat 64 delta))
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) (evalKExpr env g')).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.writeReg,
          hm.hgprs rn hrnNe, addImm_delta_eq, eval_smartAdd64, evalKExpr, g', delta]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrdNe g' rfl))
  · rename_i rd rn rm
    by_cases hc : (rd == 31#5 || rn == 31#5 || rm == 31#5) = true
    · simp [hc] at hstep
    · have hcF : (rd == 31#5 || rn == 31#5 || rm == 31#5) = false := Bool.eq_false_iff.mpr hc
      simp only [Bool.or_eq_false_iff] at hcF
      have hrdNe : rd ≠ 31#5 := fun h => by rw [beq_iff_eq.mpr h] at hcF; cases hcF.1.1
      have hrnNe : rn ≠ 31#5 := fun h => by rw [beq_iff_eq.mpr h] at hcF; cases hcF.1.2
      have hrmNe : rm ≠ 31#5 := fun h => by rw [beq_iff_eq.mpr h] at hcF; cases hcF.2
      simp only [hcF.1.1, hcF.1.2, hcF.2, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq] at hstep; subst hstep
      let g' := smartAdd64 (st.gprs.get rn.toNat) (st.gprs.get rm.toNat)
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) (evalKExpr env g')).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execAddSubShift, shiftVal, shift64,
          State.readReg, State.writeReg, hm.hgprs rn hrnNe, hm.hgprs rm hrmNe, eval_smartAdd64, g']
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrdNe g' rfl))
  · rename_i rn imm12
    by_cases hrn : (rn == 31#5) = true
    · rw [hrn] at hstep; cases hstep
    · have hrnF : (rn == 31#5) = false := Bool.eq_false_iff.mpr hrn
      have hrnNe : rn ≠ 31#5 := fun h => hrn (beq_iff_eq.mpr h)
      rw [hrnF] at hstep
      cases hg : st.gprs.get rn.toNat <;> rw [hg] at hstep <;> try cases hstep
      · rename_i v
        refine SepWP.step_pure hpc hrun hfetch
          (s' := (s.setPState (subsPState64 v (imm12.zeroExtend 64))).advancePC) ?_ rfl ?_
        · rw [setPC_self hpc]
          simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.writeReg,
            hm.hgprs rn hrnNe, hg, evalKExpr]
        · exact hnext _ (by simp [State.advancePC, State.setPState, hpc]) hrun
            (matches_advancePC (matches_setPState hm (kzMatches_subs64_const env v _)))
      · by_cases himm : (imm12 == 192#12) = true
        · rw [himm] at hstep; cases hstep
          rw [beq_iff_eq.mp himm] at hfetch
          refine SepWP.step_pure hpc hrun hfetch
            (s' := (s.setPState
              (subsPState64 (BitVec.ofNat 64 (8 * env.rLoop) + 8#64) 192#64)).advancePC) ?_ rfl ?_
          · rw [setPC_self hpc]
            simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.writeReg,
              hm.hgprs rn hrnNe, hg, evalKExpr]
          · exact hnext _ (by simp [State.advancePC, State.setPState, hpc]) hrun
              (matches_advancePC (matches_setPState hm (kzMatches_subs64_loopDone env)))
        · rw [Bool.eq_false_iff.mpr himm] at hstep; cases hstep
  · rename_i rn
    by_cases hrn : (rn == 31#5) = true
    · rw [hrn] at hstep; cases hstep
    · have hrnF : (rn == 31#5) = false := Bool.eq_false_iff.mpr hrn
      have hrnNe : rn ≠ 31#5 := fun h => hrn (beq_iff_eq.mpr h)
      rw [hrnF] at hstep
      cases hg : st.gprs.get rn.toNat <;> rw [hg] at hstep <;> try cases hstep
      rename_i v
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.setPState (subsPState64 v 0#64)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        have hxzr : s.readReg64 .xzr = 0#64 := rfl
        simp [Program.evalInst, execInstWithSvc, execAddSubShift, shiftVal, shift64,
          State.readReg, hxzr, State.writeReg, hm.hgprs rn hrnNe, hg, evalKExpr]
      · exact hnext _ (by simp [State.advancePC, State.setPState, hpc]) hrun
          (matches_advancePC (matches_setPState hm (kzMatches_subs64_const env v 0#64)))
  · rename_i rd imm16
    by_cases hrd : (rd == 31#5) = true
    · simp [hrd] at hstep
    · have hrdF : (rd == 31#5) = false := Bool.eq_false_iff.mpr hrd
      have hrdNe : rd ≠ 31#5 := fun h => hrd (beq_iff_eq.mpr h)
      simp only [hrdF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) (imm16.zeroExtend 64)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execMoveWide, State.writeReg]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrdNe _ rfl))
  · rename_i rd
    by_cases hrd : (rd == 31#5) = true
    · simp [hrd] at hstep
    · have hrdF : (rd == 31#5) = false := Bool.eq_false_iff.mpr hrd
      have hrdNe : rd ≠ 31#5 := fun h => hrd (beq_iff_eq.mpr h)
      simp only [hrdF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) 0#64).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execLogicalShift, shiftVal, shift32, evalLogical,
          State.readReg, State.readReg32, State.readReg64, State.writeReg]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrdNe _ rfl))
  · rename_i rd
    by_cases hrd : (rd == 31#5) = true
    · simp [hrd] at hstep
    · have hrdF : (rd == 31#5) = false := Bool.eq_false_iff.mpr hrd
      have hrdNe : rd ≠ 31#5 := fun h => hrd (beq_iff_eq.mpr h)
      simp only [hrdF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) 0#64).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, execLogicalShift, shiftVal, shift64, evalLogical,
          State.readReg, State.readReg64, State.writeReg]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrdNe _ rfl))
  · rename_i rd rm
    by_cases hc : (rd == 31#5 || rm == 31#5) = true
    · simp [hc] at hstep
    · have hcF : (rd == 31#5 || rm == 31#5) = false := Bool.eq_false_iff.mpr hc
      rw [Bool.or_eq_false_iff] at hcF
      have hrdNe : rd ≠ 31#5 := fun h => by rw [beq_iff_eq.mpr h] at hcF; cases hcF.1
      have hrmNe : rm ≠ 31#5 := fun h => by rw [beq_iff_eq.mpr h] at hcF; cases hcF.2
      simp only [hcF.1, hcF.2, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeReg64 (.gpr rd) (evalKExpr env (st.gprs.get rm.toNat))).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        have hxzr : s.readReg64 .xzr = 0#64 := rfl
        simp [Program.evalInst, execInstWithSvc, execLogicalShift, shiftVal, shift64, evalLogical,
          State.readReg, hxzr, State.writeReg, hm.hgprs rm hrmNe]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          (matches_advancePC (matches_writeGpr hm hrdNe _ rfl))
  · rename_i vt addr
    cases hr : resolveMemIdx? cfg st addr 2 with
    | none => simp [hr] at hstep
    | some p =>
      rcases p with ⟨inB, idx⟩
      simp only [hr, Option.some.injEq] at hstep; subst hstep
      rcases sepLoad128_kspatial hv hm hr F with ⟨ea, hsp, haddr, hld⟩
      exact step_ldrQ128 hpc hrun hfetch hsp haddr hld rfl
        (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _ rfl) _))
  · rename_i vt1 vt2 addr
    cases hr : resolveMemIdx? cfg st addr 4 with
    | none => simp [hr] at hstep
    | some p =>
      rcases p with ⟨inB, idx⟩
      simp only [hr, Option.some.injEq] at hstep; subst hstep
      rcases sepLoad256_kspatial hv hm hr F with ⟨ea, hsp, haddr, hld1, hld2⟩
      exact step_ldpQ128 hpc hrun hfetch hsp haddr rfl hld1 hld2 rfl
        (hnext _ rfl hrun (matches_setPC (matches_writeVReg (matches_writeVReg hm vt1 _ rfl) vt2 _ rfl) _))
  · rename_i vt addr
    cases hr : resolveMemIdx? cfg st addr 2 with
    | none => simp [hr] at hstep
    | some p =>
      rcases p with ⟨inB, idx⟩
      simp only [hr, Option.some.injEq] at hstep; subst hstep
      let vp := st.vregs.get vt.toNat
      rcases sepStore128_kspatial hv hm hr vp.1 vp.2 F with ⟨ea, hsp, haddr, hst128⟩
      exact step_strQ128 hpc hrun hfetch hsp haddr (hm.hvregs vt) hst128 rfl
        (fun m' => hnext _ rfl hrun (matches_writeMemWord
          (matches_writeMemWord (matches_setMem (matches_setPC hm _) m') inB idx vp.1) inB (idx + 1) vp.2))
  · rename_i vt1 vt2 addr
    cases hr : resolveMemIdx? cfg st addr 4 with
    | none => simp [hr] at hstep
    | some p =>
      rcases p with ⟨inB, idx⟩
      simp only [hr, Option.some.injEq] at hstep; subst hstep
      let v1 := st.vregs.get vt1.toNat; let v2 := st.vregs.get vt2.toNat
      rcases sepStore256_kspatial hv hm hr v1.1 v1.2 v2.1 v2.2 F with ⟨ea, hsp, haddr, hst1, hst2⟩
      exact step_stpQ128 hpc hrun hfetch hsp haddr rfl (hm.hvregs vt1) (hm.hvregs vt2)
        hst1 hst2 rfl (fun m' => hnext _ rfl hrun
          (matches_writeMemWord (matches_writeMemWord (matches_writeMemWord (matches_writeMemWord
            (matches_setMem (matches_setPC hm _) m') inB idx v1.1) inB (idx + 1) v1.2)
            inB (idx + 2) v2.1) inB (idx + 3) v2.2))
  · rename_i vt addr
    cases hr : resolveMemIdx? cfg st addr 1 with
    | none => simp [hr] at hstep
    | some p =>
      rcases p with ⟨inB, idx⟩
      simp only [hr, Option.some.injEq] at hstep; subst hstep
      let e := (st.vregs.get vt.toNat).1
      rcases sepStore64_kspatial hv hm hr e F with ⟨ea, hsp, haddr, hst64⟩
      have hv0 : (s.readVReg128 vt).extractLsb' 0 64 = evalKExpr env e := by
        rw [hm.hvregs vt, extractLsb_lo_append]
      exact SepWP.step_strSimd64 hpc hrun hfetch hsp haddr hv0 hst64 rfl
        (fun m' => hnext _ rfl hrun (matches_writeMemWord (matches_setMem (matches_setPC hm _) m') inB idx e))
  · rename_i rt addr
    by_cases hrt : (rt == 31#5) = true
    · simp [hrt] at hstep
    · have hrtF : (rt == 31#5) = false := Bool.eq_false_iff.mpr hrt
      have hrtNe : rt ≠ 31#5 := fun h => hrt (beq_iff_eq.mpr h)
      simp only [hrtF, Bool.false_eq_true, ↓reduceIte] at hstep
      cases hr : resolveMemIdx? cfg st addr 1 with
      | none => simp [hr] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩
        simp only [hr, Option.some.injEq] at hstep; subst hstep
        rcases sepLoad64_kspatial hv hm hr F with ⟨ea, hsp, haddr, hld64⟩
        exact SepWP.step_ldr64 hpc hrun hfetch hsp haddr hld64 rfl
          (hnext _ rfl hrun (matches_setPC (matches_writeGpr hm hrtNe _ rfl) _))
  · rename_i addr
    cases hr : resolveMemIdx? cfg st addr 1 with
    | none => simp [hr] at hstep
    | some p =>
      rcases p with ⟨inB, idx⟩
      simp only [hr, Option.some.injEq] at hstep; subst hstep
      rcases sepStore64_kspatial hv hm hr (.const64 0#64) F with ⟨ea, hsp, haddr, hst64⟩
      exact SepWP.step_str64 hpc hrun hfetch hsp haddr rfl hst64 rfl
        (fun m' => hnext _ rfl hrun
          (matches_writeMemWord (matches_setMem (matches_setPC hm _) m') inB idx (.const64 0#64)))
  · rename_i rt addr
    by_cases hrt : (rt == 31#5) = true
    · simp [hrt] at hstep
    · have hrtF : (rt == 31#5) = false := Bool.eq_false_iff.mpr hrt
      have hrtNe : rt ≠ 31#5 := fun h => hrt (beq_iff_eq.mpr h)
      simp only [hrtF, Bool.false_eq_true, ↓reduceIte] at hstep
      cases hr : resolveMemIdx? cfg st addr 1 with
      | none => simp [hr] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩
        simp only [hr, Option.some.injEq] at hstep; subst hstep
        let e := st.gprs.get rt.toNat
        rcases sepStore64_kspatial hv hm hr e F with ⟨ea, hsp, haddr, hst64⟩
        exact SepWP.step_str64 hpc hrun hfetch hsp haddr (hm.hgprs rt hrtNe) hst64 rfl
          (fun m' => hnext _ rfl hrun (matches_writeMemWord (matches_setMem (matches_setPC hm _) m') inB idx e))

/-! ## 2. Multi-Instruction Range Soundness (`sepWP_of_runKRange`) -/

theorem sepWP_of_runKRange [MlKemPlacement] {b tgt : BitVec 64} {cfg : KCfg}
    (hv : KCfgValid cfg) {env : KEnv} (hrLoop : env.rLoop < 24)
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {wLo wHi : Nat} (count w : Nat) {st stEnd : KState} {s : State}
    (hnr : blk07NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 10252)
    (hlo : wLo ≤ w) (hhi : w + count ≤ wHi)
    (hrun_sym : runKRange cfg w count st = some stEnd)
    (hm : KStateMatches env st s)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hnext : ∀ sf : State, sf.pc = b + BitVec.ofNat 64 (4 * (w + count)) →
      sf.status = .Running → KStateMatches env stEnd sf →
      SepWP (blkPC07.rebase b (fun _ => none)) tgt sf (KSpatial cfg env stEnd F) post oom) :
    SepWP (blkPC07.rebase b (fun _ => none)) tgt s (KSpatial cfg env st F) post oom := by
  induction count generalizing w st s with
  | zero =>
    simp only [runKRange, Option.some.injEq] at hrun_sym; subst hrun_sym
    exact hnext s (by simpa using hpc) hrun hm
  | succ n ih =>
    unfold runKRange at hrun_sym
    cases hfw : fetchWordTree07 w with
    | none => simp [hfw] at hrun_sym
    | some inst =>
      simp only [hfw] at hrun_sym
      cases hst : stepKInst cfg inst st with
      | none => simp [hst] at hrun_sym
      | some st1 =>
        simp only [hst] at hrun_sym
        have hfetch := fetch_blk07_range (b := b) hnr hmax hlo (by omega) hfw
        refine sepWP_of_stepKInst hv hrLoop hm hpc hrun hfetch hst ?_
        intro s' hpc' hrun' hm'
        have hpc_eq : b + BitVec.ofNat 64 (4 * w) + 4#64 = b + BitVec.ofNat 64 (4 * (w + 1)) := by
          bv_omega
        rw [hpc_eq] at hpc'
        have hend_eq : 4 * (w + (n + 1)) = 4 * (w + 1 + n) := by omega
        exact ih (w + 1) (by omega) (by omega) hrun_sym hm' hpc' hrun'
          (fun sf h1 h2 h3 => hnext sf (by rwa [hend_eq]) h2 h3)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSym

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

/-!
# `kyber_encapsulate` (`B07`) — Pure Instruction & Bitwise Helpers for `KeccakSym` (`KeccakSymEval`)

State-preservation helpers and per-instruction `execInstWithSvc` / `BitVec 128` reductions
supporting `KeccakSym.sepWP_of_stepKInst`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval

open Arm64 ProofLib BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp (
  add_2d_lanes eor_append execInst_zip1_2d execInst_zip2_2d extractLsb_hi_append
  extractLsb_lo_append shl_2d_lanes
  usra_2d_r2 usra_2d_r3 usra_2d_r8 usra_2d_r9 usra_2d_r19 usra_2d_r20 usra_2d_r21 usra_2d_r23
  usra_2d_r25 usra_2d_r28 usra_2d_r36 usra_2d_r37 usra_2d_r39 usra_2d_r43 usra_2d_r44
  usra_2d_r46 usra_2d_r49 usra_2d_r50 usra_2d_r54 usra_2d_r56 usra_2d_r58 usra_2d_r61
  usra_2d_r62 usra_2d_r63
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  KEnv KExpr KState KZFlag evalKExpr usraShift? writeMemWord
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  KStateMatches KZMatches
)

theorem setPC_self {s : State} {pc : BitVec 64} (hpc : s.pc = pc) : s.setPC pc = s := by
  cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm

theorem matches_setPC {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (pc : BitVec 64) :
    KStateMatches env st (s.setPC pc) :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hzflag⟩

theorem matches_advancePC {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) :
    KStateMatches env st s.advancePC :=
  matches_setPC hm (s.pc + 4#64)

theorem matches_setPState {env : KEnv} {st : KState} {s : State}
    {zf : Option KZFlag} {ps : PState}
    (hm : KStateMatches env st s) (hz : KZMatches env zf ps) :
    KStateMatches env { st with zFlag := zf } (s.setPState ps) :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hz⟩

theorem matches_writeMemWord {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (inB : Bool) (idx : Nat) (e : KExpr) :
    KStateMatches env (writeMemWord st inB idx e) s := by
  cases inB <;> exact ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hzflag⟩

theorem writeReg64_xzr (s : State) (v : BitVec 64) : s.writeReg64 .xzr v = s := by
  cases s; rfl

theorem fromZRBits_ne31 {r : BitVec 5} (hr : r ≠ 31#5) : Reg.fromZRBits r = .gpr r := by
  revert hr; revert r; decide

theorem addImm_delta_eq (imm12 : BitVec 12) (shift12 : Bool) :
    (if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64) =
      BitVec.ofNat 64 (if shift12 then imm12.toNat <<< 12 else imm12.toNat) := by
  revert imm12 shift12; decide

theorem movz_w32_eq (imm16 : BitVec 16) :
    (((imm16.zeroExtend 64 : BitVec 64).truncate 32).zeroExtend 64 : BitVec 64) =
      imm16.zeroExtend 64 := by
  bv_bits

theorem bsl_append (vd1 vd0 vn1 vn0 vm1 vm0 : BitVec 64) :
    (((vn1 ++ vn0) ^^^ (vm1 ++ vm0)) &&& (vd1 ++ vd0)) ^^^ (vm1 ++ vm0) =
      ((((vn1 ^^^ vm1) &&& vd1) ^^^ vm1) ++ (((vn0 ^^^ vm0) &&& vd0) ^^^ vm0)) := by
  rw [eor_append, BitVec.and_append, eor_append]

theorem bit_append (vd1 vd0 vn1 vn0 vm1 vm0 : BitVec 64) :
    (vd1 ++ vd0) ^^^ (((vd1 ++ vd0) ^^^ (vn1 ++ vn0)) &&& (vm1 ++ vm0)) =
      ((((vn1 ^^^ vd1) &&& vm1) ^^^ vd1) ++ (((vn0 ^^^ vd0) &&& vm0) ^^^ vd0)) := by
  rw [eor_append, BitVec.and_append, eor_append,
    BitVec.xor_comm vd1 vn1, BitVec.xor_comm vd1 _,
    BitVec.xor_comm vd0 vn0, BitVec.xor_comm vd0 _]

theorem add2d_eval (svc : State → State) (vn1 vn0 vm1 vm0 : BitVec 64) (rm rn rd : BitVec 5)
    (s : State) (hn : s.readVReg128 rn = vn1 ++ vn0) (hm : s.readVReg128 rm = vm1 ++ vm0) :
    execInstWithSvc svc (.simdThreeSame true false 0x3#2 rm 0x10#5 rn rd) s =
      (s.writeVReg128 rd ((vn1 + vm1) ++ (vn0 + vm0))).advancePC := by
  have hex : execInstWithSvc svc (.simdThreeSame true false 0x3#2 rm 0x10#5 rn rd) s =
      (s.writeVReg128 rd (zipSimdLanes true 64 (vn1 ++ vn0) (vm1 ++ vm0) (· + ·))).advancePC := by
    simp [execInstWithSvc, hn, hm]
  rw [hex]
  simp only [ProofLib.zipSimdLanes_true_64, ProofLib.zipLanes, ProofLib.laneMask_64]
  rw [add_2d_lanes, extractLsb_hi_append, extractLsb_hi_append, extractLsb_lo_append,
    extractLsb_lo_append]

theorem zip1_eval (svc : State → State) (vn1 vn0 vm1 vm0 : BitVec 64) (rm rn rd : BitVec 5)
    (s : State) (hn : s.readVReg128 rn = vn1 ++ vn0) (hm : s.readVReg128 rm = vm1 ++ vm0) :
    execInstWithSvc svc (.simdPermute true 0x3#2 rm 0x3#3 rn rd) s =
      (s.writeVReg128 rd (vm0 ++ vn0)).advancePC := by
  change execInst (.simdPermute true 0x3#2 rm 0x3#3 rn rd) s = _
  rw [execInst_zip1_2d, hn, hm, extractLsb_lo_append, extractLsb_lo_append]

theorem zip2_eval (svc : State → State) (vn1 vn0 vm1 vm0 : BitVec 64) (rm rn rd : BitVec 5)
    (s : State) (hn : s.readVReg128 rn = vn1 ++ vn0) (hm : s.readVReg128 rm = vm1 ++ vm0) :
    execInstWithSvc svc (.simdPermute true 0x3#2 rm 0x7#3 rn rd) s =
      (s.writeVReg128 rd (vm1 ++ vn1)).advancePC := by
  change execInst (.simdPermute true 0x3#2 rm 0x7#3 rn rd) s = _
  rw [execInst_zip2_2d, hn, hm, extractLsb_hi_append, extractLsb_hi_append]

private theorem immhb_toNat_eq (immh : BitVec 4) (immb : BitVec 3) :
    (immh ++ immb).toNat = immh.toNat * 8 + immb.toNat := by
  revert immh immb; decide

theorem shl_2d_eval (svc : State → State) {immh : BitVec 4} (immb : BitVec 3)
    (hge : ¬ immh.toNat < 8) (vn1 vn0 : BitVec 64) (rn rd : BitVec 5) (s : State)
    (hn : s.readVReg128 rn = vn1 ++ vn0) :
    let sh := immh.toNat * 8 + immb.toNat - 64
    execInstWithSvc svc (.simdImmShift true false immh immb 0x0a#5 rn rd) s =
      (s.writeVReg128 rd ((vn1 <<< sh) ++ (vn0 <<< sh))).advancePC := by
  intro sh
  have hne0 : (immh == 0#4) = false := by
    apply beq_false_of_ne; intro h; subst h; exact hge (by decide)
  have h64 : 64 ≤ immh.toNat * 8 + immb.toNat := by omega
  have hex : execInstWithSvc svc (.simdImmShift true false immh immb 0x0a#5 rn rd) s =
      (s.writeVReg128 rd (mapSimdLanes true 64 (vn1 ++ vn0) (fun lane => lane <<< sh))).advancePC := by
    simp [execInstWithSvc, hne0, hn, immhb_toNat_eq, h64, sh]
  rw [hex]
  simp only [ProofLib.mapSimdLanes_true_64, ProofLib.mapLanes, ProofLib.laneMask_64]
  rw [shl_2d_lanes, extractLsb_hi_append, extractLsb_lo_append]

theorem movi_31_eval (svc : State → State) (rd : BitVec 5) (s : State) :
    let c := (31#64 <<< 48) ||| (31#64 <<< 32) ||| (31#64 <<< 16) ||| 31#64
    execInstWithSvc svc (.simdImmShift true false 0x0#4 0x0#3 0x10#5 0x1f#5 rd) s =
      (s.writeVReg128 rd (c ++ c)).advancePC :=
  rfl

theorem usra_2d_of_shift {immh : BitVec 4} {immb : BitVec 3} {r : Nat}
    (hs : usraShift? immh immb = some r) (vd1 vd0 vn1 vn0 : BitVec 64) :
    (immh == 0#4) = false ∧
      evalSimdImmShiftNonZeroExt true true immh immb 0x02#5 (vd1 ++ vd0) (vn1 ++ vn0) =
        Except.ok ((vd1 + (vn1 >>> r)) ++ (vd0 + (vn0 >>> r))) := by
  unfold usraShift? at hs
  split at hs <;> cases hs
  all_goals
    refine ⟨by decide, ?_⟩
    first
    | rw [usra_2d_r63]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r62]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r61]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r58]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r56]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r54]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r50]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r49]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r46]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r44]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r43]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r39]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r37]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r36]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r28]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r25]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r23]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r21]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r20]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r19]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r9]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r8]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r3]; simp only [extractLsb_hi_append, extractLsb_lo_append]
    | rw [usra_2d_r2]; simp only [extractLsb_hi_append, extractLsb_lo_append]

private theorem zext128_eq_append64 (gr : BitVec 64) :
    (gr.zeroExtend 128 : BitVec 128) = 0#64 ++ gr := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_zero, hi, decide_true, Bool.true_and]
  split
  · rfl
  · rename_i h64
    exact BitVec.getLsbD_of_ge gr (i := i) (Nat.le_of_not_lt h64)

private theorem and_not_zero64 (x : BitVec 64) : x &&& ~~~0#64 = x := by
  bv_bits

theorem insByte0_eval (svc : State → State) {rn rd : BitVec 5} (hrn : rn ≠ 31#5)
    (vd1 vd0 gr : BitVec 64) (s : State)
    (hd : s.readVReg128 rd = vd1 ++ vd0) (hn : s.readReg64 (.gpr rn) = gr) :
    execInstWithSvc svc (.simdInsDup true false 0x01#5 0x3#4 rn rd) s =
      (s.writeVReg128 rd (vd1 ++ ((vd0 &&& ~~~255#64) ||| (gr &&& 255#64)))).advancePC := by
  have hm1 : (~~~(((1#128 <<< 8) - 1#128) <<< 0) : BitVec 128) = ~~~0#64 ++ ~~~255#64 := by decide
  have hm2 : ((1#128 <<< 8) - 1#128 : BitVec 128) = 0#64 ++ 255#64 := by decide
  have hex : execInstWithSvc svc (.simdInsDup true false 0x01#5 0x3#4 rn rd) s =
      (s.writeVReg128 rd (((vd1 ++ vd0) &&& ~~~(((1#128 <<< 8) - 1#128) <<< 0)) |||
        (gr.zeroExtend 128 &&& ((1#128 <<< 8) - 1#128)))).advancePC := by
    simp [execInstWithSvc, fromZRBits_ne31 hrn, hd, hn]
  rw [hex, hm1, hm2, zext128_eq_append64, BitVec.and_append, BitVec.and_append, BitVec.or_append]
  simp only [and_not_zero64, BitVec.and_zero, BitVec.or_zero]

private theorem shiftLeft64_lo_append (u : BitVec 64) :
    ((0#64 ++ u : BitVec 128) <<< 64) = u ++ 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_zero,
    hi, decide_true, Bool.true_and]
  by_cases h64 : i < 64
  · simp [h64]
  · have hlt : i - 64 < 64 := by omega
    simp [h64, hlt]

theorem mov_d1_d0_eval (svc : State → State) (rn rd : BitVec 5) (vd1 vd0 vn1 vn0 : BitVec 64)
    (s : State) (hd : s.readVReg128 rd = vd1 ++ vd0) (hn : s.readVReg128 rn = vn1 ++ vn0) :
    execInstWithSvc svc (.simdInsDup true true 0x18#5 0x0#4 rn rd) s =
      (s.writeVReg128 rd (vn0 ++ vd0)).advancePC := by
  have hm : ((1#128 <<< 64) - 1#128 : BitVec 128) = 0#64 ++ ~~~0#64 := by decide
  have hmnot : (~~~(((1#128 <<< 64) - 1#128) <<< 64) : BitVec 128) = 0#64 ++ ~~~0#64 := by decide
  have hex : execInstWithSvc svc (.simdInsDup true true 0x18#5 0x0#4 rn rd) s =
      (s.writeVReg128 rd (((vd1 ++ vd0) &&& ~~~(((1#128 <<< 64) - 1#128) <<< 64)) |||
        ((((vn1 ++ vn0) &&& ((1#128 <<< 64) - 1#128))) <<< 64))).advancePC := by
    simp [execInstWithSvc, getSimdLane, hd, hn]
  rw [hex, hmnot, hm, BitVec.and_append, BitVec.and_append]
  simp only [BitVec.and_zero, and_not_zero64]
  rw [shiftLeft64_lo_append, BitVec.or_append, BitVec.zero_or, BitVec.or_zero]

theorem dupScalar_d1_eq (vn1 vn0 : BitVec 64) :
    evalSimdDupScalar 0x18#5 (vn1 ++ vn0) = 0#64 ++ vn1 := by
  simp only [evalSimdDupScalar, getSimdLane]; bv_bits

theorem umov_d1_eq (vn1 vn0 : BitVec 64) :
    (getSimdLane (vn1 ++ vn0) 64 1).truncate 64 = vn1 := by
  simp only [getSimdLane]; bv_bits

theorem truncate64_append (hi lo : BitVec 64) :
    (hi ++ lo).truncate 64 = lo := by
  bv_bits

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval

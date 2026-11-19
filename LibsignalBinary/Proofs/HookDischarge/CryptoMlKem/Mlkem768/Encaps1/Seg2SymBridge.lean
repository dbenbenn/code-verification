/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

/-!
# `encapsulate1` (`B03`) — `Seg2` Symbolic State, SIMD Lane Rules, & Memory Routing (`Seg2SymBridge`)

Connects `KState` / `KCfg` (`Seg2SymDefs`) and `TreeMem` (`Seg2Mem`) to concrete ARM64 `State` and
`SepProp`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
  (keccakRcAt mlkemData01Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (SepLoad128 SepStore128 Vec128At)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (Seg2ConstsLo)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
  (BTree KCfg KEnv KExpr KPFlag KState UsraRot evalKExpr readMemWord resolveByteOff?
   resolveMemIdx? usraRot? writeMemWord)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem
  (TreeMem sepLoad64_treeMem sepStore64_treeMem sepLoad128_treeMem sepStore128_treeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
  (add_2d_lanes and_append bic_append dup_2d_lane0 dup_2d_lane1 eor_append extractLsb_hi_append
   extractLsb_lo_append fneg_2d_eval fneg_2d_satFlags mov_d1_d0 movi_8h_31_eq or_append
   shl_2d_lanes usra_2d_r2 usra_2d_r3 usra_2d_r8 usra_2d_r9 usra_2d_r19 usra_2d_r20 usra_2d_r21
   usra_2d_r23 usra_2d_r25 usra_2d_r28 usra_2d_r36 usra_2d_r37 usra_2d_r39 usra_2d_r43
   usra_2d_r44 usra_2d_r46 usra_2d_r49 usra_2d_r50 usra_2d_r54 usra_2d_r56 usra_2d_r58
   usra_2d_r61 usra_2d_r62 usra_2d_r63 usra_2d_satFlags)

/-! ## 1. Concrete State & Spatial Matching (`KCfgWf`, `KPFlagMatches`, `KStateMatches`, `KSpatial`) -/

@[expose] def KCfgWf (cfg : KCfg) : Prop :=
  cfg.offA % 8 = 0 ∧ cfg.lenA ≤ 512 ∧ cfg.offB % 8 = 0 ∧ cfg.lenB ≤ 512

instance (cfg : KCfg) : Decidable (KCfgWf cfg) := by
  unfold KCfgWf; infer_instance

@[expose] def evalMemTree (env : KEnv) (t : BTree KExpr 9) : BTree (BitVec 64) 9 :=
  t.map (evalKExpr env)

@[expose] def KPFlagMatches (env : KEnv) : Option KPFlag → PState → Prop
  | none, _ => True
  | some (.subs64 lhs rhs), ps => ps = subsPState64 (evalKExpr env lhs) rhs
  | some .loopDone, ps => ps = subsPState64 (BitVec.ofNat 64 (8 * env.rLoop) + 8#64) 192#64

structure KStateMatches (env : KEnv) (st : KState) (s : State) : Prop where
  hsp    : s.sp = env.sp
  hsp_al : s.spAligned = true
  hvregs : ∀ r : BitVec 5,
    s.readVReg128 r =
      evalKExpr env (st.vregs.get r.toNat).2 ++ evalKExpr env (st.vregs.get r.toNat).1
  hgprs  : ∀ r : BitVec 5, r ≠ 31#5 →
    s.readReg64 (.gpr r) = evalKExpr env (st.gprs.get r.toNat)
  hpflag : KPFlagMatches env st.pstateFlag s.pstate

@[expose] def KConstsLoOpt (sp : BitVec 64) : Bool → SepProp
  | false => emp
  | true => Seg2ConstsLo sp

@[expose] def KSpatial (cfg : KCfg) (env : KEnv) (st : KState) (F : SepProp) : SepProp :=
  (env.rcBase ↦ᵣ mlkemData01Bytes) ∗
    (KConstsLoOpt env.sp cfg.hasConstsLo ∗
      (TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (evalMemTree env st.memA) ∗
        (TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB (evalMemTree env st.memB) ∗ F)))

theorem setPC_self {s : State} {pc : BitVec 64} (hpc : s.pc = pc) :
    s.setPC pc = s := by
  cases s; cases hpc; rfl

theorem ne31_of_beq_false {r : BitVec 5} (hr : (r == 31#5) = false) :
    r ≠ 31#5 := by
  intro heq; subst heq; simp at hr

theorem fromZRBits_of_beq_false {r : BitVec 5} (hr : (r == 31#5) = false) :
    Reg.fromZRBits r = .gpr r := by
  simp [Reg.fromZRBits, ne31_of_beq_false hr]

theorem matches_writeVReg {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (rd : BitVec 5) (p : KExpr × KExpr)
    {val : BitVec 128} (hval : val = evalKExpr env p.2 ++ evalKExpr env p.1) :
    KStateMatches env { st with vregs := st.vregs.set rd.toNat p }
      (s.writeVReg128 rd val) := by
  refine ⟨hm.hsp, hm.hsp_al, ?_, hm.hgprs, hm.hpflag⟩
  intro r
  rw [BTree.get_set st.vregs rd.toNat p rd.isLt r.toNat r.isLt]
  by_cases heq : r = rd
  · subst heq; simp [State.readVReg128, State.writeVReg128, hval]
  · have hne : r.toNat ≠ rd.toNat := fun h => heq (BitVec.eq_of_toNat_eq h)
    simp only [hne, ↓reduceIte]
    simpa [State.readVReg128, State.writeVReg128, heq] using hm.hvregs r

theorem matches_writeGpr {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {rd : BitVec 5} (hrd : rd ≠ 31#5)
    (e : KExpr) {val : BitVec 64} (hval : val = evalKExpr env e) :
    KStateMatches env { st with gprs := st.gprs.set rd.toNat e }
      (s.writeReg64 (.gpr rd) val) := by
  refine ⟨by simp [State.writeReg64, hm.hsp],
    by simpa [State.spAligned, State.writeReg64] using hm.hsp_al,
    hm.hvregs, ?_, hm.hpflag⟩
  intro r hr
  rw [BTree.get_set st.gprs rd.toNat e rd.isLt r.toNat r.isLt]
  have hrdF : (rd == 31#5) = false := beq_false_of_ne hrd
  have hrF : (r == 31#5) = false := beq_false_of_ne hr
  by_cases heq : r = rd
  · subst heq; simp [State.readReg64, State.writeReg64, hrdF, RegFile.read, RegFile.write, hval]
  · have hne : r.toNat ≠ rd.toNat := fun h => heq (BitVec.eq_of_toNat_eq h)
    simp only [hne, ↓reduceIte]
    simpa [State.readReg64, State.writeReg64, hrdF, hrF, RegFile.read, RegFile.write, heq]
      using hm.hgprs r hr

theorem matches_setPFlag {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (fl : Option KPFlag) {ps : PState}
    (hfl : KPFlagMatches env fl ps) :
    KStateMatches env { st with pstateFlag := fl } (s.setPState ps) :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hfl⟩

theorem matches_orFpsr {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (fl : BitVec 32) :
    KStateMatches env st (s.orFpsr fl) :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpflag⟩

theorem matches_setPC {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (pc' : BitVec 64) :
    KStateMatches env st (s.setPC pc') :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpflag⟩

theorem matches_advancePC {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) :
    KStateMatches env st s.advancePC :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpflag⟩

theorem matches_setMem {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (m' : Memory) :
    KStateMatches env st (s.setMem m') :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs,
   fun r hr => by simpa [State.setMem, State.readReg64] using hm.hgprs r hr,
   hm.hpflag⟩

theorem matches_writeMemWord {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (inB : Bool) (idx : Nat) (val : KExpr) :
    KStateMatches env (writeMemWord st inB idx val) s := by
  unfold writeMemWord
  cases inB <;> exact ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpflag⟩

/-! ## 2. Pure 2-Lane NEON / GPR Evaluation Helpers for `stepKInst` -/

theorem bsl_append (a1 a0 b1 b0 m1 m0 : BitVec 64) :
    (((a1 ++ a0) ^^^ (b1 ++ b0)) &&& (m1 ++ m0)) ^^^ (b1 ++ b0) =
      (((a1 ^^^ b1) &&& m1) ^^^ b1) ++ (((a0 ^^^ b0) &&& m0) ^^^ b0) := by
  rw [eor_append, and_append, eor_append]

theorem insByte0_append (d1 d0 src : BitVec 64) :
    let mask : BitVec 128 := (1#128 <<< 8) - 1#128
    let elem : BitVec 128 := (src.zeroExtend 128) &&& mask
    (((d1 ++ d0) &&& ~~~(mask <<< 0)) ||| (elem <<< 0)) =
      d1 ++ ((d0 &&& 0xffffffffffffff00#64) ||| (src &&& 0xff#64)) := by
  dsimp only
  bv_bits

theorem dupScalar_d1_append (n1 n0 : BitVec 64) :
    evalSimdDupScalar 0x18#5 (n1 ++ n0) = (0#64 : BitVec 64) ++ n1 := by
  unfold evalSimdDupScalar getSimdLane
  bv_bits

theorem umov_d1_append (n1 n0 : BitVec 64) :
    (getSimdLane (n1 ++ n0) 64 1).truncate 64 = n1 := by
  unfold getSimdLane
  bv_bits

private theorem usra_case {immh : BitVec 4} {immb : BitVec 3} {rot : UsraRot}
    {rest : Option UsraRot} (c : UsraRot) (r : Nat) (h0 : BitVec 4) (b0 : BitVec 3) (k : BitVec 7)
    (vd1 vd0 vn1 vn0 : BitVec 64)
    (hcr : c.ushrAmt = r) (hkb : h0 ++ b0 = k) (hnz : h0 ≠ 0#4)
    (hev : evalSimdImmShiftNonZeroExt true true h0 b0 0x02#5 (vd1 ++ vd0) (vn1 ++ vn0) =
      Except.ok (((vd1 ++ vd0).extractLsb' 64 64 + ((vn1 ++ vn0).extractLsb' 64 64 >>> r)) ++
        ((vd1 ++ vd0).extractLsb' 0 64 + ((vn1 ++ vn0).extractLsb' 0 64 >>> r))))
    (h : (if immh ++ immb == k then some c else rest) = some rot)
    (hrest : rest = some rot → immh ≠ 0#4 ∧
      evalSimdImmShiftNonZeroExt true true immh immb 0x02#5 (vd1 ++ vd0) (vn1 ++ vn0) =
        Except.ok ((vd1 + (vn1 >>> rot.ushrAmt)) ++ (vd0 + (vn0 >>> rot.ushrAmt)))) :
    immh ≠ 0#4 ∧
    evalSimdImmShiftNonZeroExt true true immh immb 0x02#5 (vd1 ++ vd0) (vn1 ++ vn0) =
      Except.ok ((vd1 + (vn1 >>> rot.ushrAmt)) ++ (vd0 + (vn0 >>> rot.ushrAmt))) := by
  by_cases hk : (immh ++ immb == k) = true
  · simp only [hk, ↓reduceIte] at h
    have hrot : rot = c := (Option.some.inj h).symm
    have hab : immh ++ immb = h0 ++ b0 := (beq_iff_eq.mp hk).trans hkb.symm
    have hh : immh = h0 := by
      rw [← show (immh ++ immb).extractLsb' 3 4 = immh by bv_bits, hab]; bv_bits
    have hb : immb = b0 := by
      rw [← show (immh ++ immb).extractLsb' 0 3 = immb by bv_bits, hab]; bv_bits
    rw [hh, hb, hrot, hcr]
    refine ⟨hnz, ?_⟩
    simpa only [extractLsb_hi_append, extractLsb_lo_append] using hev
  · simp only [hk] at h
    exact hrest h

theorem usra_eval_of_usraRot? {immh : BitVec 4} {immb : BitVec 3} {rot : UsraRot}
    (h : usraRot? immh immb = some rot) (vd1 vd0 vn1 vn0 : BitVec 64) :
    immh ≠ 0#4 ∧
    evalSimdImmShiftNonZeroExt true true immh immb 0x02#5 (vd1 ++ vd0) (vn1 ++ vn0) =
      Except.ok ((vd1 + (vn1 >>> rot.ushrAmt)) ++ (vd0 + (vn0 >>> rot.ushrAmt))) := by
  unfold usraRot? at h
  dsimp only at h
  refine usra_case .r1 63 8#4 1#3 65#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r63 _ _) h fun h => ?_
  refine usra_case .r2 62 8#4 2#3 66#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r62 _ _) h fun h => ?_
  refine usra_case .r3 61 8#4 3#3 67#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r61 _ _) h fun h => ?_
  refine usra_case .r6 58 8#4 6#3 70#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r58 _ _) h fun h => ?_
  refine usra_case .r8 56 9#4 0#3 72#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r56 _ _) h fun h => ?_
  refine usra_case .r10 54 9#4 2#3 74#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r54 _ _) h fun h => ?_
  refine usra_case .r14 50 9#4 6#3 78#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r50 _ _) h fun h => ?_
  refine usra_case .r15 49 9#4 7#3 79#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r49 _ _) h fun h => ?_
  refine usra_case .r18 46 10#4 2#3 82#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r46 _ _) h fun h => ?_
  refine usra_case .r20 44 10#4 4#3 84#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r44 _ _) h fun h => ?_
  refine usra_case .r21 43 10#4 5#3 85#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r43 _ _) h fun h => ?_
  refine usra_case .r25 39 11#4 1#3 89#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r39 _ _) h fun h => ?_
  refine usra_case .r27 37 11#4 3#3 91#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r37 _ _) h fun h => ?_
  refine usra_case .r28 36 11#4 4#3 92#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r36 _ _) h fun h => ?_
  refine usra_case .r36 28 12#4 4#3 100#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r28 _ _) h fun h => ?_
  refine usra_case .r39 25 12#4 7#3 103#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r25 _ _) h fun h => ?_
  refine usra_case .r41 23 13#4 1#3 105#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r23 _ _) h fun h => ?_
  refine usra_case .r43 21 13#4 3#3 107#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r21 _ _) h fun h => ?_
  refine usra_case .r44 20 13#4 4#3 108#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r20 _ _) h fun h => ?_
  refine usra_case .r45 19 13#4 5#3 109#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r19 _ _) h fun h => ?_
  refine usra_case .r55 9 14#4 7#3 119#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r9 _ _) h fun h => ?_
  refine usra_case .r56 8 15#4 0#3 120#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r8 _ _) h fun h => ?_
  refine usra_case .r61 3 15#4 5#3 125#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r3 _ _) h fun h => ?_
  refine usra_case .r62 2 15#4 6#3 126#7 vd1 vd0 vn1 vn0 rfl rfl (by decide) (usra_2d_r2 _ _) h fun h => ?_
  nomatch h

/-! ## 3. Spatial Memory Routing (`KSpatial`, `Seg2ConstsLo`, `step_strSimd64`) -/

theorem step_strSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .D64 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readVReg128 vt).truncate 64 = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.strSimd .D64 vt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 8 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.strSimd .D64 vt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      SimdMemSize.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

theorem sepLoad64_rcBase {cfg : KCfg} {env : KEnv} {st : KState} {F : SepProp}
    {ea : BitVec 64} {r : Nat} (hr : r < 24)
    (hea : env.rcBase + BitVec.ofNat 64 (8 * r) = ea) :
    SepLoad64 ea (KSpatial cfg env st F) (keccakRcAt r) := by
  have hlen : 8 * r + 8 ≤ mlkemData01Bytes.length := by
    rw [mlkemData01Bytes_length]; omega
  exact SepLoad64.of_pointsToBytes_readLE_RO (P := KSpatial cfg env st F) rfl hlen hea

theorem sepLoad64_constsLo_40 {cfg : KCfg} (hc : cfg.hasConstsLo = true)
    {env : KEnv} {st : KState} {F : SepProp} :
    SepLoad64 (env.sp + 40#64) (KSpatial cfg env st F) (env.sp + 3496#64) := by
  unfold KSpatial
  rw [hc]
  unfold KConstsLoOpt Seg2ConstsLo
  exact (SepLoad64.here (v := env.sp + 3496#64) rfl).left.left.right

theorem sepLoad64_constsLo_88 {cfg : KCfg} (hc : cfg.hasConstsLo = true)
    {env : KEnv} {st : KState} {F : SepProp} :
    SepLoad64 (env.sp + 88#64) (KSpatial cfg env st F) (env.sp + 2203#64) := by
  unfold KSpatial
  rw [hc]
  unfold KConstsLoOpt Seg2ConstsLo
  have hv : (env.sp + 2192#64) + 11#64 = env.sp + 2203#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [hv]
  exact (SepLoad64.here (v := env.sp + 2203#64) rfl).right.right.right.left.right

theorem sepLoad128_constsLo_48 {cfg : KCfg} (hc : cfg.hasConstsLo = true)
    {env : KEnv} {st : KState} {F : SepProp} :
    SepLoad128 (env.sp + 48#64) (KSpatial cfg env st F)
      ((0#64 : BitVec 64) ++ 0x00000000001f0200#64) := by
  unfold KSpatial
  rw [hc]
  unfold KConstsLoOpt Seg2ConstsLo
  have hv : (0x000000000000000000000000001f0200#128 : BitVec 128) =
      (0#64 : BitVec 64) ++ 0x00000000001f0200#64 := by decide
  rw [hv]
  exact (SepLoad128.vec128At
    (v := (0#64 : BitVec 64) ++ 0x00000000001f0200#64) rfl).left.right.left.right

theorem sepLoad128_constsLo_64 {cfg : KCfg} (hc : cfg.hasConstsLo = true)
    {env : KEnv} {st : KState} {F : SepProp} :
    SepLoad128 (env.sp + 64#64) (KSpatial cfg env st F)
      ((0#64 : BitVec 64) ++ 0x00000000001f0100#64) := by
  unfold KSpatial
  rw [hc]
  unfold KConstsLoOpt Seg2ConstsLo
  have hv : (0x000000000000000000000000001f0100#128 : BitVec 128) =
      (0#64 : BitVec 64) ++ 0x00000000001f0100#64 := by decide
  rw [hv]
  exact (SepLoad128.vec128At
    (v := (0#64 : BitVec 64) ++ 0x00000000001f0100#64) rfl).left.right.right.left.right

theorem resolveByteOff?_sound {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {byteOff : Nat}
    (hr : resolveByteOff? st addr = some byteOff) :
    checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (env.sp + BitVec.ofNat 64 byteOff, none) := by
  unfold resolveByteOff? at hr
  cases addr with
  | Offset base off64 | UnscaledOffset base off64 =>
      cases base with
      | sp =>
          simp only at hr
          split at hr <;> try cases hr
          next hcond =>
          rw [Bool.and_eq_true] at hcond
          have hoff : off64 = BitVec.ofNat 64 off64.toNat := beq_iff_eq.mp hcond.2
          refine ⟨by simp [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, hm.hsp_al], ?_⟩
          simp [evalAddrMode, hm.hsp, ← hoff]
      | gpr r =>
          simp only at hr
          by_cases hr31 : (r == 31#5) = true
          · simp [hr31] at hr
          · have hr31F : (r == 31#5) = false := Bool.eq_false_iff.mpr hr31
            have hrNe : r ≠ 31#5 := ne31_of_beq_false hr31F
            simp only [hr31F, Bool.false_eq_true, ↓reduceIte] at hr
            cases hg : st.gprs.get r.toNat <;> simp only [hg] at hr <;> try cases hr
            case spAdd bOff =>
              split at hr <;> try cases hr
              next hcond =>
              rw [Bool.and_eq_true] at hcond
              have htot : bOff + off64 = BitVec.ofNat 64 (bOff + off64).toNat :=
                beq_iff_eq.mp hcond.2
              have hreg := hm.hgprs r hrNe
              rw [hg] at hreg
              simp only [evalKExpr] at hreg
              refine ⟨by simp [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned], ?_⟩
              simp only [evalAddrMode, hreg, BitVec.add_assoc]
              exact Prod.ext (congrArg (env.sp + ·) htot) rfl
      | xzr => simp at hr
  | _ => simp at hr

theorem resolveMemIdx?_sound {cfg : KCfg} (hv : KCfgWf cfg) {env : KEnv} {st : KState}
    {s : State} (hm : KStateMatches env st s) {addr : AddrMode} {words : Nat}
    {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr words = some (inB, idx)) :
    checkAddrSPAligned s addr = true ∧
      if inB then
        idx + words ≤ cfg.lenB ∧
          evalAddrMode s addr =
            ((env.sp + BitVec.ofNat 64 cfg.offB) + BitVec.ofNat 64 (8 * idx), none)
      else
        idx + words ≤ cfg.lenA ∧
          evalAddrMode s addr =
            ((env.sp + BitVec.ofNat 64 cfg.offA) + BitVec.ofNat 64 (8 * idx), none) := by
  rcases hv with ⟨hmodA, _, hmodB, _⟩
  unfold resolveMemIdx? at hr
  cases hb : resolveByteOff? st addr with
  | none => simp [hb] at hr
  | some byteOff =>
      simp only [hb] at hr
      rcases resolveByteOff?_sound hm hb with ⟨hsp, haddr⟩
      refine ⟨hsp, ?_⟩
      by_cases hmod : (!(Nat.beq (byteOff % 8) 0)) = true
      · simp [hmod] at hr
      · have hmod0 : byteOff % 8 = 0 := by
          cases hm8 : Nat.beq (byteOff % 8) 0
          · simp [hm8] at hmod
          · exact Nat.eq_of_beq_eq_true hm8
        have hnotF : (!(Nat.beq (byteOff % 8) 0)) = false := Bool.eq_false_iff.mpr hmod
        simp only [hnotF, Bool.false_eq_true, ↓reduceIte] at hr
        split at hr
        · next hA =>
            cases hr
            simp only [Bool.false_eq_true, ↓reduceIte]
            simp only [Bool.and_eq_true, Nat.ble_eq] at hA
            refine ⟨by omega, ?_⟩
            rw [haddr, BitVec.add_assoc]
            congr 2; rw [← BitVec.ofNat_add]; congr 1; omega
        · split at hr <;> try cases hr
          next hB =>
            simp only [↓reduceIte]
            simp only [Bool.and_eq_true, Nat.ble_eq] at hB
            refine ⟨by omega, ?_⟩
            rw [haddr, BitVec.add_assoc]
            congr 2; rw [← BitVec.ofNat_add]; congr 1; omega

private theorem kspatial_focus_A (cfg : KCfg) (env : KEnv) (st : KState) (F : SepProp) :
    KSpatial cfg env st F =
      TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (evalMemTree env st.memA) ∗
        ((env.rcBase ↦ᵣ mlkemData01Bytes) ∗
          (KConstsLoOpt env.sp cfg.hasConstsLo ∗
            (TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB (evalMemTree env st.memB) ∗ F))) := by
  unfold KSpatial
  rw [← sepConj_assoc (KConstsLoOpt env.sp cfg.hasConstsLo),
      sepConj_comm (KConstsLoOpt env.sp cfg.hasConstsLo),
      sepConj_assoc (TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) _ _),
      ← sepConj_assoc (env.rcBase ↦ᵣ mlkemData01Bytes),
      sepConj_comm (env.rcBase ↦ᵣ mlkemData01Bytes),
      sepConj_assoc]

private theorem kspatial_focus_B (cfg : KCfg) (env : KEnv) (st : KState) (F : SepProp) :
    KSpatial cfg env st F =
      TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB (evalMemTree env st.memB) ∗
        ((env.rcBase ↦ᵣ mlkemData01Bytes) ∗
          (KConstsLoOpt env.sp cfg.hasConstsLo ∗
            (TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (evalMemTree env st.memA) ∗ F))) := by
  rw [kspatial_focus_A]
  set A := TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (evalMemTree env st.memA)
  set B := TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB (evalMemTree env st.memB)
  set R1 := (env.rcBase ↦ᵣ mlkemData01Bytes)
  set R2 := KConstsLoOpt env.sp cfg.hasConstsLo
  rw [← sepConj_assoc R2 B F, sepConj_comm R2 B, sepConj_assoc B R2 F,
      ← sepConj_assoc R1 B _, sepConj_comm R1 B, sepConj_assoc B R1 _,
      ← sepConj_assoc A B _, sepConj_comm A B, sepConj_assoc B A _,
      ← sepConj_assoc A R1 _, sepConj_comm A R1, sepConj_assoc R1 A _,
      ← sepConj_assoc A R2 _, sepConj_comm A R2, sepConj_assoc R2 A _]

theorem sepLoad64_kspatial {cfg : KCfg} (hv : KCfgWf cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 1 = some (inB, idx)) (F : SepProp) :
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepLoad64 ea (KSpatial cfg env st F) (evalKExpr env (readMemWord st inB idx)) := by
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte, readMemWord] at hrest ⊢
    refine ⟨_, hsp, hrest.2, ?_⟩
    exact SepLoad64.congr_val
      (sepLoad64_treeMem (by omega) hv.2.1 (kspatial_focus_A cfg env st F) rfl)
      (by simp [evalMemTree, BTree.get_map])
  · simp only [↓reduceIte, readMemWord] at hrest ⊢
    refine ⟨_, hsp, hrest.2, ?_⟩
    exact SepLoad64.congr_val
      (sepLoad64_treeMem (by omega) hv.2.2.2 (kspatial_focus_B cfg env st F) rfl)
      (by simp [evalMemTree, BTree.get_map])

theorem sepStore64_kspatial {cfg : KCfg} (hv : KCfgWf cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 1 = some (inB, idx)) (e : KExpr) (F : SepProp) :
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepStore64 ea (evalKExpr env e) (KSpatial cfg env st F)
        (KSpatial cfg env (writeMemWord st inB idx e) F) := by
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte] at hrest
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hP' := kspatial_focus_A cfg env (writeMemWord st false idx e) F
    simp only [writeMemWord, Bool.false_eq_true, ↓reduceIte, evalMemTree, BTree.map_set] at hP'
    exact sepStore64_treeMem (by omega) hv.2.1 (kspatial_focus_A cfg env st F) hP' rfl
  · simp only [↓reduceIte] at hrest
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hP' := kspatial_focus_B cfg env (writeMemWord st true idx e) F
    simp only [writeMemWord, ↓reduceIte, evalMemTree, BTree.map_set] at hP'
    exact sepStore64_treeMem (by omega) hv.2.2.2 (kspatial_focus_B cfg env st F) hP' rfl

private theorem add_idx2_eq_add16 (ptr : BitVec 64) (idx : Nat) :
    ptr + BitVec.ofNat 64 (8 * (idx + 2)) = (ptr + BitVec.ofNat 64 (8 * idx)) + 16#64 := by
  have h16 : BitVec.ofNat 64 (8 * (idx + 2)) = BitVec.ofNat 64 (8 * idx) + 16#64 :=
    BitVec.ofNat_add (8 * idx) 16
  rw [h16, ← BitVec.add_assoc]

theorem sepLoad128_kspatial {cfg : KCfg} (hv : KCfgWf cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 2 = some (inB, idx)) (F : SepProp) :
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepLoad128 ea (KSpatial cfg env st F)
        (evalKExpr env (readMemWord st inB (idx + 1)) ++ evalKExpr env (readMemWord st inB idx)) := by
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte, readMemWord] at hrest ⊢
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hl := sepLoad128_treeMem hrest.1 hv.2.1 (kspatial_focus_A cfg env st F) rfl
    simpa [evalMemTree, BTree.get_map] using hl
  · simp only [↓reduceIte, readMemWord] at hrest ⊢
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hl := sepLoad128_treeMem hrest.1 hv.2.2.2 (kspatial_focus_B cfg env st F) rfl
    simpa [evalMemTree, BTree.get_map] using hl

theorem sepLoad256_kspatial {cfg : KCfg} (hv : KCfgWf cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 4 = some (inB, idx)) (F : SepProp) :
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepLoad128 ea (KSpatial cfg env st F)
        (evalKExpr env (readMemWord st inB (idx + 1)) ++ evalKExpr env (readMemWord st inB idx)) ∧
      SepLoad128 (ea + 16#64) (KSpatial cfg env st F)
        (evalKExpr env (readMemWord st inB (idx + 3)) ++ evalKExpr env (readMemWord st inB (idx + 2))) := by
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte, readMemWord] at hrest ⊢
    refine ⟨_, hsp, hrest.2, ?_, ?_⟩
    · simpa [evalMemTree, BTree.get_map] using
        sepLoad128_treeMem (by omega) hv.2.1 (kspatial_focus_A cfg env st F) rfl
    · simpa [evalMemTree, BTree.get_map] using
        sepLoad128_treeMem (idx := idx + 2) (by omega) hv.2.1 (kspatial_focus_A cfg env st F)
          (add_idx2_eq_add16 _ idx)
  · simp only [↓reduceIte, readMemWord] at hrest ⊢
    refine ⟨_, hsp, hrest.2, ?_, ?_⟩
    · simpa [evalMemTree, BTree.get_map] using
        sepLoad128_treeMem (by omega) hv.2.2.2 (kspatial_focus_B cfg env st F) rfl
    · simpa [evalMemTree, BTree.get_map] using
        sepLoad128_treeMem (idx := idx + 2) (by omega) hv.2.2.2 (kspatial_focus_B cfg env st F)
          (add_idx2_eq_add16 _ idx)

theorem sepStore128_kspatial {cfg : KCfg} (hv : KCfgWf cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 2 = some (inB, idx)) (eLo eHi : KExpr) (F : SepProp) :
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepStore128 ea (evalKExpr env eHi ++ evalKExpr env eLo) (KSpatial cfg env st F)
        (KSpatial cfg env (writeMemWord (writeMemWord st inB idx eLo) inB (idx + 1) eHi) F) := by
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte] at hrest
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hP' := kspatial_focus_A cfg env (writeMemWord (writeMemWord st false idx eLo) false (idx + 1) eHi) F
    simp only [writeMemWord, Bool.false_eq_true, ↓reduceIte, evalMemTree, BTree.map_set] at hP'
    exact sepStore128_treeMem hrest.1 hv.2.1 (kspatial_focus_A cfg env st F) hP' rfl
  · simp only [↓reduceIte] at hrest
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hP' := kspatial_focus_B cfg env (writeMemWord (writeMemWord st true idx eLo) true (idx + 1) eHi) F
    simp only [writeMemWord, ↓reduceIte, evalMemTree, BTree.map_set] at hP'
    exact sepStore128_treeMem hrest.1 hv.2.2.2 (kspatial_focus_B cfg env st F) hP' rfl

theorem sepStore256_kspatial {cfg : KCfg} (hv : KCfgWf cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 4 = some (inB, idx))
    (e1Lo e1Hi e2Lo e2Hi : KExpr) (F : SepProp) :
    let st1 := writeMemWord (writeMemWord st inB idx e1Lo) inB (idx + 1) e1Hi
    let st2 := writeMemWord (writeMemWord st1 inB (idx + 2) e2Lo) inB (idx + 3) e2Hi
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepStore128 ea (evalKExpr env e1Hi ++ evalKExpr env e1Lo)
        (KSpatial cfg env st F) (KSpatial cfg env st1 F) ∧
      SepStore128 (ea + 16#64) (evalKExpr env e2Hi ++ evalKExpr env e2Lo)
        (KSpatial cfg env st1 F) (KSpatial cfg env st2 F) := by
  intro st1 st2
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte] at hrest
    refine ⟨_, hsp, hrest.2, ?_, ?_⟩
    · have hP1 := kspatial_focus_A cfg env st1 F
      simp only [st1, writeMemWord, Bool.false_eq_true, ↓reduceIte, evalMemTree, BTree.map_set] at hP1
      exact sepStore128_treeMem (by omega) hv.2.1 (kspatial_focus_A cfg env st F) hP1 rfl
    · have hP1 := kspatial_focus_A cfg env st1 F
      have hP2 := kspatial_focus_A cfg env st2 F
      simp only [st2, writeMemWord, Bool.false_eq_true, ↓reduceIte, evalMemTree, BTree.map_set] at hP2
      exact sepStore128_treeMem (idx := idx + 2) (by omega) hv.2.1 hP1 hP2 (add_idx2_eq_add16 _ idx)
  · simp only [↓reduceIte] at hrest
    refine ⟨_, hsp, hrest.2, ?_, ?_⟩
    · have hP1 := kspatial_focus_B cfg env st1 F
      simp only [st1, writeMemWord, ↓reduceIte, evalMemTree, BTree.map_set] at hP1
      exact sepStore128_treeMem (by omega) hv.2.2.2 (kspatial_focus_B cfg env st F) hP1 rfl
    · have hP1 := kspatial_focus_B cfg env st1 F
      have hP2 := kspatial_focus_B cfg env st2 F
      simp only [st2, writeMemWord, ↓reduceIte, evalMemTree, BTree.map_set] at hP2
      exact sepStore128_treeMem (idx := idx + 2) (by omega) hv.2.2.2 hP1 hP2 (add_idx2_eq_add16 _ idx)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge

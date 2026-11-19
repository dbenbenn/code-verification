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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB

/-!
# `kyber_encapsulate` (`B07`) — Segment 2 Post-Site Shuffle/Clamp Stepper (`Seg2Clamp`)

Post-site shuffle/clamp symbolic stepper (`ClampState`, `stepClampInst`, `runClampRange`,
`sepWP_of_runClampRange`) and slot/register preservation extractors shared by `Seg2Init` and
`Seg2Extra`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (KeccakState keccakAbsorb keccakF1600)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (clampSampled)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSepFrom
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  RejSiteConfig SitePreserved
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  step_ldrQ128 step_strQ128
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blkPC07 fetchWordTree07
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr readMemWord resolveMemIdx? writeMemWord
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem BTreeMemFrom KCfgValid KSpatial KStateMatches blk07NoRelocInRange evalMemTree
  fetch_blk07_range matches_setMem matches_writeGpr matches_writeVReg sepLoad128_kspatial
  sepLoad64_kspatial sepStore128_kspatial sepStore64_kspatial
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval (
  matches_advancePC matches_setPC matches_writeMemWord setPC_self
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (
  btree_ext_get readSlot readSlot_holds slotHolds slotValid
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (eval_checked_gpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (
  MemAHeaderOk RowCalleeGprs cfgC
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA (
  calleeGprExpr checkCalleeGprsPreserved checkHeaderPreserved checked_calleeGprs checked_headerOk
  envInitA eval_headerMemAExpr headerMemAExpr stInitA_matches
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitB (slotHolds_inj)

attribute [local irreducible] blkPC07 keccakF1600 keccakAbsorb BTreeMem

/-! ## 1. `cfgClamp`, Branch Helpers, & Symbolic Shuffle/Clamp Stepper -/

@[expose] def cfgClamp : KCfg := { offA := 144, lenA := 286, offB := 24720, lenB := 4 }

theorem cfgClamp_valid : KCfgValid cfgClamp := by decide

theorem btreeMem4_eq_multiLaneSampled4 (ptr : BitVec 64) {t : BTree (BitVec 64) 9}
    {f : Nat → Nat}
    (h0 : t.get 0 = BitVec.ofNat 64 (f 0)) (h1 : t.get 1 = BitVec.ofNat 64 (f 1))
    (h2 : t.get 2 = BitVec.ofNat 64 (f 2)) (h3 : t.get 3 = BitVec.ofNat 64 (f 3)) :
    BTreeMem ptr 4 t = MultiLaneSampled ptr 4 f := by
  have hp0 : ptr + BitVec.ofNat 64 (8 * 0) = ptr := BitVec.add_zero ptr
  have hp1 : BitVec.ofNat 64 (8 * 1) = 8#64 := rfl
  have hp2 : ptr + BitVec.ofNat 64 (8 * 2) = (ptr + 8#64) + 8#64 := by bv_omega
  have hp3 : ptr + BitVec.ofNat 64 (8 * 3) = ((ptr + 8#64) + 8#64) + 8#64 := by bv_omega
  unfold BTreeMem
  simp only [BTreeMemFrom, MultiLaneSampled, MultiLaneSepFrom,
    h0, h1, h2, h3, hp0, hp1, hp2, hp3]

theorem multiLaneSampled4_eq_btreeMem4 (ptr : BitVec 64) (f : Nat → Nat) :
    MultiLaneSampled ptr 4 f =
      BTreeMem ptr 4 (BTree.ofFn 9 (fun i => BitVec.ofNat 64 (f i))) :=
  (btreeMem4_eq_multiLaneSampled4 ptr
    (BTree.get_ofFn 9 _ 0 (by decide)) (BTree.get_ofFn 9 _ 1 (by decide))
    (BTree.get_ofFn 9 _ 2 (by decide)) (BTree.get_ofFn 9 _ 3 (by decide))).symm

private theorem clampSelect_fin :
    ∀ s : Fin 272,
      (if ConditionHolds .HI (subsPState64 (BitVec.ofNat 64 s.val) 255#64) then 256#64
        else BitVec.ofNat 64 s.val) = BitVec.ofNat 64 (clampSampled s.val) := by
  decide +kernel

theorem clampSelect_of_le271 {s : Nat} (hs : s ≤ 271) :
    (if ConditionHolds .HI (subsPState64 (BitVec.ofNat 64 s) 255#64) then 256#64
      else BitVec.ofNat 64 s) = BitVec.ofNat 64 (clampSampled s) :=
  clampSelect_fin ⟨s, by omega⟩

private theorem condLS_255_fin :
    ∀ s : Fin 272,
      ConditionHolds .LS (subsPState64 (BitVec.ofNat 64 s.val) 255#64) = decide (s.val < 256) := by
  decide +kernel

theorem condLS_255_of_le271 {s : Nat} (hs : s ≤ 271) :
    ConditionHolds .LS (subsPState64 (BitVec.ofNat 64 s) 255#64) = decide (s < 256) :=
  condLS_255_fin ⟨s, by omega⟩

theorem step_b_seg2 [MlKemPlacement] {b tgt : BitVec 64} {wLo wHi w : Nat} {disp : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hnr : blk07NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 10252)
    (hlo : wLo ≤ w) (hhi : w < wHi) (hfw : fetchWordTree07 w = some (.b disp))
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hnext : SepWP (blkPC07.rebase b (fun _ => none)) tgt
      (s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) P post oom) :
    SepWP (blkPC07.rebase b (fun _ => none)) tgt s P post oom := by
  refine SepWP.step_pure hpc hrun (fetch_blk07_range hnr hmax hlo hhi hfw)
    (s' := s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) ?_ rfl hnext
  rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hpc]

theorem step_bCond_seg2 [MlKemPlacement] {b tgt : BitVec 64} {wLo wHi w : Nat}
    {cond : CondCode} {disp : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hnr : blk07NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 10252)
    (hlo : wLo ≤ w) (hhi : w < wHi) (hfw : fetchWordTree07 w = some (.bCond cond disp))
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hTaken : ConditionHolds cond s.pstate = true →
      SepWP (blkPC07.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) P post oom)
    (hFall : ConditionHolds cond s.pstate = false →
      SepWP (blkPC07.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * (w + 1)))) P post oom) :
    SepWP (blkPC07.rebase b (fun _ => none)) tgt s P post oom := by
  by_cases hc : ConditionHolds cond s.pstate = true
  · refine SepWP.step_pure hpc hrun (fetch_blk07_range hnr hmax hlo hhi hfw)
      (s' := s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) ?_ rfl (hTaken hc)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hc, hpc]
  · have hcF : ConditionHolds cond s.pstate = false := Bool.eq_false_iff.mpr hc
    have hpcAdv : s.advancePC = s.setPC (b + BitVec.ofNat 64 (4 * (w + 1))) := by
      cases s; simp only [State.advancePC, State.setPC] at hpc ⊢; congr 1; rw [hpc]; bv_omega
    refine SepWP.step_pure hpc hrun (fetch_blk07_range hnr hmax hlo hhi hfw)
      (s' := s.advancePC) ?_ rfl (by rw [hpcAdv]; exact hFall hcF)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hcF]

structure ClampState where
  st     : KState
  cmpOpt : Option (KExpr × BitVec 64)

@[expose] def ClampEnvValid (env : KEnv) : Prop :=
  ∀ c, c < 4 →
    (if ConditionHolds .HI (subsPState64 (env.vars (800 + c)) 255#64) then 256#64
      else env.vars (800 + c)) = env.vars (810 + c)

@[expose] def ClampCmpMatches (env : KEnv) (cmpOpt : Option (KExpr × BitVec 64)) (s : State) : Prop :=
  match cmpOpt with
  | none => True
  | some (lhs, rhs) => s.pstate = subsPState64 (evalKExpr env lhs) rhs

@[expose] def ClampMatches (env : KEnv) (cs : ClampState) (s : State) : Prop :=
  KStateMatches env cs.st s ∧
  cs.st.zFlag = none ∧
  ClampCmpMatches env cs.cmpOpt s

@[expose] def stepClampInst (cfg : KCfg) (inst : Instr) (cs : ClampState) : Option ClampState :=
  let st := cs.st
  match inst with
  | .simdThreeSame true false 0x2#2 rm 0x03#5 rn rd =>
      if rm == rn then
        some { st := { st with vregs := st.vregs.set rd.toNat (st.vregs.get rm.toNat) }, cmpOpt := cs.cmpOpt }
      else none
  | .ldrSimd .Q128 vt addr =>
      match resolveMemIdx? cfg st addr 2 with
      | some (inB, idx) =>
          some { st := { st with vregs := st.vregs.set vt.toNat (readMemWord st inB idx, readMemWord st inB (idx + 1)) },
                 cmpOpt := cs.cmpOpt }
      | none => none
  | .strSimd .Q128 vt addr =>
      match resolveMemIdx? cfg st addr 2 with
      | some (inB, idx) =>
          let vp := st.vregs.get vt.toNat
          some { st := writeMemWord (writeMemWord st inB idx vp.1) inB (idx + 1) vp.2, cmpOpt := cs.cmpOpt }
      | none => none
  | .ldr .W64 .X64 false (.gpr rt) addr =>
      if rt == 31#5 then none
      else match resolveMemIdx? cfg st addr 1 with
      | some (inB, idx) =>
          some { st := { st with gprs := st.gprs.set rt.toNat (readMemWord st inB idx) }, cmpOpt := cs.cmpOpt }
      | none => none
  | .str .X64 (.gpr rt) addr =>
      if rt == 31#5 then none
      else match resolveMemIdx? cfg st addr 1 with
      | some (inB, idx) =>
          some { st := writeMemWord st inB idx (st.gprs.get rt.toNat), cmpOpt := cs.cmpOpt }
      | none => none
  | .addSubImm .W64 .SUBS .xzr (.gpr rn) imm12 false =>
      if rn == 31#5 then none
      else some { st := { st with zFlag := none }, cmpOpt := some (st.gprs.get rn.toNat, imm12.zeroExtend 64) }
  | .condSelect .W64 .CSEL (.gpr rd) (.gpr rn) (.gpr rm) .HI =>
      if rd == 31#5 || rn == 31#5 || rm == 31#5 then none
      else match cs.cmpOpt, st.gprs.get rm.toNat with
      | some (.var cid, 255#64), .var mid =>
          if Nat.beq cid mid && Nat.ble 800 cid && Nat.blt cid 804 &&
              (st.gprs.get rn.toNat).beq (.const64 256#64) then
            some { st := { st with gprs := st.gprs.set rd.toNat (.var (cid + 10)) }, cmpOpt := cs.cmpOpt }
          else none
      | _, _ => none
  | _ => none

@[expose] def runClampRange (cfg : KCfg) (w : Nat) : Nat → ClampState → Option ClampState
  | 0, cs => some cs
  | n + 1, cs =>
      match fetchWordTree07 w with
      | none => none
      | some inst =>
          match stepClampInst cfg inst cs with
          | none => none
          | some cs' => runClampRange cfg (w + 1) n cs'

private theorem cmp_pstate_congr {env : KEnv} {cmpOpt : Option (KExpr × BitVec 64)} {s s' : State}
    (hcmp : ClampCmpMatches env cmpOpt s)
    (hps : s'.pstate = s.pstate) :
    ClampCmpMatches env cmpOpt s' := by
  cases cmpOpt with
  | none => trivial
  | some p => exact hps.trans hcmp

theorem sepWP_of_stepClampInst {prog : Program} {tgt pc : BitVec 64} {cfg : KCfg}
    (hv : KCfgValid cfg) {env : KEnv} (henv : ClampEnvValid env)
    {s : State} {cs cs' : ClampState} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {inst : Instr}
    (hm : ClampMatches env cs s)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hstep : stepClampInst cfg inst cs = some cs')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      ClampMatches env cs' s' →
      SepWP prog tgt s' (KSpatial cfg env cs'.st F) post oom) :
    SepWP prog tgt s (KSpatial cfg env cs.st F) post oom := by
  rcases hm with ⟨hm0, hzf0, hcmp0⟩
  unfold stepClampInst at hstep
  split at hstep <;> try contradiction
  · rename_i rm rn rd
    by_cases hrr : (rm == rn) = true
    · have hrrEq : rm = rn := beq_iff_eq.mp hrr
      subst hrrEq
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      let vn := cs.st.vregs.get rm.toNat
      refine SepWP.step_pure hpc hrun hfetch
        (s' := (s.writeVReg128 rd (evalKExpr env vn.2 ++ evalKExpr env vn.1)).advancePC) ?_ rfl ?_
      · rw [setPC_self hpc]
        simp [Program.evalInst, execInstWithSvc, hm0.hvregs rm, vn]
      · exact hnext _ (by simp [State.advancePC, hpc]) hrun
          ⟨matches_advancePC (matches_writeVReg hm0 rd vn rfl), hzf0, cmp_pstate_congr hcmp0 rfl⟩
    · simp [hrr] at hstep
  · rename_i vt addr
    cases hr : resolveMemIdx? cfg cs.st addr 2 with
    | none => simp [hr] at hstep
    | some p =>
      rcases p with ⟨inB, idx⟩
      simp only [hr, Option.some.injEq] at hstep; subst hstep
      rcases sepLoad128_kspatial hv hm0 hr F with ⟨ea, hsp, haddr, hld⟩
      exact step_ldrQ128 hpc hrun hfetch hsp haddr hld rfl
        (hnext _ rfl hrun ⟨matches_setPC (matches_writeVReg hm0 vt _ rfl) _, hzf0, cmp_pstate_congr hcmp0 rfl⟩)
  · rename_i vt addr
    cases hr : resolveMemIdx? cfg cs.st addr 2 with
    | none => simp [hr] at hstep
    | some p =>
      rcases p with ⟨inB, idx⟩
      simp only [hr, Option.some.injEq] at hstep; subst hstep
      let vp := cs.st.vregs.get vt.toNat
      rcases sepStore128_kspatial hv hm0 hr vp.1 vp.2 F with ⟨ea, hsp, haddr, hst128⟩
      exact step_strQ128 hpc hrun hfetch hsp haddr (hm0.hvregs vt) hst128 rfl
        (fun m' => hnext _ rfl hrun ⟨matches_writeMemWord
          (matches_writeMemWord (matches_setMem (matches_setPC hm0 _) m') inB idx vp.1) inB (idx + 1) vp.2,
          by cases inB <;> exact hzf0, cmp_pstate_congr hcmp0 rfl⟩)
  · rename_i rt addr
    by_cases hrt : (rt == 31#5) = true
    · simp [hrt] at hstep
    · have hrtF : (rt == 31#5) = false := Bool.eq_false_iff.mpr hrt
      have hrtNe : rt ≠ 31#5 := fun h => hrt (beq_iff_eq.mpr h)
      simp only [hrtF, Bool.false_eq_true, ↓reduceIte] at hstep
      cases hr : resolveMemIdx? cfg cs.st addr 1 with
      | none => simp [hr] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩
        simp only [hr, Option.some.injEq] at hstep; subst hstep
        rcases sepLoad64_kspatial hv hm0 hr F with ⟨ea, hsp, haddr, hld64⟩
        exact SepWP.step_ldr64 hpc hrun hfetch hsp haddr hld64 rfl
          (hnext _ rfl hrun ⟨matches_setPC (matches_writeGpr hm0 hrtNe _ rfl) _, hzf0, cmp_pstate_congr hcmp0 rfl⟩)
  · rename_i rt addr
    by_cases hrt : (rt == 31#5) = true
    · simp [hrt] at hstep
    · have hrtF : (rt == 31#5) = false := Bool.eq_false_iff.mpr hrt
      have hrtNe : rt ≠ 31#5 := fun h => hrt (beq_iff_eq.mpr h)
      simp only [hrtF, Bool.false_eq_true, ↓reduceIte] at hstep
      cases hr : resolveMemIdx? cfg cs.st addr 1 with
      | none => simp [hr] at hstep
      | some p =>
        rcases p with ⟨inB, idx⟩
        simp only [hr, Option.some.injEq] at hstep; subst hstep
        let e := cs.st.gprs.get rt.toNat
        rcases sepStore64_kspatial hv hm0 hr e F with ⟨ea, hsp, haddr, hst64⟩
        exact SepWP.step_str64 hpc hrun hfetch hsp haddr (hm0.hgprs rt hrtNe) hst64 rfl
          (fun m' => hnext _ rfl hrun ⟨matches_writeMemWord (matches_setMem (matches_setPC hm0 _) m') inB idx e,
            by cases inB <;> exact hzf0, cmp_pstate_congr hcmp0 rfl⟩)
  · rename_i rn imm12
    by_cases hrn : (rn == 31#5) = true
    · simp [hrn] at hstep
    · have hrnF : (rn == 31#5) = false := Bool.eq_false_iff.mpr hrn
      have hrnNe : rn ≠ 31#5 := fun h => hrn (beq_iff_eq.mpr h)
      simp only [hrnF, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
      let ps := subsPState64 (s.readReg64 (.gpr rn)) (imm12.zeroExtend 64)
      refine SepWP.step_pure hpc hrun hfetch
        (s' := ((s.setPC pc).setPState ps).advancePC) ?_ rfl ?_
      · simp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.writeReg, ps]
      · refine hnext _ rfl hrun ⟨matches_advancePC
          (KeccakSymEval.matches_setPState (matches_setPC hm0 pc) (zf := none) trivial), rfl, ?_⟩
        simpa [ClampCmpMatches, ps] using congrArg (subsPState64 · (imm12.zeroExtend 64)) (hm0.hgprs rn hrnNe)
  · rename_i rd rn rm
    by_cases hrr : (rd == 31#5 || rn == 31#5 || rm == 31#5) = true
    · simp [hrr] at hstep
    · have hrrF : (rd == 31#5 || rn == 31#5 || rm == 31#5) = false := Bool.eq_false_iff.mpr hrr
      simp only [hrrF, Bool.false_eq_true, ↓reduceIte] at hstep
      rcases Bool.or_eq_false_iff.mp hrrF with ⟨hrdnF, hrmF⟩
      rcases Bool.or_eq_false_iff.mp hrdnF with ⟨hrdF, hrnF⟩
      have hrdNe : rd ≠ 31#5 := fun h => by rw [beq_iff_eq.mpr h] at hrdF; cases hrdF
      have hrnNe : rn ≠ 31#5 := fun h => by rw [beq_iff_eq.mpr h] at hrnF; cases hrnF
      have hrmNe : rm ≠ 31#5 := fun h => by rw [beq_iff_eq.mpr h] at hrmF; cases hrmF
      split at hstep <;> try contradiction
      next cid mid hcmpEq hrmEq =>
        split at hstep <;> [skip; contradiction]
        next hchk =>
          simp only [Option.some.injEq] at hstep; subst hstep
          simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at hchk
          rcases hchk with ⟨⟨⟨hcm, h800⟩, h804⟩, hrn256C⟩
          have hrn256 := KExpr.beq_eq_true hrn256C
          subst hcm
          have hps : s.pstate = subsPState64 (env.vars cid) 255#64 := by
            simpa [ClampCmpMatches, hcmpEq, evalKExpr] using hcmp0
          have hval : (if ConditionHolds .HI s.pstate then s.readReg64 (.gpr rn)
              else s.readReg64 (.gpr rm)) = evalKExpr env (.var (cid + 10)) := by
            rw [hps, hm0.hgprs rn hrnNe, hm0.hgprs rm hrmNe, hrn256, hrmEq]
            have hc := henv (cid - 800) (by omega)
            rw [show 800 + (cid - 800) = cid by omega, show 810 + (cid - 800) = cid + 10 by omega] at hc
            simpa [evalKExpr] using hc
          refine SepWP.step_pure hpc hrun hfetch
            (s' := ((s.setPC pc).writeReg64 (.gpr rd) (evalKExpr env (.var (cid + 10)))).advancePC) ?_ rfl ?_
          · have hregs : (s.setPC pc).regs = s.regs := rfl
            simp [Program.evalInst, execInstWithSvc, execCondSelect, State.readReg, State.writeReg,
              State.readReg64, hregs, ← hval]
          · exact hnext _ rfl hrun ⟨matches_advancePC
              (matches_writeGpr (matches_setPC hm0 pc) hrdNe (.var (cid + 10)) rfl), hzf0,
              cmp_pstate_congr hcmp0 rfl⟩

theorem sepWP_of_runClampRange [MlKemPlacement] {b tgt : BitVec 64} {cfg : KCfg}
    (hv : KCfgValid cfg) {env : KEnv} (henv : ClampEnvValid env)
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {wLo wHi : Nat} (count w : Nat) {cs csEnd : ClampState} {s : State}
    (hnr : blk07NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 10252)
    (hlo : wLo ≤ w) (hhi : w + count ≤ wHi)
    (hrun_sym : runClampRange cfg w count cs = some csEnd)
    (hm : ClampMatches env cs s)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hnext : ∀ sf : State, sf.pc = b + BitVec.ofNat 64 (4 * (w + count)) →
      sf.status = .Running → ClampMatches env csEnd sf →
      SepWP (blkPC07.rebase b (fun _ => none)) tgt sf (KSpatial cfg env csEnd.st F) post oom) :
    SepWP (blkPC07.rebase b (fun _ => none)) tgt s (KSpatial cfg env cs.st F) post oom := by
  induction count generalizing w cs s with
  | zero =>
    simp only [runClampRange, Option.some.injEq] at hrun_sym; subst hrun_sym
    exact hnext s (by simpa using hpc) hrun hm
  | succ n ih =>
    unfold runClampRange at hrun_sym
    cases hfw : fetchWordTree07 w with
    | none => simp [hfw] at hrun_sym
    | some inst =>
      simp only [hfw] at hrun_sym
      cases hst : stepClampInst cfg inst cs with
      | none => simp [hst] at hrun_sym
      | some cs1 =>
        simp only [hst] at hrun_sym
        have hfetch := fetch_blk07_range (b := b) hnr hmax hlo (by omega) hfw
        refine sepWP_of_stepClampInst hv henv hm hpc hrun hfetch hst ?_
        intro s' hpc' hrun' hm'
        have hpc_eq : b + BitVec.ofNat 64 (4 * w) + 4#64 = b + BitVec.ofNat 64 (4 * (w + 1)) := by
          bv_omega
        rw [hpc_eq] at hpc'
        have hend_eq : 4 * (w + (n + 1)) = 4 * (w + 1 + n) := by omega
        exact ih (w + 1) (by omega) (by omega) hrun_sym hm' hpc' hrun'
          (fun sf h1 h2 h3 => hnext sf (by rwa [hend_eq]) h2 h3)

/-! ## 2. Clamp Initial State, Environment, & Post-Clamp State Extractors -/

@[expose] def stRawClamp : KState :=
  { vregs := BTree.ofFn 5 (fun vr => (.var (2 * vr), .var (2 * vr + 1)))
    gprs  := BTree.ofFn 5 calleeGprExpr
    memA  := BTree.ofFn 9 headerMemAExpr
    memB  := BTree.ofFn 9 (fun i => if i < 4 then .var (800 + i) else .const64 0#64)
    zFlag := none }

@[expose] def csInitClamp : ClampState := { st := stRawClamp, cmpOpt := none }

@[expose] def envClamp (sp rcBase : BitVec 64) (rho : List (BitVec 8)) (row : Nat)
    (s : State) (tA : BTree (BitVec 64) 9) (sampled' : Nat → Nat) : KEnv :=
  { (envInitA sp rcBase rho row s tA) with
    vars := fun id =>
      if id < 800 then (envInitA sp rcBase rho row s tA).vars id
      else if id < 804 then BitVec.ofNat 64 (sampled' (id - 800))
      else if 810 ≤ id && id < 814 then BitVec.ofNat 64 (clampSampled (sampled' (id - 810)))
      else 0#64 }

theorem envClamp_valid {sp rcBase : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s : State} {tA : BTree (BitVec 64) 9} {sampled' : Nat → Nat}
    (hsamp : ∀ c, c < 4 → sampled' c ≤ 271) :
    ClampEnvValid (envClamp sp rcBase rho row s tA sampled') := by
  intro c hc
  have h1 : ¬(800 + c < 800) := by omega
  have h2 : 800 + c < 804 := by omega
  have h3 : ¬(810 + c < 800) := by omega
  have h4 : ¬(810 + c < 804) := by omega
  have h5 : (810 ≤ 810 + c && 810 + c < 814) = true := by simp; omega
  simp only [envClamp, h1, h2, h3, h4, h5, ↓reduceIte,
    show 800 + c - 800 = c by omega, show 810 + c - 810 = c by omega]
  exact clampSelect_of_le271 (hsamp c hc)

private theorem calleeGprExpr_lt800 :
    ∀ k : Fin 32, Seg2Base.exprVarsOk (fun id => decide (id < 800)) (calleeGprExpr k.val) = true := by
  decide

private theorem headerMemAExpr_lt800 :
    ∀ i : Fin 512, Seg2Base.exprVarsOk (fun id => decide (id < 800)) (headerMemAExpr i.val) = true := by
  decide +kernel

theorem stRawClamp_matches {sp rcBase : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s : State} {tA : BTree (BitVec 64) 9} {sampled' : Nat → Nat}
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hgprs : RowCalleeGprs sp rcBase row s) (hhdr : MemAHeaderOk sp rho tA) (F : SepProp) :
    let env := envClamp sp rcBase rho row s tA sampled'
    ClampMatches env csInitClamp s ∧
      KSpatial cfgClamp env csInitClamp.st F =
        ((rcBase ↦ᵣ mlkemData01Bytes) ∗
          (BTreeMem (sp + 144#64) 286 tA ∗
            (MultiLaneSampled (sp + 24720#64) 4 sampled' ∗ F))) := by
  have hsub : ∀ e, Seg2Base.exprVarsOk (fun id => decide (id < 800)) e = true →
      evalKExpr (envClamp sp rcBase rho row s tA sampled') e =
        evalKExpr (envInitA sp rcBase rho row s tA) e :=
    Seg2Base.evalKExpr_congr_ok rfl rfl rfl fun id hid => by
      simp only [decide_eq_true_eq] at hid; simp [envClamp, hid]
  have hmA0 := (stInitA_matches hsp hspA hgprs hhdr).1
  refine ⟨⟨⟨hsp, hspA, ?_, ?_, trivial⟩, rfl, trivial⟩, ?_⟩
  · intro vr
    have hlt := vr.isLt
    have hv := hmA0.hvregs vr
    simp only [Seg2InitA.stInitA, BTree.get_ofFn 5 _ vr.toNat hlt] at hv
    simp only [csInitClamp, stRawClamp, BTree.get_ofFn 5 _ vr.toNat hlt]
    rw [hsub _ (by simp [Seg2Base.exprVarsOk]; omega),
      hsub _ (by simp [Seg2Base.exprVarsOk]; omega)]
    exact hv
  · intro g hg31
    have hlt := g.isLt
    have hg := hmA0.hgprs g hg31
    simp only [Seg2InitA.stInitA, BTree.get_ofFn 5 _ g.toNat hlt] at hg
    simp only [csInitClamp, stRawClamp, BTree.get_ofFn 5 _ g.toNat hlt]
    rwa [hsub _ (calleeGprExpr_lt800 ⟨g.toNat, hlt⟩)]
  · have htA : evalMemTree (envClamp sp rcBase rho row s tA sampled') stRawClamp.memA = tA := by
      apply btree_ext_get; intro i hi
      simp only [evalMemTree, stRawClamp, BTree.get_map, BTree.get_ofFn 9 _ i hi]
      rw [hsub _ (headerMemAExpr_lt800 ⟨i, hi⟩)]; exact eval_headerMemAExpr hhdr i hi
    let env := envClamp sp rcBase rho row s tA sampled'
    have hB (c : Nat) (hc : c < 4) :
        (evalMemTree env stRawClamp.memB).get c = BitVec.ofNat 64 (sampled' c) := by
      simp [evalMemTree, stRawClamp, BTree.get_map, BTree.get_ofFn 9 _ c (by omega),
        hc, evalKExpr, env, envClamp, show ¬(800 + c < 800) by omega,
        show 800 + c < 804 by omega, show 800 + c - 800 = c by omega]
    dsimp only [KSpatial, csInitClamp, cfgClamp]
    rw [htA, btreeMem4_eq_multiLaneSampled4 _ (hB 0 (by decide)) (hB 1 (by decide))
      (hB 2 (by decide)) (hB 3 (by decide))]
    rfl

theorem slotHolds_congr_cfg {cfg1 cfg2 : KCfg} (hoff : cfg1.offA = cfg2.offA)
    {s : State} {tA : BTree (BitVec 64) 9} {sl : KSlot} {vLo vHi : BitVec 64} :
    slotHolds cfg1 s tA sl vLo vHi ↔ slotHolds cfg2 s tA sl vLo vHi := by
  cases sl <;> simp [slotHolds, hoff]

@[expose] def checkClampCommon (stEnd : KState) : Bool :=
  checkHeaderPreserved (fun _ => true) stEnd &&
  checkCalleeGprsPreserved (fun _ => true) stEnd &&
  (stEnd.gprs.get 1).beq (.var 66) &&
  (List.range 4).all fun c => (stEnd.memB.get c).beq (.var (810 + c))

@[expose] def checkSlotsMoved (slotsIn slotsOut : List KSlot) (stEnd : KState) : Bool :=
  (List.range 25).all fun idx =>
    let pOut := readSlot cfgClamp stEnd (slotsOut.getD idx (.vreg 0))
    let pIn  := readSlot cfgClamp stRawClamp (slotsIn.getD idx (.vreg 0))
    pOut.1.beq pIn.1 && pOut.2.beq pIn.2

theorem extract_clamp_common {sp rcBase : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s sf : State} {tA : BTree (BitVec 64) 9} {sampled' : Nat → Nat} {stEnd : KState} {F : SepProp}
    (hm : KStateMatches (envClamp sp rcBase rho row s tA sampled') stEnd sf)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hchk : checkClampCommon stEnd = true) :
    let env := envClamp sp rcBase rho row s tA sampled'
    MemAHeaderOk sp rho (evalMemTree env stEnd.memA) ∧
    RowCalleeGprs sp rcBase row sf ∧
    sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
    KSpatial cfgClamp env stEnd F =
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗
        (BTreeMem (sp + 144#64) 286 (evalMemTree env stEnd.memA) ∗
          (MultiLaneSampled (sp + 24720#64) 4 (fun c => clampSampled (sampled' c)) ∗ F))) := by
  simp only [checkClampCommon, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨hhdrC, hgprC⟩, hx1C⟩, hmemBC⟩
  let env := envClamp sp rcBase rho row s tA sampled'
  have hokTrue : ∀ e, Seg2Base.exprVarsOk (fun _ => true) e = true := by
    intro e; induction e <;> simp_all [Seg2Base.exprVarsOk]
  have hhdr' : MemAHeaderOk sp rho (evalMemTree env stEnd.memA) :=
    checked_headerOk (envFinal := env) (envSpec := env) (fun _ _ => rfl) rfl
      (by simp [env, envClamp, envInitA]) (by simp [env, envClamp, envInitA])
      (by simp [env, envClamp, envInitA]) (by simp [env, envClamp, envInitA]) hhdrC
  have hgpr' : RowCalleeGprs sp rcBase row sf :=
    checked_calleeGprs (envFinal := env) (envSpec := env) hm (fun _ _ => rfl) rfl rfl
      (by simp [env, envClamp, envInitA]) hgprC
  have hx1' : sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) := by
    have hg1 := eval_checked_gpr (ok := fun _ => true) hm (fun _ _ => rfl) 1#5 (by decide)
      (.var 66) hx1C (hokTrue _)
    simpa [Reg.x1, evalKExpr, env, envClamp, envInitA] using hg1.trans hx1
  have hB (c : Nat) (hc : c < 4) :
      (evalMemTree env stEnd.memB).get c = BitVec.ofNat 64 (clampSampled (sampled' c)) := by
    have heq := KExpr.beq_eq_true (List.all_eq_true.mp hmemBC c (List.mem_range.mpr hc))
    simp [evalMemTree, BTree.get_map, heq, evalKExpr, env, envClamp,
      show ¬(810 + c < 800) by omega, show ¬(810 + c < 804) by omega,
      show 810 ≤ 810 + c by omega, show 810 + c < 814 by omega, show 810 + c - 810 = c by omega]
  refine ⟨hhdr', hgpr', hx1', ?_⟩
  dsimp only [KSpatial, cfgClamp]
  rw [btreeMem4_eq_multiLaneSampled4 (f := fun c => clampSampled (sampled' c)) _
    (hB 0 (by decide)) (hB 1 (by decide)) (hB 2 (by decide)) (hB 3 (by decide))]
  rfl

theorem extract_slots_moved {sp rcBase : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s sf : State} {tA : BTree (BitVec 64) 9} {sampled' : Nat → Nat}
    {slotsIn slotsOut : List KSlot} {stEnd : KState} {sLo sHi : KeccakState}
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hgprs : RowCalleeGprs sp rcBase row s) (hhdr : MemAHeaderOk sp rho tA)
    (hmEnd : KStateMatches (envClamp sp rcBase rho row s tA sampled') stEnd sf)
    (hvIn : slotsIn.all (slotValid cfgClamp) = true) (hlenIn : slotsIn.length = 25)
    (hvOut : slotsOut.all (slotValid cfgClamp) = true) (hlenOut : slotsOut.length = 25)
    (hholdsIn : ∀ idx, idx < 25 →
      slotHolds cfgC s tA (slotsIn.getD idx (.vreg 0)) (sLo.getD idx 0#64) (sHi.getD idx 0#64))
    (hchk : checkSlotsMoved slotsIn slotsOut stEnd = true) :
    ∀ idx, idx < 25 →
      slotHolds cfgC sf (evalMemTree (envClamp sp rcBase rho row s tA sampled') stEnd.memA)
        (slotsOut.getD idx (.vreg 0)) (sLo.getD idx 0#64) (sHi.getD idx 0#64) := by
  let env := envClamp sp rcBase rho row s tA sampled'
  have hm0 : KStateMatches env stRawClamp s :=
    (stRawClamp_matches (sampled' := sampled') hsp hspA hgprs hhdr emp).1.1
  have hmE : KStateMatches env stEnd sf := hmEnd
  have htA0 : evalMemTree env stRawClamp.memA = tA := by
    apply btree_ext_get; intro i hi
    have hsub : ∀ e, Seg2Base.exprVarsOk (fun id => decide (id < 800)) e = true →
        evalKExpr env e = evalKExpr (envInitA sp rcBase rho row s tA) e :=
      Seg2Base.evalKExpr_congr_ok rfl rfl rfl fun id hid => by
        simp only [decide_eq_true_eq] at hid; simp [env, envClamp, hid]
    simp only [evalMemTree, stRawClamp, BTree.get_map, BTree.get_ofFn 9 _ i hi]
    rw [hsub _ (headerMemAExpr_lt800 ⟨i, hi⟩)]; exact eval_headerMemAExpr hhdr i hi
  intro idx hidx
  have hall := List.all_eq_true.mp hchk idx (List.mem_range.mpr hidx)
  simp only [Bool.and_eq_true] at hall
  have hmemIn : slotsIn.getD idx (.vreg 0) ∈ slotsIn := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hmemOut : slotsOut.getD idx (.vreg 0) ∈ slotsOut := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hrIn := readSlot_holds (List.all_eq_true.mp hvIn _ hmemIn) hm0
  rw [htA0, slotHolds_congr_cfg (cfg1 := cfgClamp) (cfg2 := cfgC) rfl] at hrIn
  rcases slotHolds_inj hrIn (hholdsIn idx hidx) with ⟨heLo, heHi⟩
  have hrOut := readSlot_holds (List.all_eq_true.mp hvOut _ hmemOut) hmE
  rw [KExpr.beq_eq_true hall.1, KExpr.beq_eq_true hall.2, heLo, heHi,
    slotHolds_congr_cfg (cfg1 := cfgClamp) (cfg2 := cfgC) rfl] at hrOut
  exact hrOut

theorem sitePreserved_row {cfg : RejSiteConfig} {sp rcBase pc : BitVec 64} {row : Nat}
    {s0 sF : State} {cfgS : KCfg} {tA : BTree (BitVec 64) 9}
    (hp : SitePreserved cfg s0 sF)
    (hsp : s0.sp = sp) (hspA : s0.spAligned = true)
    (hgprs : RowCalleeGprs sp rcBase row s0)
    (hclob : ∀ r ∈ [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .fp],
      r ∉ cfg.siteClobberedRegs) :
    let s1 := sF.setPC pc
    s1.status = .Running ∧
    s1.sp = sp ∧
    s1.spAligned = true ∧
    RowCalleeGprs sp rcBase row s1 ∧
    s1.readReg64 .x1 = s0.readReg64 .x1 ∧
    ∀ sl vLo vHi, slotHolds cfgS s0 tA sl vLo vHi → slotHolds cfgS s1 tA sl vLo vHi := by
  rcases hp with ⟨hrun, hspF, hvF, hgprF⟩
  rcases hgprs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, hfp⟩
  have hsp1 : (sF.setPC pc).sp = sp := hspF.trans hsp
  have hspA1 : (sF.setPC pc).spAligned = true := by
    unfold State.spAligned at hspA ⊢
    rwa [hsp1, ← hsp]
  have hgr (r : Reg) (hm : r ∈ [Reg.x1, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .fp]) :
      (sF.setPC pc).readReg64 r = s0.readReg64 r :=
    (by cases sF; cases r <;> rfl : (sF.setPC pc).readReg64 r = sF.readReg64 r).trans (hgprF r (hclob r hm))
  refine ⟨hrun, hsp1, hspA1,
    ⟨(hgr .x19 (by simp)).trans h19, (hgr .x20 (by simp)).trans h20,
     (hgr .x21 (by simp)).trans h21, (hgr .x22 (by simp)).trans h22,
     (hgr .x23 (by simp)).trans h23, (hgr .x24 (by simp)).trans h24,
     (hgr .x25 (by simp)).trans h25, (hgr .x26 (by simp)).trans h26,
     (hgr .x27 (by simp)).trans h27, (hgr .fp (by simp)).trans hfp⟩,
    hgr .x1 (by simp), fun sl vLo vHi hs => ?_⟩
  cases sl with
  | spillQ _ => exact hs
  | vreg vr =>
      have hv1 : (sF.setPC pc).readVReg128 (BitVec.ofNat 5 vr) = s0.readVReg128 (BitVec.ofNat 5 vr) := by
        cases sF; cases s0; simp [State.setPC, State.readVReg128] at hvF ⊢; rw [hvF]
      simpa [slotHolds, hv1] using hs

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Clamp

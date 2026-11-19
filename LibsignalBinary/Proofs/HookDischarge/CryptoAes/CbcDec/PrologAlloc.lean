/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Model
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WPp
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologFast
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologKs
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologSroa

/-!
# Aligned Init Glue: Key Schedule + SROA + `alloc_zeroed` + Backend Dispatch (`CbcDec.PrologAlloc`)

Glues `cbc_prolog_ks`, `cbc_sroa_pre_alloc`, `SepWPp.call_wpp hCal.allocZeroed_ok` on
`hSplit.base`, `cbc_panic_tail` on null return (`x0 = 0`), and `cbc_post_alloc_restore` on
non-null `outBuf ≠ 0`, delivering execution at `fnAddr + 0x1d4#64` (`b = 1#8`) or
`fnAddr + 0x67c#64` (`b ≠ 1#8`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologAlloc

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.StdStartup (decodeWords hasInstrs)
open VerifiedLibraries.RustStd (allocCallPreserved_trans)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved
   OomPreserved NullAllowed RustLayoutOk FitsEvents rustAllocEvents
   rustCliAllocBudgetSpecBase)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustHandleErrorPanicSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (PureStepPreserved)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
  (cbcPostAllocWords cbcHandleErrPreWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (Aes256DecHwAddrs Aes256CbcDecryptCallees rustAllocZeroedBudgetSpecBase)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs (CbcDecCodeSegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
  (aesDecEvents fitsAllocEvents_of_fitsAesDecEvents aesDecBudgetCondSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
  (sepWP_done_let stackAt_allocHook_split16 spAligned_sub3968
   cbcSlack cbcPost cbcPanic cbcOom savedStack96 slots56)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologFast (KeyBytes960Inv)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologKs (cbc_prolog_ks)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologSroa
  (exists_headWord_of_len8 cbc_sroa_pre_alloc cbc_post_alloc_restore)

/-! ## 1. Cold Null-Alloc Panic (`fnAddr + 0x1a0#64 -> fnAddr + 0xdf8#64 -> handleError`) -/

theorem cbc_panic_tail {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {fnAddr handleErrorAddr : BitVec 64}
    {post : State → SepProp → Prop}
    (hPostAl : hasInstrs P (fnAddr + 0x1a0#64) (decodeWords cbcPostAllocWords))
    (hPanPre : hasInstrs P (fnAddr + 0xdf8#64) (decodeWords cbcHandleErrPreWords))
    (hPanBl : hasInstrs P (fnAddr + 0xe00#64) [.bl (handleErrorAddr - (fnAddr + 0xe00#64))])
    (hHandleErr : subroutine_ok P handleErrorAddr rustHandleErrorPanicSpec)
    (x : AesCall) (st : M.σ) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64)
    (Rest R : SepProp) (s0 sf2 : State)
    (hnb : ¬ (x.input.length = 0 ∨ x.input.length % 16 ≠ 0))
    (hna : NullAllowed x.input.length 1)
    (hsp0 : s0.spAligned = true)
    (hpc2 : sf2.pc = fnAddr + 0x1a0#64) (hrun2 : sf2.status = .Running)
    (hsp2 : sf2.sp = s0.sp - 3968#64) (hx0_0 : sf2.readReg64 .x0 = 0#64)
    (hfs2 : sf2.fs = s0.fs) (htr2 : sf2.trace = s0.trace) :
    SepWPp P (s0.readReg64 .lr) sf2
      (slots56 (s0.sp - 3968#64) w0 w1 w2 w3 w4 w5 w6 ∗
        stackAt (s0.sp - 3968#64) allocHookStack ∗ Rest)
      post
      (cbcPanic A lim x st R s0)
      (cbcOom M lim x st s0) := by
  have_instrs hPostAl 0 2
  have hfp2 := ProofLib.StdStartup.hasInstrs.fetch_at_zero hPanBl
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl3968b : ((s0.sp - 3968#64) &&& 15#64 == 0#64) = true := spAligned_sub3968 hspAl0
  rw [stackAt_allocHook_split16 (s0.sp - 3968#64)]
  apply SepWPp.of_sepWP (mid := handleErrorAddr)
  dsimp only [slots56]
  wp_str64 hf_0 m1 hm1
  wp_step
  clear hf_0 hf_1
  have_instrs hPanPre 0 2
  wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun2]) fun sm_pan hsm hpc_pan hrun_pan => ?_
  have hsp_pan : sm_pan.sp = s0.sp - 3968#64 := by rw [hsm]; simp [arm64_norm, hsp2]
  have hfs_pan : sm_pan.fs = s0.fs := by rw [hsm]; simp [arm64_norm, hfs2]
  have htr_pan : sm_pan.trace = s0.trace := by rw [hsm]; simp [arm64_norm, htr2]
  clear hsm
  let sp := s0.sp - 3968#64
  let RestPan :=
    (sp ↦₆₄ w0) ∗ ((sp + 8#64) ↦₆₄ w1) ∗ ((sp + 16#64) ↦₆₄ w2) ∗
    ((sp + 24#64) ↦₆₄ w3) ∗ ((sp + 32#64) ↦₆₄ w4) ∗ ((sp + 40#64) ↦₆₄ 0#64) ∗
    ((sp + 48#64) ↦₆₄ w6) ∗ Rest
  have hsp2' : sf2.sp = sp := hsp2
  have hx0' : sf2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
  try simp only [hsp2', hx0']
  refine SepWPp.call (x := ()) (ret_pc := sm_pan.readReg64 .lr)
    (F := stackFrameAt (sp - 16#64) 4080 ∗ RestPan)
    hHandleErr hpc_pan hrun_pan
    (by simpa [State.spAligned, hsp_pan, sp] using hspAl3968b) rfl ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex) ?_
    (fun _ _ _ _ _ => by
      dsimp only [rustHandleErrorPanicSpec]; exact SepWPp.pure_elim fun h => False.elim h)
    (fun _ _ _ ho => by
      dsimp only [rustHandleErrorPanicSpec] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  · intro R' hm'
    dsimp only [rustHandleErrorPanicSpec, RestPan, sp]; rw [hsp_pan]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'
  · intro sf_pan _ hmp
    dsimp only [cbcPanic, cbcSlack, rustHandleErrorPanicSpec, aesDecBudgetCondSpec] at hmp ⊢
    have hPull :
        ((⌜sf_pan.fs = sm_pan.fs ∧ sf_pan.trace = sm_pan.trace⌝ ∗ anyHeap) ∗
          (stackFrameAt (sp - 16#64) 4080 ∗ RestPan)) ∗ (cbcSlack s0 ∗ R) =
        ⌜sf_pan.fs = sm_pan.fs ∧ sf_pan.trace = sm_pan.trace⌝ ∗
          ((anyHeap ∗ stackFrameAt (sp - 16#64) 4080 ∗ RestPan ∗ cbcSlack s0) ∗ R) := by
      sep_ac_rfl
    rw [hPull, satisfies_pure_sepConj] at hmp
    rcases hmp with ⟨⟨hfsp, htrp⟩, hrest⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hnb, hna, hfsp.trans hfs_pan, htrp.trans htr_pan⟩,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hrest⟩

/-! ## 2. Full Aligned Prolog + `alloc_zeroed` + SROA Restore (`+0x028 -> +0x1d4 | +0x67c`) -/

set_option maxHeartbeats 400000 in
theorem cbc_aligned_init {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (st : M.σ) (r0 r1 r2 w1 w2 w3 w4 w5 : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hnb : ¬ (x.input.length = 0 ∨ x.input.length % 16 ≠ 0))
    (hlt40 : x.input.length < 2 ^ 40) (hkey32 : x.key.length = 32) (hiv16 : x.iv.length = 16)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = fnAddr + 0x028#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 3968#64) (hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hx1_1 : (s1.readReg64 .x1).toNat = x.input.length)
    (hx2_1 : s1.readReg64 .x2 = x.keyA) (hx3_1 : s1.readReg64 .x3 = 32#64)
    (hx4_1 : s1.readReg64 .x4 = x.ivA) (hx5_1 : s1.readReg64 .x5 = 16#64)
    (hx8_1 : s1.readReg64 .x8 = x.ret)
    (hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) (hpure1 : PureStepPreserved s0 s1)
    (hLoop : ∀ (outBuf : BitVec 64) (b : BitVec 8) (keyBytes960 : List (BitVec 8)) (sm : State),
      let sp := s0.sp - 3968#64
      let st1 := M.stepEvents (rustAllocEvents x.input.length 1) st
      KeyBytes960Inv b x.key keyBytes960 →
      outBuf ≠ 0#64 →
      sm.pc = (if b = 1#8 then fnAddr + 0x1d4#64 else fnAddr + 0x67c#64) →
      sm.status = .Running → sm.sp = sp →
      sm.readReg64 .x9 = BitVec.ofNat 64 (x.input.length / 16) →
      sm.readReg64 .x22 = sp + 0xb40#64 →
      sm.readReg64 .x24 = sp + 0x4b0#64 →
      sm.readReg64 .x25 = BitVec.ofNat 64 x.input.length →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s0 → AllocCallPreserved s0 sm →
      SepWPp P (s0.readReg64 .lr) sm
        (slots56 sp 0#64 w1 (BitVec.ofNat 64 (x.input.length / 16))
            (BitVec.ofNat 64 x.input.length) x.ret outBuf x.inA ∗
          memRegion (sp + 0x038#64) 168 ∗
          memRegion (sp + 0x0e0#64) 8 ∗
          memRegion (sp + 0x0e8#64) 968 ∗
          memRegion (sp + 0x4b0#64) 960 ∗
          memRegion (sp + 0x870#64) 240 ∗
          memRegion (sp + 0x960#64) 240 ∗
          memRegion (sp + 0xa50#64) 240 ∗
          ((sp + 0xb40#64) ↦ₛ keyBytes960) ∗
          ((sp + 0xf00#64) ↦ₛ x.iv) ∗
          memRegion (sp + 0xf10#64) 16 ∗
          (outBuf ↦ₛ List.replicate x.input.length 0#8) ∗
          hSplit.base.live outBuf x.input.length 1 ∗
          (hw.storageAddr ↦₈ b) ∗
          hSplit.base.pool lim st1 sm ∗
          ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
          (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
          (hw.rconAddr ↦ᵣ aesRconBytes) ∗
          savedStack96 s0 ∗
          stackAt sp allocHookStack)
        (cbcPost A lim hw.rconAddr errStr1Addr errStr2Addr x st R s0)
        (cbcPanic A lim x st R s0)
        (cbcOom M lim x st s0)) :
    SepWPp P (s0.readReg64 .lr) s1
      (slots56 (s0.sp - 3968#64) 0#64 w1 w2 w3 w4 w5 x.inA ∗
        memRegion (s0.sp - 3968#64 + 56#64) 3816 ∗
        (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
        A.pool lim st s0 ∗
        stackAt (s0.sp - 3968#64) allocHookStack ∗
        ((x.ivA ↦ₛ x.iv) ∗
          ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
          (x.inA ↦ₛ x.input) ∗ savedStack96 s0))
      (cbcPost A lim hw.rconAddr errStr1Addr errStr2Addr x st R s0)
      (cbcPanic A lim x st R s0)
      (cbcOom M lim x st s0) := by
  have hpos : 0 < x.input.length := by
    rcases Nat.eq_zero_or_pos x.input.length with hz | hp
    · exact False.elim (hnb (Or.inl hz))
    · exact hp
  have hmod16 : x.input.length % 16 = 0 := by
    apply Classical.byContradiction; intro hne
    exact hnb (Or.inr hne)
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl3968 : ((s0.sp - 3968#64) &&& 15#64 == 0#64) = true := spAligned_sub3968 hspAl0
  let sp := s0.sp - 3968#64
  apply SepWPp.of_sepWP (mid := allocZeroedAddr)
  refine cbc_prolog_ks (sp := sp) A lim cs hCal x st w1 w2 w3 w4 w5
    ((x.ivA ↦ₛ x.iv) ∗
      ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
      (x.inA ↦ₛ x.input) ∗ savedStack96 s0)
    s0 s1 hpos hmod16 hlt40 hkey32 hspAl3968
    hpc1 hrun1 hsp1 hx29_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx8_1 hv1 hpure1
    fun sf_ks b keyBytes960 hinv hpc_ks hrun_ks hsp_ks hx19_ks hx20_ks hx21_ks hx24_ks hx25_ks
      hx29_ks hv_ks hpure_ks => ?_
  have hk960 : keyBytes960.length = 960 := hinv.1
  have htake8_len : (keyBytes960.take 8).length = 8 := by rw [List.length_take, hk960]; decide
  obtain ⟨headWord, hhead⟩ := exists_headWord_of_len8 htake8_len
  let SroaRest :=
    slots56 sp 0#64 w1 w2 w3 x.ret w5 x.inA ∗
      memRegion (sp + 0x038#64) 168 ∗
      memRegion (sp + 0x0e0#64) 8 ∗
      memRegion (sp + 0x870#64) 240 ∗
      memRegion (sp + 0x960#64) 240 ∗
      memRegion (sp + 0xa50#64) 240 ∗
      memRegion (sp + 0xf10#64) 16 ∗
      (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
      (hw.storageAddr ↦₈ b) ∗ hSplit.base.pool lim st sf_ks ∗
      stackAt sp allocHookStack ∗
      ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
      (x.inA ↦ₛ x.input) ∗ savedStack96 s0
  refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [SroaRest, sp]; sep_ac_rfl))
    (cbc_sroa_pre_alloc (hSplit := hSplit) cs hCal x keyBytes960 headWord SroaRest sf_ks
      hk960 hhead hiv16 hspAl3968 hpc_ks hrun_ks hsp_ks hx20_ks hx21_ks
      fun sm_al hpc_al hrun_al hsp_al hlr_al hx0_al hx1_al hx19_al hx21_al hx24_al hx25_al
        hx29_al hv_al hpure_sroa => ?_)
  refine SepWP.done hpc_al hrun_al ?_
  have hpure_s0_al : PureStepPreserved s0 sm_al := hpure_ks.trans hpure_sroa
  have hpool_al : hSplit.base.pool lim st sm_al = hSplit.base.pool lim st sf_ks :=
    hpure_sroa.pool_eq hSplit.base lim st
  let FrameAl :=
    ((sp + 0x0e8#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ∗
      memRegion (sp + 0x4b0#64) 960 ∗
      memRegion (sp + 0xb40#64) 976 ∗
      (x.ivA ↦ₛ x.iv) ∗
      slots56 sp 0#64 w1 w2 w3 x.ret w5 x.inA ∗
      memRegion (sp + 0x038#64) 168 ∗
      memRegion (sp + 0x0e0#64) 8 ∗
      memRegion (sp + 0x870#64) 240 ∗
      memRegion (sp + 0x960#64) 240 ∗
      memRegion (sp + 0xa50#64) 240 ∗
      memRegion (sp + 0xf10#64) 16 ∗
      (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
      (hw.storageAddr ↦₈ b) ∗
      ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
      (x.inA ↦ₛ x.input) ∗ savedStack96 s0
  have hx0_nat : (sm_al.readReg64 .x0).toNat = x.input.length := by
    rw [hx0_al, hx25_ks, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x.input.length < 2 ^ 64)]
  have hx1_nat : (sm_al.readReg64 .x1).toNat = 1 := by rw [hx1_al]; rfl
  have hLay : RustLayoutOk x.input.length 1 := ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  refine SepWPp.call_wpp (x := (x.input.length, 1, st)) (ret_pc := fnAddr + 0x1a0#64)
    (F := FrameAl) hCal.allocZeroed_ok hpc_al hrun_al
    (by simpa [State.spAligned, hsp_al, sp] using hspAl3968) hlr_al ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hp⟩ => by
      dsimp only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase] at hp
      exact False.elim (not_satisfies_false_sepConj hp))
    ?_ ?_
  · intro R' hm'
    dsimp only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase, FrameAl, SroaRest] at hm' ⊢
    rw [hsp_al, hpool_al, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_nat, hx1_nat, hLay⟩,
      Satisfies.mono (Entails.of_eq (by dsimp only [sp]; sep_ac_rfl)) hm'⟩
  · intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 hcs_sf2
    dsimp only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase, FrameAl]
    rw [hsp_al, sepConj_assoc]
    refine SepWPp.pure_elim fun hpres_al => ?_
    have hpres_s0_sf2 : AllocCallPreserved s0 sf2 :=
      allocCallPreserved_trans hpure_s0_al.allocCallPreserved hpres_al
    have hsp_sf2' : sf2.sp = sp := hsp_sf2.trans hsp_al
    have hx19_sf2 : sf2.readReg64 .x19 = (hw.storageAddr &&& 0xfffffffffffff000#64) :=
      hcs_sf2.readReg64_x19.trans (hx19_al.trans hx19_ks)
    have hx21_sf2 : sf2.readReg64 .x21 = headWord :=
      hcs_sf2.readReg64_x21.trans hx21_al
    have hx24_sf2 : sf2.readReg64 .x24 = sp + 0x4b0#64 :=
      hcs_sf2.readReg64_x24.trans (hx24_al.trans hx24_ks)
    have hx25_sf2 : sf2.readReg64 .x25 = BitVec.ofNat 64 x.input.length :=
      hcs_sf2.readReg64_x25.trans (hx25_al.trans hx25_ks)
    have hx29_sf2 : sf2.readReg64 .x29 = s0.sp - 96#64 :=
      hcs_sf2.readReg64_x29.trans (hx29_al.trans hx29_ks)
    have hv_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 :=
      hcs_sf2.vregs.trans (hv_al.trans hv_ks)
    by_cases hnull : sf2.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte]
      let RestNull :=
        hSplit.base.pool lim st sf2 ∗
          ((sp + 0x0e8#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ∗
          memRegion (sp + 0x4b0#64) 960 ∗
          memRegion (sp + 0xb40#64) 976 ∗
          (x.ivA ↦ₛ x.iv) ∗
          memRegion (sp + 0x038#64) 168 ∗
          memRegion (sp + 0x0e0#64) 8 ∗
          memRegion (sp + 0x870#64) 240 ∗
          memRegion (sp + 0x960#64) 240 ∗
          memRegion (sp + 0xa50#64) 240 ∗
          memRegion (sp + 0xf10#64) 16 ∗
          (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
          (hw.storageAddr ↦₈ b) ∗
          ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
          (x.inA ↦ₛ x.input) ∗ savedStack96 s0
      have hPullNull :
          (hSplit.base.pool lim st sf2 ∗ stackAt sp allocHookStack ∗
            ⌜NullAllowed x.input.length 1⌝) ∗ FrameAl =
          ⌜NullAllowed x.input.length 1⌝ ∗
            (slots56 sp 0#64 w1 w2 w3 x.ret w5 x.inA ∗ stackAt sp allocHookStack ∗ RestNull) := by
        dsimp only [FrameAl, RestNull]; sep_ac_rfl
      rw [hPullNull]
      refine SepWPp.pure_elim fun hna => ?_
      exact cbc_panic_tail A lim cs.postAlloc cs.handleErrPre cs.bl_handleErr hCal.handleError_ok
        x st 0#64 w1 w2 w3 x.ret w5 x.inA RestNull R s0 sf2 hnb hna hsp0
        hpc_sf2 hrun_sf2 hsp_sf2' hnull hpres_s0_sf2.1 hpres_s0_sf2.2.1
    · simp only [hnull, ↓reduceIte]
      let outBuf := sf2.readReg64 .x0
      let st1 := M.stepEvents (rustAllocEvents x.input.length 1) st
      have hpNe0 : outBuf ≠ 0#64 := hnull
      let RestOk :=
        memRegion (sp + 0x038#64) 168 ∗
          memRegion (sp + 0x0e0#64) 8 ∗
          memRegion (sp + 0x4b0#64) 960 ∗
          memRegion (sp + 0x870#64) 240 ∗
          memRegion (sp + 0x960#64) 240 ∗
          memRegion (sp + 0xa50#64) 240 ∗
          memRegion (sp + 0xf10#64) 16 ∗
          (outBuf ↦ₛ List.replicate x.input.length 0#8) ∗
          hSplit.base.live outBuf x.input.length 1 ∗
          hSplit.base.pool lim st1 sf2 ∗
          ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
          (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
          (hw.rconAddr ↦ᵣ aesRconBytes) ∗
          savedStack96 s0 ∗ stackAt sp allocHookStack
      have hPullOk :
          (hSplit.base.pool lim st1 sf2 ∗ stackAt sp allocHookStack ∗
            (⌜outBuf.toNat % 1 = 0⌝ ∗ hSplit.base.live outBuf x.input.length 1 ∗
              (outBuf ↦ₛ List.replicate x.input.length 0#8))) ∗ FrameAl =
          ⌜outBuf.toNat % 1 = 0⌝ ∗
            (slots56 sp 0#64 w1 w2 w3 x.ret w5 x.inA ∗
              ((sp + 0x0e8#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ∗
              memRegion (sp + 0xb40#64) 976 ∗
              (hw.storageAddr ↦₈ b) ∗ RestOk) := by
        dsimp only [FrameAl, RestOk, outBuf, st1]; sep_ac_rfl
      rw [hPullOk]
      refine SepWPp.pure_elim fun _ => ?_
      apply SepWPp.of_sepWP (mid := if b = 1#8 then fnAddr + 0x1d4#64 else fnAddr + 0x67c#64)
      refine cbc_post_alloc_restore (hSplit := hSplit) cs hCal x b keyBytes960
        headWord 0#64 w1 w2 w3 x.ret w5 RestOk sf2
        hlt40 hk960 hhead hiv16 hspAl3968 hpNe0
        hpc_sf2 hrun_sf2 hsp_sf2' rfl hx19_sf2 hx21_sf2 hx24_sf2 hx25_sf2
        fun sm_lp hpc_lp hrun_lp hsp_lp hx9_lp hx22_lp hx24_lp hx25_lp hx29_lp hv_lp hpure_lp => ?_
      refine SepWP.done hpc_lp hrun_lp ?_
      have hpool_lp : hSplit.base.pool lim st1 sm_lp = hSplit.base.pool lim st1 sf2 :=
        hpure_lp.pool_eq hSplit.base lim st1
      have hpres_lp : AllocCallPreserved s0 sm_lp :=
        allocCallPreserved_trans hpres_s0_sf2 hpure_lp.allocCallPreserved
      refine SepWPp.weaken_pre ?_
        (hLoop outBuf b keyBytes960 sm_lp hinv hpNe0 hpc_lp hrun_lp hsp_lp
          hx9_lp hx22_lp hx24_lp hx25_lp (hx29_lp.trans hx29_sf2)
          (hv_lp.trans hv_sf2) hpres_lp)
      apply Entails.of_eq
      dsimp only [RestOk, sp, st1] at hpool_lp ⊢
      rw [← hpool_lp]
      sep_ac_rfl
  · intro sf_oom R' _ ho
    dsimp only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase, cbcOom] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    rcases ho with ⟨⟨hnfit_al, hoom_al⟩, hFR⟩
    have hnfit : ¬ FitsEvents M lim st (aesDecEvents Spec.Aes256.aes256Dec x) := fun hfit =>
      hnfit_al (fitsAllocEvents_of_fitsAesDecEvents hnb hfit)
    have hpres_al0 : AllocCallPreserved s0 sm_al := hpure_s0_al.allocCallPreserved
    have hoom0 : OomPreserved s0 sf_oom :=
      ⟨hoom_al.1.trans hpres_al0.1,
       hoom_al.2.1.trans hpres_al0.2.1,
       hoom_al.2.2.trans hpres_al0.2.2.1⟩
    exact ⟨⟨hnfit, hoom0⟩, Satisfies.drop_left hFR⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologAlloc

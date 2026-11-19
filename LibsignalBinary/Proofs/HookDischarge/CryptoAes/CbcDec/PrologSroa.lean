/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Model
public import ProofLib.SepLogic.WP
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Unified SROA Staging & Post-Alloc Restore (`CbcDec.PrologSroa`)

Verifies `fnAddr + 0x140#64 -> allocZeroedAddr` and `fnAddr + 0x1a0#64 -> fnAddr + 0x1d4#64 | fnAddr + 0x67c#64`
(`0x4c9294..0x4c9324`) uniformly over `keyBytes960` (`length = 960`) and `b : BitVec 8`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologSroa

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.StdStartup (hasInstrs pageLo12)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved VmPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (PureStepPreserved)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (Aes256DecHwAddrs Aes256CbcDecryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs (CbcDecCodeSegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
  (sepWP_weaken_pre pack8LE exists_bytes16 pointsToBytes16_eq_pts64_pair sepWP_memRegion8_elim)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules.Macros
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
  (pureStepPreserved_bl step_bl_call step_bl_memcpy slots56)

/-! ## 1. Arithmetic & 8-Byte Word Helpers -/

theorem exists_headWord_of_len8 {bs : List (BitVec 8)} (h : bs.length = 8) :
    ∃ w : BitVec 64, ∀ ptr : BitVec 64, (ptr ↦ₛ bs) = (ptr ↦₆₄ w) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at h)
  exact ⟨pack8LE b0 b1 b2 b3 b4 b5 b6 b7,
    fun ptr => pointsToBytes8_eq_pointsTo64 ptr b0 b1 b2 b3 b4 b5 b6 b7⟩

theorem sp_add_0x4b0_orr_8 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    (sp + 0x4b0#64) ||| 8#64 = sp + 0x4b8#64 := by
  have h0 : sp &&& 15#64 = 0#64 := beq_iff_eq.mp h
  revert h0; bv_bits

theorem sp_add_0xb40_orr_8 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    (sp + 0xb40#64) ||| 8#64 = sp + 0xb48#64 := by
  have h0 : sp &&& 15#64 = 0#64 := beq_iff_eq.mp h
  revert h0; bv_bits

theorem lsr4_ofNat_eq (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n) >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

private theorem pageBase_add_pageLo12_eq (target : BitVec 64) :
    (target &&& 0xfffffffffffff000#64) + (pageLo12 target).signExtend 64 = target := by
  unfold pageLo12; bv_bits

private theorem step_bl_shim {P : Program} {blPc calleeAddr target_pc : BitVec 64}
    (hbl : hasInstrs P blPc [.bl (calleeAddr - blPc)])
    (hcall : subroutine_ok P calleeAddr rustAllocShimVmSpec)
    {s : State} {Full : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf Full post oom) :
    SepWP P target_pc s Full post oom := by
  let s_cal := (s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr
  exact step_bl_call hbl hcall ()
    (A := emp) (A' := emp) (F := Full)
    (φ := True) (ψ := fun sf => AllocCallPreserved s_cal sf ∧ VmPreserved s_cal sf)
    hpc hrun hsp_al
    (by dsimp only [rustAllocShimVmSpec]; simp)
    (fun sf => by dsimp only [rustAllocShimVmSpec]; exact (sepConj_emp _).symm)
    (emp_sepConj Full).symm
    trivial
    fun sf hpc' hrun' hsp' hcs ⟨ha, hv⟩ => by
      rw [emp_sepConj]
      exact hnext sf hpc' hrun' hsp' hcs (pureStepPreserved_bl ⟨ha, hv⟩)

/-! ## 2. Pre-Alloc SROA Staging (`fnAddr + 0x140#64 -> allocZeroedAddr`) -/

set_option maxHeartbeats 400000 in
theorem cbc_sroa_pre_alloc {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (keyBytes960 : List (BitVec 8)) (headWord : BitVec 64)
    (Rest : SepProp) (s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hk960 : keyBytes960.length = 960)
    (hhead : ∀ ptr : BitVec 64, (ptr ↦ₛ keyBytes960.take 8) = (ptr ↦₆₄ headWord))
    (hiv16 : x.iv.length = 16)
    (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = fnAddr + 0x140#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = x.ivA) (hx21 : s.readReg64 .x21 = 16#64)
    (hnext : ∀ sf : State,
      sf.pc = allocZeroedAddr → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .lr = fnAddr + 0x1a0#64 →
      sf.readReg64 .x0 = s.readReg64 .x25 →
      sf.readReg64 .x1 = 1#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x21 = headWord →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (((sp + 0x0e8#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ∗
         memRegion (sp + 0x4b0#64) 960 ∗
         memRegion (sp + 0xb40#64) 976 ∗
         (x.ivA ↦ₛ x.iv) ∗ Rest)
        post oom) :
    SepWP P target_pc s
      (memRegion (sp + 0x0e8#64) 968 ∗
       memRegion (sp + 0x4b0#64) 960 ∗
       ((sp + 0xb40#64) ↦ₛ keyBytes960) ∗
       memRegion (sp + 0xf00#64) 16 ∗
       (x.ivA ↦ₛ x.iv) ∗ Rest)
      post oom := by
  have htake8_len : (keyBytes960.take 8).length = 8 := by rw [List.length_take, hk960]; decide
  have hdrop8_len : (keyBytes960.drop 8).length = 952 := by rw [List.length_drop, hk960]
  have hstage_len : (keyBytes960.drop 8 ++ x.iv).length = 968 := by
    rw [List.length_append, hdrop8_len, hiv16]
  have_instrs cs.sroaCopy960 0 5
  wp_steps 5
  refine step_bl_memcpy (sp := sp) (dst := sp + 0x4b0#64) (src := sp + 0xb40#64)
    (bs := keyBytes960) cs.bl_memcpy960 hCal.memcpy_ok
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp] using hspAl)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by rw [hk960]; simp [wp_norm, arm64_norm])
    (by rw [hk960]; decide)
    (by rw [hk960]; sep_ac_rfl)
    fun s1 hpc1 hrun1 hsp1 hcs1 hpure1 => ?_
  replace hpc1 : s1.pc = fnAddr + 0x158#64 := by simpa [BitVec.add_assoc] using hpc1
  have hx20_1 : s1.readReg64 .x20 = x.ivA :=
    hcs1.readReg64_x20.trans (by simpa [wp_norm, arm64_norm] using hx20)
  have hx21_1 : s1.readReg64 .x21 = 16#64 :=
    hcs1.readReg64_x21.trans (by simpa [wp_norm, arm64_norm] using hx21)
  have hx22_1 : s1.readReg64 .x22 = sp + 0xb40#64 :=
    hcs1.readReg64_x22.trans (by simp [wp_norm, arm64_norm])
  have hx23_1 : s1.readReg64 .x23 = sp + 0x4b0#64 :=
    hcs1.readReg64_x23.trans (by simp [wp_norm, arm64_norm])
  have hsplit_4b0 : ((sp + 0x4b0#64) ↦ₛ keyBytes960) =
      ((sp + 0x4b0#64) ↦₆₄ headWord) ∗ ((sp + 0x4b8#64) ↦ₛ keyBytes960.drop 8) := by
    rw [pointsToBytes_take_drop (sp + 0x4b0#64) 8 keyBytes960 (by omega), hhead (sp + 0x4b0#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hb40_to_reg : ((sp + 0xb40#64) ↦ₛ keyBytes960) ⊢
      memRegion (sp + 0xb40#64) 952 ∗ memRegion (sp + 0xef8#64) 8 := by
    refine Entails.trans (by simpa only [hk960] using pointsToBytes_entails_memRegion (sp + 0xb40#64) keyBytes960) ?_
    rw [show (960 : Nat) = 952 + 8 from rfl, memRegion_split (sp + 0xb40#64) 952 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  refine sepWP_weaken_pre
    (Entails.trans
      (sepConj_mono_left (sepConj_mono (Entails.of_eq hsplit_4b0) hb40_to_reg))
      (Entails.of_eq (by sep_ac_rfl))) ?_
  have_instrs cs.sroaCopy952 0 6
  wp_steps 6
  refine step_bl_memcpy (sp := sp) (dst := sp + 0xb40#64) (src := sp + 0x4b8#64)
    (bs := keyBytes960.drop 8) cs.bl_memcpy952 hCal.memcpy_ok
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun1])
    (by simp [wp_norm, arm64_norm, hsp1])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp1] using hspAl)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, sp_add_0x4b0_orr_8 hspAl])
    (by rw [hdrop8_len]; simp [wp_norm, arm64_norm])
    (by rw [hdrop8_len]; decide)
    (by rw [hdrop8_len]; sep_ac_rfl)
    fun s2 hpc2 hrun2 hsp2 hcs2 hpure2 => ?_
  replace hpc2 : s2.pc = fnAddr + 0x174#64 := by simpa [BitVec.add_assoc] using hpc2
  have hx20_2 : s2.readReg64 .x20 = x.ivA :=
    hcs2.readReg64_x20.trans (by simpa [wp_norm, arm64_norm] using hx20_1)
  have hx21_2 : s2.readReg64 .x21 = headWord :=
    hcs2.readReg64_x21.trans (by simp [wp_norm, arm64_norm])
  have hx22_2 : s2.readReg64 .x22 = sp + 0xb40#64 :=
    hcs2.readReg64_x22.trans (by simpa [wp_norm, arm64_norm] using hx22_1)
  obtain ⟨iv0, iv1, iv2, iv3, iv4, iv5, iv6, iv7, iv8, iv9, iv10, iv11, iv12, iv13, iv14, iv15, hiv_eq⟩ :=
    exists_bytes16 hiv16
  have hiv_pts := pointsToBytes16_eq_pts64_pair x.ivA iv0 iv1 iv2 iv3 iv4 iv5 iv6 iv7
    iv8 iv9 iv10 iv11 iv12 iv13 iv14 iv15
  have hef8_split : memRegion (sp + 0xef8#64) 8 ∗ memRegion (sp + 0xf00#64) 16 =
      memRegion (sp + 0xef8#64) 8 ∗ memRegion (sp + 0xf00#64) 8 ∗ memRegion (sp + 0xf08#64) 8 := by
    rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split (sp + 0xf00#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine sepWP_weaken_pre
    (Entails.of_eq (show _ = memRegion (sp + 0xef8#64) 8 ∗ (memRegion (sp + 0xf00#64) 8 ∗
      (((x.ivA ↦₆₄ pack8LE iv0 iv1 iv2 iv3 iv4 iv5 iv6 iv7) ∗
        ((x.ivA + 8#64) ↦₆₄ pack8LE iv8 iv9 iv10 iv11 iv12 iv13 iv14 iv15)) ∗
       ((sp + 0xb40#64) ↦ₛ keyBytes960.drop 8) ∗ memRegion (sp + 0x0e8#64) 968 ∗
       ((sp + 0x4b0#64) ↦₆₄ headWord) ∗ ((sp + 0x4b8#64) ↦ₛ keyBytes960.drop 8) ∗
       memRegion (sp + 0xf08#64) 8 ∗ Rest)) by
      rw [hiv_eq, hiv_pts, ← sepConj_assoc (memRegion (sp + 0xef8#64) 8) (memRegion (sp + 0xf00#64) 16),
          hef8_split]
      sep_ac_rfl)) ?_
  refine sepWP_memRegion8_elim fun u0 => ?_
  rw [sepConj_left_comm ((sp + 0xef8#64) ↦₆₄ u0)]
  refine sepWP_memRegion8_elim fun u1 => ?_
  have_instrs cs.sroaStage968 0 6
  wp_steps 5
  wp_str128 hf_5 m1 hm1
  have hcomb_968 :
      ((sp + 0xb40#64) ↦ₛ keyBytes960.drop 8) ∗
        ((sp + 0xef8#64) ↦₆₄ pack8LE iv0 iv1 iv2 iv3 iv4 iv5 iv6 iv7) ∗
        ((sp + 0xf00#64) ↦₆₄ pack8LE iv8 iv9 iv10 iv11 iv12 iv13 iv14 iv15) =
      ((sp + 0xb40#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) := by
    have hpair := pointsToBytes16_eq_pts64_pair (sp + 0xef8#64) iv0 iv1 iv2 iv3 iv4 iv5 iv6 iv7
      iv8 iv9 iv10 iv11 iv12 iv13 iv14 iv15
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpair
    rw [pointsToBytes_append, hdrop8_len, show sp + 0xb40#64 + BitVec.ofNat 64 952 = sp + 0xef8#64 from by bv_lin,
        hiv_eq, hpair]
  refine step_bl_memcpy (sp := sp) (dst := sp + 0x0e8#64) (src := sp + 0xb40#64)
    (bs := keyBytes960.drop 8 ++ x.iv) cs.bl_memcpyStage968 hCal.memcpy_ok
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun2])
    (by simp [wp_norm, arm64_norm, hsp2])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp2] using hspAl)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm])
    (by rw [hstage_len]; simp [wp_norm, arm64_norm])
    (by rw [hstage_len]; decide)
    (by
      rw [hstage_len]
      simp only [wp_norm, arm64_norm]
      rw [← hcomb_968]
      sep_ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 hpure3 => ?_
  refine step_bl_shim cs.bl_shim hCal.shim_ok (by simpa [BitVec.add_assoc] using hpc3) hrun3
    (by simpa [State.spAligned, hsp3] using hspAl)
    fun s4 hpc4 hrun4 hsp4 hcs4 hpure4 => ?_
  replace hpc4 : s4.pc = fnAddr + 0x194#64 := by simpa [BitVec.add_assoc] using hpc4
  have_instrs cs.preAlloc 0 2
  have hf_blAl := ProofLib.StdStartup.hasInstrs.fetch_at_zero cs.bl_alloc
  wp_steps 3
  have hfold_4b0 :
      ((sp + 0x4b0#64) ↦₆₄ headWord) ∗ ((sp + 0x4b8#64) ↦ₛ keyBytes960.drop 8) ⊢
        memRegion (sp + 0x4b0#64) 960 := by
    rw [← hsplit_4b0]
    simpa only [hk960] using pointsToBytes_entails_memRegion (sp + 0x4b0#64) keyBytes960
  have hfold_b40 :
      ((sp + 0xb40#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ∗ memRegion (sp + 0xf08#64) 8 ⊢
        memRegion (sp + 0xb40#64) 976 := by
    rw [show (976 : Nat) = 968 + 8 from rfl, memRegion_split (sp + 0xb40#64) 968 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left
      (by simpa only [hstage_len] using
        pointsToBytes_entails_memRegion (sp + 0xb40#64) (keyBytes960.drop 8 ++ x.iv))
  refine sepWP_weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        ((sp + 0x0e8#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ∗
        (((sp + 0x4b0#64) ↦₆₄ headWord) ∗ ((sp + 0x4b8#64) ↦ₛ keyBytes960.drop 8)) ∗
        (((sp + 0xb40#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ∗ memRegion (sp + 0xf08#64) 8) ∗
        (x.ivA ↦ₛ x.iv) ∗ Rest by
        rw [hiv_eq, hiv_pts]; sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono hfold_4b0 (sepConj_mono_left hfold_b40)))) ?_
  have hx19_2 : s2.readReg64 .x19 = s.readReg64 .x19 :=
    hcs2.readReg64_x19.trans (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x19)
  have hx19_4 : s4.readReg64 .x19 = s.readReg64 .x19 :=
    hcs4.readReg64_x19.trans (hcs3.readReg64_x19.trans (by simpa [wp_norm, arm64_norm] using hx19_2))
  have hx21_4 : s4.readReg64 .x21 = headWord :=
    hcs4.readReg64_x21.trans (hcs3.readReg64_x21.trans (by simpa [wp_norm, arm64_norm] using hx21_2))
  have hx24_2 : s2.readReg64 .x24 = s.readReg64 .x24 :=
    hcs2.readReg64_x24.trans (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x24)
  have hx24_4 : s4.readReg64 .x24 = s.readReg64 .x24 :=
    hcs4.readReg64_x24.trans (hcs3.readReg64_x24.trans (by simpa [wp_norm, arm64_norm] using hx24_2))
  have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 :=
    hcs2.readReg64_x25.trans (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x25)
  have hx25_4 : s4.readReg64 .x25 = s.readReg64 .x25 :=
    hcs4.readReg64_x25.trans (hcs3.readReg64_x25.trans (by simpa [wp_norm, arm64_norm] using hx25_2))
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 :=
    hcs2.readReg64_x29.trans (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x29)
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 :=
    hcs4.readReg64_x29.trans (hcs3.readReg64_x29.trans (by simpa [wp_norm, arm64_norm] using hx29_2))
  have hv_2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
    hcs2.vregs.trans (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hcs1.vregs)
  have hv_4 : calleeSavedVRegs s4 = calleeSavedVRegs s :=
    hcs4.vregs.trans (hcs3.vregs.trans (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv_2))
  have hpure_s_4 : PureStepPreserved s s4 :=
    ((((PureStepPreserved.of_proj_perm rfl rfl).trans hpure1).trans
      ((PureStepPreserved.of_proj_perm rfl rfl).trans hpure2)).trans
      ((PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simpa [wp_norm, arm64_norm] using hm1)).trans hpure3)).trans hpure4
  exact hnext _
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun4])
    (by simp [wp_norm, arm64_norm, hsp4, hsp3])
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hx25_4])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hx19_4])
    (by simp [wp_norm, arm64_norm, hx21_4])
    (by simp [wp_norm, arm64_norm, hx24_4])
    (by simp [wp_norm, arm64_norm, hx25_4])
    (by simp [wp_norm, arm64_norm, hx29_4])
    (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv_4)
    (hpure_s_4.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl))

/-! ## 3. Non-Null SROA Restore & Backend Dispatch (`fnAddr + 0x1a0#64 -> +0x1d4 / +0x67c`) -/

set_option maxHeartbeats 400000 in
theorem cbc_post_alloc_restore {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp outBuf : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (b : BitVec 8) (keyBytes960 : List (BitVec 8))
    (headWord w0 w1 w2 w3 w4 w5 : BitVec 64)
    (Rest : SepProp) (s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlt40 : x.input.length < 2 ^ 40)
    (hk960 : keyBytes960.length = 960)
    (hhead : ∀ ptr : BitVec 64, (ptr ↦ₛ keyBytes960.take 8) = (ptr ↦₆₄ headWord))
    (hiv16 : x.iv.length = 16)
    (hspAl : (sp &&& 15#64 == 0#64) = true)
    (houtNe0 : outBuf ≠ 0#64)
    (hpc : s.pc = fnAddr + 0x1a0#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = outBuf)
    (hx19 : s.readReg64 .x19 = (hw.storageAddr &&& 0xfffffffffffff000#64))
    (hx21 : s.readReg64 .x21 = headWord)
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.input.length)
    (hnext : ∀ sf : State,
      sf.pc = (if b = 1#8 then fnAddr + 0x1d4#64 else fnAddr + 0x67c#64) →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x9 = BitVec.ofNat 64 (x.input.length / 16) →
      sf.readReg64 .x22 = sp + 0xb40#64 →
      sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x25 = BitVec.ofNat 64 x.input.length →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      PureStepPreserved s sf →
      SepWP P target_pc sf
        (slots56 sp w0 w1 (BitVec.ofNat 64 (x.input.length / 16))
           (BitVec.ofNat 64 x.input.length) w4 outBuf x.inA ∗
         memRegion (sp + 0x0e8#64) 968 ∗
         ((sp + 0xb40#64) ↦ₛ keyBytes960) ∗
         ((sp + 0xf00#64) ↦ₛ x.iv) ∗
         (hw.storageAddr ↦₈ b) ∗ Rest)
        post oom) :
    SepWP P target_pc s
      (slots56 sp w0 w1 w2 w3 w4 w5 x.inA ∗
       ((sp + 0x0e8#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ∗
       memRegion (sp + 0xb40#64) 976 ∗
       (hw.storageAddr ↦₈ b) ∗ Rest)
      post oom := by
  have hstage_len : (keyBytes960.drop 8 ++ x.iv).length = 968 := by
    rw [List.length_append, List.length_drop, hk960, hiv16]
  have hb40_split : memRegion (sp + 0xb40#64) 976 =
      memRegion (sp + 0xb40#64) 8 ∗ memRegion (sp + 0xb48#64) 968 := by
    rw [show (976 : Nat) = 8 + 968 from rfl, memRegion_split (sp + 0xb40#64) 8 968 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine sepWP_weaken_pre
    (Entails.of_eq (show _ = memRegion (sp + 0xb40#64) 8 ∗
      (slots56 sp w0 w1 w2 w3 w4 w5 x.inA ∗
       ((sp + 0x0e8#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ∗
       memRegion (sp + 0xb48#64) 968 ∗ (hw.storageAddr ↦₈ b) ∗ Rest) by
      rw [hb40_split]; sep_ac_rfl)) ?_
  refine sepWP_memRegion8_elim fun oldHead => ?_
  have houtBeq : (outBuf == 0#64) = false := beq_false_of_ne houtNe0
  have_instrs cs.postAlloc 0 7
  dsimp only [slots56]
  wp_str64 hf_0 m1 hm1
  wp_steps 5
  wp_str64 hf_6 m2 hm2
  refine step_bl_memcpy (sp := sp) (dst := sp + 0xb48#64) (src := sp + 0x0e8#64)
    (bs := keyBytes960.drop 8 ++ x.iv) cs.bl_memcpyUnstage hCal.memcpy_ok
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp] using hspAl)
    (by simp [wp_norm, arm64_norm, sp_add_0xb40_orr_8 hspAl])
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by rw [hstage_len]; simp [wp_norm, arm64_norm])
    (by rw [hstage_len]; decide)
    (by rw [hstage_len]; sep_ac_rfl)
    fun s1 hpc1 hrun1 hsp1 hcs1 hpure1 => ?_
  have hx19_1 : s1.readReg64 .x19 = (hw.storageAddr &&& 0xfffffffffffff000#64) :=
    hcs1.readReg64_x19.trans (by simpa [wp_norm, arm64_norm] using hx19)
  have hx22_1 : s1.readReg64 .x22 = sp + 0xb40#64 :=
    hcs1.readReg64_x22.trans (by simp [wp_norm, arm64_norm])
  have hx24_1 : s1.readReg64 .x24 = sp + 0x4b0#64 :=
    hcs1.readReg64_x24.trans (by simpa [wp_norm, arm64_norm] using hx24)
  have hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 x.input.length :=
    hcs1.readReg64_x25.trans (by simpa [wp_norm, arm64_norm] using hx25)
  have hf_ldrb1 := ProofLib.StdStartup.hasInstrs.fetch_at_zero cs.ldrbStorage1
  have_instrs cs.loopDispatch 0 4
  have hpc1' : s1.pc = fnAddr + 0x1c0#64 := by simpa [BitVec.add_assoc] using hpc1
  refine SepWP.step_ldr8 (ea := hw.storageAddr) (wb := none)
    (hpc := hpc1') (hrun := hrun1) (hfetch := hf_ldrb1) (hsp := rfl)
    (haddr := by
      simp only [evalAddrMode, hx19_1, wp_norm, arm64_norm]
      try exact ⟨pageBase_add_pageLo12_eq _, rfl⟩)
    (hload := SepLoad8.of_eq (by sep_ac_rfl)) (hexec := rfl) ?_
  simp only [wp_norm, arm64_norm]
  wp_steps 2
  wp_stp64 hf_2 m3 hm3
  have hrecomb :
      ((sp + 0xb40#64) ↦₆₄ headWord) ∗ ((sp + 0xb48#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) =
      ((sp + 0xb40#64) ↦ₛ keyBytes960) ∗ ((sp + 0xf00#64) ↦ₛ x.iv) := by
    have h1 : ((sp + 0xb40#64) ↦ₛ (keyBytes960 ++ x.iv)) =
        ((sp + 0xb40#64) ↦ₛ keyBytes960) ∗ ((sp + 0xf00#64) ↦ₛ x.iv) := by
      rw [pointsToBytes_append, hk960]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have h2 : ((sp + 0xb40#64) ↦ₛ (keyBytes960.take 8 ++ (keyBytes960.drop 8 ++ x.iv))) =
        ((sp + 0xb40#64) ↦₆₄ headWord) ∗ ((sp + 0xb48#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) := by
      rw [pointsToBytes_append,
          show (keyBytes960.take 8).length = 8 by rw [List.length_take, hk960]; decide,
          hhead (sp + 0xb40#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [← h2, ← List.append_assoc, List.take_append_drop, h1]
  have hdrop_0e8 :
      ((sp + 0x0e8#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ⊢ memRegion (sp + 0x0e8#64) 968 := by
    simpa only [hstage_len] using
      pointsToBytes_entails_memRegion (sp + 0x0e8#64) (keyBytes960.drop 8 ++ x.iv)
  have hlsr : (BitVec.ofNat 64 x.input.length) >>> 4 = BitVec.ofNat 64 (x.input.length / 16) :=
    lsr4_ofNat_eq x.input.length (by omega)
  have hpure_s_1 : PureStepPreserved s s1 :=
    (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm] at hm1 hm2 ⊢; exact hm2.trans hm1)).trans hpure1
  wp_step; wp_if hbne
  · have hb_ne1 : b ≠ 1#8 := fun h => hbne (by subst h; rfl)
    refine sepWP_weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          (((sp + 0xb40#64) ↦₆₄ headWord) ∗ ((sp + 0xb48#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv))) ∗
          ((sp + 0x0e8#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ∗
          (slots56 sp w0 w1 (BitVec.ofNat 64 (x.input.length / 16))
             (BitVec.ofNat 64 x.input.length) w4 outBuf x.inA ∗
           (hw.storageAddr ↦₈ b) ∗ Rest) by
          dsimp only [slots56]
          simp only [wp_norm, arm64_norm, hlsr]
          sep_ac_rfl))
        (Entails.trans (sepConj_mono (Entails.of_eq hrecomb) (sepConj_mono_left hdrop_0e8))
          (Entails.of_eq (by sep_ac_rfl))))
      (hnext _
        (by simp [hb_ne1, wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun1])
        (by simp [wp_norm, arm64_norm, hsp1])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx22_1])
        (by simp [wp_norm, arm64_norm, hx24_1])
        (by simp [wp_norm, arm64_norm, hx25_1])
        (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x29)
        (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hcs1.vregs)
        (hpure_s_1.trans (PureStepPreserved.of_proj_perm
          (by simp [wp_norm, arm64_norm])
          (by simpa [wp_norm, arm64_norm] using hm3))))
  · have hb_eq1 : b = 1#8 := by
      simpa using congrArg (BitVec.truncate 8) hbne
    subst hb_eq1
    refine sepWP_weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          (((sp + 0xb40#64) ↦₆₄ headWord) ∗ ((sp + 0xb48#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv))) ∗
          ((sp + 0x0e8#64) ↦ₛ (keyBytes960.drop 8 ++ x.iv)) ∗
          (slots56 sp w0 w1 (BitVec.ofNat 64 (x.input.length / 16))
             (BitVec.ofNat 64 x.input.length) w4 outBuf x.inA ∗
           (hw.storageAddr ↦₈ 1#8) ∗ Rest) by
          dsimp only [slots56]
          simp only [wp_norm, arm64_norm, hlsr]
          sep_ac_rfl))
        (Entails.trans (sepConj_mono (Entails.of_eq hrecomb) (sepConj_mono_left hdrop_0e8))
          (Entails.of_eq (by sep_ac_rfl))))
      (hnext _
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun1])
        (by simp [wp_norm, arm64_norm, hsp1])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx22_1])
        (by simp [wp_norm, arm64_norm, hx24_1])
        (by simp [wp_norm, arm64_norm, hx25_1])
        (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x29)
        (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hcs1.vregs)
        (hpure_s_1.trans (PureStepPreserved.of_proj_perm
          (by simp [wp_norm, arm64_norm])
          (by simpa [wp_norm, arm64_norm] using hm3))))

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologSroa

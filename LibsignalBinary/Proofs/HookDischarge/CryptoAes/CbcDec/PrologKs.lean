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
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologFast
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Aligned Prologue & Dual-Backend Key-Schedule Dispatch (`CbcDec.PrologKs`)

Verifies `fnAddr + 0x028#64 -> fnAddr + 0x140#64` (`0x4c917c..0x4c9294`) on aligned non-empty
inputs (`0 < x.input.length`, `x.input.length % 16 = 0`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologKs

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.StdStartup (adrpOff)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (aes256KeyScheduleFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved fsKeys256Bytes fsKeys256Bytes_length fsKeys256At_eq_pointsToBytes)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (aesRconBytes armv8ExpandKey armv8InvExpandedKeys roundKeys15Bytes roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
  (PoolAesInitSplit step_bl_aesInitInner_allocStack)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (roundKeys15Bytes_length roundKeys15At_eq_pointsToBytes
   roundKeys15At_entails_memRegion memRegion240_eq_exists_roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (Aes256DecHwAddrs Aes256CbcDecryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs (CbcDecCodeSegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules (sepWP_weaken_pre)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
  (step_bl_memcpy stackAt_allocHook_split256 stackAt_allocHook_split1120 slots56)

private theorem adrp_val_eq (pc target : BitVec 64) :
    (pc &&& 0xfffffffffffff000#64) + adrpOff pc target =
      target &&& 0xfffffffffffff000#64 := by
  unfold adrpOff; bv_bits

private theorem sepWP_bind_state {P : Program} {target_pc : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ s' : State, s' = s → SepWP P target_pc s' Pre post oom) :
    SepWP P target_pc s Pre post oom := h s rfl
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologFast
  (localWork3816_split KeyBytes960Inv bv64_and15_eq_zero_iff
   step_bl_keySchedule step_bl_expandKey15 step_bl_invExpand15 cbc_hw_copy_ek)

/-! ## 1. `Fixslice64` & Hardware Key-Schedule Branches (`+0x068 / +0x0a4 -> +0x140`) -/

private theorem cbc_soft_ks_branch {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (b : BitVec 8) (Rest : SepProp) (s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hb : b ≠ 1#8) (hkey32 : x.key.length = 32)
    (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = fnAddr + 0x068#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx2 : s.readReg64 .x2 = x.keyA)
    (hnext : ∀ (sf : State) (keyBytes960 : List (BitVec 8)),
      KeyBytes960Inv b x.key keyBytes960 →
      sf.pc = fnAddr + 0x140#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s → PureStepPreserved s sf →
      SepWP P target_pc sf
        (((sp + 0xb40#64) ↦ₛ keyBytes960) ∗
         memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240 ∗
         memRegion (sp + 0xa50#64) 240 ∗ (x.keyA ↦ₛ x.key) ∗
         (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ Rest)
        post oom) :
    SepWP P target_pc s
      (memRegion (sp + 0xb40#64) 960 ∗
       memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240 ∗
       memRegion (sp + 0xa50#64) 240 ∗ (x.keyA ↦ₛ x.key) ∗
       (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ Rest)
      post oom := by
  have_instrs cs.storageCheck 7 2
  have_instrs cs.postSoftKs 0 1
  wp_steps 2
  rw [stackAt_allocHook_split1120 sp]
  refine step_bl_keySchedule sp (sp + 0xb40#64) x.keyA cs.bl_ks hCal.keySchedule_ok
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp] using hspAl)
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    hkey32
    (by sep_ac_rfl)
    fun sf1 hpc1 hrun1 hsp1 hcs1 hpure1 => ?_
  wp_step
  have hinv : KeyBytes960Inv b x.key (fsKeys256Bytes (aes256KeyScheduleFs x.key)) :=
    ⟨fsKeys256Bytes_length _, by simp only [hb, ↓reduceIte]⟩
  refine sepWP_weaken_pre
    (Entails.of_eq (by
      rw [stackAt_allocHook_split1120 sp, fsKeys256At_eq_pointsToBytes]
      sep_ac_rfl))
    (hnext _ _ hinv
      (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun1])
      (by simp [wp_norm, arm64_norm, hsp1])
      (by simp [wp_norm, arm64_norm, hcs1.readReg64_x19])
      (by simp [wp_norm, arm64_norm, hcs1.readReg64_x20])
      (by simp [wp_norm, arm64_norm, hcs1.readReg64_x21])
      (by simp [wp_norm, arm64_norm, hcs1.readReg64_x24])
      (by simp [wp_norm, arm64_norm, hcs1.readReg64_x25])
      (by simp [wp_norm, arm64_norm, hcs1.readReg64_x29])
      (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hcs1.vregs)
      ((PureStepPreserved.of_proj_perm rfl rfl).trans
        (hpure1.trans (PureStepPreserved.of_proj_perm rfl rfl))))

private theorem cbc_hw_ks_branch {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (Rest : SepProp) (s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hkey32 : x.key.length = 32)
    (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = fnAddr + 0x0a4#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx2 : s.readReg64 .x2 = x.keyA) (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hnext : ∀ (sf : State) (keyBytes960 : List (BitVec 8)),
      KeyBytes960Inv 1#8 x.key keyBytes960 →
      sf.pc = fnAddr + 0x140#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s → PureStepPreserved s sf →
      SepWP P target_pc sf
        (((sp + 0xb40#64) ↦ₛ keyBytes960) ∗
         memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240 ∗
         memRegion (sp + 0xa50#64) 240 ∗ (x.keyA ↦ₛ x.key) ∗
         (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ Rest)
        post oom) :
    SepWP P target_pc s
      (memRegion (sp + 0xb40#64) 960 ∗
       memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240 ∗
       memRegion (sp + 0xa50#64) 240 ∗ (x.keyA ↦ₛ x.key) ∗
       (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ Rest)
      post oom := by
  have_instrs cs.postInit 2 2
  wp_steps 2
  rw [stackAt_allocHook_split256 sp]
  refine step_bl_expandKey15 sp (sp + 0xa50#64) x.keyA cs.bl_expandKey hCal.expandKey_ok
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp] using hspAl)
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    hkey32
    (by sep_ac_rfl)
    fun s1 hpc1 hrun1 hsp1 hcs1 hpure1 => ?_
  rw [show (roundKeys15At (sp + 0xa50#64) (armv8ExpandKey x.key) ∗ (x.keyA ↦ₛ x.key) ∗
        (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackFrameAt sp 0x100) ∗
        (memRegion (sp + 0xb40#64) 960 ∗ memRegion (sp + 0x870#64) 240 ∗
         memRegion (sp + 0x960#64) 240 ∗ stackFrameAt (sp - 256#64) 3840 ∗ Rest) =
      memRegion (sp + 0x960#64) 240 ∗ roundKeys15At (sp + 0xa50#64) (armv8ExpandKey x.key) ∗
        (memRegion (sp + 0xb40#64) 960 ∗ memRegion (sp + 0x870#64) 240 ∗ (x.keyA ↦ₛ x.key) ∗
         (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ Rest) by
    rw [stackAt_allocHook_split256 sp]; sep_ac_rfl]
  have_instrs cs.preInvExpand 0 3
  wp_steps 3
  refine step_bl_invExpand15 sp (sp + 0x960#64) (sp + 0xa50#64) cs.bl_invExpand hCal.invExpand_ok
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun1])
    (by simp [wp_norm, arm64_norm, hsp1])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp1] using hspAl)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by sep_ac_rfl)
    fun s2 hpc2 hrun2 hsp2 hcs2 hpure2 => ?_
  have hx24_2 : s2.readReg64 .x24 = sp + 0x4b0#64 :=
    hcs2.readReg64_x24.trans (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x24.trans (by simpa [wp_norm, arm64_norm] using hx24))
  refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (cbc_hw_copy_ek cs.hwCopyEk (armv8ExpandKey x.key) _ s2
      (by simpa [BitVec.add_assoc] using hpc2) hrun2 hsp2 hspAl hx24_2
      fun s3 hpc3 hrun3 hsp3 hx0_3 hx1_3 hx2_3 hx19_3 hx20_3 hx21_3 hx24_3 hx25_3 hx29_3 hv3 hpure3 => ?_)
  let ek := armv8ExpandKey x.key
  let dk := armv8InvExpandedKeys ek
  let pair480 := roundKeys15Bytes ek ++ roundKeys15Bytes dk
  have hp480_len : pair480.length = 480 := by
    simp [pair480, roundKeys15Bytes_length]
  have hsrc480 :
      roundKeys15At (sp + 0x870#64) ek ∗ roundKeys15At (sp + 0x960#64) dk =
        ((sp + 0x870#64) ↦ₛ pair480) := by
    rw [roundKeys15At_eq_pointsToBytes, roundKeys15At_eq_pointsToBytes,
        show pair480 = roundKeys15Bytes ek ++ roundKeys15Bytes dk from rfl,
        pointsToBytes_append, roundKeys15Bytes_length]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hsplit960 : memRegion (sp + 0xb40#64) 960 =
      memRegion (sp + 0xb40#64) 480 ∗
      memRegion (sp + 0xd20#64) 240 ∗ memRegion (sp + 0xe10#64) 240 := by
    have h1 := memRegion_split (sp + 0xb40#64) 480 480 (by decide)
    have h2 := memRegion_split (sp + 0xd20#64) 240 240 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2
    rw [show (960 : Nat) = 480 + 480 from rfl, h1, show (480 : Nat) = 240 + 240 from rfl, h2]
  refine sepWP_weaken_pre
    (Entails.of_eq (show _ = memRegion (sp + 0xd20#64) 240 ∗ (memRegion (sp + 0xe10#64) 240 ∗
      (memRegion (sp + 0xb40#64) 480 ∗ ((sp + 0x870#64) ↦ₛ pair480) ∗
       roundKeys15At (sp + 0xa50#64) ek ∗ (x.keyA ↦ₛ x.key) ∗
       (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ Rest)) by
      rw [hsplit960, ← hsrc480]; dsimp only [ek, dk]; sep_ac_rfl)) ?_
  rw [memRegion240_eq_exists_roundKeys15At (sp + 0xd20#64), sepExists_sepConj_left]
  apply SepWP.exists_elim; intro t1
  rw [sepConj_left_comm (roundKeys15At (sp + 0xd20#64) t1),
      memRegion240_eq_exists_roundKeys15At (sp + 0xe10#64), sepExists_sepConj_left]
  apply SepWP.exists_elim; intro t2
  refine step_bl_memcpy (bs := pair480) cs.bl_memcpy480 hCal.memcpy_ok hpc3 hrun3 hsp3
    (by simpa [State.spAligned, hsp3] using hspAl)
    hx0_3 hx1_3 (by rw [hx2_3, hp480_len]) (by rw [hp480_len]; decide)
    (by rw [hp480_len]; sep_ac_rfl)
    fun sf hpc4 hrun4 hsp4 hcs4 hpure4 => ?_
  let tail480 := roundKeys15Bytes t1 ++ roundKeys15Bytes t2
  let keyBytes960 := pair480 ++ tail480
  have ht480_len : tail480.length = 480 := by simp [tail480, roundKeys15Bytes_length]
  have hinv : KeyBytes960Inv 1#8 x.key keyBytes960 :=
    ⟨by simp [keyBytes960, hp480_len, ht480_len],
     by simp only [↓reduceIte]; exact ⟨roundKeys15Bytes ek, tail480, roundKeys15Bytes_length ek, ht480_len, rfl⟩⟩
  have hpack_dst :
      ((sp + 0xb40#64) ↦ₛ pair480) ∗ roundKeys15At (sp + 0xd20#64) t1 ∗
        roundKeys15At (sp + 0xe10#64) t2 =
      ((sp + 0xb40#64) ↦ₛ keyBytes960) := by
    have h1 := pointsToBytes_append (sp + 0xd20#64) (roundKeys15Bytes t1) (roundKeys15Bytes t2)
    have h2 := pointsToBytes_append (sp + 0xb40#64) pair480 (roundKeys15Bytes t1 ++ roundKeys15Bytes t2)
    rw [roundKeys15Bytes_length] at h1
    rw [hp480_len] at h2
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2
    rw [roundKeys15At_eq_pointsToBytes, roundKeys15At_eq_pointsToBytes, ← h1, ← h2]
  have hdrop_src :
      ((sp + 0x870#64) ↦ₛ pair480) ∗ roundKeys15At (sp + 0xa50#64) ek ⊢
        memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240 ∗
        memRegion (sp + 0xa50#64) 240 := by
    rw [← hsrc480, ← sepConj_assoc]
    exact sepConj_mono
      (sepConj_mono (roundKeys15At_entails_memRegion _ _) (roundKeys15At_entails_memRegion _ _))
      (roundKeys15At_entails_memRegion _ _)
  refine sepWP_weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (((sp + 0xb40#64) ↦ₛ pair480) ∗ roundKeys15At (sp + 0xd20#64) t1 ∗
          roundKeys15At (sp + 0xe10#64) t2) ∗
        (((sp + 0x870#64) ↦ₛ pair480) ∗ roundKeys15At (sp + 0xa50#64) ek) ∗
        ((x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ Rest) by
        dsimp only [ek]; sep_ac_rfl))
      (Entails.trans
        (sepConj_mono (Entails.of_eq hpack_dst) (sepConj_mono_left hdrop_src))
        (Entails.of_eq (by sep_ac_rfl))))
    (hnext sf keyBytes960 hinv (by simpa [BitVec.add_assoc] using hpc4) hrun4 hsp4
      (hcs4.readReg64_x19.trans (hx19_3.trans (hcs2.readReg64_x19.trans (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x19))))
      (hcs4.readReg64_x20.trans (hx20_3.trans (hcs2.readReg64_x20.trans (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x20))))
      (hcs4.readReg64_x21.trans (hx21_3.trans (hcs2.readReg64_x21.trans (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x21))))
      (hcs4.readReg64_x24.trans hx24_3)
      (hcs4.readReg64_x25.trans (hx25_3.trans (hcs2.readReg64_x25.trans (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x25))))
      (hcs4.readReg64_x29.trans (hx29_3.trans (hcs2.readReg64_x29.trans (by simpa [wp_norm, arm64_norm] using hcs1.readReg64_x29))))
      (hcs4.vregs.trans (hv3.trans (hcs2.vregs.trans (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hcs1.vregs))))
      ((((PureStepPreserved.of_proj_perm rfl rfl).trans hpure1).trans
        ((PureStepPreserved.of_proj_perm rfl rfl).trans hpure2)).trans
        (hpure3.trans hpure4)))

private theorem cbc_init_ks_branch {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (b0 : BitVec 8) (st : M.σ) (Rest : SepProp) (s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hkey32 : x.key.length = 32)
    (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = fnAddr + 0x094#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx2 : s.readReg64 .x2 = x.keyA) (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hnext : ∀ (sf : State) (b : BitVec 8) (keyBytes960 : List (BitVec 8)),
      KeyBytes960Inv b x.key keyBytes960 →
      sf.pc = fnAddr + 0x140#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s → PureStepPreserved s sf →
      SepWP P target_pc sf
        ((hw.storageAddr ↦₈ b) ∗ hSplit.base.pool lim st sf ∗
         ((sp + 0xb40#64) ↦ₛ keyBytes960) ∗
         memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240 ∗
         memRegion (sp + 0xa50#64) 240 ∗ (x.keyA ↦ₛ x.key) ∗
         (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ Rest)
        post oom) :
    SepWP P target_pc s
      ((hw.storageAddr ↦₈ b0) ∗ hSplit.base.pool lim st s ∗
       memRegion (sp + 0xb40#64) 960 ∗
       memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240 ∗
       memRegion (sp + 0xa50#64) 240 ∗ (x.keyA ↦ₛ x.key) ∗
       (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ Rest)
      post oom := by
  have_instrs cs.fastReject 4 1
  have hf_init := ProofLib.StdStartup.hasInstrs.fetch_at_zero cs.bl_initInner
  have_instrs cs.postInit 0 2
  wp_step
  refine sepWP_bind_state fun s_pre hs_pre => ?_
  have hpure_pre : PureStepPreserved s s_pre := by
    rw [hs_pre]; exact PureStepPreserved.of_proj_perm rfl rfl
  rw [← hpure_pre.pool_eq hSplit.base lim st]
  subst hs_pre
  refine step_bl_aesInitInner_allocStack b0 st hf_init hCal.initInner_ok
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp] using hspAl)
    (Entails.of_eq (by simp only [wp_norm, arm64_norm, hsp]; sep_ac_rfl))
    fun s_in b hb01 hx0_in hpc_in hrun_in hsp_in hcs_in hpure_in => ?_
  have hpure_s_in : PureStepPreserved s s_in := hpure_pre.trans hpure_in
  have hsp_in' : s_in.sp = sp := hsp_in.trans (by simp [wp_norm, arm64_norm, hsp])
  simp only [wp_norm, arm64_norm, hsp] at hsp_in ⊢
  wp_steps 2
  wp_if htbz
  · have hb_eq0 : b = 0#8 := by
      rcases hb01 with rfl | rfl
      · rfl
      · simp [wp_norm, arm64_norm] at htbz
    subst hb_eq0
    refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (cbc_soft_ks_branch (hSplit := hSplit) cs hCal x 0#8 _ _ (by decide) hkey32 hspAl
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun_in])
        (by simp [wp_norm, arm64_norm, hsp_in'])
        (by simpa [wp_norm, arm64_norm, hx2] using hcs_in.readReg64_x22)
        fun sf keyBytes960 hinv hpc_f hrun_f hsp_f hx19_f hx20_f hx21_f hx24_f hx25_f hx29_f hv_f hpure_f => ?_)
    have hpure_in_sf : PureStepPreserved s_in sf :=
      (PureStepPreserved.of_proj_perm rfl rfl).trans hpure_f
    rw [← hpure_in_sf.pool_eq hSplit.base lim st]
    refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf 0#8 keyBytes960 hinv hpc_f hrun_f hsp_f
        (hx19_f.trans (by simpa [wp_norm, arm64_norm] using hcs_in.readReg64_x19))
        (hx20_f.trans (by simpa [wp_norm, arm64_norm] using hcs_in.readReg64_x20))
        (hx21_f.trans (by simpa [wp_norm, arm64_norm] using hcs_in.readReg64_x21))
        (hx24_f.trans (by simpa [wp_norm, arm64_norm, hx24] using hcs_in.readReg64_x24))
        (hx25_f.trans (by simpa [wp_norm, arm64_norm] using hcs_in.readReg64_x25))
        (hx29_f.trans (by simpa [wp_norm, arm64_norm] using hcs_in.readReg64_x29))
        (hv_f.trans (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hcs_in.vregs))
        (hpure_s_in.trans hpure_in_sf))
  · have hb_eq1 : b = 1#8 := by
      rcases hb01 with rfl | rfl
      · exfalso; apply htbz; simp [wp_norm, arm64_norm]
      · rfl
    subst hb_eq1
    refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (cbc_hw_ks_branch (hSplit := hSplit) cs hCal x _ _ hkey32 hspAl
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun_in])
        (by simp [wp_norm, arm64_norm, hsp_in'])
        (by simpa [wp_norm, arm64_norm, hx2] using hcs_in.readReg64_x22)
        (by simpa [wp_norm, arm64_norm, hx24] using hcs_in.readReg64_x24)
        fun sf keyBytes960 hinv hpc_f hrun_f hsp_f hx19_f hx20_f hx21_f hx24_f hx25_f hx29_f hv_f hpure_f => ?_)
    have hpure_in_sf : PureStepPreserved s_in sf :=
      (PureStepPreserved.of_proj_perm rfl rfl).trans hpure_f
    rw [← hpure_in_sf.pool_eq hSplit.base lim st]
    refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf 1#8 keyBytes960 hinv hpc_f hrun_f hsp_f
        (hx19_f.trans (by simpa [wp_norm, arm64_norm] using hcs_in.readReg64_x19))
        (hx20_f.trans (by simpa [wp_norm, arm64_norm] using hcs_in.readReg64_x20))
        (hx21_f.trans (by simpa [wp_norm, arm64_norm] using hcs_in.readReg64_x21))
        hx24_f
        (hx25_f.trans (by simpa [wp_norm, arm64_norm] using hcs_in.readReg64_x25))
        (hx29_f.trans (by simpa [wp_norm, arm64_norm] using hcs_in.readReg64_x29))
        (hv_f.trans (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hcs_in.vregs))
        (hpure_s_in.trans hpure_in_sf))

/-! ## 2. Full Aligned Prolog + Key-Schedule Dispatch (`fnAddr + 0x028#64 -> fnAddr + 0x140#64`) -/

set_option maxHeartbeats 400000 in
theorem cbc_prolog_ks {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (st : M.σ) (w1 w2 w3 w4 w5 : BitVec 64)
    (Rest : SepProp) (s0 s1 : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpos : 0 < x.input.length) (hmod16 : x.input.length % 16 = 0)
    (hlt40 : x.input.length < 2 ^ 40) (hkey32 : x.key.length = 32)
    (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = fnAddr + 0x028#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = sp) (hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hx1 : (s1.readReg64 .x1).toNat = x.input.length)
    (hx2 : s1.readReg64 .x2 = x.keyA) (hx3 : s1.readReg64 .x3 = 32#64)
    (hx4 : s1.readReg64 .x4 = x.ivA) (hx5 : s1.readReg64 .x5 = 16#64)
    (hx8 : s1.readReg64 .x8 = x.ret)
    (hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hpure1 : PureStepPreserved s0 s1)
    (hnext : ∀ (sf : State) (b : BitVec 8) (keyBytes960 : List (BitVec 8)),
      KeyBytes960Inv b x.key keyBytes960 →
      sf.pc = fnAddr + 0x140#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = (hw.storageAddr &&& 0xfffffffffffff000#64) →
      sf.readReg64 .x20 = x.ivA → sf.readReg64 .x21 = 16#64 →
      sf.readReg64 .x24 = sp + 0x4b0#64 → sf.readReg64 .x25 = BitVec.ofNat 64 x.input.length →
      sf.readReg64 .x29 = s0.sp - 96#64 → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      PureStepPreserved s0 sf →
      SepWP P target_pc sf
        (slots56 sp 0#64 w1 w2 w3 x.ret w5 x.inA ∗
         memRegion (sp + 0x038#64) 168 ∗ memRegion (sp + 0x0e0#64) 8 ∗
         memRegion (sp + 0x0e8#64) 968 ∗ memRegion (sp + 0x4b0#64) 960 ∗
         memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240 ∗
         memRegion (sp + 0xa50#64) 240 ∗ ((sp + 0xb40#64) ↦ₛ keyBytes960) ∗
         memRegion (sp + 0xf00#64) 16 ∗ memRegion (sp + 0xf10#64) 16 ∗
         (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
         (hw.storageAddr ↦₈ b) ∗ hSplit.base.pool lim st sf ∗
         stackAt sp allocHookStack ∗ Rest)
        post oom) :
    SepWP P target_pc s1
      (slots56 sp 0#64 w1 w2 w3 w4 w5 x.inA ∗
       memRegion (sp + 56#64) 3816 ∗
       (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
       A.pool lim st s0 ∗
       stackAt sp allocHookStack ∗ Rest)
      post oom := by
  have hx1_bv : s1.readReg64 .x1 = BitVec.ofNat 64 x.input.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x.input.length < 2 ^ 64)]
  have hx1_ne0 : (BitVec.ofNat 64 x.input.length == 0#64) = false := by
    apply beq_false_of_ne; intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x.input.length < 2 ^ 64)] at this
    change x.input.length = 0 at this; omega
  have hx1_and15 : BitVec.ofNat 64 x.input.length &&& 15#64 = 0#64 := by
    rw [bv64_and15_eq_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x.input.length < 2 ^ 64)]
    exact hmod16
  rw [← hpure1.pool_eq A lim st]
  have h56 : sp + 56#64 = sp + 0x038#64 := rfl
  refine sepWP_weaken_pre
    (Entails.trans
      (Entails.of_eq (show slots56 sp 0#64 w1 w2 w3 w4 w5 x.inA ∗ memRegion (sp + 56#64) 3816 ∗
          (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗ A.pool lim st s1 ∗
          stackAt sp allocHookStack ∗ Rest =
        A.pool lim st s1 ∗ (slots56 sp 0#64 w1 w2 w3 w4 w5 x.inA ∗
          (memRegion (sp + 0x038#64) 168 ∗ memRegion (sp + 0x0e0#64) 8 ∗
           memRegion (sp + 0x0e8#64) 968 ∗ memRegion (sp + 0x4b0#64) 960 ∗
           memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240 ∗
           memRegion (sp + 0xa50#64) 240 ∗ memRegion (sp + 0xb40#64) 960 ∗
           memRegion (sp + 0xf00#64) 16 ∗ memRegion (sp + 0xf10#64) 16) ∗
          (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
          stackAt sp allocHookStack ∗ Rest) by
        rw [h56, localWork3816_split sp]; sep_ac_rfl))
      (sepConj_mono_left (hSplit.pool_out lim st s1))) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro b0
  have_instrs cs.prologue 10 6
  have hf_adrp := ProofLib.StdStartup.hasInstrs.fetch_at_zero cs.adrpStorage
  have_instrs cs.postStorageAdrp 0 1
  have hf_ldrb0 := ProofLib.StdStartup.hasInstrs.fetch_at_zero cs.ldrbStorage0
  have_instrs cs.storageCheck 0 7
  dsimp only [slots56]
  wp_steps 5
  wp_str64 hf_15 m0 hm0
  wp_steps 2
  refine SepWP.step_ldr8 (ea := hw.storageAddr) (wb := none)
    (hpc := by simp [wp_norm, arm64_norm]; try bv_lin)
    (hrun := by simp [wp_norm, arm64_norm, hrun1]) (hfetch := hf_ldrb0) (hsp := rfl)
    (haddr := by simp [evalAddrMode, wp_norm, arm64_norm])
    (hload := SepLoad8.of_eq (by sep_ac_rfl)) (hexec := rfl) ?_
  simp only [wp_norm, arm64_norm]
  wp_steps 5
  wp_if hb1
  · have hb0_eq1 : b0 = 1#8 := by
      have := congrArg (BitVec.truncate 8) hb1
      simpa using this
    subst hb0_eq1
    refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (cbc_hw_ks_branch (hSplit := hSplit) cs hCal x _ _ hkey32 hspAl
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun1])
        (by simp [wp_norm, arm64_norm, hsp1])
        (by simp [wp_norm, arm64_norm, hx2])
        (by simp [wp_norm, arm64_norm])
        fun sf keyBytes960 hinv hpc_f hrun_f hsp_f hx19_f hx20_f hx21_f hx24_f hx25_f hx29_f hv_f hpure_f => ?_)
    have hpure_s1_sf : PureStepPreserved s1 sf :=
      (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm0])).trans hpure_f
    rw [← hpure_s1_sf.pool_eq hSplit.base lim st]
    refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf 1#8 keyBytes960 hinv hpc_f hrun_f hsp_f
        (by simpa [wp_norm, arm64_norm, adrp_val_eq] using hx19_f)
        (by simpa [wp_norm, arm64_norm, hx4] using hx20_f)
        (by simpa [wp_norm, arm64_norm, hx5] using hx21_f)
        hx24_f
        (by simpa [wp_norm, arm64_norm, hx1_bv] using hx25_f)
        (by simpa [wp_norm, arm64_norm, hx29_1] using hx29_f)
        (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv_f.trans hv1)
        (hpure1.trans hpure_s1_sf))
  · have hb0_ne1 : b0 ≠ 1#8 := fun h => hb1 (by subst h; rfl)
    wp_steps 2
    wp_if hbff
    · refine sepWP_bind_state fun s_mid hs_mid => ?_
      have hpure_s1_mid : PureStepPreserved s1 s_mid := by
        rw [hs_mid]
        exact PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm] at hm0 ⊢; exact hm0)
      rw [← hpure_s1_mid.pool_eq hSplit.base lim st]
      subst hs_mid
      refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (cbc_init_ks_branch (hSplit := hSplit) cs hCal x b0 st _ _ hkey32 hspAl
          (by simp [wp_norm, arm64_norm]; try bv_lin)
          (by simp [wp_norm, arm64_norm, hrun1])
          (by simp [wp_norm, arm64_norm, hsp1])
          (by simp [wp_norm, arm64_norm, hx2])
          (by simp [wp_norm, arm64_norm])
          fun sf b keyBytes960 hinv hpc_f hrun_f hsp_f hx19_f hx20_f hx21_f hx24_f hx25_f hx29_f hv_f hpure_f => ?_)
      refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf b keyBytes960 hinv hpc_f hrun_f hsp_f
          (by simpa [wp_norm, arm64_norm, adrp_val_eq] using hx19_f)
          (by simpa [wp_norm, arm64_norm, hx4] using hx20_f)
          (by simpa [wp_norm, arm64_norm, hx5] using hx21_f)
          hx24_f
          (by simpa [wp_norm, arm64_norm, hx1_bv] using hx25_f)
          (by simpa [wp_norm, arm64_norm, hx29_1] using hx29_f)
          (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv_f.trans hv1)
          (hpure1.trans (hpure_s1_mid.trans hpure_f)))
    · refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (cbc_soft_ks_branch (hSplit := hSplit) cs hCal x b0 _ _ hb0_ne1 hkey32 hspAl
          (by simp [wp_norm, arm64_norm]; try bv_lin)
          (by simp [wp_norm, arm64_norm, hrun1])
          (by simp [wp_norm, arm64_norm, hsp1])
          (by simp [wp_norm, arm64_norm, hx2])
          fun sf keyBytes960 hinv hpc_f hrun_f hsp_f hx19_f hx20_f hx21_f hx24_f hx25_f hx29_f hv_f hpure_f => ?_)
      have hpure_s1_sf : PureStepPreserved s1 sf :=
        (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm0])).trans hpure_f
      rw [← hpure_s1_sf.pool_eq hSplit.base lim st]
      refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf b0 keyBytes960 hinv hpc_f hrun_f hsp_f
          (by simpa [wp_norm, arm64_norm, adrp_val_eq] using hx19_f)
          (by simpa [wp_norm, arm64_norm, hx4] using hx20_f)
          (by simpa [wp_norm, arm64_norm, hx5] using hx21_f)
          (by simpa [wp_norm, arm64_norm, hsp1] using hx24_f)
          (by simpa [wp_norm, arm64_norm, hx1_bv] using hx25_f)
          (by simpa [wp_norm, arm64_norm, hx29_1] using hx29_f)
          (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv_f.trans hv1)
          (hpure1.trans hpure_s1_sf))

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologKs

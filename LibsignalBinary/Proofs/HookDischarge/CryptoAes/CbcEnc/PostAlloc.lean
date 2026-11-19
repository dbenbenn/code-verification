/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.KeySetup
import ProofLib.BV
import Arm64.Trusted.ISA.Eval
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Post-Allocation Key/IV Restore & PKCS#7 Tail Spill (`+0x0c4..+0x188`) (`CbcEnc.PostAlloc`)

Verifies non-null `outBuf` check, `cmp/b.hi` untaken, `memcpy(sp+0xc90, sp+0x8c0, 976)` restoring
`CbcKeyState sp b x.key ∗ byte16At (sp + 0x1050#64) iv`, PKCS#7 tail staging via `memcpy` + `memset`
at `sp + 0x7d0`, and spilling all 16 tail bytes to `spill16At sp (pkcs7TailBytes x.input)`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.PostAlloc

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open CryptoGames.CBC (bytesToBlock blockToBytesLE blockToBytesLE_bytesToBlock padLen)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Heap.Fine (allocMemsetVmSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (aes256KeyScheduleFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (fsKeys256At step_str64_perm)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (armv8ExpandKey armv8InvExpandedKeys roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
  (Aes256EncHwAddrs CbcEncCode Aes256CbcEncryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
  (length_blockToBytesLE pkcs7TailBytes pkcs7TailBytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
  (CbcPreserved spAligned_of_eq spill16Words spill16At memRegion_64_eq_pts32
   byte16Cells16 byte16At pointsToBytes_16_eq_byte16At byte16Cells16_entails_memRegion_16
   CbcKeyState cbcKeyState_entails_memRegion_960 pointsTo64_entails_memRegion_8)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers
  (step_stp32_perm step_bl_cbc u_lsr4_eq u_and15_eq zext32_zext64_eq trunc32_zext64_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.KeySetup
  (KsStaged pointsToBytes_entails_cbcKeyState)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

section
arm64_proof_prelude
attribute [local irreducible] armv8ExpandKey armv8InvExpandedKeys aes256KeyScheduleFs roundKeys15At fsKeys256At
attribute [local simp, local arm64_norm] zext32_zext64_eq trunc32_zext64_eq

@[local simp, local arm64_norm] private theorem sp_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_advancePC (s : State) :
    s.advancePC.sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_setMem (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_setPState (s : State) (p : PState) :
    (s.setPState p).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_writeReg64_gpr (s : State) (n : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr n) v).sp = s.sp := by simp [State.writeReg64]

local macro "wp_stp32 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp32_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

theorem step_seg_post_alloc_stage {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc outBuf sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) {b : BitVec 8} {ksBytes : List (BitVec 8)} (hks : KsStaged b x.key ksBytes)
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsp_15 : sp &&& 15#64 = 0#64) (hne0 : outBuf ≠ 0#64)
    (hiv : x.iv.length = 16) (hin : x.input.length < 2 ^ 40)
    (hpc : s.pc = fnAddr + 0x0c4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 (.gpr 0#5) = outBuf)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16))
    (hx22 : s.readReg64 (.gpr 22#5) = x.inA)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (16 * (x.input.length / 16)))
    (hx29 : s.readReg64 (.gpr 29#5) = sp + 0x10c0#64)
    (hnext : ∀ s4 : State,
      s4.pc = fnAddr + 0x188#64 → s4.status = .Running → s4.sp = sp →
      CbcPreserved s s4 → calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      s4.readReg64 (.gpr 19#5) = x.ret →
      s4.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) →
      s4.readReg64 (.gpr 21#5) = outBuf →
      s4.readReg64 (.gpr 22#5) = x.inA →
      s4.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)) →
      s4.readReg64 (.gpr 24#5) = sp + 0xc90#64 →
      s4.readReg64 (.gpr 26#5) = sp + 0xc90#64 →
      s4.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (x.input.length / 16) →
      s4.readReg64 (.gpr 29#5) = sp + 0x10c0#64 →
      SepWP P target_pc s4
        ((spill16At sp (pkcs7TailBytes x.input) ∗ memRegion (sp + 0x7d0#64) 240 ∗
          memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
          CbcKeyState sp b x.key ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗
          (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s
      ((memRegion sp 64 ∗ memRegion (sp + 0x7d0#64) 240 ∗
        ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)) ∗
        memRegion (sp + 0xc90#64) 960 ∗ memRegion (sp + 0x1050#64) 16 ∗
        (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack) ∗ F) post oom := by
  have_instrs hc.segPostAlloc 0 9
  have hne0' : outBuf ≠ 0 := hne0
  apply SepWP.step_pure hpc hrun hf_0 rfl
    (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
  conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx0, hne0']
  wp_steps 1
  have h_ult_false :
      (BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16)).ult
        (BitVec.ofNat 64 x.input.length) = false := by
    have hn64 : x.input.length < 2 ^ 64 := by omega
    have hct64 : (x.input.length / 16 + 1) * 16 < 2 ^ 64 := by omega
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hct64,
      decide_eq_false_iff_not]
    omega
  apply SepWP.step_pure (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) hf_2 rfl
    (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
  conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, h_ult_false]
  wp_steps 6
  have h976_len : (ksBytes ++ x.iv).length = 976 := by rw [List.length_append, hks.1, hiv]
  refine step_bl_cbc hc.bl_postMc hCallees.memcpy_ok
    (sp + 0xc90#64, sp + 0x8c0#64, ksBytes ++ x.iv)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp]) hsp_15)
    (F := memRegion sp 64 ∗ memRegion (sp + 0x7d0#64) 240 ∗ (x.inA ↦ₛ x.input) ∗
      stackAt sp allocHookStack ∗ F)
    (PreSpatial := memRegion (sp + 0xc90#64) 976 ∗ ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)))
    (PostSpatial := memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
      CbcKeyState sp b x.key ∗ byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)))
    ?_ ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
  · rw [show (976 : Nat) = 960 + 16 from rfl, memRegion_split (sp + 0xc90#64) 960 16 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by sep_ac_rfl)
  · intro s_c hsc; dsimp only [allocMemcpyVmSpec]; rw [h976_len]
    have hx0c : s_c.readReg64 .x0 = sp + 0xc90#64 := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
    have hx1c : s_c.readReg64 .x1 = sp + 0x8c0#64 := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
    have hx2c : s_c.readReg64 .x2 = 976#64 := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
    exact Entails.pure_right ⟨hx0c, hx1c, hx2c, by decide⟩ (Entails.refl _)
  · intro _ _ _ _; dsimp only [allocMemcpyVmSpec]
    refine Entails.pure_left fun ⟨_, hacp, hvm⟩ => Entails.pure_right ⟨hacp, hvm⟩ ?_
    have hdst : ((sp + 0xc90#64) ↦ₛ (ksBytes ++ x.iv)) ⊢
        CbcKeyState sp b x.key ∗ byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) := by
      have haddr : (sp + 0xc90#64) + BitVec.ofNat 64 960 = sp + 0x1050#64 := by
        simp only [BitVec.add_assoc]; rfl
      conv => lhs; rw [pointsToBytes_append, hks.1, haddr,
        ← blockToBytesLE_bytesToBlock x.iv hiv,
        pointsToBytes_16_eq_byte16At (sp + 0x1050#64) (length_blockToBytesLE _)]
      exact sepConj_mono_left (pointsToBytes_entails_cbcKeyState hks)
    have hsrc : ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)) ⊢
        memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 := by
      have haddr : (sp + 0x8c0#64) + BitVec.ofNat 64 960 = sp + 0xc80#64 := by
        simp only [BitVec.add_assoc]; rfl
      rw [pointsToBytes_append, hks.1, haddr]
      refine sepConj_mono ?_ ?_
      · rw [← hks.1]; exact pointsToBytes_entails_memRegion _ _
      · rw [← hiv]; exact pointsToBytes_entails_memRegion _ _
    refine Entails.trans (sepConj_mono hdst hsrc) (Entails.of_eq (by sep_ac_rfl))
  · intro s1 hpc1 hrun1 hsp1 hcs1 hp1
    rw [BitVec.add_assoc] at hpc1; simp only [BitVec.reduceAdd] at hpc1
    have hsp1' : s1.sp = sp := by rw [hsp1]; simp [wp_norm, arm64_norm, hsp]
    have hx19_1 : s1.readReg64 (.gpr 19#5) = x.ret := by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm, hx19]
    have hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) := by
      rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm, hx20]
    have hx21_1 : s1.readReg64 (.gpr 21#5) = outBuf := by rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm]
    have hx22_1 : s1.readReg64 (.gpr 22#5) = x.inA := by rw [hcs1.readReg64_x22]; simp [wp_norm, arm64_norm, hx22]
    have hx23_1 : s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length := by
      rw [hcs1.readReg64_x23]; simp [wp_norm, arm64_norm, hx23]
    have hx24_1 : s1.readReg64 (.gpr 24#5) = sp + 0xc90#64 := by rw [hcs1.readReg64_x24]; simp [wp_norm, arm64_norm]
    have hx25_1 : s1.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (16 * (x.input.length / 16)) := by
      rw [hcs1.readReg64_x25]; simp [wp_norm, arm64_norm, hx25]
    have hx26_1 : s1.readReg64 (.gpr 26#5) = sp + 0xc90#64 := by rw [hcs1.readReg64_x26]; simp [wp_norm, arm64_norm]
    have hx29_1 : s1.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by rw [hcs1.readReg64_x29]; simp [wp_norm, arm64_norm, hx29]
    have hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
      rw [hcs1.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv
    have hp01 : CbcPreserved s s1 :=
      (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl).trans hp1
    clear hsp1 hcs1 hp1
    rw [show (240 : Nat) = 16 + 224 from rfl,
        memRegion_split (sp + 0x7d0#64) 16 224 (by decide),
        memRegion_split (sp + 0x7d0#64) 8 8 (by decide),
        memRegion_eight, memRegion_eight]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun cSlot0 => SepWP.exists_elim fun cSlot1 => ?_
    have_instrs hc.segPadMc 0 8
    wp_steps 5
    wp_str64 hf_5 m_zr0 hm_zr0
    wp_str64 hf_6 m_zr1 hm_zr1
    wp_steps 1
    let remBs := x.input.drop (16 * (x.input.length / 16))
    have hrem_len : remBs.length = x.input.length % 16 := by dsimp only [remBs]; rw [List.length_drop]; omega
    have hin_split :
        (x.inA ↦ₛ x.input) =
          (x.inA ↦ₛ x.input.take (16 * (x.input.length / 16))) ∗
            ((x.inA + BitVec.ofNat 64 (16 * (x.input.length / 16))) ↦ₛ remBs) := by
      conv => lhs; rw [← List.take_append_drop (16 * (x.input.length / 16)) x.input]
      rw [pointsToBytes_append, List.length_take_of_le (by omega)]
    refine step_bl_cbc hc.bl_padMc hCallees.memcpy_ok
      (sp + 0x7d0#64, x.inA + BitVec.ofNat 64 (16 * (x.input.length / 16)), remBs)
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp1']) hsp_15)
      (F := memRegion sp 64 ∗ memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
        CbcKeyState sp b x.key ∗ byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗
        memRegion (sp + 0x7d0#64 + BitVec.ofNat 64 (x.input.length % 16)) (padLen x.input.length) ∗
        memRegion (sp + 0x7e0#64) 224 ∗
        (x.inA ↦ₛ x.input.take (16 * (x.input.length / 16))) ∗ stackAt sp allocHookStack ∗ F)
      (PreSpatial := memRegion (sp + 0x7d0#64) remBs.length ∗
        ((x.inA + BitVec.ofNat 64 (16 * (x.input.length / 16))) ↦ₛ remBs))
      (PostSpatial := ((sp + 0x7d0#64) ↦ₛ remBs) ∗
        ((x.inA + BitVec.ofNat 64 (16 * (x.input.length / 16))) ↦ₛ remBs))
      ?_ ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
    · have h16_split :
          (((sp + 0x7d0#64) ↦₆₄ 0#64) ∗ ((sp + 0x7d8#64) ↦₆₄ 0#64)) ⊢
            memRegion (sp + 0x7d0#64) remBs.length ∗
              memRegion (sp + 0x7d0#64 + BitVec.ofNat 64 (x.input.length % 16)) (padLen x.input.length) := by
        have hmr16 : (((sp + 0x7d0#64) ↦₆₄ 0#64) ∗ ((sp + 0x7d8#64) ↦₆₄ 0#64)) ⊢
            memRegion (sp + 0x7d0#64) 16 := by
          rw [memRegion_split (sp + 0x7d0#64) 8 8 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact sepConj_mono (pointsTo64_entails_memRegion_8 _ _) (pointsTo64_entails_memRegion_8 _ _)
        refine Entails.trans hmr16 ?_
        have h16_pad : 16 = remBs.length + padLen x.input.length := by rw [hrem_len]; unfold padLen; omega
        conv => lhs; rw [h16_pad, memRegion_split (sp + 0x7d0#64) remBs.length _ (by unfold padLen; rw [hrem_len]; omega)]
        conv => lhs; arg 2; arg 1; rw [hrem_len]
        exact Entails.refl _
      rw [hin_split]
      refine Entails.trans (Entails.of_eq (show _ =
          (((sp + 0x7d0#64) ↦₆₄ 0#64) ∗ ((sp + 0x7d8#64) ↦₆₄ 0#64)) ∗
          (memRegion sp 64 ∗ memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
            CbcKeyState sp b x.key ∗ byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗
            memRegion (sp + 0x7e0#64) 224 ∗
            (x.inA ↦ₛ x.input.take (16 * (x.input.length / 16))) ∗
            ((x.inA + BitVec.ofNat 64 (16 * (x.input.length / 16))) ↦ₛ remBs) ∗
            stackAt sp allocHookStack ∗ F) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h16_split) (Entails.of_eq (by sep_ac_rfl))
    · intro s_c hsc; dsimp only [allocMemcpyVmSpec]
      have hx0c : s_c.readReg64 .x0 = sp + 0x7d0#64 := by
        rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
      have hx1c : s_c.readReg64 .x1 = x.inA + BitVec.ofNat 64 (16 * (x.input.length / 16)) := by
        rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
      have hx2c : s_c.readReg64 .x2 = BitVec.ofNat 64 remBs.length := by
        rw [hsc, hrem_len, ← u_and15_eq hin]
        simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
      exact Entails.pure_right ⟨hx0c, hx1c, hx2c, by rw [hrem_len]; omega⟩ (Entails.refl _)
    · intro _ _ _ _; dsimp only [allocMemcpyVmSpec]
      exact Entails.pure_left fun ⟨_, hacp, hvm⟩ => Entails.pure_right ⟨hacp, hvm⟩ (Entails.refl _)
    · intro s2 hpc2 hrun2 hsp2 hcs2 hp2
      rw [BitVec.add_assoc] at hpc2; simp only [BitVec.reduceAdd] at hpc2
      have hsp2' : s2.sp = sp := by rw [hsp2]; simp [wp_norm, arm64_norm, hsp1']
      have hx19_2 : s2.readReg64 (.gpr 19#5) = x.ret := by rw [hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_1]
      have hx20_2 : s2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) := by
        rw [hcs2.readReg64_x20]; simp [wp_norm, arm64_norm, hx20_1]
      have hx21_2 : s2.readReg64 (.gpr 21#5) = outBuf := by rw [hcs2.readReg64_x21]; simp [wp_norm, arm64_norm, hx21_1]
      have hx22_2 : s2.readReg64 (.gpr 22#5) = x.inA := by rw [hcs2.readReg64_x22]; simp [wp_norm, arm64_norm, hx22_1]
      have hx23_2 : s2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (x.input.length % 16) := by
        rw [hcs2.readReg64_x23, ← u_and15_eq hin]; simp [wp_norm, arm64_norm]
      have hx24_2 : s2.readReg64 (.gpr 24#5) = sp + 0xc90#64 := by rw [hcs2.readReg64_x24]; simp [wp_norm, arm64_norm, hx24_1]
      have hx25_2 : s2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (16 * (x.input.length / 16)) := by
        rw [hcs2.readReg64_x25]; simp [wp_norm, arm64_norm, hx25_1]
      have hx26_2 : s2.readReg64 (.gpr 26#5) = sp + 0xc90#64 := by rw [hcs2.readReg64_x26]; simp [wp_norm, arm64_norm, hx26_1]
      have hx27_2 : s2.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (x.input.length / 16) := by
        rw [hcs2.readReg64_x27, ← u_lsr4_eq hin]; simp [wp_norm, arm64_norm]
      have hx28_2 : s2.readReg64 (.gpr 28#5) = sp + 0x7d0#64 := by rw [hcs2.readReg64_x28]; simp [wp_norm, arm64_norm]
      have hx29_2 : s2.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by rw [hcs2.readReg64_x29]; simp [wp_norm, arm64_norm, hx29_1]
      have hv2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
        rw [hcs2.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv1
      have hp02 : CbcPreserved s s2 := hp01.trans
        ((CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hm_zr1, hm_zr0])).trans hp2)
      clear hsp2 hcs2 hp2
      have_instrs hc.segPadMs 0 4; wp_steps 4
      have hpad_bv64 :
          16#64 - BitVec.ofNat 64 (x.input.length % 16) = BitVec.ofNat 64 (padLen x.input.length) := by
        apply BitVec.eq_of_toNat_eq
        have hr : x.input.length % 16 < 16 := Nat.mod_lt _ (by decide)
        unfold padLen; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have hpad_bv8 :
          ((BitVec.ofNat 64 (padLen x.input.length)).truncate 32).setWidth 8 =
            BitVec.ofNat 8 (padLen x.input.length) := by
        apply BitVec.eq_of_toNat_eq; unfold padLen; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      refine step_bl_cbc hc.bl_padMs hCallees.memset_ok
        (sp + 0x7d0#64 + BitVec.ofNat 64 (x.input.length % 16),
          BitVec.ofNat 8 (padLen x.input.length), padLen x.input.length)
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun2])
        (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp2']) hsp_15)
        (F := memRegion sp 64 ∗ memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
          CbcKeyState sp b x.key ∗ byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗
          memRegion (sp + 0x7e0#64) 224 ∗ ((sp + 0x7d0#64) ↦ₛ remBs) ∗
          (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ F)
        (PreSpatial := memRegion (sp + 0x7d0#64 + BitVec.ofNat 64 (x.input.length % 16)) (padLen x.input.length))
        (PostSpatial := ((sp + 0x7d0#64 + BitVec.ofNat 64 (x.input.length % 16)) ↦ₛ
          List.replicate (padLen x.input.length) (BitVec.ofNat 8 (padLen x.input.length))))
        (by rw [hin_split]; exact Entails.of_eq (by sep_ac_rfl)) ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
      · intro s_c hsc; dsimp only [allocMemsetVmSpec]
        have hx0c : s_c.readReg64 .x0 = sp + 0x7d0#64 + BitVec.ofNat 64 (x.input.length % 16) := by
          rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
        have hx1c : s_c.readReg64 .x1 = BitVec.ofNat 64 (padLen x.input.length) := by
          rw [hsc, ← hpad_bv64]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
        have hx1_8 : (s_c.readReg32 .x1).setWidth 8 =
            BitVec.ofNat 8 (padLen x.input.length) := by
          rw [State.readReg32, hx1c, hpad_bv8]
        have hx2c : s_c.readReg64 .x2 = BitVec.ofNat 64 (padLen x.input.length) := by
          rw [hsc, ← hpad_bv64]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
        exact Entails.pure_right ⟨hx0c, hx1_8, hx2c, by unfold padLen; omega⟩ (Entails.refl _)
      · intro _ _ _ _; dsimp only [allocMemsetVmSpec]
        exact Entails.pure_left fun ⟨_, hacp, hvm⟩ => Entails.pure_right ⟨hacp, hvm⟩ (Entails.refl _)
      · intro s3 hpc3 hrun3 hsp3 hcs3 hp3
        rw [BitVec.add_assoc] at hpc3; simp only [BitVec.reduceAdd] at hpc3
        have hsp3' : s3.sp = sp := by rw [hsp3]; simp [wp_norm, arm64_norm, hsp2']
        have hx19_3 : s3.readReg64 (.gpr 19#5) = x.ret := by rw [hcs3.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_2]
        have hx20_3 : s3.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) := by
          rw [hcs3.readReg64_x20]; simp [wp_norm, arm64_norm, hx20_2]
        have hx21_3 : s3.readReg64 (.gpr 21#5) = outBuf := by rw [hcs3.readReg64_x21]; simp [wp_norm, arm64_norm, hx21_2]
        have hx22_3 : s3.readReg64 (.gpr 22#5) = x.inA := by rw [hcs3.readReg64_x22]; simp [wp_norm, arm64_norm, hx22_2]
        have hx24_3 : s3.readReg64 (.gpr 24#5) = sp + 0xc90#64 := by rw [hcs3.readReg64_x24]; simp [wp_norm, arm64_norm, hx24_2]
        have hx25_3 : s3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (16 * (x.input.length / 16)) := by
          rw [hcs3.readReg64_x25]; simp [wp_norm, arm64_norm, hx25_2]
        have hx26_3 : s3.readReg64 (.gpr 26#5) = sp + 0xc90#64 := by rw [hcs3.readReg64_x26]; simp [wp_norm, arm64_norm, hx26_2]
        have hx27_3 : s3.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (x.input.length / 16) := by
          rw [hcs3.readReg64_x27]; simp [wp_norm, arm64_norm, hx27_2]
        have hx29_3 : s3.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by rw [hcs3.readReg64_x29]; simp [wp_norm, arm64_norm, hx29_2]
        have hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
          rw [hcs3.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv2
        have hp03 : CbcPreserved s s3 := hp02.trans
          ((CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl).trans hp3)
        clear hsp3 hcs3 hp3
        let tb := pkcs7TailBytes x.input
        have htb_merge :
            ((sp + 0x7d0#64 + BitVec.ofNat 64 (x.input.length % 16)) ↦ₛ
              List.replicate (padLen x.input.length) (BitVec.ofNat 8 (padLen x.input.length))) ∗
            ((sp + 0x7d0#64) ↦ₛ remBs) = byte16At (sp + 0x7d0#64) tb := by
          rw [sepConj_comm, ← hrem_len, ← pointsToBytes_append]
          exact pointsToBytes_16_eq_byte16At (sp + 0x7d0#64) (pkcs7TailBytes_length x.input)
        refine SepWP.weaken_pre (P' :=
            byte16At (sp + 0x7d0#64) tb ∗ memRegion sp 64 ∗
            (memRegion (sp + 0x7e0#64) 224 ∗ memRegion (sp + 0x8c0#64) 960 ∗
              memRegion (sp + 0xc80#64) 16 ∗ CbcKeyState sp b x.key ∗
              byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗
              (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ F))
          (by rw [← htb_merge]; exact Entails.of_eq (by sep_ac_rfl)) ?_
        generalize h_iv : byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) = ivCell
        rw [memRegion_64_eq_pts32 sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        iterate 16 refine SepWP.exists_elim fun _ => ?_
        dsimp only [byte16At, byte16Cells16]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        have_instrs hc.segSpillTail 0 25
        wp_steps 3; wp_stp32 hf_3 m_s0 hm_s0
        wp_steps 2; wp_stp32 hf_6 m_s1 hm_s1
        wp_steps 2; wp_stp32 hf_9 m_s2 hm_s2
        wp_steps 2; wp_stp32 hf_12 m_s3 hm_s3
        wp_steps 2; wp_stp32 hf_15 m_s4 hm_s4
        wp_steps 2; wp_stp32 hf_18 m_s5 hm_s5
        wp_steps 2; wp_stp32 hf_21 m_s6 hm_s6
        wp_steps 2; wp_stp32 hf_24 m_s7 hm_s7
        have hmr240 :
            byte16Cells16 (sp + 0x7d0#64)
              (tb.getD 0 0#8) (tb.getD 1 0#8) (tb.getD 2 0#8) (tb.getD 3 0#8)
              (tb.getD 4 0#8) (tb.getD 5 0#8) (tb.getD 6 0#8) (tb.getD 7 0#8)
              (tb.getD 8 0#8) (tb.getD 9 0#8) (tb.getD 10 0#8) (tb.getD 11 0#8)
              (tb.getD 12 0#8) (tb.getD 13 0#8) (tb.getD 14 0#8) (tb.getD 15 0#8) ∗
            memRegion (sp + 0x7e0#64) 224 ⊢ memRegion (sp + 0x7d0#64) 240 := by
          rw [show (240 : Nat) = 16 + 224 from rfl,
              memRegion_split (sp + 0x7d0#64) 16 224 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact sepConj_mono_left (byte16Cells16_entails_memRegion_16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        refine SepWP.weaken_pre ?_
          (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
            (by simp [wp_norm, arm64_norm, hrun3]) (by simp [wp_norm, arm64_norm, hsp3'])
            (hp03.trans (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm, hm_s7, hm_s6, hm_s5, hm_s4, hm_s3, hm_s2, hm_s1, hm_s0])))
            (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv3)
            (by simp [wp_norm, arm64_norm, hx19_3]) (by simp [wp_norm, arm64_norm, hx20_3])
            (by simp [wp_norm, arm64_norm, hx21_3]) (by simp [wp_norm, arm64_norm, hx22_3])
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx24_3])
            (by simp [wp_norm, arm64_norm, hx26_3]) (by simp [wp_norm, arm64_norm, hx27_3])
            (by simp [wp_norm, arm64_norm, hx29_3]))
        rw [h_iv]
        have hfold_pre :
            (((byte16Cells16 (sp + 0x7d0#64)
                (tb.getD 0 0#8) (tb.getD 1 0#8) (tb.getD 2 0#8) (tb.getD 3 0#8)
                (tb.getD 4 0#8) (tb.getD 5 0#8) (tb.getD 6 0#8) (tb.getD 7 0#8)
                (tb.getD 8 0#8) (tb.getD 9 0#8) (tb.getD 10 0#8) (tb.getD 11 0#8)
                (tb.getD 12 0#8) (tb.getD 13 0#8) (tb.getD 14 0#8) (tb.getD 15 0#8) ∗
              memRegion (sp + 0x7e0#64) 224) ∗
              (spill16At sp tb ∗ memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
                CbcKeyState sp b x.key ∗ ivCell ∗ (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ F))) ⊢
            ((spill16At sp tb ∗ memRegion (sp + 0x7d0#64) 240 ∗
              memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
              CbcKeyState sp b x.key ∗ ivCell ∗ (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack) ∗ F) :=
          Entails.trans (sepConj_mono_left hmr240) (Entails.of_eq (by sep_ac_rfl))
        refine Entails.trans ?_ hfold_pre
        dsimp only [byte16Cells16, spill16At, spill16Words]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Entails.of_eq (by sep_ac_rfl)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.PostAlloc

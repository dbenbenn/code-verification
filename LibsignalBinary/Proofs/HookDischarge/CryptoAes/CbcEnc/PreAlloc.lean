/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WPp
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
meta import ProofLib.StdStartup.StdDetect
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Pre-Allocation Entry, `init_inner` Dispatch & Panic Tail (`CbcEnc.PreAlloc`)

Verifies `+0x000..+0x0c0` (prologue, `STORAGE` dispatch across `1#8`, `0xff#8` lazy `init_inner`,
and fallback, plus `[ksBytes, iv]` staging up to `bl alloc_zeroed`) and `cbc_panic_tail`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.PreAlloc

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open ProofLib.StdStartup (pageLo12)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget FitsEvents NullAllowed VmPreserved OomPreserved
   AllocCallPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (rustAllocShimVmSpec allocMemcpyVmSpec rustHandleErrorPanicSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (step_str64_perm step_stp64_perm)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
  (PoolAesInitSplit step_bl_aesInitInner_allocStack)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockEnc
  (pointsTo128_eq_pointsToBytes pointsToBytes16_eq_pointsTo128 u128ToBytesLE_bytesToU128LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
  (Aes256EncHwAddrs CbcEncCode Aes256CbcEncryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
  (aesEncEvents aesEncBudgetCondSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
  (CbcPreserved sp_sub96_and_15 sp_sub4192_and_15 sp_sub4384_and_15 spAligned_of_eq
   allocHookStack_split_16 memRegion_976_split_probe memRegion_976_fold_probe
   cbcSavedCells cbcSavedRegs stackFrameAt_96_cells)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers
  (step_bl_cbc u_eq_ofNat_of_lt40 u_lsr40_zero fullLen_and_eq ctLen_adds_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.KeySetup
  (KsStaged step_hw_key_setup step_sw_key_setup)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand.Simp
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

section
arm64_proof_prelude
attribute [local irreducible] aesRconBytes

@[local simp, local arm64_norm] private theorem applyWriteback_none (s : State) :
    applyWriteback s none = s := rfl

@[local simp, local arm64_norm] private theorem sp_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_advancePC (s : State) :
    s.advancePC.sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_setMem (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_setPState (s : State) (p : PState) :
    (s.setPState p).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_writeVReg128 (s : State) (n : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 n v).sp = s.sp := by cases s; rfl
@[local simp, local arm64_norm] private theorem sp_writeReg64_gpr (s : State) (n : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr n) v).sp = s.sp := by simp [State.writeReg64]
@[local simp, local arm64_norm] private theorem sp_writeReg64_sp (s : State) (v : BitVec 64) :
    (s.writeReg64 .sp v).sp = v := rfl

private theorem entails_init_pre {M : AllocCostModel} {B : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {s0 s1 : State} {sp storageAddr : BitVec 64}
    {oldVal : BitVec 8} {Pre F : SepProp}
    (hp : CbcPreserved s0 s1) (hsp : s1.sp = sp)
    (hent : Pre ⊢ ((storageAddr ↦₈ oldVal) ∗ B.pool lim st s0 ∗ stackAt sp allocHookStack) ∗ F) :
    Pre ⊢ ((storageAddr ↦₈ oldVal) ∗ B.pool lim st s1 ∗ stackAt s1.sp allocHookStack) ∗ F := by
  rwa [hp.pool_eq B lim st, hsp]

private theorem cbcPreserved_trans_rev {s0 s1 s2 : State}
    (h2 : CbcPreserved s1 s2) (h1 : CbcPreserved s0 s1) : CbcPreserved s0 s2 := h1.trans h2

/-! ## 1. Unified Join-to-Alloc (`+0x07c..+0x0c0`) -/

private theorem step_join_to_alloc {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) {ksBytes : List (BitVec 8)} (hks_len : ksBytes.length = 960)
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x07c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_15 : sp &&& 15#64 = 0#64)
    (hp0 : CbcPreserved s0 s) (hv0 : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret) (hx20 : s.readReg64 (.gpr 20#5) = x.ivA)
    (hx22 : s.readReg64 (.gpr 22#5) = x.inA)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length)
    (hx29 : s.readReg64 (.gpr 29#5) = sp + 0x10c0#64)
    (hiv : x.iv.length = 16) (hin : x.input.length < 2 ^ 40)
    (hnext : ∀ sf : State,
      let ctLen := (x.input.length / 16 + 1) * 16
      sf.pc = fnAddr + 0x0c0#64 → sf.status = .Running → sf.sp = sp →
      CbcPreserved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 (.gpr 0#5) = BitVec.ofNat 64 ctLen →
      sf.readReg64 (.gpr 1#5) = 1#64 →
      sf.readReg64 (.gpr 19#5) = x.ret →
      sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ctLen →
      sf.readReg64 (.gpr 22#5) = x.inA →
      sf.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length →
      sf.readReg64 (.gpr 24#5) = 1#64 →
      sf.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (16 * (x.input.length / 16)) →
      sf.readReg64 (.gpr 29#5) = sp + 0x10c0#64 →
      SepWP P target_pc sf
        ((memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x410#64) 960 ∗
          ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)) ∗ (x.ivA ↦ₛ x.iv)) ∗ F) post oom) :
    SepWP P target_pc s
      ((memRegion (sp + 0x040#64) 976 ∗ ((sp + 0x410#64) ↦ₛ ksBytes) ∗
        memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
        (x.ivA ↦ₛ x.iv)) ∗ F) post oom := by
  have hsp_reg : s.readReg64 .sp = sp := hsp
  have_instrs hc.segJoinMc1 0 3; wp_steps 3
  refine step_bl_cbc hc.bl_joinMc1 hCallees.memcpy_ok
    (sp + 0x8c0#64, sp + 0x410#64, ksBytes)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp]) hsp_15)
    (F := memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0xc80#64) 16 ∗ (x.ivA ↦ₛ x.iv) ∗ F)
    (PreSpatial := memRegion (sp + 0x8c0#64) 960 ∗ ((sp + 0x410#64) ↦ₛ ksBytes))
    (PostSpatial := ((sp + 0x8c0#64) ↦ₛ ksBytes) ∗ memRegion (sp + 0x410#64) 960)
    (Entails.of_eq (by sep_ac_rfl)) ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
  · intro s_c hsc; dsimp only [allocMemcpyVmSpec]; rw [hks_len]
    have hx0c : s_c.readReg64 .x0 = sp + 0x8c0#64 := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
    have hx1c : s_c.readReg64 .x1 = sp + 0x410#64 := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
    have hx2c : s_c.readReg64 .x2 = 960#64 := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
    exact Entails.pure_right ⟨hx0c, hx1c, hx2c, by decide⟩ (Entails.refl _)
  · intro _ _ _ _; dsimp only [allocMemcpyVmSpec]
    refine Entails.pure_left fun ⟨_, hacp, hvm⟩ => Entails.pure_right ⟨hacp, hvm⟩ ?_
    refine sepConj_mono_right ?_; rw [← hks_len]; exact pointsToBytes_entails_memRegion _ _
  · intro s1 hpc1 hrun1 hsp1 hcs1 hp1
    have hsp1' : s1.sp = sp := by rw [hsp1]; simp [wp_norm, arm64_norm, hsp]
    have hsp1_reg : s1.readReg64 .sp = sp := hsp1'
    have hsp1_and : s1.sp &&& 15#64 = 0#64 := hsp1' ▸ hsp_15
    have hx19_1 : s1.readReg64 (.gpr 19#5) = x.ret := by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm, hx19]
    have hx20_1 : s1.readReg64 (.gpr 20#5) = x.ivA := by rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm, hx20]
    have hx22_1 : s1.readReg64 (.gpr 22#5) = x.inA := by rw [hcs1.readReg64_x22]; simp [wp_norm, arm64_norm, hx22]
    have hx23_1 : s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length := by
      rw [hcs1.readReg64_x23]; simp [wp_norm, arm64_norm, hx23]
    have hx29_1 : s1.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by
      rw [hcs1.readReg64_x29]; simp [wp_norm, arm64_norm, hx29]
    have hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
      rw [hcs1.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv0
    have hp01 : CbcPreserved s0 s1 :=
      hp0.trans ((CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl).trans hp1)
    clear hsp1 hcs1 hp1
    rw [pointsToBytes16_eq_pointsTo128 hiv]
    have_instrs hc.segJoinMc2 0 5
    wp_ldr128 hf_0; wp_steps 3; wp_str128 hf_4 m_iv hm_iv
    have h976_len : (ksBytes ++ x.iv).length = 976 := by rw [List.length_append, hks_len, hiv]
    refine step_bl_cbc hc.bl_joinMc2 hCallees.memcpy_ok
      (sp + 0x040#64, sp + 0x8c0#64, ksBytes ++ x.iv)
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp1']) hsp_15)
      (F := memRegion (sp + 0x410#64) 960 ∗ (x.ivA ↦ₛ x.iv) ∗ F)
      (PreSpatial := memRegion (sp + 0x040#64) 976 ∗ ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)))
      (PostSpatial := memRegion (sp + 0x040#64) 976 ∗ ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)))
      ?_ ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
    · rw [pointsTo128_eq_pointsToBytes, pointsTo128_eq_pointsToBytes, u128ToBytesLE_bytesToU128LE hiv]
      have hcat : ((sp + 0x8c0#64) ↦ₛ ksBytes) ∗ ((sp + 0xc80#64) ↦ₛ x.iv) =
          ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)) := by
        rw [pointsToBytes_append, hks_len]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [← hcat]; exact Entails.of_eq (by sep_ac_rfl)
    · intro s_c hsc; dsimp only [allocMemcpyVmSpec]; rw [h976_len]
      have hx0c : s_c.readReg64 .x0 = sp + 0x040#64 := by
        rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
      have hx1c : s_c.readReg64 .x1 = sp + 0x8c0#64 := by
        rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
      have hx2c : s_c.readReg64 .x2 = 976#64 := by
        rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
      exact Entails.pure_right ⟨hx0c, hx1c, hx2c, by decide⟩ (Entails.refl _)
    · intro _ _ _ _; dsimp only [allocMemcpyVmSpec]
      refine Entails.pure_left fun ⟨_, hacp, hvm⟩ => Entails.pure_right ⟨hacp, hvm⟩ ?_
      refine sepConj_mono_left ?_; rw [← h976_len]; exact pointsToBytes_entails_memRegion _ _
    · intro s2 hpc2 hrun2 hsp2 hcs2 hp2
      have hsp2' : s2.sp = sp := by rw [hsp2]; simp [wp_norm, arm64_norm, hsp1']
      have hx19_2 : s2.readReg64 (.gpr 19#5) = x.ret := by rw [hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_1]
      have hx22_2 : s2.readReg64 (.gpr 22#5) = x.inA := by rw [hcs2.readReg64_x22]; simp [wp_norm, arm64_norm, hx22_1]
      have hx23_2 : s2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length := by
        rw [hcs2.readReg64_x23]; simp [wp_norm, arm64_norm, hx23_1]
      have hx29_2 : s2.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by
        rw [hcs2.readReg64_x29]; simp [wp_norm, arm64_norm, hx29_1]
      have hv2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
        rw [hcs2.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv1
      have hp02 : CbcPreserved s0 s2 :=
        hp01.trans ((CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hm_iv])).trans hp2)
      clear hsp2 hcs2 hp2
      have_instrs hc.segSizeCalc 0 3; wp_steps 2
      have hfull_eq := fullLen_and_eq hin
      have hct_eq := ctLen_adds_eq hin
      have hmsb_false :
          (((BitVec.ofNat 64 x.input.length &&& 0x7ffffffffffffff0#64) + 16#64)).msb = false := by
        have h40 := u_lsr40_zero hin
        generalize BitVec.ofNat 64 x.input.length = u at h40 ⊢; revert h40; bv_bits
      apply SepWP.step_pure (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun2]) hf_2 rfl
        (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
      conv => arg 3; simp [Program.evalInst, execInstWithSvc, conditionHolds_mi_addsPState64,
        arm64_norm, wp_norm, hmsb_false]
      refine step_bl_cbc hc.bl_shim hCallees.shim_ok ()
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun2])
        (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp2']) hsp_15)
        (PreSpatial := emp) (PostSpatial := emp)
        (F := (memRegion (sp + 0x040#64) 976 ∗ ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv))) ∗
          (memRegion (sp + 0x410#64) 960 ∗ (x.ivA ↦ₛ x.iv) ∗ F))
        (by rw [emp_sepConj]; exact Entails.refl _) (fun _ _ => Entails.refl _)
        (fun _ _ _ _ => by
          dsimp only [rustAllocShimVmSpec]
          rw [← sepConj_emp ⌜AllocCallPreserved _ _ ∧ VmPreserved _ _⌝]
          exact Entails.pure_left fun h => Entails.pure_right h (Entails.refl _))
        (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
      intro s3 hpc3 hrun3 hsp3 hcs3 hp3
      have hsp3' : s3.sp = sp := by rw [hsp3]; simp [wp_norm, arm64_norm, hsp2']
      have hx19_3 : s3.readReg64 (.gpr 19#5) = x.ret := by rw [hcs3.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_2]
      have hx20_3 : s3.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) := by
        rw [hcs3.readReg64_x20]; simp [wp_norm, arm64_norm, hfull_eq, hct_eq]
      have hx22_3 : s3.readReg64 (.gpr 22#5) = x.inA := by rw [hcs3.readReg64_x22]; simp [wp_norm, arm64_norm, hx22_2]
      have hx23_3 : s3.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length := by
        rw [hcs3.readReg64_x23]; simp [wp_norm, arm64_norm, hx23_2]
      have hx25_3 : s3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (16 * (x.input.length / 16)) := by
        rw [hcs3.readReg64_x25]; simp [wp_norm, arm64_norm, hfull_eq]
      have hx29_3 : s3.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by
        rw [hcs3.readReg64_x29]; simp [wp_norm, arm64_norm, hx29_2]
      have hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
        rw [hcs3.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv2
      have hp03 : CbcPreserved s0 s3 :=
        hp02.trans ((CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl).trans hp3)
      clear hsp3 hcs3 hp3
      have_instrs hc.segAllocArgs 0 3; wp_steps 3
      refine SepWP.weaken_pre ?_
        (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
          (by simp [wp_norm, arm64_norm, hrun3]) (by simp [wp_norm, arm64_norm, hsp3'])
          (hp03.trans (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl))
          (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv3)
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hx19_3]) (by simp [wp_norm, arm64_norm, hx20_3])
          (by simp [wp_norm, arm64_norm, hx22_3]) (by simp [wp_norm, arm64_norm, hx23_3])
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx25_3])
          (by simp [wp_norm, arm64_norm, hx29_3]))
      rw [emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. Full Pre-Allocation Segment (`+0x000..+0x0c0`) & Null-Return Panic Tail -/

theorem step_seg_pre_alloc {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) (st : M.σ) (b0 : BitVec 8) {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsp_def : s0.sp - 4384#64 = sp)
    (hpc : s0.pc = fnAddr) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.inA) (hx1 : (s0.readReg64 .x1).toNat = x.input.length)
    (hx2 : s0.readReg64 .x2 = x.keyA) (hx3 : s0.readReg64 .x3 = 32#64)
    (hx4 : s0.readReg64 .x4 = x.ivA) (hx5 : s0.readReg64 .x5 = 16#64)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hk : x.key.length = 32) (hiv : x.iv.length = 16) (hin : x.input.length < 2 ^ 40)
    (hnext : ∀ (s1 : State) (b : BitVec 8) (ksBytes : List (BitVec 8)),
      let ctLen := (x.input.length / 16 + 1) * 16
      KsStaged b x.key ksBytes →
      s1.pc = fnAddr + 0x0c0#64 → s1.status = .Running → s1.sp = sp →
      CbcPreserved s0 s1 → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      s1.readReg64 (.gpr 0#5) = BitVec.ofNat 64 ctLen →
      s1.readReg64 (.gpr 1#5) = 1#64 →
      s1.readReg64 (.gpr 19#5) = x.ret →
      s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ctLen →
      s1.readReg64 (.gpr 22#5) = x.inA →
      s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length →
      s1.readReg64 (.gpr 24#5) = 1#64 →
      s1.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (16 * (x.input.length / 16)) →
      s1.readReg64 (.gpr 29#5) = sp + 0x10c0#64 →
      SepWP P target_pc s1
        ((cbcSavedRegs s0 ∗ memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x410#64) 960 ∗
          memRegion (sp + 0x7d0#64) 240 ∗ ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)) ∗
          memRegion (sp + 0xc90#64) 960 ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
          (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ b) ∗
          hSplit.base.pool lim st s1 ∗ stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s0
      ((stackFrameAt s0.sp 96 ∗ memRegion (sp + 0x040#64) 976 ∗
        memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
        memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
        memRegion (sp + 0xc90#64) 960 ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
        (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ b0) ∗
        hSplit.base.pool lim st s0 ∗ stackAt sp allocHookStack) ∗ F) post oom := by
  have hsp0_15 : s0.sp &&& 15#64 = 0#64 := sp_and_15_of_spAligned hsp0
  have hsp96_15 : (s0.sp - 96#64) &&& 15#64 = 0#64 := sp_sub96_and_15 hsp0_15
  have hsp4192_15 : (s0.sp - 96#64 - 4096#64) &&& 15#64 = 0#64 := sp_sub4192_and_15 hsp0_15
  have hsp_15 : sp &&& 15#64 = 0#64 := hsp_def ▸ sp_sub4384_and_15 hsp0_15
  have hx1_bv : s0.readReg64 .x1 = BitVec.ofNat 64 x.input.length := u_eq_ofNat_of_lt40 hx1 hin
  have hprobe_addr : s0.sp - 96#64 - 4096#64 = sp + 0x0c0#64 := by rw [← hsp_def]; bv_omega
  rw [stackFrameAt_96_cells s0.sp, memRegion_976_split_probe sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun sv0 => SepWP.exists_elim fun sv1 =>
    SepWP.exists_elim fun sv2 => SepWP.exists_elim fun sv3 =>
    SepWP.exists_elim fun sv4 => SepWP.exists_elim fun sv5 =>
    SepWP.exists_elim fun sv6 => SepWP.exists_elim fun sv7 =>
    SepWP.exists_elim fun sv8 => SepWP.exists_elim fun sv9 =>
    SepWP.exists_elim fun sv10 => SepWP.exists_elim fun sv11 =>
    SepWP.exists_elim fun probeSlot => ?_
  dsimp only [cbcSavedCells]
  have_instrs hc.segProlog 0 12
  wp_stp64 hf_0 m1 hm1; wp_stp64 hf_1 m2 hm2; wp_stp64 hf_2 m3 hm3
  wp_stp64 hf_3 m4 hm4; wp_stp64 hf_4 m5 hm5; wp_stp64 hf_5 m6 hm6
  wp_steps 2; rw [← hprobe_addr]; wp_str64 hf_8 m7 hm7; rw [hprobe_addr]; wp_steps 2
  have hx3_gpr : s0.readReg64 (.gpr 3#5) = 32#64 := hx3
  apply SepWP.step_pure (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun]) hf_11 rfl
    (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
  conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx3_gpr]
  have hf_adrp0 := hc.adrp_st0; wp_step
  have_instrs hc.segSave45 0 2; wp_steps 2
  refine SepWP.step_ldr8 (hpc := by simp [wp_norm, arm64_norm, bv_lin_norm])
    (hrun := by simp [wp_norm, arm64_norm, hrun]) (hfetch := hc.ldrb_st0) (hsp := rfl)
    (haddr := show evalAddrMode _ (.Offset (.gpr 25#5) (pageLo12 hw.storageAddr)) = (hw.storageAddr, none) by
      simp [evalAddrMode, pageLo12, wp_norm, arm64_norm]; try bv_bits)
    (hload := SepLoad8.of_eq (by sep_ac_rfl)) (hexec := rfl) ?_
  have hent_probe :
      (memRegion (sp + 0x040#64) 128 ∗ ((sp + 0x0c0#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x0c8#64) 840) ∗
      (cbcSavedRegs s0 ∗ memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
        memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗ memRegion (sp + 0xc90#64) 960 ∗
        (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
        (hw.storageAddr ↦₈ b0) ∗ hSplit.base.pool lim st s0 ∗ stackAt sp allocHookStack ∗ F) ⊢
      (memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
        memRegion (sp + 0xc90#64) 960 ∗ (x.keyA ↦ₛ x.key) ∗
        (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack) ∗
      ((hw.storageAddr ↦₈ b0) ∗ hSplit.base.pool lim st s0 ∗ cbcSavedRegs s0 ∗
        memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x8c0#64) 960 ∗
        memRegion (sp + 0xc80#64) 16 ∗ (x.ivA ↦ₛ x.iv) ∗ F) := by
    generalize cbcSavedRegs s0 = svRegs
    exact Entails.trans (sepConj_mono_left (memRegion_976_fold_probe sp 0#64)) (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre (Entails.trans ?_ hent_probe) ?_
  · dsimp only [cbcSavedRegs, cbcSavedCells]; exact Entails.of_eq (by sep_ac_rfl)
  have_instrs hc.segDisp0 0 6; wp_steps 4
  have hsp_cur : (s0.sp - 96#64 - 4096#64 - 192#64) = sp := by rw [← hsp_def]; bv_omega
  wp_if hbr1
  · have hb0_eq : b0 = 1#8 := by revert hbr1; simp [wp_norm, arm64_norm]; bv_bits
    subst hb0_eq
    refine step_hw_key_setup (s0 := s0) hc hCallees x
      (by simp [wp_norm, arm64_norm]; try bv_omega) (by simp [wp_norm, arm64_norm, hrun])
      (by rw [← hsp_def]; simp [wp_norm, arm64_norm]; try bv_omega) hsp_15
      (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm7, hm6, hm5, hm4, hm3, hm2, hm1]))
      (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx2]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by rw [← hsp_def]; simp [wp_norm, arm64_norm]; bv_omega) hk
      fun sj ksBytes hks hpcj hrunj hspj hp0j hvj hx19j hx20j hx22j hx23j hx29j => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
        (memRegion (sp + 0x040#64) 976 ∗ ((sp + 0x410#64) ↦ₛ ksBytes) ∗
          memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗ (x.ivA ↦ₛ x.iv)) ∗
        (cbcSavedRegs s0 ∗ memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0xc90#64) 960 ∗
          (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ 1#8) ∗
          hSplit.base.pool lim st s0 ∗ stackAt sp allocHookStack ∗ F) by sep_ac_rfl)) ?_
    refine step_join_to_alloc hc hCallees x hks.1 hpcj hrunj hspj hsp_15 hp0j hvj
      hx19j hx20j hx22j hx23j hx29j hiv hin
      fun sf hpcf hrunf hspf hp0f hvf hx0f hx1f hx19f hx20f hx22f hx23f hx24f hx25f hx29f => ?_
    refine SepWP.weaken_pre ?_
      (hnext sf 1#8 ksBytes hks hpcf hrunf hspf hp0f hvf hx0f hx1f hx19f hx20f hx22f hx23f hx24f hx25f hx29f)
    rw [hp0f.pool_eq hSplit.base lim st]; exact Entails.of_eq (by sep_ac_rfl)
  · have hb0_ne1 : b0 ≠ 1#8 := by intro h; subst h; simp [wp_norm, arm64_norm] at hbr1
    wp_steps 2; wp_if hbrff
    · have hb0_ff : b0 = 0xff#8 := by revert hbrff; simp [wp_norm, arm64_norm]; bv_bits
      subst hb0_ff
      have_instrs hc.segInitSave 0 1; wp_steps 1
      refine step_bl_aesInitInner_allocStack 0xff#8 st hc.bl_init hCallees.initInner_ok
        (by simp [wp_norm, arm64_norm]; try bv_omega) (by simp [wp_norm, arm64_norm, hrun])
        (spAligned_of_eq (by rw [← hsp_def]; simp [wp_norm, arm64_norm]; try bv_omega) hsp_15)
        (F := memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
          memRegion (sp + 0xc90#64) 960 ∗ (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
          cbcSavedRegs s0 ∗ memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x8c0#64) 960 ∗
          memRegion (sp + 0xc80#64) 16 ∗ (x.ivA ↦ₛ x.iv) ∗ F)
        ?_ ?_
      · refine entails_init_pre (s0 := s0) (sp := sp)
          (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hm7, hm6, hm5, hm4, hm3, hm2, hm1]))
          (by rw [← hsp_def]; simp [wp_norm, arm64_norm])
          (Entails.of_eq (by sep_ac_rfl))
      · intro si b hb_or hx0_si hpci hruni hspi hcsi hpi
        rw [BitVec.add_assoc] at hpci; simp only [BitVec.reduceAdd] at hpci
        have hspi' : si.sp = sp := by rw [hspi, ← hsp_def]; simp [wp_norm, arm64_norm]
        have hx19_i : si.readReg64 (.gpr 19#5) = x.ret := by rw [hcsi.readReg64_x19]; simp [wp_norm, arm64_norm]
        have hx20_i : si.readReg64 (.gpr 20#5) = x.ivA := by rw [hcsi.readReg64_x20]; simp [wp_norm, arm64_norm]
        have hx21_i : si.readReg64 (.gpr 21#5) = 16#64 := by rw [hcsi.readReg64_x21]; simp [wp_norm, arm64_norm]
        have hx22_i : si.readReg64 (.gpr 22#5) = x.inA := by rw [hcsi.readReg64_x22]; simp [wp_norm, arm64_norm]
        have hx23_i : si.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length := by
          rw [hcsi.readReg64_x23]; simp [wp_norm, arm64_norm]
        have hx24_i : si.readReg64 (.gpr 24#5) = x.keyA := by rw [hcsi.readReg64_x24]; simp [wp_norm, arm64_norm]
        have hx29_i : si.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by
          rw [hcsi.readReg64_x29, ← hsp_def]; simp [wp_norm, arm64_norm]; bv_omega
        have hvi : calleeSavedVRegs si = calleeSavedVRegs s0 := by
          rw [hcsi.vregs]; simp [calleeSavedVRegs, wp_norm, arm64_norm]
        have hp0i : CbcPreserved s0 si :=
          cbcPreserved_trans_rev (CbcPreserved.of_pure hpi)
            (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm, hm7, hm6, hm5, hm4, hm3, hm2, hm1]))
        rw [hp0i.pool_eq hSplit.base lim st, ← hspi, hspi']
        clear hspi hcsi hpi
        refine SepWP.weaken_pre (Entails.of_eq (show _ =
            (memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
              memRegion (sp + 0xc90#64) 960 ∗ (x.keyA ↦ₛ x.key) ∗
              (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack) ∗
            ((hw.storageAddr ↦₈ b) ∗ hSplit.base.pool lim st s0 ∗ cbcSavedRegs s0 ∗
              memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x8c0#64) 960 ∗
              memRegion (sp + 0xc80#64) 16 ∗ (x.ivA ↦ₛ x.iv) ∗ F) by sep_ac_rfl)) ?_
        have_instrs hc.segInitPost 0 2; wp_steps 1
        have hx0_gpr : si.readReg64 (.gpr 0#5) = b.zeroExtend 64 := hx0_si
        rcases hb_or with rfl | rfl
        · apply SepWP.step_pure (by simp [wp_norm, arm64_norm]; try bv_omega)
            (by simp [wp_norm, arm64_norm, hruni]) hf_1 rfl
            (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
          conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx0_gpr]
          refine step_sw_key_setup (s0 := s0) hc hCallees x (by decide : (0#8 : BitVec 8) ≠ 1#8)
            (by simp [wp_norm, arm64_norm]; try bv_omega)
            (by simp [wp_norm, arm64_norm, hruni]) (by simp [wp_norm, arm64_norm, hspi']) hsp_15
            (hp0i.trans (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl))
            (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hvi)
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx19_i])
            (by simp [wp_norm, arm64_norm, hx20_i]) (by simp [wp_norm, arm64_norm, hx21_i])
            (by simp [wp_norm, arm64_norm, hx22_i]) (by simp [wp_norm, arm64_norm, hx23_i])
            (by simp [wp_norm, arm64_norm, hx29_i]) hk
            fun sj ksBytes hks hpcj hrunj hspj hp0j hvj hx19j hx20j hx22j hx23j hx29j => ?_
          refine SepWP.weaken_pre (Entails.of_eq (show _ =
              (memRegion (sp + 0x040#64) 976 ∗ ((sp + 0x410#64) ↦ₛ ksBytes) ∗
                memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗ (x.ivA ↦ₛ x.iv)) ∗
              (cbcSavedRegs s0 ∗ memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0xc90#64) 960 ∗
                (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ 0#8) ∗
                hSplit.base.pool lim st s0 ∗ stackAt sp allocHookStack ∗ F) by sep_ac_rfl)) ?_
          refine step_join_to_alloc hc hCallees x hks.1 hpcj hrunj hspj hsp_15 hp0j hvj
            hx19j hx20j hx22j hx23j hx29j hiv hin
            fun sf hpcf hrunf hspf hp0f hvf hx0f hx1f hx19f hx20f hx22f hx23f hx24f hx25f hx29f => ?_
          refine SepWP.weaken_pre ?_
            (hnext sf 0#8 ksBytes hks hpcf hrunf hspf hp0f hvf hx0f hx1f hx19f hx20f hx22f hx23f hx24f hx25f hx29f)
          rw [hp0f.pool_eq hSplit.base lim st]; exact Entails.of_eq (by sep_ac_rfl)
        · apply SepWP.step_pure (by simp [wp_norm, arm64_norm]; try bv_omega)
            (by simp [wp_norm, arm64_norm, hruni]) hf_1 rfl
            (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
          conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx0_gpr]
          refine step_hw_key_setup (s0 := s0) hc hCallees x
            (by simp [wp_norm, arm64_norm]; try bv_omega)
            (by simp [wp_norm, arm64_norm, hruni]) (by simp [wp_norm, arm64_norm, hspi']) hsp_15
            (hp0i.trans (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl))
            (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hvi)
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx19_i])
            (by simp [wp_norm, arm64_norm, hx20_i]) (by simp [wp_norm, arm64_norm, hx21_i])
            (by simp [wp_norm, arm64_norm, hx22_i]) (by simp [wp_norm, arm64_norm, hx23_i])
            (by simp [wp_norm, arm64_norm, hx29_i]) hk
            fun sj ksBytes hks hpcj hrunj hspj hp0j hvj hx19j hx20j hx22j hx23j hx29j => ?_
          refine SepWP.weaken_pre (Entails.of_eq (show _ =
              (memRegion (sp + 0x040#64) 976 ∗ ((sp + 0x410#64) ↦ₛ ksBytes) ∗
                memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗ (x.ivA ↦ₛ x.iv)) ∗
              (cbcSavedRegs s0 ∗ memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0xc90#64) 960 ∗
                (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ 1#8) ∗
                hSplit.base.pool lim st s0 ∗ stackAt sp allocHookStack ∗ F) by sep_ac_rfl)) ?_
          refine step_join_to_alloc hc hCallees x hks.1 hpcj hrunj hspj hsp_15 hp0j hvj
            hx19j hx20j hx22j hx23j hx29j hiv hin
            fun sf hpcf hrunf hspf hp0f hvf hx0f hx1f hx19f hx20f hx22f hx23f hx24f hx25f hx29f => ?_
          refine SepWP.weaken_pre ?_
            (hnext sf 1#8 ksBytes hks hpcf hrunf hspf hp0f hvf hx0f hx1f hx19f hx20f hx22f hx23f hx24f hx25f hx29f)
          rw [hp0f.pool_eq hSplit.base lim st]; exact Entails.of_eq (by sep_ac_rfl)
    · refine step_sw_key_setup (s0 := s0) hc hCallees x hb0_ne1
        (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun]) (by rw [← hsp_def]; simp [wp_norm, arm64_norm]; try bv_omega) hsp_15
        (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hm7, hm6, hm5, hm4, hm3, hm2, hm1]))
        (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx2]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by rw [← hsp_def]; simp [wp_norm, arm64_norm]; bv_omega) hk
        fun sj ksBytes hks hpcj hrunj hspj hp0j hvj hx19j hx20j hx22j hx23j hx29j => ?_
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
          (memRegion (sp + 0x040#64) 976 ∗ ((sp + 0x410#64) ↦ₛ ksBytes) ∗
            memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗ (x.ivA ↦ₛ x.iv)) ∗
          (cbcSavedRegs s0 ∗ memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0xc90#64) 960 ∗
            (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ b0) ∗
            hSplit.base.pool lim st s0 ∗ stackAt sp allocHookStack ∗ F) by sep_ac_rfl)) ?_
      refine step_join_to_alloc hc hCallees x hks.1 hpcj hrunj hspj hsp_15 hp0j hvj
        hx19j hx20j hx22j hx23j hx29j hiv hin
        fun sf hpcf hrunf hspf hp0f hvf hx0f hx1f hx19f hx20f hx22f hx23f hx24f hx25f hx29f => ?_
      refine SepWP.weaken_pre ?_
        (hnext sf b0 ksBytes hks hpcf hrunf hspf hp0f hvf hx0f hx1f hx19f hx20f hx22f hx23f hx24f hx25f hx29f)
      rw [hp0f.pool_eq hSplit.base lim st]; exact Entails.of_eq (by sep_ac_rfl)

private theorem sepWP_done_let {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (h : ∀ sm, sm = s → sm.pc = mid → sm.status = .Running → SepWPp prog ret sm P Q Qp oom) :
    SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp oom) oom :=
  SepWP.done hpc hrun (h s rfl hpc hrun)

theorem cbc_panic_tail {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hHandleErr : subroutine_ok P handleErrorAddr rustHandleErrorPanicSpec)
    (x : AesCall) (st : M.σ) (Rest F0 R : SepProp) {Q : State → SepProp → Prop} (s0 sf2 : State)
    (hna : NullAllowed ((x.input.length / 16 + 1) * 16) 1)
    (hsp0 : s0.spAligned = true) (hpc2 : sf2.pc = fnAddr + 0x0c4#64)
    (hrun2 : sf2.status = .Running) (hsp2 : sf2.sp = s0.sp - 4384#64)
    (hx0_0 : sf2.readReg64 .x0 = 0#64)
    (hfs2 : sf2.fs = s0.fs) (htr2 : sf2.trace = s0.trace) :
    SepWPp P (s0.readReg64 .lr) sf2
      (stackAt (s0.sp - 4384#64) allocHookStack ∗ Rest) Q
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ (F0 ∗ R)) →
          (sf.mem ⊨ (aesEncBudgetCondSpec Spec.Aes256.aes256Enc M A lim).onPanic (x, st) s0 sf ∗ R))
      (fun sf => ⌜¬ FitsEvents M lim st (aesEncEvents x) ∧ OomPreserved s0 sf⌝) := by
  have hsp_15 : (s0.sp - 4384#64) &&& 15#64 = 0#64 := sp_sub4384_and_15 (sp_and_15_of_spAligned hsp0)
  rw [allocHookStack_split_16 (s0.sp - 4384#64)]
  apply SepWPp.of_sepWP (mid := handleErrorAddr)
  have_instrs hc.segPostAlloc 0 1
  have_instrs hc.segPanicArgs 0 2
  have hf_bl := hc.bl_handleErr
  wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun2]) fun sm_pan hsm hpc_pan hrun_pan => ?_
  have hsp_pan : sm_pan.sp = s0.sp - 4384#64 := by rw [hsm]; simp [arm64_norm, hsp2]
  have hfs_pan : sm_pan.fs = s0.fs := by rw [hsm]; simp [arm64_norm, hfs2]
  have htr_pan : sm_pan.trace = s0.trace := by rw [hsm]; simp [arm64_norm, htr2]
  clear hsm
  refine SepWPp.call (x := ()) (ret_pc := sm_pan.readReg64 .lr)
    (F := stackFrameAt (s0.sp - 4384#64 - 16#64) 4080 ∗ Rest)
    hHandleErr hpc_pan hrun_pan (spAligned_of_eq hsp_pan hsp_15) rfl ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex) ?_
    (fun _ _ _ _ _ => by
      dsimp only [rustHandleErrorPanicSpec]; exact SepWPp.pure_elim fun h => False.elim h)
    (fun _ _ _ ho => by
      dsimp only [rustHandleErrorPanicSpec] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  · intro R' hm'; dsimp only [rustHandleErrorPanicSpec]; rw [hsp_pan]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'
  · intro sf_pan _ hmp; dsimp only [rustHandleErrorPanicSpec, aesEncBudgetCondSpec] at hmp ⊢
    have hPull :
        ((⌜sf_pan.fs = sm_pan.fs ∧ sf_pan.trace = sm_pan.trace⌝ ∗ anyHeap) ∗
          (stackFrameAt (s0.sp - 4384#64 - 16#64) 4080 ∗ Rest)) ∗ (F0 ∗ R) =
        ⌜sf_pan.fs = sm_pan.fs ∧ sf_pan.trace = sm_pan.trace⌝ ∗
          ((anyHeap ∗ stackFrameAt (s0.sp - 4384#64 - 16#64) 4080 ∗ Rest ∗ F0) ∗ R) := by sep_ac_rfl
    rw [hPull, satisfies_pure_sepConj] at hmp; rcases hmp with ⟨⟨hfsp, htrp⟩, hrest⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hna, hfsp.trans hfs_pan, htrp.trans htr_pan⟩,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hrest⟩

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.PreAlloc

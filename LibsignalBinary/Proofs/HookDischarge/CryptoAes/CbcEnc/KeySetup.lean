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
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers
import ProofLib.BV
import Arm64.Trusted.ISA.Eval
import VerifiedLibraries.Mallocng.Proofs.PlacedReallocHelpers
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Hardware & Software Key-Schedule Setup (`+0x7d8..+0x890` & `+0x058..+0x078`) (`CbcEnc.KeySetup`)

Verifies both `STORAGE == 1` (`expand_key::<32, 15>`, `inv_expanded_keys::<15>`, 15 `ldr q / str q`,
`memcpy`×2) and `STORAGE != 1` (`Fixslice64.aes256KeySchedule`, `memcpy`) converging at `+0x07c`
under the unified `KsStaged` invariant.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.KeySetup

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open VerifiedLibraries.Mallocng.Proofs (memRegion_entails_exists_pointsToBytes)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (aes256KeyScheduleFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (fsKeys256At fsKeys256Bytes fsKeys256Bytes_length fsKeys256At_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule (aes256KeyScheduleSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (aesRconBytes armv8ExpandKey armv8InvExpandedKeys roundKeys15Bytes roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeySchedule (expandKey15RegionSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (invExpandedKeys15RegionSpec roundKeys15Bytes_length roundKeys15At_eq_pointsToBytes
   roundKeys15At_entails_memRegion memRegion240_eq_exists_roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
  (Aes256EncHwAddrs CbcEncCode Aes256CbcEncryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
  (CbcPreserved spAligned_of_eq allocHookStack_split_1120 allocHookStack_split_256 CbcKeyState)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers (step_bl_cbc)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand.Simp
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

/-! ## 1. Unified Key-Schedule Staging Invariant (`KsStaged`) -/

@[expose] def KsStaged (b : BitVec 8) (key ksBytes : List (BitVec 8)) : Prop :=
  ksBytes.length = 960 ∧
  if b == 1#8 then ksBytes.take 240 = roundKeys15Bytes (armv8ExpandKey key)
  else ksBytes = fsKeys256Bytes (aes256KeyScheduleFs key)

theorem pointsToBytes_entails_cbcKeyState {sp : BitVec 64} {b : BitVec 8}
    {key ksBytes : List (BitVec 8)} (hks : KsStaged b key ksBytes) :
    ((sp + 0xc90#64) ↦ₛ ksBytes) ⊢ CbcKeyState sp b key := by
  rcases hks with ⟨hlen, hbody⟩; unfold CbcKeyState
  by_cases hb : (b == 1#8) = true
  · simp only [hb, ↓reduceIte] at hbody ⊢
    have haddr : sp + 0xc90#64 + BitVec.ofNat 64 240 = sp + 0xd80#64 := by
      simp only [BitVec.add_assoc]; rfl
    rw [← List.take_append_drop 240 ksBytes, pointsToBytes_append, hbody,
        roundKeys15Bytes_length, haddr, ← roundKeys15At_eq_pointsToBytes]
    have hdlen : (ksBytes.drop 240).length = 720 := by rw [List.length_drop, hlen]
    have hmr := pointsToBytes_entails_memRegion (sp + 0xd80#64) (ksBytes.drop 240)
    rw [hdlen] at hmr
    exact sepConj_mono_right (P := roundKeys15At (sp + 0xc90#64) (armv8ExpandKey key)) hmr
  · simp only [Bool.not_eq_true _ ▸ hb, Bool.false_eq_true, ↓reduceIte] at hbody ⊢
    rw [hbody, ← fsKeys256At_eq_pointsToBytes]; exact Entails.refl _

section
arm64_proof_prelude
attribute [local irreducible] armv8ExpandKey armv8InvExpandedKeys

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

/-! ## 2. Hardware Key-Schedule Copy & Setup (`+0x7d8..+0x890 -> +0x07c`) -/

private theorem step_hw_copy_ek {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    {ek oldEk : Vector (BitVec 128) 15} {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x7f4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_15 : sp &&& 15#64 = 0#64)
    (hp0 : CbcPreserved s0 s) (hv0 : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x878#64 → sf.status = .Running → sf.sp = sp →
      CbcPreserved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 (.gpr 0#5) = sp + 0x410#64 →
      sf.readReg64 (.gpr 1#5) = sp + 0xc90#64 →
      sf.readReg64 (.gpr 2#5) = 480#64 →
      (∀ r : BitVec 5, 19 ≤ r.toNat → r.toNat ≤ 30 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      SepWP P target_pc sf
        ((roundKeys15At (sp + 0x7d0#64) ek ∗ roundKeys15At (sp + 0xc90#64) ek) ∗ F) post oom) :
    SepWP P target_pc s
      ((roundKeys15At (sp + 0x7d0#64) ek ∗ roundKeys15At (sp + 0xc90#64) oldEk) ∗ F) post oom := by
  have hsp_and : s.sp &&& 15#64 = 0#64 := hsp ▸ hsp_15
  have hsp_reg : s.readReg64 .sp = sp := hsp
  have_instrs hc.segHwCopyEk 0 33
  dsimp only [roundKeys15At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_ldr128 hf_0; wp_ldr128 hf_1; wp_steps 1; wp_ldr128 hf_3; wp_steps 2
  wp_str128 hf_6 m0 hm0; wp_ldr128 hf_7; wp_str128 hf_8 m1 hm1; wp_ldr128 hf_9
  wp_str128 hf_10 m2 hm2; wp_ldr128 hf_11; wp_str128 hf_12 m3 hm3; wp_ldr128 hf_13
  wp_str128 hf_14 m4 hm4; wp_ldr128 hf_15; wp_str128 hf_16 m5 hm5; wp_ldr128 hf_17
  wp_str128 hf_18 m6 hm6; wp_ldr128 hf_19; wp_str128 hf_20 m7 hm7; wp_ldr128 hf_21
  wp_str128 hf_22 m8 hm8; wp_ldr128 hf_23; wp_str128 hf_24 m9 hm9; wp_ldr128 hf_25
  wp_str128 hf_26 m10 hm10; wp_ldr128 hf_27; wp_str128 hf_28 m11 hm11; wp_ldr128 hf_29
  wp_str128 hf_30 m12 hm12; wp_str128 hf_31 m13 hm13; wp_str128 hf_32 m14 hm14
  refine SepWP.weaken_pre ?_
    (hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hsp])
      (hp0.trans (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6,
          hm5, hm4, hm3, hm2, hm1, hm0])))
      (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv0)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (fun r hr19 _ => by
        have hne0 : r ≠ 0#5 := by intro h; subst h; simp at hr19
        have hne1 : r ≠ 1#5 := by intro h; subst h; simp at hr19
        have hne2 : r ≠ 2#5 := by intro h; subst h; simp at hr19
        simp [wp_norm, arm64_norm, hne0, hne1, hne2]))
  dsimp only [roundKeys15At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.refl _

attribute [local irreducible] roundKeys15At aesRconBytes

theorem step_hw_key_setup {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x7d8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_15 : sp &&& 15#64 = 0#64)
    (hp0 : CbcPreserved s0 s) (hv0 : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx2 : s.readReg64 (.gpr 2#5) = x.keyA) (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = x.ivA) (hx21 : s.readReg64 (.gpr 21#5) = 16#64)
    (hx22 : s.readReg64 (.gpr 22#5) = x.inA)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length)
    (hx29 : s.readReg64 (.gpr 29#5) = sp + 0x10c0#64) (hk : x.key.length = 32)
    (hnext : ∀ (sf : State) (ksBytes : List (BitVec 8)),
      KsStaged 1#8 x.key ksBytes →
      sf.pc = fnAddr + 0x07c#64 → sf.status = .Running → sf.sp = sp →
      CbcPreserved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 (.gpr 19#5) = x.ret → sf.readReg64 (.gpr 20#5) = x.ivA →
      sf.readReg64 (.gpr 22#5) = x.inA →
      sf.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length →
      sf.readReg64 (.gpr 29#5) = sp + 0x10c0#64 →
      SepWP P target_pc sf
        ((((sp + 0x410#64) ↦ₛ ksBytes) ∗ memRegion (sp + 0x7d0#64) 240 ∗
          memRegion (sp + 0xc90#64) 960 ∗ (x.keyA ↦ₛ x.key) ∗
          (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s
      ((memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
        memRegion (sp + 0xc90#64) 960 ∗ (x.keyA ↦ₛ x.key) ∗
        (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack) ∗ F) post oom := by
  have hsp_reg : s.readReg64 .sp = sp := hsp
  have_instrs hc.segHwKsArgs 0 2; wp_steps 2
  refine step_bl_cbc hc.bl_hwExp hCallees.expandKey_ok
    (false, true, sp + 0x7d0#64, x.keyA, x.key)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp]) hsp_15)
    (F := memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0xc90#64) 960 ∗
      stackFrameAt (sp - 0x100#64) 3840 ∗ F)
    (PreSpatial := memRegion (sp + 0x7d0#64) 240 ∗ bytesAt false x.keyA x.key ∗
      bytesAt true hw.rconAddr aesRconBytes ∗ stackFrameAt sp 0x100)
    (PostSpatial := roundKeys15At (sp + 0x7d0#64) (armv8ExpandKey x.key) ∗
      (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackFrameAt sp 0x100)
    ?_ ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
  · simp only [bytesAt, Bool.false_eq_true, ↓reduceIte, allocHookStack_split_256 sp]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s_c hsc; dsimp only [expandKey15RegionSpec]
    have hx0c : s_c.readReg64 .x0 = sp + 0x7d0#64 := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
    have hx1c : s_c.readReg64 .x1 = x.keyA := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
    have hspc : s_c.sp = sp := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hsp]
    rw [hspc]; exact Entails.pure_right ⟨hx0c, hx1c, hk⟩ (Entails.refl _)
  · intro s_c _ hsc _; dsimp only [expandKey15RegionSpec, bytesAt]
    have hspc : s_c.sp = sp := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hsp]
    rw [hspc]; exact Entails.pure_left fun ⟨hp, _⟩ => Entails.pure_right (CbcPreserved.of_pure hp) (Entails.refl _)
  · intro s1 hpc1 hrun1 hsp1 hcs1 hp1
    rw [BitVec.add_assoc] at hpc1; simp only [BitVec.reduceAdd] at hpc1
    have hsp1' : s1.sp = sp := by rw [hsp1]; simp [wp_norm, arm64_norm, hsp]
    have hsp1_reg : s1.readReg64 .sp = sp := hsp1'
    have hx19_1 : s1.readReg64 (.gpr 19#5) = x.ret := by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm, hx19]
    have hx20_1 : s1.readReg64 (.gpr 20#5) = x.ivA := by rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm, hx20]
    have hx21_1 : s1.readReg64 (.gpr 21#5) = 16#64 := by rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm, hx21]
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
    refine SepWP.weaken_pre (P' :=
        (roundKeys15At (sp + 0x7d0#64) (armv8ExpandKey x.key) ∗ (x.keyA ↦ₛ x.key) ∗
          (hw.rconAddr ↦ᵣ aesRconBytes) ∗ memRegion (sp + 0x410#64) 960 ∗
          memRegion (sp + 0xc90#64) 960 ∗ stackAt sp allocHookStack) ∗ F)
      (by rw [allocHookStack_split_256 sp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    have_instrs hc.segHwInvArgs 0 3; wp_steps 3
    let ek := armv8ExpandKey x.key
    refine step_bl_cbc hc.bl_hwInv hCallees.invExpandedKeys_ok
      (sp + 0xd80#64, sp + 0x7d0#64, ek)
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp1']) hsp_15)
      (F := memRegion (sp + 0xc90#64) 240 ∗ memRegion (sp + 0xe70#64) 480 ∗
        memRegion (sp + 0x410#64) 960 ∗ (x.keyA ↦ₛ x.key) ∗
        (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ F)
      (PreSpatial := memRegion (sp + 0xd80#64) 240 ∗ roundKeys15At (sp + 0x7d0#64) ek)
      (PostSpatial := roundKeys15At (sp + 0xd80#64) (armv8InvExpandedKeys ek) ∗
        roundKeys15At (sp + 0x7d0#64) ek)
      ?_ ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
    · rw [show (960 : Nat) = 240 + (240 + 480) from rfl,
          memRegion_split (sp + 0xc90#64) 240 720 (by decide),
          memRegion_split _ 240 480 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by sep_ac_rfl)
    · intro s_c hsc; dsimp only [invExpandedKeys15RegionSpec]
      have hx0c : s_c.readReg64 .x0 = sp + 0xd80#64 := by
        rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
      have hx1c : s_c.readReg64 .x1 = sp + 0x7d0#64 := by
        rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
      exact Entails.pure_right ⟨hx0c, hx1c⟩ (Entails.refl _)
    · intro _ _ _ _; dsimp only [invExpandedKeys15RegionSpec]
      exact Entails.pure_left fun ⟨hp, _⟩ => Entails.pure_right (CbcPreserved.of_pure hp) (Entails.refl _)
    · intro s2 hpc2 hrun2 hsp2 hcs2 hp2
      rw [BitVec.add_assoc] at hpc2; simp only [BitVec.reduceAdd] at hpc2
      have hsp2' : s2.sp = sp := by rw [hsp2]; simp [wp_norm, arm64_norm, hsp1']
      have hx19_2 : s2.readReg64 (.gpr 19#5) = x.ret := by rw [hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_1]
      have hx20_2 : s2.readReg64 (.gpr 20#5) = x.ivA := by rw [hcs2.readReg64_x20]; simp [wp_norm, arm64_norm, hx20_1]
      have hx21_2 : s2.readReg64 (.gpr 21#5) = 16#64 := by rw [hcs2.readReg64_x21]; simp [wp_norm, arm64_norm, hx21_1]
      have hx22_2 : s2.readReg64 (.gpr 22#5) = x.inA := by rw [hcs2.readReg64_x22]; simp [wp_norm, arm64_norm, hx22_1]
      have hx23_2 : s2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length := by
        rw [hcs2.readReg64_x23]; simp [wp_norm, arm64_norm, hx23_1]
      have hx29_2 : s2.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by
        rw [hcs2.readReg64_x29]; simp [wp_norm, arm64_norm, hx29_1]
      have hv2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
        rw [hcs2.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv1
      have hp02 : CbcPreserved s0 s2 :=
        hp01.trans ((CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl).trans hp2)
      clear hsp2 hcs2 hp2
      rw [memRegion240_eq_exists_roundKeys15At (sp + 0xc90#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWP.exists_elim fun oldEk => ?_
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
          (roundKeys15At (sp + 0x7d0#64) ek ∗ roundKeys15At (sp + 0xc90#64) oldEk) ∗
          (roundKeys15At (sp + 0xd80#64) (armv8InvExpandedKeys ek) ∗ memRegion (sp + 0xe70#64) 480 ∗
            memRegion (sp + 0x410#64) 960 ∗ (x.keyA ↦ₛ x.key) ∗
            (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ F) by sep_ac_rfl)) ?_
      refine step_hw_copy_ek hc hpc2 hrun2 hsp2' hsp_15 hp02 hv2
        fun s3 hpc3 hrun3 hsp3 hp03 hv3 hx0_3 hx1_3 hx2_3 hcal3 => ?_
      let pair480 := roundKeys15Bytes ek ++ roundKeys15Bytes (armv8InvExpandedKeys ek)
      have hpair_len : pair480.length = 480 := by
        dsimp [pair480]; rw [List.length_append, roundKeys15Bytes_length, roundKeys15Bytes_length]
      refine step_bl_cbc hc.bl_hwMc1 hCallees.memcpy_ok
        (sp + 0x410#64, sp + 0xc90#64, pair480)
        hpc3 hrun3 (spAligned_of_eq hsp3 hsp_15)
        (F := memRegion (sp + 0x5f0#64) 480 ∗ memRegion (sp + 0x7d0#64) 240 ∗
          memRegion (sp + 0xe70#64) 480 ∗ (x.keyA ↦ₛ x.key) ∗
          (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ F)
        (PreSpatial := memRegion (sp + 0x410#64) 480 ∗ ((sp + 0xc90#64) ↦ₛ pair480))
        (PostSpatial := ((sp + 0x410#64) ↦ₛ pair480) ∗ memRegion (sp + 0xc90#64) 480)
        ?_ ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
      · have hcat : roundKeys15At (sp + 0xc90#64) ek ∗
            roundKeys15At (sp + 0xd80#64) (armv8InvExpandedKeys ek) = ((sp + 0xc90#64) ↦ₛ pair480) := by
          dsimp [pair480]
          rw [roundKeys15At_eq_pointsToBytes, roundKeys15At_eq_pointsToBytes, pointsToBytes_append,
              roundKeys15Bytes_length]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
        rw [show (960 : Nat) = 480 + 480 from rfl, memRegion_split (sp + 0x410#64) 480 480 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        refine Entails.trans (sepConj_mono_left (sepConj_mono_left (roundKeys15At_entails_memRegion _ _))) ?_
        have hrearr :
            (memRegion (sp + 0x7d0#64) 240 ∗ roundKeys15At (sp + 0xc90#64) ek) ∗
              (roundKeys15At (sp + 0xd80#64) (armv8InvExpandedKeys ek) ∗ memRegion (sp + 0xe70#64) 480 ∗
                (memRegion (sp + 0x410#64) 480 ∗ memRegion (sp + 0x5f0#64) 480) ∗ (x.keyA ↦ₛ x.key) ∗
                (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ F) =
            (memRegion (sp + 0x410#64) 480 ∗
              (roundKeys15At (sp + 0xc90#64) ek ∗ roundKeys15At (sp + 0xd80#64) (armv8InvExpandedKeys ek))) ∗
              (memRegion (sp + 0x5f0#64) 480 ∗ memRegion (sp + 0x7d0#64) 240 ∗
                memRegion (sp + 0xe70#64) 480 ∗ (x.keyA ↦ₛ x.key) ∗
                (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ F) := by sep_ac_rfl
        rw [hrearr, hcat]; exact Entails.refl _
      · intro s_c hsc; dsimp only [allocMemcpyVmSpec]; rw [hpair_len]
        have hx0c : s_c.readReg64 .x0 = sp + 0x410#64 := by
          rw [hsc]; simpa [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx0_3
        have hx1c : s_c.readReg64 .x1 = sp + 0xc90#64 := by
          rw [hsc]; simpa [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx1_3
        have hx2c : s_c.readReg64 .x2 = 480#64 := by
          rw [hsc]; simpa [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx2_3
        exact Entails.pure_right ⟨hx0c, hx1c, hx2c, by decide⟩ (Entails.refl _)
      · intro _ _ _ _; dsimp only [allocMemcpyVmSpec]
        refine Entails.pure_left fun ⟨_, hacp, hvm⟩ => Entails.pure_right ⟨hacp, hvm⟩ ?_
        refine sepConj_mono_right ?_; rw [← hpair_len]; exact pointsToBytes_entails_memRegion _ _
      · intro s4 hpc4 hrun4 hsp4 hcs4 hp4
        rw [BitVec.add_assoc] at hpc4; simp only [BitVec.reduceAdd] at hpc4
        have hsp4' : s4.sp = sp := hsp4.trans hsp3
        have hsp4_reg : s4.readReg64 .sp = sp := hsp4'
        have hx19_4 : s4.readReg64 (.gpr 19#5) = x.ret := by
          rw [hcs4.readReg64_x19, hcal3 19#5 (by decide) (by decide), hx19_2]
        have hx20_4 : s4.readReg64 (.gpr 20#5) = x.ivA := by
          rw [hcs4.readReg64_x20, hcal3 20#5 (by decide) (by decide), hx20_2]
        have hx21_4 : s4.readReg64 (.gpr 21#5) = 16#64 := by
          rw [hcs4.readReg64_x21, hcal3 21#5 (by decide) (by decide), hx21_2]
        have hx22_4 : s4.readReg64 (.gpr 22#5) = x.inA := by
          rw [hcs4.readReg64_x22, hcal3 22#5 (by decide) (by decide), hx22_2]
        have hx23_4 : s4.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length := by
          rw [hcs4.readReg64_x23, hcal3 23#5 (by decide) (by decide), hx23_2]
        have hx29_4 : s4.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by
          rw [hcs4.readReg64_x29, hcal3 29#5 (by decide) (by decide), hx29_2]
        have hv4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := (hcs4.vregs ▸ hv3)
        have hp04 : CbcPreserved s0 s4 := hp03.trans hp4
        clear hsp4 hcs4 hp4
        refine SepWP.weaken_pre
          (sepConj_mono_right (sepConj_mono_left (memRegion_entails_exists_pointsToBytes 480 (sp + 0x5f0#64) (by decide)))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWP.exists_elim fun pad480 => ?_
        rw [show (((sp + 0x410#64) ↦ₛ pair480) ∗ memRegion (sp + 0xc90#64) 480) ∗
              ((⌜pad480.length = 480⌝ ∗ ((sp + 0x5f0#64) ↦ₛ pad480)) ∗
                memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0xe70#64) 480 ∗
                (x.keyA ↦ₛ x.key) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ F) =
            ⌜pad480.length = 480⌝ ∗
              ((((sp + 0x410#64) ↦ₛ pair480) ∗ ((sp + 0x5f0#64) ↦ₛ pad480)) ∗
                (memRegion (sp + 0xc90#64) 480 ∗ memRegion (sp + 0xe70#64) 480) ∗
                memRegion (sp + 0x7d0#64) 240 ∗ (x.keyA ↦ₛ x.key) ∗
                (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ F) by sep_ac_rfl]
        apply SepWP.pure_elim; intro hpad_len
        let ksBytes := pair480 ++ pad480
        have hks_len : ksBytes.length = 960 := by dsimp [ksBytes]; rw [List.length_append, hpair_len, hpad_len]
        have hks_staged : KsStaged 1#8 x.key ksBytes := by
          refine ⟨hks_len, ?_⟩; simp only [beq_self_eq_true, ↓reduceIte]; dsimp [ksBytes, pair480]
          rw [List.append_assoc, List.take_append_of_le_length (by rw [roundKeys15Bytes_length]),
              List.take_of_length_le (by rw [roundKeys15Bytes_length])]
        have hcat960 : ((sp + 0x410#64) ↦ₛ pair480) ∗ ((sp + 0x5f0#64) ↦ₛ pad480) =
            ((sp + 0x410#64) ↦ₛ ksBytes) := by
          dsimp only [ksBytes]
          rw [pointsToBytes_append (sp + 0x410#64) pair480 pad480, hpair_len]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
        have hmr960 : memRegion (sp + 0xc90#64) 480 ∗ memRegion (sp + 0xe70#64) 480 =
            memRegion (sp + 0xc90#64) 960 := by
          rw [show (960 : Nat) = 480 + 480 from rfl, memRegion_split (sp + 0xc90#64) 480 480 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
        rw [hcat960, hmr960]
        have_instrs hc.segHwMc2Args 0 3; wp_steps 3
        refine step_bl_cbc hc.bl_hwMc2 hCallees.memcpy_ok
          (sp + 0xc90#64, sp + 0x410#64, ksBytes)
          (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun4])
          (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp4']) hsp_15)
          (F := memRegion (sp + 0x7d0#64) 240 ∗ (x.keyA ↦ₛ x.key) ∗
            (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ F)
          (PreSpatial := memRegion (sp + 0xc90#64) 960 ∗ ((sp + 0x410#64) ↦ₛ ksBytes))
          (PostSpatial := memRegion (sp + 0xc90#64) 960 ∗ ((sp + 0x410#64) ↦ₛ ksBytes))
          (Entails.of_eq (by sep_ac_rfl)) ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
        · intro s_c hsc; dsimp only [allocMemcpyVmSpec]; rw [hks_len]
          have hx0c : s_c.readReg64 .x0 = sp + 0xc90#64 := by
            rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
          have hx1c : s_c.readReg64 .x1 = sp + 0x410#64 := by
            rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
          have hx2c : s_c.readReg64 .x2 = 960#64 := by
            rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
          exact Entails.pure_right ⟨hx0c, hx1c, hx2c, by decide⟩ (Entails.refl _)
        · intro _ _ _ _; dsimp only [allocMemcpyVmSpec]
          refine Entails.pure_left fun ⟨_, hacp, hvm⟩ => Entails.pure_right ⟨hacp, hvm⟩ ?_
          refine sepConj_mono_left ?_; rw [← hks_len]; exact pointsToBytes_entails_memRegion _ _
        · intro s5 hpc5 hrun5 hsp5 hcs5 hp5
          rw [BitVec.add_assoc] at hpc5; simp only [BitVec.reduceAdd] at hpc5
          have hsp5' : s5.sp = sp := by rw [hsp5]; simp [wp_norm, arm64_norm, hsp4']
          have hx19_5 : s5.readReg64 (.gpr 19#5) = x.ret := by rw [hcs5.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_4]
          have hx20_5 : s5.readReg64 (.gpr 20#5) = x.ivA := by rw [hcs5.readReg64_x20]; simp [wp_norm, arm64_norm, hx20_4]
          have hx21_5 : s5.readReg64 (.gpr 21#5) = 16#64 := by rw [hcs5.readReg64_x21]; simp [wp_norm, arm64_norm, hx21_4]
          have hx22_5 : s5.readReg64 (.gpr 22#5) = x.inA := by rw [hcs5.readReg64_x22]; simp [wp_norm, arm64_norm, hx22_4]
          have hx23_5 : s5.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length := by
            rw [hcs5.readReg64_x23]; simp [wp_norm, arm64_norm, hx23_4]
          have hx29_5 : s5.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by
            rw [hcs5.readReg64_x29]; simp [wp_norm, arm64_norm, hx29_4]
          have hv5 : calleeSavedVRegs s5 = calleeSavedVRegs s0 := by
            rw [hcs5.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv4
          have hp05 : CbcPreserved s0 s5 :=
            hp04.trans ((CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl).trans hp5)
          clear hsp5 hcs5 hp5
          have_instrs hc.segHwIvChk 0 2; wp_steps 1
          apply SepWP.step_pure (by simp [wp_norm, arm64_norm, bv_lin_norm])
            (by simp [wp_norm, arm64_norm, hrun5]) hf_1 rfl
            (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
          conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx21_5]
          refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (hnext _ ksBytes hks_staged
              (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm, hrun5]) (by simp [wp_norm, arm64_norm, hsp5'])
              (hp05.trans (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl))
              (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv5)
              (by simp [wp_norm, arm64_norm, hx19_5]) (by simp [wp_norm, arm64_norm, hx20_5])
              (by simp [wp_norm, arm64_norm, hx22_5]) (by simp [wp_norm, arm64_norm, hx23_5])
              (by simp [wp_norm, arm64_norm, hx29_5]))

/-! ## 3. Software Key-Schedule Setup (`+0x058..+0x078 -> +0x07c`) -/

theorem step_sw_key_setup {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) {b : BitVec 8} (hb : b ≠ 1#8) {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x058#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_15 : sp &&& 15#64 = 0#64)
    (hp0 : CbcPreserved s0 s) (hv0 : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx2 : s.readReg64 (.gpr 2#5) = x.keyA) (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = x.ivA) (hx21 : s.readReg64 (.gpr 21#5) = 16#64)
    (hx22 : s.readReg64 (.gpr 22#5) = x.inA)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length)
    (hx29 : s.readReg64 (.gpr 29#5) = sp + 0x10c0#64) (hk : x.key.length = 32)
    (hnext : ∀ (sf : State) (ksBytes : List (BitVec 8)),
      KsStaged b x.key ksBytes →
      sf.pc = fnAddr + 0x07c#64 → sf.status = .Running → sf.sp = sp →
      CbcPreserved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 (.gpr 19#5) = x.ret → sf.readReg64 (.gpr 20#5) = x.ivA →
      sf.readReg64 (.gpr 22#5) = x.inA →
      sf.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length →
      sf.readReg64 (.gpr 29#5) = sp + 0x10c0#64 →
      SepWP P target_pc sf
        ((((sp + 0x410#64) ↦ₛ ksBytes) ∗ memRegion (sp + 0x7d0#64) 240 ∗
          memRegion (sp + 0xc90#64) 960 ∗ (x.keyA ↦ₛ x.key) ∗
          (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s
      ((memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
        memRegion (sp + 0xc90#64) 960 ∗ (x.keyA ↦ₛ x.key) ∗
        (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack) ∗ F) post oom := by
  have hsp_reg : s.readReg64 .sp = sp := hsp
  have_instrs hc.segSwKsPre 0 2; wp_steps 2
  refine step_bl_cbc hc.bl_ks hCallees.keySchedule_ok
    (false, sp + 0x410#64, x.keyA, x.key)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp]) hsp_15)
    (F := memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0xc90#64) 960 ∗
      (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackFrameAt (sp - 1120#64) 2976 ∗ F)
    (PreSpatial := bytesAt false x.keyA x.key ∗ memRegion (sp + 0x410#64) 960 ∗ stackFrameAt sp 1120)
    (PostSpatial := (x.keyA ↦ₛ x.key) ∗ fsKeys256At (sp + 0x410#64) (aes256KeyScheduleFs x.key) ∗
      stackFrameAt sp 1120)
    ?_ ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
  · simp only [bytesAt, Bool.false_eq_true, ↓reduceIte, allocHookStack_split_1120 sp]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s_c hsc; dsimp only [aes256KeyScheduleSpec]
    have hx0c : s_c.readReg64 .x0 = x.keyA := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
    have hx8c : s_c.readReg64 .x8 = sp + 0x410#64 := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
    have hspc : s_c.sp = sp := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hsp]
    rw [hspc]; exact Entails.pure_right ⟨hx0c, hx8c, hk⟩ (Entails.refl _)
  · intro s_c _ hsc _; dsimp only [aes256KeyScheduleSpec, bytesAt]
    have hspc : s_c.sp = sp := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hsp]
    rw [hspc]; exact Entails.pure_left fun hp => Entails.pure_right (CbcPreserved.of_pure hp) (Entails.refl _)
  · intro s1 hpc1 hrun1 hsp1 hcs1 hp1
    let ksBytes := fsKeys256Bytes (aes256KeyScheduleFs x.key)
    have hks_len : ksBytes.length = 960 := fsKeys256Bytes_length _
    have hks_staged : KsStaged b x.key ksBytes := by
      refine ⟨hks_len, ?_⟩; dsimp [ksBytes]
      simp only [beq_eq_false_iff_ne.mpr hb, Bool.false_eq_true, ↓reduceIte]
    have hsp1' : s1.sp = sp := by rw [hsp1]; simp [wp_norm, arm64_norm, hsp]
    have hsp1_reg : s1.readReg64 .sp = sp := hsp1'
    have hx19_1 : s1.readReg64 (.gpr 19#5) = x.ret := by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm, hx19]
    have hx20_1 : s1.readReg64 (.gpr 20#5) = x.ivA := by rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm, hx20]
    have hx21_1 : s1.readReg64 (.gpr 21#5) = 16#64 := by rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm, hx21]
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
    have_instrs hc.segSwKsMc 0 3; wp_steps 3
    refine step_bl_cbc hc.bl_swMc hCallees.memcpy_ok
      (sp + 0xc90#64, sp + 0x410#64, ksBytes)
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp1']) hsp_15)
      (F := memRegion (sp + 0x7d0#64) 240 ∗ (x.keyA ↦ₛ x.key) ∗
        (hw.rconAddr ↦ᵣ aesRconBytes) ∗ stackAt sp allocHookStack ∗ F)
      (PreSpatial := memRegion (sp + 0xc90#64) 960 ∗ ((sp + 0x410#64) ↦ₛ ksBytes))
      (PostSpatial := memRegion (sp + 0xc90#64) 960 ∗ ((sp + 0x410#64) ↦ₛ ksBytes))
      ?_ ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
    · rw [fsKeys256At_eq_pointsToBytes, allocHookStack_split_1120 sp]; exact Entails.of_eq (by sep_ac_rfl)
    · intro s_c hsc; dsimp only [allocMemcpyVmSpec]; rw [hks_len]
      have hx0c : s_c.readReg64 .x0 = sp + 0xc90#64 := by
        rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
      have hx1c : s_c.readReg64 .x1 = sp + 0x410#64 := by
        rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
      have hx2c : s_c.readReg64 .x2 = 960#64 := by
        rw [hsc]; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
      exact Entails.pure_right ⟨hx0c, hx1c, hx2c, by decide⟩ (Entails.refl _)
    · intro _ _ _ _; dsimp only [allocMemcpyVmSpec]
      refine Entails.pure_left fun ⟨_, hacp, hvm⟩ => Entails.pure_right ⟨hacp, hvm⟩ ?_
      refine sepConj_mono_left ?_; rw [← hks_len]; exact pointsToBytes_entails_memRegion _ _
    · intro s2 hpc2 hrun2 hsp2 hcs2 hp2
      have hsp2' : s2.sp = sp := by rw [hsp2]; simp [wp_norm, arm64_norm, hsp1']
      have hx19_2 : s2.readReg64 (.gpr 19#5) = x.ret := by rw [hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_1]
      have hx20_2 : s2.readReg64 (.gpr 20#5) = x.ivA := by rw [hcs2.readReg64_x20]; simp [wp_norm, arm64_norm, hx20_1]
      have hx21_2 : s2.readReg64 (.gpr 21#5) = 16#64 := by rw [hcs2.readReg64_x21]; simp [wp_norm, arm64_norm, hx21_1]
      have hx22_2 : s2.readReg64 (.gpr 22#5) = x.inA := by rw [hcs2.readReg64_x22]; simp [wp_norm, arm64_norm, hx22_1]
      have hx23_2 : s2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length := by
        rw [hcs2.readReg64_x23]; simp [wp_norm, arm64_norm, hx23_1]
      have hx29_2 : s2.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by
        rw [hcs2.readReg64_x29]; simp [wp_norm, arm64_norm, hx29_1]
      have hv2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
        rw [hcs2.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv1
      have hp02 : CbcPreserved s0 s2 :=
        hp01.trans ((CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl).trans hp2)
      clear hsp2 hcs2 hp2
      have_instrs hc.segSwIvChk 0 2; wp_steps 1
      apply SepWP.step_pure (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun2]) hf_1 rfl
        (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
      conv => arg 3; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hx21_2]
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext _ ksBytes hks_staged
          (by simp [wp_norm, arm64_norm, bv_lin_norm])
          (by simp [wp_norm, arm64_norm, hrun2]) (by simp [wp_norm, arm64_norm, hsp2'])
          (hp02.trans (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl))
          (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv2)
          (by simp [wp_norm, arm64_norm, hx19_2]) (by simp [wp_norm, arm64_norm, hx20_2])
          (by simp [wp_norm, arm64_norm, hx22_2]) (by simp [wp_norm, arm64_norm, hx23_2])
          (by simp [wp_norm, arm64_norm, hx29_2]))

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.KeySetup

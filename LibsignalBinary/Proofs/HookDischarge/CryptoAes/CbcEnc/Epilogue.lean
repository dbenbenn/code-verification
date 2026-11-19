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
import ProofLib.BV
import Arm64.Trusted.ISA.Eval
meta import ProofLib.StdStartup.StdDetect
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.LoopHw
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.LoopSw
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.TailHw
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.TailSw

/-!
# Backend Dispatch, `drop_glue` Zeroization & Epilogue (`CbcEnc.Epilogue`)

Joins the `STORAGE == 1` (`Armv8`) and `STORAGE != 1` (`Fixslice64`) full-block CBC loops and
PKCS#7 final-block paths, steps `drop_glue<Decryptor<Aes256>>`, writes the output `Vec<u8>`,
restores callee-saved registers, and re-packs `PoolAesInitSplit` and `extHookStack`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Epilogue

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open ProofLib.StdStartup (adrpOff pageLo12)
open CryptoGames.CBC (Block bytesToBlock blockToBytesLE)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcEncrypt)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall extHookStack)
open VerifiedLibraries.RustStd (allocCallPreserved_trans)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget FitsEvents OomPreserved AllocCallPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (withRoDataSep)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (aes256KeyScheduleFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (fsKeys256At fsKeys256At_entails_memRegion step_str64_perm step_stp64_perm)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (aesRconBytes armv8ExpandKey roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.DropDecryptor (dropDecryptorSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
  (Aes256EncHwAddrs CbcEncCode Aes256CbcEncryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
  (aesEncEvents aesEncBudgetCondSpec cbcEncBlocks cbcChain ptFullBlocks pkcs7TailBytes
   length_cbcEncBlocks_flatMap length_ptFullBlocks aesCbcEncrypt_split_tail aesCbcEncrypt_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
  (CbcPreserved spAligned_of_eq allocHookStack_split_16 extHookStack_split_4384 stackFrameAt_4384_eq
   cbcSavedCells cbcSavedRegs cbcSavedRegs_entails_stackFrameAt_96
   spill16At byte16At CbcKeyState cbcKeyState_entails_memRegion_960
   vecU8_nonempty_pack memRegion24_eq_pts)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.StepHelpers (step_bl_cbc)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.LoopHw (step_hw_loop)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.LoopSw (step_sw_loop)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.TailHw (step_hw_tail)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.TailSw (step_sw_tail)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand.Simp
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

section
arm64_proof_prelude
attribute [local irreducible] aesRconBytes armv8ExpandKey aes256KeyScheduleFs
  roundKeys15At fsKeys256At Spec.Aes256.aes256Enc bytesToKey32

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
@[local simp, local arm64_norm] private theorem sp_writeReg64_gpr (s : State) (n : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr n) v).sp = s.sp := by simp [State.writeReg64]
@[local simp, local arm64_norm] private theorem sp_writeReg64_sp (s : State) (v : BitVec 64) :
    (s.writeReg64 .sp v).sp = v := rfl
@[local simp, local arm64_norm] private theorem readReg64_sp_eq (s : State) : s.readReg64 .sp = s.sp := rfl

private theorem cbcPreserved_trans_rev {s0 s1 s2 : State}
    (h2 : CbcPreserved s1 s2) (h1 : CbcPreserved s0 s1) : CbcPreserved s0 s2 := h1.trans h2

private theorem cbcSavedCells_eq_sp_off {sp0 sp : BitVec 64} (hsp_def : sp0 - 4384#64 = sp)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    cbcSavedCells sp0 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 =
      ((sp + 0x10c0#64) ↦₆₄ v0) ∗ ((sp + 0x10c8#64) ↦₆₄ v1) ∗
      ((sp + 0x10d0#64) ↦₆₄ v2) ∗ ((sp + 0x10d8#64) ↦₆₄ v3) ∗
      ((sp + 0x10e0#64) ↦₆₄ v4) ∗ ((sp + 0x10e8#64) ↦₆₄ v5) ∗
      ((sp + 0x10f0#64) ↦₆₄ v6) ∗ ((sp + 0x10f8#64) ↦₆₄ v7) ∗
      ((sp + 0x1100#64) ↦₆₄ v8) ∗ ((sp + 0x1108#64) ↦₆₄ v9) ∗
      ((sp + 0x1110#64) ↦₆₄ v10) ∗ ((sp + 0x1118#64) ↦₆₄ v11) := by
  subst hsp_def; unfold cbcSavedCells
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]

private theorem sepWP_done_cbc (s0 sf2 : State) {P : Program} {target : BitVec 64} {s : State}
    {pre : SepProp} {post : State → SepProp → Prop} {onOom : State → SepProp}
    (hpc : s.pc = target) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp) (hcsp : CalleeSavedPreserved s0 s) (hp : CbcPreserved sf2 s)
    (h : ∀ sf : State, sf.sp = s0.sp → CalleeSavedPreserved s0 sf → CbcPreserved sf2 sf → post sf pre) :
    SepWP P target s pre post onOom :=
  SepWP.done hpc hrun (h s hsp hcsp hp)

private theorem step_storage_cmp_bne {P : Program} {pc0 storageAddr brOff target_pc : BitVec 64}
    {b : BitVec 8} {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hadrp : P.fetch pc0 = some (.adr true (.gpr 8#5) (adrpOff pc0 storageAddr)))
    (hldrb : P.fetch (pc0 + 4#64) =
      some (.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 8#5) (pageLo12 storageAddr))))
    (hcmp : P.fetch (pc0 + 8#64) = some (.addSubImm .W32 .SUBS .xzr (.gpr 8#5) 1#12 false))
    (hbne : P.fetch (pc0 + 12#64) = some (.bCond .NE brOff))
    (hent : Pre ⊢ (storageAddr ↦₈ b) ∗ F)
    (hpc : s.pc = pc0) (hrun : s.status = .Running)
    (hsw : b ≠ 1#8 → ∀ s' : State, s'.pc = (pc0 + 12#64) + brOff → s'.status = .Running →
      s'.sp = s.sp → CbcPreserved s s' → calleeSavedVRegs s' = calleeSavedVRegs s →
      (∀ r : BitVec 5, r ≠ 8#5 → s'.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      SepWP P target_pc s' ((storageAddr ↦₈ b) ∗ F) post oom)
    (hhw : b = 1#8 → ∀ s' : State, s'.pc = pc0 + 16#64 → s'.status = .Running →
      s'.sp = s.sp → CbcPreserved s s' → calleeSavedVRegs s' = calleeSavedVRegs s →
      (∀ r : BitVec 5, r ≠ 8#5 → s'.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      SepWP P target_pc s' ((storageAddr ↦₈ b) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre hent ?_
  apply SepWP.step_pure hpc hrun hadrp rfl
    (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
  refine SepWP.step_ldr8
    (hpc := by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
    (hrun := by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hrun])
    (hfetch := hldrb) (hsp := rfl)
    (haddr := show evalAddrMode _ (.Offset (.gpr 8#5) (pageLo12 storageAddr)) = (storageAddr, none) by
      simp [Program.evalInst, execInstWithSvc, evalAddrMode, pageLo12, wp_norm, arm64_norm]; try bv_bits)
    (hload := SepLoad8.of_eq rfl) (hexec := rfl) ?_
  apply SepWP.step_pure
    (by simp [arm64_norm, wp_norm]; try bv_omega)
    (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hrun])
    hcmp rfl (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
  apply SepWP.step_pure
    (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]; try bv_omega)
    (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hrun])
    hbne rfl (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
  by_cases hb : b = 1#8
  · refine hhw hb _
      (by subst hb; simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]; try bv_omega)
      (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hrun])
      (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
      (CbcPreserved.of_proj_perm
        (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
        (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]))
      (by simp [Program.evalInst, execInstWithSvc, calleeSavedVRegs, arm64_norm, wp_norm])
      (fun r hr => by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hr])
  · have hb64 : b.zeroExtend 64 ≠ 1#64 := by revert hb; bv_bits
    refine hsw hb _
      (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hb64])
      (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hrun])
      (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
      (CbcPreserved.of_proj_perm
        (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm])
        (by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]))
      (by simp [Program.evalInst, execInstWithSvc, calleeSavedVRegs, arm64_norm, wp_norm])
      (fun r hr => by simp [Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hr])

/-! ## 1. Full-Block CBC Loop Dispatch (`+0x188..+0x4cc`) -/

theorem step_loop_dispatch {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc outBuf sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) (b : BitVec 8) {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsp_15 : sp &&& 15#64 = 0#64) (hk : x.key.length = 32) (hin : x.input.length < 2 ^ 40)
    (hpc : s.pc = fnAddr + 0x188#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16))
    (hx21 : s.readReg64 (.gpr 21#5) = outBuf) (hx22 : s.readReg64 (.gpr 22#5) = x.inA)
    (hx23 : s.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)))
    (hx24 : s.readReg64 (.gpr 24#5) = sp + 0xc90#64) (hx26 : s.readReg64 (.gpr 26#5) = sp + 0xc90#64)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (x.input.length / 16))
    (hx29 : s.readReg64 (.gpr 29#5) = sp + 0x10c0#64)
    (hnext : ∀ sf : State,
      let prevFinal := cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) (bytesToBlock x.iv) (ptFullBlocks x.input)
      sf.pc = fnAddr + 0x4cc#64 → sf.status = .Running → sf.sp = sp →
      CbcPreserved s sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 (.gpr 19#5) = x.ret →
      sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) →
      sf.readReg64 (.gpr 21#5) = outBuf →
      sf.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)) →
      sf.readReg64 (.gpr 24#5) = sp + 0xc90#64 → sf.readReg64 (.gpr 26#5) = sp + 0xc90#64 →
      sf.readReg64 (.gpr 29#5) = sp + 0x10c0#64 →
      SepWP P target_pc sf
        ((CbcKeyState sp b x.key ∗ memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0x106c#64) 64 ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE prevFinal) ∗ (x.inA ↦ₛ x.input) ∗
          (outBuf ↦ₛ (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
            (bytesToBlock x.iv) (ptFullBlocks x.input)).flatMap blockToBytesLE) ∗
          (hw.storageAddr ↦₈ b) ∗ stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s
      ((CbcKeyState sp b x.key ∗ memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0x106c#64) 64 ∗
        byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗ (x.inA ↦ₛ x.input) ∗
        memRegion outBuf (16 * (x.input.length / 16)) ∗ (hw.storageAddr ↦₈ b) ∗
        stackAt sp allocHookStack) ∗ F) post oom := by
  have_instrs hc.segLoopDisp 0 2
  refine step_storage_cmp_bne (pc0 := fnAddr + 0x188#64) hc.adrp_st1
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hc.ldrb_st1)
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hf_0)
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hf_1)
    (F := CbcKeyState sp b x.key ∗ memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0x106c#64) 64 ∗
      byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗ (x.inA ↦ₛ x.input) ∗
      memRegion outBuf (16 * (x.input.length / 16)) ∗ stackAt sp allocHookStack ∗ F)
    (Entails.of_eq (by sep_ac_rfl)) hpc hrun ?_ ?_
  · intro hb_ne s1 hpc1 hrun1 hsp1 hp1 hv1 hr1
    rw [BitVec.add_assoc, BitVec.add_assoc] at hpc1; simp only [BitVec.reduceAdd] at hpc1
    have hb_beq : (b == 1#8) = false := beq_eq_false_iff_ne.mpr hb_ne
    refine SepWP.weaken_pre (P' :=
        (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗ memRegion (sp + 0x7d0#64) 64 ∗
          memRegion (sp + 0x106c#64) 64 ∗ byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗
          (x.inA ↦ₛ x.input) ∗ memRegion outBuf (16 * (x.input.length / 16)) ∗ stackAt sp allocHookStack) ∗
        (memRegion (sp + 0x810#64) 176 ∗ (hw.storageAddr ↦₈ b) ∗ F)) ?_ ?_
    · unfold CbcKeyState; rw [memRegion_split (sp + 0x7d0#64) 64 176 (by decide)]
      simp only [hb_beq, Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq (by sep_ac_rfl)
    refine step_sw_loop (s0 := s0) hc hCallees x hsp_15 hk hin hpc1 hrun1 (hsp1.trans hsp) (hv1.trans hv)
      ((hr1 19#5 (by decide)).trans hx19) ((hr1 20#5 (by decide)).trans hx20)
      ((hr1 21#5 (by decide)).trans hx21) ((hr1 22#5 (by decide)).trans hx22)
      ((hr1 23#5 (by decide)).trans hx23) ((hr1 24#5 (by decide)).trans hx24)
      ((hr1 26#5 (by decide)).trans hx26) ((hr1 27#5 (by decide)).trans hx27)
      ((hr1 29#5 (by decide)).trans hx29)
      fun sf hpcf hrunf hspf hpf hvf hx19f hx20f hx21f hx23f hx24f hx26f hx29f => ?_
    apply SepWP.weaken_pre; swap
    · exact hnext sf hpcf hrunf hspf (hp1.trans hpf) hvf hx19f hx20f hx21f hx23f hx24f hx26f hx29f
    unfold CbcKeyState; rw [memRegion_split (sp + 0x7d0#64) 64 176 (by decide)]
    simp only [hb_beq, Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro hb_eq s1 hpc1 hrun1 hsp1 hp1 hv1 hr1
    rw [BitVec.add_assoc] at hpc1; simp only [BitVec.reduceAdd] at hpc1
    have hb_beq : (b == 1#8) = true := beq_iff_eq.mpr hb_eq
    refine SepWP.weaken_pre (P' :=
        (roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗ memRegion (sp + 0x7d0#64) 16 ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗
          (x.inA ↦ₛ x.input) ∗ memRegion outBuf (16 * (x.input.length / 16))) ∗
        (memRegion (sp + 0xd80#64) 720 ∗ memRegion (sp + 0x7e0#64) 224 ∗
          memRegion (sp + 0x106c#64) 64 ∗ (hw.storageAddr ↦₈ b) ∗ stackAt sp allocHookStack ∗ F)) ?_ ?_
    · unfold CbcKeyState; rw [memRegion_split (sp + 0x7d0#64) 16 224 (by decide)]
      simp only [hb_beq, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq (by sep_ac_rfl)
    refine step_hw_loop (s0 := s0) hc hCallees x hsp_15 hk hin hpc1 hrun1 (hsp1.trans hsp) (hv1.trans hv)
      ((hr1 19#5 (by decide)).trans hx19) ((hr1 20#5 (by decide)).trans hx20)
      ((hr1 21#5 (by decide)).trans hx21) ((hr1 22#5 (by decide)).trans hx22)
      ((hr1 23#5 (by decide)).trans hx23) ((hr1 24#5 (by decide)).trans hx24)
      ((hr1 26#5 (by decide)).trans hx26) ((hr1 27#5 (by decide)).trans hx27)
      ((hr1 29#5 (by decide)).trans hx29)
      fun sf hpcf hrunf hspf hpf hvf hx19f hx20f hx21f hx23f hx24f hx26f hx29f => ?_
    apply SepWP.weaken_pre; swap
    · exact hnext sf hpcf hrunf hspf (hp1.trans hpf) hvf hx19f hx20f hx21f hx23f hx24f hx26f hx29f
    unfold CbcKeyState; rw [memRegion_split (sp + 0x7d0#64) 16 224 (by decide)]
    simp only [hb_beq, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. PKCS#7 Final-Block Dispatch (`+0x4cc..+0x7b4`) -/

theorem step_tail_dispatch {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr target_pc outBuf sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) (b : BitVec 8) {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsp_15 : sp &&& 15#64 = 0#64) (hk : x.key.length = 32)
    (hpc : s.pc = fnAddr + 0x4cc#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16))
    (hx21 : s.readReg64 (.gpr 21#5) = outBuf)
    (hx23 : s.readReg64 (.gpr 23#5) = outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16)))
    (hx24 : s.readReg64 (.gpr 24#5) = sp + 0xc90#64) (hx26 : s.readReg64 (.gpr 26#5) = sp + 0xc90#64)
    (hx29 : s.readReg64 (.gpr 29#5) = sp + 0x10c0#64)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0x7b4#64 → sf.status = .Running → sf.sp = sp →
      CbcPreserved s sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 (.gpr 19#5) = x.ret →
      sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) →
      sf.readReg64 (.gpr 21#5) = outBuf → sf.readReg64 (.gpr 29#5) = sp + 0x10c0#64 →
      SepWP P target_pc sf
        ((memRegion sp 64 ∗ memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0x106c#64) 64 ∗
          memRegion (sp + 0xc90#64) 0x3d0 ∗
          (outBuf ↦ₛ aesCbcEncrypt Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock x.iv) x.input) ∗
          (hw.storageAddr ↦₈ b) ∗ stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s
      ((CbcKeyState sp b x.key ∗ spill16At sp (pkcs7TailBytes x.input) ∗
        memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0x106c#64) 64 ∗
        byte16At (sp + 0x1050#64) (blockToBytesLE
          (cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) (bytesToBlock x.iv) (ptFullBlocks x.input))) ∗
        (outBuf ↦ₛ (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
          (bytesToBlock x.iv) (ptFullBlocks x.input)).flatMap blockToBytesLE) ∗
        memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16 ∗
        (hw.storageAddr ↦₈ b) ∗ stackAt sp allocHookStack) ∗ F) post oom := by
  have hct_split :
      (outBuf ↦ₛ (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
        (bytesToBlock x.iv) (ptFullBlocks x.input)).flatMap blockToBytesLE) ∗
      ((outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) ↦ₛ blockToBytesLE
        (Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock (pkcs7TailBytes x.input) ^^^
          cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) (bytesToBlock x.iv) (ptFullBlocks x.input)))) =
      (outBuf ↦ₛ aesCbcEncrypt Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock x.iv) x.input) := by
    rw [aesCbcEncrypt_split_tail, pointsToBytes_append, length_cbcEncBlocks_flatMap, length_ptFullBlocks]
  have_instrs hc.segTailDisp 0 2
  refine step_storage_cmp_bne (pc0 := fnAddr + 0x4cc#64) hc.adrp_st2
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hc.ldrb_st2)
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hf_0)
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hf_1)
    (F := CbcKeyState sp b x.key ∗ spill16At sp (pkcs7TailBytes x.input) ∗
      memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0x106c#64) 64 ∗
      byte16At (sp + 0x1050#64) (blockToBytesLE
        (cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) (bytesToBlock x.iv) (ptFullBlocks x.input))) ∗
      (outBuf ↦ₛ (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
        (bytesToBlock x.iv) (ptFullBlocks x.input)).flatMap blockToBytesLE) ∗
      memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16 ∗
      stackAt sp allocHookStack ∗ F)
    (Entails.of_eq (by sep_ac_rfl)) hpc hrun ?_ ?_
  · intro hb_ne s1 hpc1 hrun1 hsp1 hp1 hv1 hr1
    rw [BitVec.add_assoc, BitVec.add_assoc] at hpc1; simp only [BitVec.reduceAdd] at hpc1
    have hb_beq : (b == 1#8) = false := beq_eq_false_iff_ne.mpr hb_ne
    refine SepWP.weaken_pre (P' :=
        (fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ∗
          spill16At sp (pkcs7TailBytes x.input) ∗ memRegion (sp + 0x7d0#64) 64 ∗
          memRegion (sp + 0x106c#64) 64 ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE
            (cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) (bytesToBlock x.iv) (ptFullBlocks x.input))) ∗
          memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16 ∗ stackAt sp allocHookStack) ∗
        (memRegion (sp + 0x810#64) 176 ∗
          (outBuf ↦ₛ (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
            (bytesToBlock x.iv) (ptFullBlocks x.input)).flatMap blockToBytesLE) ∗
          (hw.storageAddr ↦₈ b) ∗ F)) ?_ ?_
    · unfold CbcKeyState; rw [memRegion_split (sp + 0x7d0#64) 64 176 (by decide)]
      simp only [hb_beq, Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq (by sep_ac_rfl)
    refine step_sw_tail (s0 := s0) hc hCallees x hsp_15 hk hpc1 hrun1 (hsp1.trans hsp) (hv1.trans hv)
      ((hr1 19#5 (by decide)).trans hx19) ((hr1 20#5 (by decide)).trans hx20)
      ((hr1 21#5 (by decide)).trans hx21) ((hr1 23#5 (by decide)).trans hx23)
      ((hr1 24#5 (by decide)).trans hx24) ((hr1 29#5 (by decide)).trans hx29)
      fun sf hpcf hrunf hspf hpf hvf hx19f hx20f hx21f hx29f => ?_
    apply SepWP.weaken_pre; swap
    · exact hnext sf hpcf hrunf hspf (hp1.trans hpf) hvf hx19f hx20f hx21f hx29f
    have hks960 : fsKeys256At (sp + 0xc90#64) (aes256KeyScheduleFs x.key) ⊢ memRegion (sp + 0xc90#64) 960 :=
      fsKeys256At_entails_memRegion _ _
    rw [memRegion_split (sp + 0x7d0#64) 64 176 (by decide), show (0x3d0 : Nat) = 960 + 16 from rfl,
        memRegion_split (sp + 0xc90#64) 960 16 (by decide), ← hct_split]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left hks960))))))
    exact Entails.of_eq (by sep_ac_rfl)
  · intro hb_eq s1 hpc1 hrun1 hsp1 hp1 hv1 hr1
    rw [BitVec.add_assoc] at hpc1; simp only [BitVec.reduceAdd] at hpc1
    have hb_beq : (b == 1#8) = true := beq_iff_eq.mpr hb_eq
    refine SepWP.weaken_pre (P' :=
        (roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗
          spill16At sp (pkcs7TailBytes x.input) ∗ memRegion (sp + 0x7d0#64) 16 ∗
          byte16At (sp + 0x1050#64) (blockToBytesLE
            (cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) (bytesToBlock x.iv) (ptFullBlocks x.input))) ∗
          memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16) ∗
        (memRegion (sp + 0xd80#64) 720 ∗ memRegion (sp + 0x7e0#64) 224 ∗ memRegion (sp + 0x106c#64) 64 ∗
          (outBuf ↦ₛ (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
            (bytesToBlock x.iv) (ptFullBlocks x.input)).flatMap blockToBytesLE) ∗
          (hw.storageAddr ↦₈ b) ∗ stackAt sp allocHookStack ∗ F)) ?_ ?_
    · unfold CbcKeyState; rw [memRegion_split (sp + 0x7d0#64) 16 224 (by decide)]
      simp only [hb_beq, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq (by sep_ac_rfl)
    refine step_hw_tail (s0 := s0) hc hCallees x hsp_15 hk hpc1 hrun1 (hsp1.trans hsp) (hv1.trans hv)
      ((hr1 19#5 (by decide)).trans hx19) ((hr1 20#5 (by decide)).trans hx20)
      ((hr1 21#5 (by decide)).trans hx21) ((hr1 23#5 (by decide)).trans hx23)
      ((hr1 24#5 (by decide)).trans hx24) ((hr1 26#5 (by decide)).trans hx26)
      ((hr1 29#5 (by decide)).trans hx29)
      fun sf hpcf hrunf hspf hpf hvf hx19f hx20f hx21f hx29f => ?_
    apply SepWP.weaken_pre; swap
    · exact hnext sf hpcf hrunf hspf (hp1.trans hpf) hvf hx19f hx20f hx21f hx29f
    have hks960 : roundKeys15At (sp + 0xc90#64) (armv8ExpandKey x.key) ∗ memRegion (sp + 0xd80#64) 720 ⊢
        memRegion (sp + 0xc90#64) 960 := by
      have h := cbcKeyState_entails_memRegion_960 sp b x.key
      unfold CbcKeyState at h; simpa only [hb_beq, ↓reduceIte] using h
    rw [memRegion_split (sp + 0x7d0#64) 16 224 (by decide), show (0x3d0 : Nat) = 960 + 16 from rfl,
        memRegion_split (sp + 0xc90#64) 960 16 (by decide), ← hct_split]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left hks960))))))
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. `drop_glue<Decryptor<Aes256>>`, `Vec<u8>` Write & Epilogue (`+0x7b4..+0x90c`) -/

theorem step_drop_and_epilogue {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr outBuf sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) (st : M.σ) (b : BitVec 8) {s0 sf2 s : State} {R : SepProp}
    (hsp_def : s0.sp - 4384#64 = sp) (hsp_15 : sp &&& 15#64 = 0#64)
    (hne0 : outBuf ≠ 0#64) (hin : x.input.length < 2 ^ 40)
    (hacp2 : AllocCallPreserved s0 sf2) (hp_post : CbcPreserved sf2 s)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hpc : s.pc = fnAddr + 0x7b4#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16))
    (hx21 : s.readReg64 (.gpr 21#5) = outBuf) :
    SepWP P (s0.readReg64 .lr) s
      ((memRegion sp 64 ∗ memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0x106c#64) 64 ∗
        memRegion (sp + 0xc90#64) 0x3d0 ∗
        (outBuf ↦ₛ aesCbcEncrypt Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock x.iv) x.input) ∗
        (hw.storageAddr ↦₈ b) ∗ stackAt sp allocHookStack) ∗
       (cbcSavedRegs s0 ∗ memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x410#64) 960 ∗
        memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
        memRegion (sp + 0x1060#64) 12 ∗ memRegion (sp + 0x10ac#64) 20 ∗
        memRegion x.ret 24 ∗ A.live outBuf ((x.input.length / 16 + 1) * 16) 1 ∗
        x.frame ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
        hSplit.base.pool lim (M.stepEvents (aesEncEvents x) st) sf2))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ (stackFrameAt (s0.sp - 4384#64 - 4096#64) 7904 ∗ R)) →
          (sf.mem ⊨ (withRoDataSep hw.rconAddr aesRconBytes
            (aesEncBudgetCondSpec Spec.Aes256.aes256Enc M A lim)).post (x, st) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜¬ FitsEvents M lim st (aesEncEvents x) ∧ OomPreserved s0 sf⌝) := by
  have hsp_reg : s.readReg64 .sp = sp := hsp
  have_instrs hc.segDropArg 0 1; wp_steps 1
  refine step_bl_cbc hc.bl_drop hCallees.dropDecryptor_ok (sp + 0xc90#64, b)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (spAligned_of_eq (by simp [wp_norm, arm64_norm, hsp]) hsp_15)
    (PreSpatial := memRegion (sp + 0xc90#64) 0x3d0 ∗ (hw.storageAddr ↦₈ b) ∗ stackFrameAt sp 0x10)
    (PostSpatial := memRegion (sp + 0xc90#64) 960 ∗ memRegion (sp + 0x1050#64) 16 ∗
      (hw.storageAddr ↦₈ b) ∗ stackFrameAt sp 0x10)
    (F := stackFrameAt (sp - 16#64) 4080 ∗ memRegion sp 64 ∗ memRegion (sp + 0x7d0#64) 240 ∗
      memRegion (sp + 0x106c#64) 64 ∗
      (outBuf ↦ₛ aesCbcEncrypt Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock x.iv) x.input) ∗
      cbcSavedRegs s0 ∗ memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x410#64) 960 ∗
      memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
      memRegion (sp + 0x1060#64) 12 ∗ memRegion (sp + 0x10ac#64) 20 ∗
      memRegion x.ret 24 ∗ A.live outBuf ((x.input.length / 16 + 1) * 16) 1 ∗
      x.frame ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
      hSplit.base.pool lim (M.stepEvents (aesEncEvents x) st) sf2)
    ?_ ?_ ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl) ?_
  · rw [allocHookStack_split_16 sp]; exact Entails.of_eq (by sep_ac_rfl)
  · intro s_call hsc; dsimp only [dropDecryptorSpec]
    have hx0_sc : s_call.readReg64 .x0 = sp + 0xc90#64 := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, wp_norm, arm64_norm]
    have hsp_sc : s_call.sp = sp := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, wp_norm, arm64_norm, hsp]
    rw [hsp_sc]; exact Entails.pure_right hx0_sc (Entails.refl _)
  · intro s_call s1 hsc _; dsimp only [dropDecryptorSpec]
    have hsp_sc : s_call.sp = sp := by
      rw [hsc]; simp [Program.evalInst, execInstWithSvc, wp_norm, arm64_norm, hsp]
    rw [hsp_sc, show (0x3d0 : Nat) = 960 + 16 from rfl,
        memRegion_split (sp + 0xc90#64) 960 16 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.pure_left fun hp => Entails.pure_right (CbcPreserved.of_pure hp) (Entails.of_eq (by sep_ac_rfl))
  · intro s1 hpc1 hrun1 hsp1 hcs1 hp1
    rw [BitVec.add_assoc] at hpc1; simp only [BitVec.reduceAdd] at hpc1
    have hsp1' : s1.sp = sp := by rw [hsp1]; simp [wp_norm, arm64_norm, hsp]
    have hx19_1 : s1.readReg64 (.gpr 19#5) = x.ret := by rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm, hx19]
    have hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) := by
      rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm, hx20]
    have hx21_1 : s1.readReg64 (.gpr 21#5) = outBuf := by rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm, hx21]
    have hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
      rw [hcs1.vregs]; simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv
    have hp_s1 : CbcPreserved sf2 s1 := hp_post.trans
      (cbcPreserved_trans_rev hp1 (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) rfl))
    clear hsp1 hcs1 hp1
    refine SepWP.weaken_pre (P' :=
        memRegion x.ret 24 ∗ cbcSavedRegs s0 ∗
        (memRegion sp 64 ∗ memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x410#64) 960 ∗
          memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0x8c0#64) 960 ∗
          memRegion (sp + 0xc80#64) 16 ∗ memRegion (sp + 0xc90#64) 960 ∗
          memRegion (sp + 0x1050#64) 16 ∗ memRegion (sp + 0x1060#64) 12 ∗
          memRegion (sp + 0x106c#64) 64 ∗ memRegion (sp + 0x10ac#64) 20 ∗
          A.live outBuf ((x.input.length / 16 + 1) * 16) 1 ∗
          (outBuf ↦ₛ aesCbcEncrypt Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock x.iv) x.input) ∗
          x.frame ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ b) ∗
          hSplit.base.pool lim (M.stepEvents (aesEncEvents x) st) sf2 ∗ stackAt sp allocHookStack)) ?_ ?_
    · rw [allocHookStack_split_16 sp]; exact Entails.of_eq (by sep_ac_rfl)
    rw [memRegion24_eq_pts x.ret]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 3 refine SepWP.exists_elim fun _ => ?_
    unfold cbcSavedRegs; rw [cbcSavedCells_eq_sp_off hsp_def]
    have hsp1_reg : s1.readReg64 .sp = sp := hsp1'
    have hsp_10c0_15 : (sp + 0x10c0#64) &&& 15#64 = 0#64 := by revert hsp_15; bv_bits
    have hsp_1000_c0_15 : ((sp + 4096#64) + 192#64) &&& 15#64 = 0#64 := by revert hsp_15; bv_bits
    have_instrs hc.segWriteVec 0 3; wp_stp64 hf_0 mr0 hmr0; wp_str64 hf_1 mr1 hmr1; wp_steps 1
    have_instrs hc.segEpilogue 0 9; wp_steps 9
    have hmr_perm : mr1.perm = s1.mem.perm := by simp [hmr1, hmr0, wp_norm, arm64_norm]
    apply sepWP_done_cbc s0 sf2
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (by subst hsp_def; simp [wp_norm, arm64_norm])
      (by rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, hv1])
      (hp_s1.trans (CbcPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hmr_perm])))
    intro sf hsp_sf hcsp_sf hp_fin
    refine ⟨fun hmf => ?_, hsp_sf, hcsp_sf⟩
    have hacp_fin : AllocCallPreserved s0 sf := allocCallPreserved_trans hacp2 hp_fin.1
    have hpool_eq : hSplit.base.pool lim (M.stepEvents (aesEncEvents x) st) sf =
        hSplit.base.pool lim (M.stepEvents (aesEncEvents x) st) sf2 :=
      hp_fin.pool_eq hSplit.base lim (M.stepEvents (aesEncEvents x) st)
    have hpool_in : (hw.storageAddr ↦₈ b) ∗ hSplit.base.pool lim (M.stepEvents (aesEncEvents x) st) sf2 ⊢
        A.pool lim (M.stepEvents (aesEncEvents x) st) sf := by
      rw [← hpool_eq]; exact hSplit.pool_in lim (M.stepEvents (aesEncEvents x) st) sf b
    have hct_len := aesCbcEncrypt_length Spec.Aes256.aes256Enc
      (bytesToKey32 x.key) (bytesToBlock x.iv) x.input
    have hvec := vecU8_nonempty_pack A x.ret outBuf
      (aesCbcEncrypt Spec.Aes256.aes256Enc (bytesToKey32 x.key) (bytesToBlock x.iv) x.input)
      (by rw [hct_len]; omega) (by rw [hct_len]; omega) hne0
    dsimp only at hvec; rw [hct_len] at hvec
    have hsf4384 :
        cbcSavedRegs s0 ∗ memRegion sp 64 ∗ memRegion (sp + 0x040#64) 976 ∗
        memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
        memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
        memRegion (sp + 0xc90#64) 960 ∗ memRegion (sp + 0x1050#64) 16 ∗
        memRegion (sp + 0x1060#64) 12 ∗ memRegion (sp + 0x106c#64) 64 ∗
        memRegion (sp + 0x10ac#64) 20 ⊢ stackFrameAt s0.sp 4384 := by
      subst hsp_def; rw [stackFrameAt_4384_eq s0.sp]
      exact sepConj_mono_left (cbcSavedRegs_entails_stackFrameAt_96 s0)
    have hfold_sv :
        cbcSavedCells s0.sp
          (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
          (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
          (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
          (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
          (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
          (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)) =
          cbcSavedRegs s0 := rfl
    rw [← cbcSavedCells_eq_sp_off hsp_def, hfold_sv, hsp_def] at hmf
    generalize cbcSavedRegs s0 = svRegs at hmf hsf4384
    dsimp only [withRoDataSep, aesEncBudgetCondSpec]
    rw [extHookStack_split_4384 s0.sp, hsp_def]
    refine Satisfies.mono ?_ hmf
    refine Entails.trans ?_
      (sepConj_mono_left (sepConj_mono_right
        (Entails.pure_right hacp_fin
          (sepConj_mono_right (sepConj_mono hvec
            (sepConj_mono hpool_in (sepConj_mono_left hsf4384)))))))
    exact Entails.of_eq (by sep_ac_rfl)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Epilogue

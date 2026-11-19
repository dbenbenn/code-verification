/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Model
public import ProofLib.SepLogic.WPp
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.AesDecErrRoBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.DropDecryptor
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules

/-!
# `drop_glue`, Workspace Recombination & `Ok`/`Err` Epilogues (`CbcDec.Epilog`)

Verifies `bl drop_glue` (`step_bl_dropDecryptor`), stack workspace recombination for both
hardware and software decryption paths, and the shared `Ok` (`+0xda8`) / `Err` (`+0xd64`)
return epilogues (`cbc_epilogue`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Epilog

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.StdStartup (decodeWords hasInstrs)
open VerifiedLibraries.RustStd (allocCallPreserved_trans)
open CryptoGames.CBC (bytesToBlock pkcs7Unpad)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcDecrypt)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved
   rustAllocEvents rustDeallocEvents rustCliDeallocBudgetSpecBase)
open LibsignalBinary.Heap.AesDecErrRoBudget (errResultErrRo_pack)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (FsKeys256)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved adrpAddPair fsKeys256At fsKeys256At_entails_memRegion)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (aesRconBytes armv8ExpandKey armv8InvExpandedKeys roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (roundKeys15Bytes_length roundKeys15At_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.DropDecryptor (dropDecryptorSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
  (cbcOkRetWords cbcErrDeallocArgsWords cbcErrRetPreWords cbcErrRetPostWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (Aes256DecHwAddrs Aes256CbcDecryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs (CbcDecCodeSegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas (aesDecEvents)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules (sepWP_weaken_pre)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
  (pureStepPreserved_bl sepWP_done_let step_bl_call step_adrpAddPair
   stackAt_allocHook_split16 spAligned_sub3968 vecU8_cbc_pack
   cbcPost cbcPanic cbcOom savedStack96 slots56 cbc_common_ret)

/-! ## 1. `drop_glue` Call Helper, Focused Epilogue Steps & Workspace Recombination -/

theorem step_bl_dropDecryptor {P : Program}
    {blPc calleeAddr storageAddr target_pc sp : BitVec 64} (b : BitVec 8)
    (hbl : hasInstrs P blPc [.bl (calleeAddr - blPc)])
    (hcall : subroutine_ok P calleeAddr (dropDecryptorSpec storageAddr))
    {s : State} {Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 0xb40#64)
    (hFull : Full = (memRegion (sp + 0xb40#64) 976 ∗ (storageAddr ↦₈ b) ∗ stackAt sp allocHookStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running → sf.sp = sp →
      CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf
        ((memRegion (sp + 0xb40#64) 976 ∗ (storageAddr ↦₈ b) ∗ stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s Full post oom := by
  have hsp' : ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).sp = sp := by cases s; exact hsp
  have hx0' : ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr).readReg64 .x0 = sp + 0xb40#64 := by
    simpa [arm64_norm] using hx0
  refine step_bl_call hbl hcall (sp + 0xb40#64, b) hpc hrun hsp_al
    (A := memRegion (sp + 0xb40#64) 976 ∗ (storageAddr ↦₈ b) ∗ stackFrameAt sp 16)
    (A' := memRegion (sp + 0xb40#64) 976 ∗ (storageAddr ↦₈ b) ∗ stackFrameAt sp 16)
    (F := stackFrameAt (sp - 16#64) 4080 ∗ F)
    (by dsimp only [dropDecryptorSpec]; rw [hsp'])
    (fun _ => by dsimp only [dropDecryptorSpec]; rw [hsp'])
    (by rw [hFull, stackAt_allocHook_split16 sp]; sep_ac_rfl)
    hx0'
    fun sf hpc_f hrun_f hsp_f hcs_f hpure_f => ?_
  refine sepWP_weaken_pre
    (P2 := (memRegion (sp + 0xb40#64) 976 ∗ (storageAddr ↦₈ b) ∗ stackAt sp allocHookStack) ∗ F)
    (Entails.of_eq (by rw [stackAt_allocHook_split16 sp]; sep_ac_rfl)) ?_
  exact hnext sf hpc_f hrun_f (hsp_f.trans hsp) hcs_f (pureStepPreserved_bl hpure_f)

private theorem step_ok_ret {P : Program} {fnAddr target_pc sp retPtr outBuf ctLenBv ptLenBv r0 r1 r2 : BitVec 64}
    (hOkRet : hasInstrs P (fnAddr + 0xdac#64) (decodeWords cbcOkRetWords))
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0xdac#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx21 : s.readReg64 .x21 = ptLenBv) (hx23 : s.readReg64 .x23 = ctLenBv)
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x65c#64 → sf.status = .Running → sf.sp = sp →
      calleeSavedVRegs sf = calleeSavedVRegs s → PureStepPreserved s sf →
      SepWP P target_pc sf
        (((sp + 32#64) ↦₆₄ retPtr) ∗ ((sp + 40#64) ↦₆₄ outBuf) ∗
         (retPtr ↦₆₄ ctLenBv) ∗ ((retPtr + 8#64) ↦₆₄ outBuf) ∗
         ((retPtr + 16#64) ↦₆₄ ptLenBv) ∗ Rest) post oom) :
    SepWP P target_pc s
      (((sp + 32#64) ↦₆₄ retPtr) ∗ ((sp + 40#64) ↦₆₄ outBuf) ∗
       (retPtr ↦₆₄ r0) ∗ ((retPtr + 8#64) ↦₆₄ r1) ∗ ((retPtr + 16#64) ↦₆₄ r2) ∗ Rest) post oom := by
  simp only [arm64_norm] at hx21 hx23
  have_instrs hOkRet 0 4
  wp_step
  wp_stp64 hf_1 m1 hm1
  wp_str64 hf_2 m2 hm2
  wp_step
  try simp only [hx21, hx23, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
  exact hnext _
    (by simp [wp_norm, arm64_norm]; try bv_omega)
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp])
    (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
    (PureStepPreserved.of_proj_perm
      (by simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm] at hm1 hm2 ⊢; exact hm2.trans hm1))

private theorem step_err_dealloc_args {P : Program} {fnAddr deallocAddr target_pc sp outBuf ctLenBv : BitVec 64}
    (hArgs : hasInstrs P (fnAddr + 0xd68#64) (decodeWords cbcErrDeallocArgsWords))
    (hBl : hasInstrs P (fnAddr + 0xd74#64) [.bl (deallocAddr - (fnAddr + 0xd74#64))])
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0xd68#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = ctLenBv)
    (hnext : ∀ sf : State, sf.pc = deallocAddr → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .lr = fnAddr + 0xd78#64 →
      sf.readReg64 .x0 = outBuf → sf.readReg64 .x1 = ctLenBv → sf.readReg64 .x2 = 1#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s → PureStepPreserved s sf →
      SepWP P target_pc sf (((sp + 40#64) ↦₆₄ outBuf) ∗ Rest) post oom) :
    SepWP P target_pc s (((sp + 40#64) ↦₆₄ outBuf) ∗ Rest) post oom := by
  simp only [arm64_norm] at hx23
  have_instrs hArgs 0 3
  have_instrs hBl 0 1
  wp_steps 4
  exact hnext _
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp])
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
    (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))

private theorem step_err_ret {P : Program} {fnAddr errStr2Addr target_pc sp retPtr r0 r1 r2 : BitVec 64}
    {errStr2Relax : Bool}
    (hPre : hasInstrs P (fnAddr + 0xd78#64) (decodeWords cbcErrRetPreWords))
    (hPair : hasInstrs P (fnAddr + 0xd80#64)
      (adrpAddPair (.gpr 9#5) (fnAddr + 0xd80#64) errStr2Addr errStr2Relax))
    (hPost : hasInstrs P (fnAddr + 0xd88#64) (decodeWords cbcErrRetPostWords))
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0xd78#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x65c#64 → sf.status = .Running → sf.sp = sp →
      calleeSavedVRegs sf = calleeSavedVRegs s → PureStepPreserved s sf →
      SepWP P target_pc sf
        (((sp + 32#64) ↦₆₄ retPtr) ∗ (retPtr ↦₆₄ errTag) ∗
         ((retPtr + 8#64) ↦₆₄ errStr2Addr) ∗ ((retPtr + 16#64) ↦₆₄ 0x11#64) ∗ Rest) post oom) :
    SepWP P target_pc s
      (((sp + 32#64) ↦₆₄ retPtr) ∗
       (retPtr ↦₆₄ r0) ∗ ((retPtr + 8#64) ↦₆₄ r1) ∗ ((retPtr + 16#64) ↦₆₄ r2) ∗ Rest) post oom := by
  have_instrs hPre 0 2
  wp_steps 2
  refine step_adrpAddPair hPair (by decide)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun]) ?_
  have hpc_d88 : fnAddr + 0xd80#64 + 8#64 = fnAddr + 0xd88#64 := by bv_lin
  try simp only [hpc_d88]
  clear hf_0 hf_1
  have_instrs hPost 0 4
  wp_stp64 hf_0 m1 hm1
  wp_step
  wp_str64 hf_2 m2 hm2
  wp_step
  try simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
  refine sepWP_weaken_pre (Entails.of_eq (by dsimp only [errTag]; try sep_ac_rfl)) ?_
  exact hnext _
    (by simp [wp_norm, arm64_norm]; try bv_omega)
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp])
    (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
    (PureStepPreserved.of_proj_perm
      (by simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm] at hm1 hm2 ⊢; exact hm2.trans hm1))

theorem work3816_pack (sp : BitVec 64) :
    memRegion (sp + 56#64) 2824 ∗ memRegion (sp + 0xb40#64) 976 ∗ memRegion (sp + 0xf10#64) 16 =
      memRegion (sp + 56#64) 3816 := by
  rw [show (3816 : Nat) = 2824 + (976 + 16) from rfl,
      memRegion_split (sp + 56#64) 2824 (976 + 16) (by decide),
      memRegion_split _ 976 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem work2824_split_hw (sp : BitVec 64) :
    memRegion (sp + 56#64) 2824 =
      memRegion (sp + 0x038#64) 168 ∗ memRegion (sp + 0x0e0#64) 8 ∗
      memRegion (sp + 0x0e8#64) 968 ∗ memRegion (sp + 0x4b0#64) 272 ∗
      memRegion (sp + 0x5c0#64) 688 ∗ memRegion (sp + 0x870#64) 272 ∗
      memRegion (sp + 0x980#64) 208 ∗ memRegion (sp + 0xa50#64) 16 ∗
      memRegion (sp + 0xa60#64) 224 := by
  rw [show (2824 : Nat) = 168 + 2656 from rfl, memRegion_split (sp + 56#64) 168 2656 (by decide),
      show (2656 : Nat) = 8 + 2648 from rfl, memRegion_split _ 8 2648 (by decide),
      show (2648 : Nat) = 968 + 1680 from rfl, memRegion_split _ 968 1680 (by decide),
      show (1680 : Nat) = 272 + 1408 from rfl, memRegion_split _ 272 1408 (by decide),
      show (1408 : Nat) = 688 + 720 from rfl, memRegion_split _ 688 720 (by decide),
      show (720 : Nat) = 272 + 448 from rfl, memRegion_split _ 272 448 (by decide),
      show (448 : Nat) = 208 + 240 from rfl, memRegion_split _ 208 240 (by decide),
      show (240 : Nat) = 16 + 224 from rfl, memRegion_split _ 16 224 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem work2824_split_sw (sp : BitVec 64) :
    memRegion (sp + 56#64) 2824 =
      memRegion (sp + 0x038#64) 4 ∗ memRegion (sp + 0x03c#64) 168 ∗ memRegion (sp + 0x0e4#64) 4 ∗
      memRegion (sp + 0x0e8#64) 968 ∗ memRegion (sp + 0x4b0#64) 64 ∗ memRegion (sp + 0x4f0#64) 896 ∗
      memRegion (sp + 0x870#64) 64 ∗ memRegion (sp + 0x8b0#64) 176 ∗
      memRegion (sp + 0x960#64) 240 ∗ memRegion (sp + 0xa50#64) 240 := by
  rw [show (2824 : Nat) = 4 + 2820 from rfl, memRegion_split (sp + 56#64) 4 2820 (by decide),
      show (2820 : Nat) = 168 + 2652 from rfl, memRegion_split _ 168 2652 (by decide),
      show (2652 : Nat) = 4 + 2648 from rfl, memRegion_split _ 4 2648 (by decide),
      show (2648 : Nat) = 968 + 1680 from rfl, memRegion_split _ 968 1680 (by decide),
      show (1680 : Nat) = 64 + 1616 from rfl, memRegion_split _ 64 1616 (by decide),
      show (1616 : Nat) = 896 + 720 from rfl, memRegion_split _ 896 720 (by decide),
      show (720 : Nat) = 64 + 656 from rfl, memRegion_split _ 64 656 (by decide),
      show (656 : Nat) = 176 + 480 from rfl, memRegion_split _ 176 480 (by decide),
      show (480 : Nat) = 240 + 240 from rfl, memRegion_split _ 240 240 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem decryptor976_pack_hw (sp : BitVec 64) (key : List (BitVec 8)) :
    memRegion (sp + 0xb40#64) 240 ∗
      roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
      memRegion (sp + 0xd20#64) 480 ∗ memRegion (sp + 0xf00#64) 16 ⊢
      memRegion (sp + 0xb40#64) 976 := by
  have hrk : roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ⊢
      memRegion (sp + 0xc30#64) 240 := by
    rw [roundKeys15At_eq_pointsToBytes]
    have hm := pointsToBytes_entails_memRegion (sp + 0xc30#64)
      (Armv8.Defs.roundKeys15Bytes (armv8InvExpandedKeys (armv8ExpandKey key)))
    rwa [roundKeys15Bytes_length] at hm
  have hsplit : memRegion (sp + 0xb40#64) 976 =
      memRegion (sp + 0xb40#64) 240 ∗ memRegion (sp + 0xc30#64) 240 ∗
      memRegion (sp + 0xd20#64) 480 ∗ memRegion (sp + 0xf00#64) 16 := by
    rw [show (976 : Nat) = 240 + (240 + (480 + 16)) from rfl,
        memRegion_split (sp + 0xb40#64) 240 (240 + (480 + 16)) (by decide),
        memRegion_split _ 240 (480 + 16) (by decide),
        memRegion_split _ 480 16 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hsplit]
  exact sepConj_mono_right (sepConj_mono_left hrk)

theorem decryptor976_pack_sw (sp : BitVec 64) (ks : FsKeys256)
    {prevBs : List (BitVec 8)} (hprev : prevBs.length = 16) :
    fsKeys256At (sp + 0xb40#64) ks ∗ ((sp + 0xf00#64) ↦ₛ prevBs) ⊢
      memRegion (sp + 0xb40#64) 976 := by
  have h16 : ((sp + 0xf00#64) ↦ₛ prevBs) ⊢ memRegion (sp + 0xf00#64) 16 := by
    simpa only [hprev] using pointsToBytes_entails_memRegion (sp + 0xf00#64) prevBs
  have hsplit : memRegion (sp + 0xb40#64) 976 =
      memRegion (sp + 0xb40#64) 960 ∗ memRegion (sp + 0xf00#64) 16 := by
    rw [show (976 : Nat) = 960 + 16 from rfl, memRegion_split (sp + 0xb40#64) 960 16 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hsplit]
  exact sepConj_mono (fsKeys256At_entails_memRegion (sp + 0xb40#64) ks) h16

/-! ## 2. Shared `Ok` & `Err` Epilogues (`fnAddr + 0xda8#64 | +0xd64#64 -> ret`) -/

set_option maxHeartbeats 500000 in
theorem cbc_epilogue {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr outBuf : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (st : M.σ) (b : BitVec 8) (rawBs : List (BitVec 8))
    (r0 r1 r2 w0 w1 w2 w3 : BitVec 64) (R : SepProp) (s0 sm : State)
    (hnb : ¬ (x.input.length = 0 ∨ x.input.length % 16 ≠ 0))
    (hlt40 : x.input.length < 2 ^ 40)
    (hsp0 : s0.spAligned = true) (houtNe0 : outBuf ≠ 0#64)
    (hraw_len : rawBs.length = x.input.length)
    (haes_eq : aesCbcDecrypt Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock x.iv) x.input =
      pkcs7Unpad rawBs)
    (hrunm : sm.status = .Running) (hspm : sm.sp = s0.sp - 3968#64)
    (hx0 : sm.readReg64 .x0 = s0.sp - 3968#64 + 0xb40#64)
    (hx23 : sm.readReg64 .x23 = BitVec.ofNat 64 x.input.length)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hpres : AllocCallPreserved s0 sm)
    (hunpad :
      (∃ ptLen : Nat,
        ptLen < x.input.length ∧
        pkcs7Unpad rawBs = some (rawBs.take ptLen) ∧
        sm.pc = fnAddr + 0xda8#64 ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 ptLen) ∨
      (pkcs7Unpad rawBs = none ∧ sm.pc = fnAddr + 0xd64#64)) :
    let sp := s0.sp - 3968#64
    let st1 := M.stepEvents (rustAllocEvents x.input.length 1) st
    SepWPp P (s0.readReg64 .lr) sm
      ((hw.rconAddr ↦ᵣ aesRconBytes) ∗
        slots56 sp w0 w1 w2 w3 x.ret outBuf x.inA ∗
        memRegion (sp + 56#64) 2824 ∗ memRegion (sp + 0xb40#64) 976 ∗
        memRegion (sp + 0xf10#64) 16 ∗ (outBuf ↦ₛ rawBs) ∗
        hSplit.base.live outBuf x.input.length 1 ∗
        (hw.storageAddr ↦₈ b) ∗ hSplit.base.pool lim st1 sm ∗
        ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
        x.frame ∗ savedStack96 s0 ∗ stackAt sp allocHookStack)
      (cbcPost A lim hw.rconAddr errStr1Addr errStr2Addr x st R s0)
      (cbcPanic A lim x st R s0) (cbcOom M lim x st s0) := by
  intro sp st1
  have hpos : 0 < x.input.length := by omega
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl : (sp &&& 15#64 == 0#64) = true := spAligned_sub3968 hspAl0
  have hspm_sp : sm.sp = sp := hspm
  have hx0_sp : sm.readReg64 .x0 = sp + 0xb40#64 := hx0
  clear hspm hx0
  rcases hunpad with ⟨ptLen, hpt_lt, hpk, hpc_ok, hx21_pt⟩ | ⟨hpk, hpc_err⟩
  · -- Valid PKCS#7: `bl drop_glue` at `+0xda8` -> `step_ok_ret` -> `cbc_common_ret`
    have haes : aesCbcDecrypt Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock x.iv) x.input =
        some (rawBs.take ptLen) := haes_eq.trans hpk
    have hevs : aesDecEvents Spec.Aes256.aes256Dec x = rustAllocEvents x.input.length 1 := by
      unfold aesDecEvents; simp only [hnb, ↓reduceIte, haes, Option.isSome_some]
    have hst1 : st1 = M.stepEvents (aesDecEvents Spec.Aes256.aes256Dec x) st := by rw [hevs]
    apply SepWPp.of_sepWP (mid := fnAddr + 0x65c#64)
    let OkDropRest :=
      (hw.rconAddr ↦ᵣ aesRconBytes) ∗ slots56 sp w0 w1 w2 w3 x.ret outBuf x.inA ∗
      memRegion (sp + 56#64) 2824 ∗ memRegion (sp + 0xf10#64) 16 ∗
      (outBuf ↦ₛ rawBs) ∗ hSplit.base.live outBuf x.input.length 1 ∗
      hSplit.base.pool lim st1 sm ∗
      ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
      x.frame ∗ savedStack96 s0
    refine step_bl_dropDecryptor (sp := sp) b cs.bl_dropOk hCal.dropDecryptor_ok
      hpc_ok hrunm hspm_sp (by simpa [State.spAligned, hspm_sp] using hspAl) hx0_sp
      (F := OkDropRest) (by dsimp only [OkDropRest]; sep_ac_rfl)
      fun s_dr hpc_dr hrun_dr hsp_dr hcs_dr hpure_dr => ?_
    have hpc_dr' : s_dr.pc = fnAddr + 0xdac#64 := by simpa [BitVec.add_assoc] using hpc_dr
    have hx21_dr : s_dr.readReg64 .x21 = BitVec.ofNat 64 ptLen :=
      hcs_dr.readReg64_x21.trans hx21_pt
    have hx23_dr : s_dr.readReg64 .x23 = BitVec.ofNat 64 x.input.length :=
      hcs_dr.readReg64_x23.trans hx23
    have hv_dr : calleeSavedVRegs s_dr = calleeSavedVRegs s0 := hcs_dr.vregs.trans hvm
    let OkStepRest :=
      memRegion (sp + 56#64) 3816 ∗ (hw.storageAddr ↦₈ b) ∗ stackAt sp allocHookStack ∗
      (hw.rconAddr ↦ᵣ aesRconBytes) ∗
      (sp ↦₆₄ w0) ∗ ((sp + 8#64) ↦₆₄ w1) ∗ ((sp + 16#64) ↦₆₄ w2) ∗
      ((sp + 24#64) ↦₆₄ w3) ∗ ((sp + 48#64) ↦₆₄ x.inA) ∗
      (outBuf ↦ₛ rawBs) ∗ hSplit.base.live outBuf x.input.length 1 ∗
      hSplit.base.pool lim st1 sm ∗ x.frame ∗ savedStack96 s0
    refine sepWP_weaken_pre
      (Entails.of_eq (by
        dsimp only [OkDropRest, OkStepRest, slots56]
        rw [← work3816_pack sp]; sep_ac_rfl))
      (step_ok_ret cs.okRet OkStepRest s_dr hpc_dr' hrun_dr hsp_dr hspAl hx21_dr hx23_dr
        fun sm2 hpc2 hrun2 hsp2 hv2 hpure_step => ?_)
    refine SepWP.done hpc2 hrun2 ?_
    have hpure_sm2 : PureStepPreserved sm sm2 := hpure_dr.trans hpure_step
    have hpres2 : AllocCallPreserved s0 sm2 :=
      allocCallPreserved_trans hpres hpure_sm2.allocCallPreserved
    have hpool2 : hSplit.base.pool lim st1 sm2 = hSplit.base.pool lim st1 sm :=
      hpure_sm2.pool_eq hSplit.base lim st1
    let OutOk :=
      x.frame ∗ (((x.ret ↦₆₄ BitVec.ofNat 64 x.input.length) ∗
        ((x.ret + 8#64) ↦₆₄ outBuf) ∗ ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 ptLen)) ∗
        A.live outBuf x.input.length 1 ∗ (outBuf ↦ₛ rawBs))
    refine SepWPp.weaken_pre
      (P' := (hw.rconAddr ↦ᵣ aesRconBytes) ∗ OutOk ∗
        slots56 sp w0 w1 w2 w3 x.ret outBuf x.inA ∗
        memRegion (sp + 56#64) 3816 ∗ savedStack96 s0 ∗
        A.pool lim st1 sm2 ∗ stackAt sp allocHookStack)
      (by
        dsimp only [OkStepRest, OutOk, slots56]
        rw [← hpool2, ← hSplit.live_eq]
        refine Entails.trans (Entails.of_eq (show _ =
            ((hw.storageAddr ↦₈ b) ∗ hSplit.base.pool lim st1 sm2) ∗ _ by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left (hSplit.pool_in lim st1 sm2 b))
          (Entails.of_eq (by sep_ac_rfl))) ?_
    exact cbc_common_ret A lim hw.rconAddr errStr1Addr errStr2Addr cs.retEpilogue x st st1
      w0 w1 w2 w3 x.ret outBuf x.inA OutOk R s0 sm2 hsp0 hpc2 hrun2 hsp2 (hv2.trans hv_dr)
      hpres2 hst1 (by
        rw [haes]
        exact sepConj_mono_right
          (vecU8_cbc_pack A x.ret outBuf rawBs x.input.length ptLen hraw_len hpos
            (by omega) (by omega) houtNe0))
  · -- Invalid PKCS#7: `bl drop_glue` at `+0xd64` -> `bl __rust_dealloc` -> `step_err_ret` -> `cbc_common_ret`
    have haes : aesCbcDecrypt Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock x.iv) x.input =
        none := haes_eq.trans hpk
    have hevs : aesDecEvents Spec.Aes256.aes256Dec x =
        rustAllocEvents x.input.length 1 ++ rustDeallocEvents x.input.length 1 := by
      unfold aesDecEvents; simp only [hnb, ↓reduceIte, haes]; rfl
    let st2 := M.stepEvents (rustDeallocEvents x.input.length 1) st1
    have hst2 : st2 = M.stepEvents (aesDecEvents Spec.Aes256.aes256Dec x) st := by
      rw [hevs, AllocCostModel.stepEvents_append]
    apply SepWPp.of_sepWP (mid := deallocAddr)
    let ErrDropRest :=
      (hw.rconAddr ↦ᵣ aesRconBytes) ∗ slots56 sp w0 w1 w2 w3 x.ret outBuf x.inA ∗
      memRegion (sp + 56#64) 2824 ∗ memRegion (sp + 0xf10#64) 16 ∗
      (outBuf ↦ₛ rawBs) ∗ hSplit.base.live outBuf x.input.length 1 ∗
      hSplit.base.pool lim st1 sm ∗
      ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
      x.frame ∗ savedStack96 s0
    refine step_bl_dropDecryptor (sp := sp) b cs.bl_dropErr hCal.dropDecryptor_ok
      hpc_err hrunm hspm_sp (by simpa [State.spAligned, hspm_sp] using hspAl) hx0_sp
      (F := ErrDropRest) (by dsimp only [ErrDropRest]; sep_ac_rfl)
      fun s_dr hpc_dr hrun_dr hsp_dr hcs_dr hpure_dr => ?_
    have hpc_dr' : s_dr.pc = fnAddr + 0xd68#64 := by simpa [BitVec.add_assoc] using hpc_dr
    have hx23_dr : s_dr.readReg64 .x23 = BitVec.ofNat 64 x.input.length :=
      hcs_dr.readReg64_x23.trans hx23
    have hv_dr : calleeSavedVRegs s_dr = calleeSavedVRegs s0 := hcs_dr.vregs.trans hvm
    let ArgsRest :=
      memRegion (sp + 56#64) 3816 ∗ (hw.storageAddr ↦₈ b) ∗ stackAt sp allocHookStack ∗
      (hw.rconAddr ↦ᵣ aesRconBytes) ∗
      (sp ↦₆₄ w0) ∗ ((sp + 8#64) ↦₆₄ w1) ∗ ((sp + 16#64) ↦₆₄ w2) ∗
      ((sp + 24#64) ↦₆₄ w3) ∗ ((sp + 32#64) ↦₆₄ x.ret) ∗ ((sp + 48#64) ↦₆₄ x.inA) ∗
      (outBuf ↦ₛ rawBs) ∗ hSplit.base.live outBuf x.input.length 1 ∗
      hSplit.base.pool lim st1 sm ∗
      ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
      x.frame ∗ savedStack96 s0
    refine sepWP_weaken_pre
      (Entails.of_eq (by
        dsimp only [ErrDropRest, ArgsRest, slots56]
        rw [← work3816_pack sp]; sep_ac_rfl))
      (step_err_dealloc_args (outBuf := outBuf) cs.errDeallocArgs cs.bl_dealloc ArgsRest s_dr
        hpc_dr' hrun_dr hsp_dr hspAl hx23_dr
        fun s_bl hpc_bl hrun_bl hsp_bl hlr_bl hx0_bl hx1_bv hx2_bv hv_bl hpure_args => ?_)
    refine SepWP.done hpc_bl hrun_bl ?_
    have hx1_bl : (s_bl.readReg64 .x1).toNat = x.input.length := by
      rw [hx1_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x.input.length < 2 ^ 64)]
    have hx2_bl : (s_bl.readReg64 .x2).toNat = 1 := by rw [hx2_bv]; rfl
    have hpure_bl : PureStepPreserved sm s_bl := hpure_dr.trans hpure_args
    have hpres_bl : AllocCallPreserved s0 s_bl :=
      allocCallPreserved_trans hpres hpure_bl.allocCallPreserved
    have hpool_bl : hSplit.base.pool lim st1 s_bl = hSplit.base.pool lim st1 sm :=
      hpure_bl.pool_eq hSplit.base lim st1
    have hraw_mem : (outBuf ↦ₛ rawBs) ⊢ memRegion outBuf x.input.length := by
      simpa only [hraw_len] using pointsToBytes_entails_memRegion outBuf rawBs
    let FrameDealloc :=
      (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ b) ∗
      slots56 sp w0 w1 w2 w3 x.ret outBuf x.inA ∗ memRegion (sp + 56#64) 3816 ∗
      ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
      x.frame ∗ savedStack96 s0
    refine SepWPp.weaken_pre
      (P' := (hSplit.base.pool lim st1 s_bl ∗ hSplit.base.live outBuf x.input.length 1 ∗
        memRegion outBuf x.input.length ∗ stackAt sp allocHookStack) ∗ FrameDealloc)
      (by
        dsimp only [ArgsRest, FrameDealloc, slots56]; rw [← hpool_bl]
        refine Entails.trans (Entails.of_eq (show _ = (outBuf ↦ₛ rawBs) ∗ _ by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hraw_mem) (Entails.of_eq (by sep_ac_rfl))) ?_
    refine SepWPp.call_wpp (x := (outBuf, x.input.length, 1, st1))
      (ret_pc := fnAddr + 0xd78#64) (F := FrameDealloc)
      hCal.dealloc_ok hpc_bl hrun_bl (by simpa [State.spAligned, hsp_bl] using hspAl) hlr_bl
      ?_
      (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
      (fun _ _ ⟨_, hp⟩ => False.elim (not_satisfies_false_sepConj hp))
      ?_
      (fun _ _ _ hm_oom => by
        dsimp only [rustCliDeallocBudgetSpecBase] at hm_oom
        exact False.elim (not_satisfies_false_sepConj hm_oom))
    · intro R' hm'
      dsimp only [rustCliDeallocBudgetSpecBase]
      rw [hsp_bl, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_bl, hx1_bl, hx2_bl⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'⟩
    · intro sf_d hpc_d hrun_d hsp_d hcs_d
      dsimp only [rustCliDeallocBudgetSpecBase]
      rw [hsp_bl, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hpres_d, _⟩ => ?_
      have hpres_s0_d : AllocCallPreserved s0 sf_d := allocCallPreserved_trans hpres_bl hpres_d
      have hsp_d' : sf_d.sp = sp := hsp_d.trans hsp_bl
      have hv_d : calleeSavedVRegs sf_d = calleeSavedVRegs s0 := hcs_d.vregs.trans (hv_bl.trans hv_dr)
      apply SepWPp.of_sepWP (mid := fnAddr + 0x65c#64)
      let ErrStepRest :=
        hSplit.base.pool lim st2 sf_d ∗ stackAt sp allocHookStack ∗
        (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ b) ∗
        (sp ↦₆₄ w0) ∗ ((sp + 8#64) ↦₆₄ w1) ∗ ((sp + 16#64) ↦₆₄ w2) ∗
        ((sp + 24#64) ↦₆₄ w3) ∗ ((sp + 40#64) ↦₆₄ outBuf) ∗ ((sp + 48#64) ↦₆₄ x.inA) ∗
        memRegion (sp + 56#64) 3816 ∗ x.frame ∗ savedStack96 s0
      refine sepWP_weaken_pre
        (Entails.of_eq (by dsimp only [FrameDealloc, ErrStepRest, slots56, st2]; sep_ac_rfl))
        (step_err_ret cs.errRetPre cs.errStr2Pair cs.errRetPost ErrStepRest sf_d
          hpc_d hrun_d hsp_d' hspAl
          fun sm3 hpc3 hrun3 hsp3 hv3 hpure3 => ?_)
      refine SepWP.done hpc3 hrun3 ?_
      have hpres3 : AllocCallPreserved s0 sm3 :=
        allocCallPreserved_trans hpres_s0_d hpure3.allocCallPreserved
      have hpool3 : hSplit.base.pool lim st2 sm3 = hSplit.base.pool lim st2 sf_d :=
        hpure3.pool_eq hSplit.base lim st2
      let OutErr :=
        x.frame ∗ ((x.ret ↦₆₄ errTag) ∗ ((x.ret + 8#64) ↦₆₄ errStr2Addr) ∗ ((x.ret + 16#64) ↦₆₄ 0x11#64))
      refine SepWPp.weaken_pre
        (P' := (hw.rconAddr ↦ᵣ aesRconBytes) ∗ OutErr ∗
          slots56 sp w0 w1 w2 w3 x.ret outBuf x.inA ∗
          memRegion (sp + 56#64) 3816 ∗ savedStack96 s0 ∗
          A.pool lim st2 sm3 ∗ stackAt sp allocHookStack)
        (by
          dsimp only [ErrStepRest, OutErr, slots56]; rw [← hpool3]
          refine Entails.trans (Entails.of_eq (show _ =
              ((hw.storageAddr ↦₈ b) ∗ hSplit.base.pool lim st2 sm3) ∗ _ by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left (hSplit.pool_in lim st2 sm3 b))
            (Entails.of_eq (by sep_ac_rfl))) ?_
      exact cbc_common_ret A lim hw.rconAddr errStr1Addr errStr2Addr cs.retEpilogue x st st2
        w0 w1 w2 w3 x.ret outBuf x.inA OutErr R s0 sm3 hsp0 hpc3 hrun3 hsp3 (hv3.trans hv_d)
        hpres3 hst2 (by
          rw [haes]
          exact sepConj_mono_right
            (errResultErrRo_pack x.ret errStr1Addr errStr2Addr errStr2Addr 0x11#64 (Or.inr ⟨rfl, rfl⟩)))

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Epilog

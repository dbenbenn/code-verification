/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.ProgramReflection
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
import ProofLib.SepLogic.WP
import ProofLib.SepLogic.WPp
import ProofLib.BV
import Arm64.Trusted.ISA.Eval
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.KeySetup
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.PreAlloc
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.PostAlloc
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Epilogue

/-!
# Public Facade & Consumer Ladder for `aes_256_cbc_encrypt` (`CryptoAes.CbcEncrypt`)

Top-level machine-code + `mallocng` correctness theorems for the relinked `595`-instruction
`signal_crypto::aes_cbc::aes_256_cbc_encrypt` (`aes::autodetect::Aes256`: `STORAGE == 1` ARMv8
hardware AES, `STORAGE == 0xff` lazy `features_aes::init_inner` initialization, `STORAGE != 1`
`aes::soft::fixslice64` fallback, and `drop_glue<Decryptor<Aes256>>` zeroization) against consumer
specifications parameterized by `Spec.Aes256.aes256Enc` under `withRoData hw.rconAddr aesRconBytes`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEncrypt

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open ProofLib.ProgramReflection (WordTree)
open ProofLib.StdStartup (hasInstrs)
open CryptoGames.CBC (bytesToBlock blockToBytesLE)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcEncrypt)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall extHookStack)
open VerifiedLibraries.RustStd (allocCallPreserved_trans checkShimInstrsAt)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget FitsEvents NullAllowed RustLayoutOk
   OomPreserved AllocCallPreserved rustAllocEvents rustCliAllocBudgetSpecBase
   rustAllocZeroedBudgetSpecBase)
open LibsignalBinary.Heap.SpecBudget
  (aesEncFnBudgetSpec aesEncBudgetSpec aesEncFnBudgetSpec_block_eq)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (hasShimInstrs_of_wordTree)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (withRoData withRoDataSep)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (hasInstrs_prefix)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
  (CbcEncCode aes256CbcEncryptReachableInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
  (cbcEncBlocks cbcChain ptFullBlocks pkcs7TailBytes subroutine_ok_roData_cond_of_sep
   subroutine_ok_roData_noOom_of_cond subroutine_ok_roData_keepsFs_of_noOom
   subroutine_ok_roData_budget_of_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Layout
  (CbcPreserved sp_sub4384_and_15 spAligned_of_eq
   extHookStack_split_4384 stackFrameAt_4384_eq cbcSavedRegs spill16At byte16At CbcKeyState)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.KeySetup (KsStaged)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.PreAlloc
  (step_seg_pre_alloc cbc_panic_tail)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.PostAlloc (step_seg_post_alloc_stage)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Epilogue
  (step_loop_dispatch step_tail_dispatch step_drop_and_epilogue)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

export LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Code
  (Aes256EncHwAddrs Aes256CbcEncryptPanicSyms aes256CbcEncryptInstrs
   aes256CbcEncryptInstrs_length Aes256CbcEncryptCallees)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
  (aesEncEvents aesEncBudgetCondSpec aesEncNoOomSpec)

section
arm64_proof_prelude
attribute [local irreducible] aesRconBytes cbcSavedRegs Spec.Aes256.aes256Enc bytesToKey32

/-! ## 1. Non-Null Tail & Reachable-Prefix `withRoDataSep` Theorem -/

private theorem cbc_nonnull_tail {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr outBuf sp : BitVec 64}
    (hc : CbcEncCode P fnAddr hw keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
      memcpyAddr memsetAddr handleErrorAddr)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr)
    (x : AesCall) (st : M.σ) {b : BitVec 8} {ksBytes : List (BitVec 8)} (hks : KsStaged b x.key ksBytes)
    {s0 sf2 : State} {R : SepProp}
    (hsp_def : s0.sp - 4384#64 = sp) (hsp_15 : sp &&& 15#64 = 0#64)
    (hne0 : outBuf ≠ 0#64) (hk : x.key.length = 32) (hiv : x.iv.length = 16)
    (hin : x.input.length < 2 ^ 40)
    (hacp2 : AllocCallPreserved s0 sf2) (hv2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hpc2 : sf2.pc = fnAddr + 0x0c4#64) (hrun2 : sf2.status = .Running) (hsp2 : sf2.sp = sp)
    (hx0_2 : sf2.readReg64 (.gpr 0#5) = outBuf) (hx19_2 : sf2.readReg64 (.gpr 19#5) = x.ret)
    (hx20_2 : sf2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16))
    (hx22_2 : sf2.readReg64 (.gpr 22#5) = x.inA)
    (hx23_2 : sf2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length)
    (hx25_2 : sf2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (16 * (x.input.length / 16)))
    (hx29_2 : sf2.readReg64 (.gpr 29#5) = sp + 0x10c0#64) :
    SepWPp P (s0.readReg64 .lr) sf2
      (cbcSavedRegs s0 ∗ memRegion sp 64 ∗ memRegion (sp + 0x040#64) 976 ∗
       memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
       ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)) ∗ memRegion (sp + 0xc90#64) 960 ∗
       memRegion (sp + 0x1050#64) 16 ∗ memRegion (sp + 0x1060#64) 12 ∗
       memRegion (sp + 0x106c#64) 64 ∗ memRegion (sp + 0x10ac#64) 20 ∗
       (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
       memRegion x.ret 24 ∗ A.live outBuf ((x.input.length / 16 + 1) * 16) 1 ∗
       (outBuf ↦ₛ List.replicate ((x.input.length / 16 + 1) * 16) 0#8) ∗
       (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ b) ∗
       hSplit.base.pool lim (M.stepEvents (aesEncEvents x) st) sf2 ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ (stackFrameAt (s0.sp - 4384#64 - 4096#64) 7904 ∗ R)) →
          (sf.mem ⊨ (withRoDataSep hw.rconAddr aesRconBytes
            (aesEncBudgetCondSpec Spec.Aes256.aes256Enc M A lim)).post (x, st) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ (stackFrameAt (s0.sp - 4384#64 - 4096#64) 7904 ∗ R)) →
          (sf.mem ⊨ (withRoDataSep hw.rconAddr aesRconBytes
            (aesEncBudgetCondSpec Spec.Aes256.aes256Enc M A lim)).onPanic (x, st) s0 sf ∗ R))
      (fun sf => ⌜¬ FitsEvents M lim st (aesEncEvents x) ∧ OomPreserved s0 sf⌝) := by
  apply SepWPp.of_sepWP_ret
  have hout_mr :
      (outBuf ↦ₛ List.replicate ((x.input.length / 16 + 1) * 16) 0#8) ⊢
        memRegion outBuf (16 * (x.input.length / 16)) ∗
          memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16 := by
    have h1 : (outBuf ↦ₛ List.replicate ((x.input.length / 16 + 1) * 16) 0#8) ⊢
        memRegion outBuf ((x.input.length / 16 + 1) * 16) := by
      simpa only [List.length_replicate] using
        pointsToBytes_entails_memRegion outBuf (List.replicate ((x.input.length / 16 + 1) * 16) 0#8)
    refine Entails.trans h1 ?_
    rw [show (x.input.length / 16 + 1) * 16 = 16 * (x.input.length / 16) + 16 by omega,
        memRegion_split outBuf (16 * (x.input.length / 16)) 16 (by omega)]
    exact Entails.refl _
  refine SepWP.weaken_pre (P' :=
      (memRegion sp 64 ∗ memRegion (sp + 0x7d0#64) 240 ∗ ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)) ∗
        memRegion (sp + 0xc90#64) 960 ∗ memRegion (sp + 0x1050#64) 16 ∗
        (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack) ∗
      (memRegion outBuf (16 * (x.input.length / 16)) ∗
        memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16 ∗
        memRegion (sp + 0x106c#64) 64 ∗ (hw.storageAddr ↦₈ b) ∗
        cbcSavedRegs s0 ∗ memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x410#64) 960 ∗
        memRegion (sp + 0x1060#64) 12 ∗ memRegion (sp + 0x10ac#64) 20 ∗
        (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ memRegion x.ret 24 ∗
        A.live outBuf ((x.input.length / 16 + 1) * 16) 1 ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
        hSplit.base.pool lim (M.stepEvents (aesEncEvents x) st) sf2)) ?_ ?_
  · refine Entails.trans ?_
      (sepConj_mono_right (Entails.trans (sepConj_mono_left hout_mr)
        (Entails.of_eq (sepConj_assoc _ _ _))))
    exact Entails.of_eq (by sep_ac_rfl)
  refine step_seg_post_alloc_stage (s0 := s0) hc hCallees x hks hsp_15 hne0 hiv hin
    hpc2 hrun2 hsp2 hv2 hx0_2 hx19_2 hx20_2 hx22_2 hx23_2 hx25_2 hx29_2
    fun s3 hpc3 hrun3 hsp3 hp23 hv3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx26_3 hx27_3 hx29_3 => ?_
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
      (CbcKeyState sp b x.key ∗ memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0x106c#64) 64 ∗
        byte16At (sp + 0x1050#64) (blockToBytesLE (bytesToBlock x.iv)) ∗
        (x.inA ↦ₛ x.input) ∗ memRegion outBuf (16 * (x.input.length / 16)) ∗
        (hw.storageAddr ↦₈ b) ∗ stackAt sp allocHookStack) ∗
      (spill16At sp (pkcs7TailBytes x.input) ∗
        memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16 ∗
        cbcSavedRegs s0 ∗ memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x410#64) 960 ∗
        memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
        memRegion (sp + 0x1060#64) 12 ∗ memRegion (sp + 0x10ac#64) 20 ∗
        (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ memRegion x.ret 24 ∗
        A.live outBuf ((x.input.length / 16 + 1) * 16) 1 ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
        hSplit.base.pool lim (M.stepEvents (aesEncEvents x) st) sf2) by sep_ac_rfl)) ?_
  refine step_loop_dispatch (s0 := s0) hc hCallees x b hsp_15 hk hin
    hpc3 hrun3 hsp3 hv3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx26_3 hx27_3 hx29_3
    fun s4 hpc4 hrun4 hsp4 hp34 hv4 hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx26_4 hx29_4 => ?_
  have hframe_eq : (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) = x.frame := rfl
  refine SepWP.weaken_pre (P' :=
      (CbcKeyState sp b x.key ∗ spill16At sp (pkcs7TailBytes x.input) ∗
        memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0x106c#64) 64 ∗
        byte16At (sp + 0x1050#64) (blockToBytesLE
          (cbcChain (Spec.Aes256.aes256Enc (bytesToKey32 x.key)) (bytesToBlock x.iv) (ptFullBlocks x.input))) ∗
        (outBuf ↦ₛ (cbcEncBlocks (Spec.Aes256.aes256Enc (bytesToKey32 x.key))
          (bytesToBlock x.iv) (ptFullBlocks x.input)).flatMap blockToBytesLE) ∗
        memRegion (outBuf + BitVec.ofNat 64 (16 * (x.input.length / 16))) 16 ∗
        (hw.storageAddr ↦₈ b) ∗ stackAt sp allocHookStack) ∗
      (cbcSavedRegs s0 ∗ memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x410#64) 960 ∗
        memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
        memRegion (sp + 0x1060#64) 12 ∗ memRegion (sp + 0x10ac#64) 20 ∗
        memRegion x.ret 24 ∗ A.live outBuf ((x.input.length / 16 + 1) * 16) 1 ∗
        x.frame ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
        hSplit.base.pool lim (M.stepEvents (aesEncEvents x) st) sf2))
    (by rw [← hframe_eq]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine step_tail_dispatch (s0 := s0) hc hCallees x b hsp_15 hk
    hpc4 hrun4 hsp4 hv4 hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx26_4 hx29_4
    fun s5 hpc5 hrun5 hsp5 hp45 hv5 hx19_5 hx20_5 hx21_5 _hx29_5 => ?_
  exact step_drop_and_epilogue A lim hc hCallees x st b hsp_def hsp_15 hne0 hin
    hacp2 ((hp23.trans hp34).trans hp45) hv5 hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5

private theorem aes256CbcEncrypt_sep_cond_of_reachable_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program}
    {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (aes256CbcEncryptReachableInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
        allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr))
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoDataSep hw.rconAddr aesRconBytes
        (aesEncBudgetCondSpec Spec.Aes256.aes256Enc M A lim)) := by
  have hc := CbcEncCode.of_hasInstrs hCode
  apply subroutine_ok_of_sepWPp_pure_oom
    (φ := fun (x, st) s0 sf => ¬ FitsEvents M lim st (aesEncEvents x) ∧ OomPreserved s0 sf)
    (by rintro ⟨_, _⟩ _ _; rfl)
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [withRoDataSep, aesEncBudgetCondSpec] at hpre
  rw [hSplit.pool_eq lim st s0] at hpre
  have hpull :
      ((hw.rconAddr ↦ᵣ aesRconBytes) ∗
        (⌜s0.readReg64 .x0 = x.inA ∧ (s0.readReg64 .x1).toNat = x.input.length ∧
          s0.readReg64 .x2 = x.keyA ∧ s0.readReg64 .x3 = 32#64 ∧
          s0.readReg64 .x4 = x.ivA ∧ s0.readReg64 .x5 = 16#64 ∧
          s0.readReg64 .x8 = x.ret ∧ x.key.length = 32 ∧ x.iv.length = 16 ∧
          x.input.length < 2 ^ 40⌝ ∗
         (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ memRegion x.ret 24 ∗
         (∃∗ b0 : BitVec 8, (hw.storageAddr ↦₈ b0) ∗ hSplit.base.pool lim st s0) ∗
         stackAt s0.sp extHookStack)) ∗ R =
      ⌜s0.readReg64 .x0 = x.inA ∧ (s0.readReg64 .x1).toNat = x.input.length ∧
        s0.readReg64 .x2 = x.keyA ∧ s0.readReg64 .x3 = 32#64 ∧
        s0.readReg64 .x4 = x.ivA ∧ s0.readReg64 .x5 = 16#64 ∧
        s0.readReg64 .x8 = x.ret ∧ x.key.length = 32 ∧ x.iv.length = 16 ∧
        x.input.length < 2 ^ 40⌝ ∗
      (∃∗ b0 : BitVec 8,
        (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
        memRegion x.ret 24 ∗ (hw.storageAddr ↦₈ b0) ∗ hSplit.base.pool lim st s0 ∗
        stackAt s0.sp extHookStack ∗ R) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; sep_ac_rfl
  rw [hpull, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hin⟩, hrest⟩
  rw [satisfies_sepExists] at hrest; rcases hrest with ⟨b0, hrest⟩
  generalize hsp_def : s0.sp - 4384#64 = sp
  have hsp0_15 : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp0
  have hsp_15 : sp &&& 15#64 = 0#64 := hsp_def ▸ sp_sub4384_and_15 hsp0_15
  have hsf_init : stackFrameAt s0.sp 4384 =
      stackFrameAt s0.sp 96 ∗ memRegion sp 64 ∗ memRegion (sp + 0x040#64) 976 ∗
      memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
      memRegion (sp + 0x8c0#64) 960 ∗ memRegion (sp + 0xc80#64) 16 ∗
      memRegion (sp + 0xc90#64) 960 ∗ memRegion (sp + 0x1050#64) 16 ∗
      memRegion (sp + 0x1060#64) 12 ∗ memRegion (sp + 0x106c#64) 64 ∗
      memRegion (sp + 0x10ac#64) 20 := by subst hsp_def; exact stackFrameAt_4384_eq s0.sp
  have hext_init : stackAt s0.sp extHookStack =
      stackFrameAt s0.sp 4384 ∗
        (stackAt sp allocHookStack ∗ stackFrameAt (s0.sp - 4384#64 - 4096#64) 7904) := by
    conv_rhs => arg 2; arg 1; rw [← hsp_def]
    exact extHookStack_split_4384 s0.sp
  let F0 := stackFrameAt (s0.sp - 4384#64 - 4096#64) 7904
  let F_pre :=
    memRegion sp 64 ∗ memRegion (sp + 0x1050#64) 16 ∗ memRegion (sp + 0x1060#64) 12 ∗
    memRegion (sp + 0x106c#64) 64 ∗ memRegion (sp + 0x10ac#64) 20 ∗
    (x.inA ↦ₛ x.input) ∗ memRegion x.ret 24
  let P0 :=
    (stackFrameAt s0.sp 96 ∗ memRegion (sp + 0x040#64) 976 ∗ memRegion (sp + 0x410#64) 960 ∗
     memRegion (sp + 0x7d0#64) 240 ∗ memRegion (sp + 0x8c0#64) 960 ∗
     memRegion (sp + 0xc80#64) 16 ∗ memRegion (sp + 0xc90#64) 960 ∗
     (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗
     (hw.storageAddr ↦₈ b0) ∗ hSplit.base.pool lim st s0 ∗ stackAt sp allocHookStack) ∗ F_pre
  have hm0 : s0.mem ⊨ P0 ∗ (F0 ∗ R) := by
    rw [hext_init, hsf_init] at hrest; dsimp only [P0, F_pre, F0]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  refine ⟨P0, F0, hm0, ?_⟩
  apply SepWPp.of_sepWP (mid := allocZeroedAddr)
  refine step_seg_pre_alloc hc hCallees x st b0 hsp_def hpc hrun hsp0
    hx0 hx1 hx2 hx3 hx4 hx5 hx8 hk hiv hin
    fun s1 b ksBytes hks hpc1 hrun1 hsp1 hp1 hv1 hx0_1 hx1_1 hx19_1 hx20_1
      hx22_1 hx23_1 _hx24_1 hx25_1 hx29_1 => ?_
  let sm := P.evalInst (.bl (allocZeroedAddr - (fnAddr + 0x0c0#64))) (s1.setPC (fnAddr + 0x0c0#64))
  have hmem_sm : sm.mem = s1.mem := by simp [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  have hpc_sm : sm.pc = allocZeroedAddr := by
    simp [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]; bv_omega
  have hrun_sm : sm.status = .Running := by
    simp [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hrun1]
  apply SepWP.step_pure hpc1 hrun1 hc.bl_alloc rfl hmem_sm
  apply SepWP.done hpc_sm hrun_sm
  have hsp_sm : sm.sp = sp := by simp [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hsp1]
  have hspAl_sm : sm.spAligned = true := spAligned_of_eq hsp_sm hsp_15
  have hlr_sm : sm.readReg64 .lr = fnAddr + 0x0c4#64 := by
    simp [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  have hx0_sm : sm.readReg64 .x0 = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) := by
    simpa [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx0_1
  have hx1_sm : sm.readReg64 .x1 = 1#64 := by
    simpa [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx1_1
  have hx19_sm : sm.readReg64 (.gpr 19#5) = x.ret := by
    simpa [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx19_1
  have hx20_sm : sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ((x.input.length / 16 + 1) * 16) := by
    simpa [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx20_1
  have hx22_sm : sm.readReg64 (.gpr 22#5) = x.inA := by
    simpa [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx22_1
  have hx23_sm : sm.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length := by
    simpa [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx23_1
  have hx25_sm : sm.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (16 * (x.input.length / 16)) := by
    simpa [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx25_1
  have hx29_sm : sm.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := by
    simpa [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm] using hx29_1
  have hv_sm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    simpa [sm, Program.evalInst, execInstWithSvc, calleeSavedVRegs, arm64_norm, wp_norm] using hv1
  have hp1_sm : CbcPreserved s1 sm := CbcPreserved.of_proj_perm
    (by simp [sm, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]) (by simp [hmem_sm])
  have hp_sm : CbcPreserved s0 sm := hp1.trans hp1_sm
  have hpool_sm : hSplit.base.pool lim st sm = hSplit.base.pool lim st s1 :=
    hp1_sm.pool_eq hSplit.base lim st
  let ctLen := (x.input.length / 16 + 1) * 16
  let FrameAl :=
    cbcSavedRegs s0 ∗ memRegion sp 64 ∗ memRegion (sp + 0x040#64) 976 ∗
    memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
    ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)) ∗ memRegion (sp + 0xc90#64) 960 ∗
    memRegion (sp + 0x1050#64) 16 ∗ memRegion (sp + 0x1060#64) 12 ∗
    memRegion (sp + 0x106c#64) 64 ∗ memRegion (sp + 0x10ac#64) 20 ∗
    (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
    memRegion x.ret 24 ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ b)
  have hx0_nat : (sm.readReg64 .x0).toNat = ctLen := by
    rw [hx0_sm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [ctLen]; omega)]
  have hx1_nat : (sm.readReg64 .x1).toNat = 1 := by rw [hx1_sm]; rfl
  have hLay : RustLayoutOk ctLen 1 := ⟨⟨by dsimp [ctLen]; omega, ⟨0, rfl⟩, by dsimp [ctLen]; omega⟩, by decide⟩
  refine SepWPp.call_wpp (x := (ctLen, 1, st)) (ret_pc := fnAddr + 0x0c4#64)
    (F := FrameAl) hCallees.allocZeroed_ok hpc_sm hrun_sm hspAl_sm hlr_sm ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ ⟨_, hp⟩ => by
      dsimp only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase] at hp
      exact False.elim (not_satisfies_false_sepConj hp))
    ?_ ?_
  · intro R' hm'; dsimp only [F_pre] at hm'
    dsimp only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase, FrameAl]
    rw [hsp_sm, hpool_sm, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_nat, hx1_nat, hLay⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'⟩
  · intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 hcs_sf2
    dsimp only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase]
    rw [hsp_sm, sepConj_assoc]; refine SepWPp.pure_elim fun hacp_al => ?_
    have hacp2 : AllocCallPreserved s0 sf2 := allocCallPreserved_trans hp_sm.1 hacp_al
    have hsp2 : sf2.sp = sp := hsp_sf2.trans hsp_sm
    have hv2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := hcs_sf2.vregs.trans hv_sm
    have hx19_2 : sf2.readReg64 (.gpr 19#5) = x.ret := hcs_sf2.readReg64_x19.trans hx19_sm
    have hx20_2 : sf2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 ctLen := hcs_sf2.readReg64_x20.trans hx20_sm
    have hx22_2 : sf2.readReg64 (.gpr 22#5) = x.inA := hcs_sf2.readReg64_x22.trans hx22_sm
    have hx23_2 : sf2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 x.input.length := hcs_sf2.readReg64_x23.trans hx23_sm
    have hx25_2 : sf2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (16 * (x.input.length / 16)) := hcs_sf2.readReg64_x25.trans hx25_sm
    have hx29_2 : sf2.readReg64 (.gpr 29#5) = sp + 0x10c0#64 := hcs_sf2.readReg64_x29.trans hx29_sm
    by_cases hnull : sf2.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte]
      have hPullNull :
          (hSplit.base.pool lim st sf2 ∗ stackAt sp allocHookStack ∗ ⌜NullAllowed ctLen 1⌝) ∗ FrameAl =
          ⌜NullAllowed ctLen 1⌝ ∗
            (stackAt (s0.sp - 4384#64) allocHookStack ∗ (hSplit.base.pool lim st sf2 ∗ FrameAl)) := by
        rw [← hsp_def]; dsimp only [FrameAl]; sep_ac_rfl
      rw [hPullNull]
      refine SepWPp.pure_elim fun hna => ?_
      exact cbc_panic_tail A lim hc hCallees.handleError_ok x st
        (hSplit.base.pool lim st sf2 ∗ FrameAl) F0 R s0 sf2 hna hsp0 hpc_sf2 hrun_sf2
        (by rw [hsp2, ← hsp_def]) hnull hacp2.1 hacp2.2.1
    · simp only [hnull, ↓reduceIte, ← hSplit.live_eq]
      let outBuf := sf2.readReg64 .x0
      have hne0 : outBuf ≠ 0#64 := hnull
      have hPullOk :
          (hSplit.base.pool lim (M.stepEvents (rustAllocEvents ctLen 1) st) sf2 ∗
            stackAt sp allocHookStack ∗
            (⌜outBuf.toNat % 1 = 0⌝ ∗ A.live outBuf ctLen 1 ∗
              (outBuf ↦ₛ List.replicate ctLen 0#8))) ∗ FrameAl =
          ⌜outBuf.toNat % 1 = 0⌝ ∗
            (cbcSavedRegs s0 ∗ memRegion sp 64 ∗ memRegion (sp + 0x040#64) 976 ∗
             memRegion (sp + 0x410#64) 960 ∗ memRegion (sp + 0x7d0#64) 240 ∗
             ((sp + 0x8c0#64) ↦ₛ (ksBytes ++ x.iv)) ∗ memRegion (sp + 0xc90#64) 960 ∗
             memRegion (sp + 0x1050#64) 16 ∗ memRegion (sp + 0x1060#64) 12 ∗
             memRegion (sp + 0x106c#64) 64 ∗ memRegion (sp + 0x10ac#64) 20 ∗
             (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
             memRegion x.ret 24 ∗ A.live outBuf ctLen 1 ∗
             (outBuf ↦ₛ List.replicate ctLen 0#8) ∗
             (hw.rconAddr ↦ᵣ aesRconBytes) ∗ (hw.storageAddr ↦₈ b) ∗
             hSplit.base.pool lim (M.stepEvents (aesEncEvents x) st) sf2 ∗
             stackAt sp allocHookStack) := by
        dsimp only [FrameAl, outBuf, ctLen, aesEncEvents]; sep_ac_rfl
      rw [hPullOk]
      refine SepWPp.pure_elim fun _ => ?_
      exact cbc_nonnull_tail A lim hc hCallees x st hks hsp_def hsp_15 hne0 hk hiv hin
        hacp2 hv2 hpc_sf2 hrun_sf2 hsp2 rfl hx19_2 hx20_2 hx22_2 hx23_2 hx25_2 hx29_2
  · intro sf_oom R' _ ho
    dsimp only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase] at ho
    rw [satisfies_pure_sepConj] at ho ⊢
    rcases ho with ⟨⟨hnfit, hoom2⟩, hFR⟩
    exact ⟨⟨hnfit, hp_sm.toOomPreserved.trans hoom2⟩, Satisfies.drop_left hFR⟩

end

/-! ## 2. Full-Instruction & `WordTree` Consumer Ladder (`withRoData hw.rconAddr aesRconBytes`) -/

theorem aes256CbcEncrypt_cond_ok {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs} [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr : BitVec 64}
    {p : Aes256CbcEncryptPanicSyms}
    (hCode : hasInstrs P fnAddr (aes256CbcEncryptInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p))
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesEncBudgetCondSpec Spec.Aes256.aes256Enc M A lim)) :=
  subroutine_ok_roData_cond_of_sep
    (aes256CbcEncrypt_sep_cond_of_reachable_ok A lim (hasInstrs_prefix hCode) hCallees)

theorem aes256CbcEncrypt_noOom_ok {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs} [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr : BitVec 64}
    {p : Aes256CbcEncryptPanicSyms}
    (hCode : hasInstrs P fnAddr (aes256CbcEncryptInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p))
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesEncNoOomSpec Spec.Aes256.aes256Enc M A lim)) :=
  subroutine_ok_roData_noOom_of_cond (aes256CbcEncrypt_cond_ok A lim hCode hCallees)

theorem aes256CbcEncrypt_keepsFs_ok {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs} [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr : BitVec 64}
    {p : Aes256CbcEncryptPanicSyms}
    (hCode : hasInstrs P fnAddr (aes256CbcEncryptInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p))
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (keepsFs (aesEncBudgetSpec Spec.Aes256.aes256Enc M A lim))) :=
  subroutine_ok_roData_keepsFs_of_noOom (aes256CbcEncrypt_noOom_ok A lim hCode hCallees)

theorem aes256CbcEncrypt_budget_ok {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs} [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr : BitVec 64}
    {p : Aes256CbcEncryptPanicSyms}
    (hCode : hasInstrs P fnAddr (aes256CbcEncryptInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p))
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesEncBudgetSpec Spec.Aes256.aes256Enc M A lim)) :=
  subroutine_ok_roData_budget_of_keepsFs (aes256CbcEncrypt_keepsFs_ok A lim hCode hCallees)

theorem aes256CbcEncrypt_fnBudget_ok {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {P : Program} {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs} [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr : BitVec 64}
    {p : Aes256CbcEncryptPanicSyms}
    (hCode : hasInstrs P fnAddr (aes256CbcEncryptInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p))
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesEncFnBudgetSpec
          (fun pt k iv => aesCbcEncrypt Spec.Aes256.aes256Enc (bytesToKey32 k) (bytesToBlock iv) pt)
          M A lim)) :=
  aesEncFnBudgetSpec_block_eq Spec.Aes256.aes256Enc M A lim ▸
    aes256CbcEncrypt_budget_ok A lim hCode hCallees

theorem aes256CbcEncrypt_cond_of_wordTree_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program} {t : WordTree} (n : Nat)
    {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs} [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64} {p : Aes256CbcEncryptPanicSyms}
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 595 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact ProofLib.ProgramReflection.hookAtOff?_eq_none_of_isNone
        (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcEncryptInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
        allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p) = true)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesEncBudgetCondSpec Spec.Aes256.aes256Enc M A lim)) :=
  aes256CbcEncrypt_cond_ok A lim
    (hasShimInstrs_of_wordTree n hcode hwf
      (fun i hi => hhook i
        ((aes256CbcEncryptInstrs_length fnAddr hw keyScheduleAddr encryptAddr shimAddr
          allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p) ▸ hi))
      hok)
    hCallees

theorem aes256CbcEncrypt_noOom_of_wordTree_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program} {t : WordTree} (n : Nat)
    {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs} [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64} {p : Aes256CbcEncryptPanicSyms}
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 595 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact ProofLib.ProgramReflection.hookAtOff?_eq_none_of_isNone
        (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcEncryptInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
        allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p) = true)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesEncNoOomSpec Spec.Aes256.aes256Enc M A lim)) :=
  subroutine_ok_roData_noOom_of_cond
    (aes256CbcEncrypt_cond_of_wordTree_ok A lim n hcode hwf hhook hok hCallees)

theorem aes256CbcEncrypt_keepsFs_of_wordTree_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program} {t : WordTree} (n : Nat)
    {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs} [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64} {p : Aes256CbcEncryptPanicSyms}
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 595 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact ProofLib.ProgramReflection.hookAtOff?_eq_none_of_isNone
        (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcEncryptInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
        allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p) = true)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (keepsFs (aesEncBudgetSpec Spec.Aes256.aes256Enc M A lim))) :=
  subroutine_ok_roData_keepsFs_of_noOom
    (aes256CbcEncrypt_noOom_of_wordTree_ok A lim n hcode hwf hhook hok hCallees)

theorem aes256CbcEncrypt_budget_of_wordTree_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program} {t : WordTree} (n : Nat)
    {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs} [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64} {p : Aes256CbcEncryptPanicSyms}
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 595 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact ProofLib.ProgramReflection.hookAtOff?_eq_none_of_isNone
        (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcEncryptInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
        allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p) = true)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesEncBudgetSpec Spec.Aes256.aes256Enc M A lim)) :=
  subroutine_ok_roData_budget_of_keepsFs
    (aes256CbcEncrypt_keepsFs_of_wordTree_ok A lim n hcode hwf hhook hok hCallees)

theorem aes256CbcEncrypt_fnBudget_of_wordTree_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {P : Program} {t : WordTree} (n : Nat)
    {fnAddr : BitVec 64} {hw : Aes256EncHwAddrs} [PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr encryptAddr shimAddr allocZeroedAddr
     memcpyAddr memsetAddr handleErrorAddr : BitVec 64} {p : Aes256CbcEncryptPanicSyms}
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 595 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact ProofLib.ProgramReflection.hookAtOff?_eq_none_of_isNone
        (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcEncryptInstrs fnAddr hw keyScheduleAddr encryptAddr shimAddr
        allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr p) = true)
    (hCallees : Aes256CbcEncryptCallees M A lim P hw keyScheduleAddr encryptAddr shimAddr
      allocZeroedAddr memcpyAddr memsetAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesEncFnBudgetSpec
          (fun pt k iv => aesCbcEncrypt Spec.Aes256.aes256Enc (bytesToKey32 k) (bytesToBlock iv) pt)
          M A lim)) :=
  aesEncFnBudgetSpec_block_eq Spec.Aes256.aes256Enc M A lim ▸
    aes256CbcEncrypt_budget_of_wordTree_ok A lim n hcode hwf hhook hok hCallees

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEncrypt

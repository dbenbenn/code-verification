/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Model
public import ProofLib.StdStartup.StdDetect
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.AesDecErrRoBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
import ProofLib.Hoare.SubroutineOk
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologFast
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologAlloc
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftCommon
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuad
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftTail
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Unpad
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Epilog

/-!
# Backend Join & Core `900`-Instruction `subroutine_ok` (`CbcDec.UnpadEpilog`)

Joins the `b = 1#8` (`HwLoopContract`) and `b ≠ 1#8` (`SoftQuad` + `SoftTail`) decryption backends
at `fnAddr + 0xd20#64` into `cbc_unpad` and `cbc_epilogue`, establishing
`aes256CbcDecrypt_errRo_cond_of_hwLoop_ok` over all `900` instructions.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.UnpadEpilog

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.StdStartup (hasInstrs)
open VerifiedLibraries.RustStd (allocCallPreserved_trans)
open CryptoGames.CBC (bytesToBlock blockToBytesLE chunks16 cbcDecryptBlocks pkcs7Unpad)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcDecrypt)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved
   OomPreserved FitsEvents rustAllocEvents)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common
  (withRoData withRoDataSep SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model (aes256KeyScheduleFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved fsKeys256At)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (aesRconBytes armv8ExpandKey armv8InvExpandedKeys roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (Aes256DecHwAddrs Aes256CbcDecryptPanicSyms Aes256CbcDecryptCallees HwLoopContract
   aes256CbcDecryptInstrs hasInstrs_hwLoop_of_full)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs (CbcDecCodeSegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
  (aesDecEvents aesDecBudgetCondSpec aesDecBudgetCondSpecErrRo aesCbcDecrypt_of_aligned
   cbcChainAt cbcChainAt_length cbcPrefixBytes_full)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules (sepWP_weaken_pre)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
  (sepWPp_exists_left extHookStack_split_3968 spAligned_sub3968
   memRegion24_eq_exists_pts cbcSlack cbcPost cbcPanic cbcOom
   savedCells96 savedStack96 slots56 stackFrameAt96_eq_savedCells stackFrameAt56_eq_slots
   stackFrame3968_split)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologFast
  (keyBytes960_unpack_hw keyBytes960_unpack_sw cbc_prologue_step cbc_fast_reject)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PrologAlloc (cbc_aligned_init)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftCommon (cbcSoftWork)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftQuad (cbc_quad_loop)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftTail (cbc_tail_loop)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Unpad (cbc_unpad)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Epilog
  (work2824_split_hw work2824_split_sw decryptor976_pack_hw decryptor976_pack_sw cbc_epilogue)

set_option maxHeartbeats 550000 in
theorem aes256CbcDecrypt_errRo_cond_sep_of_hwLoop_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr : BitVec 64}
    {panics : Aes256CbcDecryptPanicSyms} {errStr1Relax errStr2Relax : Bool}
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoDataSep hw.rconAddr aesRconBytes
        (aesDecBudgetCondSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim)) := by
  refine subroutine_ok_of_sepWPp_pure_oom
    (φ := fun p s0 sf =>
      ¬ FitsEvents M lim p.2 (aesDecEvents Spec.Aes256.aes256Dec p.1) ∧ OomPreserved s0 sf)
    (by rintro ⟨x, st⟩ s0 sf; rfl) ?_
  rintro ⟨x, st⟩ R s0 hpc0 hrun0 hm0 hsp0
  have cs := CbcDecCodeSegs.of_hasInstrs hCode
  dsimp only [withRoDataSep, aesDecBudgetCondSpecErrRo, aesDecBudgetCondSpec] at hm0
  rw [sepConj_left_comm (hw.rconAddr ↦ᵣ aesRconBytes),
      sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hm0
  rcases hm0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hkey32, hiv16, hlt40⟩, hm0⟩
  rw [extHookStack_split_3968 s0.sp, stackFrame3968_split s0.sp] at hm0
  let P_init : SepProp :=
    memRegion x.ret 24 ∗ stackFrameAt (s0.sp - 3912#64) 56 ∗ stackFrameAt s0.sp 96 ∗
    memRegion (s0.sp - 3968#64 + 56#64) 3816 ∗
    (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
    (hw.rconAddr ↦ᵣ aesRconBytes) ∗ A.pool lim st s0 ∗ stackAt (s0.sp - 3968#64) allocHookStack
  refine ⟨P_init, cbcSlack s0,
    Satisfies.mono (Entails.of_eq (by dsimp only [P_init, cbcSlack]; sep_ac_rfl)) hm0, ?_⟩
  dsimp only [P_init]
  rw [memRegion24_eq_exists_pts x.ret]
  refine sepWPp_exists_left fun r0 => sepWPp_exists_left fun r1 => sepWPp_exists_left fun r2 => ?_
  rw [sepConj_left_comm _ (stackFrameAt (s0.sp - 3912#64) 56), stackFrameAt56_eq_slots s0.sp]
  refine sepWPp_exists_left fun w0 => sepWPp_exists_left fun w1 => sepWPp_exists_left fun w2 =>
    sepWPp_exists_left fun w3 => sepWPp_exists_left fun w4 => sepWPp_exists_left fun w5 =>
    sepWPp_exists_left fun w6 => ?_
  refine SepWPp.weaken_pre
    (P' := stackFrameAt s0.sp 96 ∗
      slots56 (s0.sp - 3968#64) w0 w1 w2 w3 w4 w5 w6 ∗
      ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
      memRegion (s0.sp - 3968#64 + 56#64) 3816 ∗
      (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
      (hw.rconAddr ↦ᵣ aesRconBytes) ∗ A.pool lim st s0 ∗ stackAt (s0.sp - 3968#64) allocHookStack)
    (Entails.of_eq (by sep_ac_rfl)) ?_
  rw [stackFrameAt96_eq_savedCells s0.sp]
  refine sepWPp_exists_left fun c0 => sepWPp_exists_left fun c1 => sepWPp_exists_left fun c2 =>
    sepWPp_exists_left fun c3 => sepWPp_exists_left fun c4 => sepWPp_exists_left fun c5 =>
    sepWPp_exists_left fun c6 => sepWPp_exists_left fun c7 => sepWPp_exists_left fun c8 =>
    sepWPp_exists_left fun c9 => sepWPp_exists_left fun c10 => sepWPp_exists_left fun c11 => ?_
  let ProlRest :=
    ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
    memRegion (s0.sp - 3968#64 + 56#64) 3816 ∗
    (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
    (hw.rconAddr ↦ᵣ aesRconBytes) ∗ A.pool lim st s0 ∗ stackAt (s0.sp - 3968#64) allocHookStack
  refine SepWPp.weaken_pre
    (P' := slots56 (s0.sp - 3968#64) w0 w1 w2 w3 w4 w5 w6 ∗
      savedCells96 s0.sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 ∗ ProlRest)
    (Entails.of_eq (by dsimp only [ProlRest]; sep_ac_rfl)) ?_
  apply SepWPp.of_sepWP (mid := fnAddr + 0x028#64)
  refine cbc_prologue_step cs.prologue hpc0 hrun0 hsp0
    fun s1 hpc1 hrun1 hsp1 hx29_1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx8_1 _ hv1 hpure1 => ?_
  refine SepWP.done hpc1 hrun1 ?_
  have hx1_nat : (s1.readReg64 .x1).toNat = x.input.length := by rw [hx1_1, hx1]
  rw [hx0] at *
  by_cases hbad : x.input.length = 0 ∨ x.input.length % 16 ≠ 0
  · refine SepWPp.weaken_pre
      (Entails.of_eq (by dsimp only [ProlRest, AesCall.frame]; sep_ac_rfl))
      (cbc_fast_reject A lim cs x st r0 r1 r2 0#64 w1 w2 w3 w4 w5 x.inA R s0 s1
        hbad hsp0 hpc1 hrun1 hsp1 hx1_nat (hx8_1.trans hx8) hv1 hpure1)
  · have hpos : 0 < x.input.length := by omega
    have hmod16 : x.input.length % 16 = 0 := by omega
    refine SepWPp.weaken_pre
      (Entails.of_eq (by dsimp only [ProlRest]; sep_ac_rfl))
      (cbc_aligned_init A lim cs hCal x st r0 r1 r2 w1 w2 w3 w4 w5 R s0 s1
        hbad hlt40 hkey32 hiv16 hsp0 hpc1 hrun1 hsp1 hx29_1 hx1_nat
        (hx2_1.trans hx2) (hx3_1.trans hx3) (hx4_1.trans hx4) (hx5_1.trans hx5)
        (hx8_1.trans hx8) hv1 hpure1
        fun outBuf b keyBytes960 sm hkb houtNe0 hpc_m hrun_m hsp_m hx9_m hx22_m hx24_m hx25_m _ hv_m hpres_m => ?_)
    let sp := s0.sp - 3968#64
    let st1 := M.stepEvents (rustAllocEvents x.input.length 1) st
    let numBlocks := x.input.length / 16
    let rawBs := (cbcDecryptBlocks (Spec.Aes256.aes256Dec (bytesToKey32 x.key))
      (bytesToBlock x.iv) (chunks16 x.input)).flatMap blockToBytesLE
    have hnb_pos : 0 < numBlocks := by dsimp only [numBlocks]; omega
    have h16_nb : 16 * numBlocks = x.input.length := by dsimp only [numBlocks]; omega
    have hraw_len : rawBs.length = 16 * numBlocks := by
      dsimp only [rawBs]
      rw [← cbcPrefixBytes_full x.key x.iv x.input,
          PureLemmas.cbcPrefixBytes_length (Nat.le_refl numBlocks)]
    have haes_eq : aesCbcDecrypt Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock x.iv)
        x.input = pkcs7Unpad rawBs :=
      aesCbcDecrypt_of_aligned Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock x.iv) hbad
    have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
    have hspAl : (sp &&& 15#64 == 0#64) = true := spAligned_sub3968 hspAl0
    let TailCommon :=
      memRegion (sp + 0xf10#64) 16 ∗ hSplit.base.live outBuf x.input.length 1 ∗
      (hw.storageAddr ↦₈ b) ∗ hSplit.base.pool lim st1 sm ∗
      ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
      (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ (hw.rconAddr ↦ᵣ aesRconBytes) ∗ savedStack96 s0
    have hAtUnpad : ∀ (w1' : BitVec 64) (s_unp : State),
        s_unp.pc = fnAddr + 0xd20#64 → s_unp.status = .Running → s_unp.sp = sp →
        s_unp.readReg64 .x23 = BitVec.ofNat 64 x.input.length →
        s_unp.readReg64 .x26 = BitVec.ofNat 64 numBlocks →
        calleeSavedVRegs s_unp = calleeSavedVRegs s0 → PureStepPreserved sm s_unp →
        SepWPp P (s0.readReg64 .lr) s_unp
          (slots56 sp 0#64 w1' (BitVec.ofNat 64 numBlocks) (BitVec.ofNat 64 x.input.length) x.ret outBuf x.inA ∗
            memRegion (sp + 56#64) 2824 ∗ memRegion (sp + 0xb40#64) 976 ∗
            (outBuf ↦ₛ rawBs) ∗ (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ TailCommon)
          (cbcPost A lim hw.rconAddr errStr1Addr errStr2Addr x st R s0)
          (cbcPanic A lim x st R s0) (cbcOom M lim x st s0) := by
      intro w1' s_unp hpc_u hrun_u hsp_u hx23_u hx26_u hv_u hpure_u
      let mid_epi := if (pkcs7Unpad rawBs).isSome then fnAddr + 0xda8#64 else fnAddr + 0xd64#64
      apply SepWPp.of_sepWP (mid := mid_epi)
      let UnpRest :=
        (sp ↦₆₄ 0#64) ∗ ((sp + 8#64) ↦₆₄ w1') ∗ ((sp + 16#64) ↦₆₄ BitVec.ofNat 64 numBlocks) ∗
        ((sp + 24#64) ↦₆₄ BitVec.ofNat 64 x.input.length) ∗ ((sp + 32#64) ↦₆₄ x.ret) ∗
        ((sp + 48#64) ↦₆₄ x.inA) ∗ memRegion (sp + 56#64) 2824 ∗ memRegion (sp + 0xb40#64) 976 ∗
        (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ TailCommon
      refine sepWP_weaken_pre (Entails.of_eq (by dsimp only [slots56, UnpRest]; sep_ac_rfl))
        (cbc_unpad cs.unpad cs.okPreDrop rawBs numBlocks UnpRest s0 s_unp
          hraw_len hnb_pos (by omega) hspAl hpc_u hrun_u hsp_u
          (by simpa only [h16_nb] using hx23_u) hx26_u hv_u
          fun s_epi hrun_e hsp_e hx0_e hx23_e hv_e hpure_e hout_e => ?_)
      have hpc_mid : s_epi.pc = mid_epi := by
        rcases hout_e with ⟨_, _, hpk, hpc_e, _⟩ | ⟨hpk, hpc_e⟩ <;> simp [mid_epi, hpk, hpc_e]
      refine SepWP.done hpc_mid hrun_e ?_
      have hpure_all : PureStepPreserved sm s_epi := hpure_u.trans hpure_e
      have hpool_e : hSplit.base.pool lim st1 s_epi = hSplit.base.pool lim st1 sm :=
        hpure_all.pool_eq hSplit.base lim st1
      have hpres_e : AllocCallPreserved s0 s_epi :=
        allocCallPreserved_trans hpres_m hpure_all.allocCallPreserved
      have hx23_e' : s_epi.readReg64 .x23 = BitVec.ofNat 64 x.input.length := by
        simpa only [h16_nb] using hx23_e
      have hout_e' :
          (∃ ptLen : Nat, ptLen < x.input.length ∧ pkcs7Unpad rawBs = some (rawBs.take ptLen) ∧
            s_epi.pc = fnAddr + 0xda8#64 ∧ s_epi.readReg64 .x21 = BitVec.ofNat 64 ptLen) ∨
          (pkcs7Unpad rawBs = none ∧ s_epi.pc = fnAddr + 0xd64#64) := by
        simpa only [h16_nb] using hout_e
      exact SepWPp.weaken_pre
        (Entails.of_eq (by
          dsimp only [UnpRest, TailCommon, slots56, AesCall.frame, sp, st1]
          rw [← hpool_e]; sep_ac_rfl))
        (cbc_epilogue A lim cs hCal x st b rawBs r0 r1 r2 0#64 w1'
          (BitVec.ofNat 64 numBlocks) (BitVec.ofNat 64 x.input.length) R s0 s_epi
          hbad hlt40 hsp0 houtNe0 (hraw_len.trans h16_nb) haes_eq
          hrun_e hsp_e hx0_e hx23_e' hv_e hpres_e hout_e')
    by_cases hb1 : b = 1#8
    · subst hb1; simp only [↓reduceIte] at hpc_m
      apply SepWPp.of_sepWP (mid := fnAddr + 0xd20#64)
      have hout_mem : (outBuf ↦ₛ List.replicate x.input.length 0#8) ⊢ memRegion outBuf x.input.length := by
        simpa only [List.length_replicate] using
          pointsToBytes_entails_memRegion outBuf (List.replicate x.input.length 0#8)
      let HwRest :=
        (sp ↦₆₄ 0#64) ∗ ((sp + 8#64) ↦₆₄ w1) ∗ ((sp + 32#64) ↦₆₄ x.ret) ∗
        memRegion (sp + 0x038#64) 168 ∗ memRegion (sp + 0x0e8#64) 968 ∗
        memRegion (sp + 0x5c0#64) 688 ∗ memRegion (sp + 0x980#64) 208 ∗
        memRegion (sp + 0xa60#64) 224 ∗ memRegion (sp + 0xb40#64) 240 ∗
        memRegion (sp + 0xd20#64) 480 ∗ TailCommon
      refine sepWP_weaken_pre ?_
        (hHwLoop (hasInstrs_hwLoop_of_full hCode) hCal.memcpy_ok hCal.hwDecryptPar17_ok hCal.hwDecrypt_ok
          (fnAddr + 0xd20#64) sp outBuf x HwRest sm _ _
          hpos hmod16 hlt40 hkey32 hiv16 houtNe0 hpc_m hrun_m hsp_m (beq_iff_eq.mp hspAl)
          hx9_m hx24_m hx25_m fun s_unp hpc_u hrun_u hsp_u hx26_u hx23_u hv_u hpure_u => ?_)
      · have h4b0 : memRegion (sp + 0x4b0#64) 960 =
            memRegion (sp + 0x4b0#64) 272 ∗ memRegion (sp + 0x5c0#64) 688 := by
          rw [show (960 : Nat) = 272 + 688 from rfl, memRegion_split (sp + 0x4b0#64) 272 688 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
        have h870 : memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240 =
            memRegion (sp + 0x870#64) 272 ∗ memRegion (sp + 0x980#64) 208 := by
          rw [show memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240 =
                memRegion (sp + 0x870#64) 480 from by
                rw [show (480 : Nat) = 240 + 240 from rfl, memRegion_split (sp + 0x870#64) 240 240 (by decide)]
                simp only [BitVec.add_assoc, BitVec.reduceAdd],
              show (480 : Nat) = 272 + 208 from rfl, memRegion_split (sp + 0x870#64) 272 208 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
        have ha50 : memRegion (sp + 0xa50#64) 240 =
            memRegion (sp + 0xa50#64) 16 ∗ memRegion (sp + 0xa60#64) 224 := by
          rw [show (240 : Nat) = 16 + 224 from rfl, memRegion_split (sp + 0xa50#64) 16 224 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
        dsimp only [slots56, HwRest, TailCommon, sp, st1]
        rw [h4b0, ha50]
        refine Entails.trans (Entails.of_eq (show _ =
            ((sp + 0xb40#64) ↦ₛ keyBytes960) ∗ ((outBuf ↦ₛ List.replicate x.input.length 0#8) ∗
            ((memRegion (sp + 0x870#64) 240 ∗ memRegion (sp + 0x960#64) 240) ∗ _)) by sep_ac_rfl)) ?_
        rw [h870]
        exact Entails.trans (sepConj_mono (keyBytes960_unpack_hw hkb) (sepConj_mono_left hout_mem))
          (Entails.of_eq (by sep_ac_rfl))
      · refine SepWP.done hpc_u hrun_u ?_
        refine SepWPp.weaken_pre ?_
          (hAtUnpad w1 s_unp hpc_u hrun_u hsp_u hx23_u hx26_u (hv_u.trans hv_m) hpure_u)
        dsimp only [HwRest, slots56, rawBs, numBlocks]
        rw [work2824_split_hw sp]
        refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (sp + 0xb40#64) 240 ∗
              roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey x.key)) ∗
              memRegion (sp + 0xd20#64) 480 ∗ memRegion (sp + 0xf00#64) 16) ∗ _ by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left (decryptor976_pack_hw sp x.key))
          (Entails.of_eq (by sep_ac_rfl))
    · simp only [hb1, ↓reduceIte] at hpc_m
      apply SepWPp.of_sepWP (mid := fnAddr + 0xd20#64)
      let SwRest :=
        memRegion (sp + 0x038#64) 4 ∗ memRegion (sp + 0x0e4#64) 4 ∗
        memRegion (sp + 0x0e8#64) 968 ∗ memRegion (sp + 0x4f0#64) 896 ∗
        memRegion (sp + 0x8b0#64) 176 ∗ memRegion (sp + 0x960#64) 240 ∗
        memRegion (sp + 0xa50#64) 240 ∗ TailCommon
      refine sepWP_weaken_pre ?_
        (cbc_quad_loop (hSplit := hSplit) (outBuf := outBuf) cs hCal x 0#64 w1
          (BitVec.ofNat 64 numBlocks) (BitVec.ofNat 64 x.input.length) x.ret SwRest s0 sm
          hlt40 hkey32 hiv16 hspAl hpc_m hrun_m hsp_m hx22_m hx24_m hx25_m hv_m
          fun s_tail hpc_t hrun_t hsp_t hx22_t hx24_t _ hv_t hpure_t => ?_)
      · have h176 : memRegion (sp + 0x038#64) 168 ∗ memRegion (sp + 0x0e0#64) 8 =
            memRegion (sp + 0x038#64) 4 ∗ memRegion (sp + 0x03c#64) 168 ∗ memRegion (sp + 0x0e4#64) 4 := by
          rw [show memRegion (sp + 0x038#64) 168 ∗ memRegion (sp + 0x0e0#64) 8 =
                memRegion (sp + 0x038#64) 176 from by
                rw [show (176 : Nat) = 168 + 8 from rfl, memRegion_split (sp + 0x038#64) 168 8 (by decide)]
                simp only [BitVec.add_assoc, BitVec.reduceAdd],
              show (176 : Nat) = 4 + (168 + 4) from rfl, memRegion_split (sp + 0x038#64) 4 (168 + 4) (by decide),
              memRegion_split _ 168 4 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]; try sep_ac_rfl
        have h4b0 : memRegion (sp + 0x4b0#64) 960 =
            memRegion (sp + 0x4b0#64) 64 ∗ memRegion (sp + 0x4f0#64) 896 := by
          rw [show (960 : Nat) = 64 + 896 from rfl, memRegion_split (sp + 0x4b0#64) 64 896 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
        have h870 : memRegion (sp + 0x870#64) 240 =
            memRegion (sp + 0x870#64) 64 ∗ memRegion (sp + 0x8b0#64) 176 := by
          rw [show (240 : Nat) = 64 + 176 from rfl, memRegion_split (sp + 0x870#64) 64 176 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
        rw [keyBytes960_unpack_sw hb1 hkb, h4b0, h870]
        dsimp only [cbcSoftWork, SwRest, TailCommon, sp, st1, numBlocks]
        refine Entails.of_eq ?_
        trans ((memRegion (sp + 0x038#64) 168 ∗ memRegion (sp + 0x0e0#64) 8) ∗
          (slots56 sp 0#64 w1 (BitVec.ofNat 64 (x.input.length / 16))
              (BitVec.ofNat 64 x.input.length) x.ret outBuf x.inA ∗
            memRegion (sp + 0x0e8#64) 968 ∗
            memRegion (sp + 0x4b0#64) 64 ∗ memRegion (sp + 0x4f0#64) 896 ∗
            memRegion (sp + 0x870#64) 64 ∗ memRegion (sp + 0x8b0#64) 176 ∗
            memRegion (sp + 0x960#64) 240 ∗ memRegion (sp + 0xa50#64) 240 ∗
            fsKeys256At (sp + 0xb40#64) (aes256KeyScheduleFs x.key) ∗
            ((sp + 0xf00#64) ↦ₛ x.iv) ∗ memRegion (sp + 0xf10#64) 16 ∗
            (outBuf ↦ₛ List.replicate x.input.length 0#8) ∗
            hSplit.base.live outBuf x.input.length 1 ∗
            (hw.storageAddr ↦₈ b) ∗ hSplit.base.pool lim st1 sm ∗
            ((x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2)) ∗
            (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗
            (hw.rconAddr ↦ᵣ aesRconBytes) ∗ savedStack96 s0 ∗ stackAt sp allocHookStack))
        · sep_ac_rfl
        · rw [h176]; sep_ac_rfl
      · refine cbc_tail_loop (hSplit := hSplit) (outBuf := outBuf) cs hCal x 0#64 x.ret SwRest s0 s_tail
          hmod16 hlt40 hkey32 hiv16 hspAl hpc_t hrun_t hsp_t hx22_t hx24_t hv_t
          fun s_unp hpc_u hrun_u hsp_u hx23_u hx26_u _ hv_u hpure_u => ?_
        refine SepWP.done hpc_u hrun_u ?_
        refine SepWPp.weaken_pre ?_
          (hAtUnpad (BitVec.ofNat 64 (numBlocks % 4)) s_unp hpc_u hrun_u hsp_u hx23_u hx26_u
            hv_u (hpure_t.trans hpure_u))
        have hprev_len : (cbcChainAt x.iv x.input numBlocks).length = 16 :=
          cbcChainAt_length hiv16 (by omega)
        rw [cbcPrefixBytes_full x.key x.iv x.input]
        dsimp only [cbcSoftWork, SwRest, rawBs, numBlocks]
        rw [work2824_split_sw sp]
        refine Entails.trans (Entails.of_eq (show _ =
            (fsKeys256At (sp + 0xb40#64) (aes256KeyScheduleFs x.key) ∗
              ((sp + 0xf00#64) ↦ₛ cbcChainAt x.iv x.input (x.input.length / 16))) ∗ _ by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left (decryptor976_pack_sw sp _ hprev_len))
          (Entails.of_eq (by sep_ac_rfl))

/-- Core conditional-OOM `subroutine_ok` verification of all `900` instructions of
    `signal_crypto::aes_cbc::aes_256_cbc_decrypt` under `withRoData hw.rconAddr aesRconBytes`,
    parameterized by `hHwLoop : HwLoopContract`. -/
theorem aes256CbcDecrypt_errRo_cond_of_hwLoop_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr : BitVec 64}
    {panics : Aes256CbcDecryptPanicSyms} {errStr1Relax errStr2Relax : Bool}
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesDecBudgetCondSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim)) :=
  (SpecSimulates.withRoData_of_sep (by decide : aesRconBytes.length ≤ 2 ^ 64)).subroutine_ok
    (aes256CbcDecrypt_errRo_cond_sep_of_hwLoop_ok A lim hHwLoop hCode hCal)

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.UnpadEpilog

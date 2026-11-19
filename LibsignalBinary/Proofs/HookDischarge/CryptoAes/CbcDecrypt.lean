/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Model
public import ProofLib.ProgramReflection
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.AesDecErrRoBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
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
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Top
import ProofLib.Hoare.SubroutineOk
import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopPar17
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopRem
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoops

/-!
# `signal_crypto::aes_cbc::aes_256_cbc_decrypt` Machine-Code Proof (`900` Instructions)

Public facade wiring `CbcDec.HwLoops.step_cbcDec_hwLoops` (`266`-instruction ARMv8 AES hardware
decryption loop slice) into `CbcDec.Top`, providing closed `0`-sorry `subroutine_ok` and `WordTree`
(`checkShimInstrsAt`) theorems over all `900` instructions of relinked `aes_256_cbc_decrypt`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDecrypt

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.ProgramReflection (WordTree hookAtOff?_eq_none_of_isNone)
open ProofLib.StdStartup (hasInstrs)
open VerifiedLibraries.RustStd (checkShimInstrsAt)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (aesCallPreBudget aesDecBudgetSpec aesDecFnBudgetSpec aesDecWeakBudgetSpec)
open LibsignalBinary.Heap.AesDecErrRoBudget (aesDecBudgetSpecErrRo)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (hasShimInstrs_of_wordTree checkBranchStub2
   subroutine_ok_of_branchStub subroutine_ok_of_branchStub_wordTree
   subroutine_ok_of_branchStub2 subroutine_ok_of_branchStub2_wordTree)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt withRoData)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules (sepWP_weaken_pre)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoops (step_cbcDec_hwLoops)

export LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (Aes256DecHwAddrs Aes256CbcDecryptPanicSyms Aes256CbcDecryptCallees HwLoopContract
   rustAllocZeroedBudgetSpecBase)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (aes256CbcDecryptInstrs aes256CbcDecryptInstrs_length
   cbcDecHwLoopInstrs cbcDecHwLoopInstrs_length hasInstrs_hwLoop_of_full)

export LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
  (aesDecEvents aesDecEnv_aesDecEvents fitsAllocEvents_of_fitsAesDecEvents)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
  (aesDecBudgetCondSpec aesDecNoOomSpec aesDecBudgetCondSpecErrRo aesDecNoOomSpecErrRo)

export LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Top
  (aes256CbcDecrypt_errRo_cond_sep_of_hwLoop_ok
   aes256CbcDecrypt_errRo_cond_of_hwLoop_ok
   aes256CbcDecrypt_errRo_noOom_of_hwLoop_ok
   aes256CbcDecrypt_errRo_keepsFs_of_hwLoop_ok
   aes256CbcDecrypt_errRo_budget_of_hwLoop_ok)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Top
  (aes256CbcDecrypt_cond_of_hwLoop_ok
   aes256CbcDecrypt_noOom_of_hwLoop_ok
   aes256CbcDecrypt_keepsFs_of_hwLoop_ok
   aes256CbcDecrypt_budget_of_hwLoop_ok
   aes256CbcDecrypt_weakBudget_of_hwLoop_ok)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Top
  (aes256CbcDecrypt_errRo_cond_of_hwLoop_wordTree_ok
   aes256CbcDecrypt_errRo_keepsFs_of_hwLoop_wordTree_ok
   aes256CbcDecrypt_errRo_budget_of_hwLoop_wordTree_ok
   aes256CbcDecrypt_keepsFs_of_hwLoop_wordTree_ok)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Top
  (aes256CbcDecrypt_budget_of_hwLoop_wordTree_ok
   aes256CbcDecrypt_weakBudget_of_hwLoop_wordTree_ok)

/-! ## 1. Discharge of `HwLoopContract` via `CbcDec.HwLoops.step_cbcDec_hwLoops` -/

private theorem hwLoopInstrs_eq
    (fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr : BitVec 64) :
    CbcDec.HwLoops.cbcDecHwLoopInstrs fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr =
      cbcDecHwLoopInstrs fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr := by
  have hdm : ∀ a b : List (BitVec 32),
      ProofLib.StdStartup.decodeWords (a ++ b) =
        ProofLib.StdStartup.decodeWords a ++ ProofLib.StdStartup.decodeWords b :=
    fun _ _ => List.map_append
  have h1 : CbcDec.HwLoops.hwSetupWords = CbcDec.CodeWords.hwSetupWords := rfl
  have h2 : CbcDec.HwLoopPar17.hwPar17InitWords = CbcDec.CodeWords.hwPar17InitWords := rfl
  have h3 : CbcDec.HwLoopPar17.hwPar17PreMc1Words = CbcDec.CodeWords.hwPar17PreMc1Words := rfl
  have h4 : CbcDec.HwLoopPar17.hwPar17PreMc2Words = CbcDec.CodeWords.hwPar17PreMc2Words := rfl
  have h5 : CbcDec.HwLoopPar17.hwPar17PreDecWords = CbcDec.CodeWords.hwPar17PreDecWords := rfl
  have h6 : CbcDec.HwLoopPar17.hwPar17Xor0Words =
      CbcDec.CodeWords.hwPar17Xor0AWords ++ CbcDec.CodeWords.hwPar17Xor0BWords := rfl
  have h7 : CbcDec.HwLoopPar17.hwPar17XorLoopHeadWords ++ CbcDec.HwLoopPar17.hwPar17XorLoopBodyWords =
      CbcDec.CodeWords.hwPar17XorLoopAWords ++ CbcDec.CodeWords.hwPar17XorLoopBWords := rfl
  have h8 : CbcDec.HwLoopPar17.hwPar17PostMcWords = CbcDec.CodeWords.hwPar17PostMcWords := rfl
  have h9 : CbcDec.HwLoopPar17.hwPar17TailWords = CbcDec.CodeWords.hwPar17TailWords := rfl
  have h10 : CbcDec.HwLoopRem.hwRemSetupWords = CbcDec.CodeWords.hwRemSetupWords := rfl
  have h11 : CbcDec.HwLoopRem.hwRemPreDecWords = CbcDec.CodeWords.hwRemPreDecWords := rfl
  have h12 : CbcDec.HwLoopRem.hwRemPostWords =
      CbcDec.CodeWords.hwRemPostAWords ++ CbcDec.CodeWords.hwRemPostBWords := rfl
  have h13 : CbcDec.HwLoopRem.hwRemExitWords = CbcDec.CodeWords.hwRemExitWords := rfl
  have h7' : ∀ tail : List Instr,
      ProofLib.StdStartup.decodeWords CbcDec.HwLoopPar17.hwPar17XorLoopHeadWords ++
        (ProofLib.StdStartup.decodeWords CbcDec.HwLoopPar17.hwPar17XorLoopBodyWords ++ tail) =
      ProofLib.StdStartup.decodeWords CbcDec.CodeWords.hwPar17XorLoopAWords ++
        (ProofLib.StdStartup.decodeWords CbcDec.CodeWords.hwPar17XorLoopBWords ++ tail) := by
    intro tail; rw [← List.append_assoc, ← hdm, h7, hdm, List.append_assoc]
  unfold CbcDec.HwLoops.cbcDecHwLoopInstrs cbcDecHwLoopInstrs
  rw [h1, h2, h3, h4, h5, h6, hdm, h8, h9, h10, h11, h12, hdm, h13]
  simp only [List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil, h7']

theorem cbcDec_hwLoop_ok {P : Program}
    {fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr : BitVec 64} :
    HwLoopContract P fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr := by
  intro hc hMemcpy hDecPar17 hDec1 target_pc sp outBuf x Rest s post oom
    hpos hmod hlt hkey hiv _ hpc hrun hsp hspAl hx9 hx24 hx25 hnext
  have hc' : hasInstrs P (fnAddr + 0x1d4#64)
      (CbcDec.HwLoops.cbcDecHwLoopInstrs fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr) := by
    rwa [hwLoopInstrs_eq]
  refine sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (step_cbcDec_hwLoops hc' hMemcpy hDecPar17 hDec1 hkey hiv hpos hmod hlt
      hpc hrun hsp hspAl hx9 hx24 hx25
      fun sf hpc_f hrun_f hsp_f _ hv_f hpure_f hx26_f hx23_f => ?_)
  exact sepWP_weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext sf hpc_f hrun_f hsp_f hx26_f hx23_f hv_f hpure_f)

/-! ## 2. Closed `hasInstrs` & `WordTree` (`900` Insns) Subroutine Theorems -/

section ClosedLadder

variable {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
  {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
  [hSplit : PoolAesInitSplit A hw.storageAddr]
  {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
   handleErrorAddr errStr1Addr errStr2Addr : BitVec 64}
  {panics : Aes256CbcDecryptPanicSyms} {errStr1Relax errStr2Relax : Bool}

theorem aes256CbcDecrypt_errRo_cond_ok
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesDecBudgetCondSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim)) :=
  aes256CbcDecrypt_errRo_cond_of_hwLoop_ok A lim cbcDec_hwLoop_ok hCode hCal

theorem aes256CbcDecrypt_errRo_noOom_ok
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesDecNoOomSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim)) :=
  aes256CbcDecrypt_errRo_noOom_of_hwLoop_ok A lim cbcDec_hwLoop_ok hCode hCal

theorem aes256CbcDecrypt_errRo_keepsFs_ok
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (keepsFs (aesDecBudgetSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim))) :=
  aes256CbcDecrypt_errRo_keepsFs_of_hwLoop_ok A lim cbcDec_hwLoop_ok hCode hCal

theorem aes256CbcDecrypt_errRo_budget_ok
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesDecBudgetSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim)) :=
  aes256CbcDecrypt_errRo_budget_of_hwLoop_ok A lim cbcDec_hwLoop_ok hCode hCal

theorem aes256CbcDecrypt_cond_ok
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesDecBudgetCondSpec Spec.Aes256.aes256Dec M A lim)) :=
  aes256CbcDecrypt_cond_of_hwLoop_ok A lim cbcDec_hwLoop_ok hCode hCal hErr1 hErr2

theorem aes256CbcDecrypt_noOom_ok
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesDecNoOomSpec Spec.Aes256.aes256Dec M A lim)) :=
  aes256CbcDecrypt_noOom_of_hwLoop_ok A lim cbcDec_hwLoop_ok hCode hCal hErr1 hErr2

theorem aes256CbcDecrypt_keepsFs_ok
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (keepsFs (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim))) :=
  aes256CbcDecrypt_keepsFs_of_hwLoop_ok A lim cbcDec_hwLoop_ok hCode hCal hErr1 hErr2

theorem aes256CbcDecrypt_budget_ok
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  aes256CbcDecrypt_budget_of_hwLoop_ok A lim cbcDec_hwLoop_ok hCode hCal hErr1 hErr2

theorem aes256CbcDecrypt_weakBudget_ok
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesDecWeakBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  aes256CbcDecrypt_weakBudget_of_hwLoop_ok A lim cbcDec_hwLoop_ok hCode hCal hErr1 hErr2

theorem aes256CbcDecrypt_errRo_cond_of_wordTree_ok {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 900 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax) = true)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesDecBudgetCondSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim)) :=
  aes256CbcDecrypt_errRo_cond_of_hwLoop_wordTree_ok A lim n cbcDec_hwLoop_ok hcode hwf hhook hok hCal

theorem aes256CbcDecrypt_errRo_keepsFs_of_wordTree_ok {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 900 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax) = true)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (keepsFs (aesDecBudgetSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim))) :=
  aes256CbcDecrypt_errRo_keepsFs_of_hwLoop_wordTree_ok A lim n cbcDec_hwLoop_ok hcode hwf hhook hok hCal

theorem aes256CbcDecrypt_errRo_budget_of_wordTree_ok {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 900 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax) = true)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesDecBudgetSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim)) :=
  aes256CbcDecrypt_errRo_budget_of_hwLoop_wordTree_ok A lim n cbcDec_hwLoop_ok hcode hwf hhook hok hCal

theorem aes256CbcDecrypt_cond_of_wordTree_ok {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 900 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax) = true)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesDecBudgetCondSpec Spec.Aes256.aes256Dec M A lim)) :=
  aes256CbcDecrypt_cond_ok A lim
    (hasShimInstrs_of_wordTree n hcode hwf
      (by simpa only [aes256CbcDecryptInstrs_length] using hhook) hok) hCal hErr1 hErr2

theorem aes256CbcDecrypt_keepsFs_of_wordTree_ok {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 900 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax) = true)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (keepsFs (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim))) :=
  aes256CbcDecrypt_keepsFs_of_hwLoop_wordTree_ok A lim n cbcDec_hwLoop_ok
    hcode hwf hhook hok hCal hErr1 hErr2

theorem aes256CbcDecrypt_budget_of_wordTree_ok {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 900 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax) = true)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  aes256CbcDecrypt_budget_of_hwLoop_wordTree_ok A lim n cbcDec_hwLoop_ok
    hcode hwf hhook hok hCal hErr1 hErr2

theorem aes256CbcDecrypt_weakBudget_of_wordTree_ok {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 900 → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax) = true)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesDecWeakBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  aes256CbcDecrypt_weakBudget_of_hwLoop_wordTree_ok A lim n cbcDec_hwLoop_ok
    hcode hwf hhook hok hCal hErr1 hErr2

end ClosedLadder

/-! ## 3. 1-Hop & 2-Hop `B`-Stub Alias Lifts Under `withRoData` -/

theorem aes256CbcDecrypt_budget_alias_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} (rconAddr aliasAddr fnAddr : BitVec 64)
    (hStub : hasInstrs P aliasAddr [ .b (fnAddr - aliasAddr) ])
    (hTarget : subroutine_ok P fnAddr
      (withRoData rconAddr aesRconBytes (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim))) :
    subroutine_ok P aliasAddr
      (withRoData rconAddr aesRconBytes (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  subroutine_ok_of_branchStub aliasAddr fnAddr hStub
    (by rintro ⟨_, _⟩ _ _; simp [withRoData, RoDataAt, aesDecBudgetSpec, aesCallPreBudget])
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl) hTarget

theorem aes256CbcDecrypt_budget_alias_wordTree_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {t : WordTree} (n : Nat)
    (rconAddr aliasAddr fnAddr : BitVec 64)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t aliasAddr [ .b (fnAddr - aliasAddr) ] = true)
    (hTarget : subroutine_ok P fnAddr
      (withRoData rconAddr aesRconBytes (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim))) :
    subroutine_ok P aliasAddr
      (withRoData rconAddr aesRconBytes (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  subroutine_ok_of_branchStub_wordTree n aliasAddr fnAddr hcode hwf hhook hok
    (by rintro ⟨_, _⟩ _ _; simp [withRoData, RoDataAt, aesDecBudgetSpec, aesCallPreBudget])
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl) hTarget

theorem aes256CbcDecrypt_budget_alias2_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} (rconAddr snapstubAddr aliasAddr fnAddr : BitVec 64)
    (hSnap : hasInstrs P snapstubAddr [ .b (aliasAddr - snapstubAddr) ])
    (hAlias : hasInstrs P aliasAddr [ .b (fnAddr - aliasAddr) ])
    (hTarget : subroutine_ok P fnAddr
      (withRoData rconAddr aesRconBytes (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim))) :
    subroutine_ok P snapstubAddr
      (withRoData rconAddr aesRconBytes (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  subroutine_ok_of_branchStub2 snapstubAddr aliasAddr fnAddr hSnap hAlias
    (by rintro ⟨_, _⟩ _ _; simp [withRoData, RoDataAt, aesDecBudgetSpec, aesCallPreBudget])
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl) hTarget

theorem aes256CbcDecrypt_budget_alias2_wordTree_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {t : WordTree} (n : Nat)
    (rconAddr snapstubAddr aliasAddr fnAddr : BitVec 64)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhookSnap : ∀ i, i < 1 → P.hookAtOff? ((snapstubAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hhookAlias : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkBranchStub2 P.base t snapstubAddr aliasAddr fnAddr = true)
    (hTarget : subroutine_ok P fnAddr
      (withRoData rconAddr aesRconBytes (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim))) :
    subroutine_ok P snapstubAddr
      (withRoData rconAddr aesRconBytes (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  subroutine_ok_of_branchStub2_wordTree n snapstubAddr aliasAddr fnAddr
    hcode hwf hhookSnap hhookAlias hok
    (by rintro ⟨_, _⟩ _ _; simp [withRoData, RoDataAt, aesDecBudgetSpec, aesCallPreBudget])
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl) hTarget

theorem aes256CbcDecrypt_weakBudget_alias_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} (rconAddr aliasAddr fnAddr : BitVec 64)
    (hStub : hasInstrs P aliasAddr [ .b (fnAddr - aliasAddr) ])
    (hTarget : subroutine_ok P fnAddr
      (withRoData rconAddr aesRconBytes (aesDecWeakBudgetSpec Spec.Aes256.aes256Dec M A lim))) :
    subroutine_ok P aliasAddr
      (withRoData rconAddr aesRconBytes (aesDecWeakBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  subroutine_ok_of_branchStub aliasAddr fnAddr hStub
    (by rintro ⟨_, _⟩ _ _; simp [withRoData, RoDataAt, aesDecWeakBudgetSpec, aesDecFnBudgetSpec, aesCallPreBudget])
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl) hTarget

theorem aes256CbcDecrypt_weakBudget_alias_wordTree_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {t : WordTree} (n : Nat)
    (rconAddr aliasAddr fnAddr : BitVec 64)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t aliasAddr [ .b (fnAddr - aliasAddr) ] = true)
    (hTarget : subroutine_ok P fnAddr
      (withRoData rconAddr aesRconBytes (aesDecWeakBudgetSpec Spec.Aes256.aes256Dec M A lim))) :
    subroutine_ok P aliasAddr
      (withRoData rconAddr aesRconBytes (aesDecWeakBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  subroutine_ok_of_branchStub_wordTree n aliasAddr fnAddr hcode hwf hhook hok
    (by rintro ⟨_, _⟩ _ _; simp [withRoData, RoDataAt, aesDecWeakBudgetSpec, aesDecFnBudgetSpec, aesCallPreBudget])
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl) hTarget

theorem aes256CbcDecrypt_weakBudget_alias2_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} (rconAddr snapstubAddr aliasAddr fnAddr : BitVec 64)
    (hSnap : hasInstrs P snapstubAddr [ .b (aliasAddr - snapstubAddr) ])
    (hAlias : hasInstrs P aliasAddr [ .b (fnAddr - aliasAddr) ])
    (hTarget : subroutine_ok P fnAddr
      (withRoData rconAddr aesRconBytes (aesDecWeakBudgetSpec Spec.Aes256.aes256Dec M A lim))) :
    subroutine_ok P snapstubAddr
      (withRoData rconAddr aesRconBytes (aesDecWeakBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  subroutine_ok_of_branchStub2 snapstubAddr aliasAddr fnAddr hSnap hAlias
    (by rintro ⟨_, _⟩ _ _; simp [withRoData, RoDataAt, aesDecWeakBudgetSpec, aesDecFnBudgetSpec, aesCallPreBudget])
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl) hTarget

theorem aes256CbcDecrypt_weakBudget_alias2_wordTree_ok {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program} {t : WordTree} (n : Nat)
    (rconAddr snapstubAddr aliasAddr fnAddr : BitVec 64)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhookSnap : ∀ i, i < 1 → P.hookAtOff? ((snapstubAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hhookAlias : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkBranchStub2 P.base t snapstubAddr aliasAddr fnAddr = true)
    (hTarget : subroutine_ok P fnAddr
      (withRoData rconAddr aesRconBytes (aesDecWeakBudgetSpec Spec.Aes256.aes256Dec M A lim))) :
    subroutine_ok P snapstubAddr
      (withRoData rconAddr aesRconBytes (aesDecWeakBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  subroutine_ok_of_branchStub2_wordTree n snapstubAddr aliasAddr fnAddr
    hcode hwf hhookSnap hhookAlias hok
    (by rintro ⟨_, _⟩ _ _; simp [withRoData, RoDataAt, aesDecWeakBudgetSpec, aesDecFnBudgetSpec, aesCallPreBudget])
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl)
    (by rintro ⟨_, _⟩ _ _ _; rfl) (by rintro ⟨_, _⟩ _ _ _; rfl) hTarget

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDecrypt

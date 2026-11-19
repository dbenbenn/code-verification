/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.AesDecErrRoBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Concrete `seg[2]` Subroutine Witness for `cliAesDecBudgetSpecErrRo` (`HooksDehook.AesDecErrRoSubroutine`)

Proves `c2_aesDec_errRo_subroutineOk` on `aesCbcSubProg` at `c2AesDecAddr` by reusing the
hardware + `Fixslice64` callee bundle `c2_aesDecCallees_aesCbcSubProg` and `900`-instruction
`WordTree` certificate `c2_aes256CbcDecrypt_chk` from `C2RowLayoutFacts.AesCbc`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesDecErrRoSubroutine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries (mallocngLib)
open CryptoGames.AES256 (aes256Dec)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (cliElfBytes)
open LibsignalBinary.Heap (BudgetLimits zeroBudgetLimits)
open LibsignalBinary.Heap.AesDecErrRoBudget
  (aesDecBudgetSpecErrRo cliAesDecBudgetSpecErrRo cliAesDecErrStr1Addr cliAesDecErrStr2Addr)
open LibsignalBinary.Heap.Fine
  (f3RxWordCount f3StdLayout fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (withRoData)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDecrypt
  (aes256CbcDecrypt_errRo_keepsFs_of_wordTree_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays
  (c2AesRconAddr withAesStubRconRO withFsTraceExact withStubPermRO)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (aesCbcSubProg aesCbcSubProg_base aesCbcSubProg_code aesCbcSubProg_hookAtOff_none
   c2AesDecAddr c2_aes256CbcDecrypt_chk c2_aesDecCallees_aesCbcSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.PrePanicMngLift
  (fineHookPool_nonZeroEquivLim fitsEnv_nonZeroEquivLim nonZeroEquivLim nonZeroEquivLim_ne_zero
   withExecFrozenBudget withExecFrozenBudget_pool_entails)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxWordTree_size)

theorem c2_aesDec_errRo_subroutineOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (hbrk : brkStart = f3StdLayout.brkStart)
    (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok aesCbcSubProg c2AesDecAddr
      (withAesStubRconRO aesCbcSubProg
        (withFsTraceExact
          (withLsRet (cliAesDecBudgetSpecErrRo aes256Dec fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)))) := by
  subst hbrk
  let lim' := nonZeroEquivLim lim
  have hlim' : lim' ≠ zeroBudgetLimits := nonZeroEquivLim_ne_zero lim
  let A0 := fineHookRustCliAllocBudget γ mmpl tp f3StdLayout.brkStart
  let A' := withExecFrozenBudget A0
  have hCal := c2_aesDecCallees_aesCbcSubProg mmpl hMm γ tp hlim'
  have hRaw := aes256CbcDecrypt_errRo_keepsFs_of_wordTree_ok (fnAddr := c2AesDecAddr)
    A' lim' f3RxWordCount aesCbcSubProg_code f3TrialRxWordTree_size
    (fun i hi => by
      rw [aesCbcSubProg_base]
      have hlo : 0x47ac2c - 0x474000 ≤ (c2AesDecAddr - f3RxSegBase).toNat := by decide
      have hfit : (c2AesDecAddr - f3RxSegBase).toNat + 4 * 900 ≤ 0x4cb070 - 0x474000 := by decide
      exact aesCbcSubProg_hookAtOff_none (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    c2_aes256CbcDecrypt_chk
    hCal
  apply subroutine_ok.of_codeLoaded
  intro (x, st0) R s0 hpc hrun hpre hsp _
  dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withFsTraceExact, withLsRet,
    cliAesDecBudgetSpecErrRo] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hfr⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hrcon, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hpre⟩
  have hpre' : s0.mem ⊨
      (withRoData c2AesRconAddr aesRconBytes
        (keepsFs (aesDecBudgetSpecErrRo aes256Dec cliAesDecErrStr1Addr cliAesDecErrStr2Addr
          fineCostModel A' lim'))).pre (x, st0) s0 ∗ R := by
    dsimp only [withRoData]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hrcon, ?_⟩
    dsimp only [keepsFs, aesDecBudgetSpecErrRo, LibsignalBinary.Heap.SpecBudget.aesCallPreBudget,
      A', A0, withExecFrozenBudget, lim'] at hpre ⊢
    rw [fitsEnv_nonZeroEquivLim, fineHookPool_nonZeroEquivLim]
    refine Satisfies.mono ?_ hpre
    exact Entails.trans
      (Entails.pure_right (fun (_ : lim' ≠ zeroBudgetLimits) => hfr) (Entails.refl _))
      (Entails.of_eq (by sep_ac_rfl))
  refine subroutine_ok.mono_outcome hRaw (x, st0) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoData, keepsFs, aesDecBudgetSpecErrRo, A', A0, lim'] at hpost
    dsimp only [withAesStubRconRO, withStubPermRO, withRoData, withFsTraceExact, withLsRet,
      cliAesDecBudgetSpecErrRo, aesDecBudgetSpecErrRo]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hfs, hpost⟩
    rw [sepExists_sepConj_left] at hpost
    obtain ⟨evs, hpost⟩ := (satisfies_sepExists _ _).mp hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htr, hev⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfs, htr⟩, ?_⟩
    rw [sepExists_sepConj_left]
    refine (satisfies_sepExists _ _).mpr ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hev⟩, ?_⟩
    exact Satisfies.mono
      (sepConj_mono_left
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono_left
              (withExecFrozenBudget_pool_entails γ mmpl tp f3StdLayout.brkStart lim _ sf)))))
      hpost
  · dsimp only [withRoData, keepsFs, aesDecBudgetSpecErrRo] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesDecErrRoSubroutine

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
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.UnpadEpilog
import ProofLib.Hoare.SubroutineOk
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Top-Level Spec & `WordTree` Ladder Parameterized by `HwLoopContract` (`CbcDec.Top`)

Lowers `aes256CbcDecrypt_errRo_cond_of_hwLoop_ok` across `NoOom`, `keepsFs`, `Budget`, and
`WeakBudget` specs under `withRoData hw.rconAddr aesRconBytes`, and provides `900`-instruction
`WordTree` (`checkShimInstrsAt`) entrypoints.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Top

open Arm64 ProofLib SepProp ProofLib.SepLogic
open ProofLib.ProgramReflection (WordTree hookAtOff?_eq_none_of_isNone)
open ProofLib.StdStartup (hasInstrs)
open VerifiedLibraries.RustStd (checkShimInstrsAt)
open CryptoGames.CBC (AesKey Block bytesToBlock)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcDecrypt)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk
   not_nullAllowed_of_fitsAllocEvents)
open LibsignalBinary.Heap.SpecBudget
  (aesCallPreBudget aesDecBudgetSpec aesDecFnBudgetSpec aesDecWeakBudgetSpec)
open LibsignalBinary.Heap.AesDecErrRoBudget (aesDecBudgetSpecErrRo aesErrRo_entails_aesErr)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (hasShimInstrs_of_wordTree)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (withRoData SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (Aes256DecHwAddrs Aes256CbcDecryptPanicSyms Aes256CbcDecryptCallees HwLoopContract
   aes256CbcDecryptInstrs aes256CbcDecryptInstrs_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
  (aesDecEvents aesDecEnv_aesDecEvents fitsAllocEvents_of_fitsAesDecEvents
   aesDecBudgetCondSpec aesDecNoOomSpec aesDecBudgetCondSpecErrRo aesDecNoOomSpecErrRo)

export LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.UnpadEpilog
  (aes256CbcDecrypt_errRo_cond_sep_of_hwLoop_ok aes256CbcDecrypt_errRo_cond_of_hwLoop_ok)

/-! ## 1. `SpecSimulates` Transport Combinators Under `withRoData` -/

theorem map_withRoData {α β : Type} {addr : BitVec 64} {bytes : List (BitVec 8)}
    {spec₁ : Spec α} {spec₂ : Spec β} (hsim : SpecSimulates spec₁ spec₂) :
    SpecSimulates (withRoData addr bytes spec₁) (withRoData addr bytes spec₂) := by
  intro y R s0 hpre
  dsimp only [withRoData] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro, hpre₂⟩ := hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre₂
  refine ⟨x, R₁, ?_, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hro, hpre₁⟩

theorem sim_aesDecCond_of_errRoCond {D : AesKey → Block → Block}
    {errStr1Addr errStr2Addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    SpecSimulates (aesDecBudgetCondSpecErrRo D errStr1Addr errStr2Addr M A lim)
      (aesDecBudgetCondSpec D M A lim) := by
  intro ⟨x, st⟩ R s0 hpre
  refine ⟨(x, st), R, hpre, ?_⟩
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hext | hoom)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [aesDecBudgetCondSpecErrRo, aesDecBudgetCondSpec] at hpost ⊢
    cases hdec : aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
    | some pt => simpa only [hdec] using hpost
    | none =>
      rw [hdec] at hpost; dsimp only at hpost ⊢
      exact Satisfies.mono
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (aesErrRo_entails_aesErr x.ret hErr1 hErr2))))) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hext))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem sim_aesDecErrRoNoOom_of_cond {D : AesKey → Block → Block}
    {errStr1Addr errStr2Addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} :
    SpecSimulates (aesDecBudgetCondSpecErrRo D errStr1Addr errStr2Addr M A lim)
      (aesDecNoOomSpecErrRo D errStr1Addr errStr2Addr M A lim) := by
  intro ⟨x, st⟩ R s0 hpre
  dsimp only [aesDecNoOomSpecErrRo, aesDecNoOomSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hlt40, hfits⟩, hrest⟩
  refine ⟨(x, st), R, ?_, ?_⟩
  · dsimp only [aesDecBudgetCondSpecErrRo, aesDecBudgetCondSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hlt40⟩, hrest⟩
  · rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hmp⟩ | ⟨c, hc, hex⟩ | ⟨_, hmo⟩)
    · exact Or.inl ⟨hret, hcc, hpost⟩
    · exfalso
      dsimp only [aesDecBudgetCondSpecErrRo, aesDecBudgetCondSpec] at hmp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hmp
      rcases hmp with ⟨⟨hnb, hna, _, _⟩, _⟩
      have hLay : RustLayoutOk x.input.length 1 := ⟨⟨by omega, ⟨0, rfl⟩, by omega⟩, by decide⟩
      exact not_nullAllowed_of_fitsAllocEvents hLay
        (fitsAllocEvents_of_fitsAesDecEvents hnb hfits) hna
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
    · exfalso
      dsimp only [aesDecBudgetCondSpecErrRo, aesDecBudgetCondSpec] at hmo
      rw [satisfies_pure_sepConj] at hmo; exact hmo.1.1 hfits

theorem sim_aesDecErrRoKeepsFs_of_noOom {D : AesKey → Block → Block}
    {errStr1Addr errStr2Addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} :
    SpecSimulates (aesDecNoOomSpecErrRo D errStr1Addr errStr2Addr M A lim)
      (keepsFs (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim)) := by
  intro ⟨x, st⟩ R s0 hpre
  dsimp only [keepsFs, aesDecBudgetSpecErrRo, aesCallPreBudget] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hlt40, hEnv⟩, hrest⟩
  refine ⟨(x, st), R, ?_, ?_⟩
  · dsimp only [aesDecNoOomSpecErrRo, aesDecNoOomSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hlt40,
      hEnv _ (aesDecEnv_aesDecEvents D x)⟩, hrest⟩
  · rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hmp⟩ | ⟨_, _, hex⟩ | ⟨_, hmo⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [aesDecNoOomSpecErrRo, aesDecBudgetCondSpecErrRo] at hpost
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hpres, hrest'⟩
      dsimp only [keepsFs, aesDecBudgetSpecErrRo]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hpres.1, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨aesDecEvents D x, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpres.2.1, aesDecEnv_aesDecEvents D x⟩,
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest'⟩
    · dsimp only [aesDecNoOomSpecErrRo] at hmp; rw [satisfies_pure_sepConj] at hmp; exact False.elim hmp.1
    · dsimp only [aesDecNoOomSpecErrRo] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
    · dsimp only [aesDecNoOomSpecErrRo] at hmo; rw [satisfies_pure_sepConj] at hmo; exact False.elim hmo.1

theorem sim_aesDecNoOom_of_cond {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} :
    SpecSimulates (aesDecBudgetCondSpec D M A lim) (aesDecNoOomSpec D M A lim) := by
  intro ⟨x, st⟩ R s0 hpre
  dsimp only [aesDecNoOomSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hlt40, hfits⟩, hrest⟩
  refine ⟨(x, st), R, ?_, ?_⟩
  · dsimp only [aesDecBudgetCondSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hlt40⟩, hrest⟩
  · rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hmp⟩ | ⟨c, hc, hex⟩ | ⟨_, hmo⟩)
    · exact Or.inl ⟨hret, hcc, hpost⟩
    · exfalso
      dsimp only [aesDecBudgetCondSpec] at hmp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hmp
      rcases hmp with ⟨⟨hnb, hna, _, _⟩, _⟩
      have hLay : RustLayoutOk x.input.length 1 := ⟨⟨by omega, ⟨0, rfl⟩, by omega⟩, by decide⟩
      exact not_nullAllowed_of_fitsAllocEvents hLay
        (fitsAllocEvents_of_fitsAesDecEvents hnb hfits) hna
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
    · exfalso
      dsimp only [aesDecBudgetCondSpec] at hmo
      rw [satisfies_pure_sepConj] at hmo; exact hmo.1.1 hfits

theorem sim_aesDecKeepsFs_of_noOom {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} :
    SpecSimulates (aesDecNoOomSpec D M A lim) (keepsFs (aesDecBudgetSpec D M A lim)) := by
  intro ⟨x, st⟩ R s0 hpre
  dsimp only [keepsFs, aesDecBudgetSpec, aesCallPreBudget] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hlt40, hEnv⟩, hrest⟩
  refine ⟨(x, st), R, ?_, ?_⟩
  · dsimp only [aesDecNoOomSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hlt40,
      hEnv _ (aesDecEnv_aesDecEvents D x)⟩, hrest⟩
  · rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hmp⟩ | ⟨_, _, hex⟩ | ⟨_, hmo⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [aesDecNoOomSpec, aesDecBudgetCondSpec] at hpost
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hpres, hrest'⟩
      dsimp only [keepsFs, aesDecBudgetSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hpres.1, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨aesDecEvents D x, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpres.2.1, aesDecEnv_aesDecEvents D x⟩,
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest'⟩
    · dsimp only [aesDecNoOomSpec] at hmp; rw [satisfies_pure_sepConj] at hmp; exact False.elim hmp.1
    · dsimp only [aesDecNoOomSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
    · dsimp only [aesDecNoOomSpec] at hmo; rw [satisfies_pure_sepConj] at hmo; exact False.elim hmo.1

private theorem aesErr_entails_weak (ret : BitVec 64) :
    (ret ↦₆₄ errTag) ∗
      (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((ret + 8#64) ↦₆₄ p)) ∗ memRegion (ret + 16#64) 8 ⊢
      (ret ↦₆₄ errTag) ∗ memRegion (ret + 8#64) 16 := by
  have hp8 : (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((ret + 8#64) ↦₆₄ p)) ⊢ memRegion (ret + 8#64) 8 := by
    rw [memRegion_eight (ret + 8#64)]
    refine Entails.sepExists_elim fun p => Entails.pure_left fun _ => ?_
    exact @Entails.sepExists_intro (BitVec 64) (fun q => (ret + 8#64) ↦₆₄ q) p
  have h16 : memRegion (ret + 8#64) 8 ∗ memRegion (ret + 16#64) 8 = memRegion (ret + 8#64) 16 :=
    (memRegion_split' (b := ret + 8#64) (n := 8) (k := 8) (b' := ret + 16#64)
      rfl (by bv_omega) (by decide)).symm
  rw [← h16]; exact sepConj_mono_right (sepConj_mono_left hp8)

theorem sim_aesDecWeak_of_budget {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} :
    SpecSimulates (aesDecBudgetSpec D M A lim) (aesDecWeakBudgetSpec D M A lim) := by
  intro ⟨x, st⟩ R s0 hpre
  refine ⟨(x, st), R, hpre, ?_⟩
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hext | hoom)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [aesDecBudgetSpec, aesDecWeakBudgetSpec, aesDecFnBudgetSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hevs⟩
    refine ⟨evs, ?_⟩
    cases hdec : aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
    | some pt => simpa only [hdec] using hevs
    | none =>
      rw [hdec] at hevs; dsimp only at hevs ⊢
      exact Satisfies.mono
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (aesErr_entails_weak x.ret))))) hevs
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hext))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-! ## 2. `hasInstrs` & `WordTree` (`900` Insns) Ladder Parameterized by `HwLoopContract` -/

section ParameterizedLadder

variable {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
  {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
  [hSplit : PoolAesInitSplit A hw.storageAddr]
  {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
   handleErrorAddr errStr1Addr errStr2Addr : BitVec 64}
  {panics : Aes256CbcDecryptPanicSyms} {errStr1Relax errStr2Relax : Bool}

theorem aes256CbcDecrypt_errRo_noOom_of_hwLoop_ok
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesDecNoOomSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim)) :=
  (map_withRoData sim_aesDecErrRoNoOom_of_cond).subroutine_ok
    (aes256CbcDecrypt_errRo_cond_of_hwLoop_ok A lim hHwLoop hCode hCal)

theorem aes256CbcDecrypt_errRo_keepsFs_of_hwLoop_ok
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (keepsFs (aesDecBudgetSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim))) :=
  (map_withRoData sim_aesDecErrRoKeepsFs_of_noOom).subroutine_ok
    (aes256CbcDecrypt_errRo_noOom_of_hwLoop_ok A lim hHwLoop hCode hCal)

theorem aes256CbcDecrypt_errRo_budget_of_hwLoop_ok
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes
        (aesDecBudgetSpecErrRo Spec.Aes256.aes256Dec errStr1Addr errStr2Addr M A lim)) :=
  (map_withRoData SpecSimulates.drop_keepsFs).subroutine_ok
    (aes256CbcDecrypt_errRo_keepsFs_of_hwLoop_ok A lim hHwLoop hCode hCal)

theorem aes256CbcDecrypt_cond_of_hwLoop_ok
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesDecBudgetCondSpec Spec.Aes256.aes256Dec M A lim)) :=
  (map_withRoData (sim_aesDecCond_of_errRoCond hErr1 hErr2)).subroutine_ok
    (aes256CbcDecrypt_errRo_cond_of_hwLoop_ok A lim hHwLoop hCode hCal)

theorem aes256CbcDecrypt_noOom_of_hwLoop_ok
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesDecNoOomSpec Spec.Aes256.aes256Dec M A lim)) :=
  (map_withRoData sim_aesDecNoOom_of_cond).subroutine_ok
    (aes256CbcDecrypt_cond_of_hwLoop_ok A lim hHwLoop hCode hCal hErr1 hErr2)

theorem aes256CbcDecrypt_keepsFs_of_hwLoop_ok
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
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
  (map_withRoData sim_aesDecKeepsFs_of_noOom).subroutine_ok
    (aes256CbcDecrypt_noOom_of_hwLoop_ok A lim hHwLoop hCode hCal hErr1 hErr2)

theorem aes256CbcDecrypt_budget_of_hwLoop_ok
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesDecBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  (map_withRoData SpecSimulates.drop_keepsFs).subroutine_ok
    (aes256CbcDecrypt_keepsFs_of_hwLoop_ok A lim hHwLoop hCode hCal hErr1 hErr2)

theorem aes256CbcDecrypt_weakBudget_of_hwLoop_ok
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
    (hCode : hasInstrs P fnAddr
      (aes256CbcDecryptInstrs fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
        deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr panics
        errStr1Relax errStr2Relax))
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (hErr1 : errStr1Addr ≠ 0#64) (hErr2 : errStr2Addr ≠ 0#64) :
    subroutine_ok P fnAddr
      (withRoData hw.rconAddr aesRconBytes (aesDecWeakBudgetSpec Spec.Aes256.aes256Dec M A lim)) :=
  (map_withRoData sim_aesDecWeak_of_budget).subroutine_ok
    (aes256CbcDecrypt_budget_of_hwLoop_ok A lim hHwLoop hCode hCal hErr1 hErr2)

theorem aes256CbcDecrypt_errRo_cond_of_hwLoop_wordTree_ok {t : WordTree} (n : Nat)
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
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
  aes256CbcDecrypt_errRo_cond_of_hwLoop_ok A lim hHwLoop
    (hasShimInstrs_of_wordTree n hcode hwf
      (by simpa only [aes256CbcDecryptInstrs_length] using hhook) hok) hCal

theorem aes256CbcDecrypt_errRo_keepsFs_of_hwLoop_wordTree_ok {t : WordTree} (n : Nat)
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
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
  aes256CbcDecrypt_errRo_keepsFs_of_hwLoop_ok A lim hHwLoop
    (hasShimInstrs_of_wordTree n hcode hwf
      (by simpa only [aes256CbcDecryptInstrs_length] using hhook) hok) hCal

theorem aes256CbcDecrypt_errRo_budget_of_hwLoop_wordTree_ok {t : WordTree} (n : Nat)
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
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
  aes256CbcDecrypt_errRo_budget_of_hwLoop_ok A lim hHwLoop
    (hasShimInstrs_of_wordTree n hcode hwf
      (by simpa only [aes256CbcDecryptInstrs_length] using hhook) hok) hCal

theorem aes256CbcDecrypt_keepsFs_of_hwLoop_wordTree_ok {t : WordTree} (n : Nat)
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
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
  aes256CbcDecrypt_keepsFs_of_hwLoop_ok A lim hHwLoop
    (hasShimInstrs_of_wordTree n hcode hwf
      (by simpa only [aes256CbcDecryptInstrs_length] using hhook) hok) hCal hErr1 hErr2

theorem aes256CbcDecrypt_budget_of_hwLoop_wordTree_ok {t : WordTree} (n : Nat)
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
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
  aes256CbcDecrypt_budget_of_hwLoop_ok A lim hHwLoop
    (hasShimInstrs_of_wordTree n hcode hwf
      (by simpa only [aes256CbcDecryptInstrs_length] using hhook) hok) hCal hErr1 hErr2

theorem aes256CbcDecrypt_weakBudget_of_hwLoop_wordTree_ok {t : WordTree} (n : Nat)
    (hHwLoop : HwLoopContract P fnAddr memcpyAddr hw.hwDecryptPar17Addr hw.hwDecryptAddr)
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
  aes256CbcDecrypt_weakBudget_of_hwLoop_ok A lim hHwLoop
    (hasShimInstrs_of_wordTree n hcode hwf
      (by simpa only [aes256CbcDecryptInstrs_length] using hhook) hok) hCal hErr1 hErr2

end ParameterizedLadder

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Top

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget -- proof-setup: allow-public-import
meta import Lean.Elab.Command -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
meta import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `HookSat`-Compatible (`1152`-B `extract` / `816`-B `expand_multi_info`) Contracts for `Keys`

Lifts `extractSpecSat` / `extractBudgetSpecSat` (`1152` B) and `expandMultiInfoSpecSat` /
`expandMultiInfoBudgetSpecSat` (`816` B) into the `4096`-B (`allocHookStack`) and `16384`-B
(`extHookStack`) call-site specs of `CreateChain`, `CreateChainBudget`, `GenerateKeys`, and
`GenerateKeysBudget`, preserving `createChainStack` and `generateKeysStack` unchanged.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Keys.KeysSat

public section

open Arm64 Arm64.Obj ProofLib
open CryptoGames.HKDF (hkdfExpand hkdfExtract whisperMessageKeys)
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPC_207 blkPC_40 blkPC_69 blkPl_207 blkPl_40 blkPl_69
   lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc allocHookStack rustAllocSpec rustDeallocSpec vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet
  (ExpandMultiInfoGhost ExtractGhost calculateAgreementExtStack calculateAgreementSpec
   calculateAgreementSpecX calculateAgreementStack createChainSpec createChainSpecX ctEqSliceROSpec
   diffieHellmanSpec extHookStack generateKeysSpec generateKeysSpecX hmacCoreAt
   keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro
   messageKeysAt mkgAt noAllocShimSpec optSaltAt rustDeallocExternSpecWithStack spqrRecvKeyAt
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded withStack zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (LsFrozenInv SepWP.done_frozen SepWP.of_sepWP_lscro bv_add_neg64 bv_sub_sub_lit
   calculateAgreementPlacedCallX_ok calculateAgreementPlacedCall_ok
   calculateAgreement_placed_ok createChain_placed_ok_of_hooks_gen
   deallocAllocStackSpec deallocAllocStack_of_rustDealloc_placed
   deallocPlacedExtStackSpec deallocPlacedExtStack_of_rustDeallocExtern
   deallocPlacedStackSpecAt deriveMessageKeys_eq
   exists_unpack64_of_length_80 expandCellsPlacedAllocStackSpec expandCellsPlacedExtStackSpec
   expandCellsPlacedStackSpecAt extractEmptyPlacedAllocStackSpec extractKey32PlacedAllocStackSpec
   extractKey32PlacedStackSpecAt extractNonePlacedAllocStackSpec extractSomePlacedAllocStackSpec
   fnFrame_split_generateKeys_post fnFrame_split_generateKeys_pre hkdfExtract_length'
   hmacCore_entails_cells hmacCore_split lsDhSym lsHandleAllocErrorSym lsRustAllocSym
   lsRustDeallocSym lsRustNoAllocShimSym lsSharedDropSym lsStaticDropSym lt_32_18
   memRegion_out_generateKeys messageKeysAt_generateKeys pointsToBytes_memRegion_merge_32
   pointsTo_keyVec_toList slt_one_eq_false_of_small stackAt_calc_alloc_split stackAt_calc_ext
   stackAt_ext_alloc subroutine_ok_createChainSpecX_of_createChainSpec
   subroutine_ok_generateKeysSpecX_of_generateKeysSpec subroutine_ok_withLsCodeRoLoaded_rodata''
   vecU8At_split_32 vecU8At_split_nil whisperMessageKeys_length withLsRet624)
open CryptoVerification.LibsignalTripleRatchet.Keys.GenerateKeysFacts
  (bv_sub_add_lit' cells_sub208_14_merge cells_sub240_4_merge cells_sub272_4_merge
   cells_sub416_8_merge cells_sub496_10_merge cells_sub96_12_merge hmacCore_merge_sub416
   memRegion_24_merge memRegion_gen_merge readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre)
open scoped CryptoVerification CryptoVerification.LibsignalTripleRatchet.Keys
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved rustCliAllocBudgetSpec
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliDeallocBudgetExternSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
  (expandMultiInfoBudgetSpecSat extractBudgetSpecSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (expandMultiInfoSpecSat expandMultiInfoStackSat extractSpecSat extractStackSat)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
  (calculateAgreementBudgetCallAt_ok deallocBudgetPlacedAllocStack_of_rustCliDealloc
   deallocBudgetPlacedExtStack_of_rustCliDeallocExtern deallocBudgetPlacedStackSpecAt
   expandCellsBudgetPlacedStackSpecAt extractKey32BudgetPlacedStackSpecAt
   extractSomeBudgetPlacedAllocStackSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget
  (deallocGenBudgetPlacedAllocStack_of_rustCliDealloc
   deallocGenBudgetPlacedExtStack_of_rustCliDeallocExtern extractEmptyBudgetPlacedStackSpecAt
   extractNoneBudgetPlacedStackSpecAt extractSomeBudgetPlacedStackSpecAt
   generateKeys_placed_ok_of_hooks_gen)

attribute [local simp, local arm64_norm] whisperMessageKeys_length lt_32_18 hkdfExtract_length'
attribute [local arm64_norm] bv_sub_sub_lit bv_sub_add_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local irreducible] Program.fetch Program.externAt?

local elab "erase_leaked_esp_arm64_norm" : command =>
  Lean.Elab.Command.liftCoreM do
    Lean.Attribute.erase ``CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp `arm64_norm
    Lean.Attribute.erase ``CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp `arm64_norm
    Lean.Attribute.erase ``CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496 `arm64_norm

erase_leaked_esp_arm64_norm

/-! ## Stack-Frame Split Helpers (`4096 = 2944 + 1152` and `4096 = 3280 + 816`) -/

private theorem stackAt_alloc_extract_sat (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 4096#64) 2944 ∗ stackAt sp extractStackSat := by
  simp only [stackAt, allocHookStack, extractStackSat]
  exact ProofLib.memRegion_split' rfl (by bv_omega) (by decide)

private theorem stackAt_alloc_expand_sat (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 4096#64) 3280 ∗ stackAt sp expandMultiInfoStackSat := by
  simp only [stackAt, allocHookStack, expandMultiInfoStackSat]
  exact ProofLib.memRegion_split' rfl (by bv_omega) (by decide)

/-! ## 1. Budget `CreateChainBudget` Siblings -/

theorem extractSomeBudgetPlacedAllocStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpecSat C.F))) :
    subroutine_ok prog addr (extractSomeBudgetPlacedAllocStackSpec C.F pl) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, saltA, sv, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractSomeBudgetPlacedAllocStackSpec] at hpre
  rw [stackAt_alloc_extract_sat sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hx4, hsp, hsalt_ne, hikm⟩, hpre⟩
  refine ⟨⟨ret, saltA, some sv, ikmA, ikm⟩, memRegion (sp - 4096#64) 2944 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, extractBudgetSpecSat, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [extractSpecSat, optSaltAt]
    subst hsp
    rw [eq_true hsalt_ne, pure_true, emp_sepConj]
    simp only [Option.isSome_some, reduceCtorEq, IsEmpty.forall_iff, forall_const, true_and,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hikm⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, extractBudgetSpecSat, withVmPreserved, extractSpecSat,
      ExtractGhost.prk, optSaltAt, extractSomeBudgetPlacedAllocStackSpec] at hpost ⊢
    rw [stackAt_alloc_extract_sat sp]
    subst hsp
    rw [eq_true hsalt_ne, pure_true, emp_sepConj] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    exact ⟨⟨htr, hvm⟩, by arm64_sep_close⟩

theorem extractKey32BudgetPlacedAllocStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpecSat C.F))) :
    subroutine_ok prog addr (extractKey32BudgetPlacedStackSpecAt C.F pl allocHookStack) := by
  refine subroutine_ok_map (extractSomeBudgetPlacedAllocStack_ok_sat (C := C) hext) ?_
  rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
  refine ⟨⟨ret, saltA, keyToBytesVec32 rk, ikmA, ikm, sp⟩, R, ?_, ?_⟩
  · dsimp only [extractSomeBudgetPlacedAllocStackSpec, extractKey32BudgetPlacedStackSpecAt] at hpre ⊢
    rw [pointsTo_keyVec_toList]
    exact hpre
  · intro sf hpost
    dsimp only [extractSomeBudgetPlacedAllocStackSpec, extractKey32BudgetPlacedStackSpecAt] at hpost ⊢
    rw [← pointsTo_keyVec_toList]
    exact hpost

theorem expandCellsBudgetPlacedAllocStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hexp : subroutine_ok prog addr (withLsCodeRoLoaded pl (expandMultiInfoBudgetSpecSat C.F)))
    (n : Nat) (hn : 8 * n ≤ 2 ^ 64) :
    subroutine_ok prog addr (expandCellsBudgetPlacedStackSpecAt C.F pl n allocHookStack) := by
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [expandCellsBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_alloc_expand_sat sp, ← memRegion_cells okmA n hn] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hinfo, hlen⟩, hpre⟩
  refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, 8 * n⟩,
    memRegion (sp - 4096#64) 3280 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, expandMultiInfoBudgetSpecSat, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [expandMultiInfoSpecSat]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk, hinfo, hlen⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, expandMultiInfoBudgetSpecSat, withVmPreserved,
      expandMultiInfoSpecSat, expandCellsBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_alloc_expand_sat sp]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand C.F prk info (8 * n)) ∗
        stackAt s0.sp expandMultiInfoStackSat ∗ memRegion (s0.sp - 4096#64) 3280) ∗ R)
      (hmacCore_entails_cells C.F hkdfA prk)
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨⟨htr, hvm⟩, by arm64_sep_close⟩

private theorem extractKey32BudgetPlacedStack_widen {prog : Program} {pl : Obj.MultiPlacement}
    {F : ShaCompress} {addr : BitVec 64} {st₁ st₂ k : Nat} {off : BitVec 64}
    (hsplit : ∀ sp, stackAt sp st₂ = memRegion (sp - off) k ∗ stackAt sp st₁)
    (h : subroutine_ok prog addr (extractKey32BudgetPlacedStackSpecAt F pl st₁)) :
    subroutine_ok prog addr (extractKey32BudgetPlacedStackSpecAt F pl st₂) := by
  refine subroutine_ok_map h ?_
  rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractKey32BudgetPlacedStackSpecAt] at hpre
  rw [hsplit sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨ret, saltA, rk, ikmA, ikm, sp⟩, memRegion (sp - off) k ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [extractKey32BudgetPlacedStackSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hpure, by arm64_sep_close⟩
  · dsimp only [extractKey32BudgetPlacedStackSpecAt] at hpost ⊢
    rw [hsplit sp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩; exact ⟨htr, by arm64_sep_close⟩

private theorem expandCellsBudgetPlacedStack_widen {prog : Program} {pl : Obj.MultiPlacement}
    {F : ShaCompress} {addr : BitVec 64} {n st₁ st₂ k : Nat} {off : BitVec 64}
    (hsplit : ∀ sp, stackAt sp st₂ = memRegion (sp - off) k ∗ stackAt sp st₁)
    (h : subroutine_ok prog addr (expandCellsBudgetPlacedStackSpecAt F pl n st₁)) :
    subroutine_ok prog addr (expandCellsBudgetPlacedStackSpecAt F pl n st₂) := by
  refine subroutine_ok_map h ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [expandCellsBudgetPlacedStackSpecAt] at hpre
  rw [hsplit sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩, memRegion (sp - off) k ∗ R, ?_,
    fun sf hpost => ?_⟩
  · dsimp only [expandCellsBudgetPlacedStackSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hpure, by arm64_sep_close⟩
  · dsimp only [expandCellsBudgetPlacedStackSpecAt] at hpost ⊢
    rw [hsplit sp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩; exact ⟨htr, by arm64_sep_close⟩

private theorem deallocBudgetPlacedStack_widen [LibsignalPlacement]
    {prog : Program} {pl : Obj.MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {addr : BitVec 64} {st₁ st₂ k : Nat} {off : BitVec 64}
    (hsplit : ∀ sp, stackAt sp st₂ = memRegion (sp - off) k ∗ stackAt sp st₁)
    (h : subroutine_ok prog addr (deallocBudgetPlacedStackSpecAt M A lim pl st₁)) :
    subroutine_ok prog addr (deallocBudgetPlacedStackSpecAt M A lim pl st₂) := by
  refine subroutine_ok_map h ?_
  rintro ⟨p, size, align, sp, st⟩ R s0 hpre
  dsimp only [deallocBudgetPlacedStackSpecAt] at hpre
  rw [hsplit sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨p, size, align, sp, st⟩, memRegion (sp - off) k ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [deallocBudgetPlacedStackSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hpure, by arm64_sep_close⟩
  · dsimp only [deallocBudgetPlacedStackSpecAt] at hpost ⊢
    rw [hsplit sp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩; exact ⟨htr, by arm64_sep_close⟩

/-- Contract-backed relocatable budget `<RootKey>::create_chain` (Block `40`) consuming
`extractBudgetSpecSat C.F` (`1152` B) and `expandMultiInfoBudgetSpecSat C.F` (`816` B). -/
theorem createChain_placed_ok_of_contracts_budget_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (hag_ok : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementSpec M A lim C.X)))
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractBudgetSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoBudgetSpecSat C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.createChainSpec M A lim C)) :=
  LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget.createChain_placed_ok_of_hooks_gen
    (callStack := calculateAgreementStack) (by decide)
    (calculateAgreementBudgetCallAt_ok hag_ok)
    (extractKey32BudgetPlacedStack_widen stackAt_calc_alloc_split
      (extractKey32BudgetPlacedAllocStack_ok_sat (C := C) hext))
    (expandCellsBudgetPlacedStack_widen stackAt_calc_alloc_split
      (expandCellsBudgetPlacedAllocStack_ok_sat (C := C) hexp 8 (by decide)))
    (deallocBudgetPlacedStack_widen stackAt_calc_alloc_split
      (deallocBudgetPlacedAllocStack_of_rustCliDealloc (pl := lsmpl) hdealloc_raw))

/-- Contract-backed relocatable budget `<RootKey>::create_chain` (Block `40`) at `createChainStackX`
consuming `extractBudgetSpecSat C.F` and `expandMultiInfoBudgetSpecSat C.F`. -/
theorem createChain_placed_ok_of_contracts_x_budget_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (hag_ok : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementSpecX M A lim C.X)))
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractBudgetSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoBudgetSpecSat C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack))) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.createChainSpecX M A lim C)) :=
  LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget.createChain_placed_ok_of_hooks_gen
    (callStack := calculateAgreementExtStack) (by decide)
    (calculateAgreementBudgetCallAt_ok hag_ok)
    (extractKey32BudgetPlacedStack_widen stackAt_calc_ext
      (extractKey32BudgetPlacedStack_widen stackAt_ext_alloc
        (extractKey32BudgetPlacedAllocStack_ok_sat (C := C) hext)))
    (expandCellsBudgetPlacedStack_widen stackAt_calc_ext
      (expandCellsBudgetPlacedStack_widen stackAt_ext_alloc
        (expandCellsBudgetPlacedAllocStack_ok_sat (C := C) hexp 8 (by decide))))
    (deallocBudgetPlacedStack_widen stackAt_calc_ext
      (deallocBudgetPlacedExtStack_of_rustCliDeallocExtern hdealloc_raw))

/-- Relocatable budget `<RootKey>::create_chain` (Block `40`) from callee contracts and `HookSat`
hypotheses (`extractBudgetSpecSat` + `expandMultiInfoBudgetSpecSat`). -/
theorem createChain_placed_ok_budget_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withLsRet624 (withVmPreserved (withStack (diffieHellmanSpec C.X) 1808))))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.ctEqSliceROSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractBudgetSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoBudgetSpecSat C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.createChainSpec M A lim C)) :=
  createChain_placed_ok_of_contracts_budget_sat
    (keys_ls_subroutine_ok_of_block_cro
      (LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget.calculateAgreement_placed_ok
        h_dh h_shdrop hct h_shim h_alloc h_stdrop))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hext)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hexp)
    (keys_ls_hook_ok_of_mem h_dealloc)

/-- Relocatable budget `<RootKey>::create_chain` (Block `40`) at `createChainStackX` from callee
contracts and `HookSat` hypotheses (`extractBudgetSpecSat` + `expandMultiInfoBudgetSpecSat`). -/
theorem createChain_placed_ok_x_budget_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withLsRet624 (withVmPreserved (withStack (diffieHellmanSpec C.X) 1808))))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.ctEqSliceROSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractBudgetSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoBudgetSpecSat C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.createChainSpecX M A lim C)) :=
  LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget.subroutine_ok_createChainSpecX_of_createChainSpec
    (createChain_placed_ok_budget_sat h_dh h_shdrop hct h_shim h_alloc h_stdrop hext hexp h_dealloc)

/-! ## 2. Budget `GenerateKeysBudget` Siblings -/

theorem extractSomeBudgetPlacedExtStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpecSat C.F))) :
    subroutine_ok prog addr (extractSomeBudgetPlacedStackSpecAt C.F pl extHookStack) := by
  refine subroutine_ok_map (extractSomeBudgetPlacedAllocStack_ok_sat (C := C) hext) ?_
  rintro ⟨ret, saltA, sv, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractSomeBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_ext_alloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨ret, saltA, sv, ikmA, ikm, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [extractSomeBudgetPlacedAllocStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [extractSomeBudgetPlacedAllocStackSpec,
      extractSomeBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_ext_alloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

theorem extractNoneBudgetPlacedAllocStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpecSat C.F))) :
    subroutine_ok prog addr (extractNoneBudgetPlacedStackSpecAt C.F pl allocHookStack) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractNoneBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_alloc_extract_sat sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx3, hx4, hsp, hikm⟩, hpre⟩
  refine ⟨⟨ret, 0#64, none, ikmA, ikm⟩, memRegion (sp - 4096#64) 2944 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, extractBudgetSpecSat, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [extractSpecSat, optSaltAt]
    subst hsp
    simp only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, forall_const, true_or,
      true_and, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx3, hx4, hikm⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, extractBudgetSpecSat, withVmPreserved, extractSpecSat,
      ExtractGhost.prk, optSaltAt, extractNoneBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_alloc_extract_sat sp]
    subst hsp
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    exact ⟨⟨htr, hvm⟩, by arm64_sep_close⟩

theorem extractNoneBudgetPlacedExtStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpecSat C.F))) :
    subroutine_ok prog addr (extractNoneBudgetPlacedStackSpecAt C.F pl extHookStack) := by
  refine subroutine_ok_map (extractNoneBudgetPlacedAllocStack_ok_sat (C := C) hext) ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractNoneBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_ext_alloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨ret, ikmA, ikm, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [extractNoneBudgetPlacedStackSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [extractNoneBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_ext_alloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

theorem extractEmptyBudgetPlacedAllocStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpecSat C.F))) :
    subroutine_ok prog addr (extractEmptyBudgetPlacedStackSpecAt C.F pl allocHookStack) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractEmptyBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_alloc_extract_sat sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx2, hx3, hx4, hsp, hikm⟩, hpre⟩
  refine ⟨⟨ret, s0.readReg64 .x1, none, ikmA, ikm⟩, memRegion (sp - 4096#64) 2944 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, extractBudgetSpecSat, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [extractSpecSat, optSaltAt]
    subst hsp
    simp only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, forall_const,
      true_and, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, Or.inr hx2, hx3, hx4, hikm⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, extractBudgetSpecSat, withVmPreserved, extractSpecSat,
      ExtractGhost.prk, optSaltAt, extractEmptyBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_alloc_extract_sat sp]
    subst hsp
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    exact ⟨⟨htr, hvm⟩, by arm64_sep_close⟩

theorem extractEmptyBudgetPlacedExtStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpecSat C.F))) :
    subroutine_ok prog addr (extractEmptyBudgetPlacedStackSpecAt C.F pl extHookStack) := by
  refine subroutine_ok_map (extractEmptyBudgetPlacedAllocStack_ok_sat (C := C) hext) ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractEmptyBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_ext_alloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨ret, ikmA, ikm, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [extractEmptyBudgetPlacedStackSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [extractEmptyBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_ext_alloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

theorem expandCellsBudgetPlacedExtStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hexp : subroutine_ok prog addr (withLsCodeRoLoaded pl (expandMultiInfoBudgetSpecSat C.F)))
    (n : Nat) (hn : 8 * n ≤ 2 ^ 64) :
    subroutine_ok prog addr (expandCellsBudgetPlacedStackSpecAt C.F pl n extHookStack) :=
  expandCellsBudgetPlacedStack_widen stackAt_ext_alloc
    (expandCellsBudgetPlacedAllocStack_ok_sat (C := C) hexp n hn)

/-- Contract-backed relocatable budget `<MessageKeyGenerator>::generate_keys` (Block `69`)
consuming `extractBudgetSpecSat C.F` (`1152` B) and `expandMultiInfoBudgetSpecSat C.F` (`816` B). -/
theorem generateKeys_placed_ok_of_contracts_budget_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractBudgetSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoBudgetSpecSat C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.generateKeysSpec M A lim C.F)) :=
  generateKeys_placed_ok_of_hooks_gen (callStack := allocHookStack) (by decide)
    (extractNoneBudgetPlacedAllocStack_ok_sat (C := C) hext)
    (extractEmptyBudgetPlacedAllocStack_ok_sat (C := C) hext)
    (extractSomeBudgetPlacedAllocStack_ok_sat (C := C) hext)
    (expandCellsBudgetPlacedAllocStack_ok_sat (C := C) hexp 10 (by decide))
    (deallocGenBudgetPlacedAllocStack_of_rustCliDealloc (pl := lsmpl) hdealloc_raw)

/-- Contract-backed relocatable budget `<MessageKeyGenerator>::generate_keys` (Block `69`) at
`generateKeysStackX` consuming `extractBudgetSpecSat C.F` and `expandMultiInfoBudgetSpecSat C.F`. -/
theorem generateKeys_placed_ok_of_contracts_x_budget_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractBudgetSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoBudgetSpecSat C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack))) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.generateKeysSpecX M A lim C.F)) :=
  generateKeys_placed_ok_of_hooks_gen (callStack := extHookStack) (by decide)
    (extractNoneBudgetPlacedExtStack_ok_sat (C := C) hext)
    (extractEmptyBudgetPlacedExtStack_ok_sat (C := C) hext)
    (extractSomeBudgetPlacedExtStack_ok_sat (C := C) hext)
    (expandCellsBudgetPlacedExtStack_ok_sat (C := C) hexp 10 (by decide))
    (deallocGenBudgetPlacedExtStack_of_rustCliDeallocExtern hdealloc_raw)

/-- Relocatable budget `<MessageKeyGenerator>::generate_keys` (Block `69`) from callee contracts
and `HookSat` hypotheses (`extractBudgetSpecSat` + `expandMultiInfoBudgetSpecSat`). -/
theorem generateKeys_placed_ok_budget_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractBudgetSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoBudgetSpecSat C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.generateKeysSpec M A lim C.F)) :=
  generateKeys_placed_ok_of_contracts_budget_sat
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hext)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hexp)
    (keys_ls_hook_ok_of_mem h_dealloc)

/-- Relocatable budget `<MessageKeyGenerator>::generate_keys` (Block `69`) at `generateKeysStackX`
from callee contracts and `HookSat` hypotheses. -/
theorem generateKeys_placed_ok_x_budget_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractBudgetSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoBudgetSpecSat C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.generateKeysSpecX M A lim C.F)) :=
  LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget.subroutine_ok_generateKeysSpecX_of_generateKeysSpec
    (generateKeys_placed_ok_budget_sat hext hexp h_dealloc)

/-! ## 3. Non-Budget `CreateChain` and `GenerateKeys` Siblings -/

theorem extractSomePlacedAllocStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractSpecSat C.F))) :
    subroutine_ok prog addr (extractSomePlacedAllocStackSpec C.F pl) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, saltA, sv, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractSomePlacedAllocStackSpec] at hpre
  rw [stackAt_alloc_extract_sat sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hx4, hsp, hsalt_ne, hikm⟩, hpre⟩
  refine ⟨⟨ret, saltA, some sv, ikmA, ikm⟩, memRegion (sp - 4096#64) 2944 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [extractSpecSat, optSaltAt]
    subst hsp
    rw [eq_true hsalt_ne, pure_true, emp_sepConj]
    simp only [Option.isSome_some, reduceCtorEq, IsEmpty.forall_iff, forall_const, true_and,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hikm⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, extractSpecSat, ExtractGhost.prk, optSaltAt,
      extractSomePlacedAllocStackSpec] at hpost ⊢
    rw [stackAt_alloc_extract_sat sp]
    subst hsp
    rw [eq_true hsalt_ne, pure_true, emp_sepConj] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

theorem extractKey32PlacedAllocStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractSpecSat C.F))) :
    subroutine_ok prog addr (extractKey32PlacedAllocStackSpec C.F pl) := by
  refine subroutine_ok_map (extractSomePlacedAllocStack_ok_sat (C := C) hext) ?_
  rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
  refine ⟨⟨ret, saltA, keyToBytesVec32 rk, ikmA, ikm, sp⟩, R, ?_, ?_⟩
  · dsimp only [extractSomePlacedAllocStackSpec, extractKey32PlacedAllocStackSpec] at hpre ⊢
    rw [pointsTo_keyVec_toList]
    exact hpre
  · intro sf hpost
    dsimp only [extractSomePlacedAllocStackSpec, extractKey32PlacedAllocStackSpec] at hpost ⊢
    rw [← pointsTo_keyVec_toList]
    exact hpost

theorem extractNonePlacedAllocStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractSpecSat C.F))) :
    subroutine_ok prog addr (extractNonePlacedAllocStackSpec C.F pl) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractNonePlacedAllocStackSpec] at hpre
  rw [stackAt_alloc_extract_sat sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx3, hx4, hsp, hikm⟩, hpre⟩
  refine ⟨⟨ret, 0#64, none, ikmA, ikm⟩, memRegion (sp - 4096#64) 2944 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [extractSpecSat, optSaltAt]
    subst hsp
    simp only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, forall_const, true_or,
      true_and, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx3, hx4, hikm⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, extractSpecSat, ExtractGhost.prk, optSaltAt,
      extractNonePlacedAllocStackSpec] at hpost ⊢
    rw [stackAt_alloc_extract_sat sp]
    subst hsp
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

theorem extractEmptyPlacedAllocStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractSpecSat C.F))) :
    subroutine_ok prog addr (extractEmptyPlacedAllocStackSpec C.F pl) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractEmptyPlacedAllocStackSpec] at hpre
  rw [stackAt_alloc_extract_sat sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx2, hx3, hx4, hsp, hikm⟩, hpre⟩
  refine ⟨⟨ret, s0.readReg64 .x1, none, ikmA, ikm⟩, memRegion (sp - 4096#64) 2944 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [extractSpecSat, optSaltAt]
    subst hsp
    simp only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, forall_const,
      true_and, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, Or.inr hx2, hx3, hx4, hikm⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, extractSpecSat, ExtractGhost.prk, optSaltAt,
      extractEmptyPlacedAllocStackSpec] at hpost ⊢
    rw [stackAt_alloc_extract_sat sp]
    subst hsp
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

theorem expandCellsPlacedAllocStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hexp : subroutine_ok prog addr (withLsCodeRoLoaded pl (expandMultiInfoSpecSat C.F)))
    (n : Nat) (hn : 8 * n ≤ 2 ^ 64) :
    subroutine_ok prog addr (expandCellsPlacedAllocStackSpec C.F pl n) := by
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [expandCellsPlacedAllocStackSpec] at hpre
  rw [stackAt_alloc_expand_sat sp, ← memRegion_cells okmA n hn] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hinfo, hlen⟩, hpre⟩
  refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, 8 * n⟩,
    memRegion (sp - 4096#64) 3280 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [expandMultiInfoSpecSat]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk, hinfo, hlen⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, expandMultiInfoSpecSat, expandCellsPlacedAllocStackSpec] at hpost ⊢
    rw [stackAt_alloc_expand_sat sp]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand C.F prk info (8 * n)) ∗
        stackAt s0.sp expandMultiInfoStackSat ∗ memRegion (s0.sp - 4096#64) 3280) ∗ R)
      (hmacCore_entails_cells C.F hkdfA prk)
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

private theorem extractKey32PlacedStack_widen {prog : Program} {pl : Obj.MultiPlacement}
    {F : ShaCompress} {addr : BitVec 64} {st₁ st₂ k : Nat} {off : BitVec 64}
    (hsplit : ∀ sp, stackAt sp st₂ = memRegion (sp - off) k ∗ stackAt sp st₁)
    (h : subroutine_ok prog addr (extractKey32PlacedStackSpecAt F pl st₁)) :
    subroutine_ok prog addr (extractKey32PlacedStackSpecAt F pl st₂) := by
  refine subroutine_ok_map h ?_
  rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractKey32PlacedStackSpecAt] at hpre
  rw [hsplit sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨ret, saltA, rk, ikmA, ikm, sp⟩, memRegion (sp - off) k ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [extractKey32PlacedStackSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hpure, by arm64_sep_close⟩
  · dsimp only [extractKey32PlacedStackSpecAt] at hpost ⊢
    rw [hsplit sp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩; exact ⟨htr, by arm64_sep_close⟩

private theorem expandCellsPlacedStack_widen {prog : Program} {pl : Obj.MultiPlacement}
    {F : ShaCompress} {addr : BitVec 64} {n st₁ st₂ k : Nat} {off : BitVec 64}
    (hsplit : ∀ sp, stackAt sp st₂ = memRegion (sp - off) k ∗ stackAt sp st₁)
    (h : subroutine_ok prog addr (expandCellsPlacedStackSpecAt F pl n st₁)) :
    subroutine_ok prog addr (expandCellsPlacedStackSpecAt F pl n st₂) := by
  refine subroutine_ok_map h ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [expandCellsPlacedStackSpecAt] at hpre
  rw [hsplit sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩, memRegion (sp - off) k ∗ R, ?_,
    fun sf hpost => ?_⟩
  · dsimp only [expandCellsPlacedStackSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hpure, by arm64_sep_close⟩
  · dsimp only [expandCellsPlacedStackSpecAt] at hpost ⊢
    rw [hsplit sp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩; exact ⟨htr, by arm64_sep_close⟩

theorem expandCellsPlacedExtStack_ok_sat {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hexp : subroutine_ok prog addr (withLsCodeRoLoaded pl (expandMultiInfoSpecSat C.F)))
    (n : Nat) (hn : 8 * n ≤ 2 ^ 64) :
    subroutine_ok prog addr (expandCellsPlacedExtStackSpec C.F pl n) :=
  expandCellsPlacedStack_widen stackAt_ext_alloc
    (expandCellsPlacedAllocStack_ok_sat (C := C) hexp n hn)

/-- Contract-backed relocatable `<RootKey>::create_chain` (Block `40`) consuming
`extractSpecSat C.F` (`1152` B) and `expandMultiInfoSpecSat C.F` (`816` B). -/
theorem createChain_placed_ok_of_contracts_sat [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (hag_ok : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec C.X A)))
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoSpecSat C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpec C A)) := by
  have hdealloc_c : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsρ lsRustDeallocSym)
      (deallocPlacedStackSpecAt A lsmpl calculateAgreementStack) := by
    refine subroutine_ok_map (deallocAllocStack_of_rustDealloc_placed hdealloc_raw) ?_
    rintro ⟨p, size, align, sp⟩ R s0 hpre
    dsimp only [deallocPlacedStackSpecAt] at hpre
    rw [stackAt_calc_alloc_split sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, hx0, hx1, hx2, _, _, _, hsp⟩, hpre⟩
    refine ⟨⟨p, size, align, sp⟩, memRegion (sp - 4256#64) 160 ∗ R, ?_, fun sf hpost => ?_⟩
    · dsimp only [deallocAllocStackSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1, hx2, hsp⟩, by arm64_sep_close⟩
    · dsimp only [deallocAllocStackSpec, deallocPlacedStackSpecAt] at hpost ⊢
      rw [stackAt_calc_alloc_split sp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩; exact ⟨htr, by arm64_sep_close⟩
  exact createChain_placed_ok_of_hooks_gen (callStack := calculateAgreementStack) (by decide)
    (calculateAgreementPlacedCall_ok hag_ok)
    (extractKey32PlacedStack_widen stackAt_calc_alloc_split
      (extractKey32PlacedAllocStack_ok_sat (C := C) hext))
    (expandCellsPlacedStack_widen stackAt_calc_alloc_split
      (expandCellsPlacedAllocStack_ok_sat (C := C) hexp 8 (by decide)))
    hdealloc_c

/-- Contract-backed relocatable `<RootKey>::create_chain` (Block `40`) at `createChainStackX`
consuming `extractSpecSat C.F` and `expandMultiInfoSpecSat C.F`. -/
theorem createChain_placed_ok_of_contracts_x_sat [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (hag_ok : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpecX C.X A)))
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoSpecSat C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack))) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpecX C A)) := by
  have hdealloc_c : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsρ lsRustDeallocSym)
      (deallocPlacedStackSpecAt A lsmpl calculateAgreementExtStack) := by
    refine subroutine_ok_map (deallocPlacedExtStack_of_rustDeallocExtern hdealloc_raw) ?_
    rintro ⟨p, size, align, sp⟩ R s0 hpre
    dsimp only [deallocPlacedStackSpecAt] at hpre
    rw [stackAt_calc_ext sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hpre⟩
    refine ⟨⟨p, size, align, sp⟩, memRegion (sp - 16544#64) 160 ∗ R, ?_, fun sf hpost => ?_⟩
    · dsimp only [deallocPlacedExtStackSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hpure, by arm64_sep_close⟩
    · dsimp only [deallocPlacedExtStackSpec, deallocPlacedStackSpecAt] at hpost ⊢
      rw [stackAt_calc_ext sp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩; exact ⟨htr, by arm64_sep_close⟩
  exact createChain_placed_ok_of_hooks_gen (callStack := calculateAgreementExtStack) (by decide)
    (calculateAgreementPlacedCallX_ok hag_ok)
    (extractKey32PlacedStack_widen stackAt_calc_ext
      (extractKey32PlacedStack_widen stackAt_ext_alloc
        (extractKey32PlacedAllocStack_ok_sat (C := C) hext)))
    (expandCellsPlacedStack_widen stackAt_calc_ext
      (expandCellsPlacedExtStack_ok_sat (C := C) hexp 8 (by decide)))
    hdealloc_c

/-- Relocatable `<RootKey>::create_chain` (Block `40`) from callee contracts and `HookSat`
hypotheses (`extractSpecSat` + `expandMultiInfoSpecSat`). -/
theorem createChain_placed_ok_sat [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withLsRet624 (withStack (diffieHellmanSpec C.X) 1808)))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked)
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoSpecSat C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpec C A)) :=
  createChain_placed_ok_of_contracts_sat
    (keys_ls_subroutine_ok_of_block_cro
      (calculateAgreement_placed_ok h_dh h_shdrop hct h_shim h_alloc h_stdrop hpanic))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hext)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hexp)
    (keys_ls_hook_ok_of_mem h_dealloc)

/-- Relocatable `<RootKey>::create_chain` (Block `40`) at `createChainStackX` from callee contracts
and `HookSat` hypotheses (`extractSpecSat` + `expandMultiInfoSpecSat`). -/
theorem createChain_placed_ok_x_sat [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withLsRet624 (withStack (diffieHellmanSpec C.X) 1808)))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked)
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoSpecSat C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpecX C A)) :=
  subroutine_ok_createChainSpecX_of_createChainSpec
    (createChain_placed_ok_sat h_dh h_shdrop hct h_shim h_alloc h_stdrop hpanic hext hexp h_dealloc)

set_option maxHeartbeats 6000000 in
/-- Relocatable `<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys` (Block `69`)
consuming `extractSpecSat C.F` (`1152` B) and `expandMultiInfoSpecSat C.F` (`816` B). -/
theorem generateKeys_placed_ok_of_contracts_sat [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoSpecSat C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)) := by
  refine subroutine_ok_withLsCodeRoLoaded_rodata''
    (roSym := "libsignal_protocol:.rodata..Lanon.175")
    (roBytes := whisperMessageKeys) (by decide) ?_
  wp_init x s0
  have hext_none := extractNonePlacedAllocStack_ok_sat (C := C) hext
  have hext_empty := extractEmptyPlacedAllocStack_ok_sat (C := C) hext
  have hext_some := extractSomePlacedAllocStack_ok_sat (C := C) hext
  have hexp' := expandCellsPlacedAllocStack_ok_sat (C := C) hexp 10 (by decide)
  simp only [expandCellsPlacedAllocStackSpec, cells, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  have hdealloc := deallocAllocStack_of_rustDealloc_placed hdealloc_raw
  clear hext hexp hdealloc_raw
  obtain ⟨genA, ⟨seed, counter⟩, pqrKeyA, pqrKey, out⟩ := x
  dsimp only [generateKeysSpec] at *
  have hF0 : LsFrozenInv lsmpl s0 := ‹_›
  have hseed_len : seed.length = 32 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = genA› ‹s0.readReg64 (.gpr 1#5) = pqrKeyA›
    ‹s0.readReg64 (.gpr 8#5) = out›
  rw (occs := .pos [1]) [fnFrame_split_generateKeys_pre s0.sp]
  rw [memRegion_out_generateKeys (s0.readReg64 (.gpr 8#5))]
  wp_simp_pre_fast [mkgAt, vecU8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  rename_i seed_cap seed_ptr
  apply SepWP.replace_pre
    (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 0#5) + 8#64) seed_cap seed_ptr seed hseed_len)
    (by sep_focus)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_extract_exists
  rename_i hseed
  obtain ⟨hseed_le, hseed_small, hseed_ptr, hseed_cap_ne⟩ := hseed
  have hseed_cap_beq : (seed_cap == 0#64) = false := beq_eq_false_iff_ne.mpr hseed_cap_ne
  rcases pqrKey with _ | sv
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F none seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed none
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, sepConj_assoc]
    wp_extract_exists
    rename_i isNiche
    cases isNiche
    · wp_simp_pre_fast [Bool.false_eq_true, ↓reduceIte, vecU8, sepConj_assoc]
      wp_extract_exists
      rename_i pqr_cap pqr_ptr
      apply SepWP.replace_pre
        (hPQ := vecU8At_split_nil A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr)
        (by sep_focus)
      wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_extract_exists
      rename_i hpqr
      obtain ⟨hpqr_small, hpqr_ptr⟩ := hpqr
      have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
      have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hpqr_add1_ne
      apply SepWP.of_sepWP_lscro hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_lscro hF1
      wp_call hext_empty (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        lsmpl.ρ "libsignal_protocol:.rodata..Lanon.175", whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64),
        bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap hseed_len hseed_le hseed_small)
        (by sep_focus)
      wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
      wp_extract_exists
      by_cases hpqr_cap0 : pqr_cap = 0#64
      · subst hpqr_cap0
        wp_simp_pre_fast [↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _) (by sep_focus)
        rw [fnFrame_split_generateKeys_post s0.sp, messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
      · have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap0
        wp_simp_pre_fast [hpqr_cap0, ↓reduceIte, sepConj_assoc]
        wp_steps
        wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _) (by sep_focus)
        rw [fnFrame_split_generateKeys_post s0.sp, messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
    · wp_simp_pre_fast [↓reduceIte, noneCap,
        (memRegion_cells (s0.readReg64 (.gpr 1#5) + 8#64) 2 (by decide) :
          memRegion (s0.readReg64 (.gpr 1#5) + 8#64) 16 = cells (s0.readReg64 (.gpr 1#5) + 8#64) 2),
        sepConj_assoc]
      cells_pre_unfold_fast
      wp_extract_exists
      apply SepWP.of_sepWP_lscro hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_lscro hF1
      wp_call hext_none (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _) (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        lsmpl.ρ "libsignal_protocol:.rodata..Lanon.175", whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64),
        bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap hseed_len hseed_le hseed_small)
        (by sep_focus)
      wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
      wp_extract_exists
      wp_steps
      apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _) (by sep_focus)
      rw [fnFrame_split_generateKeys_post s0.sp, messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
      wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
      wp_done
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F (some sv) seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed (some sv)
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, vecU8, sepConj_assoc]
    wp_extract_exists
    rename_i pqr_cap pqr_ptr
    have hsv_len : sv.toList.length = 32 := List.Vector.toList_length sv
    apply SepWP.replace_pre
      (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr sv.toList hsv_len)
      (by sep_focus)
    wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_extract_exists
    rename_i hpqr
    obtain ⟨hpqr_le, hpqr_small, hpqr_ptr, hpqr_cap_ne⟩ := hpqr
    have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
    have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hpqr_add1_ne
    have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap_ne
    apply SepWP.of_sepWP_lscro hF0
    wp_steps
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF1
    apply SepWP.of_sepWP_lscro hF1
    wp_call hext_some (s0.sp - 272#64, pqr_ptr, sv, seed_ptr, seed, s0.sp - 496#64)
    wp_extract_exists
    rw [hprk (s0.sp - 272#64)]
    apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _) (by sep_focus)
    wp_extract_exists
    rename_i hgood
    wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF2
    wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F (some sv) seed, s0.sp - 272#64,
      lsmpl.ρ "libsignal_protocol:.rodata..Lanon.175", whisperMessageKeys,
      s0.sp - 496#64, s0.sp - 496#64)
    wp_extract_exists
    wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64),
      bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap hseed_len hseed_le hseed_small)
      (by sep_focus)
    wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 pqr_ptr sv.toList pqr_cap hsv_len hpqr_le hpqr_small)
      (by sep_focus)
    wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _) (by sep_focus)
    rw [fnFrame_split_generateKeys_post s0.sp,
      messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
    wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
    wp_done

/-- Relocatable `<MessageKeyGenerator>::generate_keys` (Block `69`) from callee contracts and
`HookSat` hypotheses (`extractSpecSat` + `expandMultiInfoSpecSat`). -/
theorem generateKeys_placed_ok_sat [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoSpecSat C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)) :=
  generateKeys_placed_ok_of_contracts_sat
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hext)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hexp)
    (keys_ls_hook_ok_of_mem h_dealloc)

/-- Relocatable `<MessageKeyGenerator>::generate_keys` (Block `69`) at `generateKeysStackX` from
callee contracts and `HookSat` hypotheses (`extractSpecSat` + `expandMultiInfoSpecSat`). -/
theorem generateKeys_placed_ok_x_sat [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractSpecSat C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoSpecSat C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpecX C.F A)) :=
  subroutine_ok_generateKeysSpecX_of_generateKeysSpec
    (generateKeys_placed_ok_sat hext hexp h_dealloc)

end

end LibsignalBinary.Proofs.TripleRatchet.Keys.KeysSat

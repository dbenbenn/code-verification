/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetBbSat
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudgetSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Keys.KeysSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat

/-!
# `HookSat`-backed `black_box` Sibling of `Stage2V1BasePlacedBudget{,Sat}` (`Stage2V1BasePlacedBudgetBbSat`)

Stacks `blackBox : HookSat H lsBlackBoxU8Sym blackBoxSpecSat` on top of post-WP6b
`Stage2V1BasePlacedBudgetSat.ResponderPqxdhPlacedHookContractsSat`
(`hkdf : HkdfPlacedHooksExactSat C.F H` and `memsetBudget : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`):
- `ResponderPqxdhPlacedHookContractsBbSat`
- `ResponderPqxdhPlacedHookContractsSat.toBbSat` & `ResponderPqxdhPlacedHookContracts.toBbSat`
- All 8 bundle projections
- `cliResponderPqxdhHookContractsPlaced{,_of_hookSat,_of_runHooks}_bb_sat` (taking `hG`, `hMs`, and
  `hBb`, with zero reference to `memset_row_placed` or `blackBox_row_placed`) plus `hG`/`hMs`-only
  convenience wrappers from `Stage2V1BasePlacedBudgetSat`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudgetBbSat

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsBlackBoxU8Sym lsRustDeallocSym
   lsRustNoAllocShimSym lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims)
open CryptoVerification.E2E.Pqxdh.Initiator
  (Primitives StructuralPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PrimitivesMatchCrypto lsDalekMontToEdSym lsDalekTorsionFreeSym lsKyberDecapsSym
   ofSignalPqxdhPrimitives toSignalPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchet
  (diffieHellmanSpec keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro lsMemsetSym
   noAllocShimSpec withLsCodeRoLoaded withStack zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (lsDhSym lsRustAllocSym lsSharedDropSym lsStaticDropSym)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
  (PqxdhHkdfExpandMultiInfoPlacedOk PqxdhHkdfExtractPlacedOk
   handshakeKeysDerivePlacedBaseSpec handshakeKeysDerivePlacedVmSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
  (PqxdhCalculateAgreementPlacedFrozenOk PqxdhCalculateAgreementPlacedOk)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
  (expand_multi_info_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
  (kyberDecapsStubBudgetSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetBbSat
  (calculateAgreement_placed_ok_unconditional_sat pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat
   pqxdhCalculateAgreement_placed_ok_of_block_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (extract_placed_vm_ok_of_other_block_sat handshakeKeysDerive_placed_ok_of_block_sat
   handshakeKeysDerive_placed_vm_ok_of_block_sat pqxdhHkdfExpandMultiInfo_placed_ok_sat
   pqxdhHkdfExtract_placed_ok_sat)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202
  (IsCanonicalCurveSound dalekHookStack dalekMontToEdExtSpec dalekTorsionFreeExtSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
  (ResponderPqxdhPlacedHookContracts cliExternsPlaced_noAllocShimBudget_sat
   cliGhostExterns_dh1808_budget_sat cliGhostExterns_kemDecaps_budget_sat
   cliModelPrims_curveSound)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudgetSat
  (ResponderPqxdhPlacedHookContractsSat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliGhostExterns_blackBoxSat_budget_sat
   cliGhostExterns_sharedSecretDrop_budget_sat cliGhostExterns_staticSecretDrop_budget_sat
   cliGhostExterns_toEdwards_budget_sat cliGhostExterns_torsionFree_budget_sat)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
  (subroutine_ok_createChainSpecX_of_createChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec createChainSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Keys.KeysSat
  (createChain_placed_ok_of_contracts_budget_sat)

private theorem hookSat_noAllocShimBudget_of_withVmPreserved_bb {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-- `HookSat`-backed `black_box` sibling stacked on
`Stage2V1BasePlacedBudgetSat.ResponderPqxdhPlacedHookContractsSat`
(`hkdf : HkdfPlacedHooksExactSat C.F H` and
`memsetBudget : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`). -/
structure ResponderPqxdhPlacedHookContractsBbSat [LibsignalPlacement] (M : AllocCostModel)
    (P : Primitives) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop where
  hkdf             : HkdfPlacedHooksExactSat C.F H
  memsetBudget     : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec
  dh               : HookSat H lsDhSym (withLsRet (withVmPreserved (withStack (diffieHellmanSpec C.X) 1808)))
  sharedDrop       : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec)
  staticDrop       : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)
  blackBox         : HookSat H lsBlackBoxU8Sym blackBoxSpecSat
  noAllocShim      : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec
  alloc            : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc          : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubBudgetSpec P)
  curveSound       : IsCanonicalCurveSound (toSignalPqxdhPrimitives P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym
    (withLsRet (withVmPreserved (dalekMontToEdExtSpec dalekHookStack)))
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym
    (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec dalekHookStack)))

/-- Bridge from `Stage2V1BasePlacedBudgetSat.ResponderPqxdhPlacedHookContractsSat` to
`ResponderPqxdhPlacedHookContractsBbSat` (weakening only `blackBox`). -/
theorem ResponderPqxdhPlacedHookContractsSat.toBbSat [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : ResponderPqxdhPlacedHookContractsSat M P C A lim H) :
    ResponderPqxdhPlacedHookContractsBbSat M P C A lim H :=
  { hkdf             := h.hkdf
    memsetBudget     := h.memsetBudget
    dh               := h.dh
    sharedDrop       := h.sharedDrop
    staticDrop       := h.staticDrop
    blackBox         := h.blackBox
    noAllocShim      := h.noAllocShim
    alloc            := h.alloc
    dealloc          := h.dealloc
    kyberDecaps      := h.kyberDecaps
    curveSound       := h.curveSound
    dalekMontToEd    := h.dalekMontToEd
    dalekTorsionFree := h.dalekTorsionFree }

/-- Exact-to-`HookSat` bridge from `ResponderPqxdhPlacedHookContracts`
(`Stage2V1BasePlacedBudget.lean`) to `ResponderPqxdhPlacedHookContractsBbSat`. -/
theorem ResponderPqxdhPlacedHookContracts.toBbSat [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : ResponderPqxdhPlacedHookContracts M P C A lim H) :
    ResponderPqxdhPlacedHookContractsBbSat M P C A lim H :=
  ResponderPqxdhPlacedHookContractsSat.toBbSat
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudgetSat.ResponderPqxdhPlacedHookContracts.toSat h)

theorem ResponderPqxdhPlacedHookContractsBbSat.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsBbSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block_sat hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

theorem ResponderPqxdhPlacedHookContractsBbSat.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsBbSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

theorem ResponderPqxdhPlacedHookContractsBbSat.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsBbSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have _ : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  exact pqxdhHkdfExtract_placed_ok_sat hP hi

theorem ResponderPqxdhPlacedHookContractsBbSat.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsBbSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have _ : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  exact pqxdhHkdfExpandMultiInfo_placed_ok_sat hP hi

theorem ResponderPqxdhPlacedHookContractsBbSat.handshakeKeysDerive_vm_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsBbSat M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedVmSpec P)) := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have _ : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  exact handshakeKeysDerive_placed_vm_ok_of_block_sat hWF hP hi

theorem ResponderPqxdhPlacedHookContractsBbSat.handshakeKeysDerive_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsBbSat M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec M P A lim)) := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have _ : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  exact handshakeKeysDerive_placed_ok_of_block_sat hWF hP hi

theorem ResponderPqxdhPlacedHookContractsBbSat.createChain_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsBbSat M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)) := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have _ : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  have h40 := createChain_placed_ok_of_contracts_budget_sat
    (keys_ls_subroutine_ok_of_block_cro
      (calculateAgreement_placed_ok_unconditional_sat hH.dh hH.sharedDrop hH.blackBox
        hH.noAllocShim hH.alloc hH.staticDrop))
    (extract_placed_vm_ok_of_other_block_sat C H)
    (expand_multi_info_placed_vm_ok_of_other_block_sat C H)
    (keys_ls_hook_ok_of_mem hH.dealloc)
  exact keys_ls_subroutine_ok_of_block_cro h40 hi (by decide) (by decide)

theorem ResponderPqxdhPlacedHookContractsBbSat.createChain_x_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsBbSat M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)) := by
  have : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  have _ : HkdfPlacedHooksExactBudgetSat C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hH.memsetBudget
  have h40 := subroutine_ok_createChainSpecX_of_createChainSpec
    (createChain_placed_ok_of_contracts_budget_sat
      (keys_ls_subroutine_ok_of_block_cro
        (calculateAgreement_placed_ok_unconditional_sat hH.dh hH.sharedDrop hH.blackBox
          hH.noAllocShim hH.alloc hH.staticDrop))
      (extract_placed_vm_ok_of_other_block_sat C H)
      (expand_multi_info_placed_vm_ok_of_other_block_sat C H)
      (keys_ls_hook_ok_of_mem hH.dealloc))
  exact keys_ls_subroutine_ok_of_block_cro h40 hi (by decide) (by decide)

/-- `ResponderPqxdhPlacedHookContractsBbSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g`, `hMs`, `hBb`, and `HookSat` contracts for `alloc`, `dealloc`, and
`noAllocShim` (with zero reference to `memset_row_placed` or `blackBox_row_placed`). -/
theorem cliResponderPqxdhHookContractsPlaced_of_hookSat_bb_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (hBb : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsBlackBoxU8Sym
      blackBoxSpecSat)
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq) :
    ResponderPqxdhPlacedHookContractsBbSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  hkdf := HkdfPlacedHooksExactSat.of_allocHooks hG hF
  memsetBudget := hMs
  dh := cliGhostExterns_dh1808_budget_sat mmpl g W hG hX
  sharedDrop := cliGhostExterns_sharedSecretDrop_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk
  staticDrop := cliGhostExterns_staticSecretDrop_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk
  blackBox := hBb
  noAllocShim := hnoAllocShim
  alloc := halloc
  dealloc := hdealloc
  kyberDecaps := cliGhostExterns_kemDecaps_budget_sat mmpl g W hG hDecaps X
  curveSound := cliModelPrims_curveSound X W
  dalekMontToEd := cliGhostExterns_toEdwards_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk
  dalekTorsionFree := cliGhostExterns_torsionFree_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk

theorem cliResponderPqxdhHookContractsPlaced_bb_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (hBb : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsBlackBoxU8Sym
      blackBoxSpecSat) :
    ResponderPqxdhPlacedHookContractsBbSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliResponderPqxdhHookContractsPlaced_of_hookSat_bb_sat X mmpl g W hG hF hX hDecaps hMs hBb
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq)

theorem cliResponderPqxdhHookContractsPlaced_of_runHooks_bb_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (hBb : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsBlackBoxU8Sym
      blackBoxSpecSat) :
    ResponderPqxdhPlacedHookContractsBbSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliResponderPqxdhHookContractsPlaced_of_hookSat_bb_sat X mmpl g W hG hF hX hDecaps hMs hBb
    hh.codecHooks.alloc hh.codecHooks.dealloc
    (hookSat_noAllocShimBudget_of_withVmPreserved_bb hh.codecHooks.shim)

theorem cliResponderPqxdhHookContractsPlaced_of_hookSat_sat_toBbSat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq) :
    ResponderPqxdhPlacedHookContractsBbSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliResponderPqxdhHookContractsPlaced_of_hookSat_bb_sat X mmpl g W hG hF hX hDecaps hMs
    (cliGhostExterns_blackBoxSat_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)
    halloc hdealloc hnoAllocShim

theorem cliResponderPqxdhHookContractsPlaced_sat_toBbSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    ResponderPqxdhPlacedHookContractsBbSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliResponderPqxdhHookContractsPlaced_bb_sat X mmpl g W hG hF hX hDecaps hMs
    (cliGhostExterns_blackBoxSat_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)

theorem cliResponderPqxdhHookContractsPlaced_of_runHooks_sat_toBbSat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hDecaps : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    ResponderPqxdhPlacedHookContractsBbSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliResponderPqxdhHookContractsPlaced_of_runHooks_bb_sat X mmpl g W hG hF hX hDecaps hh hMs
    (cliGhostExterns_blackBoxSat_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudgetBbSat

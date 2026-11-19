/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseX -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Budget-Threaded `SessionStructure::clone` Base Helpers (Block `80`)

Specializes `SerContractsXPlaced M A lim H` stub contracts and Block `82 → 80` `Chain::clone`
bridges onto `lsProg_80 H`, and provides `VmPreserved`-aware `SepWPpLsCl` stepping and `A.pool`
transport combinators for `SessionStructure::clone`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseXBudget

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded lsmpl lsρ
  lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
  withLsCodeLoaded withLsCl withMemEq
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (sepWPp_pure_2nd)
open CryptoVerification.E2E.Record.Placed (
  blkPl_80 blkPl_82 lsProg_80 lsProg_82
)
open CryptoVerification.E2E.Record.Serialization (SessionCloneGhost)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  RustLayoutOk FitsEvents rustAllocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget (
  sepWPp_of_sepWP_lscl_vm_sc sc_transport_pool scNoPanicPost sc_noPanic_of_false
  maxReq_le_mallocngMaxAllocSize_of_fitsEnv sessionCloneEnv_segCloneEvents
  fitsEvents_segCloneEvents_of_fitsEnv
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  SerContractsXPlaced sessionCloneSpecX
  shim_placed_ok_at_stateX alloc_placed_ok_at_stateX
  allocNoOom_placed_ok_at_stateX memcpy_placed_ok_at_stateX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (SepWPpLsCl)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget (
  protoChainCloneSpecX chainCloneSpecX senderChainCloneSpecX
  ProtoChainCloneLocal1PlacedOkX ChainCloneLocal1PlacedOkX SenderChainCloneLocal1PlacedOkX
)

/-! ## Re-exported stack decomposition and `SessionCloneEnv` bridges -/

abbrev scSubStackX : Nat :=
  CryptoVerification.E2E.Record.Serialization.SessionCloneAux.scSubStackX

abbrev stackAt_sessionClone_eq_x :=
  @CryptoVerification.E2E.Record.Serialization.SessionCloneAux.stackAt_sessionClone_eq_x

abbrev fitsEvents_segCloneEvents_of_fitsEnv_x :=
  @fitsEvents_segCloneEvents_of_fitsEnv

/-! ## Extern stub bridges and call helpers on Block `80` -/

theorem sc_shim_placed_ok_at_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_80 H) (lsρ lsRustNoAllocShimSym)
      (withLsCl lsmpl session2ShimBudgetSpecX) :=
  hC.alloc.shim (callerProg := lsProg_80 H)

theorem sc_alloc_placed_ok_at_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_80 H) (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)) :=
  hC.alloc.alloc (callerProg := lsProg_80 H)

theorem sc_memcpy_placed_ok_at_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)) :=
  hC.memcpy (callerProg := lsProg_80 H)

/-! ## Block `82 → 80` `Chain::clone` callee bridges -/

theorem sc_chainClone_placed_ok_at_x [LibsignalPlacement] {H : LibsignalHooks}
    {α : Type} (spec : Spec α)
    (hcc : subroutine_ok (lsProg_82 H) (blkPl_82).base (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok (lsProg_80 H) (blkPl_82).base (withLsCodeLoaded lsmpl spec) :=
  CryptoVerification.E2E.Record.Serialization.SessionCloneAux.sc_chainClone_placed_ok_at_x spec hcc

/-! ## Stepping, `A.pool` transport, and panic-postcondition combinators -/

theorem sepWPpLsCl_pure_2nd_x {pl : MultiPlacement} {prog : Program}
    {ret : BitVec 64} {s : State} {φ : Prop} {P Q_post : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpLsCl pl prog ret s (P ∗ Q_post) Q Qp) :
    SepWPpLsCl pl prog ret s (P ∗ ⌜φ⌝ ∗ Q_post) Q Qp :=
  fun hcl => sepWPp_pure_2nd fun hφ => h hφ hcl

/-- Canonical panic postcondition for `subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl` on
`sessionCloneSpecX M A lim` (`onPanic = ⌜False⌝`). -/
abbrev scPanicPostX {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : SessionCloneGhost × M.σ) (Fr R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (sessionCloneSpecX M A lim).onPanic x s0 sf ∗ R)

theorem sc_panic_of_false_x {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : SessionCloneGhost × M.σ} {Fr R F : SepProp} {s0 : State}
    (sf : State) (_hpan : sf.status = .Panicked) :
    scPanicPostX A lim x Fr R s0 sf (⌜False⌝ ∗ F) := by
  intro hm
  rw [sepConj_assoc] at hm
  exact False.elim (not_satisfies_false_sepConj hm)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseXBudget

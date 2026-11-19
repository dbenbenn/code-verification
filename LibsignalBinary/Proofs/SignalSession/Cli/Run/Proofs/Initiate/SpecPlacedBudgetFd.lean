/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd -- proof-setup: allow-public-import

import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# File-Descriptor-Guarded Tight Budget Contract for `initiate`

Lifts `SpecPlacedBudget`'s tight `Compose.SemPlacedBudget.initSlotSpecPlaced` contract on block `521`
and caller blocks `i < 619` to `withPreFdsGe3Closed` via `AllocWithFds.withFds A` when
`lim.enforced = true`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudgetFd

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic SepProp
open CryptoVerification (IsLsBlockProg LibsignalPlacement lsmpl)
open CryptoVerification.E2E (PreKeyBundleFields UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem SlotCtx)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (AtInitEntryPlaced initProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (extract_withPreFdsGe3Closed withPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (initSlotSpecPlaced slotFramePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget
  (CliInitiateBudgetFits Stage3PlacedOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (SubsetA4InitCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget
  (cliInitiate_caller_tight_placed_ok cliInitiate_tight_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesEnvs ExistingStoreCalleesPlaced)

/-- Under `lim.enforced = true`, `SemPlacedBudget.slotFramePlaced (withFds A)` equals `⌜FdsGe3Closed s.fs⌝ ∗ SemPlacedBudget.slotFramePlaced A`. -/
theorem semSlotFramePlaced_withFds_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = true)
    (st : M.σ) (x : SlotCtx) (s : State) :
    slotFramePlaced (withFds A) lim st x s =
      (⌜FdsGe3Closed s.fs⌝ ∗ slotFramePlaced A lim st x s) := by
  unfold slotFramePlaced
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced
  rw [withFds_repAlloc, withFds_pool_enforced A henf st s]
  sep_ac_rfl

private theorem push_pure_slot6 {Q : Prop} {P1 Slot P3 P4 P5 P6 R : SepProp} {m : Memory}
    (hq : Q) (h : m ⊨ (P1 ∗ Slot ∗ P3 ∗ P4 ∗ P5 ∗ P6) ∗ R) :
    m ⊨ (P1 ∗ (⌜Q⌝ ∗ Slot) ∗ P3 ∗ P4 ∗ P5 ∗ P6) ∗ R := by
  have h' : m ⊨ ⌜Q⌝ ∗ ((P1 ∗ Slot ∗ P3 ∗ P4 ∗ P5 ∗ P6) ∗ R) := by
    rw [satisfies_pure_sepConj]
    exact ⟨hq, h⟩
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h'

private theorem drop_pure_10 {Q : Prop}
    {P1 P2 P3 P4 P5 P6 P7 P8 Pool P9 P10 R : SepProp} {m : Memory}
    (h : m ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8 ∗ (⌜Q⌝ ∗ Pool) ∗ P9 ∗ P10) ∗ R) :
    m ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8 ∗ Pool ∗ P9 ∗ P10) ∗ R := by
  have h' : m ⊨ ⌜Q⌝ ∗ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8 ∗ Pool ∗ P9 ∗ P10) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h
  rw [satisfies_pure_sepConj] at h'
  exact h'.2

/-- Weakens `subroutine_ok` from `SemPlacedBudget.initSlotSpecPlaced (withFds A)` to `withPreFdsGe3Closed (SemPlacedBudget.initSlotSpecPlaced A)` when `lim.enforced = true`. -/
theorem subroutine_ok_semInitSlot_preFd_of_withFds [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {InitEnv : InitGhost → List AllocEvent → Prop} {S : RunSem} {stk : Nat}
    (hok : subroutine_ok prog entry (initSlotSpecPlaced (withFds A) lim InitEnv S stk)) :
    subroutine_ok prog entry
      (withPreFdsGe3Closed (initSlotSpecPlaced A lim InitEnv S stk)) := by
  apply subroutine_ok.of_codeLoaded
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  obtain ⟨hfds0, hpre0⟩ := extract_withPreFdsGe3Closed hpre
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre0
  have hpre_fds : s0.mem ⊨
      (initSlotSpecPlaced (withFds A) lim InitEnv S stk).pre (x, st) s0 ∗ R := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [initSlotSpecPlaced] at hpre1 ⊢
    rw [semSlotFramePlaced_withFds_eq A henf st x.toSlotCtx s0]
    exact push_pure_slot6 hfds0 hpre1
  refine subroutine_ok.mono_outcome hok (x, st) R s0 hpc hrun hpre_fds hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hexc⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withPreFdsGe3Closed, initSlotSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    rw [withFds_repAlloc] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨g', hpost⟩
    refine ⟨g', ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨e, hpost⟩
    refine ⟨e, ?_⟩
    rw [withFds_pool_enforced A henf (M.stepEvents evs st) sf] at hpost
    exact drop_pure_10 hpost
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudgetFd

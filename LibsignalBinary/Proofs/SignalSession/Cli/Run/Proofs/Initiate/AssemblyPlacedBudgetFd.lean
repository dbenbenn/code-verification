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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd -- proof-setup: allow-public-import

import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# File-Descriptor-Guarded Budget-Threaded Assembly for `initiate`

Reduces the `FdsGe3Closed`-guarded `initSlotSpecPlaced` contract on block `521` and caller blocks
`i < 619` to `AssemblyPlacedBudget.cliInitiate_placed_ok_proof` instantiated at the pool-carried
allocator `AllocWithFds.withFds A` when `lim.enforced = true`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudgetFd

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic SepProp
open CryptoVerification (IsLsBlockProg LibsignalPlacement lsmpl)
open CryptoVerification.E2E (PreKeyBundleFields UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem SlotCtx)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtInitEntryPlaced initEntryPlaced initProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (extract_withPreFdsGe3Closed withPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget
  (CliInitiateBudgetFits Stage3PlacedOk cliInitiate_caller_placed_ok cliInitiate_placed_ok_proof)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (initSlotSpecPlaced slotFramePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (SubsetA4InitCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesEnvs ExistingStoreCalleesPlaced)

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

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudgetFd

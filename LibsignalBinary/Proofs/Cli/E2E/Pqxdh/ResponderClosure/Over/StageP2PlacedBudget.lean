/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Placed -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub5PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import ProofLib.SepLogic.WP.SyscallsMmap
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedLibcFreeStage1
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Placed Stage P2 Over-Path Call-Stack Bounds

Proves `retag*Store` and `A.atState` call-stack equalities together with `[LibsignalPlacement]`
stack-floor, 4K-equivalence, and `< 2 ^ 32` bounds for `stageP2OverCallStack` and
`stageP2OverV1CallStack` over `A : RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2PlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  IdentitySelfStoreSpec IdentityStoreSpec KyberPreKeyStoreSpec PreKeyStoreSpec
  SignedPreKeyStoreSpec
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  stageP2CallStack stageP2V1CallStack
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  p2_over_callStack_le_v1CallStack p2_over_callStack_le_v1CallStack_placed
  p2_over_callStack_lt_32 p2_over_pure_le_callStack p2_over_pure_le_callStack_placed
  p2_over_pure_le_v1CallStack p2_over_pure_le_v1CallStack_placed p2_over_v1CallStack_lt_32
  stageP2OverCallStack stageP2OverCallStack4K stageP2OverCallStack4K_eq
  stageP2OverPureAndErrStack stageP2OverV1CallStack stageP2OverV1CallStack4K
  stageP2OverV1CallStack4K_eq
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (retagSignedPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (retagKyberPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (retagPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (retagIdentitySelfStore)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  p2_over_pure_le_callStack_placed
  p2_over_pure_le_v1CallStack_placed
  p2_over_callStack_le_v1CallStack_placed
)

/-! ## Store-Retagging and `A.atState` Stack Equalities -/

/-! ## Placed Stack-Floor and 4K-Equivalence Lemmas -/

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2PlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable `VersionNegotiationPB` Field Error Push Paths (Block `325`)

Proves the budget-threaded relocatable `DecodeError::push` and wire-type mismatch blocks
(`+2156..+2348`) for `VersionNegotiationPB` fields (`public`, `version`, `max_version`, `params`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg decodeStateSavedAt protoPqRatchetStateAt sp_sub_1392_aligned)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (bv_sub_688_add_8 decodeStateErrFramePlaced scratch_680_fold_1_1 scratch_680_fold_8 scratch_680_split_1_1 scratch_680_split_8)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWPp_fold {prog : Program} {ret : BitVec 64} {s : State} {P T T' F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : SepWPp prog ret s (T' ∗ F) Q Qp oom) : SepWPp prog ret s P Q Qp oom := fun R hm hL => by
  rw [hf] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

private theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a : α, SepWPp prog ret s (P a) Q Qp oom) :
    SepWPp prog ret s (∃∗ a : α, P a) Q Qp oom := fun R hm hL => by
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hm⟩
  exact h a R hm hL

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudgetAux

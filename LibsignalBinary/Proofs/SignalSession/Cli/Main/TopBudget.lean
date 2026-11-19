/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top -- proof-setup: allow-public-import

/-!
# Budget-Threaded CLI `main` Entry Frame

Defines the budget-threaded entry separation-logic frame `mainFrame` under `RustCliAllocBudget M`
and its `symtab`-independence lemma `mainFrame_symtab`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.TopBudget

open Arm64 ProofLib
open Arm64.Process (bytesOfString)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (argvAt)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)

/-! ## Entry Frame -/

/-- Entry separation-logic frame for `main` under `RustCliAllocBudget M`. -/
@[expose] def mainFrame {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (stk : Nat) (Statics : SepProp) (i : Inputs) (s : State) : SepProp :=
  argvAt (s.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
    stackAt s.sp stk ∗ A.pool lim st s ∗ Statics

theorem mainFrame_symtab {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (stk : Nat) (Statics : SepProp) (i : Inputs) (s : State)
    (t : String → String → Option (BitVec 64)) :
    mainFrame A lim st stk Statics i { s with symtab := t } =
      mainFrame A lim st stk Statics i s := by
  unfold mainFrame
  have hpool : A.pool lim st { s with symtab := t } = A.pool lim st s :=
    A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  rw [hpool]
  rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Main.TopBudget

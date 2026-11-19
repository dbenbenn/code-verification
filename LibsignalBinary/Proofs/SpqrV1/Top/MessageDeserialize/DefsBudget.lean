/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.Defs

/-!
# Budget-Threaded Specification for `<Message>::deserialize`

Allocation-budget specification (`MsgDeserPostEvs`: `FreeOnlyEvs` on `.ok _`, `FreeOnlyEvs ∨
MsgDeserErrEnv` on `.error _`, with `FitsEnv ... MsgDeserErrEnv` required only on `.error _`)
for `<spqr::v1::chunked::states::Message>::deserialize`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
  (MsgDeserErrEnv)
open CryptoVerification.LibsignalSpqrV1
  (Message PolyApi)
open CryptoVerification.SpqrV1.Top.MessageDeserialize
  (MessageDeserializeCall messageDeserializeName messageDeserializeStackX messageResultAt)

/-- Postcondition allocator-event predicate for `<Message>::deserialize`:
    `FreeOnlyEvs` on `.ok _`, and `FreeOnlyEvs ∨ MsgDeserErrEnv` on `.error _`. -/
@[expose] def MsgDeserPostEvs {ε α : Type} (r : Except ε α)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ ((∃ err, r = .error err) ∧ MsgDeserErrEnv evs)

/-- Budget-threaded contract of `<spqr::v1::chunked::states::Message>::deserialize` (`0x5f434`,
    212 instructions) at `messageDeserializeStackX` (`MsgDeserPostEvs`, `onPanic = ⌜False⌝`,
    `onOom = ⌜False⌝`, `FitsEnv ... MsgDeserErrEnv` required only when `Message.deserialize`
    returns `.error _`). -/
@[expose] def messageDeserializeSpecX (P : PolyApi) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (MessageDeserializeCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg64 .x1 = x.epoch ∧
      s.readReg64 .x2 = x.fromPtr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 x.fromBytes.length ∧
      x.fromBytes.length < 2 ^ 63 ∧
      ((∃ err, Message.deserialize P x.epoch x.fromBytes = .error err) →
        FitsEnv M lim st MsgDeserErrEnv)⌝ ∗
    memRegion x.out 48 ∗
    (x.fromPtr ↦ₛ x.fromBytes) ∗
    A.pool lim st s ∗
    stackAt s.sp messageDeserializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧
        MsgDeserPostEvs (Message.deserialize P x.epoch x.fromBytes) evs⌝ ∗
      messageResultAt P x.out (Message.deserialize P x.epoch x.fromBytes) ∗
      (x.fromPtr ↦ₛ x.fromBytes) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp messageDeserializeStackX

end LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsBudget

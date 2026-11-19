/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Defs

/-!
# Budget-Threaded Specifications for `spqr::chain_from_version_negotiation`

`RustCliAllocBudget` specifications (`chainFromVersionNegotiationSpecX`, `chainFromVersionNegotiationSpecExt`)
allocating a single 32-byte `root_key` buffer on `Ok` and `evs = []` on `Err`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromVersionNegotiationEnv)
open CryptoVerification.LibsignalSpqrV1
  (HkdfFn chainFromVersionNegotiation)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
  (ChainFromVersionNegotiationCall chainFromVersionNegotiationName
   chainFromVersionNegotiationStackExt chainFromVersionNegotiationStackX
   chainResultAt versionNegotiationPBAt)

/-- Budget-threaded contract of `spqr::chain_from_version_negotiation` (`0x545e4`, 18 instructions)
at `chainFromVersionNegotiationStackX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
@[expose] def chainFromVersionNegotiationSpecX (hkdf : HkdfFn) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ChainFromVersionNegotiationCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧
      s.readReg64 .x0 = x.vPtr ∧
      FitsEnv M lim st (ChainFromVersionNegotiationEnv x.v)⌝ ∗
    memRegion x.out 88 ∗
    versionNegotiationPBAt A.repAlloc x.pin x.vPtr x.v ∗
    A.pool lim st s ∗
    stackAt s.sp chainFromVersionNegotiationStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ ChainFromVersionNegotiationEnv x.v evs⌝ ∗
      chainResultAt A.repAlloc x.out (chainFromVersionNegotiation hkdf x.v) ∗
      versionNegotiationPBAt A.repAlloc x.pin x.vPtr x.v ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp chainFromVersionNegotiationStackX

/-- Budget-threaded contract-backed (`chainFromVersionNegotiationStackExt`) spec of
`spqr::chain_from_version_negotiation` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
@[expose] def chainFromVersionNegotiationSpecExt (hkdf : HkdfFn) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ChainFromVersionNegotiationCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧
      s.readReg64 .x0 = x.vPtr ∧
      FitsEnv M lim st (ChainFromVersionNegotiationEnv x.v)⌝ ∗
    memRegion x.out 88 ∗
    versionNegotiationPBAt A.repAlloc x.pin x.vPtr x.v ∗
    A.pool lim st s ∗
    stackAt s.sp chainFromVersionNegotiationStackExt
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ ChainFromVersionNegotiationEnv x.v evs⌝ ∗
      chainResultAt A.repAlloc x.out (chainFromVersionNegotiation hkdf x.v) ∗
      versionNegotiationPBAt A.repAlloc x.pin x.vPtr x.v ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp chainFromVersionNegotiationStackExt

end LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.Common.InImageKit
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import ProofLib.Hoare.OutcomeSteps
import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.Common.SharedHelpers
public import ProofLib.BV
public import ProofLib.StdStartup.MuslStage1Init

/-!
# Stack-Parameterized and `.inImage` `<String as Clone>::clone` Proofs

Proves a unified stack- and state-invariant-parameterized correctness theorem
(`stringClone_withInv_fetches_ok`) for `<alloc::string::String as core::clone::Clone>::clone` and
specializes it to:
- `stringClone_4k_ok`: `stringCloneSpec A` on `tripleRatchetProgAtExt` from `4,096`-byte
  (`allocHookStack`) `memcpy`.
- `stringClone_inImage_4k_ok`: `(stringCloneSpec A).inImage img` on `tripleRatchetProgAtExt` carving
  `allocHookStack` out of `extHookStack` (`16,384` B) below the `48`-byte frame.
- `stringClone2x_inImage_of_allocContractsX`: `(stringCloneSpecWithStack A (2 * extHookStack)).inImage img`
  from `AllocContractsX`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.Common.StringCloneFlatX

open CryptoVerification.LibsignalTripleRatchet (extHookStack rustAllocSpecWithStack sessionMemcpyRegionSpec sessionShimSpec withStack)

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open ProofLib.ProgramReflection
open ProofLib.StdStartup
open ProofLib.StdStartup.Stage1Internal (step_str64_perm)
open CryptoVerification.RustHeap
  (RustAlloc vecHeader vecU8 vecU8At allocHookStack LayoutOk
   allocFailedEvent allocFailedIn rustAllocSpec)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalPublicApi (stringCloneHookName stringCloneSpec)

/-! ## Stack-Parameterized Spec -/

/-- `stringCloneSpec A` parameterized by callee stack budget `calleeStk` (`= stringCloneSpec A` at
    `extHookStack`, and definitionally equal to `Initiate.Stage1Lemmas.stringCloneAtStkSpec`). -/
@[expose] def stringCloneSpecWithStack (A : RustAlloc) (calleeStk : Nat) :
    Spec (BitVec 64 × BitVec 64 × VecGhost) where
  pre := fun (p, ret, g) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗ vecGhostAt A g p ∗ memRegion ret 24 ∗
      A.pool ∗ stackAt s.sp calleeStk
  post := fun (p, ret, g) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecGhostAt A g p ∗ vecU8 A ret g.bytes ∗ A.pool ∗
      stackAt s0.sp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end LibsignalBinary.Proofs.Common.StringCloneFlatX

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessage.Helpers
import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import

/-!
# Drop Glue Contract for `SignalMessage`

Defines `dropSignalMessageSpec` and lifts the exact-stack proof `dropSignalMessageRaw_ok` to
arbitrary stack budgets `32 + extHookStack ≤ stk ≤ 2 ^ 64`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

abbrev cliDropSignalMessageName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>"

structure DropSignalMessageGhost where
  a : BitVec 64
  g : SignalMessageGhost
  m : SignalMessage

@[expose] def dropSignalMessageSpec (A : RustAlloc) (stk : Nat) : Spec DropSignalMessageGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ signalMessageAt A x.g x.a x.m ∗ A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 120 ∗ A.pool ∗ stackAt s0.sp stk

end CryptoVerification.SignalSession.Cli.RunProofs

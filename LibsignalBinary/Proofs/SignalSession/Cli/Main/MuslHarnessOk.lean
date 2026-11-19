/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslElf -- proof-setup: allow-public-import

public section

set_option autoImplicit false

/-!
# `MuslHarness` Instance from musl Startup and Exit Proofs

Proves `Cli.MuslHarness` (`muslHarness_ok`) generically from musl startup (`MuslElf.musl_startup`)
and exit (`MuslExit.musl_exit_ofImage`) hypotheses together with `argvAt_eq` (`InitStack.argvAt =
Cli.argvAt`).
-/

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.MuslExit CryptoVerification.SignalSession.MuslStart
  CryptoVerification.SignalSession.MuslElf

theorem argvAt_eq (a : BitVec 64) (ss : List (List (BitVec 8))) :
    InitStack.argvAt a ss = argvAt a ss := by
  induction ss generalizing a with
  | nil => rfl
  | cons s ss ih =>
    simp only [InitStack.argvAt, argvAt, ih]
    rfl

theorem musl_exit_bound {e : BitVec 64} (h : e.toNat + 4 ≤ InitStack.stackBase) :
    e.toNat + 0xb74 ≤ 2 ^ 64 := by
  have := InitStack.stackBase_eq
  omega

end CryptoVerification.SignalSession.Cli

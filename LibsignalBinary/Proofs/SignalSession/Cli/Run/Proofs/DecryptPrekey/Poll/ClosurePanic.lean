/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SpecState -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2

/-!
# Poll Panic Postcondition Bridges

Lifts `P3P4.PanicOomProp`, `ResponderClosure.PanicOomProp`, and `GenP3.genP3S5PanicProp` across an
outer spatial frame into `((dpPollSpecState K stk').inImage img).onPanic`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.SignalSession.Cli.RunProofs

private theorem anyHeap_sepConj_left (Fr : SepProp) : anyHeap ∗ Fr ⊢ anyHeap :=
  entails_anyHeap (anyHeap ∗ Fr)

/-- Monotonicity adapter from `ResponderClosure.PanicOomProp s0` to `P3P4.PanicOomProp s0`. -/
theorem p3p4PanicOom_of_closPanicOom {s0 sf : State} {Pf : SepProp}
    (h : CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf Pf) :
    CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.PanicOomProp s0 sf Pf :=
  h

end CryptoVerification.SignalSession.Cli.RunProofs.Poll


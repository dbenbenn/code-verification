/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import ProofLib.SepLogic.WPp
public import ProofLib.GenDecodes

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.BundleRead.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit

/-!
# `read_file` Call-Site Lemma for `read_bundle::{closure#0}`

Isolates the `bl signal_session::io::read_file` call step at offset `+40` (`0x28`), preserving
`FsInv F0 T0`.
-/

theorem allocFailedIn_of_eq_trace {s0 s1 sf : State}
    (htr : s1.trace = s0.trace) (h : allocFailedIn s1 sf) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn at *
  rwa [htr] at h

end CryptoVerification.SignalSession.Cli.BundleRead.Helpers

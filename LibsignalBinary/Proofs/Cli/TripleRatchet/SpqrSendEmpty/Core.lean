/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Core -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `spqr::send` on Empty PQ State for the CLI Image

Proves `SpqrSendEmptyRunStmt` in the CLI image: `spqr::send::<Coins>` on an empty PQ ratchet state
returns `NotEnabled` without advancing the coins tape.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000

set_option maxHeartbeats 3200000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Address Arithmetic and Empty-State Proofs -/

end CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty

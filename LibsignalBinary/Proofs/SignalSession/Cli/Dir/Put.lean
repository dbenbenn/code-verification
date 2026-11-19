/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.HitAndLoop
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi

/-!
# Verification of `<signal_session::stores::Dir>::put::<alloc::string::String>`

Verifies `Dir::put::<String>` (`0x60`-byte frame) against `dirPutSpec A img stk`:
scans `Dir.changed` via `bcmp` (`DirGhost.setOrPush`), replacing the first matching entry's value
buffer and tail-deallocating the moved `name` on hit, or growing `Dir.changed` via `grow_one` when
full and appending `(name, bytes)` on miss.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Put

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SignalSession.Cli.Put.Helpers

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem mul_48_bv (n : BitVec 64) :
    ((n + (n <<< 1)) <<< 4) = 48#64 * n := by
  bv_bits

end CryptoVerification.SignalSession.Cli.Put

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Dev
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseSidFs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.StoreKit.Fs
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

public section

set_option autoImplicit false

/-!
# Binary Refinement Proof of `signal_session::address`

Proves `address_ok` against `(addressSpec A uuidTryParse resStack).inImage img` on `mProg img ext`,
discharging `ServiceId::parse_from_service_id_string` via `parseSid_okFs` and re-exporting
`MemrchrCall`, `memrchrIdx`, and `memrchrSpec`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPublicApi.StoreKit
open Address.Helpers

set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

private theorem bv_ult_of_lt' {i n : Nat} (hi : i < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 n) = true ∧
      (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans hi hn), Nat.mod_eq_of_lt hn]
  exact ⟨decide_eq_true hi, decide_eq_false (by omega)⟩

end CryptoVerification.SignalSession.Cli.MainHops

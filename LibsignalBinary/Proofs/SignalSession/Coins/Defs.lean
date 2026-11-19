/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- shake: keep -- proof-setup: allow-public-import
public import ProofLib.GenDecodes

/-!
# Coins Tape Predicates and `signal_session_coins_fill` Specification

Defines the two-cell randomness tape (`tapeAt2`, `tapeAfter2`), the image-static instances
`coinsAt` / `coinsAfter` at `signal_session::coins::{NEXT, LEFT}`, and the Hoare contracts
`coinsFillSpec` and `coinsFillAtSpec` for `signal_session_coins_fill(dst, len)`.
-/

public section

namespace CryptoVerification.SignalSession.Coins

open Arm64 ProofLib
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

/-! ## 1. The two-cell tape -/

/-- The tape with cursor cell `nx`, remaining-count cell `lf` and the remaining bytes `rest` at the
cursor `cur`. -/
@[expose] def tapeAt2 (nx lf cur : BitVec 64) (rest : List (BitVec 8)) : SepProp :=
  ⌜rest.length < 2 ^ 63⌝ ∗ (nx ↦₆₄ cur) ∗ (lf ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (cur ↦ₛ rest)

/-- The tape after `k` bytes were drawn: cursor `cur + k`, remaining count `rest.length - k`. The drawn
bytes stay owned (read-only for the program). -/
@[expose] def tapeAfter2 (nx lf cur : BitVec 64) (rest : List (BitVec 8)) (k : Nat) : SepProp :=
  (nx ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗ (lf ↦₆₄ BitVec.ofNat 64 (rest.length - k)) ∗ (cur ↦ₛ rest)

theorem tapeAt_eq_tapeAt2 (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest = tapeAt2 ctl (ctl + 8#64) cur rest :=
  rfl

theorem tapeAfter_eq_tapeAfter2 (ctl cur : BitVec 64) (rest : List (BitVec 8)) (k : Nat) :
    tapeAfter ctl cur rest k = tapeAfter2 ctl (ctl + 8#64) cur rest k :=
  rfl

/-- `tapeAfter2 nx lf cur rest 0` is the tape without the `< 2 ^ 63` side condition. -/
theorem tapeAfter2_zero_eq (nx lf cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAfter2 nx lf cur rest 0 =
      (nx ↦₆₄ cur) ∗ (lf ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (cur ↦ₛ rest) := by
  unfold tapeAfter2
  simp only [BitVec.add_zero, Nat.sub_zero]

/-! ## 2. The coins statics of the image loaded at `b` -/

/-- The function that draws from the coins tape. -/
abbrev coinsFillName : String := "signal_session_coins_fill"

/-! ## 3. The callee spec -/

end CryptoVerification.SignalSession.Coins

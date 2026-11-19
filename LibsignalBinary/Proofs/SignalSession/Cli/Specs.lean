/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Kits -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.CodeLayout

/-!
# Specifications for `signal_session::stores::{path, decimal}`

Defines function-level specifications (`pathSpec`, `decimalSpec`) for `signal_session::stores::path`
and `signal_session::stores::decimal` against the pure path and decimal-formatting operations of
`Cli/Kits.lean`:
- `path(dir: &str, name: &str) -> String`: sret in `x0`, `dir` in `(x1, x2)`, `name` in `(x3, x4)`,
  frame `0x70`, returning a fresh `String` with bytes `dir ++ "/" ++ name` (`pathOf dir name` when
  `dir ≠ []`) while preserving read-only or owned input slices (`ChainProofs.bytesAt ro`).
- `decimal(n: u32) -> String`: sret in `x0`, `n` in `w1`, frame `0x50` (recursion depth `≤ 10` for
  `u32`), returning a fresh `String` with ASCII `decimalText n`.
-/

public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## Symbol names and image offset checks -/

/-- `signal_session::stores::path`. -/
abbrev pathName : String := "libsignal_cli::stores::path"

/-- `signal_session::stores::decimal`. -/
abbrev decimalName : String := "libsignal_cli::stores::decimal"

/-- Symbol name of the CLI crate's `RawVecInner::reserve::do_reserve_and_handle` (`[local#9]`). -/
abbrev cliDoReserveName : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"

/-- Ghost arguments for `signal_session::stores::path`: two input slices (each read-only or owned
according to its `ro` flag), output sret pointer, and `do_reserve_and_handle` stack budget `resStack`. -/
structure PathGhost where
  dirA : BitVec 64
  dir : List (BitVec 8)
  dirRo : Bool
  nameA : BitVec 64
  name : List (BitVec 8)
  nameRo : Bool
  ret : BitVec 64

theorem utf8_slash : utf8 "/" = [0x2f#8] := by decide +kernel

/-- For non-empty `dir`, `pathOf dir name` equals `dir ++ [0x2f#8] ++ name`. -/
theorem pathOf_eq_path {dir : List (BitVec 8)} (h : dir ≠ []) (name : List (BitVec 8)) :
    pathOf dir name = dir ++ [0x2f#8] ++ name := by
  simp only [pathOf, h, ite_false, utf8_slash]

/-! ## `signal_session::stores::decimal` -/

structure DecimalGhost where
  n : BitVec 32
  ret : BitVec 64

end CryptoVerification.SignalSession.Cli

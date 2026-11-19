/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.RoLiterals -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

public section

set_option autoImplicit false

/-!
# Read-Only `.rodata` Literals of `signal-session` `main`

**Checked by Lean.**

Proves that the 8 read-only string literals in `mainLits img` (`"coins"` and the 7 nonempty `Dir`
paths of `Stores::open()`) hold automatically whenever `img.FrozenLoaded s` holds
(`mainLits_of_frozenLoaded`), eliminating `mainLits img` from `main` hop preconditions
(`sepWPp_mainFrame_mainLits`).
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

def mainLitList : List (Nat × List (BitVec 8)) :=
  (coinsLitOff.toNat, utf8 "coins") :: dirLits.map fun l => (l.1.toNat, utf8 l.2)

theorem foldr_lits_eq_roLits (base : BitVec 64) (ls : List (BitVec 64 × String)) :
    ls.foldr (fun l P => ((base + l.1) ↦ᵣ utf8 l.2) ∗ P) emp =
      roLits base (ls.map fun l => (l.1.toNat, utf8 l.2)) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => rw [List.foldr_cons, ih, List.map_cons, roLits_cons, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]

end CryptoVerification.SignalSession.Cli.MainHops

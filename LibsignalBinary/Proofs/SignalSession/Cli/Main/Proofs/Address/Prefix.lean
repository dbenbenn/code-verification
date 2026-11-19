/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

public section

set_option autoImplicit false

/-!
# Post-Sign and Sign-Handling Blocks for `signal_session::address` (`+180 .. +252`, `+288`)
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open Address.Helpers

namespace Address.Helpers

set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

@[expose] def postSignOff : BitVec 64 := 196#64

private theorem zext32_8_43_false {b : BitVec 8} (hne : (b == 43#8) = false) :
    ((b.zeroExtend 32 == 43#32) = false) ∧
    ((b.zeroExtend 32 - 43#32 == 0#32) = false) ∧
    ((b.zeroExtend 32 + (-43#32) == 0#32) = false) ∧
    ((b.zeroExtend 32 != 43#32) = true) := by
  clear * - hne; revert b hne; decide

private theorem bv_uge_3_of_ge3 {n : Nat} (h3 : 3 ≤ n) (hn : n < 2 ^ 64) :
    (3#64).ule (BitVec.ofNat 64 n) = true ∧
      (BitVec.ofNat 64 n).ult 3#64 = false := by
  simp only [BitVec.ule, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  exact ⟨decide_eq_true h3, decide_eq_false (by omega)⟩

/-! ### Post-sign device dispatch (`+196 .. +252` and `+288 -> +292`) -/

end Address.Helpers

end CryptoVerification.SignalSession.Cli.MainHops

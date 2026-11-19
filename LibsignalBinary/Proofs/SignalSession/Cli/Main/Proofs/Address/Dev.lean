/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Alloc -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Prefix
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

public section

set_option autoImplicit false

/-!
# Post-`ServiceId::parse_from_service_id_string` Tag Check & Device Dispatch (`+116 .. +176`)
-/

namespace CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

private theorem zext32_8_43_false {b : BitVec 8} (hne : (b == 43#8) = false) :
    ((b.zeroExtend 32 == 43#32) = false) ∧
    ((b.zeroExtend 32 - 43#32 == 0#32) = false) ∧
    ((b.zeroExtend 32 + (-43#32) == 0#32) = false) ∧
    ((b.zeroExtend 32 != 43#32) = true) := by
  clear * - hne; revert b hne; decide

private theorem zext32_8_45_false {b : BitVec 8} (hne : (b == 45#8) = false) :
    ((b.zeroExtend 32 == 45#32) = false) ∧
    ((b.zeroExtend 32 - 45#32 == 0#32) = false) ∧
    ((b.zeroExtend 32 + (-45#32) == 0#32) = false) ∧
    ((b.zeroExtend 32 != 45#32) = true) := by
  clear * - hne; revert b hne; decide

private theorem kindByte_zext32_beq2 (pni : Bool) :
    (((kindByte pni).zeroExtend 32 == 2#32) = false) ∧
    (((kindByte pni).zeroExtend 32 - 2#32 == 0#32) = false) ∧
    (((kindByte pni).zeroExtend 32 + (-2#32) == 0#32) = false) := by
  cases pni <;> decide

private theorem kindByte_zext32_bne2 (pni : Bool) :
    (((kindByte pni).zeroExtend 32 != 2#32) = true) ∧
    (((kindByte pni).zeroExtend 32 - 2#32 != 0#32) = true) := by
  cases pni <;> decide

private theorem bv_ne_zero_and_ne_one {n : Nat} (h2 : 2 ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false ∧
    (BitVec.ofNat 64 n == 1#64) = false ∧
    (BitVec.ofNat 64 n - 1#64 == 0#64) = false ∧
    (BitVec.ofNat 64 n + (-1#64) == 0#64) = false := by
  have h0 : BitVec.ofNat 64 n ≠ 0#64 := by
    intro h; have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht; change n = 0 at ht; omega
  have h1 : BitVec.ofNat 64 n ≠ 1#64 := by
    intro h; have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht; change n = 1 at ht; omega
  have hsub1 : BitVec.ofNat 64 n - 1#64 ≠ 0#64 := by
    intro h; exact h1 (by clear * - h; bv_omega)
  have hadd1 : BitVec.ofNat 64 n + (-1#64) ≠ 0#64 := by
    intro h; exact h1 (by clear * - h; bv_omega)
  exact ⟨beq_eq_false_iff_ne.mpr h0, beq_eq_false_iff_ne.mpr h1,
    beq_eq_false_iff_ne.mpr hsub1, beq_eq_false_iff_ne.mpr hadd1⟩

end CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers

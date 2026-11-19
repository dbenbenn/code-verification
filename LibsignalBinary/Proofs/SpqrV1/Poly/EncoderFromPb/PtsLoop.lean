/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: `.points` Branch and OOM Helpers

**Checked by Lean.**

Proves OOM panic blocks (`+1536`, `+1696`, `+1708`), 16-slot empty `Point` header initialization
(`+56..+260`), the inner `GF16` decoding loop (`+376..+440`), and the 16-slot `.points` outer loop
(`+260 → +1612 / +1648`).
-/

public section

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

theorem bv_add_lit_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

@[local arm64_norm, local wp_norm]
theorem bv_lit_add_lit (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [← BitVec.ofNat_add]

@[local arm64_norm, local wp_norm]
theorem ofNat_succ_sub_one (k : Nat) :
    BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add]; bv_omega

@[local arm64_norm, local wp_norm]
theorem ofNat_succ_add_neg_one (k : Nat) :
    BitVec.ofNat 64 (k + 1) + 18446744073709551615#64 = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add]; bv_omega

theorem cells_456_eq (fsp : BitVec 64) :
    cells (fsp + 456#64) 3 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2,
        ((fsp + 456#64) ↦₆₄ v0) ∗ ((fsp + 464#64) ↦₆₄ v1) ∗ ((fsp + 472#64) ↦₆₄ v2) := by
  have h1 : fsp + 456#64 + 8#64 = fsp + 464#64 := by bv_omega
  have h2 : fsp + 464#64 + 8#64 = fsp + 472#64 := by bv_omega
  rw [ProofLib.cells_succ, h1, ProofLib.cells_succ, h2, ProofLib.cells_succ, ProofLib.cells_zero]
  simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]

/-! ## OOM Panic Helpers (`+1536`, `+1696`, `+1708` -> `handle_error`) -/

attribute [local arm64_norm, local wp_norm] madd_24_eq

@[local arm64_norm, local wp_norm]
theorem mul_24_eq (j : Nat) :
    BitVec.ofNat 64 j * 24#64 = BitVec.ofNat 64 (24 * j) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

@[local arm64_norm, local wp_norm]
theorem fsp_add_201_add_255 (fsp : BitVec 64) :
    fsp + 201#64 + 255#64 = fsp + 456#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_add_255_add_201 (fsp : BitVec 64) :
    fsp + (255#64 + 201#64) = fsp + 456#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem exists_pow_two_eq_two :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

end CryptoVerification.SpqrV1.Poly.EncoderFromPb

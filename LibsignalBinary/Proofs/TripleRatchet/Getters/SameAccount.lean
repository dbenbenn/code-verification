/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<IdentityKey>::is_same_account`

Verifies `<libsignal_protocol::identity_key::IdentityKey>::is_same_account` against
`isSameAccountSpec` on `tripleRatchetProgAt` and under `[LibsignalPlacement]`, given
`<PublicKey as PartialEq>::eq`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

private theorem publicKey_beq_false_of_ne {ik1 ik2 : IdentityKey} (h : ik1 ≠ ik2) :
    (ik1.publicKey == ik2.publicKey) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  apply h
  cases ik1; cases ik2
  cases heq
  rfl

private def publicKeyEqMemSpec :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    memRegion (sp - 16#64) 16 ∗
    memRegion (sp - 16#64 - 48#64) 48
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    memRegion (sp - 16#64) 16 ∗
    memRegion (sp - 16#64 - 48#64) 48

private theorem stackAt_isSameAccount_split (sp : BitVec 64) :
    stackAt sp isSameAccountStack =
      memRegion (sp - 80#64 - 16#64) 16 ∗
      memRegion (sp - 80#64 - 16#64 - 48#64) 48 ∗
      memRegion (sp - 80#64) 32 ∗
      cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountStack]
  have h144 : sp - 80#64 - 16#64 - 48#64 = sp - 144#64 := by bv_omega
  have h96 : sp - 80#64 - 16#64 = sp - 96#64 := by bv_omega
  rw [h144, h96,
      show (80 + 64 : Nat) = 144 from rfl,
      show BitVec.ofNat 64 144 = 144#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 144#64) (n := 48) (k := 96)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 16) (k := 80)
        (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 32) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      (memRegion_cells (sp - 48#64) 6 (by decide) :
        memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]
  ac_rfl

end CryptoVerification.LibsignalTripleRatchet.Getters

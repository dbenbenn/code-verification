/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBase
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# `prost::encoding::message::merge::<Authenticator, &mut &[u8]>`

Proves the main loop induction (`auth_loop_ok`) and top-level contracts
(`auth_merge_ok_of_contracts`, `auth_merge_ok_of_fnAddr`, `AuthMergeOkX`) for
`prost::encoding::message::merge::<spqr::proto::pq_ratchet::Authenticator, &mut &[u8]>`
(`0x4df38`) against `Proto.mergeMessage ProtoAuthenticator.mergeField`.
-/

public section

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
/-- `Option<ProtoAuthenticator>` at `a` (48 bytes) with `BytesMergeCapOk cap bsLen` when `some`. -/
@[expose] def optAuthenticatorPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option ProtoAuthenticator → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some auth => authenticatorPBCapAt A a bsLen auth

@[simp]
theorem optAuthenticatorPBCapAt_none (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    optAuthenticatorPBCapAt A a bsLen none = (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40 := rfl

@[simp]
theorem optAuthenticatorPBCapAt_some (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (auth : ProtoAuthenticator) :
    optAuthenticatorPBCapAt A a bsLen (some auth) = authenticatorPBCapAt A a bsLen auth := rfl

theorem optAuthenticatorPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option ProtoAuthenticator) {m n : Nat} (hle : m ≤ n) :
    optAuthenticatorPBCapAt A a n opt ⊢ optAuthenticatorPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some auth => exact authenticatorPBCapAt_mono A a auth hle

theorem optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option ProtoAuthenticator) :
    optAuthenticatorPBCapAt A a n opt ⊢ optAuthenticatorPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some auth => exact authenticatorPBCapAt_entails_authenticatorPBAt A a n auth

theorem optAuthenticatorPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (opt : Option ProtoAuthenticator) :
    optAuthenticatorPBAt A a opt ⊢ ∃∗ opt' : Option ProtoAuthenticator, optAuthenticatorPBAt A a opt' :=
  Entails.sepExists_intro opt

theorem authenticatorPBAt_exists_entails_opt_exists (A : RustAlloc) (a : BitVec 64) :
    (∃∗ m' : ProtoAuthenticator, authenticatorPBAt A a m') ⊢
      ∃∗ opt' : Option ProtoAuthenticator, optAuthenticatorPBAt A a opt' :=
  Entails.sepExists_elim fun m' => Entails.sepExists_intro (P := optAuthenticatorPBAt A a) (some m')

theorem optAuthenticatorPBAt_entails_cap_of_lt32 (A : RustAlloc) (a : BitVec 64)
    {n : Nat} (hn : n < 2 ^ 32) (opt : Option ProtoAuthenticator) :
    optAuthenticatorPBAt A a opt ⊢ optAuthenticatorPBCapAt A a n opt := by
  cases opt with
  | none => exact Entails.refl _
  | some auth => exact authenticatorPBAt_entails_cap_of_lt32 A a hn auth

theorem memRegion_40_cells (a : BitVec 64) :
    memRegion (a + 8#64) 40 =
      (∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((a + 8#64) ↦₆₄ w5) ∗ ((a + 16#64) ↦₆₄ w4) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w2) ∗ ((a + 40#64) ↦₆₄ w1)) := by
  have s1 := ProofLib.memRegion_split (a + 8#64) 8 32 (by decide)
  have s2 := ProofLib.memRegion_split (a + 8#64 + 8#64) 8 24 (by decide)
  have s3 := ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64) 8 16 (by decide)
  have s4 := ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)
  rw [s1, s2, s3, s4,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]

/-- Folds default-initialized `Option::get_or_insert_with` cells into `authenticatorPBCapAt A a n default`. -/
theorem default_cells_entails_authenticatorPBCapAt (A : RustAlloc) (a : BitVec 64) (n : Nat) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ⊢
      authenticatorPBCapAt A a n (default : ProtoAuthenticator) := by
  refine Entails.trans ?_ (authenticatorPBPinnedAt_zero_entails_cap A 1#64 1#64 a n ⟨[], []⟩)
  unfold authenticatorPBPinnedAt vecU8At vecHeader
  have h1 : (a + 0x18#64) + 8#64 = a + 32#64 := by bv_omega
  have h2 : (a + 0x18#64) + 16#64 = a + 40#64 := by bv_omega
  have h0 : a + 0x18#64 = a + 24#64 := rfl
  rw [h1, h2, h0]
  dsimp only [List.length_nil]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Nat.le_refl,
    true_and, ↓reduceIte, sepConj_emp]
  have hp : (0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64 := ⟨by decide, by decide⟩
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Auth

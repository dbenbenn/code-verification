/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4d
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 4 (`EkSentCt1Received`, `+248`)

Top-level composition and `subroutine_ok` contract for `InnerState.ekSentCt1Received`.
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## Stack & Heap Helpers (`v4e_*`) -/

theorem v4e_optProtoPolyDecoderHeap_some_info (A : RustAlloc) (pb : ProtoPolynomialDecoder)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64) :
    v4b_optProtoPolyDecoderHeap A (some pb) d0 d8 d16 d24 d28 d32 ⊢
    ⌜d0.toNat < 2 ^ 63 ∧ d24 = pb.ptsNeeded⌝ ∗
    v4b_optProtoPolyDecoderHeap A (some pb) d0 d8 d16 d24 d28 d32 := by
  unfold v4b_optProtoPolyDecoderHeap
  apply Entails.pure_left; rintro ⟨h1, h2, h3, hle, hcap, h6, h7⟩
  have hd0 : d0.toNat < 2 ^ 63 := by omega
  exact Entails.pure_right ⟨hd0, h2⟩ (Entails.pure_right ⟨h1, h2, h3, hle, hcap, h6, h7⟩ (Entails.refl _))

theorem v4e_optProtoUcHeap_none_info (A : RustAlloc)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64) :
    v4b_optProtoUcHeap A none u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ⊢
    ⌜u0 = noneCap⌝ ∗ emp := by
  dsimp only [v4b_optProtoUcHeap]
  exact Entails.of_eq (sepConj_emp _).symm

theorem v4e_ucWordsAt_pbA_eq (pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64) :
    v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 =
      ((pbA + 96#64) ↦₆₄ u88) ∗ ((pbA + 104#64) ↦₆₄ u96) ∗
      (((pbA + 8#64) ↦₆₄ u0) ∗ ((pbA + 16#64) ↦₆₄ u8) ∗ ((pbA + 24#64) ↦₆₄ u16) ∗
       ((pbA + 32#64) ↦₆₄ u24) ∗ ((pbA + 40#64) ↦₆₄ u32) ∗ ((pbA + 48#64) ↦₆₄ u40) ∗
       ((pbA + 56#64) ↦₆₄ u48) ∗ ((pbA + 64#64) ↦₆₄ u56) ∗ ((pbA + 72#64) ↦₆₄ u64) ∗
       ((pbA + 80#64) ↦₆₄ u72) ∗ ((pbA + 88#64) ↦₆₄ u80)) := by
  unfold v4b_optProtoUcWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-! ## `+2228 -> +18368 -> +2308 -> ret` when `s.uc = some u` -/

theorem v4e_sepWPp_exists {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ x, SepWPp prog target_pc s (P x) post Qp) :
    SepWPp prog target_pc s (∃∗ x, P x) post Qp := by
  intro R' hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R' hmx

end CryptoVerification.SpqrV1.States.FromPb

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Varint
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Main Proof of Empty-State `spqr::recv`

Combines the preamble varint loops and `Ok`/`Err` tails to prove `spqrRecvEmpty_base_F`,
`spqrRecvEmpty_base`, and `spqrRecvEmpty_run'`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty
  (mr_cut' vecU8Tail vecArg_at_nil)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- The buffer tail of `msg.at A` (`vecU8At`). -/
@[expose] def msgHeaderTail (A : RustAlloc) (msg : VecArg) : SepProp :=
  if msg.cap = 0 then emp
  else A.live msg.ptr msg.cap.toNat 1 ∗ (msg.ptr ↦ₛ msg.bytes) ∗
    memRegion (msg.ptr + BitVec.ofNat 64 msg.bytes.length) (msg.cap.toNat - msg.bytes.length)

theorem msg_expose_hdr (A : RustAlloc) (msg : VecArg) :
    msg.at A ⊢
      ⌜msg.bytes.length < 2 ^ 63⌝ ∗
      (msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
      ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
      ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
      msgHeaderTail A msg := by
  have h1 : msg.at A =
      ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
      ((msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
        ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
        msgHeaderTail A msg) := by
    simp only [VecArg.at, vecU8At, vecHeader, msgHeaderTail]
    ac_rfl
  rw [h1]
  refine Entails.pure_left fun hp => ?_
  have hlt : msg.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp.1 hp.2.1
  refine Entails.pure_right hlt ?_
  rw [show ((msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
        ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
        ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
        msgHeaderTail A msg) =
      ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
      ((msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
        ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
        msgHeaderTail A msg) by ac_rfl]
  exact Entails.pure_right hp (Entails.refl _)

theorem msg_unexpose_hdr (A : RustAlloc) (msg : VecArg) :
    ((msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
      ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
      ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
      msgHeaderTail A msg) ⊢ msg.at A := by
  simp only [VecArg.at, vecU8At, vecHeader, msgHeaderTail, sepConj_assoc]
  exact Entails.refl _

theorem spqrRecvEmpty_nil : spqrRecvEmpty [] = .ok ([], none) := rfl

theorem spqrRecvEmpty_singleton (v : BitVec 8) : spqrRecvEmpty [v] = .error false := rfl

theorem spqrRecvEmpty_cons_cons (v b : BitVec 8) (rest : List (BitVec 8)) :
    spqrRecvEmpty (v :: b :: rest) =
      match spqrVarintAux 0 0#64 (b :: rest) with
      | none => .error false
      | some (epoch, rest1) =>
        if epoch == 0#64 then .error false
        else
          match spqrDecodeVarint rest1 with
          | none => .error false
          | some (index, _) => if index.toNat < 2 ^ 32 then .ok ([], none) else .error false := by
  change (if (match spqrVarintAux 0 0#64 (b :: rest) with
    | none => none
    | some (epoch, rest1) =>
      if epoch = 0#64 then none
      else match spqrDecodeVarint rest1 with
        | none => none
        | some (index, rest2) =>
          if index.toNat < 2 ^ 32 then some ({ version := v, epoch := epoch, index := index.setWidth 32, remaining := rest2 } : MsgPreamble)
          else none).isSome = true then Except.ok ([], none) else Except.error false) = _
  cases spqrVarintAux 0 0#64 (b :: rest) with
  | none => rfl
  | some p =>
    rcases p with ⟨epoch, rest1⟩
    dsimp only
    by_cases he : epoch = 0#64
    · subst he; rfl
    · have hef : (epoch == 0#64) = false := beq_false_of_ne he
      simp only [he, hef, ↓reduceIte]
      cases spqrDecodeVarint rest1 with
      | none => rfl
      | some q =>
        rcases q with ⟨index, rest2⟩
        dsimp only
        by_cases hi : index.toNat < 2 ^ 32
        · simp only [hi, ↓reduceIte]; rfl
        · simp only [hi, ↓reduceIte]; rfl

theorem msg_nil_of_len_zero {bs : List (BitVec 8)} (hlt : bs.length < 2 ^ 63)
    (h0 : BitVec.ofNat 64 bs.length = 0#64) : bs = [] := by
  have hlen0 : bs.length = 0 := by bv_omega
  exact List.eq_nil_of_length_eq_zero hlen0

theorem msg_singleton_of_len_one {bs : List (BitVec 8)} (hlt : bs.length < 2 ^ 63)
    (h1 : BitVec.ofNat 64 bs.length = 1#64) : ∃ v, bs = [v] := by
  have hlen1 : bs.length = 1 := by bv_omega
  cases bs with
  | nil => simp at hlen1
  | cons v rest =>
    simp at hlen1
    exact ⟨v, congrArg (v :: ·) hlen1⟩

theorem msg_cons_cons_of_len_ge_two {bs : List (BitVec 8)} (hlt : bs.length < 2 ^ 63)
    (h0 : ¬BitVec.ofNat 64 bs.length = 0#64)
    (h1 : ¬BitVec.ofNat 64 bs.length = 1#64) :
    ∃ v b rest, bs = v :: b :: rest := by
  have hge2 : 2 ≤ bs.length := by bv_omega
  cases bs with
  | nil => simp at hge2
  | cons v rest1 =>
    cases rest1 with
    | nil => simp at hge2
    | cons b rest => exact ⟨v, b, rest, rfl⟩

end CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty

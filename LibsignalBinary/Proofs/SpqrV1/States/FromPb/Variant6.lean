/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6e
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6f
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 6 (`HeaderReceived`, `+1464`)

Assembles the top-level theorem `states_from_pb_headerReceived_1464` for
`InnerState.headerReceived` at jump-table offset `+1464` (`0x5a65c`).
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff v6hr_stagingSlotsPre v6hr_stagingSlotsPost v6hr_decWordsAt v6hr_stackRest10000 v6hr_decHeap epilogueStackSlots epilogueStackGaps epilogueOutFull resultChunkedStatesAt statesFromPbSavedCells vecU8Payload
theorem v6hr_sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp) :
    SepWPp prog ret s (∃∗ x : α, P x) Q Qp := by
  intro R hsat hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hsat
  rcases hsat with ⟨x, hsat⟩
  exact h x R hsat hL

theorem v6hr_sepWP_pure_left {φ : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P Rest : SepProp} {Q : State → SepProp → Prop}
    (h : φ → SepWP prog ret s (P ∗ Rest) Q) :
    SepWP prog ret s ((⌜φ⌝ ∗ P) ∗ Rest) Q := by
  rw [sepConj_assoc]; exact ProofLib.SepWP.pure_elim h

theorem v6hr_sepWPp_pure_left {φ : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P ∗ Rest) Q Qp) :
    SepWPp prog ret s ((⌜φ⌝ ∗ P) ∗ Rest) Q Qp := by
  rw [sepConj_assoc]; exact SepWPp.pure_left h

theorem v6hr_sepWPp_to_sat {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P R : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf)) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R' hm hL
  rcases hout with hret | ⟨hpan, Pf, hmf, hent⟩ | hoom
  · exact ⟨sf, hsteps, Or.inl hret⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, Pf, hmf, fun hsat => Satisfies.mono (sepConj_mono_left hent) hsat⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem v6hr_sepWPp_post_reassoc {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P1 P2 : SepProp} (heq : P1 = P2)
    (h : SepWPp prog ret s P
      (fun sf Pf => (Pf ⊢ P1) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf)) :
    SepWPp prog ret s P
      (fun sf Pf => (Pf ⊢ P2) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  rwa [heq] at h

theorem v6hr_uc_auth_none_unpack' (A : RustAlloc) (pbA : BitVec 64)
    (hdr : List (BitVec 8)) (epoch : BitVec 64) :
    optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64)
      (some { hdr := hdr, auth := none, epoch := epoch }) ⊢
      ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
      ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w56 : BitVec 64,
      ∃∗ w64 : BitVec 64, ∃∗ w72 : BitVec 64,
        ⌜hdr.length ≤ c0.toNat ∧ c0.toNat < 2 ^ 63⌝ ∗
        vecCapPtrDealloc A c0 p0 ∗
        ((pbA + 8#64) ↦₆₄ c0) ∗ ((pbA + 16#64) ↦₆₄ p0) ∗
        ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
        ((pbA + 32#64) ↦₆₄ noneCap) ∗
        ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗
        ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
        ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ epoch) := by
  refine Entails.trans (v6hr_uc_some_auth_none_unpack A pbA hdr epoch) ?_
  apply Entails.sepExists_elim; intro c0; apply Entails.sepExists_right c0
  apply Entails.sepExists_elim; intro p0; apply Entails.sepExists_right p0
  apply Entails.sepExists_elim; intro w40; apply Entails.sepExists_right w40
  apply Entails.sepExists_elim; intro w48; apply Entails.sepExists_right w48
  apply Entails.sepExists_elim; intro w56; apply Entails.sepExists_right w56
  apply Entails.sepExists_elim; intro w64; apply Entails.sepExists_right w64
  apply Entails.sepExists_elim; intro w72; apply Entails.sepExists_right w72
  have hd : vecU8Payload A c0 p0 hdr ⊢
      ⌜hdr.length ≤ c0.toNat ∧ c0.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A c0 p0 :=
    Entails.trans (v6hr_vecU8Payload_cap_lt A c0 p0 hdr)
      (sepConj_mono_right (v6hr_vecU8Payload_entails_vecCapPtrDealloc A c0 p0 hdr))
  refine Entails.trans
    (Entails.of_eq (show _ =
      vecU8Payload A c0 p0 hdr ∗
      (((pbA + 8#64) ↦₆₄ c0) ∗ ((pbA + 16#64) ↦₆₄ p0) ∗
       ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((pbA + 32#64) ↦₆₄ noneCap) ∗
       ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗
       ((pbA + 64#64) ↦₆₄ w64) ∗ ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ epoch)) by ac_rfl))
    (Entails.trans (sepConj_mono_left hd) (Entails.of_eq (by ac_rfl)))

theorem v6hr_uc_auth_some_unpack' (A : RustAlloc) (pbA : BitVec 64)
    (hdr : List (BitVec 8)) (authPb : ProtoAuthenticator) (epoch : BitVec 64) :
    optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64)
      (some { hdr := hdr, auth := some authPb, epoch := epoch }) ⊢
      ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
      ∃∗ c1 : BitVec 64, ∃∗ p1 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ p2 : BitVec 64,
        ⌜(hdr.length ≤ c0.toNat ∧ c0.toNat < 2 ^ 63) ∧
         (authPb.rootKey.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63)⌝ ∗
        vecU8Payload A c0 p0 hdr ∗
        vecU8Payload A c1 p1 authPb.rootKey ∗
        vecU8Payload A c2 p2 authPb.macKey ∗
        ((pbA + 8#64) ↦₆₄ c0) ∗ ((pbA + 16#64) ↦₆₄ p0) ∗
        ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
        ((pbA + 32#64) ↦₆₄ c1) ∗ ((pbA + 40#64) ↦₆₄ p1) ∗
        ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 authPb.rootKey.length) ∗
        ((pbA + 56#64) ↦₆₄ c2) ∗ ((pbA + 64#64) ↦₆₄ p2) ∗
        ((pbA + 72#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
        ((pbA + 80#64) ↦₆₄ epoch) := by
  refine Entails.trans (v6hr_uc_some_auth_some_unpack A pbA hdr authPb epoch) ?_
  apply Entails.sepExists_elim; intro c0; apply Entails.sepExists_right c0
  apply Entails.sepExists_elim; intro p0; apply Entails.sepExists_right p0
  apply Entails.sepExists_elim; intro c1; apply Entails.sepExists_right c1
  apply Entails.sepExists_elim; intro p1; apply Entails.sepExists_right p1
  apply Entails.sepExists_elim; intro c2; apply Entails.sepExists_right c2
  apply Entails.sepExists_elim; intro p2; apply Entails.sepExists_right p2
  refine Entails.trans
    (Entails.of_eq (show _ =
      vecU8Payload A c0 p0 hdr ∗ vecU8Payload A c1 p1 authPb.rootKey ∗
      (vecU8Payload A c2 p2 authPb.macKey ∗
       ((pbA + 8#64) ↦₆₄ c0) ∗ ((pbA + 16#64) ↦₆₄ p0) ∗
       ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
       ((pbA + 32#64) ↦₆₄ c1) ∗ ((pbA + 40#64) ↦₆₄ p1) ∗
       ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 authPb.rootKey.length) ∗
       ((pbA + 56#64) ↦₆₄ c2) ∗ ((pbA + 64#64) ↦₆₄ p2) ∗
       ((pbA + 72#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
       ((pbA + 80#64) ↦₆₄ epoch)) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono (v6hr_vecU8Payload_cap_lt A c0 p0 hdr)
      (sepConj_mono_left (v6hr_vecU8Payload_cap_lt A c1 p1 authPb.rootKey))) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hc0
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜authPb.rootKey.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63⌝ ∗
      (vecU8Payload A c0 p0 hdr ∗ vecU8Payload A c1 p1 authPb.rootKey ∗
       vecU8Payload A c2 p2 authPb.macKey ∗
       ((pbA + 8#64) ↦₆₄ c0) ∗ ((pbA + 16#64) ↦₆₄ p0) ∗
       ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
       ((pbA + 32#64) ↦₆₄ c1) ∗ ((pbA + 40#64) ↦₆₄ p1) ∗
       ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 authPb.rootKey.length) ∗
       ((pbA + 56#64) ↦₆₄ c2) ∗ ((pbA + 64#64) ↦₆₄ p2) ∗
       ((pbA + 72#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
       ((pbA + 80#64) ↦₆₄ epoch)) by ac_rfl)) ?_
  apply Entails.pure_left; intro hc1
  exact Entails.pure_right ⟨hc0, hc1⟩ (Entails.of_eq (by ac_rfl))

end CryptoVerification.SpqrV1.States.FromPb

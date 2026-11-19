/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6d -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6e
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 6 (`HeaderReceived`, `+1464`) — Part F

Error exits (`+10324`, `+10316`), `Ok` epilogue composition (`+10000 -> ret`), `Authenticator`
key-clone phase (`+3760 -> +9936`), and decoder-branch exit tails (`+9936 -> ret`) for
`InnerState.headerReceived`.
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

theorem v6hr_decHeap_w0_lt (A : RustAlloc) (dec : PolyDecoder) (dw : v6hr_DecWords) :
    v6hr_decHeap A dec dw ⊢
      ⌜dw.g0.w0.toNat < 2 ^ 63⌝ ∗ v6hr_decHeap A dec dw := by
  unfold v6hr_decHeap
  apply Entails.pure_left; rintro ⟨h1, h2, hw0, h4, h5⟩
  exact Entails.pure_right hw0 (Entails.pure_right ⟨h1, h2, hw0, h4, h5⟩ (Entails.refl _))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff v6hr_stagingSlotsPre v6hr_stagingSlotsPost v6hr_decWordsAt v6hr_stackRest10000 v6hr_decHeap epilogueStackSlots epilogueStackGaps epilogueOutFull resultChunkedStatesAt statesFromPbSavedCells vecU8Payload
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



/-! ## 1. Exit, Epilogue, and Clone Glue for `HeaderReceived` -/

theorem v6hr_sepWPp_bind {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q1 Q2 Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q1 Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q1 sm Pm →
      SepWPp prog ret sm Pm Q2 Qp) :
    SepWPp prog ret s P Q2 Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := h1 R hm hL
  rcases hout with ⟨hpcm, hrunm, Pm, hmm, hQ1⟩ | hpan
  · obtain ⟨sf, hsteps', hout'⟩ := h2 sm Pm hpcm hrunm hQ1 R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

theorem v6hr_vecU8Payload_cap_lt (A : RustAlloc) (c p : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Payload A c p bs ⊢ ⌜bs.length ≤ c.toNat ∧ c.toNat < 2 ^ 63⌝ ∗ vecU8Payload A c p bs := by
  unfold vecU8Payload
  apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  exact Entails.pure_right ⟨h1, h2⟩ (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))

theorem v6hr_ofNat_len_beq_64_false {n : Nat} {c0 : BitVec 64}
    (hne : n ≠ 64) (hle : n ≤ c0.toNat) (hc0 : c0.toNat < 2 ^ 63) :
    (BitVec.ofNat 64 n == 64#64) = false := by
  apply beq_false_of_ne
  intro h
  apply hne
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  exact h1

end CryptoVerification.SpqrV1.States.FromPb


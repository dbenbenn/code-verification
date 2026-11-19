/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Layout -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Blocks
import ProofLib.SepLogic.WPp

/-!
# Symbolic Execution of `get_pre_key::{closure#0}`

Proves `pkGetPollInner_ok` against `pkGetPollInnerSpec` by composing the prologue, `decimal`,
`Dir::get`, and the error, missing-key, and `PreKeyRecord::deserialize` branches.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CliPkGetPollNorm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWP_peek_err_tag {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {e : SignalProtocolError} {d0 d1 d2 d3 d4 d5 d6 : BitVec 64}
    {Rest : SepProp} {Q : State → SepProp → Prop} {P : SepProp}
    (heq : P = pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗ Rest)
    (h : d0 = errTag → SepWP prog ret s P Q) :
    SepWP prog ret s P Q := by
  subst heq
  have hent :
      pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗ Rest ⊢
        ⌜d0 = errTag⌝ ∗ (pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗ Rest) := by
    dsimp only [pkDecPayload]
    apply Entails.pure_left; rintro ⟨he, rfl, hd1⟩
    exact Entails.pure_right rfl (Entails.pure_right ⟨he, rfl, hd1⟩ (Entails.refl _))
  exact SepWP.weaken_pre hent (SepWP.pure_elim h)

private theorem sepWP_peek_ok_hd0 {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {rec : PreKeyRecord} {d0 d1 d2 d3 d4 d5 d6 : BitVec 64}
    {Rest : SepProp} {Q : State → SepProp → Prop} {P : SepProp}
    (heq : P = pkDecPayload A (.ok rec) d0 d1 d2 d3 d4 d5 d6 ∗ Rest)
    (h : d0 + 1#64 ≠ 0#64 → SepWP prog ret s P Q) :
    SepWP prog ret s P Q := by
  subst heq
  have hent :
      pkDecPayload A (.ok rec) d0 d1 d2 d3 d4 d5 d6 ∗ Rest ⊢
        ⌜d0 + 1#64 ≠ 0#64⌝ ∗ (pkDecPayload A (.ok rec) d0 d1 d2 d3 d4 d5 d6 ∗ Rest) := by
    dsimp only [pkDecPayload]
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hφ
    exact Entails.pure_right hφ.1 (Entails.pure_right hφ (Entails.refl _))
  exact SepWP.weaken_pre hent (SepWP.pure_elim h)

private theorem sepWPp_exists_right {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Rest : SepProp} {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (Rest ∗ P a) Q Qp) :
    SepWPp prog ret s (Rest ∗ (∃∗ a, P a)) Q Qp := by
  rw [sepExists_sepConj_right]
  exact SepWPp.exists_elim h

private theorem sepWPp_exists_mid {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {L R : SepProp} {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (L ∗ (P a ∗ R)) Q Qp) :
    SepWPp prog ret s (L ∗ ((∃∗ a, P a) ∗ R)) Q Qp := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  exact SepWPp.exists_elim h

end CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers

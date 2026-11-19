/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Fetch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open CryptoVerification.LibsignalPublicApi.StoreSession

theorem w0_low_byte_zero {v : BitVec 64} (h : v.setWidth 32 = 0#32) :
    (v.setWidth 32).setWidth 8 = 0#8 ∧
      v.setWidth 8 = 0#8 ∧
      BitVec.extractLsb' 0 8 (v.setWidth 32) = 0#8 := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_bits

theorem clamp_b31_eq_bfi (b31 : BitVec 8) :
    ((64#8) ||| (b31 &&& 63#8)) = ((b31 &&& 0x7f#8) ||| 0x40#8) := by
  bv_bits

theorem initFreshRecAt_eq_fsp (fsp : BitVec 64) :
    initFreshRecAt fsp =
      ((fsp + 296#64) ↦₆₄ 0#64) ∗ ((fsp + 304#64) ↦₆₄ 8#64) ∗
      ((fsp + 312#64) ↦₆₄ 0#64) ∗ ((fsp + 320#64) ↦₆₄ (0#64 - 1#64)) :=
  rfl

theorem pointsToBytes_ends (a : BitVec 64) (b0 b31 : BitVec 8) (mid : List (BitVec 8))
    (hmid : mid.length = 30) :
    (a ↦ₛ ([b0] ++ mid ++ [b31])) =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ mid) ∗ ((a + 31#64) ↦₈ b31) := by
  have hb31 : ∀ p : BitVec 64, (p ↦ₛ [b31]) = (p ↦₈ b31) := fun p => by
    rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have hb0 : (a ↦ₛ ([b0] ++ mid)) = (a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ mid) := by
    simp only [List.singleton_append, pointsToBytes_cons]
  rw [pointsToBytes_append, hb0, hb31]
  have hlen : ([b0] ++ mid).length = 31 := by simp [hmid]
  rw [hlen, sepConj_assoc]

theorem sepWP_drop_left {prog : Program} {tgt : BitVec 64} {s : State}
    {cell P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog tgt s P post oom) :
    SepWP prog tgt s (cell ∗ P) post oom :=
  SepWP.weaken_pre_frame (fun _ hm => Satisfies.of_sep_right (by rwa [sepConj_assoc] at hm)) h

theorem sepWPp_drop_left {prog : Program} {tgt : BitVec 64} {s : State}
    {cell P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog tgt s P Q Qp oom) :
    SepWPp prog tgt s (cell ∗ P) Q Qp oom := fun R hm hL =>
  h R (Satisfies.of_sep_right (by rwa [sepConj_assoc] at hm)) hL

theorem sepWPp_with_rodata {prog : Program} {ret : BitVec 64} {s : State}
    {P R0 : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : ∀ Q0, s.mem ⊨ Q0 → s.mem ⊨ R0 ∗ Q0)
    (h : SepWPp prog ret s (R0 ∗ P) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := fun R hm hL =>
  h R (by rw [sepConj_assoc]; exact hro (P ∗ R) hm) hL

theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (himp : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := fun R hm hL =>
  h R (Arm64.Satisfies.mono (sepConj_mono_left himp) hm) hL

theorem sepWPp_pure_left {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom := fun R hm hL => by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a : α, SepWPp prog ret s (P a) Q Qp oom) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp oom :=
  SepWPp.exists_elim h

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas


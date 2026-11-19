/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFill -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy

/-!
# Stage 3 Call Combinators, Relative Targets, and Stack Split Helpers

Provides `SepWPp` stepping and call combinators (`s3_step_to`, `s3_call`, `s3_call_alloc`,
`s3_panic_at`), relative symbol target equivalences on `initProg img W`, stack sub-budget split
lemmas, and `CliExternsOk` counterparts (`Stage3Lemmas.Ext.*`).
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

/-! ## Function offset and relative call/hook targets -/

theorem kyberEncaps_row (W : CliHooks) :
    (Pqxdh.Initiator.kyberEncapsStub, CryptoVerification.E2E.kemEncapsHook W.Q.encaps) ∈
      cliHookTable W :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_of_getElem? (i := 8) rfl))

theorem sepWPp_conseq_oom {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (h : P ⊢ P') (hw : SepWPp prog ret s P' Q Qp Qoom) :
    SepWPp prog ret s P Q Qp Qoom := fun R hm hL =>
  hw R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem sepWPp_pure_elim_oom {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (hw : φ → SepWPp prog ret s P Q Qp Qoom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp Qoom := fun R hm hL => by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hw hm.1 R hm.2 hL

theorem sepWPp_exists_elim_oom {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (hw : ∀ a, SepWPp prog ret s (P a) Q Qp Qoom) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp Qoom := fun R hm hL => by
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hma⟩ := hm
  exact hw a R hma hL

theorem stackAt_sub_split_init (fsp : BitVec 64) {k m : Nat}
    (hle : k ≤ m) (hm : m ≤ 2 ^ 64) :
    stackAt fsp m = memRegion (fsp - BitVec.ofNat 64 m) (m - k) ∗ stackAt fsp k := by
  have heq : m = k + (m - k) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom fsp k (m - k) (by omega), ← heq]

theorem stk_sub_le_2pow64 {stk : Nat} (hstk64 : stk ≤ 2 ^ 63) :
    stk - cliInitiateFrame ≤ 2 ^ 64 := by omega

theorem stk_sub_le_2pow63 {stk : Nat} (hstk64 : stk ≤ 2 ^ 63) :
    stk - cliInitiateFrame ≤ 2 ^ 63 := by omega
theorem lay32 : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
theorem lay192 : LayoutOk 192 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
theorem lay1568 : LayoutOk 1568 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩

namespace Ext

end Ext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

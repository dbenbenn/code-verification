/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.E2E.Bin.OpenSegs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsPartyRoData
import LibsignalBinary.Proofs.E2E.Bin.SegCommon
import LibsignalBinary.Proofs.CodeLayout

public section

namespace CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Segment 3: `open_seg_keys` (`+0x080..+0x130`) -/

@[expose] def openShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝

theorem openShim_hookOk : HookOk hookNoop openShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  dsimp only [openShimSpec, hookNoop, retHook, id_eq] at hpre ⊢
  rw [emp_sepConj] at hpre
  rw [satisfies_pure_sepConj]
  exact ⟨⟨State.trace_setPC _ _, tpidrEl0_setPC_pre_open _ _⟩, hpre⟩

theorem role_nameBytes_length (r : Role) : r.nameBytes.length = 36 := by
  cases r <;> decide +kernel

theorem allocFailedIn_panicked {s0 s1 sf : State}
    (htr1 : s1.trace = s0.trace)
    (htr : sf.trace = s1.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 (Rust.panicked sf) ∧ s0.trace <+: (Rust.panicked sf).trace := by
  have htr' : sf.trace = s0.trace ++ [allocFailedEvent] := by rw [htr, htr1]
  have hpan_tr : (Rust.panicked sf).trace = sf.trace := rfl
  refine ⟨?_, ?_⟩
  · unfold allocFailedIn
    rw [hpan_tr, htr', List.drop_left]
    exact List.Mem.head []
  · rw [hpan_tr, htr']
    exact List.prefix_append s0.trace [allocFailedEvent]

theorem layoutOk_36_1 : LayoutOk 36 1 := by
  refine ⟨by decide, ⟨0, rfl⟩, by decide⟩

end CryptoVerification.E2E.Bin

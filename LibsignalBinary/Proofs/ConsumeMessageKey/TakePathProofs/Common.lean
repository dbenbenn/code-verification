/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout

/-!
# Shared Fetch and Hook Helpers for the `consume_message_key` Take Path
-/

public section

namespace CryptoVerification.LibsignalSession.TakePath

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

abbrev cmkSym : String :=
  "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"

abbrev cmkMemmoveSym : String := "memmove"

@[expose] def TakePathPlacedSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H → H cmkMemmoveSym = some hookMemmove → FindIndexPlacedOk H A →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.counter < x.ck.index →
      CmkTakeState_placed A x R s0 s →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s

set_option maxRecDepth 200000 in
theorem dealloc_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A H) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustDeallocSym)
      (rustDeallocSpec A) := by
  rcases hA with ⟨_, hdealloc, _, _, _, _⟩
  exact cmk_hook_ok_of_mem hdealloc

set_option maxRecDepth 200000 in
theorem memmove_placed_ok_at [LibsignalPlacement]
    {H : String → Option (State → State)} (hmemmove : H cmkMemmoveSym = some hookMemmove) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkMemmoveSym)
      libcMemmoveSpec :=
  cmk_hook_ok_of_mem ⟨hookMemmove, hmemmove, hookMemmove_ok⟩

end CryptoVerification.LibsignalSession.TakePath

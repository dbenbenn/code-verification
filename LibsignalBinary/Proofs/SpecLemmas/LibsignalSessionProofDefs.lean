/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalHmac
public import ProofLib.Hoare.LibcHooks
public import LibsignalBinary.Proofs.SpecLemmas.RustHeapAllocProofDefs

/-!
# Proof-Side `RatchetState::consume_message_key` Ghost State

Defines the machine-level ghost state (`ConsumeMessageKeyGhost`), stack budget (`cmkStack`),
and model projection (`ConsumeMessageKeyGhost.model`, `ConsumeMessageKeyGhost.touched`) for
`RatchetState::consume_message_key`.
-/

public section

namespace CryptoVerification.LibsignalSession
open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- Stack the method may use below `sp`: its 480-byte frame, the deepest callee chain
(`hmac_sha256` 480 + `new_from_slice` 544) and hook stacks, rounded up. -/
abbrev cmkStack : Nat := 8192

/-- Ghost of a cmk call: the session model's state and arguments, the ghost layout, and the
argument addresses. -/
structure ConsumeMessageKeyGhost where
  /-- `self: &mut RatchetState` (`x0`). -/
  self : BitVec 64
  G : RatchetGhost
  st : RatchetState
  /-- `their_ephemeral: &PublicKey` (`x1`, 32 bytes). -/
  their : PublicKey
  theirA : BitVec 64
  /-- `chain_key: ChainKey` (by value; passed as a pointer `x2` to a 36-byte caller copy that the
  callee owns and mutates). -/
  ck : ChainKey
  ckA : BitVec 64
  /-- `counter: u32` (`w3`). -/
  counter : BitVec 32
  /-- `original_message_type: CiphertextMessageType` (`w4`, `repr(u8)`). -/
  msgType : MessageType
  /-- The sret (`x8`, 88 bytes). -/
  ret : BitVec 64

/-- The session model's result and final state of the call. -/
@[expose] def ConsumeMessageKeyGhost.model (F : ShaState → List (BitVec 8) → ShaState) (x : ConsumeMessageKeyGhost) :
    Except SignalProtocolError MessageKeyGenerator × RatchetState :=
  (RatchetState.consumeMessageKey F x.their x.ck x.counter x.msgType).exec x.st

/-- The receiver chain a call may rewrite: on success, the chain of `their` (removing a stored
skipped key when `counter < index`, or storing skipped keys and advancing the chain key when
`counter ≥ index`); on an error result (missing chain, duplicated message, or counter too far in the
future), none. -/
@[expose] def ConsumeMessageKeyGhost.touched (F : ShaState → List (BitVec 8) → ShaState) (x : ConsumeMessageKeyGhost) : Option Nat :=
  match (x.model F).1 with
  | .ok _ => x.st.findReceiverChainIndex x.their
  | .error _ => none

end CryptoVerification.LibsignalSession

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Proofs.TripleRatchet.LibsignalTripleRatchetProst
public import LibsignalBinary.Proofs.ProtoCodecKat
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSpqr
public import Init.Data.String.Pattern.Basic
public import Init.Data.String.Pattern.String
public import Init.Data.String.Slice
public import Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetReprProofDefs

/-!
# Proof-Side Triple-Ratchet Ghost Structures and Empty-State Layout

Defines ghost call structures (`OtrFromGhost`, `OtrApplyGhost`, `TryFromGhost`) and the
empty-state `decode_state` contract (`decodeStateEmptySpec`).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet
open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

/-- `Result<Uuid, uuid::Error>`'s word 0 (a `u32`) for `Ok`: the niche `0xFFFFFFFF`; the UUID's 16
bytes follow at +4. -/
@[expose] def uuidOkTag : BitVec 32 := 0xFFFFFFFF#32

/-- Word 0 of `Err(uuid::Error(ErrorKind::ParseOther))` (the `u32` tag 6). -/
@[expose] def uuidErrParseOther : BitVec 32 := 6#32

/-- `PqRatchetState.chain = None`: the word @0x30 (`-1`). -/
@[expose] def pqChainNone : BitVec 64 := 0xFFFFFFFFFFFFFFFF#64

/-- `PqRatchetState.inner = None`: the word @0x80 (`-3`). -/
@[expose] def pqInnerNone : BitVec 64 := 0xFFFFFFFFFFFFFFFD#64

/-- The 352-byte `Result<PqRatchetState, spqr::Error>` at `r` that `decode_state` returns on an
empty state (`Ok` with `inner`, `version_negotiation` and `chain` all `None`). -/
@[expose] def decodeStateEmptyAt (r : BitVec 64) : SepProp :=
  (r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
    memRegion (r + 8#64) 40 ∗ ((r + 48#64) ↦₆₄ pqChainNone) ∗ memRegion (r + 56#64) 72 ∗
    ((r + 128#64) ↦₆₄ pqInnerNone) ∗ memRegion (r + 136#64) 216

/-- `spqr::decode_state(s = x0: &Vec<u8>)` (sret `x8`, 352 bytes) on an empty state only. -/
@[expose] def decodeStateEmptySpec (A : RustAlloc) : Spec (VecArg × BitVec 64) where
  pre := fun (st, ret) s =>
    ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x8 = ret ∧ st.bytes = []⌝ ∗ st.at A ∗
      memRegion ret 352 ∗ stackAt s.sp extHookStack
  post := fun (st, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ st.at A ∗ decodeStateEmptyAt ret ∗ stackAt s0.sp extHookStack

/-- Ghost of an `OTR::from_session_state` call. -/
structure OtrFromGhost where
  /-- `state: &mut SessionState` (`x0`). -/
  ss : BitVec 64
  G : SessionGhost
  st : SessionState (List (BitVec 8))
  /-- The sret (`x8`, 200 bytes). -/
  ret : BitVec 64

/-- The session-model result and final state. -/
@[expose] def OtrFromGhost.model (x : OtrFromGhost) :
    Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8))) ×
      SessionState (List (BitVec 8)) :=
  Mut.exec OutgoingTripleRatchet.fromSessionState x.st

/-- Ghost of an `OTR::apply_to_session_state` call. -/
structure OtrApplyGhost where
  /-- `self: OutgoingTripleRatchet` by value (`x0` = a caller copy the callee consumes). -/
  o : BitVec 64
  pqCap : BitVec 64
  pqPtr : BitVec 64
  ot : OutgoingTripleRatchet (List (BitVec 8))
  /-- `state: &mut SessionState` (`x1`). -/
  ss : BitVec 64
  G : SessionGhost
  st : SessionState (List (BitVec 8))

/-- Ghost of a parse call: the bytes (`x0`, `x1`) and the sret (`x8`, 120 bytes). -/
structure TryFromGhost where
  bytesA : BitVec 64
  bytes : List (BitVec 8)
  ret : BitVec 64

end CryptoVerification.LibsignalTripleRatchet

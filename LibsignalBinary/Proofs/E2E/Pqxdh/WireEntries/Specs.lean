/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.RecordX.ScopeP -- proof-setup: allow-public-import
public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E (partyAddressName partyIdentityKey)
abbrev sendWireName : String := "session_send_wire"
abbrev recvWireName : String := "session_recv_wire"
abbrev encodeRecord := Bin.encodeRecord
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.InMem.HashbrownBin (tableAllocSize sessionBucketStride
  sessionBucketValueOff
  identityBucketStride identityBucketValueOff table4At table4SingleAt identityBucketEntryAt)

/-! ## Symbol Names and Image Offsets -/

abbrev openPqxdhName              : String := "libsignal_pqxdh_e2e::open"
abbrev packPqxdhName              : String := "libsignal_pqxdh_e2e::pack"
abbrev closePqxdhName             : String := "libsignal_pqxdh_e2e::close"
abbrev remoteIdentityKeyBytesName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::remote_identity_key_bytes"
abbrev identityKeyPairTryFromName : String :=
  "<libsignal_protocol::identity_key::IdentityKeyPair as " ++
  "core::convert::TryFrom<libsignal_core::curve::PrivateKey>>::try_from"
abbrev noopWakerClonePqxdhName : String :=
  "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as " ++
  "core::ops::function::FnOnce<(*const (),)>>::call_once [local#3]"
abbrev noopWakerNoopPqxdhName : String :=
  "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#2} as " ++
  "core::ops::function::FnOnce<(*const (),)>>::call_once [local#3]"

abbrev openPqxdhOff              : BitVec 64 := 0x7602c#64
abbrev packPqxdhOff              : BitVec 64 := 0x76364#64
abbrev closePqxdhOff             : BitVec 64 := 0x76420#64
abbrev sendWireOff               : BitVec 64 := 0x78848#64
abbrev recvWireOff               : BitVec 64 := 0x786a0#64
abbrev remoteIdentityKeyBytesOff : BitVec 64 := 0x17c94#64
abbrev identityKeyPairTryFromOff : BitVec 64 := 0x287e8#64
abbrev noopWakerClonePqxdhOff    : BitVec 64 := 0x7738c#64
abbrev noopWakerNoopPqxdhOff     : BitVec 64 := 0x7739c#64

abbrev openPqxdhStack  : Nat := 0x40000 + 0x4b0
abbrev closePqxdhStack : Nat := 0x30000 + 0x330
abbrev packPqxdhStack  : Nat := 0x50 + allocHookStack
abbrev sendWireStack   : Nat := 0x280000
abbrev recvWireStack   : Nat := 0x280000

/-! ## Kernel-Checked Address and Data Guards -/

section AddrGuards
open ProofLib.ProgramReflection
set_option maxRecDepth 2000000

end AddrGuards

/-! ## `InMemIdentityKeyStore` and `Call` Layouts -/

structure CloseGhostP where
  callPtr      : BitVec 64
  role         : Role
  keyPairBytes : List (BitVec 8)
  regId        : BitVec 32
  sess         : Session (List (BitVec 8))

@[expose] def identityKeyDecodeAnySpec : Spec (BitVec 64 × BitVec 64 × IdentityKey) where
  pre := fun (ret, keyPtr, ik) s =>
    ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = keyPtr ∧ s.readReg64 .x1 = 33#64⌝ ∗
      (keyPtr ↦ₛ (0x05#8 :: ik.publicKey.bytes.toList)) ∗ memRegion ret 40 ∗ stackAt s.sp 0x60
  post := fun (ret, keyPtr, ik) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (keyPtr ↦ₛ (0x05#8 :: ik.publicKey.bytes.toList)) ∗
      (ret ↦₆₄ 0xfffffffffffffffe#64) ∗
        ((ret + 8#64) ↦ₛ ik.publicKey.bytes.toList) ∗ stackAt s0.sp 0x60

/-- Derive the 64-byte `IdentityKeyPair` representation (`pub[32] ++ clamped_priv[32]`) from a
36-byte `me` slice (`id_priv[32] ‖ reg_id:u32`). -/
@[expose] def meKeyPairBytes (pubKey : PubKeyFn) (meBytes : List (BitVec 8)) : List (BitVec 8) :=
  if h : (meBytes.take 32).length = 32 then
    let sk := Ratchet.clampScalar ⟨meBytes.take 32, h⟩
    (pubKey sk).toList ++ sk.toList
  else List.replicate 64 0#8

theorem meKeyPairBytes_length (pubKey : PubKeyFn) (meBytes : List (BitVec 8)) :
    (meKeyPairBytes pubKey meBytes).length = 64 := by
  unfold meKeyPairBytes
  split_ifs with h <;> simp

/-- Extract the 32-bit little-endian registration id from `me[32..36]`. -/
@[expose] def meRegId (meBytes : List (BitVec 8)) : BitVec 32 :=
  let b0 := meBytes.getD 32 0#8
  let b1 := meBytes.getD 33 0#8
  let b2 := meBytes.getD 34 0#8
  let b3 := meBytes.getD 35 0#8
  b3 ++ b2 ++ b1 ++ b0

structure OpenGhostP where
  outPtr     : BitVec 64
  who        : BitVec 32
  mePtr      : BitVec 64
  meBytes    : List (BitVec 8)
  statePtr   : BitVec 64
  stateBytes : List (BitVec 8)
  sess       : Session (List (BitVec 8))
  tlsInit    : Option (BitVec 64 × BitVec 64)

/-- Canonical encoding predicate for `SessionRecord::deserialize` (`0x16ed4`) in `open` under
`RecordX.DeserializeScopeP`. -/
@[expose] def RecordCanonical (stateBytes : List (BitVec 8)) (s : Session (List (BitVec 8))) : Prop :=
  stateBytes = encodeRecord ⟨some s⟩ ∧
    RecordX.DeserializeScopeP ⟨some s⟩ ∧ ∃ G, BinCanonSession G s

theorem recordCanonical_length_pos {bs : List (BitVec 8)} {s : Session (List (BitVec 8))}
    (h : RecordCanonical bs s) : 0 < bs.length := by
  rcases h with ⟨rfl, _⟩
  simp only [encodeRecord, Bin.encodeRecord, CryptoVerification.E2E.Record.encodeRecord,
    CryptoVerification.E2E.Record.msgField, CryptoVerification.E2E.Record.lenField,
    Option.map_some, List.length_append]
  have : 0 < (encodeKey 1 WireType.lengthDelimited).length := by decide
  omega

@[expose] def recordDeserializeOpenSpec (A : RustAlloc) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × Session (List (BitVec 8))) where
  pre := fun (ptr, bs, out, sess) st =>
    ⌜st.readReg64 .x0 = ptr ∧ (st.readReg64 .x1).toNat = bs.length ∧
      st.readReg64 .x8 = out ∧ RecordCanonical bs sess⌝ ∗
      (ptr ↦ₛ bs) ∗ memRegion out 0x170 ∗ A.pool ∗ stackAt st.sp recordDeserializeStack
  post := fun (ptr, bs, out, sess) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ bs) ∗
      (∃∗ G : SessionGhost, ⌜BinCanonSession G sess⌝ ∗
        sessionRecordAt A out ⟨0#64, 8#64, some G⟩ ⟨some sess⟩) ∗
      A.pool ∗ stackAt s0.sp recordDeserializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `CiphertextMessage` wire tag and inner serialized bytes for `session_send_wire`
(`pqxdh/src/lib.rs:403–407`):
- `SignalMessage sm` -> `(2#8, sm.serialized)` (`WIRE_WHISPER`),
- `PreKeySignalMessage psm` -> `(3#8, psm.serialized)` (`WIRE_PREKEY`). -/
@[expose] def unwrapWireCiphertext : CiphertextMessage → BitVec 8 × List (BitVec 8)
  | .signalMessage sm => (2#8, sm.serialized)
  | .preKeySignalMessage psm => (3#8, psm.serialized)

/-- 248-byte `Result<CiphertextMessage, SignalProtocolError>` at `ret`
(`sp + 0xf8` in `session_send_wire`):
- `.ok (.signalMessage sm)`: word 0 = `0x8000000000000000#64`, `sm` at `ret + 8`
  (`sm.serialized` at `ret + 0x30`),
- `.ok (.preKeySignalMessage psm)`: word 0 `w` with `w.toNat < 2 ^ 63`,
  `psm.serialized` at `ret + 0x80`,
- `.error _`: word 0 = `0xffffffffffffffff#64` (`errTag`). -/
def apiEncResultAtWire (A : RustAlloc) (ret : BitVec 64) :
    Except (ApiError AddrVal Unit) CiphertextMessage → SepProp
  | .ok (.signalMessage sm) =>
    (ret ↦₆₄ 0x8000000000000000#64) ∗
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (ret + 8#64) sm) ∗
      memRegion (ret + 128#64) 120
  | .ok (.preKeySignalMessage psm) =>
    (∃∗ w : BitVec 64, ⌜w.toNat < 2 ^ 63⌝ ∗ (ret ↦₆₄ w)) ∗ memRegion (ret + 8#64) 120 ∗
      (∃∗ serPtr : BitVec 64, boxU8At A (ret + 0x80#64) serPtr psm.serialized) ∗
      memRegion (ret + 0x90#64) 104 ∗ anyHeap
  | .error _ =>
    (ret ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (ret + 8#64) 240 ∗ anyHeap

/-! ## Top-Level Wire Entry Specifications (`sendWireSpec`, `recvWireSpec`, `recvWireRejectSpec`) -/

structure SendWireGhost where
  who        : BitVec 32
  aPtr       : BitVec 64
  meBytes    : List (BitVec 8)
  stateBytes : List (BitVec 8)
  sess       : Session (List (BitVec 8))
  ptextPtr   : BitVec 64
  ptextBytes : List (BitVec 8)
  cur        : BitVec 64
  rest       : List (BitVec 8)
  tlsInit    : Option (BitVec 64 × BitVec 64)

/-- Pure outcome of `session_send_wire`: encrypts `g.ptextBytes`, prepends the 1-byte wire tag
(`2` for `SignalMessage`, `3` for `PreKeySignalMessage`), and packs `(new_state, tag :: body)`. -/
@[expose] def evalSendWire (C : Crypto) (S : SpqrModel) (_uuidParse : UuidParser) (g : SendWireGhost) :
    Option (List (BitVec 8) × List (BitVec 8) × Nat) :=
  if g.aPtr = 0#64 then none
  else if g.ptextPtr = 0#64 ∧ g.ptextBytes.length ≠ 0 then none
  else
    match evalOpen g.who g.sess with
    | none => none
    | some (role, sess) =>
      let (res, calls) := messageEncrypt C protoSignalCodec S.spqr (serializeAddrVal)
        (inMemAnswers sess) g.ptextBytes role.peer.addrVal role.addrVal SystemTime.unixEpoch g.rest
      match res with
      | .ok cm =>
        let (tag, body) := unwrapWireCiphertext cm
        some (Record.encodeRecord ⟨some (storedSession sess calls)⟩,
          tag :: body, sendDraws S sess g.rest)
      | .error _ => none

structure RecvWireGhost where
  who        : BitVec 32
  aPtr       : BitVec 64
  meBytes    : List (BitVec 8)
  stateBytes : List (BitVec 8)
  sess       : Session (List (BitVec 8))
  wirePtr    : BitVec 64
  wireBytes  : List (BitVec 8)
  cur        : BitVec 64
  rest       : List (BitVec 8)
  tlsInit    : Option (BitVec 64 × BitVec 64)

/-- Pure outcome of `session_recv_wire`: requires `wireBytes = 2#8 :: body`, parses `body` as a
`SignalMessage`, decrypts it via `messageDecryptSignal`, and packs `(new_state, ptBytes)`. -/
@[expose] def evalRecvWire (C : Crypto) (S : SpqrModel) (_uuidParse : UuidParser) (g : RecvWireGhost) :
    Option (List (BitVec 8) × List (BitVec 8) × Nat) :=
  if g.aPtr = 0#64 then none
  else if g.wirePtr = 0#64 ∧ g.wireBytes.length ≠ 0 then none
  else
    match g.wireBytes with
    | 2#8 :: body =>
      match SignalMessage.tryFrom protoSignalCodec body with
      | .error _ => none
      | .ok msg =>
        match evalOpen g.who g.sess with
        | none => none
        | some (role, sess) =>
          let (res, calls) := messageDecryptSignal C S.spqr (serializeAddrVal)
            (inMemAnswers sess) msg role.peer.addrVal role.addrVal (coinsOf g.rest)
          match res with
          | .ok ptBytes =>
            some (Record.encodeRecord ⟨some (storedSession sess calls)⟩,
              ptBytes, recvDraws C sess msg g.rest)
          | .error _ => none
    | _ => none

end CryptoVerification.E2E.Pqxdh.WireEntries

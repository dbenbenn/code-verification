/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Specifications.LibsignalPublicApiRepr
public import LibsignalBinary.Specifications.LibsignalE2E.State
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import ProofLib.GenDecodes
public import ProofLib.Placed.Multi

/-!
# `session_seed` specification, model bridge, and segment seam definitions

Defines `seedSpec` for `session_seed` (`0x46c20..0x47cd8`), bridging the 160-byte `InitKeys` FFI
buffer and role selector `who : u32` to `Params.initA` / `Params.initB` via canonical protobuf
encoding `encodeRecord (toRecord (extrasE p) (initParty C p k))`, together with callee specs and
segment seam predicates.
-/

public section

namespace CryptoVerification.E2E.Seed

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
  (OptU32Rel PendingRel KyberRel sessionStateReprAt RecordGhost sessionRecordAt)
open CryptoVerification.E2E (placeholderBaseKey spqrOffB)
export CryptoVerification.LibsignalPublicApiRepr
  (OptU32Rel PendingRel KyberRel sessionStateReprAt RecordGhost sessionRecordAt)
export CryptoVerification.E2E (placeholderBaseKey spqrOffB)

/-! ## Symbol names, hook bundle, and stack budgets -/

abbrev sessionSeedName : String := "session_seed"
abbrev keyPairTryFromName : String :=
  "<libsignal_core::curve::KeyPair as core::convert::TryFrom<libsignal_core::curve::PrivateKey>>::try_from"
abbrev hmacNewFromSliceLocal2Name : String :=
  "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#2]"
abbrev hmacFinalizeFixedLocal2Name : String :=
  "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#2]"
abbrev msgKeyEncodedLenName : String :=
  "<libsignal_e2e::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len"
abbrev chainEncodedLenName : String :=
  "<libsignal_e2e::storage::session_structure::Chain as prost::message::Message>::encoded_len"
abbrev sessionEncodedLenName : String :=
  "<libsignal_e2e::storage::SessionStructure as prost::message::Message>::encoded_len"
abbrev encodeChainName : String :=
  "prost::encoding::message::encode::<libsignal_e2e::storage::session_structure::Chain, alloc::vec::Vec<u8>>"
abbrev encodeVarintLocal3Name : String :=
  "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]"
abbrev doReserveLocal5Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#5]"
abbrev recordDeserializeName : String := "<libsignal_protocol::state::session::SessionRecord>::deserialize"
abbrev recordSerializeName : String := "<libsignal_protocol::state::session::SessionRecord>::serialize"

/-- External allocator hook bundle for `session_seed`. -/
structure SeedHooks (A : RustAlloc) (abs : String → Option (State → State)) : Prop where
  alloc : AllocHooks A abs

theorem SeedHooks.ofTripleRatchetHooks {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {abs : String → Option (State → State)} (h : TripleRatchetHooks C A S abs) : SeedHooks A abs :=
  ⟨h.alloc⟩

abbrev keyPairTryFromStack : Nat := 0x90
abbrev msgKeyEncodedLenStack : Nat := 0x10
abbrev chainEncodedLenStack : Nat := 0x30 + msgKeyEncodedLenStack
abbrev sessionEncodedLenStack : Nat := 0x60 + chainEncodedLenStack
abbrev doReserveLocal5Stack : Nat := 0x40 + finishGrowStack
abbrev encodeVarintLocal3Stack : Nat := 0x20 + doReserveLocal5Stack
abbrev encodeChainStack : Nat := 0x50 + max sessionEncodedLenStack encodeVarintLocal3Stack
abbrev recordDeserializeStack : Nat := 0x40000
abbrev recordSerializeStack : Nat := 0x30000
abbrev sessionSeedStack : Nat := 0x6c0 + recordDeserializeStack

/-! ## Fixed identity keys, `InitKeys` layout, and initial parameters -/

/-- `ALICE.id_pub[1..33]` (`.data` at `0x50d48`, 33 bytes with `0x05` prefix). -/
@[expose] def aliceIdPubBytes : List.Vector (BitVec 8) 32 :=
  ⟨[0x48, 0x3e, 0xf1, 0x07, 0x2a, 0xa0, 0x66, 0x42, 0x4f, 0x02, 0x3f, 0x4b, 0x14, 0x50,
    0x7c, 0x5f, 0x66, 0xa4, 0xcd, 0xff, 0xe8, 0xfc, 0x3c, 0x97, 0x0a, 0x95, 0x8b, 0xd5, 0xdb,
    0xdf, 0x9d, 0x3e], rfl⟩
@[expose] def aliceIdKey : IdentityKey := ⟨⟨aliceIdPubBytes⟩⟩

/-- `BOB.id_pub[1..33]` (`.data` at `0x50ca0`, 33 bytes with `0x05` prefix). -/
@[expose] def bobIdPubBytes : List.Vector (BitVec 8) 32 :=
  ⟨[0xce, 0x04, 0x50, 0xdd, 0x2f, 0x12, 0x34, 0x24, 0x84, 0x52, 0xb2, 0x37, 0x17, 0x1b,
    0x66, 0x02, 0x11, 0x0f, 0x10, 0x7c, 0x14, 0x1f, 0xfc, 0x0d, 0x19, 0x41, 0x07, 0x08, 0x42,
    0xd7, 0xc9, 0x3c], rfl⟩
@[expose] def bobIdKey : IdentityKey := ⟨⟨bobIdPubBytes⟩⟩

section ImageGuards
set_option maxRecDepth 2000000
open ProofLib.ProgramReflection
end ImageGuards

/-- The 160-byte wire layout of `InitKeys`. -/
@[expose] def initKeysBytes (k : InitKeys) : List (BitVec 8) :=
  keyToBytes32 k.rootKey ++ keyToBytes32 k.chainKey ++ keyToBytes32 k.bobSpkCoins ++
    keyToBytes32 k.aliceRatchetCoins ++ keyToBytes32 k.pqrKey

abbrev noopSpqr : Spqr (List (BitVec 8)) Unit := spqrOffB

/-- `Params` for `session_seed`: fixed `protoSignalCodec`, `spqrOffB`, `aliceIdKey`, and `bobIdKey`. -/
@[expose] def seedParams (C : Crypto) : Params (List (BitVec 8)) Unit where
  C := C; codec := protoSignalCodec; spqr := spqrOffB
  idA := aliceIdKey; idB := bobIdKey; addrAB := none; addrBA := none

/-- Role-indexed initial ghost state: `initA` for `.A` (`who = 0`), `initB` for `.B` (`who = 1`). -/
@[expose] def initParty (C : Crypto) (p : Party) (k : InitKeys) : GhostState (List (BitVec 8)) :=
  match p with | .A => (seedParams C).initA k | .B => (seedParams C).initB k

/-! ## `toRecord`, canonical protobuf `encodeRecord`, and `encodeRecordGhost` -/

structure Extras where
  pendingPreKey : Option PendingPreKey
  pendingKyberPreKey : Option PendingKyberPreKey
  localRegistrationId : BitVec 32
  remoteRegistrationId : BitVec 32
  aliceBaseKey : List (BitVec 8)
  deriving DecidableEq

/-- Session extras populated by `session_seed` for Alice and Bob. -/
@[expose] def extrasE : Party → Extras
  | .A => ⟨some ⟨none, 0#32, placeholderBaseKey, 0#64⟩, none, 0#32, 0#32, []⟩
  | .B => ⟨none, none, 0#32, 0#32, []⟩

@[expose] def toSession {PQ : Type} (ex : Extras) (g : GhostState PQ) : Session PQ :=
  ⟨g.session, ex.pendingPreKey, ex.pendingKyberPreKey,
   ex.localRegistrationId, ex.remoteRegistrationId, ex.aliceBaseKey⟩
@[expose] def toRecord {PQ : Type} (ex : Extras) (g : GhostState PQ) : SessionRecord PQ :=
  ⟨some (toSession ex g)⟩

@[expose] def encodeBytesField (tagByte : BitVec 8) (bs : List (BitVec 8)) : List (BitVec 8) :=
  if bs.isEmpty then [] else tagByte :: encodeVarint (BitVec.ofNat 64 bs.length) ++ bs
@[expose] def encodeMsgField (tagByte : BitVec 8) (bs : List (BitVec 8)) : List (BitVec 8) :=
  tagByte :: encodeVarint (BitVec.ofNat 64 bs.length) ++ bs
@[expose] def encodeU32Field (tagByte : BitVec 8) (v : BitVec 32) : List (BitVec 8) :=
  if v == 0#32 then [] else tagByte :: encodeVarint (v.zeroExtend 64)
@[expose] def encodeI32Field (tagByte : BitVec 8) (v : BitVec 32) : List (BitVec 8) :=
  if v == 0#32 then [] else tagByte :: encodeVarint (v.signExtend 64)
@[expose] def encodeU64Field (tagByte : BitVec 8) (v : BitVec 64) : List (BitVec 8) :=
  if v == 0#64 then [] else tagByte :: encodeVarint v
@[expose] def encodeChainKey (ck : ChainKey) : List (BitVec 8) :=
  encodeU32Field 0x08#8 ck.index ++ encodeBytesField 0x12#8 (keyToBytes32 ck.key)
@[expose] def encodeMessageKey (mkg : MessageKeyGenerator) : List (BitVec 8) :=
  encodeU32Field 0x08#8 mkg.counter ++ encodeBytesField 0x2a#8 mkg.seed
@[expose] def encodeChain (pub : PublicKey) (priv : List (BitVec 8)) (ck : Option ChainKey)
    (mks : List MessageKeyGenerator) : List (BitVec 8) :=
  encodeBytesField 0x0a#8 pub.serialize ++ encodeBytesField 0x12#8 priv ++
    (match ck with | none => [] | some c => encodeMsgField 0x1a#8 (encodeChainKey c)) ++
    mks.flatMap (fun mkg => encodeMsgField 0x22#8 (encodeMessageKey mkg))
@[expose] def encodeSenderChain (sc : SenderChain) : List (BitVec 8) :=
  encodeChain sc.ratchetKey.publicKey sc.ratchetKey.privateKey.bytes.toList (some sc.chainKey) []
@[expose] def encodeReceiverChain (rc : ReceiverChain) : List (BitVec 8) :=
  encodeChain rc.senderRatchetKey [] rc.chainKey rc.messageKeys
@[expose] def encodePendingPreKey (ppk : PendingPreKey) : List (BitVec 8) :=
  (match ppk.preKeyId with | none => [] | some id => 0x08#8 :: encodeVarint (id.zeroExtend 64)) ++
    encodeBytesField 0x12#8 ppk.baseKey.serialize ++ encodeI32Field 0x18#8 ppk.signedPreKeyId ++
    encodeU64Field 0x20#8 ppk.timestamp
@[expose] def encodePendingKyberPreKey (pkp : PendingKyberPreKey) : List (BitVec 8) :=
  encodeU32Field 0x08#8 pkp.preKeyId ++ encodeBytesField 0x12#8 pkp.ciphertext

/-- Canonical `storage.proto` encoding of `Session`. -/
@[expose] def encodeSession (s : Session (List (BitVec 8))) : List (BitVec 8) :=
  encodeU32Field 0x08#8 s.state.sessionVersion ++
    encodeBytesField 0x12#8 s.state.localIdentity.serialize ++
    (match s.state.remoteIdentity with | none => [] | some ik => encodeBytesField 0x1a#8 ik.serialize) ++
    encodeBytesField 0x22#8 (keyToBytes32 s.state.rootKey) ++
    encodeU32Field 0x28#8 s.state.previousCounter ++
    (match s.state.senderChain with | none => [] | some sc => encodeMsgField 0x32#8 (encodeSenderChain sc)) ++
    s.state.receiverChains.flatMap (fun rc => encodeMsgField 0x3a#8 (encodeReceiverChain rc)) ++
    (match s.pendingPreKey with | none => [] | some ppk => encodeMsgField 0x4a#8 (encodePendingPreKey ppk)) ++
    encodeU32Field 0x50#8 s.remoteRegistrationId ++ encodeU32Field 0x58#8 s.localRegistrationId ++
    encodeBytesField 0x6a#8 s.aliceBaseKey ++
    (match s.pendingKyberPreKey with | none => [] | some pkp => encodeMsgField 0x72#8 (encodePendingKyberPreKey pkp)) ++
    encodeBytesField 0x7a#8 s.state.pqRatchetState

/-- Canonical `storage.proto` encoding of `SessionRecord`. -/
@[expose] def encodeRecord (r : SessionRecord (List (BitVec 8))) : List (BitVec 8) :=
  match r.currentSession with | none => [] | some s => encodeMsgField 0x0a#8 (encodeSession s)

/-- Direct `GhostState` encoder matching `CryptoVerification.E2E.encodeRecord`. -/
def encodeRecordGhost (g : GhostState (List (BitVec 8))) : List (BitVec 8) :=
  let st := g.session
  encodeMsgField 0x0a#8
    (encodeU32Field 0x08#8 st.sessionVersion ++ encodeBytesField 0x12#8 st.localIdentity.serialize ++
      (match st.remoteIdentity with | none => [] | some ik => encodeBytesField 0x1a#8 ik.serialize) ++
      encodeBytesField 0x22#8 (keyToBytes32 st.rootKey) ++ encodeU32Field 0x28#8 st.previousCounter ++
      (match st.senderChain with | none => [] | some sc => encodeMsgField 0x32#8 (encodeSenderChain sc)) ++
      st.receiverChains.flatMap (fun rc => encodeMsgField 0x3a#8 (encodeReceiverChain rc)) ++
      (if st.pendingPreKey then encodeMsgField 0x4a#8 (encodeBytesField 0x12#8 placeholderBaseKey.serialize) else []) ++
      encodeBytesField 0x7a#8 st.pqRatchetState)

/-! ## In-memory `Session` / `SessionRecord` representation and ghost interface -/

@[expose] def CanonSession (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  s.Wf ∧ G.localIk.bytes = s.state.localIdentity.serialize ∧
    (match s.state.remoteIdentity with | none => G.remoteIk.bytes = [] | some ik => G.remoteIk.bytes = ik.serialize) ∧
    (match G.sender, s.state.senderChain with
     | none, none => True | some sg, some sc => sg.srk.bytes = sc.ratchetKey.publicKey.serialize | _, _ => False) ∧
    s.state.receiverChains.length ≤ maxReceiverChains ∧
    (∀ rc ∈ s.state.receiverChains, rc.messageKeys.length ≤ maxMessageKeys ∧
      ∀ mkg ∈ rc.messageKeys, mkg.seed.length = 32) ∧
    (∀ cg ∈ G.chains, cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []) ∧
    s.aliceBaseKey.length < 2 ^ 32 ∧
    (match s.pendingKyberPreKey with | none => True | some pkp => pkp.ciphertext.length < 2 ^ 32) ∧
    s.state.pqRatchetState.length < 2 ^ 32 ∧ (encodeSession s).length < 2 ^ 62

@[expose] def CanonRecord (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Prop :=
  match g.cur, r.currentSession with | none, none => True | some G, some s => CanonSession G s | _, _ => False

@[expose] def SeedSession (s : Session (List (BitVec 8))) : Prop :=
  ∃ C p k, s = toSession (extrasE p) (initParty C p k)

@[expose] def CanonChainSerialization (gc : ChainGhost × ReceiverChain) : Prop :=
  gc.1.srk.bytes = gc.2.senderRatchetKey.serialize ∧ gc.1.priv.bytes = []

@[expose] def CanonSenderSerialization : Option SenderChainGhost → Option SenderChain → Prop
  | none, none => True
  | some g, some sc => g.srk.bytes = sc.ratchetKey.publicKey.serialize ∧
      g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList
  | _, _ => False

@[expose] def CanonPendingSerialization : Option TailVecGhost → Option PendingPreKey → Prop
  | none, none => True
  | some g, some p => g.vec.bytes = p.baseKey.serialize
  | _, _ => False

@[expose] def CanonSessionSerialization (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  G.localIk.bytes = s.state.localIdentity.serialize ∧
  G.remoteIk.bytes = (s.state.remoteIdentity.map IdentityKey.serialize).getD [] ∧
  CanonSenderSerialization G.sender s.state.senderChain ∧
  G.chains.length = s.state.receiverChains.length ∧
  (∀ gc ∈ G.chains.zip s.state.receiverChains, CanonChainSerialization gc) ∧
  CanonPendingSerialization G.pending s.pendingPreKey

@[expose] def CanonRecordSerialization (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Prop :=
  match g.cur, r.currentSession with
  | none, none => True
  | some G, some s => CanonSessionSerialization G s
  | _, _ => False

structure RecordDeserializeGhost where
  ptr : BitVec 64
  s : Session (List (BitVec 8))
  out : BitVec 64

@[expose] def recordDeserializeSpec (A : RustAlloc) : Spec RecordDeserializeGhost where
  pre := fun x st =>
    let bs := encodeRecord ⟨some x.s⟩
    ⌜st.readReg64 .x0 = x.ptr ∧ (st.readReg64 .x1).toNat = bs.length ∧
      st.readReg64 .x8 = x.out ∧ SeedSession x.s⌝ ∗
      (x.ptr ↦ₛ bs) ∗ memRegion x.out 0x170 ∗ A.pool ∗ stackAt st.sp recordDeserializeStack
  post := fun x s0 sf =>
    let bs := encodeRecord ⟨some x.s⟩
    ⌜sf.trace = s0.trace⌝ ∗ (x.ptr ↦ₛ bs) ∗
      (∃∗ G : SessionGhost, ⌜CanonSessionSerialization G x.s⌝ ∗ sessionRecordAt A x.out ⟨0#64, 8#64, some G⟩ ⟨some x.s⟩) ∗
      A.pool ∗ stackAt s0.sp recordDeserializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure RecordSerializeGhost where
  self : BitVec 64
  g : RecordGhost
  r : SessionRecord (List (BitVec 8))
  out : BitVec 64

@[expose] def recordSerializeSpec (A : RustAlloc) : Spec RecordSerializeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      CanonRecordSerialization x.g x.r ∧ (encodeRecord x.r).length < 2 ^ 32⌝ ∗
      sessionRecordAt A x.self x.g x.r ∗ memRegion x.out 48 ∗ A.pool ∗ stackAt s.sp recordSerializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionRecordAt A x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encodeRecord x.r) ∗
      memRegion (x.out + 32#64) 16 ∗ A.pool ∗ stackAt s0.sp recordSerializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Packed output layout `seedOutAt` and top-level `seedSpec` -/

/-- Packed FFI output buffer `[state.length : u64 LE][0 : u64 LE][state]` written by `pack(state, &[])`. -/
@[expose] def seedOutAt (A : RustAlloc) (out : BitVec 64) (state : List (BitVec 8)) : SepProp :=
  ⌜out ≠ 0#64 ∧ state.length + 16 < 2 ^ 63⌝ ∗ A.live out (state.length + 16) 1 ∗
    (out ↦₆₄ BitVec.ofNat 64 state.length) ∗ ((out + 8#64) ↦₆₄ 0#64) ∗ ((out + 16#64) ↦ₛ state)

@[expose] def decodeWho (who : BitVec 32) : Option Party :=
  if who == 0#32 then some .A else if who == 1#32 then some .B else none

structure SeedGhost where
  who : BitVec 32
  kPtr : BitVec 64
  kLen : BitVec 64
  keys : InitKeys

@[expose] def seedInputAt (x : SeedGhost) : SepProp :=
  if x.kLen = 160#64 ∧ x.kPtr ≠ 0#64 then x.kPtr ↦ₛ initKeysBytes x.keys else emp

/-- Top-level specification of `session_seed` (`0x46c20..0x47cd8`): on valid `(who, kPtr, kLen = 160)`
inputs returns `seedOutAt A x0 (encodeRecord (toRecord (extrasE p) (initParty C p x.keys)))`, and on
invalid inputs returns null (`x0 = 0`). -/
@[expose] def seedSpec (C : Crypto) (A : RustAlloc) : Spec SeedGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 32 = x.who ∧ s.readReg64 .x1 = x.kPtr ∧ s.readReg64 .x2 = x.kLen⌝ ∗
      seedInputAt x ∗ A.pool ∗ stackAt s.sp sessionSeedStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ seedInputAt x ∗ A.pool ∗ stackAt s0.sp sessionSeedStack ∗
      match if x.kLen = 160#64 ∧ x.kPtr ≠ 0#64 then decodeWho x.who else none with
      | some p =>
        seedOutAt A (sf.readReg64 .x0)
          (encodeRecord (toRecord (extrasE p) (initParty C p x.keys))) ∗ anyHeap
      | none => ⌜sf.readReg64 .x0 = 0#64⌝
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Callee specifications -/

structure KeyPairTryFromGhost where
  skA : BitVec 64
  sk : PrivateKey
  ret : BitVec 64

@[expose] def keyPairTryFromSpec (pubKey : PubKeyFn) : Spec KeyPairTryFromGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.skA ∧ s.readReg64 .x8 = x.ret⌝ ∗
      (x.skA ↦ₛ x.sk.bytes.toList) ∗ memRegion x.ret 72 ∗ stackAt s.sp keyPairTryFromStack
  post := fun x s0 sf =>
    let pk := pubKey (Ratchet.clampScalar x.sk.bytes)
    ⌜sf.trace = s0.trace⌝ ∗ (x.skA ↦ₛ x.sk.bytes.toList) ∗ (x.ret ↦₈ 0#8) ∗ ((x.ret + 1#64) ↦ₛ pk.toList) ∗
      ((x.ret + 33#64) ↦ₛ x.sk.bytes.toList) ∗ memRegion (x.ret + 65#64) 7 ∗ stackAt s0.sp keyPairTryFromStack

structure MsgKeyEncodedLenGhost where
  self : BitVec 64
  pin : MessageKeyGhost
  mkg : MessageKeyGenerator

@[expose] def msgKeyEncodedLenSpec (A : RustAlloc) : Spec MsgKeyEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ x.mkg.seed.length = 32⌝ ∗
      messageKeyAt A (x.pin, x.mkg) x.self ∗ stackAt s.sp msgKeyEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encodeMessageKey x.mkg).length ∧ sf.trace = s0.trace⌝ ∗
      messageKeyAt A (x.pin, x.mkg) x.self ∗ stackAt s0.sp msgKeyEncodedLenStack

@[expose] def seedChainAt (A : RustAlloc) (pin : SenderChainGhost) (pub : PublicKey) (priv : List (BitVec 8))
    (ck : Option ChainKey) (a : BitVec 64) : SepProp :=
  vecU8At A a pin.srk.cap pin.srk.ptr pub.serialize ∗ vecU8At A (a + 0x18#64) pin.priv.cap pin.priv.ptr priv ∗
    vecAt A 104 8 (messageKeyAt A) (a + 0x30#64) pin.mkCap pin.mkPtr [] ∗ optChainKeyAt A pin.ck ck (a + 0x48#64)

structure ChainEncodedLenGhost where
  self : BitVec 64
  pin : SenderChainGhost
  pub : PublicKey
  priv : List (BitVec 8)
  ck : Option ChainKey

@[expose] def chainEncodedLenSpec (A : RustAlloc) : Spec ChainEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ (x.priv = [] ∨ x.priv.length = 32)⌝ ∗
      seedChainAt A x.pin x.pub x.priv x.ck x.self ∗ stackAt s.sp chainEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encodeChain x.pub x.priv x.ck []).length ∧ sf.trace = s0.trace⌝ ∗
      seedChainAt A x.pin x.pub x.priv x.ck x.self ∗ stackAt s0.sp chainEncodedLenStack

structure SessionEncodedLenGhost where
  self : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))

@[expose] def sessionEncodedLenSpec (A : RustAlloc) : Spec SessionEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ CanonSession x.G x.sess⌝ ∗
      sessionStateReprAt A x.self x.G x.sess ∗ stackAt s.sp sessionEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encodeSession x.sess).length ∧ sf.trace = s0.trace⌝ ∗
      sessionStateReprAt A x.self x.G x.sess ∗ stackAt s0.sp sessionEncodedLenStack

structure EncodeChainSeedGhost where
  tag : BitVec 32
  chainPtr : BitVec 64
  pin : SenderChainGhost
  pub : PublicKey
  priv : List (BitVec 8)
  ck : Option ChainKey
  bufPtr : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

@[expose] def encodeChainSeedSpec (A : RustAlloc) : Spec EncodeChainSeedGhost where
  pre := fun x s =>
    let msgBytes := encodeMsgField ((x.tag <<< 3 ||| 2#32).setWidth 8) (encodeChain x.pub x.priv x.ck [])
    ⌜(s.readReg64 .x0).setWidth 32 = x.tag ∧ s.readReg64 .x1 = x.chainPtr ∧
      s.readReg64 .x2 = x.bufPtr ∧ (x.tag = 6#32 ∨ x.tag = 7#32) ∧
      (x.priv = [] ∨ x.priv.length = 32) ∧ x.bs.length + msgBytes.length ≤ x.cap.toNat⌝ ∗
      seedChainAt A x.pin x.pub x.priv x.ck x.chainPtr ∗
      vecU8At A x.bufPtr x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp encodeChainStack
  post := fun x s0 sf =>
    let msgBytes := encodeMsgField ((x.tag <<< 3 ||| 2#32).setWidth 8) (encodeChain x.pub x.priv x.ck [])
    ⌜sf.trace = s0.trace⌝ ∗ seedChainAt A x.pin x.pub x.priv x.ck x.chainPtr ∗
      vecU8At A x.bufPtr x.cap x.ptr (x.bs ++ msgBytes) ∗ A.pool ∗ stackAt s0.sp encodeChainStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Segment seam predicates and `SepWPp` composition -/

theorem SepWPp.trans {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q_mid Q Qp : State → SepProp → Prop} (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q_mid sm Pm → SepWPp prog ret sm Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps1, ⟨hpc, hrun, Pm, hmm, hQm⟩ | hpan⟩
  · rcases h2 sm Pm hpc hrun hQm R hmm (hsteps1.codeLoaded hL) with ⟨sf, hsteps2, hout⟩
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact ⟨sm, hsteps1, Or.inr hpan⟩

theorem subroutine_ok_of_wpp {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (s0 : State), s0.pc = entry → s0.status = .Running → s0.spAligned = true →
      SepWPp prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (Pf ⊢ spec.post x s0 sf))
        (fun sf Pf => Pf ⊢ spec.onPanic x s0 sf)) :
    subroutine_ok prog entry spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, Pf, hmf, hspf, hcsf, hq⟩ | ⟨hpan, Pf, hmf, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h x s0 hpc hrun hsp R hpre hL
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩,
      Satisfies.mono (sepConj_mono_left hq) hmf⟩))
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan,
      Satisfies.mono (sepConj_mono_left hqp) hmf⟩)))
  · exact False.elim (not_satisfies_false_sepConj hoom)

@[expose] def seedSavedRegsAt (s0 : State) (sp : BitVec 64) : SepProp :=
  ((sp + 0x660#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp + 0x668#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp + 0x670#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp + 0x678#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp + 0x680#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp + 0x688#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp + 0x690#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp + 0x698#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp + 0x6a0#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp + 0x6a8#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp + 0x6b0#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp + 0x6b8#64) ↦₆₄ s0.readReg64 .x19)

/-- Seam at `+0x0940` (`0x47560`, Alice join of `Err(dh)` `+0x0354` and `Ok(dh)` `+0x093c`). -/
@[expose] def aliceSenderReadyAt (C : Crypto) (A : RustAlloc) (s : State) (k : InitKeys) : SepProp :=
  let spk := KeyPair.generate C k.bobSpkCoins; let ratch := KeyPair.generate C k.aliceRatchetCoins
  match Ratchet.createChain C.F C.X k.rootKey spk.publicKey.bytes ratch.privateKey.bytes with
  | none =>
    ⌜s.readReg64 .x20 = noneCap⌝ ∗ boxU8Buf A (s.readReg64 .x21) (keyToBytes32 k.rootKey) ∗ memRegion (s.sp + 0x180#64) 24
  | some (rk', ck') =>
    boxU8Buf A (s.readReg64 .x20) ratch.publicKey.serialize ∗ vecU8 A (s.sp + 0x180#64) ratch.privateKey.bytes.toList ∗
      boxU8Buf A (s.readReg64 .x22) (keyToBytes32 ck') ∗ boxU8Buf A (s.readReg64 .x21) (keyToBytes32 rk')

end CryptoVerification.E2E.Seed

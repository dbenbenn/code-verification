/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwned -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Abstract Callee Semantics and Caller-Side Wrapper Slot Layouts (`Sem.lean`)

Fixes the abstract semantics (`RunSem`) and caller-side separation-logic layouts invoked by
`signal_session::run`:
- `RunSem` specifies the abstract transition (`SlotAns`: panic, reject, or accept with updated
  `StoresGhost` and return value) for `encrypt`, `decryptSignal`, `initiate`, and `decryptPrekey`,
  the all-inputs parser `pksmParse`, and the input domain predicates `filesOk`, `encOk`, `initOk`,
  and `decPkOk`.
- `decResAt`, `encResAt`, `initResAt`, `pksmResAt`, and `cliBundleAt` specify the caller-side
  result, error, and `PreKeyBundle` memory layouts.
- `slotsOf` packages the wrapper slot stack budgets together with `cliKemDeserializeSpec` into
  `RunSlots`.
-/

public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.RecordCodecs

abbrev Bytes := List (BitVec 8)

/-! ## 1. The abstract semantics -/

/-- A wrapper callee's answer: `none` = panic; `some none` = reject (`Err`, or `None`/pending,
which `run` maps to `Rejected` too); `some (some (g', v))` = accept with the stores `g'` after the
call and the value `v`. -/
abbrev SlotAns (α : Type) := Option (Option (StoresGhost × α))

/-- The `PreKeyBundle` `read_bundle` builds (`public.rs:93`), on its values: the identity key,
the registration id, the device id (the peer's), the signed pre-key (id, key, signature), the
Kyber pre-key (id, the 1568 key bytes after the `0x08` type byte, signature) and the optional
one-time pre-key (id, key). -/
structure BundleV where
  idKey : IdentityKey
  regId : BitVec 32
  device : BitVec 8
  spkId : BitVec 32
  spk : PublicKey
  spkSig : Bytes
  kpkId : BitVec 32
  kpk : Bytes
  kpkSig : Bytes
  opk : Option (BitVec 32 × PublicKey)

/-- Abstract semantics of `signal_session::run`'s four stateful wrapper callees, the all-inputs
`PreKeySignalMessage` parser, and their store/input domain preconditions. `F` is the run-entry
filesystem (`(initFsState (cliInputs i)).files`) and `coins` is `coinsOf i`; the stores at every
wrapper call are `StoresGhost.opened`. -/
structure RunSem where
  /-- `signal_session_ratchet::encrypt(ptext, peer, me, stores, now = UNIX_EPOCH)`. -/
  encrypt : FsFiles → AddrVal → AddrVal → Bytes → Bytes → SlotAns CiphertextMessage
  /-- `signal_session_ratchet::decrypt_signal(msg, peer, me, stores)`; `msg` is the parsed
  `SignalMessage` (`SignalMessage.tryFrom protoSignalCodec` of the wire bytes after the type
  byte). -/
  decryptSignal : FsFiles → AddrVal → AddrVal → SignalMessage → Bytes → SlotAns Bytes
  /-- `signal_session_handshake::initiate(peer, me, stores, bundle, now = UNIX_EPOCH)`. -/
  initiate : FsFiles → AddrVal → AddrVal → BundleV → Bytes → SlotAns Unit
  /-- `signal_session_handshake::decrypt_prekey(pksm, peer, me, stores)`. -/
  decryptPrekey : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Bytes → SlotAns Bytes
  /-- All-inputs `PreKeySignalMessage::try_from` parser on the wire bytes after the tag byte. -/
  pksmParse : Bytes → Option PreKeySignalMessage
  /-- Store-file well-formedness precondition assumed by all four wrapper slots (`files`, `peer`,
  `me`), ensuring the session, identity, and pre-key store files decode cleanly. -/
  filesOk : FsFiles → AddrVal → AddrVal → Prop
  /-- Encrypt-slot domain precondition (`files`, `peer`, `coins`), e.g. `64 ≤ coins.length` or an
  empty PQ ratchet state on the peer session. -/
  encOk : FsFiles → AddrVal → Bytes → Prop
  /-- Initiate-slot domain precondition (`files`, `peer`, `me`), e.g. absence of an existing peer
  session when using 1-session `sessionRecordAt`, plus local/remote identity invariants. -/
  initOk : FsFiles → AddrVal → AddrVal → Prop
  /-- Decrypt-prekey-slot domain precondition (`files`, `peer`, `me`, parsed message `pm`). -/
  decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop

/-- Stack budgets of the four stateful wrapper slots. -/
structure RunNeeds where
  encrypt : Nat
  decryptSignal : Nat
  initiate : Nat
  decryptPrekey : Nat

/-! ## 2. Layout pieces -/

@[expose] def sessVt (_img : Unit) : BitVec 64 := 0#64
@[expose] def idVt (_img : Unit) : BitVec 64 := 0#64
@[expose] def oneTimeVt (_img : Unit) : BitVec 64 := 0#64
@[expose] def signedVt (_img : Unit) : BitVec 64 := 0#64
@[expose] def kyberVt (_img : Unit) : BitVec 64 := 0#64

/-- `now : SystemTime` by value at `p` (16 bytes, matching `MessageEncrypt.nowAt`); `run` passes
`UNIX_EPOCH` (all zero). -/
@[expose] def nowCellAt (p : BitVec 64) (t : SystemTime) : SepProp :=
  (p ↦₆₄ t.tvSec) ∗ ((p + 8#64) ↦₃₂ t.tvNsec) ∗ memRegion (p + 12#64) 4

/-- `SystemTime::UNIX_EPOCH`. -/
@[expose] def unixEpoch : SystemTime := ⟨0#64, 0#32⟩

/-- 48-byte `Option<Result<Vec<u8>, SignalProtocolError>>` return layout shared by
`decrypt_prekey` and `decrypt_signal`: `Ok` matches `apiDecResultAt` (`okTagVec = -2` at `+0` and
plaintext `Vec<u8>` at `+8`), while `Err` widens `apiDecResultAt` to any droppable
`RunDrop.speOwnedAt` at `+0` so CLI-store `InvalidState` and bad-prekey-id errors are covered. -/
@[expose] def decResAt (A : RustAlloc) (r : BitVec 64) : Except (ApiError AddrVal Unit) Bytes → SepProp
  | .ok pt => vecResultAt A r (.ok pt)
  | .error _ => ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k

/-- `decResAt`'s `Ok` arm is the public entry's (`apiDecResultAt`): only the `Err` arm widens. -/
theorem decResAt_ok (A : RustAlloc) (r : BitVec 64) (pt : Bytes) :
    decResAt A r (.ok pt) = apiDecResultAt A r (.ok pt) := rfl

/-- 248-byte `Result<CiphertextMessage, SignalProtocolError>` return layout of `encrypt`: `Ok`
matches `apiEncResultAt`, while `Err` places `errTag` at `+0`, any droppable `RunDrop.speOwnedAt`
at `+8`, and 192 unspecified trailing bytes at `+56`. -/
@[expose] def encResAt (A : RustAlloc) (r : BitVec 64) :
    Except (ApiError AddrVal Unit) CiphertextMessage → SepProp
  | .ok m => apiEncResultAt A r (.ok m)
  | .error _ =>
    (r ↦₆₄ errTag) ∗ (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (r + 8#64) k) ∗
      memRegion (r + 56#64) 192

/-- `encResAt`'s `Ok` arm is the public entry's (`apiEncResultAt`): only the `Err` arm widens. -/
theorem encResAt_ok (A : RustAlloc) (r : BitVec 64) (m : CiphertextMessage) :
    encResAt A r (.ok m) = apiEncResultAt A r (.ok m) := rfl

/-- 48-byte `Option<Result<(), SignalProtocolError>>` return layout of `initiate`: `Ok(())` has
word `0` equal to `-2`, while `Err` holds any droppable `RunDrop.speOwnedAt` at `+0` (including
`SignatureValidationFailed` = `speWord 11`). -/
@[expose] def initResAt (A : RustAlloc) (r : BitVec 64) : Except (ApiError AddrVal Unit) Unit → SepProp
  | .ok () => (r ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (r + 8#64) 40
  | .error _ => ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k

/-- 192-byte (`0xc0`) `PreKeyBundle` layout passed by reference (`&bundle`) from
`signal_session::run` to `initiate` at `a`, together with its three caller-freed heap buffers
(`spkSig` 64 B at `+0x00..+0x18`, `kpkSig` 64 B at `+0x40..+0x58`, `kpk` 1568 B at `+0x58..+0x68`),
`spkId` (`+0x38`), `kpkId` (`+0x68`), `opk` (`+0x70..+0x98`, flag `+0x9c`), `regId` (`+0x98`), and
`device` (`+0xbd`). -/
@[expose] def cliBundleAt (a : BitVec 64) (b : BundleV) (spkSigPtr kpkSigPtr kpkPtr : BitVec 64) :
    SepProp :=
  let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
  ∃∗ opkId : BitVec 32,
    ⌜b.spkSig.length = 64 ∧ b.kpkSig.length = 64 ∧ b.kpk.length = 1568 ∧
      ∀ p, b.opk = some p → opkId = p.1⌝ ∗
    (a ↦₆₄ 64#64) ∗ ((a + 8#64) ↦₆₄ spkSigPtr) ∗ ((a + 16#64) ↦₆₄ 64#64) ∗
    (spkSigPtr ↦ₛ b.spkSig) ∗
    ((a + 24#64) ↦ₛ b.spk.bytes.toList) ∗
    ((a + 56#64) ↦₃₂ b.spkId) ∗ memRegion (a + 60#64) 4 ∗
    ((a + 64#64) ↦₆₄ 64#64) ∗ ((a + 72#64) ↦₆₄ kpkSigPtr) ∗ ((a + 80#64) ↦₆₄ 64#64) ∗
    (kpkSigPtr ↦ₛ b.kpkSig) ∗
    ((a + 88#64) ↦₆₄ kpkPtr) ∗ ((a + 96#64) ↦₆₄ 1568#64) ∗ (kpkPtr ↦ₛ b.kpk) ∗
    ((a + 104#64) ↦₃₂ b.kpkId) ∗ memRegion (a + 108#64) 4 ∗
    ((a + 112#64) ↦₃₂ opkFlag) ∗ ((a + 116#64) ↦₃₂ opkId) ∗
    ((a + 120#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗ ((a + 152#64) ↦₃₂ b.regId) ∗
    ((a + 156#64) ↦₈ opkFlag.truncate 8) ∗
    (match b.opk with
     | some (_, k) => (a + 157#64) ↦ₛ k.bytes.toList
     | none => memRegion (a + 157#64) 32) ∗
    ((a + 189#64) ↦₈ b.device) ∗ memRegion (a + 190#64) 2

/-! ## 3. The slot specs -/

/-- What every wrapper call site shares: the two address ghosts and pointers, the stores, the
result slot, the coin pointer, and the run-entry values `F` / `coins` that `S` reads. -/
structure SlotCtx where
  peer : AddrGhost
  peerA : BitVec 64
  me : AddrGhost
  meA : BitVec 64
  stores : BitVec 64
  ret : BitVec 64
  coinsP : BitVec 64
  F : FsFiles
  coins : Bytes

/-- Common wrapper-slot precondition footprint: opened stores, peer and local addresses, coins
length bound `coins.length < 2 ^ 63`, and allocator pool. -/
@[expose] def slotFrame (A : RustAlloc) (_img : Unit) (x : SlotCtx) : SepProp :=
  ⌜x.coins.length < 2 ^ 63⌝ ∗
  storesAt A x.stores StoresGhost.opened ∗ protocolAddressAt A x.peer x.peerA ∗
    protocolAddressAt A x.me x.meA ∗ A.pool

/-- The common post facts: the trace only grows; files and stdout unchanged. -/
@[expose] def slotTrace (s0 sf : State) : Prop :=
  s0.trace <+: sf.trace ∧ sf.fs.files = s0.fs.files ∧
    ProcessOutcome.traceStreamBytes .stdout sf.trace =
      ProcessOutcome.traceStreamBytes .stdout s0.trace

/-- Links the wrapper return value `e` and post-call stores `g'` to the abstract answer `ans`:
`Ok v` iff `ans = some (some (g', v))` with `cliWrOk` write paths, and `Err` (excluding `store ()`)
iff `ans = some none`. -/
@[expose] def slotOut {α : Type} (ans : SlotAns α) (g' : StoresGhost)
    (e : Except (ApiError AddrVal Unit) α) (_s0 _sf : State) : Prop :=
  e ≠ .error .panic ∧ e ≠ .error (.store ()) ∧
    match e with
    | .ok v => ans = some (some (g', v)) ∧ ∀ pw ∈ g'.writes, cliWrOk pw.1
    | .error _ => ans = some none

/-- Ghost of the `encrypt` call: the shared context and the plaintext. -/
structure EncGhost extends SlotCtx where
  ptA : BitVec 64
  ptext : Bytes

/-- Ghost of the `decrypt_signal` call: the shared context and the parsed message (built by
`SignalMessage::try_from`, borrowed; `run` drops it after the call). -/
structure DecSigGhost extends SlotCtx where
  msgA : BitVec 64
  msgG : SignalMessageGhost
  msg : SignalMessage

/-- Ghost of the `initiate` call: the shared context, the bundle (borrowed at `bundleA`) and its
three heap pointers (which `run` frees after the call). -/
structure InitGhost extends SlotCtx where
  bundleA : BitVec 64
  bundle : BundleV
  spkSigPtr : BitVec 64
  kpkSigPtr : BitVec 64
  kpkPtr : BitVec 64

/-- Ghost of the `decrypt_prekey` call: the shared context and the parsed message (borrowed). -/
structure DecPkGhost extends SlotCtx where
  msgA : BitVec 64
  msgG : PreKeyMsgGhost
  msg : PreKeySignalMessage

/-- Ghost of an all-inputs `PreKeySignalMessage::try_from` call. -/
structure PksmGhost where
  ptr : BitVec 64
  bytes : Bytes
  ret : BitVec 64

/-- 248-byte return layout of `PreKeySignalMessage::try_from`: `preKeyMsgAt` at `+0` when
`S.pksmParse` returns `some`, or `errTag` at `+0` with an owned `SignalProtocolError` at `+8` when
`none`, together with `anyHeap` for residual parser allocations. -/
@[expose] def pksmResAt (A : RustAlloc) (r : BitVec 64) : Option PreKeySignalMessage → SepProp
  | some m => (∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g r m) ∗ anyHeap
  | none => (r ↦₆₄ errTag) ∗ (∃∗ fn : Bytes, ∃∗ e : SignalProtocolError, speAt A fn (r + 8#64) e) ∗
      memRegion (r + 56#64) 192 ∗ anyHeap

/-! ## 4. The slots -/

/-- Packages a `Nat → Spec G` family and stack budget `need` into a `CalleeSlot`. -/
@[expose] def mkSlot {G : Type} (spec : Nat → Spec G) (need : Nat) : CalleeSlot := ⟨G, spec, need⟩

/-- Wrapper and `cliKemDeserializeSpec` (`48 + extHookStack`) callee slots at stack budgets `needs`. -/
@[expose] def slotsOf (A : RustAlloc) (_img : Unit) (_S : RunSem) (needs : RunNeeds) : RunSlots where
  encrypt := mkSlot (G := Unit) (fun stk => { pre := fun _ s => stackAt s.sp stk, post := fun _ s0 _ => stackAt s0.sp stk }) needs.encrypt
  decryptSignal := mkSlot (G := Unit) (fun stk => { pre := fun _ s => stackAt s.sp stk, post := fun _ s0 _ => stackAt s0.sp stk }) needs.decryptSignal
  initiate := mkSlot (G := Unit) (fun stk => { pre := fun _ s => stackAt s.sp stk, post := fun _ s0 _ => stackAt s0.sp stk }) needs.initiate
  decryptPrekey := mkSlot (G := Unit) (fun stk => { pre := fun _ s => stackAt s.sp stk, post := fun _ s0 _ => stackAt s0.sp stk }) needs.decryptPrekey
  kemDeserialize := mkSlot (RunProofs.cliKemDeserializeSpec A) (48 + extHookStack)

end CryptoVerification.SignalSession.Cli.RunCompose

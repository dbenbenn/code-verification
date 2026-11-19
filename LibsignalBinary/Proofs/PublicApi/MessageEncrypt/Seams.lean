/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout

/-!
# Seam Decomposition and Frame Layout for `session_message_encrypt_with_stores`

Intermediate seam states, `0xbe0`-byte stack-frame predicates, and specification `withStoresEncSpecV`
for `session_message_encrypt_with_stores` (`0x3caf4`), parameterized by record scope `Scope` and
store contracts `SessionStoreSpec` / `IdentityStoreSpec`.

## Main-Path Seams

| Seam | Offset | Protocol step completed | Predicate |
| --- | --- | --- | --- |
| Entry | `+0x000` | — | `withStoresEncSpecV.pre` |
| `Cur` | `+0x20c` | `load_session = Ok(Some r)`, current session `sess` | `CurStateV` |
| `Otr` | `+0x2c8` | `from_session_state = Ok (otr, taken)` | `OtrStateV` |
| `Key` | `+0x344` | `taken.remoteIdentity = some k` | `KeyStateV` |
| `Cm` | `+0xa70` | `CiphertextMessage` `m` and updated `otr'` constructed | `CmStateV` |
| `Save` | `+0xbd4` | `is_trusted_identity = Ok true` | `SaveStateV` |
| `Apply` | `+0xd9c` | `save_identity = Ok c` | `ApplyStateV` |
| `Stored` | `+0xe88` | `store_session = Ok ()` | `StoredStateV` |

Error and panic exits run directly to an outcome of `withStoresEncSpecV` via shared error-tail
lemmas rather than separate error seams.

## Stack Frame Layout (`sp = s0.sp - 0xbe0`, `x29 = s0.sp - 0x60`)

| Range | Contents |
| --- | --- |
| `sp+0x000..0x058` | Call scratch and cross-seam pointer spills (`curScratch`, `cmScratch`) |
| `sp+0x058..0x110` | Prologue argument spills (`encSpillsAtV`) |
| `sp+0x110..0x280` | Loaded `SessionRecord` (368 B; `SessionState` at `sp+0x128`) |
| `sp+0x280..0x288` | `SessionState` pointer spill (`sp+0x128`) |
| `sp+0x288..0x350` | `OutgoingTripleRatchet` (200 B, `otrAt`) |
| `sp+0x350..0x370` | Remote identity key (32 B) |
| `sp+0x370..0x468` | `CiphertextMessage` result staging (248 B, `apiEncResultAt` layout) |
| `sp+0x468..0x46a` | Async state byte (`0`) and OTR PQ-`Vec` drop flag (`1` after `from_session_state`) |
| `sp+0x46a..0xb80` | Async poll buffers and call staging |
| `sp+0xb80..0xbe0` | Saved callee-saved registers `x19..x30` (`encSavedRegs`) |
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## Frame Constants and Seam PCs -/

/-- Stack frame size of `session_message_encrypt_with_stores` (`0xbe0` bytes). -/
abbrev encFrameSize : Nat := 0xbe0

/-- Stack budget at entry to `_with_stores` (`entryStack` minus the wrapper's `0x30`-byte frame). -/
abbrev withStoresEncStack : Nat := entryStack - 0x30

abbrev encSubStack : Nat := withStoresEncStack - encFrameSize

/-- Callee stack budget below the `0xbe0`-byte frame for given `SessionStoreSpec` and `IdentityStoreSpec`. -/
abbrev encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  max encSubStack
    (max (max (max kit.loadShimStack kit.loadPollStack)
              (max kit.storeShimStack kit.storePollStack))
         (max (max ikit.trustShimStack ikit.trustPollStack)
              (max ikit.saveShimStack ikit.savePollStack)))

abbrev withStoresEncStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  encSubStackV kit ikit + encFrameSize

theorem encSubStack_le_encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    encSubStack ≤ encSubStackV kit ikit :=
  Nat.le_max_left _ _

theorem withStoresEncStack_le_withStoresEncStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    withStoresEncStack ≤ withStoresEncStackV kit ikit := by
  unfold withStoresEncStackV
  have h := encSubStack_le_encSubStackV kit ikit
  have h2 : withStoresEncStack = encSubStack + encFrameSize := by decide
  omega

/-- Ghost input bundle for `session_message_encrypt_with_stores`, extending `EncryptGhost` with
the session-store (`x4`) and identity-store (`x6`) data pointers. -/
structure WithStoresEncGhost extends EncryptGhost where
  ssA : BitVec 64
  idA : BitVec 64

/-- Stack layout of `now: SystemTime` passed by value at caller `sp` (`tv_sec` at `+0`, `tv_nsec`
at `+8`, 4 bytes padding at `+12`). -/
@[expose] def nowAt (p : BitVec 64) (t : SystemTime) : SepProp :=
  (p ↦₆₄ t.tvSec) ∗ ((p + 8#64) ↦₃₂ t.tvNsec) ∗ memRegion (p + 12#64) 4

/-- Callee-saved registers `x19..x30` spilled at `[sp0 - 96 .. sp0)`. -/
@[expose] def encSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Prologue argument spills at `sp + 0x58 .. sp + 0x110`, parameterized by store vtables. -/
@[expose] def encSpillsAtV (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) : SepProp :=
  ((sp + 0x58#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0x60#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0x64#64) 4 ∗ ((sp + 0x68#64) ↦₆₄ x.ptA) ∗
  ((sp + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0x78#64) ↦₆₄ x.remA) ∗
  ((sp + 0x80#64) ↦₆₄ x.locA) ∗ ((sp + 0x88#64) ↦₆₄ x.ssA) ∗ ((sp + 0x90#64) ↦₆₄ ss_vt) ∗
  ((sp + 0x98#64) ↦₆₄ x.idA) ∗ ((sp + 0xa0#64) ↦₆₄ id_vt) ∗
  ((sp + 0xa8#64) ↦₆₄ (sp + 0xb6f#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
  ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
  ((sp + 0xc8#64) ↦₆₄ x.locA) ∗ ((sp + 0xd0#64) ↦₆₄ x.ssA) ∗ ((sp + 0xd8#64) ↦₆₄ ss_vt) ∗
  ((sp + 0xe0#64) ↦₆₄ x.idA) ∗ ((sp + 0xe8#64) ↦₆₄ id_vt) ∗
  ((sp + 0xf0#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0xf8#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0xfc#64) 4 ∗ ((sp + 0x100#64) ↦₆₄ (sp + 0xb6f#64)) ∗
  ((sp + 0x108#64) ↦₆₄ x.remA)

/-- Call scratch `sp + 0x00 .. sp + 0x58` at `Cur`, `Otr`, and `Key`, retaining the
`SessionState` pointer spill `[sp + 0x50] = sp + 0x128`. -/
@[expose] def curScratch (sp : BitVec 64) : SepProp :=
  memRegion sp 0x50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

/-- Call scratch `sp + 0x00 .. sp + 0x58` at `Cm`, `Save`, `Apply`, and `Stored`, retaining the
OTR (`[sp + 0x38] = sp + 0x288`), remote identity key (`[sp + 0x40] = sp + 0x350`), and
`SessionState` (`[sp + 0x50] = sp + 0x128`) pointer spills. -/
@[expose] def cmScratch (sp : BitVec 64) : SepProp :=
  memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
    ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗ memRegion (sp + 0x48#64) 8 ∗
    ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

/-- Session record after `from_session_state` moves the SPQR state out into `otr`. -/
@[expose] def takenRecord (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
    SessionRecord (List (BitVec 8)) :=
  { currentSession := some { sess with state := taken } }

/-- `OutgoingTripleRatchet.fromSessionState` transfers `s.pqRatchetState` into `otr.pqrState`. -/
theorem fromSessionState_pqrState {s taken : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (otr, taken)) :
    otr.pqrState = s.pqRatchetState := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq] at h
  all_goals (try split_ifs at h) <;>
    simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.ok.injEq, Prod.mk.injEq] at h
  exact h.1 ▸ rfl

/-- Updated `SessionRecord` written by `store_session` (`otr'` applied to `taken`). -/
@[expose] def storedRecord (sess : Session (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) : SessionRecord (List (BitVec 8)) :=
  { currentSession := some { sess with state := otr'.applyToSessionState taken } }

/-- Pure relation for the message-encryption branch: produces `SignalMessage` when no pending
pre-key is present, or checks expiry against `x.now` and wraps a `PreKeySignalMessage`. -/
@[expose] def EncEncryptStep (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8))) : Prop :=
  match sess.pendingPreKey with
  | none =>
    ∃ sm, execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext none x.rest) otr =
        .ok (sm, otr') ∧ m = .signalMessage sm
  | some items =>
    ∃ ts expiry sm, SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts ∧
      ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry ∧ expiry.lt x.now = false ∧
      execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
          (serializeAddrVals (serviceIdParse uuidParse) x.loc.val x.rem.val) x.rest) otr =
        .ok (sm, otr') ∧
      m = .preKeySignalMessage (PreKeySignalMessage.new otr'.sessionVersion
        sess.localRegistrationId items.preKeyId items.signedPreKeyId
        (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload))
        items.baseKey otr'.localIdentityKey sm)

/-! ## Seam States -/

abbrev loadOk (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) : TraceEvent :=
  loadEvent encRecord x.rem.val (.ok (some r))

/-- Stack slots shared across `Otr`..`Cm`: `takenRecord`, `SessionState` spill, and drop flags. -/
@[expose] def takenSlots (A : RustAlloc) (sp : BitVec 64) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) : SepProp :=
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken)) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8)

/-- Pure protocol facts established up to the `Cm` seam (`Scope r` through `EncEncryptStep`). -/
@[expose] def StepsThroughEncrypt (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (S : SpqrModel)
    (uuidParse : UuidParser) (x : WithStoresEncGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8))) :
    Prop :=
  r.currentSession = some sess ∧ Scope r ∧
    execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
    taken.remoteIdentity = some k ∧ EncEncryptStep C S uuidParse x sess otr m otr'

/-- Stack slots shared across `Cm`..`Apply`: `takenRecord`, updated `otr'`, identity key `k`,
and `CiphertextMessage` `m`. -/
@[expose] def cmSlots (A : RustAlloc) (sp : BitVec 64) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage) : SepProp :=
  takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m)

@[expose] def okAnswers (r : SessionRecord (List (BitVec 8))) (c : IdentityChange) :
    StoreAnswers (List (BitVec 8)) Unit :=
  { loadSession := .ok (some r), isTrustedIdentity := .ok true, saveIdentity := .ok c,
    storeSession := .ok () }

end CryptoVerification.LibsignalPublicApi.MessageEncrypt

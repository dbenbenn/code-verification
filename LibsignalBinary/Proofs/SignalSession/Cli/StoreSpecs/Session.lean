/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import LibsignalBinary.Proofs.CodeLayout

/-!
# Function-Level Specifications for CLI `SessionFiles` Callbacks

Separation-logic specifications over `DirGhost` (`Cli/Kits.lean`) for the `SessionFiles`
(`cli/src/stores.rs`, `Dir` at offset `0`) `dyn SessionStore` callbacks:
- `sessLoadShimSpec` (24-byte box) and `sessStoreShimSpec` (32-byte box): `async_trait` shims;
- `sessDeserializeSpec` and `sessDeserializeExtSpec`: allocator-parametric `SessionRecord::deserialize`
  contracts over a record scope `Scope`;
- `sessLoadPollSpec` (`0x350` frame, 368-byte sret): reads `sessions/<peer>` under `SessFileWf Scope`
  and decodes nonempty records via `SessionRecord::deserialize`;
- `sessStorePollSpec` (`0xd0` frame, 48-byte sret): serializes canonical records via
  `SessionRecord::serialize` and buffers `(addressText, encodeRecord r)` via `Dir::put`.
-/

public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoGames.LibsignalSessionApi

/-! ## Entry points -/

abbrev sessLoadShimName : String :=
  "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session"

abbrev sessLoadPollName : String :=
  "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"

abbrev sessStoreShimName : String :=
  "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session"

abbrev sessStorePollName : String :=
  "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"

abbrev recordDeserializeName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::deserialize"

abbrev recordSerializeName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::serialize"

/-- The `load_session` future box at `box` (24 bytes): `self` @0, the address @8, the state
byte @0x10, 7 bytes uninitialized. The shape of `hookSessionStoreSpec`'s `loadBoxAt`. -/
@[expose] def sessLoadBoxAt (box self addrA : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₈ st) ∗
    memRegion (box + 0x11#64) 7

/-- The `store_session` future box at `box` (32 bytes): `self` @0, the address @8, the record
@0x10, the state byte @0x18, 7 bytes uninitialized. The shape of `hookSessionStoreSpec`'s
`storeBoxAt`. -/
@[expose] def sessStoreBoxAt (box self addrA recA : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ recA) ∗
    ((box + 0x18#64) ↦₈ st) ∗ memRegion (box + 0x19#64) 7

/-- `sessLoadBoxAt` agrees with `(hookSessionStoreSpec A b).loadBoxAt`. -/
theorem sessLoadBoxAt_eq_hook (A : RustAlloc) (b : BitVec 64) :
    sessLoadBoxAt = (hookSessionStoreSpec A b).loadBoxAt := rfl

/-- `sessStoreBoxAt` agrees with `(hookSessionStoreSpec A b).storeBoxAt`. -/
theorem sessStoreBoxAt_eq_hook (A : RustAlloc) (b : BitVec 64) :
    sessStoreBoxAt = (hookSessionStoreSpec A b).storeBoxAt := rfl

/-! ## The shims -/

/-- A session file the CLI can load: empty (no session), or the encoding of a record in the
scope `Scope`. -/
@[expose] def SessFileWf (Scope : SessionRecord (List (BitVec 8)) → Prop) (bs : List (BitVec 8)) : Prop :=
  bs = [] ∨ ∃ r, E2E.Record.encodeRecord r = bs ∧ Scope r

/-- The answer of the load poll for the answer `gr` of `Dir::get`: an error stays an error,
an empty file is no session, and nonempty bytes are the record they encode (in `Scope`). -/
@[expose] def SessLoadAns (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    Except Unit (List (BitVec 8)) → Except Unit (Option (SessionRecord (List (BitVec 8)))) → Prop
  | .error _, ans => ans = .error ()
  | .ok [], ans => ans = .ok none
  | .ok (b :: bs), ans =>
    ∃ r, ans = .ok (some r) ∧ E2E.Record.encodeRecord r = b :: bs ∧ Scope r

/-- `SessLoadAns` is `Kits.loadSession`'s step `get(…).bind (record dec)` for any decoder `dec`
that inverts `encodeRecord` on `Scope` (the answer relation of the CLI kit). -/
theorem sessLoadAns_bind {ε : Type} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {dec : List (BitVec 8) → Except ε (SessionRecord (List (BitVec 8)))}
    (hdec : ∀ r, Scope r → dec (E2E.Record.encodeRecord r) = .ok r)
    {gr : Except Unit (List (BitVec 8))} {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (h : SessLoadAns Scope gr ans) : ans = gr.bind (record dec) := by
  match gr, h with
  | .error (), h => exact h
  | .ok [], h => exact h
  | .ok (b :: bs), ⟨r, hans, henc, hsc⟩ =>
    subst hans
    have hd : dec (b :: bs) = .ok r := henc ▸ hdec r hsc
    show Except.ok (some r) = record dec (b :: bs)
    simp only [record, hd]

/-- The load poll's sret (368 bytes) for the answer `ans`:
* `Ok(Some r)`: the record moved in (`sessionRecordAt`; the caller tells it apart by word 0, the
  record's `previous_sessions` capacity, below `2^63`);
* `Ok(None)`: word 0 `-1`, the rest uninitialized;
* `Err`: word 0 `-2`, `Dir::get`'s `InvalidState("read", _)` at `out + 8`, the rest uninitialized. -/
@[expose] def sessLoadOutAt (A : RustAlloc) (out : BitVec 64) :
    Except Unit (Option (SessionRecord (List (BitVec 8)))) → SepProp
  | .ok (some r) => ∃∗ g : RecordGhost, sessionRecordAt A out g r
  | .ok none => (out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (out + 8#64) 360
  | .error () =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ speAt A (utf8 "read") (out + 8#64) .invalidState ∗
      memRegion (out + 0x38#64) 312

/-! ## The polls -/

/-- Ghost of a `load_session` poll call: the kit's call (future box, sret, address), the
`SessionFiles` pointer (`self`, the `Dir` at offset 0) and its `Dir`. -/
structure SessLoadPollGhost where
  call : LoadPollCall
  self : BitVec 64
  dir : DirGhost

/-- Ghost of a `store_session` poll call: the kit's call (future box, sret, address, record), the
`SessionFiles` pointer and its `Dir`. -/
structure SessStorePollGhost where
  call : StorePollCall
  self : BitVec 64
  dir : DirGhost

/-- `store_session`'s update in the pure model (`Kits.storeSession`) with the encoder
`.ok ∘ encodeRecord`: the answer `Ok`, the `Dir` of `sessStorePollSpec`'s post. -/
theorem storeSession_encodeRecord (d : DirGhost) (a : AddrVal)
    (r : SessionRecord (List (BitVec 8))) :
    storeSession (ε := Unit) (fun r => .ok (E2E.Record.encodeRecord r)) d a r =
      (.ok (), d.put (addressText a) (E2E.Record.encodeRecord r)) := rfl

end CryptoVerification.SignalSession.Cli

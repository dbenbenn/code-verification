/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.CodeLayout

/-!
# Function-Level Specifications for CLI `IdentityFiles` Callbacks

Separation-logic specifications over `DirGhost` (`Cli/Kits.lean`) for the `IdentityFiles`
(`cli/src/stores.rs`, `peers` at `+0x28`) `dyn IdentityKeyStore` callbacks on the SM path:
- `idSaveShimSpec` and `idTrustShimSpec`: 32-byte `async_trait` future-boxing shims;
- `idTrustPollSpec` (`0xc0` frame, 48-byte sret): reads `identities/<name>` under `IdFileWf`,
  trusting on first use (empty file) or comparing `IdentityKey::decode` against `key`;
- `idSavePollSpec` (`0xd0` frame, 48-byte sret): reads any existing pinned key under `IdFileWf`,
  stores `key.serialize()` via `Dir::put`, and reports whether an existing key was replaced.

Allocation failures trap via `onPanic` (`allocFailedIn s0 sf ∧ s0.trace <+: sf.trace`).
-/

public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoGames.LibsignalSessionApi CryptoVerification.RecordCodecs

/-! ## Entry points -/

abbrev idSaveShimName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity"

abbrev idSavePollName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"

abbrev idTrustShimName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"

abbrev idTrustPollName : String :=
  "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"

/-- The `save_identity` future box at `box` (32 bytes): `self` @0, the address @8, the key
@0x10, the state byte @0x18, 7 bytes uninitialized. The shape of `hookIdentityStoreSpecAt`'s
`saveBoxAt`. -/
@[expose] def idSaveBoxAt (box self addrA keyA : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ keyA) ∗
    ((box + 0x18#64) ↦₈ st) ∗ memRegion (box + 0x19#64) 7

/-- The `is_trusted_identity` future box at `box` (32 bytes): as `idSaveBoxAt`, plus the
direction byte @0x19, 6 bytes uninitialized. The shape of `hookIdentityStoreSpecAt`'s
`trustBoxAt`. -/
@[expose] def idTrustBoxAt (box self addrA keyA : BitVec 64) (st d : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ keyA) ∗
    ((box + 0x18#64) ↦₈ st) ∗ ((box + 0x19#64) ↦₈ d) ∗ memRegion (box + 0x1a#64) 6

/-- The CLI's save box is `hookIdentityStoreSpecAt`'s (at any vtable address). -/
theorem idSaveBoxAt_eq_hook (A : RustAlloc) (b id_vt : BitVec 64) :
    idSaveBoxAt = (hookIdentityStoreSpecAt A b id_vt).saveBoxAt := rfl

/-- The CLI's trust box is `hookIdentityStoreSpecAt`'s (at any vtable address). -/
theorem idTrustBoxAt_eq_hook (A : RustAlloc) (b id_vt : BitVec 64) :
    idTrustBoxAt = (hookIdentityStoreSpecAt A b id_vt).trustBoxAt := rfl

/-! ## The shims -/

/-- An identity file the CLI can read: empty (no pinned key), or `k.serialize` (33 bytes:
type byte `0x05` and the key) for some identity key `k`. -/
@[expose] def IdFileWf (bs : List (BitVec 8)) : Prop :=
  bs = [] ∨ ∃ k : IdentityKey, k.serialize = bs

/-- The pinned key as the polls see it, for the answer `gr` of `Dir::get`: an error stays an
error, an empty file is no key, and nonempty bytes are the key they serialize. -/
@[expose] def IdPeerAns : Except Unit (List (BitVec 8)) → Except Unit (Option IdentityKey) → Prop
  | .error _, p => p = .error ()
  | .ok [], p => p = .ok none
  | .ok (b :: bs), p => ∃ k : IdentityKey, p = .ok (some k) ∧ k.serialize = b :: bs

/-- `IdPeerAns` is `IdGhost.peer`'s step `get(…).bind (record decodeIdentityKey)`. -/
theorem idPeerAns_bind {gr : Except Unit (List (BitVec 8))} {p : Except Unit (Option IdentityKey)}
    (h : IdPeerAns gr p) : p = gr.bind (record decodeIdentityKey) := by
  match gr, h with
  | .error (), h => exact h
  | .ok [], h => exact h
  | .ok (b :: bs), ⟨k, hp, hser⟩ =>
    subst hp
    have hd : decodeIdentityKey (b :: bs) = .ok k := hser ▸ decodeIdentityKey_serialize k
    show Except.ok (some k) = record decodeIdentityKey (b :: bs)
    simp only [record, hd]

/-- `is_trusted_identity`'s answer from the pinned key: trusted on first use, then pinned. -/
@[expose] def idTrustOf : Except Unit (Option IdentityKey) → IdentityKey → Except Unit Bool
  | .error _, _ => .error ()
  | .ok none, _ => .ok true
  | .ok (some known), k => .ok (decide (known = k))

/-- `save_identity`'s answer from the pinned key: `ReplacedExisting` iff a different key was
pinned. -/
@[expose] def idSaveOf : Except Unit (Option IdentityKey) → IdentityKey → Except Unit IdentityChange
  | .error _, _ => .error ()
  | .ok none, _ => .ok .newOrUnchanged
  | .ok (some known), k => .ok (if known = k then .newOrUnchanged else .replacedExisting)

/-- `save_identity`'s `peers` after the poll: `put(name, key.serialize())` once the pinned key
was read; unchanged on an error (the `?` returns first). -/
@[expose] def idSavePeers (d : DirGhost) (name : List (BitVec 8)) (k : IdentityKey) :
    Except Unit (Option IdentityKey) → DirGhost
  | .ok _ => d.put name k.serialize
  | .error _ => d

theorem IdGhost.trusted_eq_idTrustOf (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (a : AddrVal)
    (k : IdentityKey) : g.trusted rd F0 a k = idTrustOf (g.peer rd F0 a) k := by
  unfold IdGhost.trusted
  rcases g.peer rd F0 a with e | (_ | known) <;> rfl

theorem IdGhost.saveAns_eq_idSaveOf (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (a : AddrVal)
    (k : IdentityKey) : g.saveAns rd F0 a k = idSaveOf (g.peer rd F0 a) k := by
  unfold IdGhost.saveAns
  rcases g.peer rd F0 a with e | (_ | known) <;> rfl

theorem IdGhost.saveUpd_eq_idSavePeers (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (a : AddrVal)
    (k : IdentityKey) :
    g.saveUpd rd F0 a k = { g with peers := idSavePeers g.peers a.name k (g.peer rd F0 a) } := by
  unfold IdGhost.saveUpd
  rcases g.peer rd F0 a with e | p <;> rfl

/-- The trust poll's answer is the pure model's (`IdGhost.trusted`) on the non-OOM path. -/
theorem IdGhost.trusted_of_peerAns {rd : ReadRule} {F0 : FsFiles} {g : IdGhost} {a : AddrVal}
    {k : IdentityKey} {p : Except Unit (Option IdentityKey)}
    (h : IdPeerAns (g.peers.get rd F0 a.name) p) : g.trusted rd F0 a k = idTrustOf p k := by
  rw [IdGhost.trusted_eq_idTrustOf, idPeerAns_bind h]; rfl

/-- The save poll's answer and update are the pure model's on the non-OOM path. -/
theorem IdGhost.saveAns_of_peerAns {rd : ReadRule} {F0 : FsFiles} {g : IdGhost} {a : AddrVal}
    {k : IdentityKey} {p : Except Unit (Option IdentityKey)}
    (h : IdPeerAns (g.peers.get rd F0 a.name) p) :
    g.saveAns rd F0 a k = idSaveOf p k ∧
      g.saveUpd rd F0 a k = { g with peers := idSavePeers g.peers a.name k p } := by
  rw [IdGhost.saveAns_eq_idSaveOf, IdGhost.saveUpd_eq_idSavePeers, idPeerAns_bind h]
  exact ⟨rfl, rfl⟩

/-- `save_identity`'s `put` keeps the file invariant. -/
theorem idFileWf_put {rd : ReadRule} {F : FsFiles} {d : DirGhost} {n : List (BitVec 8)}
    (k : IdentityKey) (h : ∀ m bs, d.get rd F m = .ok bs → IdFileWf bs) :
    ∀ m bs, (d.put n k.serialize).get rd F m = .ok bs → IdFileWf bs := by
  intro m bs hm
  by_cases hmn : m = n
  · subst hmn
    rw [DirGhost.get_put_self] at hm
    exact .inr ⟨k, Except.ok.inj hm⟩
  · rw [DirGhost.get_put_ne rd F d hmn] at hm
    exact h m bs hm

/-! ## The polls' srets -/

/-- The trust poll's sret (48 bytes) for the answer `ans`: `Ok(t)` = word 0 `-2`, byte 8 `t`,
the rest uninitialized (= `trustPollOutAt`'s `Ok` arm, `idTrustOutAt_ok`); `Err` = `Dir::get`'s
`InvalidState("read", _)` moved in. -/
@[expose] def idTrustOutAt (A : RustAlloc) (out : BitVec 64) : Except Unit Bool → SepProp
  | .ok t =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₈ (if t then 1#8 else 0#8)) ∗
      memRegion (out + 9#64) 39
  | .error () => speAt A (utf8 "read") out .invalidState

/-- The save poll's sret (48 bytes) for the answer `ans`: `Ok(c)` = word 0 `-2`, `u32` at 8
`replaced`, the rest uninitialized (= `savePollOutAt`'s `Ok` arm, `idSaveOutAt_ok`); `Err` =
`Dir::get`'s `InvalidState("read", _)` moved in. -/
@[expose] def idSaveOutAt (A : RustAlloc) (out : BitVec 64) : Except Unit IdentityChange → SepProp
  | .ok c =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
      memRegion (out + 0xc#64) 36
  | .error () => speAt A (utf8 "read") out .invalidState

theorem idTrustOutAt_ok (A : RustAlloc) (b out : BitVec 64) (t : Bool) :
    idTrustOutAt A out (.ok t) = trustPollOutAt b out (.ok t) := rfl

theorem idSaveOutAt_ok (A : RustAlloc) (b out : BitVec 64) (c : IdentityChange) :
    idSaveOutAt A out (.ok c) = savePollOutAt b out (.ok c) := rfl

/-! ## The polls -/

/-- Ghost of a `save_identity` / `is_trusted_identity` poll call: the kit's call (future box,
sret, address, key), the `IdentityFiles` pointer (`self`; `peers` at `self + 0x28`) and the
`peers` `Dir`. -/
structure IdPollGhost where
  call : IdentityPollCall
  self : BitVec 64
  peers : DirGhost

end CryptoVerification.SignalSession.Cli

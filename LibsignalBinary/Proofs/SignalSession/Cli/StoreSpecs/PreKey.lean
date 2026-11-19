/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeySpec -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym

/-!
# Function-Level Specifications for CLI Pre-Key Store Callbacks

Separation-logic specifications over `DirGhost` (`Cli/Kits.lean`) for `SignedPreKeyFiles`,
`OneTimePreKeyFiles`, and `KyberPreKeyFiles` (`cli/src/stores.rs`):
- `pkShimSpec` (16-byte future box) for `get_signed_pre_key`, `get_pre_key`, `remove_pre_key`, and
  `get_kyber_pre_key`, plus `kpkMarkShimSpec` (32-byte future box) for `mark_kyber_pre_key_used`;
- `spkGetPollSpec`, `pkGetPollSpec`, and `kpkGetPollSpec`: read decimal-ID files via `Dir::get`,
  decode nonempty payloads, and refine `getSignedPreKey`, `getPreKey`, and `KyberGhost.get`;
- `pkRemovePollSpec`: clears nonempty entries via `Dir::put` (`removePreKey_eq_pkRemoveOf`), and
  `dropSpeWordSpec` drops payload-free missing-ID `SignalProtocolError` tags (`13`, `14`).
-/

public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## Entry points -/

abbrev spkGetShimName : String :=
  "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key"

abbrev spkGetPollName : String :=
  "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}"

abbrev pkGetShimName : String :=
  "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key"

abbrev pkGetPollName : String :=
  "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"

abbrev pkRemoveShimName : String :=
  "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key"

abbrev pkRemovePollName : String :=
  "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"

abbrev kpkGetShimName : String :=
  "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key"

abbrev kpkGetPollName : String :=
  "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"

abbrev kpkMarkShimName : String :=
  "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used"

abbrev kpkMarkPollName : String :=
  "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"

/-- A pre-key `get` / `remove` future box at `box` (16 bytes): `self` @0, the key id (`u32`) @8,
the state byte @0xc, 3 bytes uninitialized. -/
@[expose] def pkBoxAt (box self : BitVec 64) (id : BitVec 32) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₃₂ id) ∗ ((box + 0xc#64) ↦₈ st) ∗ memRegion (box + 0xd#64) 3

/-- The `mark_kyber_pre_key_used` future box at `box` (32 bytes): `self` @0, the base key pointer
@8, the key id @0x10, the signed pre-key id @0x14, the state byte @0x18, 7 bytes
uninitialized. -/
@[expose] def kpkMarkBoxAt (box self baseKeyA : BitVec 64) (id signedId : BitVec 32) (st : BitVec 8) :
    SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ baseKeyA) ∗ ((box + 0x10#64) ↦₃₂ id) ∗
    ((box + 0x14#64) ↦₃₂ signedId) ∗ ((box + 0x18#64) ↦₈ st) ∗ memRegion (box + 0x19#64) 7

/-! ## The shims -/

/-- Arguments of a pre-key `get` / `remove` shim: `self` (`x0`) and the key id (`w1`). -/
structure PkShimCall where
  self : BitVec 64
  id : BitVec 32

/-- Arguments of the `mark_kyber_pre_key_used` shim: `self` (`x0`), the key id (`w1`), the
signed pre-key id (`w2`), the base key pointer (`x3`). -/
structure KpkMarkShimCall where
  self : BitVec 64
  id : BitVec 32
  signedId : BitVec 32
  baseKeyA : BitVec 64

/-- A `get` poll's answer, as the binary distinguishes it: the record, `Dir::get`'s error,
the decoder's error, or an empty file (the missing-id error). -/
inductive PkAns (α : Type) where
  | found (r : α)
  | readErr
  | decodeErr (e : SignalProtocolError)
  | missing

/-- The answer for `Dir::get`'s answer `gr` and the decoder `dec`: an error stays an error, an
empty file is missing, nonempty bytes are decoded. -/
@[expose] def pkAnsOf {α : Type} (dec : List (BitVec 8) → Except SignalProtocolError α) :
    Except Unit (List (BitVec 8)) → PkAns α
  | .error _ => .readErr
  | .ok [] => .missing
  | .ok (b :: bs) =>
    match dec (b :: bs) with
    | .ok r => .found r
    | .error e => .decodeErr e

/-- `get_kyber_pre_key`'s answer from its two directories' answers: the second is used only when
the first file is empty. -/
@[expose] def kpkAnsOf {α : Type} : PkAns α → PkAns α → PkAns α
  | .missing, a2 => a2
  | a1, _ => a1

/-- The pure model's view of an answer: every non-record answer is an error. -/
@[expose] def PkAns.toExcept {α : Type} : PkAns α → Except Unit α
  | .found r => .ok r
  | _ => .error ()

/-- `record`'s view of an answer (`Kits.lean`): an empty file is no record. -/
@[expose] def PkAns.toRecord {α : Type} : PkAns α → Except Unit (Option α)
  | .found r => .ok (some r)
  | .missing => .ok none
  | _ => .error ()

/-- `pkAnsOf` refines `get(…).bind (record dec)`. -/
theorem pkAnsOf_toRecord {α : Type} (dec : List (BitVec 8) → Except SignalProtocolError α)
    (gr : Except Unit (List (BitVec 8))) :
    gr.bind (record dec) = (pkAnsOf dec gr).toRecord := by
  rcases gr with _ | _ | ⟨b, bs⟩
  · rfl
  · rfl
  · show record dec (b :: bs) = (pkAnsOf dec (.ok (b :: bs))).toRecord
    rcases h : dec (b :: bs) with e | r <;> simp [record, pkAnsOf, PkAns.toRecord, h]

/-- `get_pre_key`'s pure model is the answer's `toExcept`. -/
theorem getPreKey_eq (rd : ReadRule) (F0 : FsFiles) (d : DirGhost) (id : BitVec 32) :
    getPreKey rd F0 d id = (pkAnsOf PreKeyRecord.deserialize (d.get rd F0 (keyName id))).toExcept := by
  unfold getPreKey
  rw [pkAnsOf_toRecord]
  cases pkAnsOf PreKeyRecord.deserialize (d.get rd F0 (keyName id)) <;> rfl

/-- `get_signed_pre_key`'s pure model is the answer's `toExcept`. -/
theorem getSignedPreKey_eq (rd : ReadRule) (F0 : FsFiles) (d : DirGhost) (id : BitVec 32) :
    getSignedPreKey rd F0 d id =
      (pkAnsOf SignedPreKeyRecord.deserialize (d.get rd F0 (keyName id))).toExcept := by
  unfold getSignedPreKey
  rw [pkAnsOf_toRecord]
  cases pkAnsOf SignedPreKeyRecord.deserialize (d.get rd F0 (keyName id)) <;> rfl

/-- `get_kyber_pre_key`'s pure model is the combined answer's `toExcept`. -/
theorem KyberGhost.get_eq (rd : ReadRule) (F0 : FsFiles) (g : KyberGhost) (id : BitVec 32) :
    g.get rd F0 id =
      (kpkAnsOf (pkAnsOf KyberPreKeyRecord.deserialize (g.oneTime.get rd F0 (keyName id)))
        (pkAnsOf KyberPreKeyRecord.deserialize (g.lastResort.get rd F0 (keyName id)))).toExcept := by
  unfold KyberGhost.get
  generalize g.oneTime.get rd F0 (keyName id) = g1
  generalize g.lastResort.get rd F0 (keyName id) = g2
  show (g1.bind (record KyberPreKeyRecord.deserialize)).bind _ = _
  rw [pkAnsOf_toRecord]
  cases pkAnsOf KyberPreKeyRecord.deserialize g1 with
  | missing =>
    show (g2.bind (record KyberPreKeyRecord.deserialize)).bind _ = _
    rw [pkAnsOf_toRecord]
    cases pkAnsOf KyberPreKeyRecord.deserialize g2 <;> rfl
  | _ => rfl

/-! ## The `get` srets -/

/-- A `get` poll's sret (`size` bytes) for the answer `ans`, with the record layout `resAt`
and the missing-id SPE index `w`:
* `found r`: the decoder's `Ok` result moved in (`resAt out (.ok r)`);
* `decodeErr e`: the decoder's `Err` result moved in (`resAt out (.error e)`);
* `readErr`: `Dir::get`'s `InvalidState("read", _)` behind `errTag` (`errResultAt`);
* `missing`: `errTag`, `speWord w`, the rest uninitialized. -/
@[expose] def pkAnsAt {α : Type} (A : RustAlloc)
    (resAt : RustAlloc → BitVec 64 → Except SignalProtocolError α → SepProp)
    (size w : Nat) (out : BitVec 64) : PkAns α → SepProp
  | .found r => resAt A out (.ok r)
  | .decodeErr e => resAt A out (.error e)
  | .readErr => errResultAt A (utf8 "read") size out .invalidState
  | .missing =>
    (out ↦₆₄ errTag) ∗ ((out + 8#64) ↦₆₄ speWord w) ∗ memRegion (out + 0x10#64) (size - 16)

/-- `get_signed_pre_key`'s sret (88 bytes; `InvalidSignedPreKeyId` = SPE index 14). -/
abbrev spkAnsAt (A : RustAlloc) (out : BitVec 64) : PkAns SignedPreKeyRecord → SepProp :=
  pkAnsAt A signedPreKeyResultAt 88 14 out

/-- `get_pre_key`'s sret (56 bytes; `InvalidPreKeyId` = SPE index 13). -/
abbrev pkGetAnsAt (A : RustAlloc) (out : BitVec 64) : PkAns PreKeyRecord → SepProp :=
  pkAnsAt A preKeyResultAt 56 13 out

/-- `get_kyber_pre_key`'s sret (88 bytes; `InvalidKyberPreKeyId` = SPE index 15). -/
abbrev kpkAnsAt (A : RustAlloc) (out : BitVec 64) : PkAns KyberPreKeyRecord → SepProp :=
  pkAnsAt A kyberPreKeyResultAt 88 15 out

/-! ## `remove_pre_key`'s answer -/

/-- `remove_pre_key`'s step on `Dir::get`'s answer `gr`: an error is returned before any change,
an empty file is left alone, a nonempty one is emptied. -/
@[expose] def pkRemoveOf (d : DirGhost) (n : List (BitVec 8)) :
    Except Unit (List (BitVec 8)) → Except Unit Unit × DirGhost
  | .error _ => (.error (), d)
  | .ok [] => (.ok (), d)
  | .ok (_ :: _) => (.ok (), d.put n [])

/-- `remove_pre_key`'s pure model is `pkRemoveOf` on `Dir::get`'s answer. -/
theorem removePreKey_eq_pkRemoveOf (rd : ReadRule) (F0 : FsFiles) (d : DirGhost)
    (id : BitVec 32) :
    removePreKey rd F0 d id = pkRemoveOf d (keyName id) (d.get rd F0 (keyName id)) := by
  unfold removePreKey
  rcases d.get rd F0 (keyName id) with _ | _ | ⟨b, bs⟩ <;> rfl

/-- `remove_pre_key`'s sret (48 bytes): `Ok(())` = word 0 `-2`, the rest uninitialized;
`Err` = `Dir::get`'s `InvalidState("read", _)` moved in. -/
@[expose] def pkRemoveOutAt (A : RustAlloc) (out : BitVec 64) : Except Unit Unit → SepProp
  | .ok () => (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (out + 8#64) 40
  | .error () => speAt A (utf8 "read") out .invalidState

/-! ## The polls -/

/-- Ghost of a pre-key `get` / `remove` poll call: the future box, the sret, the store pointer
(`self`, its `Dir` at `self`), the key id, and the `Dir`. -/
structure PkPollGhost where
  fut : BitVec 64
  out : BitVec 64
  self : BitVec 64
  id : BitVec 32
  dir : DirGhost

/-- What `Dir::get` needs of the key's file name: the name (`decimal(id)`) and the `Dir`
path below `2^32`, and `pathOk` of `<path>/<id>` (`read_file`'s domain). The name bound holds
(at most 10 digits); it is stated here so that the hops need not prove it. -/
@[expose] def PkNameOk (pathOk : List (BitVec 8) → Prop) (d : DirGhost) (id : BitVec 32) : Prop :=
  (keyName id).length < 2 ^ 32 ∧ d.path.length < 2 ^ 32 ∧ pathOk (pathOf d.path (keyName id))

/-- What the decoders need of the key's file: every answer `Ok bs` that `Dir::get` would give
on the files `F` has fewer than `2^32` bytes (`preKeyDeserializeSpec` /
`decodeKyberPreKeySpec`). -/
@[expose] def PkSizeOk (rd : ReadRule) (F : FsFiles) (d : DirGhost) (id : BitVec 32) : Prop :=
  ∀ bs, d.get rd F (keyName id) = .ok bs → bs.length < 2 ^ 32

/-- Ghost of a `get_kyber_pre_key` poll call: as `PkPollGhost`, with both `Dir`s (`one_time` at
`self`, `last_resort` at `self + 0x28`). -/
structure KpkPollGhost where
  fut : BitVec 64
  out : BitVec 64
  self : BitVec 64
  id : BitVec 32
  kg : KyberGhost

/-- Ghost of a drop of a payload-free SPE: its address and SPE index. -/
structure DropSpeWordGhost where
  a : BitVec 64
  w : Nat

end CryptoVerification.SignalSession.Cli

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
public import LibsignalBinary.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# In-Memory Session Store Definitions

Symbol names, `.data.rel.ro` future vtable and relocation guards, boxed-future layouts
(`inMemLoadBoxAt`, `inMemStoreBoxAt`), and heap representation predicates (`InMemSessState`,
`singleSessionStoreAt`) for `InMemSessionStore`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.E2E.InMem.SessionStoreImpl

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.E2E.Record.Serialization (CanonSession CanonRecord)

/-! ## Symbol Names and Offset Guards -/

abbrev inMemLoadShimName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session"

abbrev inMemStoreShimName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session"

abbrev inMemLoadPollName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"

abbrev inMemStorePollName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"

/-- Shared ICF-folded no-op future `drop_glue` symbol. -/
abbrev inMemFutDropName : String :=
  "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"

abbrev inMemSessDropName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::storage::inmem::InMemSessionStore> [local#1]"

abbrev noAllocShimName : String :=
  "__rustc::__rust_no_alloc_shim_is_unstable_v2"

abbrev rustAllocName : String := "__rustc::__rust_alloc"

abbrev rustDeallocName : String := "__rustc::__rust_dealloc"

abbrev handleAllocErrorName : String :=
  "alloc::alloc::handle_alloc_error"

abbrev inMemLoadShimStack : Nat := allocHookStack + 32

abbrev inMemStoreShimStack : Nat := allocHookStack + 48

abbrev inMemLoadPollStack : Nat := loadSessionClosureStack

abbrev inMemStorePollStack : Nat := storeSessionClosureStack

theorem inMemLoadShimStack_le_extHookStack :
    inMemLoadShimStack ≤ LibsignalTripleRatchet.extHookStack := by decide
theorem inMemStoreShimStack_le_extHookStack :
    inMemStoreShimStack ≤ LibsignalTripleRatchet.extHookStack := by decide

abbrev inMemLoadBoxSize : Nat := 24

abbrev inMemStoreBoxSize : Nat := 32

/-! ## `.data.rel.ro` Vtable Byte and Relocation Guards -/

/-- Heap layout of the 24-byte `load_session` boxed future at `box`:
`[self, addrA, state : u8, 7 padding bytes]`. -/
@[expose] def inMemLoadBoxAt (box self addrA : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₈ st) ∗
    memRegion (box + 0x11#64) 7

/-- Heap layout of the 32-byte `store_session` boxed future at `box`:
`[self, addrA, recA, state : u8, 7 padding bytes]`. -/
@[expose] def inMemStoreBoxAt (box self addrA recA : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ recA) ∗
    ((box + 0x18#64) ↦₈ st) ∗ memRegion (box + 0x19#64) 7

theorem inMemLoadBoxAt_memRegion (box self addrA : BitVec 64) (st : BitVec 8) :
    inMemLoadBoxAt box self addrA st ⊢ memRegion box inMemLoadBoxSize := by
  unfold inMemLoadBoxAt inMemLoadBoxSize
  rw [show (24 : Nat) = 8 + (8 + (1 + 7)) from rfl,
    memRegion_split box 8 16 (by decide),
    memRegion_split (box + 8#64) 8 8 (by decide),
    memRegion_split (box + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo8_entails_memRegion _ _)))

theorem inMemStoreBoxAt_memRegion (box self addrA recA : BitVec 64) (st : BitVec 8) :
    inMemStoreBoxAt box self addrA recA st ⊢ memRegion box inMemStoreBoxSize := by
  unfold inMemStoreBoxAt inMemStoreBoxSize
  rw [show (32 : Nat) = 8 + (8 + (8 + (1 + 7))) from rfl,
    memRegion_split box 8 24 (by decide),
    memRegion_split (box + 8#64) 8 16 (by decide),
    memRegion_split (box + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (box + 8#64 + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo8_entails_memRegion _ _))))

/-- Bucket entry predicate for `RawTable<(ProtocolAddress, SessionRecord)>` at `a`, pairing
`protocolAddressAt` at `a` with a canonical in-scope `sessionRecordAt` at `a + 0x20`. -/
@[expose] def sessionRecordBucketEntryAt (A : RustAlloc) (g : AddrGhost)
    (r : SessionRecord (List (BitVec 8))) (a : BitVec 64) : SepProp :=
  ∃∗ G : SessionGhost, ∃∗ ss : Session (List (BitVec 8)),
    ⌜r = ⟨some ss⟩ ∧ RecordInScope r ∧ CanonSession G ss⌝ ∗
    protocolAddressAt A g a ∗
    sessionRecordAt A (a + 0x20#64) ⟨0#64, 8#64, some G⟩ ⟨some ss⟩

/-- Logical state of a single-entry `InMemSessionStore`: SipHash-1-3 keys `(k0, k1)`,
occupied bucket index `k < 4`, peer address ghost `peerG`, and stored `SessionRecord`. -/
structure InMemSessState where
  k0 : BitVec 64
  k1 : BitVec 64
  k : Nat
  peerG : AddrGhost
  record : SessionRecord (List (BitVec 8))

/-- Remote-address precondition requiring `rem` to match the store's peer `peer`. -/
@[expose] def inMemAddrOk (peer : AddrGhost) (rem : AddrVal) : Prop :=
  rem.name = peer.name.bytes ∧ rem.device = peer.device

/-- Separation-logic representation of a single-entry `InMemSessionStore` at `self`
for peer `peer` under record invariant `StoreScope`. -/
@[expose] def singleSessionStoreAt (A : RustAlloc) (peer : AddrGhost)
    (StoreScope : SessionRecord (List (BitVec 8)) → Prop) (self : BitVec 64)
    (st : InMemSessState) : SepProp :=
  ∃∗ g : AddrGhost,
    ⌜st.peerG = peer ∧ peer.name.bytes.length = 36 ∧ st.k < 4 ∧
      g.name.bytes = peer.name.bytes ∧ g.device = peer.device ∧
      StoreScope st.record ∧ RecordInScope st.record⌝ ∗
    table4SingleAt A sessionBucketStride self st.k0 st.k1 st.k
      peer.name.bytes peer.device
      (sessionRecordBucketEntryAt A g st.record)

/-! ## Instruction Decode Lemmas -/

end CryptoVerification.E2E.InMem.SessionStoreImpl

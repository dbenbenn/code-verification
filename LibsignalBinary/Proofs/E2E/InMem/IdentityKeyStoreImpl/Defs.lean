/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Defs
import LibsignalBinary.Proofs.CodeLayout

/-!
# In-Memory Identity Key Store Definitions

Symbol names, code and `.data.rel.ro` vtable offsets, boxed-future layouts (`inMemTrustBoxAt`,
`inMemSaveBoxAt`), and heap representation predicates (`InMemIdState`, `singleIdentityStoreAt`)
for `InMemIdentityKeyStore`.
-/

public section

namespace CryptoVerification.E2E.InMem.IdentityKeyStoreImpl

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.InMem.HashbrownBin

/-! ## Symbol Names and Offset Guards -/

abbrev getIdentityShimName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity"

abbrev saveIdentityShimName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity"

abbrev isTrustedIdentityShimName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"

abbrev getIdentityKeyPairShimName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"

abbrev getLocalRegistrationIdShimName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"

/-- Shared ICF-folded no-op future `drop_glue` symbol. -/
abbrev inMemFutDropName : String :=
  "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"

abbrev inMemIdentityStoreDropName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::storage::inmem::InMemIdentityKeyStore> [local#1]"

abbrev noAllocShimName : String := "__rustc::__rust_no_alloc_shim_is_unstable_v2"

abbrev rustAllocName : String := "__rustc::__rust_alloc"

abbrev rustDeallocName : String := "__rustc::__rust_dealloc"

abbrev handleAllocErrorName : String := "alloc::alloc::handle_alloc_error"

abbrev inMemIdentityShimStack : Nat := identityShimStack

abbrev inMemTrustPollStack : Nat := isTrustedIdentityClosureStack

abbrev inMemSavePollStack : Nat := saveIdentityClosureStack

/-! ## `.data.rel.ro` Future Vtable Guards -/

/-- Heap layout of the 32-byte `is_trusted_identity` boxed future at `box`:
`[self, addrA, keyA, state : u8, dir : u8, 6 padding bytes]`. -/
@[expose] def inMemTrustBoxAt (box self addrA keyA : BitVec 64) (st d : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ keyA) ∗
    ((box + 0x18#64) ↦₈ st) ∗ ((box + 0x19#64) ↦₈ d) ∗
    memRegion (box + 0x1a#64) 6

/-- Heap layout of the 32-byte `save_identity` boxed future at `box`:
`[self, addrA, keyA, state : u8, 7 padding bytes]`. -/
@[expose] def inMemSaveBoxAt (box self addrA keyA : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ keyA) ∗
    ((box + 0x18#64) ↦₈ st) ∗ memRegion (box + 0x19#64) 7

theorem inMemTrustBoxAt_memRegion (box self addrA keyA : BitVec 64) (st d : BitVec 8) :
    inMemTrustBoxAt box self addrA keyA st d ⊢ memRegion box 32 := by
  unfold inMemTrustBoxAt
  rw [show (32 : Nat) = 8 + (8 + (8 + (1 + (1 + 6)))) from rfl,
    memRegion_split box 8 24 (by decide),
    memRegion_split (box + 8#64) 8 16 (by decide),
    memRegion_split (box + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (box + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    memRegion_split (box + 8#64 + 8#64 + 8#64 + 1#64) 1 6 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo8_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo8_entails_memRegion _ _)))))

theorem inMemSaveBoxAt_memRegion (box self addrA keyA : BitVec 64) (st : BitVec 8) :
    inMemSaveBoxAt box self addrA keyA st ⊢ memRegion box 32 := by
  unfold inMemSaveBoxAt
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

/-! ## Store State and Representation Predicate -/

@[simp] theorem identityKey_bytes_length (k : IdentityKey) :
    k.publicKey.bytes.toList.length = 32 :=
  k.publicKey.bytes.toList_length

/-- Logical state of a single-entry `InMemIdentityKeyStore`: SipHash-1-3 keys `(k0, k1)`,
occupied bucket index `k < 4`, peer address ghost `peerG`, and stored `IdentityKey` `peerKey`. -/
structure InMemIdState where
  k0 : BitVec 64
  k1 : BitVec 64
  k : Nat
  peerG : AddrGhost
  peerKey : IdentityKey

/-- Separation-logic representation of a single-entry `InMemIdentityKeyStore` at `self`
for peer `peer` (36-byte UUID name) backed by a 4-bucket `RawTable` at bucket `st.k`. -/
@[expose] def singleIdentityStoreAt (A : RustAlloc) (peer : AddrGhost) (self : BitVec 64)
    (st : InMemIdState) : SepProp :=
  ⌜st.k < 4 ∧ st.peerG = peer ∧ peer.name.bytes.length = 36⌝ ∗
    table4SingleAt A identityBucketStride self st.k0 st.k1 st.k
      st.peerG.name.bytes st.peerG.device
      (identityBucketEntryAt A st.peerG st.peerKey.publicKey.bytes.toList)

end CryptoVerification.E2E.InMem.IdentityKeyStoreImpl

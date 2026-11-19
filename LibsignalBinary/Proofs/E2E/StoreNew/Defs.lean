/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib.VCGen
public import ProofLib.GenDecodes

/-!
# `RandomState::new` and `HashMap::new` TLS lazy-initialization specifications

Specifications and memory-layout predicates for `<InMemSignedPreKeyStore>::new` (`0x127d8`, ICF-shared
with `<InMemSessionStore>::new`) and `<InMemIdentityKeyStore>::new` (`0x0c238`), covering both the
uninitialized (`tag ≠ 1`, calling `hashmap_random_keys`) and initialized (`tag = 1`, incrementing
`word[t + 0]`) paths on the 24-byte thread-local `KEYS` cell at `s.tpidrEl0 + tpoff`.
-/

public section

namespace CryptoVerification.E2E.StoreNew

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet

/-! ## Symbol names, image offsets, and stack budgets -/

/-- Symbol name of the `RandomState::new` SipHash key initializer stub (`0x47f80`). -/
abbrev randomKeysName : String := "std::sys::random::linux::hashmap_random_keys"

/-- Symbol name of `<InMemSignedPreKeyStore>::new` (`0x127d8`, 28 instructions, 112 bytes;
`InMemSessionStore::new` is ICF-folded into this symbol). -/
abbrev inMemSignedPreKeyStoreNewName : String :=
  "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new"

/-- Symbol name of `<InMemIdentityKeyStore>::new` (`0x0c238`, 41 instructions, 164 bytes). -/
abbrev inMemIdentityKeyStoreNewName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new"

/-- Thread-pointer offset (`tpoff = 16 = 0x10`) stored in `got[0]` for the `KEYS` TLS variable. -/
abbrev tlsKeysTpoff : BitVec 64 := 0x10#64

abbrev inMemSessionStoreNewFrame : Nat := 0x20

abbrev inMemSessionStoreNewStack : Nat := inMemSessionStoreNewFrame + extHookStack

abbrev inMemIdentityStoreNewFrame : Nat := 0x30

abbrev inMemIdentityStoreNewStack : Nat := inMemIdentityStoreNewFrame + extHookStack

/-! ## Symbol and offset guards -/

section AddrGuards
open ProofLib.ProgramReflection
set_option maxRecDepth 2000000

end AddrGuards

/-! ## TLS `KEYS` cell, `RandomState`, `HashMap`, and `InMem` store layouts -/

/-- The 24-byte `std::sys::thread_local::native::lazy::Storage<Cell<(u64, u64)>, !>` cell at `t`:
`[t + 0 .. t + 8)` holds `k0`, `[t + 8 .. t + 16)` holds `k1`, `[t + 16]` holds `tag`
(`0#8` = `Uninitialized`, `1#8` = `Alive`), and `[t + 17 .. t + 24)` is 7 bytes of padding. -/
@[expose] def tlsKeysRawAt (t : BitVec 64) (k0 k1 : BitVec 64) (tag : BitVec 8) : SepProp :=
  (t ↦₆₄ k0) ∗ ((t + 8#64) ↦₆₄ k1) ∗ ((t + 16#64) ↦₈ tag) ∗ memRegion (t + 17#64) 7

/-- Initialized 24-byte TLS `KEYS` cell (`tag = 1#8`, `State::Alive`) holding next keys `(k0, k1)`. -/
@[expose] def tlsKeysInitAt (t : BitVec 64) (k0 k1 : BitVec 64) : SepProp :=
  tlsKeysRawAt t k0 k1 1#8

/-- Uninitialized 24-byte TLS `KEYS` cell (`tag ≠ 1#8`, e.g. `tag = 0#8` for `State::Uninitialized`). -/
@[expose] def tlsKeysUninitAt (t : BitVec 64) : SepProp :=
  ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ tag : BitVec 8,
    ⌜tag ≠ 1#8⌝ ∗ tlsKeysRawAt t k0 k1 tag

/-- Combined 24-byte TLS `KEYS` cell predicate parameterized by `Option (BitVec 64 × BitVec 64)`:
`none` = uninitialized (`tag ≠ 1#8`), `some (k0, k1)` = initialized (`tag = 1#8`) holding `(k0, k1)`. -/
@[expose] def tlsKeysAt (t : BitVec 64) : Option (BitVec 64 × BitVec 64) → SepProp
  | none => tlsKeysUninitAt t
  | some (k0, k1) => tlsKeysInitAt t k0 k1

/-- `std::hash::random::RandomState { k0, k1 }` (`16` bytes at `p`). -/
@[expose] def randomStateAt (p : BitVec 64) (k0 k1 : BitVec 64) : SepProp :=
  (p ↦₆₄ k0) ∗ ((p + 8#64) ↦₆₄ k1)

/-- Empty `hashbrown::raw::RawTableInner` (`32` bytes at `out`):
`ctrl = ctrlPtr` at `+0`, `bucket_mask = 0` at `+8`, `growth_left = 0` at `+16`, `items = 0` at `+24`. -/
@[expose] def emptyRawTableAt (ctrlPtr : BitVec 64) (out : BitVec 64) : SepProp :=
  (out ↦₆₄ ctrlPtr) ∗ ((out + 8#64) ↦₆₄ 0#64) ∗
    ((out + 16#64) ↦₆₄ 0#64) ∗ ((out + 24#64) ↦₆₄ 0#64)

/-- Empty `HashMap<K, V, RandomState>` (`48` bytes at `out`):
`emptyRawTableAt ctrlPtr out` (`32` bytes at `+0..+32`) followed by `randomStateAt (out + 32#64) k0 k1`
(`16` bytes at `+32..+48`). Also the full representation of a newly constructed
`InMemSessionStore` or `InMemSignedPreKeyStore`. -/
@[expose] def emptyHashMapAt (ctrlPtr : BitVec 64) (out : BitVec 64) (k0 k1 : BitVec 64) : SepProp :=
  emptyRawTableAt ctrlPtr out ∗ randomStateAt (out + 32#64) k0 k1

/-- Newly constructed `InMemIdentityKeyStore` (`120` bytes at `out`):
* `+0x00..+0x30` (`48` B): `emptyHashMapAt ctrlPtr out k0 k1` (`identities` table)
* `+0x30..+0x70` (`64` B): `(out + 48#64) ↦ₛ kpBytes` (`key_pair : IdentityKeyPair`)
* `+0x70..+0x74` (`4` B):  `(out + 112#64) ↦₃₂ regId` (`registration_id : u32`)
* `+0x74..+0x78` (`4` B):  `memRegion (out + 116#64) 4` (struct trailing padding) -/
@[expose] def emptyIdentityKeyStoreAt (ctrlPtr : BitVec 64) (out : BitVec 64) (k0 k1 : BitVec 64)
    (kpBytes : List (BitVec 8)) (regId : BitVec 32) : SepProp :=
  emptyHashMapAt ctrlPtr out k0 k1 ∗
    ((out + 48#64) ↦ₛ kpBytes) ∗
    ((out + 112#64) ↦₃₂ regId) ∗
    memRegion (out + 116#64) 4

/-- Ghost state for `<InMemSignedPreKeyStore>::new` (`0x127d8`) on the uninitialized TLS path (`tag ≠ 1#8`),
generic over the GOT `tpoff` and static `ctrlPtr`. -/
structure SessionStoreNewUninitGhost where
  out     : BitVec 64
  tpoff   : BitVec 64
  ctrlPtr : BitVec 64
  k0Old   : BitVec 64
  k1Old   : BitVec 64
  tag     : BitVec 8

/-- `RandomState::new` key-generation hook (`x0, x1` returned as two `u64` SipHash keys;
no constraint on `x0`/`x1` in the postcondition so any deterministic hook satisfies `HookOk`).
Definitionally equal to `CryptoVerification.E2E.Bin.randomKeysSpec`. -/
@[expose] def randomKeysSpec : Spec Unit where
  pre := fun _ s => stackAt s.sp extHookStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp extHookStack

/-- `hookNoop` satisfies `HookOk hookNoop randomKeysSpec`. -/
theorem randomKeysSpec_nonvac : HookOk hookNoop randomKeysSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [randomKeysSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨rfl, hpre⟩

/-- `randomKeysSpec` strengthened with `sf.tpidrEl0 = s0.tpidrEl0` (satisfied by any `retHook`,
including `hookNoop`). -/
@[expose] def randomKeysTpidrSpec : Spec Unit where
  pre := fun _ s => stackAt s.sp extHookStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗ stackAt s0.sp extHookStack

/-- `hookNoop` satisfies `HookOk hookNoop randomKeysTpidrSpec`. -/
theorem randomKeysTpidrSpec_nonvac : HookOk hookNoop randomKeysTpidrSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [randomKeysTpidrSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨rfl, rfl⟩, hpre⟩

/-- Ghost state for `<InMemSignedPreKeyStore>::new` (`0x127d8`) on the initialized TLS path (`tag = 1#8`),
generic over the GOT `tpoff` and static `ctrlPtr`. -/
structure SessionStoreNewInitGhost where
  out     : BitVec 64
  tpoff   : BitVec 64
  ctrlPtr : BitVec 64
  k0      : BitVec 64
  k1      : BitVec 64

/-- Ghost state for `<InMemIdentityKeyStore>::new` (`0x0c238`) on the uninitialized TLS path (`tag ≠ 1#8`),
generic over the GOT `tpoff` and static `ctrlPtr`. -/
structure IdentityStoreNewUninitGhost where
  out     : BitVec 64
  kpPtr   : BitVec 64
  kpBytes : List (BitVec 8)
  regId   : BitVec 32
  tpoff   : BitVec 64
  ctrlPtr : BitVec 64
  k0Old   : BitVec 64
  k1Old   : BitVec 64
  tag     : BitVec 8

/-- Ghost state for `<InMemIdentityKeyStore>::new` (`0x0c238`) on the initialized TLS path (`tag = 1#8`),
generic over the GOT `tpoff` and static `ctrlPtr`. -/
structure IdentityStoreNewInitGhost where
  out     : BitVec 64
  kpPtr   : BitVec 64
  kpBytes : List (BitVec 8)
  regId   : BitVec 32
  tpoff   : BitVec 64
  ctrlPtr : BitVec 64
  k0      : BitVec 64
  k1      : BitVec 64

end CryptoVerification.E2E.StoreNew

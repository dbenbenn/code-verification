/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model

/-!
# SPQR V1: exact recv key layout and DEV-SPQR1..5 notes

**Checked by Lean.**

Defines the exact message-key layout (`optKeyBytesAt`, `recvResultExactKeyAt`) for `spqr::recv`
against `spqrV1Recv` (`Model.lean`), together with the entailment bridges
`optKeyBytesAt_entails_optKeyRecvAt` and `recvResultAtX_entails_recvResultAt` to `spqrRecvResultAt`
(DEV-SPQR2).

## DEV-SPQR1 (`TokenInit` in standalone library specs)
**DEV-SPQR1 (machine model): standalone SPQR V1 library specs fix `TokenInit` (`STORAGE.0 = false`).**
The standalone placed SPQR V1 library specs fix `TOKEN` (`COMPLETE`) and `STORAGE.0` (`false`),
selecting `unaccelerated::mul` in $\mathrm{GF}(2^{16})$. The CLI ELF headlines
(`CliRunsToElf` in `CliBinaryPq.lean`) instead start from plain `ElfImage.loadState` on
`AT_HWCAP = 0x1b` and execute SPQR's `Once::call` probe (`STORAGE.0 = true`) and `PMULL`-accelerated
`mul2_unreduced`.

## DEV-SPQR3 (input sizes)
**DEV-SPQR3 (machine model): the state is shorter than `2^32` bytes, the message than `2^40`.**
SPQR V1 specs require the serialized state length to be `< 2^32` and (for recv) the message length
to be `< 2^40`, ruling out `RawVec` `capacity_overflow` panics (`2 * cap * stride >= 2^63`). On
decrypt, `< 2^40` comes from `signalMessageAt`; the state bound is discharged at public entries via
`RecordPqStateLengthBelow2Pow32` (`loadSessionSpecPqStateLengthBound` in `Entries.lean`).

## DEV-SPQR4 (recv stack non-wrap)
**DEV-SPQR4 (machine model): the recv stack does not wrap through address 0.**
`spqr::recv` requires `spqrRecvStack ≤ sp` so stack-allocated `VersionNegotiation` pointers
(`sp - 4992`, `sp - 4640`) passed as `Option<&VersionNegotiation>` to `spqr::chain_from` are
non-null; discharged at decrypt integration from `rootStack = 2^18 ≤ sp`.

## DEV-SPQR5 (send random tape)
**DEV-SPQR5 (machine model): `spqr::send` has at least 64 random-tape bytes.**
`spqr::send` and `OutgoingTripleRatchet::encrypt` require `64 ≤ x.rest.length`. Whereas `rngFillHook`
zero-pads a short tape and returns normally, the model's `generate` (64 bytes) and `encaps1`
(32 bytes) return `rngExhausted`; 64 unread tape bytes ensure a single `States::send` call never
hits `rngExhausted`.

## DEV-SPQR2 (recv key type)
**DEV-SPQR2 (libsignal): `spqr::recv` can return the key `Some([])`; the recv statement uses the
exact key type.**
In `spqr::recv`'s version-negotiation `Ordering::Greater` branch (`src/lib.rs:401–419`) with
`msg.index = 0`, `Chain::recv_key(0, 0)` returns `Ok(vec![])` wrapped unconditionally in `Some`
without the `is_empty()` filter of the V1 path (`src/lib.rs:478–482`). Recv proofs therefore target
`recvResultExactKeyAt` over `SpqrRecvModel` (`Option (List (BitVec 8))`). Under `SeedsLen32`
(DEV-LS9), `MessageKeyGenerator::generate_keys` uses the key only as an HKDF salt where `Some(&[])`
and `None` agree (DEV-LS25); `toSpqrModel.recv` maps `some []` via `recvKeyToSalt?` to `none`, and
`recvResultAtX_entails_recvResultAt` bridges `spqrV1Recv` to `spqrV1`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr

/-! ## DEV-SPQR2: recv result layout with exact key type -/

/-- Layout of `spqr::MessageKey = Option<Vec<u8>>` at `a` (24 bytes): `noneCap` niche on `none`, or
owned `vecU8` on `some k`. -/
def optKeyBytesAt (A : RustAlloc) (a : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16
  | some k => vecU8 A a k

/-- Layout of `Result<spqr::Recv, spqr::Error>` at `r` (48 bytes) with exact `Option (List (BitVec 8))`
message key (`optKeyBytesAt`). -/
def recvResultExactKeyAt (A : RustAlloc) (r : BitVec 64) :
    Except Bool (List (BitVec 8) × Option (List (BitVec 8))) → SepProp
  | .ok (st', key) => vecU8 A r st' ∗ optKeyBytesAt A (r + 24#64) key
  | .error sd =>
    (r ↦₆₄ errTag) ∗ (∃∗ d : BitVec 8, ⌜(d = 0#8 ↔ sd = true)⌝ ∗ ((r + 8#64) ↦₈ d)) ∗
      memRegion (r + 9#64) 39

theorem optKeyBytesAt_entails_optKeyRecvAt (A : RustAlloc) (a : BitVec 64)
    {key : Option (List (BitVec 8))} {salt : CryptoGames.HKDF.Salt}
    (h : recvKeyToSalt? key = some salt) :
    optKeyBytesAt A a key ⊢ spqrRecvKeyAt A a salt := by
  cases key with
  | none =>
    injection h with h; subst h
    refine Entails.trans ?_ (Entails.sepExists_intro true)
    exact Entails.refl _
  | some k =>
    cases k with
    | nil =>
      injection h with h; subst h
      refine Entails.trans ?_ (Entails.sepExists_intro false)
      exact Entails.refl _
    | cons b bs =>
      have hne : some (b :: bs) ≠ some [] := nofun
      rw [recvKeyToSalt?_of_ne hne] at h
      dsimp only [messageKeyToSalt?] at h
      split at h
      · injection h with h; subst h
        exact Entails.refl _
      · contradiction

theorem recvResultAtX_entails_recvResultAt (A : RustAlloc) (ret : BitVec 64)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (stBytes msgBytes : List (BitVec 8)) :
    recvResultExactKeyAt A ret ((spqrV1Recv F K).recv stBytes msgBytes) ⊢
      spqrRecvResultAt A ret ((spqrV1 F K).recv stBytes msgBytes) := by
  rw [spqrV1Recv_eq, spqrV1_eq]
  dsimp only [toSpqrRecvModel, toSpqrModel]
  cases h : recv (spqrDeps F K) (spqrHkdfWith F) stBytes msgBytes with
  | ok r =>
    have hv := recv_key_valid (spqrDeps F K) F stBytes msgBytes h
    cases hsalt : recvKeyToSalt? r.key with
    | none => simp [hsalt] at hv
    | some salt =>
      simp only [hsalt, recvResultExactKeyAt, spqrRecvResultAt]
      exact sepConj_mono_right (optKeyBytesAt_entails_optKeyRecvAt A (ret + 24#64) hsalt)
  | error e =>
    cases e <;> exact Entails.refl _

end CryptoVerification.LibsignalSpqrV1


/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements -- proof-setup: allow-public-import

/-!
# Displayable `spqr::Error` Discriminant Invariant & Untrusted Result Predicates

Defines the untrusted discriminant invariant `SpqrErrorValidTag` (`d.toNat < 16 ∧ d ≠ 14#8`)
required by real `<spqr::Error as core::fmt::Display>::fmt` (`libsignalSessionLib` Block `412`)
on the 0-hook CLI placed-budget path, together with:

1. Companion sret predicates `recvResultExactKeyDispAt`, `spqrRecvResultDispAt`, and
   `spqrSendResultDispAt` (identical to `recvResultExactKeyAt`, `spqrRecvResultAt`, and
   `spqrSendResultAt` on `Ok`/`some`, carrying `SpqrErrorValidTag d` on `Err`/`none`);
2. Monotonicity entailments back to the trusted result predicates;
3. Separation-logic splitting & unsplitting lemmas (`spqrErrorPayload24_split`,
   `spqrErrorPayload24_unsplit`, `spqrRecvErrPayload_split`, `spqrSendErrPayload_split`) exposing
   the inline scalar payload cells `[errPtr, errPtr + 24)` read by Block `412` and sub-blocks
   `392, 393, 394, 396, 397`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpqrV1.ErrorDisplayTag

open Arm64 ProofLib
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Error MlKem optKeyBytesAt optKeyBytesAt_entails_optKeyRecvAt recv recvKeyToSalt?
   recvResultExactKeyAt recv_key_valid spqrDeps spqrDecodeState spqrHkdfWith spqrV1 spqrV1Recv
   spqrV1Recv_eq spqrV1_eq toSpqrModel toSpqrRecvModel)
open CryptoVerification.LibsignalTripleRatchet
  (spqrRecvResultAt spqrSendResultAt)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.RustHeap (RustAlloc)

/-! ## 1. Reachable `spqr::Error` Discriminant Invariant -/

/-- Reachable `spqr::Error` discriminant tags (`0..13` and `15`).
    `14#8 = Error::InvalidParams(&'static str)` is never constructed in `spqr` and is the only
    arm of `<spqr::Error as Display>::fmt` (Block `412`) that dereferences a pointer. -/
@[expose] def SpqrErrorValidTag (d : BitVec 8) : Prop :=
  d.toNat < 16 ∧ d ≠ 14#8

instance (d : BitVec 8) : Decidable (SpqrErrorValidTag d) :=
  inferInstanceAs (Decidable (d.toNat < 16 ∧ d ≠ 14#8))

theorem spqrErrorValidTag_zero : SpqrErrorValidTag 0#8 := by
  decide

/-- Canonical `u8` discriminant of `LibsignalSpqrV1.Error` matching Rust's enum layout (`0..15`). -/
@[expose] def spqrErrorTagCanonical : Error → BitVec 8
  | .stateDecode => 0#8
  | .notImplemented => 1#8
  | .msgDecode => 2#8
  | .macVerifyFailed => 3#8
  | .epochOutOfRange _ => 4#8
  | .encodingDecoding => 5#8
  | .serialization => 6#8
  | .versionMismatch => 7#8
  | .minimumVersion => 8#8
  | .keyJump _ _ => 9#8
  | .keyTrimmed _ => 10#8
  | .keyAlreadyRequested _ => 11#8
  | .erroneousDataReceived => 12#8
  | .sendKeyEpochDecreased _ _ => 13#8
  | .invalidParams _ => 14#8
  | .chainNotAvailable => 15#8

theorem spqrErrorTagCanonical_valid_of_ne_invalidParams {e : Error}
    (h : ∀ s, e ≠ .invalidParams s) :
    SpqrErrorValidTag (spqrErrorTagCanonical e) := by
  cases e with
  | invalidParams s => exact False.elim (h s rfl)
  | _ => dsimp only [spqrErrorTagCanonical]; decide

theorem spqrErrorTagCanonical_eq_zero_iff (e : Error) :
    (spqrErrorTagCanonical e = 0#8) ↔ e.isStateDecode = true := by
  cases e <;> (dsimp only [spqrErrorTagCanonical, Error.isStateDecode]; decide)

theorem spqrDecodeState_ne_invalidParams {bs : List (BitVec 8)} {e : Error}
    (h : spqrDecodeState bs = .error e) (s : String) :
    e ≠ .invalidParams s := by
  unfold spqrDecodeState CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · injection h with he; subst he; exact nofun

/-- Displayable `spqr::Error` buffer of size `n` (`n ≥ 24`) at `errPtr`: valid non-pointer
    discriminant at `+0` and raw writable/readable bytes `[errPtr + 1, errPtr + n)`. -/
@[expose] def spqrErrorDisplayableAt (errPtr : BitVec 64) (n : Nat) : SepProp :=
  (∃∗ d : BitVec 8, ⌜SpqrErrorValidTag d⌝ ∗ (errPtr ↦₈ d)) ∗ memRegion (errPtr + 1#64) (n - 1)

/-! ## 2. Payload Splitting & Unsplitting (`[errPtr, errPtr + 24)`) -/

/-- Exact separation-logic decomposition of `(errPtr ↦₈ d) ∗ memRegion (errPtr + 1) 23` into the
    scalar cells read across all 15 reachable arms of Block `412` and sub-blocks `392..397`:
    - `d : BitVec 8` at `+0`
    - `b1 : BitVec 8` at `+1` (`EncodingDecoding`, `Serialization`)
    - `memRegion (errPtr + 2) 2` alignment padding
    - `u1 : BitVec 32` at `+4` (`KeyJump`, `KeyTrimmed`, `KeyAlreadyRequested`)
    - `q1 : BitVec 64` at `+8` (`EpochOutOfRange`, `SendKeyEpochDecreased`, and low `u32` of `KeyJump`)
    - `q2 : BitVec 64` at `+16` (`SendKeyEpochDecreased`). -/
theorem spqrErrorPayload24_split (errPtr : BitVec 64) (d : BitVec 8) :
    (errPtr ↦₈ d) ∗ memRegion (errPtr + 1#64) 23 =
      ∃∗ b1 : BitVec 8, ∃∗ u1 : BitVec 32, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64,
        (errPtr ↦₈ d) ∗ ((errPtr + 1#64) ↦₈ b1) ∗ memRegion (errPtr + 2#64) 2 ∗
          ((errPtr + 4#64) ↦₃₂ u1) ∗ ((errPtr + 8#64) ↦₆₄ q1) ∗ ((errPtr + 16#64) ↦₆₄ q2) := by
  rw [show (23 : Nat) = 1 + 22 by rfl,
      memRegion_split (errPtr + 1#64) 1 22 (by decide),
      show errPtr + 1#64 + 1#64 = errPtr + 2#64 by bv_arith,
      ProofLib.memRegion_one (errPtr + 1#64),
      sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepExists_congr fun b1 => ?_
  rw [show (22 : Nat) = 2 + 20 by rfl,
      memRegion_split (errPtr + 2#64) 2 20 (by decide),
      show errPtr + 2#64 + 2#64 = errPtr + 4#64 by bv_arith,
      show (20 : Nat) = 4 + 16 by rfl,
      memRegion_split (errPtr + 4#64) 4 16 (by decide),
      show errPtr + 4#64 + 4#64 = errPtr + 8#64 by bv_arith,
      ProofLib.memRegion_four (errPtr + 4#64),
      sepExists_sepConj_left, sepExists_sepConj_right,
      sepExists_sepConj_right, sepExists_sepConj_right]
  refine sepExists_congr fun u1 => ?_
  rw [show (16 : Nat) = 8 + 8 by rfl,
      memRegion_split (errPtr + 8#64) 8 8 (by decide),
      show errPtr + 8#64 + 8#64 = errPtr + 16#64 by bv_arith,
      ProofLib.memRegion_eight (errPtr + 8#64),
      sepExists_sepConj_left,
      sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right, sepExists_sepConj_right]
  refine sepExists_congr fun q1 => ?_
  rw [ProofLib.memRegion_eight (errPtr + 16#64),
      sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right]

/-- Re-fold concrete scalar payload cells `(b1, u1, q1, q2)` back into
    `(errPtr ↦₈ d) ∗ memRegion (errPtr + 1) 23`. -/
theorem spqrErrorPayload24_unsplit (errPtr : BitVec 64) (d b1 : BitVec 8)
    (u1 : BitVec 32) (q1 q2 : BitVec 64) :
    (errPtr ↦₈ d) ∗ ((errPtr + 1#64) ↦₈ b1) ∗ memRegion (errPtr + 2#64) 2 ∗
      ((errPtr + 4#64) ↦₃₂ u1) ∗ ((errPtr + 8#64) ↦₆₄ q1) ∗ ((errPtr + 16#64) ↦₆₄ q2) ⊢
      (errPtr ↦₈ d) ∗ memRegion (errPtr + 1#64) 23 := by
  rw [spqrErrorPayload24_split errPtr d]
  refine Entails.trans ?_ (Entails.sepExists_intro b1)
  refine Entails.trans ?_ (Entails.sepExists_intro u1)
  refine Entails.trans ?_ (Entails.sepExists_intro q1)
  refine Entails.trans ?_ (Entails.sepExists_intro q2)
  exact Entails.refl _

/-- Split `((r + 8) ↦₈ d) ∗ memRegion (r + 9) 39` (`spqr::recv` `Err` sret tail) into the 24-byte
    `spqr::Error` payload at `r + 8` and trailing `memRegion (r + 32) 16`. -/
theorem spqrRecvErrPayload_split (r : BitVec 64) (d : BitVec 8) :
    ((r + 8#64) ↦₈ d) ∗ memRegion (r + 9#64) 39 =
      (((r + 8#64) ↦₈ d) ∗ memRegion ((r + 8#64) + 1#64) 23) ∗ memRegion (r + 32#64) 16 := by
  rw [show (39 : Nat) = 23 + 16 by rfl,
      memRegion_split (r + 9#64) 23 16 (by decide),
      show r + 9#64 + 23#64 = r + 32#64 by bv_arith,
      show (r + 8#64) + 1#64 = r + 9#64 by bv_arith,
      sepConj_assoc]

/-- Split `((r + 8) ↦₈ d) ∗ memRegion (r + 9) 63` (`spqr::send` `Err` sret tail) into the 24-byte
    `spqr::Error` payload at `r + 8` and trailing `memRegion (r + 32) 40`. -/
theorem spqrSendErrPayload_split (r : BitVec 64) (d : BitVec 8) :
    ((r + 8#64) ↦₈ d) ∗ memRegion (r + 9#64) 63 =
      (((r + 8#64) ↦₈ d) ∗ memRegion ((r + 8#64) + 1#64) 23) ∗ memRegion (r + 32#64) 40 := by
  rw [show (63 : Nat) = 23 + 40 by rfl,
      memRegion_split (r + 9#64) 23 40 (by decide),
      show r + 9#64 + 23#64 = r + 32#64 by bv_arith,
      show (r + 8#64) + 1#64 = r + 9#64 by bv_arith,
      sepConj_assoc]

/-! ## 3. Untrusted Companion Result Predicates & Entailments -/

/-- Strengthened `recvResultExactKeyAt` carrying `SpqrErrorValidTag d` on `.error sd`. -/
@[expose] def recvResultExactKeyDispAt (A : RustAlloc) (r : BitVec 64) :
    Except Bool (List (BitVec 8) × Option (List (BitVec 8))) → SepProp
  | .ok x => recvResultExactKeyAt A r (.ok x)
  | .error sd =>
    (r ↦₆₄ errTag) ∗
      (∃∗ d : BitVec 8, ⌜(d = 0#8 ↔ sd = true) ∧ SpqrErrorValidTag d⌝ ∗ ((r + 8#64) ↦₈ d)) ∗
      memRegion (r + 9#64) 39

/-- Strengthened `spqrRecvResultAt` carrying `SpqrErrorValidTag d` on `.error sd`. -/
@[expose] def spqrRecvResultDispAt (A : RustAlloc) (r : BitVec 64) :
    Except Bool (List (BitVec 8) × Salt) → SepProp
  | .ok x => spqrRecvResultAt A r (.ok x)
  | .error sd =>
    (r ↦₆₄ errTag) ∗
      (∃∗ d : BitVec 8, ⌜(d = 0#8 ↔ sd = true) ∧ SpqrErrorValidTag d⌝ ∗ ((r + 8#64) ↦₈ d)) ∗
      memRegion (r + 9#64) 39

/-- Strengthened `spqrSendResultAt` carrying `SpqrErrorValidTag d` at `r + 8` on `none`. -/
@[expose] def spqrSendResultDispAt (A : RustAlloc) (r : BitVec 64) :
    Option (List (BitVec 8) × Salt × List (BitVec 8)) → SepProp
  | some x => spqrSendResultAt A r (some x)
  | none =>
    (r ↦₆₄ errTag) ∗
      (∃∗ d : BitVec 8, ⌜SpqrErrorValidTag d⌝ ∗ ((r + 8#64) ↦₈ d)) ∗
      memRegion (r + 9#64) 63

/-- Fold `recvResultExactKeyDispAt A r (.error sd)` from a concrete valid tag `d`. -/
theorem recvResultExactKeyDispAt_error_of_byte (A : RustAlloc) (r : BitVec 64)
    (d : BitVec 8) (sd : Bool) (hsd : d = 0#8 ↔ sd = true) (hd : SpqrErrorValidTag d) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₈ d) ∗ memRegion (r + 9#64) 39 ⊢
      recvResultExactKeyDispAt A r (.error sd) := by
  dsimp only [recvResultExactKeyDispAt]
  refine sepConj_mono_right (sepConj_mono_left ?_)
  refine Entails.trans ?_ (Entails.sepExists_intro d)
  exact Entails.pure_right ⟨hsd, hd⟩ (Entails.refl _)

/-- Fold `spqrRecvResultDispAt A r (.error sd)` from a concrete valid tag `d`. -/
theorem spqrRecvResultDispAt_error_of_byte (A : RustAlloc) (r : BitVec 64)
    (d : BitVec 8) (sd : Bool) (hsd : d = 0#8 ↔ sd = true) (hd : SpqrErrorValidTag d) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₈ d) ∗ memRegion (r + 9#64) 39 ⊢
      spqrRecvResultDispAt A r (.error sd) := by
  dsimp only [spqrRecvResultDispAt]
  refine sepConj_mono_right (sepConj_mono_left ?_)
  refine Entails.trans ?_ (Entails.sepExists_intro d)
  exact Entails.pure_right ⟨hsd, hd⟩ (Entails.refl _)

/-- Fold `spqrSendResultDispAt A r none` from a concrete valid tag `d`. -/
theorem spqrSendResultDispAt_none_of_byte (A : RustAlloc) (r : BitVec 64)
    (d : BitVec 8) (hd : SpqrErrorValidTag d) :
    (r ↦₆₄ errTag) ∗ ((r + 8#64) ↦₈ d) ∗ memRegion (r + 9#64) 63 ⊢
      spqrSendResultDispAt A r none := by
  dsimp only [spqrSendResultDispAt]
  refine sepConj_mono_right (sepConj_mono_left ?_)
  refine Entails.trans ?_ (Entails.sepExists_intro d)
  exact Entails.pure_right hd (Entails.refl _)

/-- Entailment 1/4: `recvResultExactKeyDispAt` implies `recvResultExactKeyAt`. -/
theorem recvResultExactKeyDispAt_entails_exactKeyAt (A : RustAlloc) (r : BitVec 64)
    (res : Except Bool (List (BitVec 8) × Option (List (BitVec 8)))) :
    recvResultExactKeyDispAt A r res ⊢ recvResultExactKeyAt A r res := by
  cases res with
  | ok x => exact Entails.refl _
  | error sd =>
    dsimp only [recvResultExactKeyDispAt, recvResultExactKeyAt]
    refine sepConj_mono_right (sepConj_mono_left ?_)
    refine Entails.sepExists_elim fun d => ?_
    refine Entails.pure_left fun ⟨hsd, _⟩ => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro d)
    exact Entails.pure_right hsd (Entails.refl _)

/-- Entailment 2/4: `recvResultExactKeyDispAt` for `spqrV1Recv F K` implies `spqrRecvResultDispAt`
    for `spqrV1 F K`. -/
theorem recvResultExactKeyDispAt_entails_spqrRecvResultDispAt (A : RustAlloc) (ret : BitVec 64)
    (F : ShaCompress) (K : MlKem) (stBytes msgBytes : List (BitVec 8)) :
    recvResultExactKeyDispAt A ret ((spqrV1Recv F K).recv stBytes msgBytes) ⊢
      spqrRecvResultDispAt A ret ((spqrV1 F K).recv stBytes msgBytes) := by
  rw [spqrV1Recv_eq, spqrV1_eq]
  dsimp only [toSpqrRecvModel, toSpqrModel]
  cases h : recv (spqrDeps F K) (spqrHkdfWith F) stBytes msgBytes with
  | ok r =>
    have hv := recv_key_valid (spqrDeps F K) F stBytes msgBytes h
    cases hsalt : recvKeyToSalt? r.key with
    | none => simp [hsalt] at hv
    | some salt =>
      simp only [hsalt, recvResultExactKeyDispAt, recvResultExactKeyAt,
        spqrRecvResultDispAt, spqrRecvResultAt]
      exact sepConj_mono_right (optKeyBytesAt_entails_optKeyRecvAt A (ret + 24#64) hsalt)
  | error e =>
    cases e <;> exact Entails.refl _

/-- Entailment 3/4: `spqrRecvResultDispAt` implies `spqrRecvResultAt`. -/
theorem spqrRecvResultDispAt_entails_spqrRecvResultAt (A : RustAlloc) (r : BitVec 64)
    (res : Except Bool (List (BitVec 8) × Salt)) :
    spqrRecvResultDispAt A r res ⊢ spqrRecvResultAt A r res := by
  cases res with
  | ok x => exact Entails.refl _
  | error sd =>
    dsimp only [spqrRecvResultDispAt, spqrRecvResultAt]
    refine sepConj_mono_right (sepConj_mono_left ?_)
    refine Entails.sepExists_elim fun d => ?_
    refine Entails.pure_left fun ⟨hsd, _⟩ => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro d)
    exact Entails.pure_right hsd (Entails.refl _)

/-- Entailment 4/4: `spqrSendResultDispAt` implies `spqrSendResultAt`. -/
theorem spqrSendResultDispAt_entails_spqrSendResultAt (A : RustAlloc) (r : BitVec 64)
    (res : Option (List (BitVec 8) × Salt × List (BitVec 8))) :
    spqrSendResultDispAt A r res ⊢ spqrSendResultAt A r res := by
  cases res with
  | some x => exact Entails.refl _
  | none =>
    dsimp only [spqrSendResultDispAt, spqrSendResultAt]
    refine sepConj_mono_right ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun d => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun _ => ?_
    have h64 : memRegion (r + 8#64) 64 =
        (∃∗ b : BitVec 8, (r + 8#64) ↦₈ b) ∗ memRegion (r + 9#64) 63 := by
      have hs := memRegion_split (r + 8#64) 1 63 (by decide)
      dsimp only [Nat.reduceAdd] at hs
      rw [hs, show r + 8#64 + BitVec.ofNat 64 1 = r + 9#64 by bv_arith,
          ProofLib.memRegion_one (r + 8#64)]
    rw [h64]
    refine sepConj_mono_left ?_
    exact Entails.sepExists_intro d

end LibsignalBinary.Proofs.SpqrV1.ErrorDisplayTag

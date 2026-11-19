/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.BV.ReflectROBDD
public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## Pure Models -/

/-- 32-bit unsigned integer assembled from little-endian bytes `b0 b1 b2 b3`. -/
@[expose] def ofLe32 (b0 b1 b2 b3 : BitVec 8) : BitVec 32 := b3 ++ b2 ++ b1 ++ b0

/-- Pure model of `split_id(file)`: splits a 4-byte little-endian `u32` ID from the remaining slice, returning `none` if `file.length < 4`. -/
@[expose] def splitId : List (BitVec 8) → Option (BitVec 32 × List (BitVec 8))
  | b0 :: b1 :: b2 :: b3 :: rest => some (ofLe32 b0 b1 b2 b3, rest)
  | _ => none

/-- Pure model of `split_signed(file)`: applies `splitId`, then splits the remaining slice into `(key, sig)` with a 64-byte trailing signature, returning `none` if `file.length < 68`. -/
@[expose] def splitSigned (file : List (BitVec 8)) :
    Option (BitVec 32 × List (BitVec 8) × List (BitVec 8)) :=
  match splitId file with
  | none => none
  | some (id, rest) =>
    if 64 ≤ rest.length then some (id, rest.take (rest.length - 64), rest.drop (rest.length - 64))
    else none

theorem ofLe32_le32 (v : BitVec 32) :
    (le32 v).length = 4 ∧
      ∀ h : (le32 v).length = 4,
        ofLe32 ((le32 v)[0]'(by omega)) ((le32 v)[1]'(by omega)) ((le32 v)[2]'(by omega))
          ((le32 v)[3]'(by omega)) = v := by
  refine ⟨rfl, fun _ => ?_⟩
  simp only [le32, ofLe32, List.getElem_cons_zero, List.getElem_cons_succ]
  bv_slice

/-- `splitId` inverts `le32 id ++ key`. -/
theorem splitId_le32 (id : BitVec 32) (key : List (BitVec 8)) :
    splitId (le32 id ++ key) = some (id, key) := by
  have h := (ofLe32_le32 id).2 rfl
  simp only [le32, List.getElem_cons_zero, List.getElem_cons_succ] at h
  simp only [le32, List.cons_append, List.nil_append, splitId, h]

/-- `splitSigned` inverts `le32 id ++ key ++ sig` for any 64-byte signature `sig`. -/
theorem splitSigned_le32 (id : BitVec 32) (key sig : List (BitVec 8)) (hs : sig.length = 64) :
    splitSigned (le32 id ++ key ++ sig) = some (id, key, sig) := by
  rw [List.append_assoc, splitSigned, splitId_le32]
  simp only [List.length_append, hs, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel,
    List.take_left', List.drop_left']

/-! ## Symbol Names -/

abbrev splitIdName : String := "libsignal_cli::public::split_id"

abbrev splitSignedName : String := "libsignal_cli::public::split_signed"

abbrev bundleReadName : String := "libsignal_cli::public::read_bundle::{closure#0}"

/-- CLI crate symbol for `drop_glue::<SignalProtocolError> [local#3]`. -/
abbrev cliDropSpeName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"

/-- Niche `Ok` tag word (`-2`) for `Result<_, SignalProtocolError>` in `split_id` and `split_signed`. -/
@[expose] def splitOkTag : BitVec 64 := 0xFFFFFFFFFFFFFFFE#64

/-- 48-byte `sret` layout at `r` for `split_id(fp, file)`: `(splitOkTag, id @ +8, fp + 4 @ +16, len - 4 @ +24)` on `Ok`, or `speAt A (utf8 "bundle") r .invalidState` on `Err`. -/
@[expose] def splitIdResultAt (A : RustAlloc) (r fp : BitVec 64) (file : List (BitVec 8)) : SepProp :=
  match splitId file with
  | some (id, rest) =>
    (r ↦₆₄ splitOkTag) ∗ ((r + 8#64) ↦₃₂ id) ∗ memRegion (r + 0xc#64) 4 ∗
      ((r + 0x10#64) ↦₆₄ (fp + 4#64)) ∗ ((r + 0x18#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
      memRegion (r + 0x20#64) 16
  | none => speAt A (utf8 "bundle") r .invalidState

/-- 48-byte `sret` layout at `r` for `split_signed(fp, file)`: `(splitOkTag, fp + 4 @ +8, key.len @ +16, id @ +24, fp + 4 + key.len @ +32, 64 @ +40)` on `Ok`, or `speAt A (utf8 "bundle") r .invalidState` on `Err`. -/
@[expose] def splitSignedResultAt (A : RustAlloc) (r fp : BitVec 64) (file : List (BitVec 8)) : SepProp :=
  match splitSigned file with
  | some (id, key, _) =>
    (r ↦₆₄ splitOkTag) ∗ ((r + 8#64) ↦₆₄ (fp + 4#64)) ∗
      ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 key.length) ∗ ((r + 0x18#64) ↦₃₂ id) ∗
      memRegion (r + 0x1c#64) 4 ∗
      ((r + 0x20#64) ↦₆₄ (fp + 4#64 + BitVec.ofNat 64 key.length)) ∗
      ((r + 0x28#64) ↦₆₄ 64#64)
  | none => speAt A (utf8 "bundle") r .invalidState

/-! ## `split_id` and `split_signed` Specifications -/

/-- Ghost state for `split_id` and `split_signed`: 48-byte `sret` pointer `ret` and borrowed input slice `file` at `fp`. -/
structure SplitGhost where
  ret : BitVec 64
  fp : BitVec 64
  file : List (BitVec 8)
  ro : Bool

/-- Ghost state for `read_bundle::{closure#0}`: 48-byte `sret` pointer `ret`, bundle directory slice `dir`, and entry name slice `name`. -/
structure BundleReadGhost where
  ret : BitVec 64
  dirA : BitVec 64
  dir : List (BitVec 8)
  dirRo : Bool
  nameA : BitVec 64
  name : List (BitVec 8)
  nameRo : Bool

end CryptoVerification.SignalSession.Cli

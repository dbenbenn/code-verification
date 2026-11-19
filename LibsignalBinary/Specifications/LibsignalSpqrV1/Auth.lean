/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
import all Init.Data.Range.Basic

/-!
# SPQR V1: Authenticator (`spqr/src/authenticator.rs`, `src/authenticator/serialize.rs`)

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `compare_prefix`, `Authenticator.verifyCt_prefix`, and `Authenticator.verifyHdr_prefix`,
which are checked by Lean (see `Computational/docs/TRUSTED_BASE.md`).

Models SPQR's epoch authenticator (`Mac`, `AuthError`, `Authenticator` with `macSize`, `new`,
`update`, `intoPb`, `fromPb`), panic-explicit HMAC-SHA256 tag computation and constant-time
verification (`macCt`, `verifyCt`, `verifyCtError`, `macHdr`, `verifyHdr`, `verifyHdrError`,
`hmacU32UnwrapPanic`), and unchecked helpers (`macCtUnchecked`, `macHdrUnchecked`,
`verifyCt_eq_ok_prefix`, `verifyHdr_eq_ok_prefix`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open CryptoGames.HMAC

/-! ## Unchecked prefix-comparison helper and `sha256With`/`hmacWith` length lemmas -/

/-- Unchecked prefix-comparing helper for `spqr::util::compare` (`src/util.rs:25–33`): accumulates
bitwise XOR differences over `lhs.zip rhs` without the `lhs.length ≤ rhs.length` bounds check. -/
def compare_prefix (lhs rhs : Bytes) : BitVec 8 :=
  isNonZero ((lhs.zip rhs).foldl (fun r (a, b) => r ||| (a ^^^ b)) 0#8)

theorem compare_eq_ok_prefix {lhs rhs : Bytes} (h : lhs.length ≤ rhs.length) :
    compare lhs rhs = .ok (compare_prefix lhs rhs) := by
  simp [compare, compare_prefix, h]

@[simp]
theorem length_sha256With (F : ShaState → List (BitVec 8) → ShaState) (m : Bytes) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  generalize (chunks64 (sha256Pad m)).foldl F sha256IV = s
  rcases s with ⟨l, hl⟩
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first | rfl | cases hl

@[simp]
theorem length_hmacWith (F : ShaState → List (BitVec 8) → ShaState) (k m : Bytes) :
    (hmacWith F k m).length = 32 := by
  unfold hmacWith
  exact length_sha256With F _

/-! ## Types and constants (`spqr/src/authenticator.rs`) -/

abbrev Mac := Bytes

/-- Panic site in `libcrux-hmac 0.0.8` (`src/impl_hacl.rs:12,14`): `u32` length unwrap when
`key.length ≥ 2^32` or `data.length ≥ 2^32`. -/
abbrev hmacU32UnwrapPanic : SpqrPanic :=
  .site "libcrux-hmac impl_hacl.rs:12/14 u32 unwrap"

/-- `spqr::authenticator::Error` (`src/authenticator.rs:11–24`). -/
inductive AuthError where
  | invalidCtMac
  | invalidHdrMac
  | authenticatorRootKeyPresent
  | authenticatorRootKeyMissing
  | authenticatorMacKeyPresent
  | authenticatorMacKeyMissing
  deriving DecidableEq, Repr, Inhabited

/-- `impl From<authenticator::Error> for Error` (`src/lib.rs:144–147`). -/
def AuthError.toError : AuthError → Error := fun _ => .macVerifyFailed

/-- `spqr::authenticator::Authenticator` (`src/authenticator.rs:27–30`). -/
structure Authenticator where
  rootKey : Mac
  macKey : Mac
  deriving DecidableEq, Repr, Inhabited

namespace Authenticator

abbrev macSize : ℕ := 32

def updateLabel : Bytes :=
  "Signal_PQCKA_V1_MLKEM768:Authenticator Update".toList.map fun c => BitVec.ofNat 8 c.toNat

def ctLabel : Bytes :=
  "Signal_PQCKA_V1_MLKEM768:ciphertext".toList.map fun c => BitVec.ofNat 8 c.toNat

def hdrLabel : Bytes :=
  "Signal_PQCKA_V1_MLKEM768:ekheader".toList.map fun c => BitVec.ofNat 8 c.toNat

/-- `Authenticator::update` (`src/authenticator.rs:44–54`): derives `(rootKey, macKey)` via 64-byte
HKDF-SHA256 from `rootKey ++ k` and `updateLabel ++ ep.to_be_bytes()` under a 32-byte zero salt. -/
def update (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (k : Bytes) : Authenticator :=
  let ikm := self.rootKey ++ k
  let info := updateLabel ++ toBEBytes 8 ep
  let kdfOut := hkdfToVecUnchecked F (List.replicate 32 0) ikm info 64
  { rootKey := kdfOut.take 32
    macKey := kdfOut.drop 32 }

/-- `Authenticator::new` (`src/authenticator.rs:35–42`). -/
def new (F : ShaState → List (BitVec 8) → ShaState) (rootKey : Bytes) (ep : Epoch) : Authenticator :=
  let result : Authenticator := { rootKey := List.replicate 32 0, macKey := List.replicate 32 0 }
  result.update F ep rootKey

def macCtUnchecked (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct : Bytes) : Mac :=
  let ctMacData := ctLabel ++ toBEBytes 8 ep ++ ct
  (hmacWith F self.macKey ctMacData).take macSize

@[simp]
theorem length_macCtUnchecked (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct : Bytes) :
    (self.macCtUnchecked F ep ct).length = 32 := by
  simp [macCtUnchecked, macSize]

/-- `Authenticator::mac_ct` (`src/authenticator.rs:66–79`): HMAC-SHA256 tag over
`ctLabel ++ ep.to_be_bytes() ++ ct`, panicking with `hmacU32UnwrapPanic` if key or input length
reaches `2^32`. -/
def macCt (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct : Bytes) : Except SpqrPanic Mac :=
  let ctMacData := ctLabel ++ toBEBytes 8 ep ++ ct
  if self.macKey.length < 2 ^ 32 ∧ ctMacData.length < 2 ^ 32 then
    .ok (self.macCtUnchecked F ep ct)
  else
    .error hmacU32UnwrapPanic

theorem macCt_of_lt (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct : Bytes)
    (hk : self.macKey.length < 2 ^ 32)
    (hd : (ctLabel ++ toBEBytes 8 ep ++ ct).length < 2 ^ 32) :
    self.macCt F ep ct = .ok (self.macCtUnchecked F ep ct) := by
  simp only [macCt, hk, hd, and_self, ↓reduceIte]

def verifyCt_prefix (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct expectedMac : Bytes) : Except AuthError Unit :=
  if compare_prefix expectedMac (self.macCtUnchecked F ep ct) != 0#8 then
    .error .invalidCtMac
  else
    .ok ()

/-- `Authenticator::verify_ct` (`src/authenticator.rs:57–63`): checks `expectedMac` against
`macCt F ep ct` via `Core.compare` (which compares `0..expectedMac.length` and panics if
`expectedMac.length > 32`). -/
def verifyCt (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct expectedMac : Bytes) :
      Except SpqrPanic (Except AuthError Unit) := do
  let mac ← self.macCt F ep ct
  let c ← compare expectedMac mac
  return if c != 0#8 then .error .invalidCtMac else .ok ()

def verifyCtError (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct expectedMac : Bytes) :
      Except SpqrPanic (Except Error Unit) :=
  (self.verifyCt F ep ct expectedMac).map (Except.mapError AuthError.toError)

theorem verifyCt_eq_ok_prefix (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (ct expectedMac : Bytes)
    (hk : self.macKey.length < 2 ^ 32)
    (hd : (ctLabel ++ toBEBytes 8 ep ++ ct).length < 2 ^ 32)
    (hm : expectedMac.length ≤ 32) :
    self.verifyCt F ep ct expectedMac = .ok (self.verifyCt_prefix F ep ct expectedMac) := by
  have hm' : expectedMac.length ≤ (self.macCtUnchecked F ep ct).length := by
    simpa [length_macCtUnchecked] using hm
  simp [verifyCt, macCt_of_lt F self ep ct hk hd, compare_eq_ok_prefix hm', verifyCt_prefix,
     Bind.bind, Except.bind, pure, Except.pure]

def macHdrUnchecked (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes) : Mac :=
  let ctMacData := hdrLabel ++ toBEBytes 8 ep ++ hdr
  (hmacWith F self.macKey ctMacData).take macSize

@[simp]
theorem length_macHdrUnchecked (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes) :
    (self.macHdrUnchecked F ep hdr).length = 32 := by
  simp [macHdrUnchecked, macSize]

/-- `Authenticator::mac_hdr` (`src/authenticator.rs:91–104`): HMAC-SHA256 tag over
`hdrLabel ++ ep.to_be_bytes() ++ hdr`, panicking with `hmacU32UnwrapPanic` if key or input length
reaches `2^32`. -/
def macHdr (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes) : Except SpqrPanic Mac :=
  let ctMacData := hdrLabel ++ toBEBytes 8 ep ++ hdr
  if self.macKey.length < 2 ^ 32 ∧ ctMacData.length < 2 ^ 32 then
    .ok (self.macHdrUnchecked F ep hdr)
  else
    .error hmacU32UnwrapPanic

theorem macHdr_of_lt (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes)
    (hk : self.macKey.length < 2 ^ 32)
    (hd : (hdrLabel ++ toBEBytes 8 ep ++ hdr).length < 2 ^ 32) :
    self.macHdr F ep hdr = .ok (self.macHdrUnchecked F ep hdr) := by
  simp only [macHdr, hk, hd, and_self, ↓reduceIte]

def verifyHdr_prefix (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr expectedMac : Bytes) : Except AuthError Unit :=
  if compare_prefix expectedMac (self.macHdrUnchecked F ep hdr) != 0#8 then
    .error .invalidHdrMac
  else
    .ok ()

/-- `Authenticator::verify_hdr` (`src/authenticator.rs:82–88`): checks `expectedMac` against
`macHdr F ep hdr` via `Core.compare` (panicking if `expectedMac.length > 32`). -/
def verifyHdr (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr expectedMac : Bytes) :
      Except SpqrPanic (Except AuthError Unit) := do
  let mac ← self.macHdr F ep hdr
  let c ← compare expectedMac mac
  return if c != 0#8 then .error .invalidHdrMac else .ok ()

def verifyHdrError (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr expectedMac : Bytes) :
      Except SpqrPanic (Except Error Unit) :=
  (self.verifyHdr F ep hdr expectedMac).map (Except.mapError AuthError.toError)

theorem verifyHdr_eq_ok_prefix (F : ShaState → List (BitVec 8) → ShaState)
    (self : Authenticator) (ep : Epoch) (hdr expectedMac : Bytes)
    (hk : self.macKey.length < 2 ^ 32)
    (hd : (hdrLabel ++ toBEBytes 8 ep ++ hdr).length < 2 ^ 32)
    (hm : expectedMac.length ≤ 32) :
    self.verifyHdr F ep hdr expectedMac = .ok (self.verifyHdr_prefix F ep hdr expectedMac) := by
  have hm' : expectedMac.length ≤ (self.macHdrUnchecked F ep hdr).length := by
    simpa [length_macHdrUnchecked] using hm
  simp [verifyHdr, macHdr_of_lt F self ep hdr hk hd, compare_eq_ok_prefix hm', verifyHdr_prefix,
    Bind.bind, Except.bind, pure, Except.pure]

def intoPb (self : Authenticator) : ProtoAuthenticator :=
  { rootKey := self.rootKey, macKey := self.macKey }

def fromPb (pb : ProtoAuthenticator) : Authenticator :=
  { rootKey := pb.rootKey, macKey := pb.macKey }

@[simp]
theorem fromPb_intoPb (a : Authenticator) : fromPb (intoPb a) = a := rfl

end Authenticator

end CryptoVerification.LibsignalSpqrV1

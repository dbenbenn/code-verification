/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Vector.Defs
public import LibsignalBinary.Specifications.CryptoGames.Hash.Sha512

/-!
# FIPS 180-4 SHA-512 block-compression reference

Re-exports `CryptoGames.SHA512` from `LibsignalBinary.Specifications.CryptoGames.Hash.Sha512`
and adds `beBytesOfU64` together with length and `.toList` helper lemmas.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref

export CryptoGames.SHA512 (sha512K beU64OfBytes sha512SmallSigma0 sha512SmallSigma1 sha512BigSigma0)
export CryptoGames.SHA512 (sha512BigSigma1 sha512Ch sha512Maj sha512Schedule sha512Round)
export CryptoGames.SHA512 (sha512CompressBlock sha512CompressState)

/-- Encode a 64-bit word into 8 big-endian bytes. -/
@[expose] def beBytesOfU64 (w : BitVec 64) : List (BitVec 8) :=
  (List.range 8).map fun i => (w >>> ((7 - i) * 8)).truncate 8

theorem sha512CompressBlock_length (st : List (BitVec 64)) (block : List (BitVec 8)) :
    (sha512CompressBlock st block).length = 8 := by
  simp [sha512CompressBlock]

@[simp]
theorem sha512CompressState_toList (st : List.Vector (BitVec 64) 8) (block : List (BitVec 8)) :
    (sha512CompressState st block).toList = sha512CompressBlock st.toList block :=
  rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref

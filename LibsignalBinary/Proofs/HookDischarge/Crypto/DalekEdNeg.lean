/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.ByteRegion
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon

/-!
# Untrusted Pure `curve25519-dalek` `<EdwardsPoint as Neg>::neg` Byte Function (`LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg`)

Defines the exact 5×51-bit byte action `dalekEdNegBytes` / `dalekEdNegVec` of `curve25519-dalek`'s
`<EdwardsPoint as Neg>::neg` strictly in untrusted `Proofs/`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg

open ProofLib

/-- Pack five 64-bit limbs into a 40-byte little-endian buffer. -/
@[expose] def packFe51Bytes (w0 w1 w2 w3 w4 : BitVec 64) : List (BitVec 8) :=
  ByteSlice.unpackLE 8 w0 ++ ByteSlice.unpackLE 8 w1 ++ ByteSlice.unpackLE 8 w2 ++
    ByteSlice.unpackLE 8 w3 ++ ByteSlice.unpackLE 8 w4

/-- Exact 5-limb `FieldElement51::neg` (`16 * p25519 - a`, followed by weak reduction) on the
    40-byte field element at byte offset `off` in `bs`. -/
@[expose] def fe51NegBytesAt (bs : List (BitVec 8)) (off : Nat) : List (BitVec 8) :=
  let l0 := ByteSlice.readLE bs off 8
  let l1 := ByteSlice.readLE bs (off + 8) 8
  let l2 := ByteSlice.readLE bs (off + 16) 8
  let l3 := ByteSlice.readLE bs (off + 24) 8
  let l4 := ByteSlice.readLE bs (off + 32) 8
  let d0 := 36028797018963664#64 - l0
  let d1 := 36028797018963952#64 - l1
  let d2 := 36028797018963952#64 - l2
  let d3 := 36028797018963952#64 - l3
  let d4 := 36028797018963952#64 - l4
  let r0 := (d0 &&& 2251799813685247#64) + (d4 >>> 51) * 19#64
  let r1 := (d1 &&& 2251799813685247#64) + (d0 >>> 51)
  let r2 := (d2 &&& 2251799813685247#64) + (d1 >>> 51)
  let r3 := (d3 &&& 2251799813685247#64) + (d2 >>> 51)
  let r4 := (d4 &&& 2251799813685247#64) + (d3 >>> 51)
  packFe51Bytes r0 r1 r2 r3 r4

/-- Exact byte-level action of `curve25519-dalek`'s `<EdwardsPoint as Neg>::neg`: negates `X`
    (`0..40`) and `T` (`120..160`) and copies `Y` (`40..80`) and `Z` (`80..120`) word-for-word. -/
@[expose] def dalekEdNegBytes (bs : List (BitVec 8)) : List (BitVec 8) :=
  fe51NegBytesAt bs 0 ++
    packFe51Bytes
      (ByteSlice.readLE bs 40 8) (ByteSlice.readLE bs 48 8)
      (ByteSlice.readLE bs 56 8) (ByteSlice.readLE bs 64 8)
      (ByteSlice.readLE bs 72 8) ++
    packFe51Bytes
      (ByteSlice.readLE bs 80 8) (ByteSlice.readLE bs 88 8)
      (ByteSlice.readLE bs 96 8) (ByteSlice.readLE bs 104 8)
      (ByteSlice.readLE bs 112 8) ++
    fe51NegBytesAt bs 120

@[simp] theorem packFe51Bytes_length (w0 w1 w2 w3 w4 : BitVec 64) :
    (packFe51Bytes w0 w1 w2 w3 w4).length = 40 := rfl

@[simp] theorem fe51NegBytesAt_length (bs : List (BitVec 8)) (off : Nat) :
    (fe51NegBytesAt bs off).length = 40 := rfl

/-- `dalekEdNegBytes bs` always has length `160`. -/
theorem dalekEdNegBytes_length (bs : List (BitVec 8)) :
    (dalekEdNegBytes bs).length = 160 := by
  unfold dalekEdNegBytes
  simp [fe51NegBytesAt_length, packFe51Bytes_length]

/-- Total 160-byte vector function for `<EdwardsPoint as Neg>::neg`. -/
@[expose] def dalekEdNegVec (v : List.Vector (BitVec 8) 160) : List.Vector (BitVec 8) 160 :=
  ⟨dalekEdNegBytes v.toList, dalekEdNegBytes_length v.toList⟩

end LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg

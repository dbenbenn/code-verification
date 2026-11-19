/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs

/-!
# Functional model of `session_m_seed` (`seedRecord`, `SeedOk`)

Models the 300-byte seed parser and `RecordStructure` protobuf builder (`seedSession`, `seedRecord`)
used by `session_m_seed`, together with X25519 scalar clamping (`SeedOk`, `seedSlice_129_clamped`).
-/

public section

namespace CryptoVerification.E2E.Record

open CryptoGames
open CryptoGames.Ratchet

/-! ## Protobuf wire-format builders -/

/-- `pb_key(v, tag, wire)`: the byte `(tag << 3) | wire` (tags below 16). -/
@[expose] def pbKey (tag wire : ℕ) : List (BitVec 8) := [BitVec.ofNat 8 (tag * 8 + wire)]

/-- The LEB128 bytes of `x` as `pb_varint`'s loop pushes them (`(x as u8) | 0x80` while
`x ≥ 0x80`, then `x as u8`); `fuel` = the number of continuation bytes allowed (5 covers `u32`). -/
@[expose] def pbVarintBody : ℕ → ℕ → List (BitVec 8)
  | 0, x => [BitVec.ofNat 8 x]
  | fuel + 1, x =>
    if x < 128 then [BitVec.ofNat 8 x] else BitVec.ofNat 8 (x % 128 + 128) :: pbVarintBody fuel (x / 128)

/-- `pb_varint(v, tag, x)`: nothing if `x = 0`, else the key (wire type 0) and the LEB128 bytes. -/
@[expose] def pbVarint (tag x : ℕ) : List (BitVec 8) :=
  if x = 0 then [] else pbKey tag 0 ++ pbVarintBody 5 x

/-- `pb_bytes(v, tag, bytes)`: the key (wire type 2), `bytes.len() as u8`, the bytes. -/
@[expose] def pbBytes (tag : ℕ) (b : List (BitVec 8)) : List (BitVec 8) :=
  pbKey tag 2 ++ [BitVec.ofNat 8 b.length] ++ b

/-- `pb_pubkey(k)`: the type byte `0x05`, then `k`. -/
@[expose] def pbPubkey (k : List (BitVec 8)) : List (BitVec 8) := 5#8 :: k

/-- `pb_chain(public, private, key, index)`: a `Chain` message (public key, optional private key,
the `ChainKey { index, key }` sub-message). -/
@[expose] def pbChain (pub : List (BitVec 8)) (priv : Option (List (BitVec 8))) (key : List (BitVec 8))
    (index : ℕ) : List (BitVec 8) :=
  let ck := pbVarint 1 index ++ pbBytes 2 key
  pbBytes 1 (pbPubkey pub) ++ (match priv with | some p => pbBytes 2 p | none => []) ++ pbBytes 3 ck

/-! ## Seed slice extractors and `SeedOk` -/

/-- The bytes `f[o .. o + n]`. -/
@[expose] def seedSlice (f : List (BitVec 8)) (o n : ℕ) : List (BitVec 8) := (f.drop o).take n

/-- `u32le(o)`: the little-endian `u32` at `f[o .. o + 4]`. -/
@[expose] def seedU32 (f : List (BitVec 8)) (o : ℕ) : ℕ :=
  (f.getD o 0).toNat + 256 * (f.getD (o + 1) 0).toNat + 65536 * (f.getD (o + 2) 0).toNat +
    16777216 * (f.getD (o + 3) 0).toNat

/-- Validity predicate for the 300-byte `session_m_seed` input: boolean presence flags at offsets
`96`, `197`, and `266`, zero padding in `267..300`, and a clamped X25519 sender private key at
`129..161` when `f[96] = 1`. -/
@[expose] def SeedOk (f : List (BitVec 8)) : Prop :=
  f.length = 300 ∧ (f.getD 96 0).toNat ≤ 1 ∧ (f.getD 197 0).toNat ≤ 1 ∧ (f.getD 266 0).toNat ≤ 1 ∧
    (∀ i, 267 ≤ i → i < 300 → f.getD i 0 = 0) ∧
    (f.getD 96 0 = 1 →
      f.getD 129 0 &&& 0xf8#8 = f.getD 129 0 ∧ (f.getD 160 0 &&& 0x7f#8) ||| 0x40#8 = f.getD 160 0)

/-- `Ratchet.clampScalar` fixes `k` iff `k[0]`'s low 3 bits are clear and `k[31]` has its top
bit clear and bit 6 set. -/
theorem clampScalar_fix_iff (k : List.Vector (BitVec 8) 32) :
    clampScalar k = k ↔
      k.get 0 &&& 0xf8#8 = k.get 0 ∧ (k.get 31 &&& 0x7f#8) ||| 0x40#8 = k.get 31 := by
  constructor
  · intro h
    have h0 : (clampScalar k).get 0 = k.get 0 := by rw [h]
    have h31 : (clampScalar k).get 31 = k.get 31 := by rw [h]
    simp only [clampScalar, List.Vector.get_set_of_ne (show (31 : Fin 32) ≠ 0 by decide),
      List.Vector.get_set_same] at h0 h31
    exact ⟨h0, h31⟩
  · rintro ⟨h0, h31⟩
    apply List.Vector.ext
    intro j
    by_cases hj31 : j = 31
    · subst hj31
      simp only [clampScalar, List.Vector.get_set_same]
      exact h31
    · by_cases hj0 : j = 0
      · subst hj0
        simp only [clampScalar, List.Vector.get_set_of_ne (Ne.symm hj31), List.Vector.get_set_same]
        exact h0
      · simp only [clampScalar, List.Vector.get_set_of_ne (Ne.symm hj31),
          List.Vector.get_set_of_ne (Ne.symm hj0)]

/-- The `SessionStructure` bytes `s` that `session_m_seed` writes. -/
@[expose] def seedSession (f : List (BitVec 8)) : List (BitVec 8) :=
  pbVarint 1 4 ++ pbBytes 2 (pbPubkey (seedSlice f 0 32)) ++ pbBytes 3 (pbPubkey (seedSlice f 32 32)) ++
    pbBytes 4 (seedSlice f 64 32) ++
    (if f.getD 96 0 = 1 then
      pbBytes 6 (pbChain (seedSlice f 97 32) (some (seedSlice f 129 32)) (seedSlice f 161 32) (seedU32 f 193))
     else []) ++
    (if f.getD 197 0 = 1 then
      pbBytes 7 (pbChain (seedSlice f 198 32) none (seedSlice f 230 32) (seedU32 f 262))
     else []) ++
    (if f.getD 266 0 = 1 then pbBytes 9 (pbBytes 2 (pbPubkey (List.replicate 32 0#8))) else [])

/-- `RecordStructure` protobuf encoding (`tag 1`, length-delimited `seedSession f`) passed to `SessionRecord::deserialize`. -/
@[expose] def seedRecord (f : List (BitVec 8)) : List (BitVec 8) :=
  pbKey 1 2 ++ pbVarintBody 5 (seedSession f).length ++ seedSession f

/-- The fixed header of `s`. -/
def seedHdr (f : List (BitVec 8)) : List (BitVec 8) :=
  pbVarint 1 4 ++ pbBytes 2 (pbPubkey (seedSlice f 0 32)) ++ pbBytes 3 (pbPubkey (seedSlice f 32 32)) ++
    pbBytes 4 (seedSlice f 64 32)

/-- The sender chain (key 6), present iff `f[96] = 1`. -/
def seedC1 (f : List (BitVec 8)) : List (BitVec 8) :=
  if f.getD 96 0 = 1 then
    pbBytes 6 (pbChain (seedSlice f 97 32) (some (seedSlice f 129 32)) (seedSlice f 161 32) (seedU32 f 193))
  else []

/-- The receiver chain (key 7), present iff `f[197] = 1`. -/
def seedC2 (f : List (BitVec 8)) : List (BitVec 8) :=
  if f.getD 197 0 = 1 then
    pbBytes 7 (pbChain (seedSlice f 198 32) none (seedSlice f 230 32) (seedU32 f 262))
  else []

/-- The pending pre-key (key 9), present iff `f[266] = 1`. -/
def seedC3 (f : List (BitVec 8)) : List (BitVec 8) :=
  if f.getD 266 0 = 1 then pbBytes 9 (pbBytes 2 (pbPubkey (List.replicate 32 0#8))) else []

theorem seedSession_eq (f : List (BitVec 8)) :
    seedSession f = seedHdr f ++ seedC1 f ++ seedC2 f ++ seedC3 f := by
  simp only [seedSession, seedHdr, seedC1, seedC2, seedC3, List.append_assoc]

namespace SeedLengthFacts

theorem seedSlice_length_le (f : List (BitVec 8)) (o n : Nat) :
    (seedSlice f o n).length ≤ n := by
  unfold seedSlice
  exact List.length_take_le n (f.drop o)

theorem pbVarintBody_length_le : ∀ fuel x, (pbVarintBody fuel x).length ≤ fuel + 1
  | 0, _ => by simp [pbVarintBody]
  | fuel + 1, x => by
    simp only [pbVarintBody]
    split
    · simp
    · simp only [List.length_cons]
      have := pbVarintBody_length_le fuel (x / 128)
      omega

theorem pbVarint_length_le (tag x : Nat) : (pbVarint tag x).length ≤ 7 := by
  unfold pbVarint pbKey
  split
  · simp
  · simp only [List.length_append, List.length_singleton]
    have := pbVarintBody_length_le 5 x
    omega

theorem seedHdr_length_bounds (f : List (BitVec 8)) :
    10 ≤ (seedHdr f).length ∧ (seedHdr f).length ≤ 106 := by
  have hv : (pbVarint 1 4).length = 2 := by decide
  have h0 := seedSlice_length_le f 0 32
  have h1 := seedSlice_length_le f 32 32
  have h2 := seedSlice_length_le f 64 32
  unfold seedHdr pbBytes pbPubkey pbKey
  simp only [List.length_append, List.length_cons, List.length_nil, hv]
  omega

theorem seedC1_length_le (f : List (BitVec 8)) : (seedC1 f).length ≤ 114 := by
  unfold seedC1
  split
  · unfold pbChain pbBytes pbPubkey pbKey
    have hv := pbVarint_length_le 1 (seedU32 f 193)
    have h0 := seedSlice_length_le f 97 32
    have h1 := seedSlice_length_le f 129 32
    have h2 := seedSlice_length_le f 161 32
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · simp

theorem seedC2_length_le (f : List (BitVec 8)) : (seedC2 f).length ≤ 80 := by
  unfold seedC2
  split
  · unfold pbChain pbBytes pbPubkey pbKey
    have hv := pbVarint_length_le 1 (seedU32 f 262)
    have h0 := seedSlice_length_le f 198 32
    have h1 := seedSlice_length_le f 230 32
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · simp

theorem seedC3_length_le (f : List (BitVec 8)) : (seedC3 f).length ≤ 37 := by
  unfold seedC3
  split <;> decide

theorem seedSession_length_bounds (f : List (BitVec 8)) :
    10 ≤ (seedSession f).length ∧ (seedSession f).length < 16384 := by
  rw [seedSession_eq]
  have h0 := seedHdr_length_bounds f
  have h1 := seedC1_length_le f
  have h2 := seedC2_length_le f
  have h3 := seedC3_length_le f
  simp only [List.length_append]
  omega

end SeedLengthFacts

end CryptoVerification.E2E.Record

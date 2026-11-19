/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.DH.X25519
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import LibsignalBinary.Specifications.SignalPqxdh.Model
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Concrete X25519 Prime-Order Subgroup Specification

**Trusted: definitions used by the statement.** Defines the concrete Curve25519 prime-order x-only
subgroup `X25519Pt`, its RFC 7748 Diffie–Hellman action `x25519Dh`, wire encoding/decoding
(`x25519EncPt`, `x25519EncT`, `x25519DecT`), uniform subgroup sampler (`SampleableType X25519Pt`),
and clamped base-point fiber bound `x25519Delta = 1 / 2 ^ 250`. See
`Computational/docs/TRUSTED_BASE.md`.

Elements of `X25519Pt` are canonical 32-byte little-endian Montgomery u-coordinates: `0^32` (the
identity) together with the `(edOrderL - 1) / 2` canonical prime-order points satisfying
`u < p25519`, `montLiftEd u 0 = some P`, and `[edOrderL] P = edZero`. Wire decoding `x25519DecT`
is the polynomial-time canonical subgroup membership test; `x25519Dh` is RFC 7748 `x25519Ref`
restricted to `X25519Pt` (the fallback `else 0` branch is provably unreachable).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoGames.RFC7748

open scoped ENNReal
open VerifiedLibraries.Common (p25519 edOrderL leBytesToNat natToLeBytes edZero edSmul)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.Ratchet.LibsignalInst (vec32)

/-- Prime subgroup order `ℓ'` of the Curve25519 quadratic twist `E'(𝔽_p)`, satisfying
`|E'(𝔽_p)| = 4 * ℓ'` and `8 * edOrderL + 4 * twistOrderL = 2 * (p25519 + 1)`. -/
def twistOrderL : Nat :=
  14474011154664524427946373126085988481603263447650325797860494125407373907997

/-- All-zero 32-byte encoding representing the identity element of `X25519Pt`. -/
def x25519ZeroKey : PublicKey :=
  ⟨List.Vector.replicate 32 0#8⟩

/-- Standard Curve25519 Montgomery basepoint `u = 9` as a `PublicKey`. -/
def x25519BaseKey : PublicKey :=
  ⟨⟨x25519Basepoint, by simp [x25519Basepoint, natToLeBytes]⟩⟩

/-- Decidable membership predicate for the Curve25519 prime-order x-only subgroup: either `0^32`
(the identity) or a canonical Montgomery u-coordinate `< p25519` whose even-x Edwards lift lies in
the `edOrderL`-torsion subgroup. -/
def isX25519SubgroupKey (pk : PublicKey) : Bool :=
  pk == x25519ZeroKey ||
    (decide (leBytesToNat pk.bytes.toList < p25519) &&
      match SignalPqxdh.montLiftEd pk.bytes.toList 0#8 with
      | some P => edSmul edOrderL P == edZero
      | none => false)

/-- Prime-order x-only subgroup of Curve25519, represented by canonical 32-byte Montgomery
u-coordinates (`0^32` together with the `(edOrderL - 1) / 2` canonical prime-order points). -/
def X25519Pt : Type :=
  { pk : PublicKey // isX25519SubgroupKey pk = true }

instance : DecidableEq X25519Pt :=
  Subtype.instDecidableEq

instance : Zero X25519Pt :=
  ⟨⟨x25519ZeroKey, by simp [isX25519SubgroupKey]⟩⟩

/-- Finite enumeration structure on `PublicKey` via its underlying 32-byte vector. -/
@[instance_reducible] def publicKeyFintype : Fintype PublicKey :=
  Fintype.ofEquiv (List.Vector (BitVec 8) 32)
    { toFun := PublicKey.mk
      invFun := PublicKey.bytes
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Canonical uniform sampler over `X25519Pt` (uniform measure on all `(edOrderL + 1) / 2`
canonical subgroup elements). -/
noncomputable instance : SampleableType X25519Pt :=
  @SampleableType.subtype PublicKey publicKeyFintype (fun pk => isX25519SubgroupKey pk = true)
    inferInstance ⟨⟨x25519ZeroKey, by simp [isX25519SubgroupKey]⟩⟩

/-- Curve25519 Montgomery basepoint `u = 9` in `X25519Pt`. The `else 0` branch is provably
unreachable. -/
def x25519BasePt : X25519Pt :=
  if h : isX25519SubgroupKey x25519BaseKey = true then ⟨x25519BaseKey, h⟩ else 0

/-- Concrete RFC 7748 X25519 Diffie–Hellman action on `X25519Pt`. The `else 0` branch is provably
unreachable because RFC 7748 clamped scalar multiplication preserves `X25519Pt`. -/
def x25519Dh : DHFun (BitVec 256) X25519Pt where
  base := x25519BasePt
  dh k Q :=
    let pk : PublicKey := ⟨x25519Ref (vec32 (HMAC.keyToBytes32 k)) Q.val.bytes⟩
    if h : isX25519SubgroupKey pk = true then ⟨pk, h⟩ else 0

/-- 32-byte wire encoding of `Q : X25519Pt` as a `PublicKey`. -/
def x25519EncT (Q : X25519Pt) : PublicKey :=
  Q.val

/-- 32-byte little-endian Montgomery encoding of `Q : X25519Pt`. -/
def x25519EncPt (Q : X25519Pt) : List (BitVec 8) :=
  Q.val.bytes.toList

/-- Polynomial-time canonical prime-order subgroup decoder `PublicKey → Option X25519Pt`. -/
def x25519DecT (pk : PublicKey) : Option X25519Pt :=
  if h : isX25519SubgroupKey pk = true then some ⟨pk, h⟩ else none

/-- Tight clamped X25519 base-point fiber probability bound `2^-250`: each point has at most `2`
signs mod `edOrderL` times `2^5` clamped-away bits (`64 / 2^256 = 1 / 2^250`). -/
noncomputable def x25519Delta : ℝ≥0∞ :=
  (1 : ℝ≥0∞) / 2 ^ 250

end CryptoGames.RFC7748

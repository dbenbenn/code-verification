/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Common.Spec.Curve25519
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession

/-!
# RFC 7748 X25519 Specification

**Trusted: definitions used by the statement.** Direct transcription of RFC 7748 (§5, §6.1) for
Curve25519 Montgomery-ladder Diffie-Hellman (`x25519Ref : CryptoGames.Ratchet.X25519Fn`) and
basepoint public-key derivation (`x25519PubFromSecretRef : CryptoGames.LibsignalSession.PubKeyFn`).
See `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoGames.RFC7748

open VerifiedLibraries.Common (
  p25519 fpAdd fpSub fpMul fpSq fpInv
  leBytesToNat natToLeBytes clampScalar
)
open CryptoGames.Ratchet (X25519Fn)
open CryptoGames.LibsignalSession (PubKeyFn)

/-- Montgomery curve constant $a_{24} = (486662 - 2) / 4 = 121665$ (RFC 7748 §5). -/
abbrev a24 : Nat := 121665

/-- Decode a 32-byte little-endian Montgomery $u$-coordinate by masking bit 255
(RFC 7748 §5 `decodeUCoordinate(u, 255)`). -/
def decodeU255 (bs : List (BitVec 8)) : Nat :=
  leBytesToNat (bs.take 32) % (2 ^ 255)

/-- Projective Kummer-line point $(U : W)$ on Montgomery Curve25519 $B v^2 = u^3 + 486662 u^2 + u$
representing $u = U \cdot W^{-1} \bmod p$ (with $(1 : 0)$ denoting $\mathcal{O}$). -/
structure MontProjPoint where
  U : Nat
  W : Nat
  deriving DecidableEq, Repr

/-- One combined differential-addition and point-doubling step on the Curve25519 Kummer line
(RFC 7748 §5 / Costello-Smith 2017 Algorithm 8): given $u_1 = u(P - Q)$ and $(P, Q)$,
returns $([2]P, P + Q)$. -/
def montDiffAddAndDouble (u1 : Nat) (P Q : MontProjPoint) :
    MontProjPoint × MontProjPoint :=
  let A := fpAdd P.U P.W
  let AA := fpSq A
  let B := fpSub P.U P.W
  let BB := fpSq B
  let E := fpSub AA BB
  let C := fpAdd Q.U Q.W
  let D := fpSub Q.U Q.W
  let DA := fpMul D A
  let CB := fpMul C B
  let U2 := fpMul AA BB
  let W2 := fpMul E (fpAdd AA (fpMul a24 E))
  let U3 := fpSq (fpAdd DA CB)
  let W3 := fpMul u1 (fpSq (fpSub DA CB))
  (⟨U2, W2⟩, ⟨U3, W3⟩)

/-- 255-bit big-endian Montgomery ladder loop (RFC 7748 §5 / `MontgomeryPoint::mul_bits_be`):
processes bits `fuel - 1` down to `0` of scalar `k`. -/
def montLadderLoop : Nat → Nat → Nat → MontProjPoint → MontProjPoint → MontProjPoint
  | 0, _, _, x0, _ => x0
  | fuel + 1, k, u1, x0, x1 =>
    let bit := (k / (2 ^ fuel)) % 2
    let (p0, p1) := if bit == 1 then (x1, x0) else (x0, x1)
    let (q0, q1) := montDiffAddAndDouble u1 p0 p1
    let (x0', x1') := if bit == 1 then (q1, q0) else (q0, q1)
    montLadderLoop fuel k u1 x0' x1'

/-- Pure integer-to-field RFC 7748 Montgomery ladder: reduces `u` mod $p$, runs 255 steps of
`montLadderLoop` with scalar `k`, and returns $U \cdot W^{p - 2} \bmod p$. -/
def x25519Ladder (k u : Nat) : Nat :=
  let u1 := u % p25519
  let res := montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩
  fpMul res.U (fpInv res.W)

/-- RFC 7748 §5 `X25519(k, u)` Diffie-Hellman function
(`StaticSecret::from(k).diffie_hellman(&PublicKey::from(u))`):
clamps `scalar`, decodes `uBytes` mod $2^{255}$ and mod $p$, runs the 255-bit Montgomery ladder,
and encodes $U \cdot W^{p - 2} \bmod p$ as 32 little-endian bytes. -/
def x25519 (scalar uBytes : List (BitVec 8)) : List (BitVec 8) :=
  natToLeBytes 32 (x25519Ladder (clampScalar scalar) (decodeU255 uBytes))

/-- Standard Curve25519 Montgomery basepoint $u = 9$ encoded as 32 little-endian bytes (RFC 7748 §6.1). -/
def x25519Basepoint : List (BitVec 8) :=
  natToLeBytes 32 9

/-- Derive the 32-byte X25519 public key from a 32-byte secret key (RFC 7748 §6.1: `X25519(secret, 9)`). -/
def x25519Pubkey (secret : List (BitVec 8)) : List (BitVec 8) :=
  x25519 secret x25519Basepoint

/-- Concrete RFC 7748 X25519 Diffie-Hellman function `W.C.X : CryptoGames.Ratchet.X25519Fn`. -/
def x25519Ref : X25519Fn :=
  fun sec pub => ⟨x25519 sec.toList pub.toList, by simp [x25519, natToLeBytes]⟩

/-- Concrete RFC 7748 X25519 public-key derivation `W.C.pubKey : CryptoGames.LibsignalSession.PubKeyFn`. -/
def x25519PubFromSecretRef : PubKeyFn :=
  fun sec => ⟨x25519Pubkey sec.toList, by simp [x25519Pubkey, x25519, natToLeBytes]⟩

end CryptoGames.RFC7748

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# Curve25519 Field $\mathbb{F}_p$, Twisted Edwards Curve, and Point Codec

Computable specification of prime-field arithmetic over $\mathbb{F}_p$ ($p = 2^{255} - 19$),
the twisted Edwards curve $-x^2 + y^2 \equiv 1 + d x^2 y^2 \pmod p$ in affine and extended
coordinates (RFC 8032 Section 5.1), 32-byte little-endian point compression and decompression
(`decodeEdDalek` and strict `decodeEdRfc`), and RFC 8032 scalar clamping.
-/

@[expose] public section

namespace VerifiedLibraries.Common

/-! ## Field $\mathbb{F}_p$ ($p = 2^{255} - 19$) and Scalar Order $\ell$ -/

/-- Prime modulus $p = 2^{255} - 19$ of Curve25519. -/
abbrev p25519 : Nat := 2 ^ 255 - 19

/-- Prime order $\ell = 2^{252} + 27742317777372353535851937790883648493$ of the Ed25519 basepoint subgroup. -/
abbrev edOrderL : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- Structural-recursion modular exponentiation `(acc * base ^ exp) % m` for up to `fuel` bits. -/
def modPowLoop : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m, acc => acc % m
  | fuel + 1, base, exp, m, acc =>
    if exp == 0 then acc % m
    else
      let acc' := if exp % 2 == 1 then (acc * base) % m else acc
      modPowLoop fuel ((base * base) % m) (exp / 2) m acc'

/-- Computable modular exponentiation `base ^ exp % m` (up to 256-bit exponents). -/
def modPow (base exp m : Nat) : Nat :=
  modPowLoop 256 (base % m) exp m 1

/-- Field addition $(a + b) \bmod p$. -/
def fpAdd (a b : Nat) : Nat := (a + b) % p25519

/-- Field subtraction $(a - b) \bmod p$. -/
def fpSub (a b : Nat) : Nat := (a + p25519 - (b % p25519)) % p25519

/-- Field negation $(-a) \bmod p$. -/
def fpNeg (a : Nat) : Nat := (p25519 - (a % p25519)) % p25519

/-- Field multiplication $(a \cdot b) \bmod p$. -/
def fpMul (a b : Nat) : Nat := ((a % p25519) * (b % p25519)) % p25519

/-- Field squaring $a^2 \bmod p$. -/
def fpSq (a : Nat) : Nat := fpMul a a

/-- Field exponentiation $a^e \bmod p$. -/
def fpPow (a e : Nat) : Nat := modPow a e p25519

/-- Field multiplicative inverse $a^{p - 2} \bmod p$ (by Fermat's Little Theorem; maps $0 \mapsto 0$). -/
def fpInv (a : Nat) : Nat := fpPow a (p25519 - 2)

/-- Principal square root of $-1$ in $\mathbb{F}_p$: $I = 2^{(p - 1) / 4} \bmod p$ (RFC 8032 §5.1.3). -/
def sqrtM1 : Nat :=
  19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- Twisted Edwards curve constant $d = -121665 / 121666 \bmod p$ (RFC 8032 §5.1). -/
def edD : Nat :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- $2 d \bmod p$ used in extended twisted Edwards point addition (RFC 8032 §5.1.4). -/
def edD2 : Nat :=
  fpAdd edD edD

/-! ## Twisted Edwards Curve $E(\mathbb{F}_p)$: $-x^2 + y^2 \equiv 1 + d x^2 y^2 \pmod p$ -/

/-- Affine point $(x, y) \in \mathbb{F}_p \times \mathbb{F}_p$ on the twisted Edwards curve. -/
structure EdPoint where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

/-- Homogeneous extended point $(X : Y : Z : T)$ with $x = X / Z$, $y = Y / Z$, $x y = T / Z$
    (RFC 8032 §5.1.4). -/
structure EdExtPoint where
  X : Nat
  Y : Nat
  Z : Nat
  T : Nat
  deriving DecidableEq, Repr

/-- Neutral element $\mathcal{O} = (0, 1)$ of the twisted Edwards curve. -/
def edZero : EdPoint := ⟨0, 1⟩

/-- Extended neutral element $(0, 1, 1, 0)$. -/
def edExtZero : EdExtPoint := ⟨0, 1, 1, 0⟩

/-- Lift an affine point $P = (x, y)$ to extended coordinates $(x \bmod p, y \bmod p, 1, x y \bmod p)$. -/
def edExtOfAffine (P : EdPoint) : EdExtPoint :=
  let x := P.x % p25519
  let y := P.y % p25519
  ⟨x, y, 1, fpMul x y⟩

/-- Project an extended point $(X, Y, Z, T)$ to affine coordinates $(X Z^{-1} \bmod p, Y Z^{-1} \bmod p)$. -/
def edExtToAffine (P : EdExtPoint) : EdPoint :=
  let zInv := fpInv P.Z
  ⟨fpMul P.X zInv, fpMul P.Y zInv⟩

/-- Standard Ed25519 basepoint $B = (B_x, 4/5 \bmod p)$ (RFC 8032 §5.1). -/
def edBasepoint : EdPoint :=
  ⟨15112221349535400772501151409588531511454012693041857206046113283949847762202,
   46316835694926478169428394003475163141307993866256225615783033603165251855960⟩

/-- Boolean check that $P = (x, y)$ has canonical coordinates $x, y < p$ satisfying
    $-x^2 + y^2 \equiv 1 + d x^2 y^2 \pmod p$. -/
def edOnCurve (P : EdPoint) : Bool :=
  P.x < p25519 && P.y < p25519 &&
  fpAdd (fpNeg (fpSq P.x)) (fpSq P.y) ==
    fpAdd 1 (fpMul edD (fpMul (fpSq P.x) (fpSq P.y)))

/-- Complete extended twisted Edwards point addition (RFC 8032 §5.1.4, 8 field multiplications,
    0 inversions). -/
def edExtAdd (P Q : EdExtPoint) : EdExtPoint :=
  let A := fpMul (fpSub P.Y P.X) (fpSub Q.Y Q.X)
  let B := fpMul (fpAdd P.Y P.X) (fpAdd Q.Y Q.X)
  let C := fpMul P.T (fpMul edD2 Q.T)
  let D := fpMul P.Z (fpAdd Q.Z Q.Z)
  let E := fpSub B A
  let F := fpSub D C
  let G := fpAdd D C
  let H := fpAdd B A
  ⟨fpMul E F, fpMul G H, fpMul F G, fpMul E H⟩

/-- Complete twisted Edwards affine point addition (RFC 8032 §5.1.4):
    $x_3 = (x_1 y_2 + y_1 x_2) / (1 + d x_1 x_2 y_1 y_2) \bmod p$,
    $y_3 = (y_1 y_2 + x_1 x_2) / (1 - d x_1 x_2 y_1 y_2) \bmod p$. -/
def edAdd (P Q : EdPoint) : EdPoint :=
  let x1y2 := fpMul P.x Q.y
  let y1x2 := fpMul P.y Q.x
  let y1y2 := fpMul P.y Q.y
  let x1x2 := fpMul P.x Q.x
  let dxxyy := fpMul edD (fpMul x1x2 y1y2)
  let x3 := fpMul (fpAdd x1y2 y1x2) (fpInv (fpAdd 1 dxxyy))
  let y3 := fpMul (fpAdd y1y2 x1x2) (fpInv (fpSub 1 dxxyy))
  ⟨x3, y3⟩

/-- Twisted Edwards point negation $-(x, y) = (-x \bmod p, y \bmod p)$. -/
def edNeg (P : EdPoint) : EdPoint :=
  ⟨fpNeg P.x, P.y % p25519⟩

/-- Twisted Edwards point subtraction $P - Q = P + (-Q)$. -/
def edSub (P Q : EdPoint) : EdPoint :=
  edAdd P (edNeg Q)

/-- Structural-recursion double-and-add scalar multiplication loop `acc + [n]P` in extended
    coordinates for up to `fuel` bits. -/
def edExtSmulLoop : Nat → Nat → EdExtPoint → EdExtPoint → EdExtPoint
  | 0, _, _, acc => acc
  | fuel + 1, n, P, acc =>
    if n == 0 then acc
    else
      let acc' := if n % 2 == 1 then edExtAdd acc P else acc
      edExtSmulLoop fuel (n / 2) (edExtAdd P P) acc'

/-- Scalar multiplication $[n]P$ on the twisted Edwards curve (up to 256-bit scalars). -/
def edSmul (n : Nat) (P : EdPoint) : EdPoint :=
  edExtToAffine (edExtSmulLoop 256 n (edExtOfAffine P) edExtZero)

/-- Cofactor-8 small-order check: `true` iff $[8]P = \mathcal{O}$ (`EdwardsPoint::is_small_order`). -/
def isSmallOrder (P : EdPoint) : Bool :=
  edSmul 8 P == edZero

/-! ## Point Compression, Decompression, and Scalar Clamping -/

/-- Decode a little-endian byte list into a natural number $\sum_{i} b_i \cdot 256^i$. -/
def leBytesToNat (bs : List (BitVec 8)) : Nat :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- Encode a natural number `n` into `len` little-endian bytes (`n mod 256^len`). -/
def natToLeBytes (len n : Nat) : List (BitVec 8) :=
  (List.range len).map fun i => BitVec.ofNat 8 ((n / (256 ^ i)) % 256)

/-- Compress an Edwards point $P = (x, y)$ to 32 little-endian bytes (RFC 8032 §5.1.2):
    low 255 bits encode $y \bmod p$, bit 255 encodes $(x \bmod p) \bmod 2$. -/
def encodeEd (P : EdPoint) : List (BitVec 8) :=
  let y := P.y % p25519
  let sign := (P.x % p25519) % 2
  natToLeBytes 32 (y + sign * (2 ^ 255))

/-- Recover the unique even square root $x \in [0, p)$ (`x % 2 = 0`) of
    $u / v = (y^2 - 1) / (d y^2 + 1) \pmod p$ via `sqrt_ratio_i` (RFC 8032 §5.1.3). -/
def recoverXEven (y : Nat) : Option Nat :=
  let y2 := fpSq y
  let u := fpSub y2 1
  let v := fpAdd (fpMul edD y2) 1
  let v3 := fpMul (fpSq v) v
  let v7 := fpMul (fpSq v3) v
  let r0 := fpMul (fpMul u v3) (fpPow (fpMul u v7) ((p25519 - 5) / 8))
  let check := fpMul v (fpSq r0)
  if check == u then
    some (if r0 % 2 == 1 then fpNeg r0 else r0)
  else if check == fpNeg u then
    let r1 := fpMul r0 sqrtM1
    some (if r1 % 2 == 1 then fpNeg r1 else r1)
  else
    none

/-- `curve25519-dalek` point decompression (`CompressedEdwardsY::decompress`, ZIP-215 point rules):
    reduces the 255-bit $y$-coordinate modulo $p$ (accepting $y_{\text{raw}} \in [p, 2^{255})$) and
    negates $x_{\text{even}}$ when $\text{sign} = 1$ (accepting $x_{\text{even}} = 0, \text{sign} = 1$
    as $x = 0$). -/
def decodeEdDalek (bs : List (BitVec 8)) : Option EdPoint :=
  if bs.length != 32 then none
  else
    let n := leBytesToNat bs
    let yRaw := n % (2 ^ 255)
    let sign := (n / (2 ^ 255)) % 2
    let y := yRaw % p25519
    match recoverXEven y with
    | none => none
    | some xEven =>
      let x := if sign == 1 then fpNeg xEven else xEven
      some ⟨x, y⟩

/-- RFC 8032 §5.1.3 canonical point decompression: requires $y_{\text{raw}} < p$ and rejects
    $(x = 0, \text{sign} = 1)$ (`-0`). -/
def decodeEdRfc (bs : List (BitVec 8)) : Option EdPoint :=
  if bs.length != 32 then none
  else
    let n := leBytesToNat bs
    let yRaw := n % (2 ^ 255)
    let sign := (n / (2 ^ 255)) % 2
    if yRaw >= p25519 then none
    else
      match recoverXEven yRaw with
      | none => none
      | some xEven =>
        if xEven == 0 && sign == 1 then none
        else
          let x := if sign == 1 then fpNeg xEven else xEven
          some ⟨x, yRaw⟩

/-- Clamp a 32-byte little-endian scalar array per RFC 8032 §5.1.5 (`curve25519_dalek::scalar::clamp_integer`):
    clear bits $0, 1, 2$ of byte $0$, clear bit $7$ of byte $31$, and set bit $6$ of byte $31$. -/
def clampScalarBytes (bs : List (BitVec 8)) : List (BitVec 8) :=
  let b0 := (bs.getD 0 0#8) &&& 0xf8#8
  let b31 := ((bs.getD 31 0#8) &&& 0x7f#8) ||| 0x40#8
  [b0] ++ (bs.drop 1).take 30 ++ [b31]

/-- Clamped secret scalar integer $a \in [2^{254}, 2^{255} - 8]$ from the first 32 bytes of `SHA-512(seed)`. -/
def clampScalar (bs : List (BitVec 8)) : Nat :=
  leBytesToNat (clampScalarBytes (bs.take 32))

end VerifiedLibraries.Common

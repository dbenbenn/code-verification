/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Common.Spec.Curve25519
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.DH.X25519

/-!
# RFC 7748 X25519 Reference and Test Vectors

Re-exports `CryptoGames.RFC7748` from `LibsignalBinary.Specifications.CryptoGames.DH.X25519`,
together with clamping idempotence, Edwards-lift canonicality helpers, and kernel-checked
RFC 7748 and `libsignal-core` test vectors.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref

open VerifiedLibraries.Common (
  p25519 edOrderL fpAdd fpSub fpNeg fpMul fpSq fpInv
  EdPoint edZero edBasepoint edSmul isSmallOrder
  leBytesToNat natToLeBytes recoverXEven clampScalarBytes clampScalar
)
open CryptoGames.Ratchet (X25519Fn)
open CryptoGames.LibsignalSession (PubKeyFn)

/-! ## 1. RFC 7748 Montgomery Ladder & Hook Reference Functions -/

export CryptoGames.RFC7748 (a24 decodeU255 MontProjPoint montDiffAddAndDouble montLadderLoop)
export CryptoGames.RFC7748 (x25519Ladder x25519 x25519Basepoint x25519Pubkey x25519Ref)
export CryptoGames.RFC7748 (x25519PubFromSecretRef)

/-- Clamped X25519 scalar integer $k \in [2^{254}, 2^{255} - 8] \cap 8\mathbb{Z}$ from 32 LE bytes. -/
abbrev clampScalar25519 (bs : List (BitVec 8)) : Nat :=
  clampScalar bs

theorem x25519_length (scalar uBytes : List (BitVec 8)) :
    (x25519 scalar uBytes).length = 32 := by
  simp [x25519, natToLeBytes]

theorem x25519Pubkey_length (secret : List (BitVec 8)) :
    (x25519Pubkey secret).length = 32 :=
  x25519_length secret x25519Basepoint

@[simp] theorem x25519Ref_toList (sec pub : List.Vector (BitVec 8) 32) :
    (x25519Ref sec pub).toList = x25519 sec.toList pub.toList := rfl

@[simp] theorem x25519PubFromSecretRef_toList (sec : List.Vector (BitVec 8) 32) :
    (x25519PubFromSecretRef sec).toList = x25519Pubkey sec.toList := rfl

/-! ## 2. Clamping Idempotence Under `CryptoGames.Ratchet.clampScalar` -/

private theorem clamp_b0_idem (b : BitVec 8) :
    (b &&& 0xf8#8) &&& 0xf8#8 = b &&& 0xf8#8 := by
  revert b; decide

private theorem clamp_b31_idem (b : BitVec 8) :
    (((b &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8 = (b &&& 0x7f#8) ||| 0x40#8 := by
  revert b; decide

theorem clampScalarBytes_ratchet_clampScalar (k : List.Vector (BitVec 8) 32) :
    clampScalarBytes (CryptoGames.Ratchet.clampScalar k).toList = clampScalarBytes k.toList := by
  rcases k with ⟨bs, hbs⟩
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (exfalso; simp at hbs; done)
  change [(b0 &&& 0xf8#8) &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13,
      b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      (((b31 &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8] =
    [b0 &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
      b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      (b31 &&& 0x7f#8) ||| 0x40#8]
  rw [clamp_b0_idem, clamp_b31_idem]

theorem clampScalar_ratchet_clampScalar (k : List.Vector (BitVec 8) 32) :
    clampScalar (CryptoGames.Ratchet.clampScalar k).toList = clampScalar k.toList := by
  have hlen1 : (CryptoGames.Ratchet.clampScalar k).toList.length = 32 :=
    (CryptoGames.Ratchet.clampScalar k).2
  have hlen2 : k.toList.length = 32 := k.2
  simp only [clampScalar, List.take_of_length_le (Nat.le_of_eq hlen1),
    List.take_of_length_le (Nat.le_of_eq hlen2), clampScalarBytes_ratchet_clampScalar]

theorem x25519Ref_clampScalar_eq (sec pub : List.Vector (BitVec 8) 32) :
    x25519Ref (CryptoGames.Ratchet.clampScalar sec) pub = x25519Ref sec pub := by
  apply Subtype.ext
  simp [x25519Ref, x25519, clampScalar_ratchet_clampScalar]

theorem x25519PubFromSecretRef_clampScalar_eq (sec : List.Vector (BitVec 8) 32) :
    x25519PubFromSecretRef (CryptoGames.Ratchet.clampScalar sec) = x25519PubFromSecretRef sec := by
  apply Subtype.ext
  simp [x25519PubFromSecretRef, x25519Pubkey, x25519, clampScalar_ratchet_clampScalar]

/-! ## 3. Montgomery–Edwards Lift, Canonicality, & Low-Order $u$-Coordinates -/

/-- Lift a 32-byte Montgomery $u$-coordinate and sign bit `sign ∈ {0, 1}` to an affine twisted
    Edwards point (`MontgomeryPoint::to_edwards`): decodes $u = \text{decodeU255}(\text{bs}) \bmod p$,
    rejects $u = p - 1$, computes $y = (u - 1) \cdot (u + 1)^{-1} \bmod p$, recovers $x_{\text{even}}$
    via `recoverXEven y`, and negates $x_{\text{even}}$ when `sign % 2 == 1`. -/
@[expose] def montToEdwards (bs : List (BitVec 8)) (sign : Nat) : Option EdPoint :=
  let u := decodeU255 bs % p25519
  if u == p25519 - 1 then none
  else
    let y := fpMul (fpSub u 1) (fpInv (fpAdd u 1))
    match recoverXEven y with
    | none => none
    | some xEven =>
      let x := if sign % 2 == 1 then fpNeg xEven else xEven
      some ⟨x, y⟩

/-- Exact `libsignal-core` `PublicKey::is_canonical` predicate (`curve.rs:165-190`):
    `true` iff `bs` is a 32-byte canonical integer `< p25519` whose Montgomery lift
    `montToEdwards bs 0` lies on $E(\mathbb{F}_p)$ and has prime order dividing $\ell$
    (`[ℓ]P = edZero`, `EdwardsPoint::is_torsion_free`). -/
@[expose] def isCanonicalX25519 (bs : List (BitVec 8)) : Bool :=
  bs.length == 32 &&
  leBytesToNat bs < p25519 &&
  match montToEdwards bs 0 with
  | none => false
  | some P => edSmul edOrderL P == edZero

/-- The 5 canonical elements $u \in \mathbb{F}_p$ for which `X25519(s, u)` produces the all-zero
    output for every clamped scalar $k \in 8\mathbb{Z}$ (RFC 7748 §6.1): the four $u$-coordinates
    on $E(\mathbb{F}_p)[8]$ (`0`, `1`, and the two order-8 $u$-coordinates) together with
    `p25519 - 1`, the order-4 point on the quadratic twist $E'(\mathbb{F}_p)$. -/
@[expose] def lowOrderUs : List Nat :=
  [ 0,
    1,
    325606250916557431795983626356110631294008115727848805560023387167927233504,
    39382357235489614581723060781553021112529911719440698176882885853963445705823,
    p25519 - 1 ]

/-! ## 4. Kernel-Checked RFC 7748 §5.2, §6.1, Low-Order/Twist, & `libsignal` Test Vectors -/

section TestVectors

set_option exponentiation.threshold 2048

@[expose] def rfc7748Scalar1 : List (BitVec 8) :=
  [ 0xa5#8, 0x46#8, 0xe3#8, 0x6b#8, 0xf0#8, 0x52#8, 0x7c#8, 0x9d#8,
    0x3b#8, 0x16#8, 0x15#8, 0x4b#8, 0x82#8, 0x46#8, 0x5e#8, 0xdd#8,
    0x62#8, 0x14#8, 0x4c#8, 0x0a#8, 0xc1#8, 0xfc#8, 0x5a#8, 0x18#8,
    0x50#8, 0x6a#8, 0x22#8, 0x44#8, 0xba#8, 0x44#8, 0x9a#8, 0xc4#8 ]

@[expose] def rfc7748U1 : List (BitVec 8) :=
  [ 0xe6#8, 0xdb#8, 0x68#8, 0x67#8, 0x58#8, 0x30#8, 0x30#8, 0xdb#8,
    0x35#8, 0x94#8, 0xc1#8, 0xa4#8, 0x24#8, 0xb1#8, 0x5f#8, 0x7c#8,
    0x72#8, 0x66#8, 0x24#8, 0xec#8, 0x26#8, 0xb3#8, 0x35#8, 0x3b#8,
    0x10#8, 0xa9#8, 0x03#8, 0xa6#8, 0xd0#8, 0xab#8, 0x1c#8, 0x4c#8 ]

@[expose] def rfc7748Out1 : List (BitVec 8) :=
  [ 0xc3#8, 0xda#8, 0x55#8, 0x37#8, 0x9d#8, 0xe9#8, 0xc6#8, 0x90#8,
    0x8e#8, 0x94#8, 0xea#8, 0x4d#8, 0xf2#8, 0x8d#8, 0x08#8, 0x4f#8,
    0x32#8, 0xec#8, 0xcf#8, 0x03#8, 0x49#8, 0x1c#8, 0x71#8, 0xf7#8,
    0x54#8, 0xb4#8, 0x07#8, 0x55#8, 0x77#8, 0xa2#8, 0x85#8, 0x52#8 ]

@[expose] def rfc7748Scalar2 : List (BitVec 8) :=
  [ 0x4b#8, 0x66#8, 0xe9#8, 0xd4#8, 0xd1#8, 0xb4#8, 0x67#8, 0x3c#8,
    0x5a#8, 0xd2#8, 0x26#8, 0x91#8, 0x95#8, 0x7d#8, 0x6a#8, 0xf5#8,
    0xc1#8, 0x1b#8, 0x64#8, 0x21#8, 0xe0#8, 0xea#8, 0x01#8, 0xd4#8,
    0x2c#8, 0xa4#8, 0x16#8, 0x9e#8, 0x79#8, 0x18#8, 0xba#8, 0x0d#8 ]

@[expose] def rfc7748U2 : List (BitVec 8) :=
  [ 0xe5#8, 0x21#8, 0x0f#8, 0x12#8, 0x78#8, 0x68#8, 0x11#8, 0xd3#8,
    0xf4#8, 0xb7#8, 0x95#8, 0x9d#8, 0x05#8, 0x38#8, 0xae#8, 0x2c#8,
    0x31#8, 0xdb#8, 0xe7#8, 0x10#8, 0x6f#8, 0xc0#8, 0x3c#8, 0x3e#8,
    0xfc#8, 0x4c#8, 0xd5#8, 0x49#8, 0xc7#8, 0x15#8, 0xa4#8, 0x93#8 ]

@[expose] def rfc7748Out2 : List (BitVec 8) :=
  [ 0x95#8, 0xcb#8, 0xde#8, 0x94#8, 0x76#8, 0xe8#8, 0x90#8, 0x7d#8,
    0x7a#8, 0xad#8, 0xe4#8, 0x5c#8, 0xb4#8, 0xb8#8, 0x73#8, 0xf8#8,
    0x8b#8, 0x59#8, 0x5a#8, 0x68#8, 0x79#8, 0x9f#8, 0xa1#8, 0x52#8,
    0xe6#8, 0xf8#8, 0xf7#8, 0x64#8, 0x7a#8, 0xac#8, 0x79#8, 0x57#8 ]

set_option maxHeartbeats 800000 in
theorem rfc7748_section_5_2_ok :
    x25519 rfc7748Scalar1 rfc7748U1 = rfc7748Out1 ∧
    x25519 rfc7748Scalar2 rfc7748U2 = rfc7748Out2 := by
  decide +kernel

@[expose] def rfc7748AlicePriv : List (BitVec 8) :=
  [ 0x77#8, 0x07#8, 0x6d#8, 0x0a#8, 0x73#8, 0x18#8, 0xa5#8, 0x7d#8,
    0x3c#8, 0x16#8, 0xc1#8, 0x72#8, 0x51#8, 0xb2#8, 0x66#8, 0x45#8,
    0xdf#8, 0x4c#8, 0x2f#8, 0x87#8, 0xeb#8, 0xc0#8, 0x99#8, 0x2a#8,
    0xb1#8, 0x77#8, 0xfb#8, 0xa5#8, 0x1d#8, 0xb9#8, 0x2c#8, 0x2a#8 ]

@[expose] def rfc7748AlicePub : List (BitVec 8) :=
  [ 0x85#8, 0x20#8, 0xf0#8, 0x09#8, 0x89#8, 0x30#8, 0xa7#8, 0x54#8,
    0x74#8, 0x8b#8, 0x7d#8, 0xdc#8, 0xb4#8, 0x3e#8, 0xf7#8, 0x5a#8,
    0x0d#8, 0xbf#8, 0x3a#8, 0x0d#8, 0x26#8, 0x38#8, 0x1a#8, 0xf4#8,
    0xeb#8, 0xa4#8, 0xa9#8, 0x8e#8, 0xaa#8, 0x9b#8, 0x4e#8, 0x6a#8 ]

@[expose] def rfc7748BobPriv : List (BitVec 8) :=
  [ 0x5d#8, 0xab#8, 0x08#8, 0x7e#8, 0x62#8, 0x4a#8, 0x8a#8, 0x4b#8,
    0x79#8, 0xe1#8, 0x7f#8, 0x8b#8, 0x83#8, 0x80#8, 0x0e#8, 0xe6#8,
    0x6f#8, 0x3b#8, 0xb1#8, 0x29#8, 0x26#8, 0x18#8, 0xb6#8, 0xfd#8,
    0x1c#8, 0x2f#8, 0x8b#8, 0x27#8, 0xff#8, 0x88#8, 0xe0#8, 0xeb#8 ]

@[expose] def rfc7748BobPub : List (BitVec 8) :=
  [ 0xde#8, 0x9e#8, 0xdb#8, 0x7d#8, 0x7b#8, 0x7d#8, 0xc1#8, 0xb4#8,
    0xd3#8, 0x5b#8, 0x61#8, 0xc2#8, 0xec#8, 0xe4#8, 0x35#8, 0x37#8,
    0x3f#8, 0x83#8, 0x43#8, 0xc8#8, 0x5b#8, 0x78#8, 0x67#8, 0x4d#8,
    0xad#8, 0xfc#8, 0x7e#8, 0x14#8, 0x6f#8, 0x88#8, 0x2b#8, 0x4f#8 ]

@[expose] def rfc7748Shared : List (BitVec 8) :=
  [ 0x4a#8, 0x5d#8, 0x9d#8, 0x5b#8, 0xa4#8, 0xce#8, 0x2d#8, 0xe1#8,
    0x72#8, 0x8e#8, 0x3b#8, 0xf4#8, 0x80#8, 0x35#8, 0x0f#8, 0x25#8,
    0xe0#8, 0x7e#8, 0x21#8, 0xc9#8, 0x47#8, 0xd1#8, 0x9e#8, 0x33#8,
    0x76#8, 0xf0#8, 0x9b#8, 0x3c#8, 0x1e#8, 0x16#8, 0x17#8, 0x42#8 ]

set_option maxHeartbeats 800000 in
theorem rfc7748_section_6_1_ok :
    x25519Pubkey rfc7748AlicePriv = rfc7748AlicePub ∧
    x25519Pubkey rfc7748BobPriv = rfc7748BobPub ∧
    isCanonicalX25519 rfc7748AlicePub = true ∧
    isCanonicalX25519 rfc7748BobPub = true ∧
    x25519 rfc7748AlicePriv rfc7748BobPub = rfc7748Shared ∧
    x25519 rfc7748BobPriv rfc7748AlicePub = rfc7748Shared := by
  decide +kernel

@[expose] def zeroBytes32 : List (BitVec 8) := List.replicate 32 0#8

@[expose] def mixedOrderPub : List (BitVec 8) :=
  [ 0xa9#8, 0x56#8, 0x56#8, 0x02#8, 0xff#8, 0x57#8, 0x5d#8, 0x6f#8,
    0xb9#8, 0x6f#8, 0xc1#8, 0xf6#8, 0x25#8, 0x15#8, 0x40#8, 0xe1#8,
    0x1e#8, 0x65#8, 0x8d#8, 0x27#8, 0xe1#8, 0x5c#8, 0x62#8, 0x70#8,
    0x60#8, 0x20#8, 0xf0#8, 0xb1#8, 0xf9#8, 0x96#8, 0xe7#8, 0x15#8 ]

set_option maxHeartbeats 1600000 in
theorem low_order_noncanonical_and_twist_ok :
    (lowOrderUs.all fun u =>
      let bs := natToLeBytes 32 u
      x25519 rfc7748AlicePriv bs == zeroBytes32 &&
      !isCanonicalX25519 bs) = true ∧
    (let lowVariants :=
       [ natToLeBytes 32 p25519,
         natToLeBytes 32 (p25519 + 1),
         natToLeBytes 32 (325606250916557431795983626356110631294008115727848805560023387167927233504 + 2 ^ 255) ]
     lowVariants.all fun bs =>
       x25519 rfc7748AlicePriv bs == zeroBytes32 &&
       !isCanonicalX25519 bs) = true ∧
    isCanonicalX25519 x25519Basepoint = true ∧
    isCanonicalX25519 (natToLeBytes 32 (9 + p25519)) = false ∧
    isCanonicalX25519 (natToLeBytes 32 (9 + 2 ^ 255)) = false ∧
    decide (leBytesToNat mixedOrderPub < p25519) = true ∧
    (match montToEdwards mixedOrderPub 0 with
     | some P => !isSmallOrder P && (edSmul edOrderL P != edZero)
     | none => false) = true ∧
    isCanonicalX25519 mixedOrderPub = false ∧
    (x25519 rfc7748AlicePriv mixedOrderPub != zeroBytes32) = true ∧
    isCanonicalX25519 (natToLeBytes 32 2) = false ∧
    (x25519 rfc7748AlicePriv (natToLeBytes 32 2) != zeroBytes32) = true := by
  decide +kernel

@[expose] def signalAlicePub : List (BitVec 8) :=
  [ 0x1b#8, 0xb7#8, 0x59#8, 0x66#8, 0xf2#8, 0xe9#8, 0x3a#8, 0x36#8,
    0x91#8, 0xdf#8, 0xff#8, 0x94#8, 0x2b#8, 0xb2#8, 0xa4#8, 0x66#8,
    0xa1#8, 0xc0#8, 0x8b#8, 0x8d#8, 0x78#8, 0xca#8, 0x3f#8, 0x4d#8,
    0x6d#8, 0xf8#8, 0xb8#8, 0xbf#8, 0xa2#8, 0xe4#8, 0xee#8, 0x28#8 ]

@[expose] def signalAlicePriv : List (BitVec 8) :=
  [ 0xc8#8, 0x06#8, 0x43#8, 0x9d#8, 0xc9#8, 0xd2#8, 0xc4#8, 0x76#8,
    0xff#8, 0xed#8, 0x8f#8, 0x25#8, 0x80#8, 0xc0#8, 0x88#8, 0x8d#8,
    0x58#8, 0xab#8, 0x40#8, 0x6b#8, 0xf7#8, 0xae#8, 0x36#8, 0x98#8,
    0x87#8, 0x90#8, 0x21#8, 0xb9#8, 0x6b#8, 0xb4#8, 0xbf#8, 0x59#8 ]

@[expose] def signalBobPub : List (BitVec 8) :=
  [ 0x65#8, 0x36#8, 0x14#8, 0x99#8, 0x3d#8, 0x2b#8, 0x15#8, 0xee#8,
    0x9e#8, 0x5f#8, 0xd3#8, 0xd8#8, 0x6c#8, 0xe7#8, 0x19#8, 0xef#8,
    0x4e#8, 0xc1#8, 0xda#8, 0xae#8, 0x18#8, 0x86#8, 0xa8#8, 0x7b#8,
    0x3f#8, 0x5f#8, 0xa9#8, 0x56#8, 0x5a#8, 0x27#8, 0xa2#8, 0x2f#8 ]

@[expose] def signalBobPriv : List (BitVec 8) :=
  [ 0xb0#8, 0x3b#8, 0x34#8, 0xc3#8, 0x3a#8, 0x1c#8, 0x44#8, 0xf2#8,
    0x25#8, 0xb6#8, 0x62#8, 0xd2#8, 0xbf#8, 0x48#8, 0x59#8, 0xb8#8,
    0x13#8, 0x54#8, 0x11#8, 0xfa#8, 0x7b#8, 0x03#8, 0x86#8, 0xd4#8,
    0x5f#8, 0xb7#8, 0x5d#8, 0xc5#8, 0xb9#8, 0x1b#8, 0x44#8, 0x66#8 ]

@[expose] def signalSharedExpected : List (BitVec 8) :=
  [ 0x32#8, 0x5f#8, 0x23#8, 0x93#8, 0x28#8, 0x94#8, 0x1c#8, 0xed#8,
    0x6e#8, 0x67#8, 0x3b#8, 0x86#8, 0xba#8, 0x41#8, 0x01#8, 0x74#8,
    0x48#8, 0xe9#8, 0x9b#8, 0x64#8, 0x9a#8, 0x9c#8, 0x38#8, 0x06#8,
    0xc1#8, 0xdd#8, 0x7c#8, 0xa4#8, 0xc4#8, 0x77#8, 0xe6#8, 0x29#8 ]

set_option maxHeartbeats 800000 in
theorem libsignal_agreement_ok :
    x25519Pubkey signalAlicePriv = signalAlicePub ∧
    x25519Pubkey signalBobPriv = signalBobPub ∧
    x25519 signalAlicePriv signalBobPub = signalSharedExpected ∧
    x25519 signalBobPriv signalAlicePub = signalSharedExpected := by
  decide +kernel

end TestVectors

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
